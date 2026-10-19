/**
 * On-chain tests for K17Machine.
 *
 * Every cycle is built by the keeper helpers, executed through scrypt-ts
 * (which runs the TypeScript method body) and then checked with the bundled
 * Bitcoin script interpreter via `tx.verifyInputScript`. Because the keeper
 * computes the next state with the reference VM, a passing cycle is a
 * differential test: reference VM == on-chain interpreter for that step.
 */
import { expect, use } from 'chai'
import chaiAsPromised from 'chai-as-promised'
import { bsv, toByteString } from 'scrypt-ts'
import { RabinSig } from 'scrypt-ts-lib'
import { K17Machine } from '../src/contracts/k17Machine'
import {
    assemble,
    Op,
    OUT_MAX,
    HAS_OPERAND,
    MEM_CELLS,
    CELL,
    encodeCell,
    slotCells,
} from '../src/k17/isa'
import {
    outputLog,
    run,
    initialState,
    readSlot,
    hashCell,
    whoOf,
    withSlot,
} from '../src/k17/vm'
import {
    fibonacciProgram,
    countdownProgram,
    heartbeatProgram,
    factoringBountyProgram,
    twoStageJobProgram,
    attestProgram,
    enrolAndAttestProgram,
} from '../src/k17/programs'
import {
    addrOf,
    bindCycleBuilder,
    newMachine,
    planCycle,
    rosterOf,
    CyclePlan,
    CycleKeys,
    CycleOverrides,
} from '../src/keeper'
import {
    NO_SIG,
    newAttester,
    signReading,
    keyHash,
    payoutOf,
    pubKeyBytes,
    signEndorsement,
} from '../src/k17/attest'
import { getDefaultSigner, randomPrivateKey } from './utils/txHelper'
use(chaiAsPromised)

const T0 = 1_760_000_000n // deployment time, unix seconds
const FUNDING = 100_000 // sats locked in the machine at deployment

const [, , , keeperA] = randomPrivateKey()
const [, , , keeperB] = randomPrivateKey()
const [, , , beneficiaryAddress] = randomPrivateKey()

const ECON = {
    beneficiary: addrOf(beneficiaryAddress),
    rewardMin: 100n,
    slope: 1n, // +1 sat per second of silence
    rewardMax: 500n,
}

/**
 * Deploy a machine for `prog` and return the live instance.
 * Input: program hex; optional funding (sats) and initial memory image hex.
 * Output: the deployed contract instance.
 */
async function deploy(
    prog: string,
    funding: number = FUNDING,
    initialMemHex?: string
): Promise<K17Machine> {
    const m = newMachine(prog, ECON, T0, rosterOf(), initialMemHex)
    await m.connect(getDefaultSigner())
    await m.deploy(funding)
    return m
}

/** Result of one on-chain cycle. */
interface CycleResult {
    plan: CyclePlan
    tx: bsv.Transaction
    next?: K17Machine
}

/**
 * Perform one cycle at `lockTime` with `keeper`, verify the script with the
 * interpreter, and return the next instance (undefined once halted).
 * `witness`, `sig` and `keys` are forwarded to planCycle; the plan's key and
 * payout byte strings (empty unless `keys` sets them) go to `step`.
 */
async function cycle(
    m: K17Machine,
    value: bigint,
    lockTime: bigint,
    keeper: bsv.Address,
    overrides: CycleOverrides & {
        witnessHex?: string
        keeperArg?: bsv.Address
        /** Signature to put in the unlocking script instead of the plan's. */
        sigArg?: RabinSig
    } = {},
    witness: bigint[] = [],
    sig: RabinSig = NO_SIG,
    keys: CycleKeys = {}
): Promise<CycleResult> {
    const plan = planCycle(m, value, lockTime, keeper, witness, sig, keys)
    const opts = bindCycleBuilder(m, plan, keeper, lockTime, overrides)
    const sent = overrides.sigArg ?? plan.sig
    const { tx, atInputIndex } = await m.methods.step(
        addrOf(overrides.keeperArg ?? keeper),
        toByteString(overrides.witnessHex ?? plan.witnessHex),
        sent.s,
        toByteString(sent.padding),
        toByteString(plan.keyAHex),
        toByteString(plan.keyBHex),
        toByteString(plan.payoutHex),
        opts
    )
    const verdict = tx.verifyInputScript(atInputIndex)
    if (!verdict.success) throw new Error(`script failed: ${verdict.error}`)
    return {
        plan,
        tx,
        next: plan.halted ? undefined : overrides.next ?? plan.next,
    }
}

/** Drive a machine to HALT; returns cycle count, payouts and the final tx. */
async function runToHalt(
    m: K17Machine,
    stepSeconds: bigint,
    keeper: bsv.Address
) {
    let cur: K17Machine | undefined = m
    let value = BigInt(FUNDING)
    let t = T0
    let cycles = 0
    let paid = 0n
    let last: CycleResult | undefined
    while (cur) {
        t += stepSeconds
        last = await cycle(cur, value, t, keeper)
        paid += last.plan.reward
        value = last.plan.remaining
        cycles++
        cur = last.next
    }
    return { cycles, paid, remaining: value, last: last as CycleResult }
}

describe('K17Machine on-chain', function () {
    this.timeout(600_000)

    before(async () => {
        await K17Machine.loadArtifact()
    })

    it('reports the compiled script size', async () => {
        const m = newMachine(fibonacciProgram(10), ECON, T0)
        const bytes = m.lockingScript.toBuffer().length
        console.log(
            `      locking script: ${bytes} bytes for K=${K17Machine.K}`
        )
        expect(bytes).to.be.greaterThan(1000)
    })

    it('runs Fibonacci(10) to HALT, every cycle script-verified, beneficiary paid', async () => {
        const prog = fibonacciProgram(10)
        const m = await deploy(prog)
        const { cycles, paid, remaining, last } = await runToHalt(
            m,
            10n,
            keeperA
        )

        // Cross-check against the reference VM run in one go.
        const ref = run(initialState(prog), 0n)
        expect(outputLog(ref.state)).to.deep.equal([
            0n,
            1n,
            1n,
            2n,
            3n,
            5n,
            8n,
            13n,
            21n,
            34n,
        ])
        expect(cycles).to.equal(Math.ceil(ref.steps / K17Machine.K))
        expect(last.plan.halted).to.be.true
        expect(paid + remaining).to.equal(BigInt(FUNDING))
        // every cycle 10 s apart -> reward 110 each
        expect(paid).to.equal(110n * BigInt(cycles))

        // Final tx: output 0 pays the beneficiary the remainder.
        const out0 = last.tx.outputs[0]
        expect(
            out0.script.toAddress(beneficiaryAddress.network).toString()
        ).to.equal(beneficiaryAddress.toString())
        expect(BigInt(out0.satoshis)).to.equal(remaining)
        console.log(
            `      ${cycles} cycles, ${paid} sats to keeper, ${remaining} sats to beneficiary`
        )
        console.log(`      final cycle tx: ${last.tx.toBuffer().length} bytes`)
    })

    it('exercises CALL/EXIT via the countdown program', async () => {
        const m = await deploy(countdownProgram(4))
        const { last } = await runToHalt(m, 1n, keeperA)
        expect(outputLog(last.plan.nextState)).to.deep.equal([4n, 3n, 2n, 1n])
    })

    it('liveness Dutch auction: reward grows with silence, caps, and a slow keeper takes over', async () => {
        const m = await deploy(heartbeatProgram())
        let value = BigInt(FUNDING)

        // Keeper A steps immediately: reward = rewardMin.
        let r = await cycle(m, value, T0 + 0n, keeperA)
        expect(r.plan.reward).to.equal(100n)
        value = r.plan.remaining

        // Keeper A again after 60 s: reward = 100 + 60.
        r = await cycle(r.next as K17Machine, value, T0 + 60n, keeperA)
        expect(r.plan.reward).to.equal(160n)
        expect(
            r.tx.outputs[1].script.toAddress(keeperA.network).toString()
        ).to.equal(keeperA.toString())
        value = r.plan.remaining

        // Keeper A disappears. Keeper B only steps once the reward reaches 300.
        r = await cycle(r.next as K17Machine, value, T0 + 60n + 200n, keeperB)
        expect(r.plan.reward).to.equal(300n)
        expect(
            r.tx.outputs[1].script.toAddress(keeperB.network).toString()
        ).to.equal(keeperB.toString())
        value = r.plan.remaining

        // Long silence: capped at rewardMax.
        r = await cycle(
            r.next as K17Machine,
            value,
            T0 + 260n + 100_000n,
            keeperB
        )
        expect(r.plan.reward).to.equal(500n)

        // TIME recorded each cycle's nLockTime, K/4 loop iterations per cycle.
        const per = K17Machine.K / 4
        const log = outputLog(r.plan.nextState)
        const expected: bigint[] = []
        for (const t of [T0, T0 + 60n, T0 + 260n, T0 + 100_260n]) {
            for (let i = 0; i < per; i++) expected.push(t)
        }
        expect(log).to.deep.equal(expected)
    })

    it('rejects a keeper who takes one satoshi too many', async () => {
        const m = await deploy(heartbeatProgram())
        const plan = planCycle(m, BigInt(FUNDING), T0 + 5n)
        await expect(
            cycle(m, BigInt(FUNDING), T0 + 5n, keeperA, {
                reward: plan.reward + 1n,
            })
        ).to.be.rejectedWith(/outputs mismatch|script failed/)
    })

    it('rejects a tampered next state', async () => {
        const m = await deploy(fibonacciProgram(3))
        const plan = planCycle(m, BigInt(FUNDING), T0 + 5n)
        const forged = (plan.next as K17Machine).next()
        forged.pc = forged.pc + 1n
        await expect(
            cycle(m, BigInt(FUNDING), T0 + 5n, keeperA, { next: forged })
        ).to.be.rejectedWith(/outputs mismatch|script failed/)
    })

    it('rejects time going backwards and a final nSequence', async () => {
        const m = await deploy(heartbeatProgram())
        const r = await cycle(m, BigInt(FUNDING), T0 + 100n, keeperA)
        const next = r.next as K17Machine
        await expect(
            cycle(next, r.plan.remaining, T0 + 50n, keeperA)
        ).to.be.rejectedWith(
            /lockTime before lastTime|time must not go backwards/
        )
        await expect(
            cycle(next, r.plan.remaining, T0 + 150n, keeperA, {
                sequence: 0xffffffff,
            })
        ).to.be.rejectedWith(/nSequence|script failed/)
    })

    it('rejects a machine that is not input 0 (output-sharing / sibling double-spend shape)', async () => {
        const m = await deploy(heartbeatProgram())
        await expect(
            cycle(m, BigInt(FUNDING), T0 + 5n, keeperA, { leadingFeeInputs: 1 })
        ).to.be.rejectedWith(/machine must be input 0/)
    })

    it('a fault releases funds to the beneficiary instead of freezing them', async () => {
        // DROP on an empty stack is a fault on the very first instruction.
        const m = await deploy(assemble(['DROP', 'LIT', 1, 'OUT', 'HALT']))
        const r = await cycle(m, BigInt(FUNDING), T0 + 1n, keeperA)
        expect(r.plan.halted).to.be.true
        expect(
            r.tx.outputs[0].script
                .toAddress(beneficiaryAddress.network)
                .toString()
        ).to.equal(beneficiaryAddress.toString())
    })

    it('differential fuzz: random programs never produce an unverifiable cycle', async () => {
        // IN, VERIFY, SIGVERIFY, ATTEST and ENDORSE make a transaction
        // invalid by design, so they are left out of the random op set;
        // everything else (PAYSLOT and VALUE included: they only fault or
        // succeed) must always verify.
        const ops = (
            Object.values(Op).filter((v) => typeof v === 'number') as number[]
        ).filter(
            (v) =>
                v !== Op.IN &&
                v !== Op.VERIFY &&
                v !== Op.SIGVERIFY &&
                v !== Op.ATTEST &&
                v !== Op.ENDORSE
        )
        let seed = 12345
        const rnd = (n: number) => {
            seed = (seed * 1103515245 + 12345) & 0x7fffffff
            return seed % n
        }
        for (let p = 0; p < 12; p++) {
            const bytes: number[] = []
            for (let i = 0; i < 24; i++) {
                const op = ops[rnd(ops.length)]
                bytes.push(op)
                if (HAS_OPERAND.has(op)) {
                    const operand = rnd(40) // small: addresses, offsets, literals
                    bytes.push(operand, 0, 0, 0)
                }
            }
            const prog = Buffer.from(bytes).toString('hex')
            const m = await deploy(prog)
            let cur: K17Machine | undefined = m
            let value = BigInt(FUNDING)
            let t = T0
            for (let c = 0; c < 6 && cur; c++) {
                t += 1n
                const r = await cycle(cur, value, t, keeperA)
                value = r.plan.remaining
                cur = r.next
            }
        }
    })

    it('output log cap faults the heartbeat after OUT_MAX cycles worth of entries', async () => {
        // Each heartbeat loop iteration is 4 instructions: K/4 log entries per cycle.
        const perCycle = K17Machine.K / 4
        const m = await deploy(heartbeatProgram())
        let cur: K17Machine | undefined = m
        let value = BigInt(FUNDING)
        let t = T0
        let n = 0
        while (cur && n < OUT_MAX + 2) {
            t += 1n
            const r = await cycle(cur, value, t, keeperA)
            value = r.plan.remaining
            cur = r.next
            n++
        }
        expect(cur).to.be.undefined
        expect(n).to.equal(Math.floor(OUT_MAX / perCycle) + 1)
    })

    // ------------------------------------------------------------------
    // Job bounties
    // ------------------------------------------------------------------

    const P = 65521
    const Q = 65519
    const N = P * Q // 4292870399, fits in 32 bits
    const BOUNTY1 = 40_000

    it('factoring bounty: a solver with the witness collects reward + bounty, beneficiary gets the rest', async () => {
        const m = await deploy(factoringBountyProgram(N, BOUNTY1))
        // Cycle 1: a plain keeper runs the leading YIELD only.
        const r1 = await cycle(m, BigInt(FUNDING), T0 + 1n, keeperA)
        expect(r1.plan.bounty).to.equal(0n)
        expect(r1.plan.nextState.pc).to.equal(1n)
        // Cycle 2: solver B supplies p, q and runs the whole stage atomically.
        const r2 = await cycle(
            r1.next as K17Machine,
            r1.plan.remaining,
            T0 + 2n,
            keeperB,
            {},
            [BigInt(P), BigInt(Q)]
        )
        expect(r2.plan.halted).to.be.true
        expect(r2.plan.bounty).to.equal(BigInt(BOUNTY1))
        expect(r2.plan.reward).to.equal(BigInt(BOUNTY1) + 101n)
        expect(outputLog(r2.plan.nextState)).to.deep.equal([
            BigInt(Q),
            BigInt(P),
        ])
        expect(
            r2.tx.outputs[1].script.toAddress(keeperB.network).toString()
        ).to.equal(keeperB.toString())
        expect(BigInt(r2.tx.outputs[1].satoshis)).to.equal(
            BigInt(BOUNTY1) + 101n
        )
        expect(
            r2.tx.outputs[0].script
                .toAddress(beneficiaryAddress.network)
                .toString()
        ).to.equal(beneficiaryAddress.toString())
    })

    it('factoring bounty: wrong, overflowing and missing witnesses are rejected', async () => {
        const m = await deploy(factoringBountyProgram(N, BOUNTY1))
        const r1 = await cycle(m, BigInt(FUNDING), T0 + 1n, keeperA)
        const staged = r1.next as K17Machine
        const v = r1.plan.remaining
        // Off-chain planner refuses a wrong factorisation.
        await expect(
            cycle(staged, v, T0 + 2n, keeperB, {}, [3n, 5n])
        ).to.be.rejectedWith(/witness rejected by VERIFY/)
        // Factors that only match modulo 2^32 are refused by the 16-bit guards.
        await expect(
            cycle(staged, v, T0 + 2n, keeperB, {}, [
                BigInt(N + 2 ** 32) / 1n,
                1n,
            ])
        ).to.be.rejectedWith(/witness rejected by VERIFY/)
        // No witness at all: the stage cannot be stepped by a plain keeper.
        await expect(cycle(staged, v, T0 + 2n, keeperA)).to.be.rejectedWith(
            /needs a witness/
        )
        // On-chain: plan with the right witness, but broadcast a wrong one.
        await expect(
            cycle(
                staged,
                v,
                T0 + 2n,
                keeperB,
                { witnessHex: '0300000005000000' },
                [BigInt(P), BigInt(Q)]
            )
        ).to.be.rejectedWith(/verify failed/)
        // On-chain: plan with the right witness, but broadcast none.
        await expect(
            cycle(staged, v, T0 + 2n, keeperB, { witnessHex: '' }, [
                BigInt(P),
                BigInt(Q),
            ])
        ).to.be.rejectedWith(/witness required/)
    })

    const X = 0xc0ffeen
    const BOUNTY2 = 25_000
    const DEADLINE = Number(T0) + 7 * 86_400 // a week, well past the commit TTL
    const COMMIT_TTL = 86_400 // a day: must dwarf confirmation latency, see twoStageJobProgram

    /** Deploy the two-stage job and run stage 1 with solver A. Returns the stage-2 machine. */
    async function stageTwoReady() {
        const target = hashCell(X ^ BigInt(P))
        const m = await deploy(
            twoStageJobProgram(
                N,
                Number(target),
                BOUNTY1,
                BOUNTY2,
                DEADLINE,
                COMMIT_TTL
            )
        )
        let value = BigInt(FUNDING)
        let r = await cycle(m, value, T0 + 1n, keeperA) // leading YIELD
        value = r.plan.remaining
        r = await cycle(r.next as K17Machine, value, T0 + 2n, keeperA, {}, [
            BigInt(P),
            BigInt(Q),
        ])
        expect(r.plan.bounty).to.equal(BigInt(BOUNTY1))
        return { machine: r.next as K17Machine, value: r.plan.remaining }
    }

    it('two-stage job with commit-reveal: dependent stage, front-runner refused', async () => {
        const ready = await stageTwoReady()
        const machine = ready.machine
        let value = ready.value

        // stage 2a: solver B commits HASH(x XOR WHO_B); selector 1 = commit
        const commitment = hashCell(X ^ whoOf(keeperB.toObject().hash))
        let r = await cycle(machine, value, T0 + 3n, keeperB, {}, [
            1n,
            commitment,
        ])
        expect(r.plan.bounty).to.equal(0n)
        value = r.plan.remaining
        const revealStage = r.next as K17Machine

        // front-runner A sees x in the mempool and tries to reveal as itself
        await expect(
            cycle(revealStage, value, T0 + 4n, keeperA, {}, [0n, X])
        ).to.be.rejectedWith(/witness rejected by VERIFY/)
        // front-runner A copies B's exact transaction but swaps the payee
        await expect(
            cycle(
                revealStage,
                value,
                T0 + 4n,
                keeperB,
                { keeperArg: keeperA },
                [0n, X]
            )
        ).to.be.rejectedWith(/verify failed/)
        // B reveals and collects
        r = await cycle(revealStage, value, T0 + 4n, keeperB, {}, [0n, X])
        expect(r.plan.halted).to.be.true
        expect(r.plan.bounty).to.equal(BigInt(BOUNTY2))
        expect(outputLog(r.plan.nextState)).to.deep.equal([BigInt(Q), X])
        expect(
            r.tx.outputs[1].script.toAddress(keeperB.network).toString()
        ).to.equal(keeperB.toString())
    })

    it('two-stage job: a bogus commit cannot lock the escrow; it expires and is overwritten', async () => {
        const ready = await stageTwoReady()
        const machine = ready.machine
        let value = ready.value

        // griefer A commits garbage
        let r = await cycle(machine, value, T0 + 10n, keeperA, {}, [1n, 0xbadn])
        value = r.plan.remaining
        // B cannot overwrite while the commit is fresh, and cannot reveal against it
        const commitment = hashCell(X ^ whoOf(keeperB.toObject().hash))
        await expect(
            cycle(r.next as K17Machine, value, T0 + 11n, keeperB, {}, [
                1n,
                commitment,
            ])
        ).to.be.rejectedWith(/witness rejected by VERIFY/)
        await expect(
            cycle(r.next as K17Machine, value, T0 + 11n, keeperB, {}, [0n, X])
        ).to.be.rejectedWith(/witness rejected by VERIFY/)
        // a plain keeper cannot step stage 2 at all (needs a selector witness)
        await expect(
            cycle(r.next as K17Machine, value, T0 + 11n, keeperA)
        ).to.be.rejectedWith(/needs a witness/)
        // after the TTL, B overwrites the commit and reveals in the next transaction
        r = await cycle(
            r.next as K17Machine,
            value,
            T0 + 10n + BigInt(COMMIT_TTL),
            keeperB,
            {},
            [1n, commitment]
        )
        value = r.plan.remaining
        r = await cycle(
            r.next as K17Machine,
            value,
            T0 + 11n + BigInt(COMMIT_TTL),
            keeperB,
            {},
            [0n, X]
        )
        expect(r.plan.halted).to.be.true
        expect(r.plan.bounty).to.equal(BigInt(BOUNTY2))
    })

    it('two-stage job: past the deadline any keeper can HALT it and the beneficiary is refunded', async () => {
        const { machine, value } = await stageTwoReady()
        const r = await cycle(machine, value, BigInt(DEADLINE), keeperA)
        expect(r.plan.halted).to.be.true
        expect(r.plan.bounty).to.equal(0n)
        expect(
            r.tx.outputs[0].script
                .toAddress(beneficiaryAddress.network)
                .toString()
        ).to.equal(beneficiaryAddress.toString())
    })

    // ---- K17+ : MIN / MAX / SIGVERIFY -------------------------------------

    it('MIN, MAX and DIV agree with the reference VM on chain', async () => {
        // prettier-ignore
        const prog = assemble([
            'LIT', 7, 'LIT', 3, 'MIN', 'OUT',
            'LIT', 7, 'LIT', 3, 'MAX', 'OUT',
            'LIT', 0xffffffff, 'LIT', 1, 'MIN', 'OUT',
            'LIT', 17, 'LIT', 5, '/', 'OUT',
            'LIT', 17, 'LIT', 0, '/', 'OUT',          // faults here
            'HALT',
        ])
        const m = await deploy(prog)
        const { last } = await runToHalt(m, 1n, keeperA)
        expect(outputLog(last.plan.nextState)).to.deep.equal([3n, 7n, 1n, 3n])
    })

    const SEED_A = Buffer.alloc(32, 1)
    const SEED_B = Buffer.alloc(32, 2)
    const attesterA = newAttester(SEED_A)
    const attesterB = newAttester(SEED_B)
    const ROSTER = rosterOf([attesterA.pub, attesterB.pub])

    /** Deploy the attest smoke program bound to slot `k`. */
    async function deployAttest(k: number): Promise<K17Machine> {
        const m = newMachine(attestProgram(k), ECON, T0, ROSTER)
        await m.connect(getDefaultSigner())
        await m.deploy(FUNDING)
        return m
    }

    it('SIGVERIFY: a reading signed by the roster key is accepted and any keeper may relay it', async () => {
        const m = await deployAttest(1)
        let value = BigInt(FUNDING)
        // cycle 1 runs up to the YIELD
        let r = await cycle(m, value, T0 + 1n, keeperA)
        value = r.plan.remaining
        // attester B signs (tag=5, value=2231); keeper A relays it
        const sig = signReading(attesterB, 5n, 2231n)
        r = await cycle(
            r.next as K17Machine,
            value,
            T0 + 2n,
            keeperA,
            {},
            [5n, 2231n],
            sig
        )
        expect(r.plan.halted).to.be.true
        expect(outputLog(r.plan.nextState)).to.deep.equal([5n, 2231n])
        console.log(
            `      attestation cycle tx: ${r.tx.toBuffer().length} bytes`
        )
    })

    it('SIGVERIFY: wrong key, altered reading, replayed tag and missing signature are all rejected', async () => {
        const m = await deployAttest(1)
        let value = BigInt(FUNDING)
        const r = await cycle(m, value, T0 + 1n, keeperA)
        value = r.plan.remaining
        const next = r.next as K17Machine
        const good = signReading(attesterB, 5n, 2231n)

        // signed by roster slot 0, program demands slot 1
        await expect(
            cycle(
                next,
                value,
                T0 + 2n,
                keeperA,
                {},
                [5n, 2231n],
                signReading(attesterA, 5n, 2231n)
            )
        ).to.be.rejectedWith(/rejected by VERIFY or SIGVERIFY/)
        // reading altered after signing
        await expect(
            cycle(next, value, T0 + 2n, keeperA, {}, [5n, 2232n], good)
        ).to.be.rejectedWith(/rejected by VERIFY or SIGVERIFY/)
        // old signature replayed under a new tag
        await expect(
            cycle(next, value, T0 + 2n, keeperA, {}, [6n, 2231n], good)
        ).to.be.rejectedWith(/rejected by VERIFY or SIGVERIFY/)
        // no signature at all
        await expect(
            cycle(next, value, T0 + 2n, keeperA, {}, [5n, 2231n])
        ).to.be.rejectedWith(/needs a witness/)
        // the plan is honest but the unlocking script carries a bad signature:
        // the script interpreter itself must refuse
        await expect(
            cycle(
                next,
                value,
                T0 + 2n,
                keeperA,
                { sigArg: signReading(attesterA, 5n, 2231n) },
                [5n, 2231n],
                good
            )
        ).to.be.rejected
    })

    it('SIGVERIFY: an empty roster slot faults the machine and refunds the beneficiary', async () => {
        const m = await deployAttest(3)
        let value = BigInt(FUNDING)
        let r = await cycle(m, value, T0 + 1n, keeperA)
        value = r.plan.remaining
        r = await cycle(
            r.next as K17Machine,
            value,
            T0 + 2n,
            keeperA,
            {},
            [5n, 2231n],
            signReading(attesterB, 5n, 2231n)
        )
        expect(r.plan.halted).to.be.true
        expect(outputLog(r.plan.nextState)).to.deep.equal([])
    })

    // ------------------------------------------------------------------
    // v2 machine: VALUE, PAYSLOT, roster write-protection
    // ------------------------------------------------------------------

    /** Address of a cell's P2PKH output, for comparisons. */
    const addressOf = (out: bsv.Transaction.Output): string =>
        out.script.toAddress(beneficiaryAddress.network).toString()

    it('VALUE agrees with the UTXO value', async () => {
        // YIELD keeps the machine alive so the log lands in the state output
        // and the contract's hashOutputs check covers it.
        const m = await deploy(assemble(['VALUE', 'OUT', 'YIELD', 'HALT']))
        const r = await cycle(m, BigInt(FUNDING), T0 + 1n, keeperA)
        expect(r.plan.halted).to.be.false
        expect(outputLog(r.plan.nextState)).to.deep.equal([BigInt(FUNDING)])
        expect((r.next as K17Machine).outLog).to.equal(
            toByteString(encodeCell(BigInt(FUNDING)))
        )
    })

    const [, , , payee] = randomPrivateKey()
    /** Memory image with roster slot 3 naming attester A and paying `payee`. */
    const SLOT3_MEM = withSlot(
        '00'.repeat(MEM_CELLS * CELL),
        3,
        slotCells(keyHash(attesterA.pub), payoutOf(payee))
    )
    const PAY700 = assemble(['LIT', 700, 'LIT', 3, 'PAYSLOT', 'YIELD'])

    it("PAYSLOT pays the slot's address in output 2 whoever relays", async () => {
        for (const keeper of [keeperA, keeperB]) {
            const m = await deploy(PAY700, FUNDING, SLOT3_MEM)
            const r = await cycle(m, BigInt(FUNDING), T0 + 1n, keeper)
            expect(r.plan.halted).to.be.false
            expect(r.plan.payslot).to.deep.equal({
                slot: 3,
                payoutHex: payoutOf(payee),
                sats: 700n,
            })
            // out0: state with the balance less reward and payout
            expect(BigInt(r.tx.outputs[0].satoshis)).to.equal(
                BigInt(FUNDING) - r.plan.reward - 700n
            )
            expect(r.plan.remaining).to.equal(
                BigInt(FUNDING) - r.plan.reward - 700n
            )
            // out1: the relaying keeper's reward
            expect(addressOf(r.tx.outputs[1])).to.equal(keeper.toString())
            expect(BigInt(r.tx.outputs[1].satoshis)).to.equal(r.plan.reward)
            // out2: the slot's payout address
            expect(addressOf(r.tx.outputs[2])).to.equal(payee.toString())
            expect(r.tx.outputs[2].satoshis).to.equal(700)
        }
    })

    /**
     * Check that a cycle faulted with no PAYSLOT payout: halted, outputs are
     * beneficiary (value less reward), keeper reward, change; no output 2.
     */
    const expectFaultRefund = (r: CycleResult, value: bigint): void => {
        expect(r.plan.halted).to.be.true
        expect(r.plan.payslot).to.be.undefined
        expect(r.tx.outputs.length).to.equal(3) // beneficiary, keeper, change
        expect(addressOf(r.tx.outputs[0])).to.equal(
            beneficiaryAddress.toString()
        )
        expect(BigInt(r.tx.outputs[0].satoshis)).to.equal(value - r.plan.reward)
        expect(r.plan.remaining).to.equal(value - r.plan.reward)
    }

    it('PAYSLOT that the balance cannot cover faults and refunds the beneficiary', async () => {
        // FUNDING 1000, reward 101 at T0+1: 898 leaves one satoshi, 899 none.
        const small = 1000
        const ok = await deploy(
            assemble(['LIT', 898, 'LIT', 3, 'PAYSLOT', 'YIELD']),
            small,
            SLOT3_MEM
        )
        const r = await cycle(ok, BigInt(small), T0 + 1n, keeperA)
        expect(r.plan.reward).to.equal(101n)
        expect(r.tx.outputs[0].satoshis).to.equal(1)
        expect(r.tx.outputs[2].satoshis).to.equal(898)

        const broke = await deploy(
            assemble(['LIT', 899, 'LIT', 3, 'PAYSLOT', 'YIELD']),
            small,
            SLOT3_MEM
        )
        const f = await cycle(broke, BigInt(small), T0 + 1n, keeperA)
        expectFaultRefund(f, BigInt(small))
        expect(f.plan.remaining).to.equal(899n)
    })

    it('PAYSLOT 0 faults and refunds the beneficiary', async () => {
        const m = await deploy(
            assemble(['LIT', 0, 'LIT', 3, 'PAYSLOT', 'YIELD']),
            FUNDING,
            SLOT3_MEM
        )
        const r = await cycle(m, BigInt(FUNDING), T0 + 1n, keeperA)
        expectFaultRefund(r, BigInt(FUNDING))
    })

    it('PAYSLOT on an empty or out-of-range slot faults and refunds the beneficiary', async () => {
        for (const slot of [2, 8]) {
            const m = await deploy(
                assemble(['LIT', 700, 'LIT', slot, 'PAYSLOT', 'YIELD']),
                FUNDING,
                SLOT3_MEM
            )
            const r = await cycle(m, BigInt(FUNDING), T0 + 1n, keeperA)
            expect(r.plan.halted).to.be.true
            expect(r.plan.payslot).to.be.undefined
            expect(r.tx.outputs.length).to.equal(3) // beneficiary, keeper, change
            expect(addressOf(r.tx.outputs[0])).to.equal(
                beneficiaryAddress.toString()
            )
            expect(BigInt(r.tx.outputs[0].satoshis)).to.equal(
                BigInt(FUNDING) - r.plan.reward
            )
        }
    })

    it('a second PAYSLOT in one cycle faults, drops the payout and refunds', async () => {
        // prettier-ignore
        const twice = assemble([
            'LIT', 1, 'LIT', 3, 'PAYSLOT', 'LIT', 1, 'LIT', 3, 'PAYSLOT', 'YIELD',
        ])
        const m = await deploy(twice, FUNDING, SLOT3_MEM)
        const r = await cycle(m, BigInt(FUNDING), T0 + 1n, keeperA)
        expectFaultRefund(r, BigInt(FUNDING))
    })

    it('STORE into the roster faults and refunds; STORE below it advances', async () => {
        const below = await deploy(
            assemble(['LIT', 7, 'LIT', 151, '!', 'YIELD'])
        )
        const r1 = await cycle(below, BigInt(FUNDING), T0 + 1n, keeperA)
        expect(r1.plan.halted).to.be.false
        const mem = (r1.next as K17Machine).mem
        expect(mem.slice(151 * 8, 152 * 8)).to.equal(encodeCell(7n))

        const into = await deploy(
            assemble(['LIT', 7, 'LIT', 152, '!', 'YIELD'])
        )
        const r2 = await cycle(into, BigInt(FUNDING), T0 + 1n, keeperA)
        expect(r2.plan.halted).to.be.true
        expect(addressOf(r2.tx.outputs[0])).to.equal(
            beneficiaryAddress.toString()
        )
        expect(BigInt(r2.tx.outputs[0].satoshis)).to.equal(
            BigInt(FUNDING) - r2.plan.reward
        )
    })

    // ------------------------------------------------------------------
    // v2 machine: ATTEST and ENDORSE against the memory roster
    // ------------------------------------------------------------------

    const sponsor = newAttester(Buffer.alloc(32, 41))
    const landowner = newAttester(Buffer.alloc(32, 42))
    const [, , , landownerAddress] = randomPrivateKey()
    const LANDOWNER_PAYOUT = payoutOf(landownerAddress)
    const TAG_E = 77
    const TAG_A = 88
    const READING = 2231n
    const BOUNTY = 5000
    /** Memory image with roster slot 0 naming the sponsor (zero payout). */
    const SPONSOR_MEM = withSlot(
        initialState('').mem,
        0,
        slotCells(keyHash(sponsor.pub), '00'.repeat(20))
    )
    /** Keys for a sponsor endorsement of the landowner. */
    const ENDORSE_KEYS: CycleKeys = {
        attestKey: sponsor.pub,
        endorseKey: landowner.pub,
        payoutHex: LANDOWNER_PAYOUT,
    }
    /** The sponsor's endorsement of the landowner into `slot`. */
    const endorsementFor = (slot: bigint): RabinSig =>
        signEndorsement(
            sponsor,
            BigInt(TAG_E),
            landowner.pub,
            LANDOWNER_PAYOUT,
            slot
        )

    /**
     * Send `plan` to `m` without the cycle() bookkeeping, so a test can pair
     * a plan made for one machine with another machine, or override keyA.
     * Input: machine, plan, lock time, optional keyA hex. Output: the step
     * call's promise (expected to reject).
     */
    function sendPlan(
        m: K17Machine,
        plan: CyclePlan,
        lockTime: bigint,
        keyAHex: string = plan.keyAHex
    ) {
        const opts = bindCycleBuilder(m, plan, keeperA, lockTime)
        return m.methods.step(
            addrOf(keeperA),
            toByteString(plan.witnessHex),
            plan.sig.s,
            toByteString(plan.sig.padding),
            toByteString(keyAHex),
            toByteString(plan.keyBHex),
            toByteString(plan.payoutHex),
            opts
        )
    }

    it('enrol, endorse and attest: the landowner is enrolled, attests and is paid', async () => {
        const m = await deploy(
            enrolAndAttestProgram(TAG_E, TAG_A, BOUNTY),
            FUNDING,
            SPONSOR_MEM
        )
        // cycle 1: the sponsor endorses the landowner into slot 1; keeper A relays
        const r1 = await cycle(
            m,
            BigInt(FUNDING),
            T0 + 1n,
            keeperA,
            {},
            [],
            endorsementFor(1n),
            ENDORSE_KEYS
        )
        expect(r1.plan.halted).to.be.false
        const enrolled = r1.next as K17Machine
        expect(readSlot(enrolled.mem, 1)).to.deep.equal({
            hashHex: keyHash(landowner.pub),
            payoutHex: LANDOWNER_PAYOUT,
            empty: false,
        })
        // cycle 2: the landowner attests a reading; keeper A relays
        const r2 = await cycle(
            enrolled,
            r1.plan.remaining,
            T0 + 2n,
            keeperA,
            {},
            [READING],
            signReading(landowner, BigInt(TAG_A), READING),
            { attestKey: landowner.pub }
        )
        expect(r2.plan.halted).to.be.true
        expect(outputLog(r2.plan.nextState)).to.deep.equal([READING])
        expect(addressOf(r2.tx.outputs[0])).to.equal(
            beneficiaryAddress.toString()
        )
        expect(addressOf(r2.tx.outputs[1])).to.equal(keeperA.toString())
        expect(addressOf(r2.tx.outputs[2])).to.equal(
            landownerAddress.toString()
        )
        expect(r2.tx.outputs[2].satoshis).to.equal(BOUNTY)
        expect(BigInt(r2.tx.outputs[0].satoshis)).to.equal(
            r1.plan.remaining - r2.plan.reward - BigInt(BOUNTY)
        )
        console.log(
            `      endorsement cycle tx: ${
                r1.tx.toBuffer().length
            } bytes, attestation cycle tx: ${r2.tx.toBuffer().length} bytes`
        )
    })

    /** Program: attest (5, 2231) against slot 0, then yield. */
    const ATTEST0 = assemble([
        'LIT',
        5,
        'LIT',
        2231,
        'LIT',
        0,
        'ATTEST',
        'YIELD',
    ])
    const ATTEST0_SIG = (): RabinSig => signReading(sponsor, 5n, 2231n)

    it('ATTEST accepts the slot key and refuses a 383-byte key', async () => {
        const m = await deploy(ATTEST0, FUNDING, SPONSOR_MEM)
        const plan = planCycle(
            m,
            BigInt(FUNDING),
            T0 + 1n,
            keeperA,
            [],
            ATTEST0_SIG(),
            {
                attestKey: sponsor.pub,
            }
        )
        await expect(
            sendPlan(m, plan, T0 + 1n, pubKeyBytes(sponsor.pub).slice(0, 766))
        ).to.be.rejectedWith(/key must be 384 bytes/)
        const r = await cycle(
            m,
            BigInt(FUNDING),
            T0 + 1n,
            keeperA,
            {},
            [],
            ATTEST0_SIG(),
            {
                attestKey: sponsor.pub,
            }
        )
        expect(r.plan.halted).to.be.false
        expect((r.next as K17Machine).ds).to.equal('')
    })

    it('ATTEST refuses a key that is not the slot key', async () => {
        const m = await deploy(ATTEST0, FUNDING, SPONSOR_MEM)
        const plan = planCycle(
            m,
            BigInt(FUNDING),
            T0 + 1n,
            keeperA,
            [],
            ATTEST0_SIG(),
            {
                attestKey: sponsor.pub,
            }
        )
        await expect(
            sendPlan(m, plan, T0 + 1n, pubKeyBytes(landowner.pub))
        ).to.be.rejectedWith(/key not in roster slot/)
    })

    it('ATTEST then ENDORSE in one cycle is refused', async () => {
        // prettier-ignore
        const both = assemble([
            'LIT', 5, 'LIT', 2231, 'LIT', 0, 'ATTEST',
            'LIT', TAG_E, 'LIT', 0, 'LIT', 1, 'ENDORSE', 'YIELD',
        ])
        const m = await deploy(both, FUNDING, SPONSOR_MEM)
        // The reference VM refuses to plan it.
        expect(() =>
            planCycle(
                m,
                BigInt(FUNDING),
                T0 + 1n,
                keeperA,
                [],
                ATTEST0_SIG(),
                ENDORSE_KEYS
            )
        ).to.throw(/needs a witness/)
        // Build the spend from an ATTEST-only plan: the contract must refuse.
        const once = newMachine(ATTEST0, ECON, T0, rosterOf(), SPONSOR_MEM)
        const plan = planCycle(
            once,
            BigInt(FUNDING),
            T0 + 1n,
            keeperA,
            [],
            ATTEST0_SIG(),
            ENDORSE_KEYS
        )
        await expect(sendPlan(m, plan, T0 + 1n)).to.be.rejectedWith(
            /one attestation per cycle/
        )
    })

    it('an endorsement signed for slot 1 is refused when presented with NEWSLOT 2', async () => {
        const into2 = assemble([
            'LIT',
            TAG_E,
            'LIT',
            0,
            'LIT',
            2,
            'ENDORSE',
            'YIELD',
        ])
        const m = await deploy(into2, FUNDING, SPONSOR_MEM)
        // The reference VM refuses to plan it.
        expect(() =>
            planCycle(
                m,
                BigInt(FUNDING),
                T0 + 1n,
                keeperA,
                [],
                endorsementFor(1n),
                ENDORSE_KEYS
            )
        ).to.throw(/witness rejected/)
        // Build the spend from the honest slot-1 plan: the contract must refuse.
        const into1 = newMachine(
            assemble(['LIT', TAG_E, 'LIT', 0, 'LIT', 1, 'ENDORSE', 'YIELD']),
            ECON,
            T0,
            rosterOf(),
            SPONSOR_MEM
        )
        const plan = planCycle(
            into1,
            BigInt(FUNDING),
            T0 + 1n,
            keeperA,
            [],
            endorsementFor(1n),
            ENDORSE_KEYS
        )
        await expect(sendPlan(m, plan, T0 + 1n)).to.be.rejectedWith(
            /signature check failed/
        )
    })

    it('ATTEST on an empty slot and ENDORSE into a filled slot fault and refund', async () => {
        const emptySlot = await deploy(
            assemble(['LIT', 5, 'LIT', 2231, 'LIT', 1, 'ATTEST', 'YIELD']),
            FUNDING,
            SPONSOR_MEM
        )
        const a = await cycle(
            emptySlot,
            BigInt(FUNDING),
            T0 + 1n,
            keeperA,
            {},
            [],
            ATTEST0_SIG(),
            {
                attestKey: sponsor.pub,
            }
        )
        expectFaultRefund(a, BigInt(FUNDING))
        const filled = await deploy(
            assemble(['LIT', TAG_E, 'LIT', 0, 'LIT', 0, 'ENDORSE', 'YIELD']),
            FUNDING,
            SPONSOR_MEM
        )
        const e = await cycle(
            filled,
            BigInt(FUNDING),
            T0 + 1n,
            keeperA,
            {},
            [],
            endorsementFor(0n),
            ENDORSE_KEYS
        )
        expectFaultRefund(e, BigInt(FUNDING))
    })
})
