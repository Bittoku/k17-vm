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
import { createHash } from 'crypto'
import chaiAsPromised from 'chai-as-promised'
import { bsv, int2ByteString, toByteString } from 'scrypt-ts'
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
    randomInstanceId,
    rosterOf,
    CyclePlan,
    CycleKeys,
    CycleOverrides,
    CycleTree,
} from '../src/keeper'
import { EMPTY_HASHES, SparseMerkleTree, encodeLeafPre } from '../src/k17/smt'
import {
    NO_SIG,
    newAttester,
    signReading,
    signReadingFor,
    keyHash,
    payoutOf,
    pubKeyBytes,
    signEndorsement,
    signMemberReading,
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

/** Fixed instance id for deterministic tests (newMachine defaults to random). */
const TEST_ID = '5a'.repeat(32)

/** Memory image with every roster slot filled (for the differential fuzz). */
const FULL_ROSTER_MEM = [0, 1, 2, 3, 4, 5, 6, 7].reduce(
    (mem, slot) =>
        withSlot(mem, slot, slotCells('ab'.repeat(32), '11'.repeat(20))),
    '00'.repeat(MEM_CELLS * CELL)
)

/**
 * Print a size measurement when K17_SIZES is set in the environment, so a
 * normal test run stays quiet. Input: message. Output: none.
 */
function logSize(message: string): void {
    if (process.env.K17_SIZES) console.log(message)
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
    const m = newMachine(prog, ECON, T0, rosterOf(), initialMemHex, TEST_ID)
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
 * `witness`, `sig`, `keys` and `tree` are forwarded to planCycle; the plan's
 * key and payout byte strings (empty unless `keys` sets them) and its tree
 * proof (leafPre '', proof '', leafIndex 0 unless `tree` sets them) go to
 * `step`.
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
    keys: CycleKeys = {},
    tree?: CycleTree
): Promise<CycleResult> {
    const plan = planCycle(m, value, lockTime, keeper, witness, sig, keys, tree)
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
        toByteString(plan.leafPre),
        toByteString(plan.proof),
        plan.leafIndex,
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
        logSize(`      locking script: ${bytes} bytes for K=${K17Machine.K}`)
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
        logSize(
            `      ${cycles} cycles, ${paid} sats to keeper, ${remaining} sats to beneficiary`
        )
        logSize(`      final cycle tx: ${last.tx.toBuffer().length} bytes`)
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

    /** Every opcode value of the ISA. */
    const ALL_OPS = Object.values(Op).filter(
        (v) => typeof v === 'number'
    ) as number[]

    /**
     * Differential fuzz: deploy 12 random 24-instruction programs over `ops`
     * with memory image `mem` and step each up to 6 cycles; every cycle goes
     * through cycle(), so every one must pass verifyInputScript.
     * Input: op set, memory image, PRNG seed. Output: none (throws on a
     * cycle that does not verify).
     */
    async function fuzz(ops: number[], mem: string, seed: number) {
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
            const m = await deploy(prog, FUNDING, mem)
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
    }

    it('differential fuzz: random programs never produce an unverifiable cycle', async () => {
        // IN, VERIFY, SIGVERIFY, ATTEST and ENDORSE can make a transaction
        // invalid by design, so they are left out of the random op set;
        // everything else (PAYSLOT and VALUE included: they only fault or
        // succeed) must always verify. Every roster slot is filled, so
        // random PAYSLOTs can succeed.
        const ops = ALL_OPS.filter(
            (v) =>
                v !== Op.IN &&
                v !== Op.VERIFY &&
                v !== Op.SIGVERIFY &&
                v !== Op.ATTEST &&
                v !== Op.ENDORSE
        )
        await fuzz(ops, FULL_ROSTER_MEM, 12345)
    })

    it('differential fuzz on an empty roster: ATTEST and ENDORSE only fault', async () => {
        // With every roster slot empty, every ATTEST and ENDORSE path faults
        // before it needs a key or a signature, so they join the op set.
        const ops = ALL_OPS.filter(
            (v) => v !== Op.IN && v !== Op.VERIFY && v !== Op.SIGVERIFY
        )
        await fuzz(ops, '00'.repeat(MEM_CELLS * CELL), 54321)
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
        const m = newMachine(
            attestProgram(k),
            ECON,
            T0,
            ROSTER,
            undefined,
            TEST_ID
        )
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
        logSize(`      attestation cycle tx: ${r.tx.toBuffer().length} bytes`)
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
        ).to.be.rejectedWith(/rejected by VERIFY, SIGVERIFY/)
        // reading altered after signing
        await expect(
            cycle(next, value, T0 + 2n, keeperA, {}, [5n, 2232n], good)
        ).to.be.rejectedWith(/rejected by VERIFY, SIGVERIFY/)
        // old signature replayed under a new tag
        await expect(
            cycle(next, value, T0 + 2n, keeperA, {}, [6n, 2231n], good)
        ).to.be.rejectedWith(/rejected by VERIFY, SIGVERIFY/)
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

    it('PAYSLOT has priority over the keeper reward; only N >= the balance faults', async () => {
        // FUNDING 1000, auction reward 101 at T0+1.
        const small = 1000
        const pay = (n: number) =>
            deploy(
                assemble(['LIT', n, 'LIT', 3, 'PAYSLOT', 'YIELD']),
                small,
                SLOT3_MEM
            )
        // 898 leaves room for the full reward and one satoshi.
        let r = await cycle(await pay(898), BigInt(small), T0 + 1n, keeperA)
        expect(r.plan.reward).to.equal(101n)
        expect(r.tx.outputs[0].satoshis).to.equal(1)
        expect(r.tx.outputs[2].satoshis).to.equal(898)
        // 950: the reward shrinks to 49, the slot is paid in full.
        r = await cycle(await pay(950), BigInt(small), T0 + 1n, keeperA)
        expect(r.plan.reward).to.equal(49n)
        expect(r.tx.outputs[0].satoshis).to.equal(1)
        expect(r.tx.outputs[2].satoshis).to.equal(950)
        // 999: no reward at all (no keeper output); payout is output 1.
        r = await cycle(await pay(999), BigInt(small), T0 + 1n, keeperA)
        expect(r.plan.reward).to.equal(0n)
        expect(r.plan.halted).to.be.false
        expect(r.tx.outputs[0].satoshis).to.equal(1)
        expect(addressOf(r.tx.outputs[1])).to.equal(payee.toString())
        expect(r.tx.outputs[1].satoshis).to.equal(999)
        // 1000 cannot leave one satoshi: fault, payout dropped, refund.
        const f = await cycle(await pay(1000), BigInt(small), T0 + 1n, keeperA)
        expectFaultRefund(f, BigInt(small))
        expect(f.plan.remaining).to.equal(899n)
    })

    it('a late keeper cannot shrink the slot payout, only its own reward', async () => {
        // FUNDING 1000, PAYSLOT 800; at T0+300 the auction offers 400
        // (capped at rewardMax 500), but only 199 is left after the payout.
        const small = 1000
        const m = await deploy(
            assemble(['LIT', 800, 'LIT', 3, 'PAYSLOT', 'YIELD']),
            small,
            SLOT3_MEM
        )
        const r = await cycle(m, BigInt(small), T0 + 300n, keeperB)
        expect(r.plan.halted).to.be.false
        expect(r.plan.reward).to.equal(199n)
        expect(r.tx.outputs[0].satoshis).to.equal(1)
        expect(addressOf(r.tx.outputs[1])).to.equal(keeperB.toString())
        expect(r.tx.outputs[1].satoshis).to.equal(199)
        expect(addressOf(r.tx.outputs[2])).to.equal(payee.toString())
        expect(r.tx.outputs[2].satoshis).to.equal(800)
    })

    it('PAYSLOT then an unrelated fault keeps the payout', async () => {
        // prettier-ignore
        const prog = assemble([
            'LIT', 700, 'LIT', 3, 'PAYSLOT', 'DROP', 'DROP', 'DROP', 'YIELD',
        ])
        const m = await deploy(prog, FUNDING, SLOT3_MEM)
        const r = await cycle(m, BigInt(FUNDING), T0 + 1n, keeperA)
        expect(r.plan.halted).to.be.true
        expect(r.plan.payslot?.sats).to.equal(700n)
        expect(addressOf(r.tx.outputs[0])).to.equal(
            beneficiaryAddress.toString()
        )
        expect(BigInt(r.tx.outputs[0].satoshis)).to.equal(
            BigInt(FUNDING) - r.plan.reward - 700n
        )
        expect(addressOf(r.tx.outputs[1])).to.equal(keeperA.toString())
        expect(addressOf(r.tx.outputs[2])).to.equal(payee.toString())
        expect(r.tx.outputs[2].satoshis).to.equal(700)
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
        // a malformed (underflowing) second PAYSLOT also drops the payout
        const bad = await deploy(
            assemble(['LIT', 1, 'LIT', 3, 'PAYSLOT', 'PAYSLOT', 'YIELD']),
            FUNDING,
            SLOT3_MEM
        )
        const rb = await cycle(bad, BigInt(FUNDING), T0 + 1n, keeperA)
        expectFaultRefund(rb, BigInt(FUNDING))
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
    const endorsementFor = (slot: bigint, instanceId: string): RabinSig =>
        signEndorsement(
            sponsor,
            instanceId,
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
            toByteString(plan.leafPre),
            toByteString(plan.proof),
            plan.leafIndex,
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
            endorsementFor(1n, m.instanceId),
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
            signReadingFor(
                landowner,
                enrolled.instanceId,
                BigInt(TAG_A),
                READING
            ),
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
        logSize(
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
    /** The sponsor's signature of (5, 2231) for the machine `instanceId`. */
    const ATTEST0_SIG = (instanceId: string): RabinSig =>
        signReadingFor(sponsor, instanceId, 5n, 2231n)

    it('ATTEST accepts the slot key and refuses a 383-byte key', async () => {
        const m = await deploy(ATTEST0, FUNDING, SPONSOR_MEM)
        const plan = planCycle(
            m,
            BigInt(FUNDING),
            T0 + 1n,
            keeperA,
            [],
            ATTEST0_SIG(m.instanceId),
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
            ATTEST0_SIG(m.instanceId),
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
            ATTEST0_SIG(m.instanceId),
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
                ATTEST0_SIG(m.instanceId),
                ENDORSE_KEYS
            )
        ).to.throw(/needs a witness/)
        // Build the spend from an ATTEST-only plan: the contract must refuse.
        const once = newMachine(
            ATTEST0,
            ECON,
            T0,
            rosterOf(),
            SPONSOR_MEM,
            m.instanceId
        )
        const plan = planCycle(
            once,
            BigInt(FUNDING),
            T0 + 1n,
            keeperA,
            [],
            ATTEST0_SIG(m.instanceId),
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
                endorsementFor(1n, m.instanceId),
                ENDORSE_KEYS
            )
        ).to.throw(/witness rejected/)
        // Build the spend from the honest slot-1 plan: the contract must refuse.
        const into1 = newMachine(
            assemble(['LIT', TAG_E, 'LIT', 0, 'LIT', 1, 'ENDORSE', 'YIELD']),
            ECON,
            T0,
            rosterOf(),
            SPONSOR_MEM,
            m.instanceId
        )
        const plan = planCycle(
            into1,
            BigInt(FUNDING),
            T0 + 1n,
            keeperA,
            [],
            endorsementFor(1n, m.instanceId),
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
            ATTEST0_SIG(emptySlot.instanceId),
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
            endorsementFor(0n, filled.instanceId),
            ENDORSE_KEYS
        )
        expectFaultRefund(e, BigInt(FUNDING))
    })

    it('a reading signed for instance A is refused by instance B', async () => {
        const idA = 'aa'.repeat(32)
        const idB = 'bb'.repeat(32)
        const a = newMachine(ATTEST0, ECON, T0, rosterOf(), SPONSOR_MEM, idA)
        const b = newMachine(ATTEST0, ECON, T0, rosterOf(), SPONSOR_MEM, idB)
        await b.connect(getDefaultSigner())
        await b.deploy(FUNDING)
        const keys = { attestKey: sponsor.pub }
        // The reference VM refuses to plan it.
        expect(() =>
            planCycle(
                b,
                BigInt(FUNDING),
                T0 + 1n,
                keeperA,
                [],
                ATTEST0_SIG(idA),
                keys
            )
        ).to.throw(/witness rejected/)
        // Build the spend from instance A's honest plan: B must refuse.
        const plan = planCycle(
            a,
            BigInt(FUNDING),
            T0 + 1n,
            keeperA,
            [],
            ATTEST0_SIG(idA),
            keys
        )
        await expect(sendPlan(b, plan, T0 + 1n)).to.be.rejectedWith(
            /signature check failed/
        )
        // and B accepts its own signature
        const r = await cycle(
            b,
            BigInt(FUNDING),
            T0 + 1n,
            keeperA,
            {},
            [],
            ATTEST0_SIG(idB),
            keys
        )
        expect(r.plan.halted).to.be.false
    })

    it('newMachine draws a random instance id and rejects a malformed one', () => {
        const m1 = newMachine(ATTEST0, ECON, T0, rosterOf(), SPONSOR_MEM)
        const m2 = newMachine(ATTEST0, ECON, T0, rosterOf(), SPONSOR_MEM)
        expect(m1.instanceId).to.match(/^[0-9a-f]{64}$/)
        // identical deployments in the same second still differ
        expect(m1.instanceId).to.not.equal(m2.instanceId)
        expect(randomInstanceId()).to.match(/^[0-9a-f]{64}$/)
        for (const bad of ['ab', 'AB'.repeat(32), 'zz'.repeat(32)]) {
            expect(() =>
                newMachine(ATTEST0, ECON, T0, rosterOf(), SPONSOR_MEM, bad)
            ).to.throw(/64 lowercase hex/)
        }
    })

    it('a machine whose instance id is not 32 bytes faults and refunds the beneficiary', async () => {
        // Built with the constructor directly: newMachine refuses such an id.
        const s0 = initialState(heartbeatProgram())
        const m = new K17Machine(
            toByteString(s0.prog),
            ECON.beneficiary,
            ECON.rewardMin,
            ECON.slope,
            ECON.rewardMax,
            rosterOf(),
            toByteString('ab'.repeat(31)),
            toByteString(s0.sponsorKeyHash),
            s0.pc,
            toByteString(s0.ds),
            toByteString(s0.rs),
            toByteString(s0.mem),
            toByteString(s0.out),
            T0,
            toByteString(s0.rosterRoot),
            s0.rosterSeq,
            toByteString(s0.logHash)
        )
        await m.connect(getDefaultSigner())
        await m.deploy(FUNDING)
        // cycle() runs verifyInputScript on the refund transaction
        const r = await cycle(m, BigInt(FUNDING), T0 + 1n, keeperA)
        expect(r.plan.halted).to.be.true
        expect(outputLog(r.plan.nextState)).to.deep.equal([]) // no step ran
        expect(addressOf(r.tx.outputs[0])).to.equal(
            beneficiaryAddress.toString()
        )
        expect(BigInt(r.tx.outputs[0].satoshis)).to.equal(
            BigInt(FUNDING) - r.plan.reward
        )
    })

    // ---- tampered unlocking scripts, judged by the script interpreter ----

    /**
     * Replace one data push in the unlocking script of input `inputIndex`
     * and re-attach the script, so the Bitcoin script interpreter (not the
     * scrypt-ts JS evaluation) judges the change.
     * Input: transaction, input index, hex of the push to replace (must
     * match exactly one non-empty push), hex of the new push.
     * Output: none (mutates tx). Throws when the push is not found once.
     */
    function tamperPush(
        tx: bsv.Transaction,
        inputIndex: number,
        fromHex: string,
        toHex: string
    ): void {
        const input = tx.inputs[inputIndex]
        const chunks = input.script.chunks
        const hits = chunks
            .map((c, i) =>
                c.buf && c.buf.toString('hex') === fromHex ? i : -1
            )
            .filter((i) => i >= 0)
        if (hits.length !== 1) {
            throw new Error(
                `push ${fromHex.slice(0, 16)}... found ${hits.length} times`
            )
        }
        const replacement = new bsv.Script('')
        replacement.add(Buffer.from(toHex, 'hex'))
        const rebuilt = new bsv.Script('')
        chunks.forEach((c, i) => {
            rebuilt.chunks.push(i === hits[0] ? replacement.chunks[0] : c)
        })
        input.setScript(rebuilt)
    }

    /** Assert that the script interpreter refuses input `i` of `tx`. */
    function expectScriptRefused(tx: bsv.Transaction, i = 0): void {
        expect(tx.verifyInputScript(i).success).to.equal(false)
    }

    it('interpreter refuses a tampered keyA on an honest ATTEST cycle (wrong key, 383 bytes)', async () => {
        const honest = async () => {
            const m = await deploy(ATTEST0, FUNDING, SPONSOR_MEM)
            return cycle(
                m,
                BigInt(FUNDING),
                T0 + 1n,
                keeperA,
                {},
                [],
                ATTEST0_SIG(m.instanceId),
                {
                    attestKey: sponsor.pub,
                }
            )
        }
        const keyA = pubKeyBytes(sponsor.pub)
        const wrong = await honest()
        expect(wrong.tx.verifyInputScript(0).success).to.equal(true)
        tamperPush(wrong.tx, 0, keyA, pubKeyBytes(landowner.pub))
        expectScriptRefused(wrong.tx)
        const short = await honest()
        tamperPush(short.tx, 0, keyA, keyA.slice(0, 766))
        expectScriptRefused(short.tx)
    })

    it('interpreter refuses a swapped payout or keyB on an honest ENDORSE cycle', async () => {
        const honest = async () => {
            const m = await deploy(
                enrolAndAttestProgram(TAG_E, TAG_A, BOUNTY),
                FUNDING,
                SPONSOR_MEM
            )
            return cycle(
                m,
                BigInt(FUNDING),
                T0 + 1n,
                keeperA,
                {},
                [],
                endorsementFor(1n, m.instanceId),
                ENDORSE_KEYS
            )
        }
        const payoutSwap = await honest()
        tamperPush(payoutSwap.tx, 0, LANDOWNER_PAYOUT, '22'.repeat(20))
        expectScriptRefused(payoutSwap.tx)
        const keyBSwap = await honest()
        tamperPush(
            keyBSwap.tx,
            0,
            pubKeyBytes(landowner.pub),
            pubKeyBytes(sponsor.pub)
        )
        expectScriptRefused(keyBSwap.tx)
    })

    it('interpreter refuses an ATTEST signature made for instance A on instance B', async () => {
        const idA = 'aa'.repeat(32)
        const idB = 'bb'.repeat(32)
        // pick a tag whose two signatures have distinct, non-empty paddings,
        // so each push is unique in the unlocking script
        let tag = 5
        const sigsFor = (t: number) => ({
            a: signReadingFor(sponsor, idA, BigInt(t), 2231n),
            b: signReadingFor(sponsor, idB, BigInt(t), 2231n),
        })
        let sigs = sigsFor(tag)
        while (
            sigs.a.padding === '' ||
            sigs.b.padding === '' ||
            sigs.a.padding === sigs.b.padding
        ) {
            sigs = sigsFor(++tag)
        }
        const prog = assemble([
            'LIT',
            tag,
            'LIT',
            2231,
            'LIT',
            0,
            'ATTEST',
            'YIELD',
        ])
        const b = newMachine(prog, ECON, T0, rosterOf(), SPONSOR_MEM, idB)
        await b.connect(getDefaultSigner())
        await b.deploy(FUNDING)
        const r = await cycle(
            b,
            BigInt(FUNDING),
            T0 + 1n,
            keeperA,
            {},
            [],
            sigs.b,
            {
                attestKey: sponsor.pub,
            }
        )
        tamperPush(r.tx, 0, int2ByteString(sigs.b.s), int2ByteString(sigs.a.s))
        tamperPush(r.tx, 0, sigs.b.padding, sigs.a.padding)
        expectScriptRefused(r.tx)
    })
    // ------------------------------------------------------------------
    // v3 machine: the Merkle roster tree
    // ------------------------------------------------------------------

    /** SHA-256 of a hex string, as hex. Input: hex. Output: 64 hex chars. */
    const sha256Hex = (hex: string): string =>
        createHash('sha256').update(Buffer.from(hex, 'hex')).digest('hex')

    const [, , , memberAAddress] = randomPrivateKey()
    const [, , , memberBAddress] = randomPrivateKey()
    /** Leaf positions of the two tree members: level-0 siblings (left, right). */
    const INDEX_A = 300
    const INDEX_B = 301
    /** Tag of the members' readings and the sats PAYLEAF pays each cycle. */
    const TAG_M = 99
    const PAY_M = 3000

    /**
     * Leaf preimage of member A (attesterA's key) or B (attesterB's key).
     * Input: which member, its lastRound. Output: 120 hex chars.
     */
    const leafOf = (member: 'A' | 'B', lastRound: bigint): string =>
        member === 'A'
            ? encodeLeafPre(
                  keyHash(attesterA.pub),
                  payoutOf(memberAAddress),
                  lastRound
              )
            : encodeLeafPre(
                  keyHash(attesterB.pub),
                  payoutOf(memberBAddress),
                  lastRound
              )

    /**
     * Off-chain tree with members A and B, both at lastRound 0.
     * Input: none. Output: a fresh SparseMerkleTree.
     */
    const twoMemberTree = (): SparseMerkleTree =>
        new SparseMerkleTree(
            new Map([
                [INDEX_A, leafOf('A', 0n)],
                [INDEX_B, leafOf('B', 0n)],
            ])
        )

    /**
     * Program: bind the member, log its lastRound, check its signed reading
     * (TAG_M, witness) with ATTESTM, fold the reading into logHash, pay it
     * PAY_M with ROUND = TIME, yield, then loop back to the start.
     */
    const MEMBER_PROG = assemble([
        'MEMBER',
        'DROP',
        'LASTROUND',
        'OUT',
        'LIT',
        TAG_M,
        'IN',
        'DUP',
        '>R',
        'ATTESTM',
        'R>',
        'OUTH',
        'LIT',
        PAY_M,
        'TIME',
        'PAYLEAF',
        'YIELD',
        'LIT',
        0,
        'IF',
        0,
    ])

    /**
     * Deploy `prog` with the roster tree root of `tree` and the sponsor's
     * key hash. Input: program hex, off-chain tree. Output: live instance.
     */
    async function deployTree(
        prog: string,
        tree: SparseMerkleTree
    ): Promise<K17Machine> {
        const m = newMachine(prog, ECON, T0, undefined, undefined, TEST_ID, {
            rosterRoot: tree.root(),
            sponsorKeyHash: keyHash(sponsor.pub),
        })
        await m.connect(getDefaultSigner())
        await m.deploy(FUNDING)
        return m
    }

    /**
     * Run one MEMBER_PROG cycle for member A or B with the member's signed
     * `reading` and its proof from `tree` (or `proofOverride`).
     * Input: machine, value, lock time, member, tree, reading, optional
     * proof to present instead. Output: the cycle result.
     */
    function memberCycle(
        m: K17Machine,
        value: bigint,
        lockTime: bigint,
        member: 'A' | 'B',
        tree: SparseMerkleTree,
        reading: bigint,
        proofOverride?: CycleTree
    ): Promise<CycleResult> {
        const attester = member === 'A' ? attesterA : attesterB
        return cycle(
            m,
            value,
            lockTime,
            keeperA,
            {},
            [reading],
            signMemberReading(attester, m.instanceId, BigInt(TAG_M), reading),
            { attestKey: attester.pub },
            proofOverride ?? tree.proof(member === 'A' ? INDEX_A : INDEX_B)
        )
    }

    it('the contract embeds the empty-subtree hashes of the off-chain tree', () => {
        expect(K17Machine.EMPTY_HASHES).to.deep.equal(EMPTY_HASHES)
        const m = newMachine(MEMBER_PROG, ECON, T0)
        expect(m.rosterRoot).to.equal(EMPTY_HASHES[16])
        expect(m.rosterSeq).to.equal(0n)
        expect(m.logHash).to.equal('00'.repeat(32))
        expect(m.sponsorKeyHash).to.equal('00'.repeat(32))
    })

    it('tree member cycle: the member is paid, rosterRoot follows the off-chain tree, logHash chains', async () => {
        const tree = twoMemberTree()
        const m = await deployTree(MEMBER_PROG, tree)
        expect(m.rosterRoot).to.equal(tree.root())
        expect(m.sponsorKeyHash).to.equal(keyHash(sponsor.pub))

        // cycle 1: member A (left child at level 0) attests 2231 and is paid
        const tA = T0 + 1n
        const r1 = await memberCycle(m, BigInt(FUNDING), tA, 'A', tree, 2231n)
        expect(r1.plan.halted).to.be.false
        expect(r1.plan.payslot).to.deep.equal({
            slot: -1,
            payoutHex: payoutOf(memberAAddress),
            sats: BigInt(PAY_M),
        })
        expect(addressOf(r1.tx.outputs[1])).to.equal(keeperA.toString())
        expect(addressOf(r1.tx.outputs[2])).to.equal(memberAAddress.toString())
        expect(r1.tx.outputs[2].satoshis).to.equal(PAY_M)
        expect(BigInt(r1.tx.outputs[0].satoshis)).to.equal(
            BigInt(FUNDING) - r1.plan.reward - BigInt(PAY_M)
        )
        tree.set(INDEX_A, leafOf('A', tA))
        const n1 = r1.next as K17Machine
        expect(n1.rosterRoot).to.equal(tree.root())
        expect(n1.rosterSeq).to.equal(0n)
        const log1 = sha256Hex('00'.repeat(32) + encodeCell(2231n))
        expect(n1.logHash).to.equal(log1)
        expect(outputLog(r1.plan.nextState)).to.deep.equal([0n])

        // cycle 2: member B (right child) attests 4242 with a fresh proof
        const tB = T0 + 2n
        const r2 = await memberCycle(
            n1,
            r1.plan.remaining,
            tB,
            'B',
            tree,
            4242n
        )
        expect(addressOf(r2.tx.outputs[2])).to.equal(memberBAddress.toString())
        tree.set(INDEX_B, leafOf('B', tB))
        const n2 = r2.next as K17Machine
        expect(n2.rosterRoot).to.equal(tree.root())
        expect(n2.logHash).to.equal(sha256Hex(log1 + encodeCell(4242n)))

        // cycle 3: member A again in a later round; LASTROUND reads tA
        const r3 = await memberCycle(
            n2,
            r2.plan.remaining,
            T0 + 3n,
            'A',
            tree,
            7n
        )
        expect(outputLog(r3.plan.nextState)).to.deep.equal([0n, 0n, tA])
        tree.set(INDEX_A, leafOf('A', T0 + 3n))
        expect((r3.next as K17Machine).rosterRoot).to.equal(tree.root())
    })

    it('a stale proof against the root before another member was paid is refused (Review Focus 1)', async () => {
        const tree = twoMemberTree()
        const m = await deployTree(MEMBER_PROG, tree)
        const staleB = tree.proof(INDEX_B)
        const r1 = await memberCycle(m, BigInt(FUNDING), T0 + 1n, 'A', tree, 1n)
        tree.set(INDEX_A, leafOf('A', T0 + 1n))
        const n1 = r1.next as K17Machine
        const freshB = tree.proof(INDEX_B)
        expect(staleB.proof).to.not.equal(freshB.proof)

        // the keeper's planner refuses it (the VM says verify_failed) ...
        await expect(
            memberCycle(n1, r1.plan.remaining, T0 + 2n, 'B', tree, 2n, staleB)
        ).to.be.rejectedWith(/rejected/)
        // ... and so does the script interpreter: an honest cycle with the
        // fresh proof verifies, the same transaction with the stale proof
        // does not.
        const honest = await memberCycle(
            n1,
            r1.plan.remaining,
            T0 + 2n,
            'B',
            tree,
            2n
        )
        expect(honest.tx.verifyInputScript(0).success).to.equal(true)
        tamperPush(honest.tx, 0, freshB.proof, staleB.proof)
        expectScriptRefused(honest.tx)
    })

    it('the same member cannot be paid twice in one round (Review Focus 3)', async () => {
        // ROUND from the witness only to build the attack; real programs
        // derive ROUND from TIME.
        const prog = assemble([
            'MEMBER',
            'DROP',
            'LIT',
            PAY_M,
            'IN',
            'PAYLEAF',
            'YIELD',
            'LIT',
            0,
            'IF',
            0,
        ])
        const tree = twoMemberTree()
        const m = await deployTree(prog, tree)
        const r1 = await cycle(
            m,
            BigInt(FUNDING),
            T0 + 1n,
            keeperA,
            {},
            [5n],
            NO_SIG,
            {},
            tree.proof(INDEX_A)
        )
        tree.set(INDEX_A, leafOf('A', 5n))
        const n1 = r1.next as K17Machine
        expect(n1.rosterRoot).to.equal(tree.root())
        const again = (round: bigint) =>
            cycle(
                n1,
                r1.plan.remaining,
                T0 + 2n,
                keeperA,
                {},
                [round],
                NO_SIG,
                {},
                tree.proof(INDEX_A)
            )
        // round 5 again (and an older round) is refused by the planner
        await expect(again(5n)).to.be.rejectedWith(/rejected/)
        await expect(again(4n)).to.be.rejectedWith(/rejected/)
        // and by the interpreter when the witness of an honest round-6
        // cycle is swapped for round 5
        const honest = await again(6n)
        tamperPush(honest.tx, 0, encodeCell(6n), encodeCell(5n))
        expectScriptRefused(honest.tx)
    })

    it('interpreter refuses a flipped proof byte, a wrong leafIndex and an index past the tree', async () => {
        const honest = async () => {
            const tree = twoMemberTree()
            const m = await deployTree(MEMBER_PROG, tree)
            const r = await memberCycle(
                m,
                BigInt(FUNDING),
                T0 + 1n,
                'A',
                tree,
                3n
            )
            expect(r.tx.verifyInputScript(0).success).to.equal(true)
            return { r, proof: tree.proof(INDEX_A).proof }
        }
        /** Minimal script-number push of a leaf index, as hex. */
        const indexPush = (index: number): string =>
            int2ByteString(BigInt(index))

        const flipped = await honest()
        const badProof =
            flipped.proof.slice(0, 64) +
            (parseInt(flipped.proof.slice(64, 66), 16) ^ 1)
                .toString(16)
                .padStart(2, '0') +
            flipped.proof.slice(66)
        tamperPush(flipped.r.tx, 0, flipped.proof, badProof)
        expectScriptRefused(flipped.r.tx)

        const wrongIndex = await honest()
        tamperPush(wrongIndex.r.tx, 0, indexPush(INDEX_A), indexPush(INDEX_B))
        expectScriptRefused(wrongIndex.r.tx)

        // INDEX_A + 2^16 has the same low 16 bits, so the proof walk alone
        // would accept it; the range check must refuse it.
        const pastTree = await honest()
        tamperPush(
            pastTree.r.tx,
            0,
            indexPush(INDEX_A),
            indexPush(INDEX_A + 65536)
        )
        expectScriptRefused(pastTree.r.tx)
    })

    it('OUTH chains logHash with the root unchanged; LASTROUND without MEMBER faults and refunds', async () => {
        const tree = twoMemberTree()
        const m = await deployTree(
            assemble(['LIT', 7, 'OUTH', 'YIELD', 'LASTROUND', 'HALT']),
            tree
        )
        const r1 = await cycle(m, BigInt(FUNDING), T0 + 1n, keeperA)
        const n1 = r1.next as K17Machine
        expect(n1.logHash).to.equal(sha256Hex('00'.repeat(32) + encodeCell(7n)))
        expect(n1.rosterRoot).to.equal(tree.root())
        const r2 = await cycle(n1, r1.plan.remaining, T0 + 2n, keeperA)
        expect(r2.plan.halted).to.be.true
        expect(addressOf(r2.tx.outputs[0])).to.equal(
            beneficiaryAddress.toString()
        )
    })
})
