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
import { K17Machine } from '../src/contracts/k17Machine'
import { assemble, Op, OUT_MAX, HAS_OPERAND } from '../src/k17/isa'
import { outputLog, run, initialState, hashCell, whoOf } from '../src/k17/vm'
import {
    fibonacciProgram,
    countdownProgram,
    heartbeatProgram,
    factoringBountyProgram,
    twoStageJobProgram,
} from '../src/k17/programs'
import {
    addrOf,
    bindCycleBuilder,
    newMachine,
    planCycle,
    CyclePlan,
    CycleOverrides,
} from '../src/keeper'
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

/** Deploy a machine for `prog` and return the live instance. */
async function deploy(prog: string): Promise<K17Machine> {
    const m = newMachine(prog, ECON, T0)
    await m.connect(getDefaultSigner())
    await m.deploy(FUNDING)
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
 */
async function cycle(
    m: K17Machine,
    value: bigint,
    lockTime: bigint,
    keeper: bsv.Address,
    overrides: CycleOverrides & {
        witnessHex?: string
        keeperArg?: bsv.Address
    } = {},
    witness: bigint[] = []
): Promise<CycleResult> {
    const plan = planCycle(m, value, lockTime, keeper, witness)
    const opts = bindCycleBuilder(m, plan, keeper, lockTime, overrides)
    const { tx, atInputIndex } = await m.methods.step(
        addrOf(overrides.keeperArg ?? keeper),
        toByteString(overrides.witnessHex ?? plan.witnessHex),
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
        // IN and VERIFY make a transaction invalid by design, so they are
        // left out of the random op set; everything else must always verify.
        const ops = (
            Object.values(Op).filter((v) => typeof v === 'number') as number[]
        ).filter((v) => v !== Op.IN && v !== Op.VERIFY)
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
})
