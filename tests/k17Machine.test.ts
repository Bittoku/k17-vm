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
    treeConsortiumSmokeProgram,
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
    DEAD_MAN_FLOOR,
} from '../src/keeper'
import {
    EMPTY_HASHES,
    SparseMerkleTree,
    decodeLeafPre,
    encodeLeafPre,
} from '../src/k17/smt'
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
    signAdmission,
    signRemoval,
    Attester,
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
 * Roster-tree settings for the differential fuzz: a seeded tree with two
 * members (fixed key hashes and payouts, at leaves 5 and 6) and a non-zero
 * sponsor key hash, so the fuzz runs on a populated tree, not the empty one.
 */
const FUZZ_TREE = {
    rosterRoot: new SparseMerkleTree(
        new Map([
            [5, encodeLeafPre('c1'.repeat(32), '21'.repeat(20), 0n)],
            [6, encodeLeafPre('c2'.repeat(32), '22'.repeat(20), 7n)],
        ])
    ).root(),
    sponsorKeyHash: 'cd'.repeat(32),
}

/**
 * Most candidates a test tries when it searches for a tag or reading whose
 * signatures give unique pushes. A search that needs more throws, so a
 * key or payout change cannot make a test loop forever.
 */
const SEARCH_CAP = 1000

/**
 * Print a size measurement when K17_SIZES is set in the environment, so a
 * normal test run stays quiet. Input: message. Output: none.
 */
function logSize(message: string): void {
    if (process.env.K17_SIZES) console.log(message)
}

/**
 * Deploy a machine for `prog` and return the live instance.
 * Input: program hex; optional funding (sats), initial memory image hex,
 * roster-tree settings (rosterRoot, sponsorKeyHash; default the empty tree
 * and no sponsor) and economics (default ECON, no dead-man).
 * Output: the deployed contract instance.
 */
async function deploy(
    prog: string,
    funding: number = FUNDING,
    initialMemHex?: string,
    tree: { rosterRoot?: string; sponsorKeyHash?: string } = {},
    econ: typeof ECON & { deadMan?: bigint; allowShortDeadMan?: boolean } = ECON
): Promise<K17Machine> {
    const m = newMachine(
        prog,
        econ,
        T0,
        rosterOf(),
        initialMemHex,
        TEST_ID,
        tree
    )
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
            70n,
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
        // every cycle 70 s apart (MIN_STEP is 60) -> reward 170 each
        expect(paid).to.equal(170n * BigInt(cycles))

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
        const { last } = await runToHalt(m, K17Machine.MIN_STEP, keeperA)
        expect(outputLog(last.plan.nextState)).to.deep.equal([4n, 3n, 2n, 1n])
    })

    it('liveness Dutch auction: reward grows with silence, caps, and a slow keeper takes over', async () => {
        const m = await deploy(heartbeatProgram())
        let value = BigInt(FUNDING)

        // Keeper A steps as early as a live cycle may (MIN_STEP = 60 s
        // after deployment): reward = rewardMin + 60.
        let r = await cycle(m, value, T0 + 60n, keeperA)
        expect(r.plan.reward).to.equal(160n)
        value = r.plan.remaining

        // Keeper A again after 60 s: reward = 100 + 60.
        r = await cycle(r.next as K17Machine, value, T0 + 120n, keeperA)
        expect(r.plan.reward).to.equal(160n)
        expect(
            r.tx.outputs[1].script.toAddress(keeperA.network).toString()
        ).to.equal(keeperA.toString())
        value = r.plan.remaining

        // Keeper A disappears. Keeper B only steps once the reward reaches 300.
        r = await cycle(r.next as K17Machine, value, T0 + 120n + 200n, keeperB)
        expect(r.plan.reward).to.equal(300n)
        expect(
            r.tx.outputs[1].script.toAddress(keeperB.network).toString()
        ).to.equal(keeperB.toString())
        value = r.plan.remaining

        // Long silence: capped at rewardMax.
        r = await cycle(
            r.next as K17Machine,
            value,
            T0 + 320n + 100_000n,
            keeperB
        )
        expect(r.plan.reward).to.equal(500n)

        // TIME recorded each cycle's nLockTime, K/4 loop iterations per cycle.
        const per = K17Machine.K / 4
        const log = outputLog(r.plan.nextState)
        const expected: bigint[] = []
        for (const t of [T0 + 60n, T0 + 120n, T0 + 320n, T0 + 100_320n]) {
            for (let i = 0; i < per; i++) expected.push(t)
        }
        expect(log).to.deep.equal(expected)
    })

    it('rejects a keeper who takes one satoshi too many', async () => {
        const m = await deploy(heartbeatProgram())
        const plan = planCycle(m, BigInt(FUNDING), T0 + 300n)
        await expect(
            cycle(m, BigInt(FUNDING), T0 + 300n, keeperA, {
                reward: plan.reward + 1n,
            })
        ).to.be.rejectedWith(/outputs mismatch|script failed/)
    })

    it('rejects a tampered next state', async () => {
        const m = await deploy(fibonacciProgram(3))
        const plan = planCycle(m, BigInt(FUNDING), T0 + 300n)
        const forged = (plan.next as K17Machine).next()
        forged.pc = forged.pc + 1n
        await expect(
            cycle(m, BigInt(FUNDING), T0 + 300n, keeperA, { next: forged })
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
            cycle(next, r.plan.remaining, T0 + 200n, keeperA, {
                sequence: 0xffffffff,
            })
        ).to.be.rejectedWith(/nSequence|script failed/)
    })

    it('rejects a machine that is not input 0 (output-sharing / sibling double-spend shape)', async () => {
        const m = await deploy(heartbeatProgram())
        await expect(
            cycle(m, BigInt(FUNDING), T0 + 300n, keeperA, {
                leadingFeeInputs: 1,
            })
        ).to.be.rejectedWith(/machine must be input 0/)
    })

    it('a fault releases funds to the beneficiary instead of freezing them', async () => {
        // DROP on an empty stack is a fault on the very first instruction.
        const m = await deploy(assemble(['DROP', 'LIT', 1, 'OUT', 'HALT']))
        const r = await cycle(m, BigInt(FUNDING), T0 + 60n, keeperA)
        expect(r.plan.halted).to.be.true
        expect(
            r.tx.outputs[0].script
                .toAddress(beneficiaryAddress.network)
                .toString()
        ).to.equal(beneficiaryAddress.toString())
    })

    /**
     * Every opcode value of the ISA except MEMBER, ATTESTM, PAYLEAF, ADMIT
     * and REMOVE. Each of those needs witness data (a tree proof, a key or
     * a signature), so a random program would always stall at it as
     * need_witness or verify_failed, and no cycle could be built. OUTH and
     * LASTROUND stay in: LASTROUND without a bound member is a fault, and
     * the fuzz must show that this is a clean halt and refund on chain.
     */
    const ALL_OPS = (
        Object.values(Op).filter((v) => typeof v === 'number') as number[]
    ).filter(
        (v) =>
            v !== Op.MEMBER &&
            v !== Op.ATTESTM &&
            v !== Op.PAYLEAF &&
            v !== Op.ADMIT &&
            v !== Op.REMOVE
    )

    /**
     * Differential fuzz: deploy 12 random 24-instruction programs over `ops`
     * with memory image `mem` on the populated FUZZ_TREE roster and step
     * each up to 6 cycles; every cycle goes through cycle(), so every one
     * must pass verifyInputScript. After every cycle (in the VM's next
     * state, and in the contract's next state when the machine is alive),
     * rosterRoot and rosterSeq must equal their deployed values (the op set
     * has no instruction that may change them), and logHash must still be zero
     * unless the program contains an OUTH instruction (a static check: the
     * fuzz does not trace which instructions ran).
     * With `deadMan` > 0 the machines are deployed with that dead-man
     * interval and each cycle advances the clock by MIN_STEP or, at
     * random, by deadMan, so the dead-man halt also meets random mid-run
     * states (v3.1). Each program then starts with `IN DUP VERIFY`, and
     * each cycle carries 0 to 2 random witness cells in 0..2, so IN can
     * block, VERIFY can fail, or both pass and leave a cell for the random
     * part. A cycle the planner refuses (missing or rejected witness) is
     * retried with no witness at lastTime + deadMan, which must be a
     * dead-man halt that verifies. These choices use the high bits of the
     * generator (`hi`); `rnd` uses the low bits, as before, so the programs
     * of the fuzz runs without a dead-man are unchanged.
     * Input: op set, memory image, PRNG seed, optional deadMan (default
     * 0n, off). Output: the number of dead-man halts and how many of them
     * freed a blocked machine (throws on a cycle that does not verify or a
     * tree field that changed).
     */
    async function fuzz(
        ops: number[],
        mem: string,
        seed: number,
        deadMan = 0n
    ) {
        const rnd = (n: number) => {
            seed = (seed * 1103515245 + 12345) & 0x7fffffff
            return seed % n
        }
        // The low bits of this generator have short periods; use the high
        // bits for the dead-man choices.
        const hi = (n: number) => {
            seed = (seed * 1103515245 + 12345) & 0x7fffffff
            return (seed >>> 16) % n
        }
        let deadManHalts = 0
        let blockedEscapes = 0
        for (let p = 0; p < 12; p++) {
            // dead-man runs: IN DUP VERIFY first, so witnesses matter
            const bytes: number[] =
                deadMan > 0n ? [Op.IN, Op.DUP, Op.VERIFY] : []
            let hasOuth = false
            for (let i = 0; i < 24; i++) {
                const op = ops[rnd(ops.length)]
                bytes.push(op)
                if (op === Op.OUTH) hasOuth = true
                if (HAS_OPERAND.has(op)) {
                    const operand = rnd(40) // small: addresses, offsets, literals
                    bytes.push(operand, 0, 0, 0)
                }
            }
            const prog = Buffer.from(bytes).toString('hex')
            const m = await deploy(prog, FUNDING, mem, FUZZ_TREE, {
                ...ECON,
                deadMan,
                allowShortDeadMan: true,
            })
            expect(m.rosterRoot).to.equal(FUZZ_TREE.rosterRoot)
            expect(m.sponsorKeyHash).to.equal(FUZZ_TREE.sponsorKeyHash)
            let cur: K17Machine | undefined = m
            let value = BigInt(FUNDING)
            let t = T0
            for (let c = 0; c < 6 && cur; c++) {
                t += deadMan > 0n && hi(3) === 0 ? deadMan : K17Machine.MIN_STEP
                let r: CycleResult
                if (deadMan > 0n) {
                    const witness = Array.from({ length: hi(3) }, () =>
                        BigInt(hi(3))
                    )
                    try {
                        r = await cycle(cur, value, t, keeperA, {}, witness)
                    } catch (e) {
                        if (!/needs a witness|witness rejected/.test(`${e}`)) {
                            throw e
                        }
                        // Blocked: only the dead-man can move it now.
                        t = cur.lastTime + deadMan
                        r = await cycle(cur, value, t, keeperA)
                        expect(r.plan.deadManHalt).to.be.true
                        blockedEscapes++
                    }
                } else {
                    r = await cycle(cur, value, t, keeperA)
                }
                if (r.plan.deadManHalt) deadManHalts++
                value = r.plan.remaining
                cur = r.next
                // The VM's next state, halted or not (most random programs
                // fault within a cycle or two) ...
                const s = r.plan.nextState
                expect(s.rosterRoot).to.equal(FUZZ_TREE.rosterRoot)
                expect(s.rosterSeq).to.equal(0n)
                if (!hasOuth) expect(s.logHash).to.equal('00'.repeat(32))
                // ... and the state output the contract accepted, when alive.
                if (cur) {
                    expect(cur.rosterRoot).to.equal(FUZZ_TREE.rosterRoot)
                    expect(cur.rosterSeq).to.equal(0n)
                    if (!hasOuth) {
                        expect(cur.logHash).to.equal('00'.repeat(32))
                    }
                }
            }
        }
        return { deadManHalts, blockedEscapes }
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

    it('differential fuzz with a dead-man: random states, IN and VERIFY included, halt cleanly when it fires', async () => {
        // IN and VERIFY join the op set: a cycle they block is freed by a
        // dead-man cycle, which needs no witness. SIGVERIFY, ATTEST and
        // ENDORSE stay out (the fuzz supplies no signature).
        const ops = ALL_OPS.filter(
            (v) => v !== Op.SIGVERIFY && v !== Op.ATTEST && v !== Op.ENDORSE
        )
        const { deadManHalts, blockedEscapes } = await fuzz(
            ops,
            FULL_ROSTER_MEM,
            777,
            DEAD_MAN_FLOOR
        )
        if (process.env.K17_SIZES) {
            console.log(
                `      dead-man halts: ${deadManHalts}, of which freed a blocked machine: ${blockedEscapes}`
            )
        }
        expect(deadManHalts).to.be.greaterThan(0)
        expect(blockedEscapes).to.be.greaterThan(0)
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
            t += K17Machine.MIN_STEP
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
        const r1 = await cycle(m, BigInt(FUNDING), T0 + 60n, keeperA)
        expect(r1.plan.bounty).to.equal(0n)
        expect(r1.plan.nextState.pc).to.equal(1n)
        // Cycle 2: solver B supplies p, q and runs the whole stage atomically.
        const r2 = await cycle(
            r1.next as K17Machine,
            r1.plan.remaining,
            T0 + 120n,
            keeperB,
            {},
            [BigInt(P), BigInt(Q)]
        )
        expect(r2.plan.halted).to.be.true
        expect(r2.plan.bounty).to.equal(BigInt(BOUNTY1))
        expect(r2.plan.reward).to.equal(BigInt(BOUNTY1) + 160n)
        expect(outputLog(r2.plan.nextState)).to.deep.equal([
            BigInt(Q),
            BigInt(P),
        ])
        expect(
            r2.tx.outputs[1].script.toAddress(keeperB.network).toString()
        ).to.equal(keeperB.toString())
        expect(BigInt(r2.tx.outputs[1].satoshis)).to.equal(
            BigInt(BOUNTY1) + 160n
        )
        expect(
            r2.tx.outputs[0].script
                .toAddress(beneficiaryAddress.network)
                .toString()
        ).to.equal(beneficiaryAddress.toString())
    })

    it('factoring bounty: wrong, overflowing and missing witnesses are rejected', async () => {
        const m = await deploy(factoringBountyProgram(N, BOUNTY1))
        const r1 = await cycle(m, BigInt(FUNDING), T0 + 60n, keeperA)
        const staged = r1.next as K17Machine
        const v = r1.plan.remaining
        // Off-chain planner refuses a wrong factorisation.
        await expect(
            cycle(staged, v, T0 + 120n, keeperB, {}, [3n, 5n])
        ).to.be.rejectedWith(/witness rejected by VERIFY/)
        // Factors that only match modulo 2^32 are refused by the 16-bit guards.
        await expect(
            cycle(staged, v, T0 + 120n, keeperB, {}, [
                BigInt(N + 2 ** 32) / 1n,
                1n,
            ])
        ).to.be.rejectedWith(/witness rejected by VERIFY/)
        // No witness at all: the stage cannot be stepped by a plain keeper.
        await expect(cycle(staged, v, T0 + 120n, keeperA)).to.be.rejectedWith(
            /needs a witness/
        )
        // On-chain: plan with the right witness, but broadcast a wrong one.
        await expect(
            cycle(
                staged,
                v,
                T0 + 120n,
                keeperB,
                { witnessHex: '0300000005000000' },
                [BigInt(P), BigInt(Q)]
            )
        ).to.be.rejectedWith(/verify failed/)
        // On-chain: plan with the right witness, but broadcast none.
        await expect(
            cycle(staged, v, T0 + 120n, keeperB, { witnessHex: '' }, [
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
        let r = await cycle(m, value, T0 + 60n, keeperA) // leading YIELD
        value = r.plan.remaining
        r = await cycle(r.next as K17Machine, value, T0 + 120n, keeperA, {}, [
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
        let r = await cycle(machine, value, T0 + 180n, keeperB, {}, [
            1n,
            commitment,
        ])
        expect(r.plan.bounty).to.equal(0n)
        value = r.plan.remaining
        const revealStage = r.next as K17Machine

        // front-runner A sees x in the mempool and tries to reveal as itself
        await expect(
            cycle(revealStage, value, T0 + 240n, keeperA, {}, [0n, X])
        ).to.be.rejectedWith(/witness rejected by VERIFY/)
        // front-runner A copies B's exact transaction but swaps the payee
        await expect(
            cycle(
                revealStage,
                value,
                T0 + 240n,
                keeperB,
                { keeperArg: keeperA },
                [0n, X]
            )
        ).to.be.rejectedWith(/verify failed/)
        // B reveals and collects
        r = await cycle(revealStage, value, T0 + 240n, keeperB, {}, [0n, X])
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
        let r = await cycle(machine, value, T0 + 600n, keeperA, {}, [
            1n,
            0xbadn,
        ])
        value = r.plan.remaining
        // B cannot overwrite while the commit is fresh, and cannot reveal against it
        const commitment = hashCell(X ^ whoOf(keeperB.toObject().hash))
        await expect(
            cycle(r.next as K17Machine, value, T0 + 660n, keeperB, {}, [
                1n,
                commitment,
            ])
        ).to.be.rejectedWith(/witness rejected by VERIFY/)
        await expect(
            cycle(r.next as K17Machine, value, T0 + 660n, keeperB, {}, [0n, X])
        ).to.be.rejectedWith(/witness rejected by VERIFY/)
        // a plain keeper cannot step stage 2 at all (needs a selector witness)
        await expect(
            cycle(r.next as K17Machine, value, T0 + 660n, keeperA)
        ).to.be.rejectedWith(/needs a witness/)
        // after the TTL, B overwrites the commit and reveals in the next transaction
        r = await cycle(
            r.next as K17Machine,
            value,
            T0 + 600n + BigInt(COMMIT_TTL),
            keeperB,
            {},
            [1n, commitment]
        )
        value = r.plan.remaining
        r = await cycle(
            r.next as K17Machine,
            value,
            T0 + 660n + BigInt(COMMIT_TTL),
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
        const { last } = await runToHalt(m, K17Machine.MIN_STEP, keeperA)
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
        let r = await cycle(m, value, T0 + 60n, keeperA)
        value = r.plan.remaining
        // attester B signs (tag=5, value=2231); keeper A relays it
        const sig = signReading(attesterB, 5n, 2231n)
        r = await cycle(
            r.next as K17Machine,
            value,
            T0 + 120n,
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
        const r = await cycle(m, value, T0 + 60n, keeperA)
        value = r.plan.remaining
        const next = r.next as K17Machine
        const good = signReading(attesterB, 5n, 2231n)

        // signed by roster slot 0, program demands slot 1
        await expect(
            cycle(
                next,
                value,
                T0 + 120n,
                keeperA,
                {},
                [5n, 2231n],
                signReading(attesterA, 5n, 2231n)
            )
        ).to.be.rejectedWith(/rejected by VERIFY, SIGVERIFY/)
        // reading altered after signing
        await expect(
            cycle(next, value, T0 + 120n, keeperA, {}, [5n, 2232n], good)
        ).to.be.rejectedWith(/rejected by VERIFY, SIGVERIFY/)
        // old signature replayed under a new tag
        await expect(
            cycle(next, value, T0 + 120n, keeperA, {}, [6n, 2231n], good)
        ).to.be.rejectedWith(/rejected by VERIFY, SIGVERIFY/)
        // no signature at all
        await expect(
            cycle(next, value, T0 + 120n, keeperA, {}, [5n, 2231n])
        ).to.be.rejectedWith(/needs a witness/)
        // the plan is honest but the unlocking script carries a bad signature:
        // the script interpreter itself must refuse
        await expect(
            cycle(
                next,
                value,
                T0 + 120n,
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
        let r = await cycle(m, value, T0 + 60n, keeperA)
        value = r.plan.remaining
        r = await cycle(
            r.next as K17Machine,
            value,
            T0 + 120n,
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
        const r = await cycle(m, BigInt(FUNDING), T0 + 60n, keeperA)
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
            const r = await cycle(m, BigInt(FUNDING), T0 + 60n, keeper)
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
        // FUNDING 1000, auction reward 160 at T0+60.
        const small = 1000
        const pay = (n: number) =>
            deploy(
                assemble(['LIT', n, 'LIT', 3, 'PAYSLOT', 'YIELD']),
                small,
                SLOT3_MEM
            )
        // 839 leaves room for the full reward and one satoshi.
        let r = await cycle(await pay(839), BigInt(small), T0 + 60n, keeperA)
        expect(r.plan.reward).to.equal(160n)
        expect(r.tx.outputs[0].satoshis).to.equal(1)
        expect(r.tx.outputs[2].satoshis).to.equal(839)
        // 950: the reward shrinks to 49, the slot is paid in full.
        r = await cycle(await pay(950), BigInt(small), T0 + 60n, keeperA)
        expect(r.plan.reward).to.equal(49n)
        expect(r.tx.outputs[0].satoshis).to.equal(1)
        expect(r.tx.outputs[2].satoshis).to.equal(950)
        // 999: no reward at all (no keeper output); payout is output 1.
        r = await cycle(await pay(999), BigInt(small), T0 + 60n, keeperA)
        expect(r.plan.reward).to.equal(0n)
        expect(r.plan.halted).to.be.false
        expect(r.tx.outputs[0].satoshis).to.equal(1)
        expect(addressOf(r.tx.outputs[1])).to.equal(payee.toString())
        expect(r.tx.outputs[1].satoshis).to.equal(999)
        // 1000 cannot leave one satoshi: fault, payout dropped, refund.
        const f = await cycle(await pay(1000), BigInt(small), T0 + 60n, keeperA)
        expectFaultRefund(f, BigInt(small))
        expect(f.plan.remaining).to.equal(840n)
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
        const r = await cycle(m, BigInt(FUNDING), T0 + 60n, keeperA)
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
        const r = await cycle(m, BigInt(FUNDING), T0 + 60n, keeperA)
        expectFaultRefund(r, BigInt(FUNDING))
    })

    it('PAYSLOT on an empty or out-of-range slot faults and refunds the beneficiary', async () => {
        for (const slot of [2, 8]) {
            const m = await deploy(
                assemble(['LIT', 700, 'LIT', slot, 'PAYSLOT', 'YIELD']),
                FUNDING,
                SLOT3_MEM
            )
            const r = await cycle(m, BigInt(FUNDING), T0 + 60n, keeperA)
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
        const r = await cycle(m, BigInt(FUNDING), T0 + 60n, keeperA)
        expectFaultRefund(r, BigInt(FUNDING))
        // a malformed (underflowing) second PAYSLOT also drops the payout
        const bad = await deploy(
            assemble(['LIT', 1, 'LIT', 3, 'PAYSLOT', 'PAYSLOT', 'YIELD']),
            FUNDING,
            SLOT3_MEM
        )
        const rb = await cycle(bad, BigInt(FUNDING), T0 + 60n, keeperA)
        expectFaultRefund(rb, BigInt(FUNDING))
    })

    it('STORE into the roster faults and refunds; STORE below it advances', async () => {
        const below = await deploy(
            assemble(['LIT', 7, 'LIT', 151, '!', 'YIELD'])
        )
        const r1 = await cycle(below, BigInt(FUNDING), T0 + 60n, keeperA)
        expect(r1.plan.halted).to.be.false
        const mem = (r1.next as K17Machine).mem
        expect(mem.slice(151 * 8, 152 * 8)).to.equal(encodeCell(7n))

        const into = await deploy(
            assemble(['LIT', 7, 'LIT', 152, '!', 'YIELD'])
        )
        const r2 = await cycle(into, BigInt(FUNDING), T0 + 60n, keeperA)
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
            T0 + 60n,
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
            T0 + 120n,
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
            T0 + 60n,
            keeperA,
            [],
            ATTEST0_SIG(m.instanceId),
            {
                attestKey: sponsor.pub,
            }
        )
        await expect(
            sendPlan(m, plan, T0 + 60n, pubKeyBytes(sponsor.pub).slice(0, 766))
        ).to.be.rejectedWith(/key must be 384 bytes/)
        const r = await cycle(
            m,
            BigInt(FUNDING),
            T0 + 60n,
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
            T0 + 60n,
            keeperA,
            [],
            ATTEST0_SIG(m.instanceId),
            {
                attestKey: sponsor.pub,
            }
        )
        await expect(
            sendPlan(m, plan, T0 + 60n, pubKeyBytes(landowner.pub))
        ).to.be.rejectedWith(/key not in roster slot/)
    })

    it('ATTEST then ENDORSE in one cycle faults and refunds (v3.1)', async () => {
        // prettier-ignore
        const both = assemble([
            'LIT', 5, 'LIT', 2231, 'LIT', 0, 'ATTEST',
            'LIT', TAG_E, 'LIT', 0, 'LIT', 1, 'ENDORSE', 'YIELD',
        ])
        const m = await deploy(both, FUNDING, SPONSOR_MEM)
        // The ATTEST verifies; the ENDORSE is a second signature in the
        // cycle, so the VM and the contract halt and refund.
        const r = await cycle(
            m,
            BigInt(FUNDING),
            T0 + 60n,
            keeperA,
            {},
            [],
            ATTEST0_SIG(m.instanceId),
            { attestKey: sponsor.pub }
        )
        expect(r.plan.halted).to.be.true
        expect(r.plan.reward).to.equal(160n)
        expect(addressOf(r.tx.outputs[0])).to.equal(
            beneficiaryAddress.toString()
        )
        expect(BigInt(r.tx.outputs[0].satoshis)).to.equal(
            BigInt(FUNDING) - 160n
        )
        expect(addressOf(r.tx.outputs[1])).to.equal(keeperA.toString())
        // slot 1 was not written
        expect(readSlot(r.plan.nextState.mem, 1).empty).to.be.true
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
                T0 + 60n,
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
            T0 + 60n,
            keeperA,
            [],
            endorsementFor(1n, m.instanceId),
            ENDORSE_KEYS
        )
        await expect(sendPlan(m, plan, T0 + 60n)).to.be.rejectedWith(
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
            T0 + 60n,
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
            T0 + 60n,
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
                T0 + 60n,
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
            T0 + 60n,
            keeperA,
            [],
            ATTEST0_SIG(idA),
            keys
        )
        await expect(sendPlan(b, plan, T0 + 60n)).to.be.rejectedWith(
            /signature check failed/
        )
        // and B accepts its own signature
        const r = await cycle(
            b,
            BigInt(FUNDING),
            T0 + 60n,
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
            0n, // deadMan: off
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
        const r = await cycle(m, BigInt(FUNDING), T0 + 60n, keeperA)
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
                T0 + 60n,
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
                T0 + 60n,
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
            if (tag - 5 >= SEARCH_CAP) throw new Error('no ATTEST tag found')
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
            T0 + 60n,
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
     * key hash. Input: program hex, off-chain tree, optional funding (sats,
     * default FUNDING) and initial memory image hex (default zeroed).
     * Output: live instance.
     */
    async function deployTree(
        prog: string,
        tree: SparseMerkleTree,
        funding: number = FUNDING,
        initialMemHex?: string
    ): Promise<K17Machine> {
        const m = newMachine(
            prog,
            ECON,
            T0,
            undefined,
            initialMemHex,
            TEST_ID,
            {
                rosterRoot: tree.root(),
                sponsorKeyHash: keyHash(sponsor.pub),
            }
        )
        await m.connect(getDefaultSigner())
        await m.deploy(funding)
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

    it("the contract's empty leaf hash is the off-chain tree's; a new machine starts on the empty tree", () => {
        expect(K17Machine.EMPTY_HASH).to.equal(EMPTY_HASHES[0])
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
        const tA = T0 + 60n
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
        const tB = T0 + 120n
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
            T0 + 180n,
            'A',
            tree,
            7n
        )
        expect(outputLog(r3.plan.nextState)).to.deep.equal([0n, 0n, tA])
        tree.set(INDEX_A, leafOf('A', T0 + 180n))
        expect((r3.next as K17Machine).rosterRoot).to.equal(tree.root())
    })

    it('a stale proof against the root before another member was paid is refused (Review Focus 1)', async () => {
        const tree = twoMemberTree()
        const m = await deployTree(MEMBER_PROG, tree)
        const staleB = tree.proof(INDEX_B)
        const r1 = await memberCycle(
            m,
            BigInt(FUNDING),
            T0 + 60n,
            'A',
            tree,
            1n
        )
        tree.set(INDEX_A, leafOf('A', T0 + 60n))
        const n1 = r1.next as K17Machine
        const freshB = tree.proof(INDEX_B)
        expect(staleB.proof).to.not.equal(freshB.proof)

        // the keeper's planner refuses it (the VM says verify_failed) ...
        await expect(
            memberCycle(n1, r1.plan.remaining, T0 + 120n, 'B', tree, 2n, staleB)
        ).to.be.rejectedWith(/rejected/)
        // ... and so does the script interpreter: an honest cycle with the
        // fresh proof verifies, the same transaction with the stale proof
        // does not.
        const honest = await memberCycle(
            n1,
            r1.plan.remaining,
            T0 + 120n,
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
            T0 + 60n,
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
                T0 + 120n,
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
                T0 + 60n,
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
        const r1 = await cycle(m, BigInt(FUNDING), T0 + 60n, keeperA)
        const n1 = r1.next as K17Machine
        expect(n1.logHash).to.equal(sha256Hex('00'.repeat(32) + encodeCell(7n)))
        expect(n1.rosterRoot).to.equal(tree.root())
        const r2 = await cycle(n1, r1.plan.remaining, T0 + 120n, keeperA)
        expect(r2.plan.halted).to.be.true
        expect(addressOf(r2.tx.outputs[0])).to.equal(
            beneficiaryAddress.toString()
        )
    })
    // ---- PAYLEAF faults and payout accounting (mirror the PAYSLOT tests) ----

    /**
     * Run one cycle of `prog` on a fresh tree machine, binding member A with
     * its proof from `tree` (or no proof when `bind` is false).
     * Input: program hex, off-chain tree, lock time, funding (sats), memory
     * image hex, whether to send member A's proof. Output: the cycle result.
     */
    async function payleafCycle(
        prog: string,
        tree: SparseMerkleTree,
        lockTime: bigint = T0 + 60n,
        funding: number = FUNDING,
        mem?: string,
        bind = true
    ): Promise<CycleResult> {
        const m = await deployTree(prog, tree, funding, mem)
        return cycle(
            m,
            BigInt(funding),
            lockTime,
            keeperA,
            {},
            [],
            NO_SIG,
            {},
            bind ? tree.proof(INDEX_A) : undefined
        )
    }

    it('PAYLEAF 0 faults and refunds the beneficiary, no payout', async () => {
        const r = await payleafCycle(
            assemble(['MEMBER', 'DROP', 'LIT', 0, 'TIME', 'PAYLEAF', 'YIELD']),
            twoMemberTree()
        )
        expect(r.plan.treeOp).to.equal('member')
        expectFaultRefund(r, BigInt(FUNDING))
    })

    it('PAYSLOT then PAYLEAF, and PAYLEAF twice, fault and drop the payout', async () => {
        // A filled memory slot (3) and a tree member (A) in one machine.
        // prettier-ignore
        const slotThenLeaf = assemble([
            'LIT', 700, 'LIT', 3, 'PAYSLOT',
            'MEMBER', 'DROP', 'LIT', 500, 'TIME', 'PAYLEAF', 'YIELD',
        ])
        const r1 = await payleafCycle(
            slotThenLeaf,
            twoMemberTree(),
            T0 + 60n,
            FUNDING,
            SLOT3_MEM
        )
        expectFaultRefund(r1, BigInt(FUNDING))
        // prettier-ignore
        const leafTwice = assemble([
            'MEMBER', 'DROP', 'LIT', 500, 'TIME', 'PAYLEAF',
            'LIT', 500, 'TIME', 'PAYLEAF', 'YIELD',
        ])
        const r2 = await payleafCycle(leafTwice, twoMemberTree())
        expectFaultRefund(r2, BigInt(FUNDING))
    })

    it('PAYLEAF without MEMBER faults and refunds', async () => {
        const r = await payleafCycle(
            assemble(['LIT', 500, 'TIME', 'PAYLEAF', 'YIELD']),
            twoMemberTree(),
            T0 + 60n,
            FUNDING,
            undefined,
            false
        )
        expect(r.plan.treeOp).to.equal('none')
        expectFaultRefund(r, BigInt(FUNDING))
    })

    it('PAYLEAF of the whole balance faults: refund, payout dropped, as planCycle predicts', async () => {
        const prog = assemble([
            'MEMBER',
            'DROP',
            'LIT',
            FUNDING,
            'TIME',
            'PAYLEAF',
            'YIELD',
        ])
        const tree = twoMemberTree()
        // planCycle alone, before any transaction: halted, no payout.
        const m = await deployTree(prog, tree)
        const plan = planCycle(
            m,
            BigInt(FUNDING),
            T0 + 60n,
            keeperA,
            [],
            NO_SIG,
            {},
            tree.proof(INDEX_A)
        )
        expect(plan.halted).to.be.true
        expect(plan.payslot).to.be.undefined
        expect(plan.reward).to.equal(160n)
        expect(plan.remaining).to.equal(BigInt(FUNDING) - 160n)
        // The same cycle on chain: the refund layout, no output 2.
        const r = await payleafCycle(prog, tree)
        expectFaultRefund(r, BigInt(FUNDING))
        expect(r.plan.reward).to.equal(plan.reward)
    })

    it('a late keeper cannot shrink the PAYLEAF payout: the reward is clamped to value - 1 - N', async () => {
        // FUNDING 1000, PAYLEAF 800; at T0+300 the auction offers 400
        // (rewardMax 500), but only 1000 - 1 - 800 = 199 is left.
        const small = 1000
        const tree = twoMemberTree()
        const lockTime = T0 + 300n
        const r = await payleafCycle(
            assemble([
                'MEMBER',
                'DROP',
                'LIT',
                800,
                'TIME',
                'PAYLEAF',
                'YIELD',
            ]),
            tree,
            lockTime,
            small
        )
        expect(r.plan.halted).to.be.false
        expect(r.plan.reward).to.equal(199n)
        expect(r.plan.payslot).to.deep.equal({
            slot: -1,
            payoutHex: payoutOf(memberAAddress),
            sats: 800n,
        })
        expect(r.plan.remaining).to.equal(1n)
        expect(r.tx.outputs[0].satoshis).to.equal(1)
        expect(addressOf(r.tx.outputs[1])).to.equal(keeperA.toString())
        expect(r.tx.outputs[1].satoshis).to.equal(199)
        expect(addressOf(r.tx.outputs[2])).to.equal(memberAAddress.toString())
        expect(r.tx.outputs[2].satoshis).to.equal(800)
        tree.set(INDEX_A, leafOf('A', lockTime))
        expect((r.next as K17Machine).rosterRoot).to.equal(tree.root())
    })

    it('PAYLEAF then an unrelated fault keeps the payout', async () => {
        // DROP on the empty stack after PAYLEAF faults, as in the PAYSLOT test.
        const r = await payleafCycle(
            assemble([
                'MEMBER',
                'DROP',
                'LIT',
                700,
                'TIME',
                'PAYLEAF',
                'DROP',
                'YIELD',
            ]),
            twoMemberTree()
        )
        expect(r.plan.halted).to.be.true
        expect(r.plan.payslot?.sats).to.equal(700n)
        expect(r.tx.outputs.length).to.equal(4) // beneficiary, keeper, member, change
        expect(addressOf(r.tx.outputs[0])).to.equal(
            beneficiaryAddress.toString()
        )
        expect(BigInt(r.tx.outputs[0].satoshis)).to.equal(
            BigInt(FUNDING) - r.plan.reward - 700n
        )
        expect(r.plan.remaining).to.equal(
            BigInt(FUNDING) - r.plan.reward - 700n
        )
        expect(addressOf(r.tx.outputs[1])).to.equal(keeperA.toString())
        expect(addressOf(r.tx.outputs[2])).to.equal(memberAAddress.toString())
        expect(r.tx.outputs[2].satoshis).to.equal(700)
    })

    it('planCycle accepts an uppercase leafPre and proof and sends them lowercased', async () => {
        const tree = twoMemberTree()
        const prog = assemble([
            'MEMBER',
            'DROP',
            'LIT',
            700,
            'TIME',
            'PAYLEAF',
            'YIELD',
        ])
        const m = await deployTree(prog, tree)
        const lower = tree.proof(INDEX_A)
        const upper: CycleTree = {
            leafPre: lower.leafPre.toUpperCase(),
            proof: lower.proof.toUpperCase(),
            leafIndex: lower.leafIndex,
        }
        const r = await cycle(
            m,
            BigInt(FUNDING),
            T0 + 60n,
            keeperA,
            {},
            [],
            NO_SIG,
            {},
            upper
        )
        expect(r.plan.halted).to.be.false
        expect(r.plan.leafPre).to.equal(lower.leafPre)
        expect(r.plan.proof).to.equal(lower.proof)
        expect(r.plan.payslot?.sats).to.equal(700n)
    })

    // ---- isolating interpreter tests for the tree asserts ----
    // Each tampered push below leaves the outputs (and so hashOutputs)
    // valid, so only the named tree assert can refuse the transaction.

    /**
     * Flip the low bit of one byte of a hex string.
     * Input: hex, byte index. Output: hex of the same length.
     */
    const flipByte = (hex: string, byteIndex: number): string =>
        hex.slice(0, byteIndex * 2) +
        (parseInt(hex.slice(byteIndex * 2, byteIndex * 2 + 2), 16) ^ 1)
            .toString(16)
            .padStart(2, '0') +
        hex.slice(byteIndex * 2 + 2)

    /**
     * Test-only: build a step transaction from an explicit plan without
     * running the contract's TypeScript body (scrypt-ts `exec: false`) and
     * without scrypt-ts's own verify-and-broadcast step (`partiallySigned:
     * true`; the machine input needs no signature), so a transaction the
     * contract must refuse can still be built and handed to the script
     * interpreter.
     * Input: machine, plan (its halted/next/payslot/remaining decide the
     * outputs), lock time, witness hex for the unlocking script, optional
     * next instance overriding plan.next. Output: the unverified tx.
     */
    async function buildStepTx(
        m: K17Machine,
        plan: CyclePlan,
        lockTime: bigint,
        witnessHex: string,
        next?: K17Machine
    ): Promise<bsv.Transaction> {
        const opts = bindCycleBuilder(m, plan, keeperA, lockTime, { next })
        const { tx } = await m.methods.step(
            addrOf(keeperA),
            toByteString(witnessHex),
            plan.sig.s,
            toByteString(plan.sig.padding),
            toByteString(plan.keyAHex),
            toByteString(plan.keyBHex),
            toByteString(plan.payoutHex),
            toByteString(plan.leafPre),
            toByteString(plan.proof),
            plan.leafIndex,
            { ...opts, exec: false, partiallySigned: true }
        )
        return tx
    }

    it('interpreter: the old-root check alone refuses a tampered proof or leafPre (state unchanged)', async () => {
        const prog = assemble(['MEMBER', 'DROP', 'YIELD'])
        const honest = async () => {
            const tree = twoMemberTree()
            const m = await deployTree(prog, tree)
            const r = await cycle(
                m,
                BigInt(FUNDING),
                T0 + 60n,
                keeperA,
                {},
                [],
                NO_SIG,
                {},
                tree.proof(INDEX_A)
            )
            expect(r.plan.halted).to.be.false
            expect((r.next as K17Machine).rosterRoot).to.equal(tree.root())
            return { r, witness: tree.proof(INDEX_A) }
        }
        const proofTamper = await honest()
        tamperPush(
            proofTamper.r.tx,
            0,
            proofTamper.witness.proof,
            flipByte(proofTamper.witness.proof, 200)
        )
        expectScriptRefused(proofTamper.r.tx)
        const leafTamper = await honest()
        tamperPush(
            leafTamper.r.tx,
            0,
            leafTamper.witness.leafPre,
            flipByte(leafTamper.witness.leafPre, 0)
        )
        expectScriptRefused(leafTamper.r.tx)
    })

    it('interpreter: the tree check still runs when the machine halts (refund layout)', async () => {
        const prog = assemble(['MEMBER', 'DROP', 'DROP'])
        const honest = async () => {
            const tree = twoMemberTree()
            const m = await deployTree(prog, tree)
            const r = await cycle(
                m,
                BigInt(FUNDING),
                T0 + 60n,
                keeperA,
                {},
                [],
                NO_SIG,
                {},
                tree.proof(INDEX_A)
            )
            expect(r.plan.halted).to.be.true
            expect(addressOf(r.tx.outputs[0])).to.equal(
                beneficiaryAddress.toString()
            )
            return { r, witness: tree.proof(INDEX_A) }
        }
        const proofTamper = await honest()
        tamperPush(
            proofTamper.r.tx,
            0,
            proofTamper.witness.proof,
            flipByte(proofTamper.witness.proof, 0)
        )
        expectScriptRefused(proofTamper.r.tx)
        const leafTamper = await honest()
        tamperPush(
            leafTamper.r.tx,
            0,
            leafTamper.witness.leafPre,
            flipByte(leafTamper.witness.leafPre, 40)
        )
        expectScriptRefused(leafTamper.r.tx)
    })

    it("interpreter: ATTESTM refuses member B's key with B's valid signature on A's leaf", async () => {
        const tree = twoMemberTree()
        const m = await deployTree(MEMBER_PROG, tree)
        // pick a reading whose two signatures have distinct, non-empty
        // paddings and distinct s values, so each push is unique
        const sigsFor = (reading: bigint) => ({
            a: signMemberReading(
                attesterA,
                m.instanceId,
                BigInt(TAG_M),
                reading
            ),
            b: signMemberReading(
                attesterB,
                m.instanceId,
                BigInt(TAG_M),
                reading
            ),
        })
        let reading = 11n
        let sigs = sigsFor(reading)
        while (
            sigs.a.padding === '' ||
            sigs.b.padding === '' ||
            sigs.a.padding === sigs.b.padding ||
            sigs.a.s === sigs.b.s
        ) {
            if (reading - 11n >= BigInt(SEARCH_CAP)) {
                throw new Error('no ATTESTM reading found')
            }
            sigs = sigsFor(++reading)
        }
        const r = await memberCycle(
            m,
            BigInt(FUNDING),
            T0 + 60n,
            'A',
            tree,
            reading
        )
        expect(r.tx.verifyInputScript(0).success).to.equal(true)
        // B's signature over the same "K17T" message verifies under B's
        // key, so only sha256(keyA) == the leaf's key hash can refuse it.
        tamperPush(
            r.tx,
            0,
            pubKeyBytes(attesterA.pub),
            pubKeyBytes(attesterB.pub)
        )
        tamperPush(r.tx, 0, int2ByteString(sigs.a.s), int2ByteString(sigs.b.s))
        tamperPush(r.tx, 0, sigs.a.padding, sigs.b.padding)
        expectScriptRefused(r.tx)
    })

    it('interpreter: the same-round assert refuses round == lastRound whatever outputs the tx carries', async () => {
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
            T0 + 60n,
            keeperA,
            {},
            [5n],
            NO_SIG,
            {},
            tree.proof(INDEX_A)
        )
        tree.set(INDEX_A, leafOf('A', 5n))
        const n1 = r1.next as K17Machine
        const t2 = T0 + 120n
        // Honest round-6 plan; the attacks reuse its reward and payout.
        const plan6 = planCycle(
            n1,
            r1.plan.remaining,
            t2,
            keeperA,
            [6n],
            NO_SIG,
            {},
            tree.proof(INDEX_A)
        )
        expect(plan6.halted).to.be.false
        const round5 = encodeCell(5n)

        // (a) what an implementation without the check would output for
        // round 5: the member paid and the leaf rewritten with
        // lastRound 5, i.e. rosterRoot unchanged.
        const wrongNext = (plan6.next as K17Machine).next()
        wrongNext.rosterRoot = toByteString(tree.root())
        const stateTx = await buildStepTx(n1, plan6, t2, round5, wrongNext)
        expectScriptRefused(stateTx)

        // (b) what an implementation that faults instead of refusing would
        // output: halted, payout dropped, beneficiary refunded.
        const refundPlan: CyclePlan = {
            ...plan6,
            halted: true,
            next: undefined,
            payslot: undefined,
            remaining: r1.plan.remaining - plan6.reward,
        }
        const refundTx = await buildStepTx(n1, refundPlan, t2, round5)
        expectScriptRefused(refundTx)

        // Control: the same builder with the honest round-6 plan verifies,
        // so the refusals above come from the round check.
        const honestTx = await buildStepTx(n1, plan6, t2, encodeCell(6n))
        expect(honestTx.verifyInputScript(0).success).to.equal(true)
    })

    // ------------------------------------------------------------------
    // v3 machine: ADMIT and REMOVE
    // ------------------------------------------------------------------

    /** Empty leaf (in twoMemberTree too) that the tests admit members into. */
    const ADMIT_INDEX = 3
    /** Tags of the REMOVE message and of the smoke program's ATTESTM reading. */
    const TAG_X = 55
    const TAG_T = 66
    /** Sats the smoke program pays the admitted member in cycle 2. */
    const SMOKE_BOUNTY = 4000

    /**
     * True when two signatures can be swapped with tamperPush: both
     * paddings are non-empty and the paddings and s values differ.
     * Input: two signatures. Output: boolean.
     */
    const swappable = (a: RabinSig, b: RabinSig): boolean =>
        a.padding !== '' &&
        b.padding !== '' &&
        a.padding !== b.padding &&
        a.s !== b.s

    /**
     * Sponsor-style admission signature for member A's key (or `newKey`)
     * with member A's payout, on the TEST_ID instance.
     * Input: signer, rosterSeq to sign, leaf index, new member key, tag.
     * Output: the Rabin signature over admitMessage.
     */
    const admissionSig = (
        signer: Attester,
        seq: bigint,
        index: number,
        newKey: bigint,
        tag: number
    ): RabinSig =>
        signAdmission(
            signer,
            TEST_ID,
            BigInt(tag),
            seq,
            BigInt(index),
            newKey,
            payoutOf(memberAAddress)
        )

    /**
     * ADMIT tag for these tests: the first tag from 1000 up (at most
     * SEARCH_CAP tries) for which the
     * signatures the tamper tests swap (sponsor at seq 0 against seq 1,
     * seq 0 against seq 2, and sponsor against attesterB at seq 0) all
     * have distinct, non-empty paddings, so each push is unique.
     */
    const TAG_D = (() => {
        for (let tag = 1000; tag < 1000 + SEARCH_CAP; tag++) {
            const sig = (signer: Attester, seq: bigint) =>
                admissionSig(signer, seq, ADMIT_INDEX, attesterA.pub, tag)
            const s0 = sig(sponsor, 0n)
            if (
                swappable(s0, sig(sponsor, 1n)) &&
                swappable(s0, sig(sponsor, 2n)) &&
                swappable(s0, sig(attesterB, 0n))
            ) {
                return tag
            }
        }
        throw new Error('no ADMIT tag found')
    })()

    /**
     * Leaf preimage of a member admitted at ADMIT_INDEX: `key`'s hash,
     * member A's payout, lastRound `round`, flags 0.
     * Input: admission round, optional key (default attesterA's).
     * Output: 120 hex chars.
     */
    const admittedLeaf = (round: bigint, key: bigint = attesterA.pub) =>
        encodeLeafPre(keyHash(key), payoutOf(memberAAddress), round)

    /**
     * Keys of an admission cycle: `signer` signs (keyA), `newKey` joins
     * (keyB) with member A's payout.
     * Input: signer, new member key. Output: CycleKeys.
     */
    const admitKeys = (signer: Attester, newKey: bigint): CycleKeys => ({
        attestKey: signer.pub,
        endorseKey: newKey,
        payoutHex: payoutOf(memberAAddress),
    })

    /**
     * Run one cycle of a program whose next instructions admit member A
     * (or `newKey`) at ADMIT_INDEX (or `index`) with its proof from `tree`.
     * Input: machine, value, lock time, tree, options: index, new key,
     * signer (default the sponsor), signature to present (default the
     * signer's signature for the machine's rosterSeq), witness cells.
     * Output: the cycle result.
     */
    function admitCycle(
        m: K17Machine,
        value: bigint,
        lockTime: bigint,
        tree: SparseMerkleTree,
        opts: {
            index?: number
            newKey?: bigint
            signer?: Attester
            sig?: RabinSig
            witness?: bigint[]
        } = {}
    ): Promise<CycleResult> {
        const index = opts.index ?? ADMIT_INDEX
        const signer = opts.signer ?? sponsor
        const newKey = opts.newKey ?? attesterA.pub
        return cycle(
            m,
            value,
            lockTime,
            keeperA,
            {},
            opts.witness ?? [],
            opts.sig ?? admissionSig(signer, m.rosterSeq, index, newKey, TAG_D),
            admitKeys(signer, newKey),
            tree.proof(index)
        )
    }

    /**
     * Program for the replay tests: witness 1 runs `TAG_D TIME ADMIT`,
     * witness 0 runs `tagX REMOVE` (default TAG_X); each ends the cycle
     * and loops back. Input: optional REMOVE tag. Output: program hex.
     */
    const ADMIN_PROG = (tagX: number = TAG_X): string =>
        assemble([
            'IN',
            'IF',
            'remove',
            'LIT',
            TAG_D,
            'TIME',
            'ADMIT',
            'YIELD',
            'LIT',
            0,
            'IF',
            0,
            'remove:',
            'LIT',
            tagX,
            'REMOVE',
            'YIELD',
            'LIT',
            0,
            'IF',
            0,
        ])

    /** Smoke program with the tags and bounty of these tests. */
    const SMOKE_PROG = (): string =>
        treeConsortiumSmokeProgram(TAG_D, TAG_T, SMOKE_BOUNTY)

    it('tree smoke: the sponsor admits a member into an empty index; it attests and is paid next cycle', async () => {
        const tree = new SparseMerkleTree()
        const m = await deployTree(SMOKE_PROG(), tree)
        expect(m.rosterSeq).to.equal(0n)

        // cycle 1: ADMIT at ADMIT_INDEX with lastRound := TIME
        const t1 = T0 + 60n
        const r1 = await admitCycle(m, BigInt(FUNDING), t1, tree)
        expect(r1.plan.halted).to.be.false
        expect(r1.plan.treeOp).to.equal('admit')
        expect(r1.plan.payslot).to.be.undefined
        tree.set(ADMIT_INDEX, admittedLeaf(t1))
        const n1 = r1.next as K17Machine
        expect(n1.rosterRoot).to.equal(tree.root())
        expect(n1.rosterSeq).to.equal(1n)

        // cycle 2: the member attests a reading and is paid. The whole
        // cycle-2 sequence must run inside one cycle of K instructions,
        // which the halt in this one cycle shows.
        const reading = 777n
        const r2 = await cycle(
            n1,
            r1.plan.remaining,
            T0 + 120n,
            keeperA,
            {},
            [reading],
            signMemberReading(attesterA, n1.instanceId, BigInt(TAG_T), reading),
            { attestKey: attesterA.pub },
            tree.proof(ADMIT_INDEX)
        )
        expect(r2.plan.halted).to.be.true
        expect(outputLog(r2.plan.nextState)).to.deep.equal([t1])
        expect(r2.plan.nextState.logHash).to.equal(
            sha256Hex('00'.repeat(32) + encodeCell(reading))
        )
        expect(addressOf(r2.tx.outputs[0])).to.equal(
            beneficiaryAddress.toString()
        )
        expect(addressOf(r2.tx.outputs[1])).to.equal(keeperA.toString())
        expect(addressOf(r2.tx.outputs[2])).to.equal(memberAAddress.toString())
        expect(r2.tx.outputs[2].satoshis).to.equal(SMOKE_BOUNTY)
    })

    it('a member admitted in round r cannot be paid in r, only in r + 1 (Review Focus 3)', async () => {
        // The smoke program (ROUND from TIME): the planner refuses cycle 2
        // at the admission's own nLockTime and accepts it one second later.
        const tree = new SparseMerkleTree()
        const m = await deployTree(SMOKE_PROG(), tree)
        const t1 = T0 + 60n
        const r1 = await admitCycle(m, BigInt(FUNDING), t1, tree)
        tree.set(ADMIT_INDEX, admittedLeaf(t1))
        const n1 = r1.next as K17Machine
        const payAt = (lockTime: bigint) =>
            cycle(
                n1,
                r1.plan.remaining,
                lockTime,
                keeperA,
                {},
                [9n],
                signMemberReading(attesterA, n1.instanceId, BigInt(TAG_T), 9n),
                { attestKey: attesterA.pub },
                tree.proof(ADMIT_INDEX)
            )
        await expect(payAt(t1)).to.be.rejectedWith(/rejected/)
        const paid = await payAt(t1 + 1n)
        expect(addressOf(paid.tx.outputs[2])).to.equal(
            memberAAddress.toString()
        )

        // The interpreter: ROUND from the witness only to build the
        // attack. Admit with ROUND 5, then try to pay with ROUND 5.
        const prog = assemble([
            'LIT',
            TAG_D,
            'IN',
            'ADMIT',
            'YIELD',
            'MEMBER',
            'DROP',
            'LIT',
            PAY_M,
            'IN',
            'PAYLEAF',
            'YIELD',
            'HALT',
        ])
        const wtree = new SparseMerkleTree()
        const w = await deployTree(prog, wtree)
        const w1 = await admitCycle(w, BigInt(FUNDING), T0 + 60n, wtree, {
            witness: [5n],
        })
        wtree.set(ADMIT_INDEX, admittedLeaf(5n))
        const wn1 = w1.next as K17Machine
        expect(wn1.rosterRoot).to.equal(wtree.root())
        const t2 = T0 + 120n
        const plan6 = planCycle(
            wn1,
            w1.plan.remaining,
            t2,
            keeperA,
            [6n],
            NO_SIG,
            {},
            wtree.proof(ADMIT_INDEX)
        )
        expect(plan6.halted).to.be.false
        expect(() =>
            planCycle(
                wn1,
                w1.plan.remaining,
                t2,
                keeperA,
                [5n],
                NO_SIG,
                {},
                wtree.proof(ADMIT_INDEX)
            )
        ).to.throw(/rejected/)
        const round5 = encodeCell(5n)
        // (a) output of an implementation without the check: member paid,
        // leaf rewritten with lastRound 5, so rosterRoot unchanged.
        const wrongNext = (plan6.next as K17Machine).next()
        wrongNext.rosterRoot = toByteString(wtree.root())
        expectScriptRefused(
            await buildStepTx(wn1, plan6, t2, round5, wrongNext)
        )
        // (b) output of an implementation that faults instead: halted,
        // payout dropped, beneficiary refunded.
        const refundPlan: CyclePlan = {
            ...plan6,
            halted: true,
            next: undefined,
            payslot: undefined,
            remaining: w1.plan.remaining - plan6.reward,
        }
        expectScriptRefused(await buildStepTx(wn1, refundPlan, t2, round5))
        // Control: the honest round-6 transaction verifies.
        const honestTx = await buildStepTx(wn1, plan6, t2, encodeCell(6n))
        expect(honestTx.verifyInputScript(0).success).to.equal(true)
    })

    it('a sponsor admission replayed after REMOVE is refused: rosterSeq moved on (Review Focus 2)', async () => {
        const tree = new SparseMerkleTree()
        const m = await deployTree(ADMIN_PROG(), tree)
        const sig0 = admissionSig(
            sponsor,
            0n,
            ADMIT_INDEX,
            attesterA.pub,
            TAG_D
        )

        // cycle 1: admit A (rosterSeq 0 -> 1)
        const t1 = T0 + 60n
        const r1 = await admitCycle(m, BigInt(FUNDING), t1, tree, {
            witness: [1n],
            sig: sig0,
        })
        tree.set(ADMIT_INDEX, admittedLeaf(t1))
        const n1 = r1.next as K17Machine
        expect(n1.rosterRoot).to.equal(tree.root())
        expect(n1.rosterSeq).to.equal(1n)

        // cycle 2: remove A (rosterSeq 1 -> 2); the tree is empty again
        const r2 = await cycle(
            n1,
            r1.plan.remaining,
            T0 + 120n,
            keeperA,
            {},
            [0n],
            signRemoval(
                sponsor,
                TEST_ID,
                BigInt(TAG_X),
                1n,
                BigInt(ADMIT_INDEX),
                decodeLeafPre(admittedLeaf(t1)).keyHashHex,
                decodeLeafPre(admittedLeaf(t1)).payoutHex
            ),
            { attestKey: sponsor.pub },
            tree.proof(ADMIT_INDEX)
        )
        expect(r2.plan.treeOp).to.equal('remove')
        tree.set(ADMIT_INDEX, '')
        const n2 = r2.next as K17Machine
        expect(n2.rosterRoot).to.equal(EMPTY_HASHES[16])
        expect(n2.rosterSeq).to.equal(2n)

        // cycle 3: the original admission is stale by rosterSeq
        const t3 = T0 + 180n
        await expect(
            admitCycle(n2, r2.plan.remaining, t3, tree, {
                witness: [1n],
                sig: sig0,
            })
        ).to.be.rejectedWith(/rejected/)
        // A fresh admission for seq 2 verifies; the same transaction with
        // the seq-0 signature has the same outputs, so only the signature
        // check can refuse it.
        const honest = await admitCycle(n2, r2.plan.remaining, t3, tree, {
            witness: [1n],
        })
        expect((honest.next as K17Machine).rosterSeq).to.equal(3n)
        const sig2 = honest.plan.sig
        tamperPush(honest.tx, 0, int2ByteString(sig2.s), int2ByteString(sig0.s))
        tamperPush(honest.tx, 0, sig2.padding, sig0.padding)
        expectScriptRefused(honest.tx)
    })

    it('an admission signed for the wrong rosterSeq is refused', async () => {
        const tree = new SparseMerkleTree()
        const m = await deployTree(SMOKE_PROG(), tree)
        const t1 = T0 + 60n
        const sig1 = admissionSig(
            sponsor,
            1n,
            ADMIT_INDEX,
            attesterA.pub,
            TAG_D
        )
        await expect(
            admitCycle(m, BigInt(FUNDING), t1, tree, { sig: sig1 })
        ).to.be.rejectedWith(/rejected/)
        const honest = await admitCycle(m, BigInt(FUNDING), t1, tree)
        const sig0 = honest.plan.sig
        tamperPush(honest.tx, 0, int2ByteString(sig0.s), int2ByteString(sig1.s))
        tamperPush(honest.tx, 0, sig0.padding, sig1.padding)
        expectScriptRefused(honest.tx)
    })

    it("interpreter refuses an admission whose keyB is swapped for a stranger's key", async () => {
        const tree = new SparseMerkleTree()
        const m = await deployTree(SMOKE_PROG(), tree)
        const t1 = T0 + 60n
        const plan = planCycle(
            m,
            BigInt(FUNDING),
            t1,
            keeperA,
            [],
            admissionSig(sponsor, 0n, ADMIT_INDEX, attesterA.pub, TAG_D),
            admitKeys(sponsor, attesterA.pub),
            tree.proof(ADMIT_INDEX)
        )
        // Control: the honest transaction verifies.
        expect(
            (await buildStepTx(m, plan, t1, '')).verifyInputScript(0).success
        ).to.equal(true)
        // (a) keyB swapped in the unlocking script only.
        const swapped = await buildStepTx(m, plan, t1, '')
        tamperPush(
            swapped,
            0,
            pubKeyBytes(attesterA.pub),
            pubKeyBytes(attesterB.pub)
        )
        expectScriptRefused(swapped)
        // (b) keyB swapped and the outputs that a contract without the
        // signature check would accept: the stranger's leaf in the root.
        // Only the signature (which covers sha256(keyB)) can refuse it.
        const strangerTree = new SparseMerkleTree(
            new Map([[ADMIT_INDEX, admittedLeaf(t1, attesterB.pub)]])
        )
        const strangerNext = (plan.next as K17Machine).next()
        strangerNext.rosterRoot = toByteString(strangerTree.root())
        strangerNext.rosterSeq = 1n
        const strangerPlan: CyclePlan = {
            ...plan,
            keyBHex: pubKeyBytes(attesterB.pub),
        }
        expectScriptRefused(
            await buildStepTx(m, strangerPlan, t1, '', strangerNext)
        )
    })

    it('ADMIT on an occupied index with an empty leafPre and the real siblings is refused', async () => {
        const tree = new SparseMerkleTree(
            new Map([[ADMIT_INDEX, admittedLeaf(0n)]])
        )
        const m = await deployTree(SMOKE_PROG(), tree)
        const t1 = T0 + 60n
        const realPath = tree.proof(ADMIT_INDEX)
        const sigB = admissionSig(
            sponsor,
            0n,
            ADMIT_INDEX,
            attesterB.pub,
            TAG_D
        )
        const occupied: CycleTree = {
            leafPre: '',
            proof: realPath.proof,
            leafIndex: BigInt(ADMIT_INDEX),
        }
        // the planner refuses it ...
        await expect(
            cycle(
                m,
                BigInt(FUNDING),
                t1,
                keeperA,
                {},
                [],
                sigB,
                admitKeys(sponsor, attesterB.pub),
                occupied
            )
        ).to.be.rejectedWith(/rejected/)
        // ... and so does the interpreter. Start from an honest admission
        // of B at the empty index 5 (same time, same reward), then present
        // index 3 with an empty leafPre, the real path and a valid sponsor
        // signature for index 3, with the root a contract without the
        // old-root check would compute. Only the old-root check can refuse.
        const plan5 = planCycle(
            m,
            BigInt(FUNDING),
            t1,
            keeperA,
            [],
            admissionSig(sponsor, 0n, 5, attesterB.pub, TAG_D),
            admitKeys(sponsor, attesterB.pub),
            tree.proof(5)
        )
        expect(
            (await buildStepTx(m, plan5, t1, '')).verifyInputScript(0).success
        ).to.equal(true)
        const overwriteNext = (plan5.next as K17Machine).next()
        overwriteNext.rosterRoot = toByteString(
            SparseMerkleTree.rootAfter(
                admittedLeaf(t1, attesterB.pub),
                realPath.proof,
                BigInt(ADMIT_INDEX)
            )
        )
        overwriteNext.rosterSeq = 1n
        const overwritePlan: CyclePlan = {
            ...plan5,
            sig: sigB,
            leafPre: '',
            proof: realPath.proof,
            leafIndex: BigInt(ADMIT_INDEX),
        }
        expectScriptRefused(
            await buildStepTx(m, overwritePlan, t1, '', overwriteNext)
        )
    })

    it("REMOVE empties the leaf; the removed member's old proof is then refused", async () => {
        const prog = assemble([
            'LIT',
            TAG_X,
            'REMOVE',
            'YIELD',
            'MEMBER',
            'DROP',
            'YIELD',
            'HALT',
        ])
        const tree = twoMemberTree()
        const m = await deployTree(prog, tree)
        const staleA = tree.proof(INDEX_A)
        const r1 = await cycle(
            m,
            BigInt(FUNDING),
            T0 + 60n,
            keeperA,
            {},
            [],
            signRemoval(
                sponsor,
                TEST_ID,
                BigInt(TAG_X),
                0n,
                BigInt(INDEX_A),
                keyHash(attesterA.pub),
                payoutOf(memberAAddress)
            ),
            { attestKey: sponsor.pub },
            staleA
        )
        tree.set(INDEX_A, '')
        const n1 = r1.next as K17Machine
        expect(n1.rosterRoot).to.equal(tree.root())
        expect(n1.rosterSeq).to.equal(1n)

        // the planner refuses A's old proof ...
        await expect(
            cycle(
                n1,
                r1.plan.remaining,
                T0 + 120n,
                keeperA,
                {},
                [],
                NO_SIG,
                {},
                staleA
            )
        ).to.be.rejectedWith(/rejected/)
        // ... and so does the interpreter: B's honest MEMBER cycle leaves
        // the root unchanged, so swapping in A's leaf, old path and index
        // keeps the outputs valid and only the old-root check can refuse.
        const freshB = tree.proof(INDEX_B)
        const honest = await cycle(
            n1,
            r1.plan.remaining,
            T0 + 120n,
            keeperA,
            {},
            [],
            NO_SIG,
            {},
            freshB
        )
        expect(honest.tx.verifyInputScript(0).success).to.equal(true)
        tamperPush(honest.tx, 0, freshB.leafPre, staleA.leafPre)
        tamperPush(honest.tx, 0, freshB.proof, staleA.proof)
        tamperPush(
            honest.tx,
            0,
            int2ByteString(BigInt(INDEX_B)),
            int2ByteString(BigInt(INDEX_A))
        )
        expectScriptRefused(honest.tx)
    })

    it('interpreter refuses an admission signed by a key that is not the sponsor', async () => {
        const tree = new SparseMerkleTree()
        const m = await deployTree(SMOKE_PROG(), tree)
        const t1 = T0 + 60n
        await expect(
            admitCycle(m, BigInt(FUNDING), t1, tree, { signer: attesterB })
        ).to.be.rejectedWith(/rejected/)
        // attesterB's signature over the same message verifies under
        // attesterB's key, so only sha256(keyA) == sponsorKeyHash refuses.
        const honest = await admitCycle(m, BigInt(FUNDING), t1, tree)
        const sigS = honest.plan.sig
        const sigB = admissionSig(
            attesterB,
            0n,
            ADMIT_INDEX,
            attesterA.pub,
            TAG_D
        )
        tamperPush(
            honest.tx,
            0,
            pubKeyBytes(sponsor.pub),
            pubKeyBytes(attesterB.pub)
        )
        tamperPush(honest.tx, 0, int2ByteString(sigS.s), int2ByteString(sigB.s))
        tamperPush(honest.tx, 0, sigS.padding, sigB.padding)
        expectScriptRefused(honest.tx)
    })

    it('ADMIT or REMOVE after MEMBER, and on a short stack, fault and refund', async () => {
        /**
         * Deploy `program` over twoMemberTree, run one cycle (with member
         * A's proof when `withProof`), and expect a halt with the balance
         * paid to the beneficiary. Input: program tokens, flag. Output: none.
         */
        const runOnce = async (
            program: (string | number)[],
            withProof = false
        ) => {
            const tree = twoMemberTree()
            const m = await deployTree(assemble(program), tree)
            const r = await cycle(
                m,
                BigInt(FUNDING),
                T0 + 60n,
                keeperA,
                {},
                [],
                NO_SIG,
                {},
                withProof ? tree.proof(INDEX_A) : undefined
            )
            expect(r.plan.halted).to.be.true
            expect(addressOf(r.tx.outputs[0])).to.equal(
                beneficiaryAddress.toString()
            )
        }
        await runOnce(['MEMBER', 'LIT', 1, 'ADMIT', 'YIELD'], true)
        await runOnce(['MEMBER', 'REMOVE', 'YIELD'], true)
        await runOnce(['LIT', 1, 'ADMIT', 'YIELD'])
        await runOnce(['REMOVE', 'YIELD'])
    })

    /** Program for the REMOVE tamper tests: remove, yield, halt. */
    const REMOVE_PROG = (tag: number): string =>
        assemble(['LIT', tag, 'REMOVE', 'YIELD', 'HALT'])

    /** Identity a removal message binds (v3.1): leafPre bytes 0..52. */
    interface RemovedMember {
        keyHashHex: string
        payoutHex: string
    }

    /** Identity of member A as twoMemberTree holds it. */
    const MEMBER_A: RemovedMember = {
        keyHashHex: keyHash(attesterA.pub),
        payoutHex: payoutOf(memberAAddress),
    }

    /** All-zero identity, signed for an empty leaf that has no member. */
    const NOBODY: RemovedMember = {
        keyHashHex: '00'.repeat(32),
        payoutHex: '00'.repeat(20),
    }

    /**
     * Removal signature of the TEST_ID instance at `seq` (default 0).
     * Input: signer, tag, leaf index, the removed member's key hash and
     * payout, rosterSeq to sign. Output: Rabin signature.
     */
    const removalSig = (
        signer: Attester,
        tag: number,
        index: number,
        member: RemovedMember,
        seq = 0n
    ): RabinSig =>
        signRemoval(
            signer,
            TEST_ID,
            BigInt(tag),
            seq,
            BigInt(index),
            member.keyHashHex,
            member.payoutHex
        )

    it('interpreter refuses a REMOVE signed by a key that is not the sponsor', async () => {
        // a tag for which the sponsor's and attesterB's signatures over the
        // same removeMessage have unique, non-empty pushes
        let tag = 2000
        while (
            !swappable(
                removalSig(sponsor, tag, INDEX_A, MEMBER_A),
                removalSig(attesterB, tag, INDEX_A, MEMBER_A)
            )
        ) {
            if (tag - 2000 >= SEARCH_CAP) throw new Error('no REMOVE tag found')
            tag++
        }
        const tree = twoMemberTree()
        const m = await deployTree(REMOVE_PROG(tag), tree)
        const removeA = (signer: Attester) =>
            cycle(
                m,
                BigInt(FUNDING),
                T0 + 60n,
                keeperA,
                {},
                [],
                removalSig(signer, tag, INDEX_A, MEMBER_A),
                { attestKey: signer.pub },
                tree.proof(INDEX_A)
            )
        await expect(removeA(attesterB)).to.be.rejectedWith(/rejected/)
        // attesterB's signature verifies under attesterB's key, so only
        // sha256(keyA) == sponsorKeyHash can refuse the swapped cycle.
        const honest = await removeA(sponsor)
        const sigS = honest.plan.sig
        const sigB = removalSig(attesterB, tag, INDEX_A, MEMBER_A)
        tamperPush(
            honest.tx,
            0,
            pubKeyBytes(sponsor.pub),
            pubKeyBytes(attesterB.pub)
        )
        tamperPush(honest.tx, 0, int2ByteString(sigS.s), int2ByteString(sigB.s))
        tamperPush(honest.tx, 0, sigS.padding, sigB.padding)
        expectScriptRefused(honest.tx)
    })

    it('REMOVE of an empty leaf is refused by the planner and the interpreter', async () => {
        const tree = twoMemberTree()
        const m = await deployTree(REMOVE_PROG(TAG_X), tree)
        const t1 = T0 + 60n
        const emptyPath = tree.proof(ADMIT_INDEX)
        expect(emptyPath.leafPre).to.equal('')
        // the planner refuses it (the VM needs a 120-hex-char preimage) ...
        await expect(
            cycle(
                m,
                BigInt(FUNDING),
                t1,
                keeperA,
                {},
                [],
                removalSig(sponsor, TAG_X, ADMIT_INDEX, NOBODY),
                { attestKey: sponsor.pub },
                emptyPath
            )
        ).to.be.rejectedWith(/rejected/)
        // ... and so does the interpreter. Start from an honest removal of
        // A (same time, same reward), then present the empty index with
        // leafPre '' and its real path. The old-root walk accepts the empty
        // leaf. The sponsor signs a removal of an all-zero identity, and
        // the outputs carry the root a removal would compute (unchanged)
        // and rosterSeq 1. The leafPre length check is the first check
        // on this path that refuses it. (In v3.1 the message tail is
        // slice(leafPre, 0, 52), so this test no longer shows that the
        // length check is the only guard.)
        const planA = planCycle(
            m,
            BigInt(FUNDING),
            t1,
            keeperA,
            [],
            removalSig(sponsor, TAG_X, INDEX_A, MEMBER_A),
            { attestKey: sponsor.pub },
            tree.proof(INDEX_A)
        )
        expect(
            (await buildStepTx(m, planA, t1, '')).verifyInputScript(0).success
        ).to.equal(true)
        const emptyNext = (planA.next as K17Machine).next()
        emptyNext.rosterRoot = toByteString(tree.root())
        emptyNext.rosterSeq = 1n
        const emptyPlan: CyclePlan = {
            ...planA,
            sig: removalSig(sponsor, TAG_X, ADMIT_INDEX, NOBODY),
            leafPre: '',
            proof: emptyPath.proof,
            leafIndex: BigInt(ADMIT_INDEX),
        }
        expectScriptRefused(await buildStepTx(m, emptyPlan, t1, '', emptyNext))
    })

    // ------------------------------------------------------------------
    // v3.1: a removal signed before a PAYLEAF still verifies after it
    // ------------------------------------------------------------------

    /**
     * Program for the v3.1 race tests. Cycle 1 binds the member, pays it
     * PAY_M with ROUND from the witness (lastRound changes, so the leaf and
     * the root change) and yields. Cycle 2 removes the member with TAG
     * `tag` and yields. Input: tag. Output: program hex.
     */
    const PAY_THEN_REMOVE_PROG = (tag: number): string =>
        assemble([
            'MEMBER',
            'DROP',
            'LIT',
            PAY_M,
            'IN',
            'PAYLEAF',
            'YIELD',
            'LIT',
            tag,
            'REMOVE',
            'YIELD',
            'HALT',
        ])

    /** Member A's identity with a payout that is not A's (B's payout). */
    const A_WRONG_PAYOUT: RemovedMember = {
        keyHashHex: keyHash(attesterA.pub),
        payoutHex: payoutOf(memberBAddress),
    }
    /** Member A's payout with a key hash that is not A's (B's key). */
    const A_WRONG_KEY: RemovedMember = {
        keyHashHex: keyHash(attesterB.pub),
        payoutHex: payoutOf(memberAAddress),
    }

    /**
     * Deploy PAY_THEN_REMOVE_PROG(tag) over twoMemberTree and run cycle 1:
     * member A is paid with ROUND 5. The tree is updated to match.
     * Input: tag. Output: the deployed machine, cycle 1 result and the
     * off-chain tree after cycle 1.
     */
    const payA = async (tag: number) => {
        const tree = twoMemberTree()
        const m = await deployTree(PAY_THEN_REMOVE_PROG(tag), tree)
        const oldRoot = tree.root()
        const r1 = await cycle(
            m,
            BigInt(FUNDING),
            T0 + 60n,
            keeperA,
            {},
            [5n],
            NO_SIG,
            {},
            tree.proof(INDEX_A)
        )
        tree.set(INDEX_A, leafOf('A', 5n))
        const n1 = r1.next as K17Machine
        expect(n1.rosterRoot).to.not.equal(oldRoot)
        expect(n1.rosterRoot).to.equal(tree.root())
        expect(n1.rosterSeq).to.equal(0n)
        return { r1, n1, tree }
    }

    /**
     * Cycle 2 of the race tests: REMOVE member A with `sig` and a fresh
     * proof against the post-payment root.
     * Input: cycle 1 result, machine after cycle 1, tree after cycle 1,
     * signature. Output: the cycle result (rejects when the planner or the
     * interpreter refuses).
     */
    const removeA = (
        r1: CycleResult,
        n1: K17Machine,
        tree: SparseMerkleTree,
        sig: RabinSig
    ) =>
        cycle(
            n1,
            r1.plan.remaining,
            T0 + 120n,
            keeperA,
            {},
            [],
            sig,
            { attestKey: sponsor.pub },
            tree.proof(INDEX_A)
        )

    it('v3.1: a removal signed before a PAYLEAF is accepted after it', async () => {
        // the sponsor signs at rosterSeq 0, before the payment
        const sig = removalSig(sponsor, TAG_X, INDEX_A, MEMBER_A)
        const { r1, n1, tree } = await payA(TAG_X)
        const r2 = await removeA(r1, n1, tree, sig)
        expect(r2.tx.verifyInputScript(0).success).to.equal(true)
        expect(r2.plan.treeOp).to.equal('remove')
        tree.set(INDEX_A, '')
        const n2 = r2.next as K17Machine
        expect(n2.rosterRoot).to.equal(tree.root())
        expect(n2.rosterSeq).to.equal(1n)
    })

    it('v3.1: a removal signature with a swapped payout or key hash is refused after a PAYLEAF', async () => {
        // a tag for which the honest signature and both swapped ones have
        // unique, non-empty pushes, so tamperPush can exchange them
        const sigsFor = (tag: number) => ({
            honest: removalSig(sponsor, tag, INDEX_A, MEMBER_A),
            payout: removalSig(sponsor, tag, INDEX_A, A_WRONG_PAYOUT),
            key: removalSig(sponsor, tag, INDEX_A, A_WRONG_KEY),
        })
        let tag = 3000
        let sigs = sigsFor(tag)
        while (
            !swappable(sigs.honest, sigs.payout) ||
            !swappable(sigs.honest, sigs.key)
        ) {
            if (tag - 3000 >= SEARCH_CAP) throw new Error('no REMOVE tag found')
            sigs = sigsFor(++tag)
        }
        const { r1, n1, tree } = await payA(tag)
        // the planner refuses both swapped signatures ...
        await expect(removeA(r1, n1, tree, sigs.payout)).to.be.rejectedWith(
            /rejected/
        )
        await expect(removeA(r1, n1, tree, sigs.key)).to.be.rejectedWith(
            /rejected/
        )
        // ... and so does the interpreter: the honest removal verifies,
        // and the same transaction with a swapped signature does not.
        for (const bad of [sigs.payout, sigs.key]) {
            const honest = await removeA(r1, n1, tree, sigs.honest)
            expect(honest.tx.verifyInputScript(0).success).to.equal(true)
            tamperPush(
                honest.tx,
                0,
                int2ByteString(sigs.honest.s),
                int2ByteString(bad.s)
            )
            tamperPush(honest.tx, 0, sigs.honest.padding, bad.padding)
            expectScriptRefused(honest.tx)
        }
    })

    it('v3.1: a removal replayed after re-admission of the same member at the same index is refused', async () => {
        // Under v3.1 the removal message binds keyHash || payout, which is
        // the same after member A is admitted again at INDEX_A with the
        // same key and payout. rosterSeq is then the only guard.
        // A REMOVE tag for which the seq-0 and seq-2 signatures have
        // unique, non-empty pushes, so tamperPush can exchange them. The
        // REMOVE cycles push the witness cell(0) ('00000000'), and member
        // A's payout is random per run, so a padding of four zero bytes
        // would collide with that push: skip such tags too.
        const witnessPush = encodeCell(0n)
        let tag = 4000
        const sigsFor = (t: number) => ({
            old: removalSig(sponsor, t, INDEX_A, MEMBER_A, 0n),
            current: removalSig(sponsor, t, INDEX_A, MEMBER_A, 2n),
        })
        let sigs = sigsFor(tag)
        while (
            !swappable(sigs.old, sigs.current) ||
            sigs.old.padding === witnessPush ||
            sigs.current.padding === witnessPush
        ) {
            if (tag - 4000 >= SEARCH_CAP) throw new Error('no REMOVE tag found')
            sigs = sigsFor(++tag)
        }
        const tree = twoMemberTree()
        const m = await deployTree(ADMIN_PROG(tag), tree)

        // cycle 1: remove A with the seq-0 signature (seq 0 -> 1)
        const r1 = await cycle(
            m,
            BigInt(FUNDING),
            T0 + 60n,
            keeperA,
            {},
            [0n],
            sigs.old,
            { attestKey: sponsor.pub },
            tree.proof(INDEX_A)
        )
        expect(r1.plan.treeOp).to.equal('remove')
        tree.set(INDEX_A, '')
        const n1 = r1.next as K17Machine
        expect(n1.rosterRoot).to.equal(tree.root())
        expect(n1.rosterSeq).to.equal(1n)

        // cycle 2: admit A again at INDEX_A, same key and payout (1 -> 2)
        const t2 = T0 + 120n
        const r2 = await admitCycle(n1, r1.plan.remaining, t2, tree, {
            index: INDEX_A,
            witness: [1n],
        })
        tree.set(INDEX_A, admittedLeaf(t2))
        const n2 = r2.next as K17Machine
        expect(n2.rosterRoot).to.equal(tree.root())
        expect(n2.rosterSeq).to.equal(2n)
        // the 52-byte identity the removal binds is unchanged
        expect(admittedLeaf(t2).slice(0, 104)).to.equal(
            leafOf('A', 0n).slice(0, 104)
        )

        // cycle 3: the seq-0 removal with a fresh proof is refused by the
        // planner ...
        const t3 = T0 + 180n
        const removeAt3 = (sig: RabinSig) =>
            cycle(
                n2,
                r2.plan.remaining,
                t3,
                keeperA,
                {},
                [0n],
                sig,
                { attestKey: sponsor.pub },
                tree.proof(INDEX_A)
            )
        await expect(removeAt3(sigs.old)).to.be.rejectedWith(/rejected/)
        // ... and by the interpreter: the honest seq-2 removal verifies,
        // and the same transaction with the seq-0 signature does not.
        const honest = await removeAt3(sigs.current)
        expect(honest.tx.verifyInputScript(0).success).to.equal(true)
        const n3 = honest.next as K17Machine
        expect(n3.rosterSeq).to.equal(3n)
        tamperPush(
            honest.tx,
            0,
            int2ByteString(sigs.current.s),
            int2ByteString(sigs.old.s)
        )
        tamperPush(honest.tx, 0, sigs.current.padding, sigs.old.padding)
        expectScriptRefused(honest.tx)
    })

    // ------------------------------------------------------------------
    // v3.1: a second signature instruction in one cycle is a fault
    // ------------------------------------------------------------------

    /**
     * Check a cycle result that faulted at `pc`: the plan is halted, the
     * beneficiary gets value - reward in output 0 and the keeper its
     * reward in output 1. Input: cycle result, value spent, expected
     * halting pc. Output: none (chai assertions).
     */
    const expectRefundAt = (r: CycleResult, value: bigint, pc: bigint) => {
        expect(r.plan.halted).to.be.true
        expect(r.plan.nextState.pc).to.equal(pc)
        expect(r.plan.reward > 0n).to.be.true
        expect(addressOf(r.tx.outputs[0])).to.equal(
            beneficiaryAddress.toString()
        )
        expect(BigInt(r.tx.outputs[0].satoshis)).to.equal(value - r.plan.reward)
        expect(addressOf(r.tx.outputs[1])).to.equal(keeperA.toString())
        expect(BigInt(r.tx.outputs[1].satoshis)).to.equal(r.plan.reward)
        expect(r.tx.verifyInputScript(0).success).to.equal(true)
    }

    it('v3.1: ATTEST then ATTESTM in one cycle faults and refunds', async () => {
        // prettier-ignore
        const prog = assemble([
            'MEMBER', 'DROP',
            'LIT', 5, 'LIT', 2231, 'LIT', 0, 'ATTEST',
            'LIT', TAG_M, 'LIT', 7, 'ATTESTM', 'YIELD',
        ])
        const tree = twoMemberTree()
        const m = await deployTree(prog, tree, FUNDING, SPONSOR_MEM)
        const r = await cycle(
            m,
            BigInt(FUNDING),
            T0 + 60n,
            keeperA,
            {},
            [],
            ATTEST0_SIG(m.instanceId),
            { attestKey: sponsor.pub },
            tree.proof(INDEX_A)
        )
        // halted at ATTESTM (pc 28) with its operands on the stack
        expectRefundAt(r, BigInt(FUNDING), 28n)
        expect(r.plan.treeOp).to.equal('member')
        expect(r.plan.nextState.ds).to.equal(
            encodeCell(BigInt(TAG_M)) + encodeCell(7n)
        )
    })

    it('v3.1: ATTESTM then ADMIT in one cycle faults and refunds', async () => {
        // prettier-ignore
        const prog = assemble([
            'MEMBER', 'DROP', 'LIT', TAG_M, 'LIT', 7, 'ATTESTM',
            'LIT', TAG_D, 'LIT', 1, 'ADMIT', 'YIELD',
        ])
        const tree = twoMemberTree()
        const m = await deployTree(prog, tree)
        const r = await cycle(
            m,
            BigInt(FUNDING),
            T0 + 60n,
            keeperA,
            {},
            [],
            signMemberReading(attesterA, m.instanceId, BigInt(TAG_M), 7n),
            { attestKey: attesterA.pub },
            tree.proof(INDEX_A)
        )
        // halted at ADMIT (pc 23): the roster is unchanged
        expectRefundAt(r, BigInt(FUNDING), 23n)
        expect(r.plan.nextState.rosterRoot).to.equal(tree.root())
        expect(r.plan.nextState.rosterSeq).to.equal(0n)
    })

    it('v3.1: ATTEST then ADMIT in one cycle faults on the signature rule alone', async () => {
        // No tree instruction runs before ADMIT, so only the second
        // signature makes it fault; the tree block never runs.
        // prettier-ignore
        const prog = assemble([
            'LIT', 5, 'LIT', 2231, 'LIT', 0, 'ATTEST',
            'LIT', TAG_D, 'LIT', 1, 'ADMIT', 'YIELD',
        ])
        const tree = new SparseMerkleTree()
        const m = await deployTree(prog, tree, FUNDING, SPONSOR_MEM)
        const r = await cycle(
            m,
            BigInt(FUNDING),
            T0 + 60n,
            keeperA,
            {},
            [],
            ATTEST0_SIG(m.instanceId),
            { attestKey: sponsor.pub }
        )
        expectRefundAt(r, BigInt(FUNDING), 26n)
        expect(r.plan.treeOp).to.equal('none')
        expect(r.plan.nextState.rosterSeq).to.equal(0n)
    })

    it('v3.1: ATTEST then REMOVE in one cycle faults on the signature rule', async () => {
        // prettier-ignore
        const prog = assemble([
            'LIT', 5, 'LIT', 2231, 'LIT', 0, 'ATTEST',
            'LIT', TAG_X, 'REMOVE', 'YIELD',
        ])
        const tree = twoMemberTree()
        const m = await deployTree(prog, tree, FUNDING, SPONSOR_MEM)
        const r = await cycle(
            m,
            BigInt(FUNDING),
            T0 + 60n,
            keeperA,
            {},
            [],
            ATTEST0_SIG(m.instanceId),
            { attestKey: sponsor.pub }
        )
        // halted at REMOVE (pc 21), member A still in the tree
        expectRefundAt(r, BigInt(FUNDING), 21n)
        expect(r.plan.treeOp).to.equal('none')
        expect(r.plan.nextState.rosterRoot).to.equal(tree.root())
        expect(r.plan.nextState.rosterSeq).to.equal(0n)
        expect(r.plan.nextState.ds).to.equal(encodeCell(BigInt(TAG_X)))
    })

    it('v3.1: SIGVERIFY then SIGVERIFY in one cycle faults and refunds', async () => {
        // prettier-ignore
        const prog = assemble([
            'IN', 'IN', 'OVER', 'OVER',
            'SIGVERIFY', 1, 'SIGVERIFY', 1, 'HALT',
        ])
        const m = newMachine(prog, ECON, T0, ROSTER, undefined, TEST_ID)
        await m.connect(getDefaultSigner())
        await m.deploy(FUNDING)
        const r = await cycle(
            m,
            BigInt(FUNDING),
            T0 + 60n,
            keeperA,
            {},
            [5n, 2231n],
            signReading(attesterB, 5n, 2231n)
        )
        // the first SIGVERIFY verified; the second (pc 9) faults
        expectRefundAt(r, BigInt(FUNDING), 9n)
        expect(r.plan.nextState.ds).to.equal(encodeCell(5n) + encodeCell(2231n))
    })

    // ------------------------------------------------------------------
    // v3.1: dead-man halt and the 60 s minimum clock advance
    // ------------------------------------------------------------------

    /** Dead-man interval of the tests below: the keeper's floor, 6 hours. */
    const DEAD_MAN = DEAD_MAN_FLOOR

    /**
     * Deploy `prog` with ECON plus a dead-man interval.
     * Input: program hex, deadMan (seconds, 0n = off), optional roster
     * tree settings (default the empty tree and no sponsor).
     * Output: the deployed contract instance (lastTime = T0).
     */
    async function deployDeadMan(
        prog: string,
        deadMan: bigint,
        tree: { rosterRoot?: string; sponsorKeyHash?: string } = {}
    ): Promise<K17Machine> {
        const m = newMachine(
            prog,
            { ...ECON, deadMan },
            T0,
            rosterOf(),
            undefined,
            TEST_ID,
            tree
        )
        await m.connect(getDefaultSigner())
        await m.deploy(FUNDING)
        return m
    }

    /** Program that logs one witness cell per cycle: IN OUT YIELD, loop. */
    const WAIT_IN = assemble(['IN', 'OUT', 'YIELD', 'LIT', 0, 'IF', 0])

    /**
     * The refund plan a keeper would send for `m` if the dead-man fired:
     * the dead-man plan at lastTime + DEAD_MAN, which has the same outputs
     * as at any lockTime from lastTime + 400 on (the reward is capped at
     * 500). Input: a WAIT_IN machine with deadMan DEAD_MAN and FUNDING
     * sats. Output: plan.
     */
    const deadManPlanFor = (m: K17Machine): CyclePlan =>
        planCycle(m, BigInt(FUNDING), m.lastTime + DEAD_MAN, keeperA)

    it('v3.1: newMachine stores deadMan and refuses a negative or too short one', () => {
        expect(DEAD_MAN_FLOOR).to.equal(21_600n)
        expect(newMachine(WAIT_IN, ECON, T0).deadMan).to.equal(0n)
        expect(
            newMachine(WAIT_IN, { ...ECON, deadMan: DEAD_MAN }, T0).deadMan
        ).to.equal(DEAD_MAN)
        // below the 6 h floor: refused unless the test override is set
        expect(() =>
            newMachine(WAIT_IN, { ...ECON, deadMan: DEAD_MAN_FLOOR - 1n }, T0)
        ).to.throw(/DEAD_MAN_FLOOR/)
        expect(
            newMachine(
                WAIT_IN,
                { ...ECON, deadMan: 3600n, allowShortDeadMan: true },
                T0
            ).deadMan
        ).to.equal(3600n)
        // at or below MIN_STEP: refused even with the override
        expect(() =>
            newMachine(
                WAIT_IN,
                {
                    ...ECON,
                    deadMan: K17Machine.MIN_STEP,
                    allowShortDeadMan: true,
                },
                T0
            )
        ).to.throw(/MIN_STEP/)
        expect(() =>
            newMachine(WAIT_IN, { ...ECON, deadMan: -1n }, T0)
        ).to.throw(/negative/)
        expect(() =>
            newMachine(WAIT_IN, { ...ECON, deadMan: K17Machine.MIN_STEP }, T0)
        ).to.throw(/MIN_STEP/)
    })

    it('v3.1: dead-man fires at exactly lastTime + deadMan on a machine blocked on IN, not one second earlier', async () => {
        const m = await deployDeadMan(WAIT_IN, DEAD_MAN)
        // One second early: the program runs and needs a witness.
        expect(() =>
            planCycle(m, BigInt(FUNDING), T0 + DEAD_MAN - 1n, keeperA)
        ).to.throw(/needs a witness/)
        // The interpreter agrees: the refund layout at T0 + deadMan - 1
        // is refused because IN asserts a witness.
        const plan = deadManPlanFor(m)
        expect(plan.deadManHalt).to.be.true
        expect(plan.halted).to.be.true
        await expect(sendPlan(m, plan, T0 + DEAD_MAN - 1n)).to.be.rejectedWith(
            /witness required/
        )
        // At exactly T0 + deadMan: no witness needed, refund plus reward.
        const r = await cycle(m, BigInt(FUNDING), T0 + DEAD_MAN, keeperA)
        expect(r.plan.deadManHalt).to.be.true
        expect(r.plan.reward).to.equal(ECON.rewardMax)
        expectFaultRefund(r, BigInt(FUNDING))
        expect(addressOf(r.tx.outputs[1])).to.equal(keeperA.toString())
        expect(BigInt(r.tx.outputs[1].satoshis)).to.equal(ECON.rewardMax)
        // nothing ran: the state is the deployed one
        expect(r.plan.nextState.pc).to.equal(0n)
        expect(r.plan.nextState.out).to.equal('')
    })

    it('v3.1: a dead-man cycle that pays the keeper rewardMax + 1 is refused by the interpreter', async () => {
        const m = await deployDeadMan(WAIT_IN, DEAD_MAN)
        const honest = deadManPlanFor(m)
        expect(honest.reward).to.equal(ECON.rewardMax)
        // Control: the honest dead-man transaction verifies.
        const ok = await buildStepTx(m, honest, T0 + DEAD_MAN, '')
        expect(ok.verifyInputScript(0).success).to.equal(true)
        // One satoshi more to the keeper, one less to the beneficiary.
        const greedy: CyclePlan = {
            ...honest,
            reward: honest.reward + 1n,
            remaining: honest.remaining - 1n,
        }
        const bad = await buildStepTx(m, greedy, T0 + DEAD_MAN, '')
        expect(BigInt(bad.outputs[1].satoshis)).to.equal(ECON.rewardMax + 1n)
        expectScriptRefused(bad)
    })

    it('v3.1: dead-man counts from the last live cycle and never fires when disabled', async () => {
        // deadMan 0: a year of silence still needs the witness.
        const off = await deployDeadMan(WAIT_IN, 0n)
        const late = T0 + 365n * 86_400n
        expect(() => planCycle(off, BigInt(FUNDING), late, keeperA)).to.throw(
            /needs a witness/
        )
        // The refund layout (taken from a twin machine with a dead-man,
        // same outputs: capped reward) is refused by the interpreter.
        const twin = newMachine(
            WAIT_IN,
            { ...ECON, deadMan: DEAD_MAN },
            T0,
            rosterOf(),
            undefined,
            TEST_ID
        )
        await expect(
            sendPlan(off, deadManPlanFor(twin), late)
        ).to.be.rejectedWith(/witness required/)

        // With a dead-man, a live cycle moves lastTime and so the deadline.
        const m = await deployDeadMan(WAIT_IN, DEAD_MAN)
        const t1 = T0 + 600n
        const r1 = await cycle(m, BigInt(FUNDING), t1, keeperA, {}, [7n])
        expect(r1.plan.deadManHalt).to.be.false
        const n1 = r1.next as K17Machine
        expect(n1.lastTime).to.equal(t1)
        expect(n1.deadMan).to.equal(DEAD_MAN)
        // T0 + deadMan is no longer enough ...
        expect(() =>
            planCycle(n1, r1.plan.remaining, T0 + DEAD_MAN, keeperA)
        ).to.throw(/needs a witness/)
        // ... t1 + deadMan is.
        const r2 = await cycle(n1, r1.plan.remaining, t1 + DEAD_MAN, keeperA)
        expect(r2.plan.deadManHalt).to.be.true
        expectFaultRefund(r2, r1.plan.remaining)
    })

    it('v3.1: a tree machine blocked on MEMBER with an empty tree escapes via the dead-man', async () => {
        const prog = assemble(['MEMBER', 'OUT', 'YIELD', 'LIT', 0, 'IF', 0])
        const m = await deployDeadMan(prog, DEAD_MAN, {
            sponsorKeyHash: keyHash(sponsor.pub),
        })
        expect(m.rosterRoot).to.equal(EMPTY_HASHES[16])
        // No member exists, so nobody can supply a proof.
        expect(() =>
            planCycle(m, BigInt(FUNDING), T0 + 600n, keeperA)
        ).to.throw(/needs a witness/)
        // The dead-man cycle carries no tree arguments and still verifies.
        const r = await cycle(m, BigInt(FUNDING), T0 + DEAD_MAN, keeperA)
        expect(r.plan.deadManHalt).to.be.true
        expect(r.plan.treeOp).to.equal('none')
        expect(r.plan.leafPre).to.equal('')
        expect(r.plan.proof).to.equal('')
        expectFaultRefund(r, BigInt(FUNDING))
    })

    it('v3.1: a live cycle at lastTime + 59 is refused by the planner and the interpreter; + 60 is accepted', async () => {
        // A program without TIME, so its next state does not depend on the
        // clock: YIELD, then loop.
        const prog = assemble(['YIELD', 'LIT', 0, 'IF', 0])
        const m = await deploy(prog)
        expect(() => planCycle(m, BigInt(FUNDING), T0 + 59n, keeperA)).to.throw(
            /MIN_STEP/
        )
        // Build the +59 transaction by hand from the honest +60 plan: the
        // next state with lastTime + 59 and the reward of 59 s.
        const plan60 = planCycle(m, BigInt(FUNDING), T0 + 60n, keeperA)
        const next59 = (plan60.next as K17Machine).next()
        next59.lastTime = T0 + 59n
        const reward59 = ECON.rewardMin + 59n * ECON.slope
        const plan59: CyclePlan = {
            ...plan60,
            next: next59,
            reward: reward59,
            remaining: BigInt(FUNDING) - reward59,
        }
        await expect(sendPlan(m, plan59, T0 + 59n)).to.be.rejectedWith(
            /MIN_STEP/
        )
        // The honest cycle at + 60 verifies and keeps the machine alive.
        const r = await cycle(m, BigInt(FUNDING), T0 + 60n, keeperA)
        expect(r.plan.halted).to.be.false
        expect((r.next as K17Machine).lastTime).to.equal(T0 + 60n)
    })

    it('v3.1: a faulting or halting cycle at lastTime + 0 is accepted (refund path exempt from MIN_STEP)', async () => {
        // A fault on the first instruction, at the deployment time itself.
        const bad = await deploy(assemble(['DROP', 'HALT']))
        const f = await cycle(bad, BigInt(FUNDING), T0, keeperA)
        expectFaultRefund(f, BigInt(FUNDING))
        expect(f.plan.reward).to.equal(ECON.rewardMin)
        // HALT right after a live cycle, at that cycle's own lockTime.
        const m = await deploy(assemble(['YIELD', 'HALT']))
        const r1 = await cycle(m, BigInt(FUNDING), T0 + 60n, keeperA)
        expect(r1.plan.halted).to.be.false
        const r2 = await cycle(
            r1.next as K17Machine,
            r1.plan.remaining,
            T0 + 60n,
            keeperA
        )
        expect(r2.plan.halted).to.be.true
        expectFaultRefund(r2, r1.plan.remaining)
    })
})
