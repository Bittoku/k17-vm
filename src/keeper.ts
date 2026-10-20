/**
 * Keeper helpers: everything an off-chain party needs to advance a
 * K17Machine UTXO by one cycle.
 *
 * A keeper
 *   1. reads the machine state out of the current contract instance,
 *   2. runs the reference VM for K instructions,
 *   3. works out the reward the Dutch auction allows at the chosen nLockTime,
 *   4. builds the spending transaction: state (or beneficiary payout), reward
 *      to itself, the PAYSLOT or PAYLEAF payout (if the cycle made one),
 *      change.
 *
 * A cycle that runs a roster-tree instruction (MEMBER) also supplies the
 * one Merkle proof of the cycle (`tree` argument of planCycle), which the
 * plan forwards to `step` as leafPre, proof and leafIndex.
 *
 * Clock rules (v3.1). A cycle that keeps the machine alive must use an
 * nLockTime at least K17Machine.MIN_STEP (60 s) after the machine's
 * lastTime; planCycle refuses an earlier one. A cycle that halts (HALT, a
 * fault, or the dead-man) may use any nLockTime from lastTime on. When the
 * machine has a dead-man interval (`deadMan` > 0) and nLockTime is at
 * least lastTime + deadMan, the cycle halts before its first instruction:
 * it needs no witness, signature or proof, refunds the beneficiary and
 * pays the keeper its reward (CyclePlan.deadManHalt). Note that the
 * first cycle after deployment counts from the deployment time.
 *
 * deadMan counts on the chain's clock, not wall time: nLockTime is bounded
 * above by the median time past (MTP), so a dead-man cycle becomes
 * mineable once MTP - 1 >= lastTime + deadMan. From then on a kill is the
 * profitable move for any keeper: it pays the same capped reward as a live
 * cycle, with about half the fee (no state output). Honest keepers cannot
 * push lastTime past MTP, so after any MTP jump of deadMan or more a
 * healthy machine can be killed. Choose deadMan as a multiple of the round
 * length (for example 30 days for daily rounds); newMachine refuses less
 * than DEAD_MAN_FLOOR (6 h) unless `econ.allowShortDeadMan` is set.
 *
 * Throughput: with MIN_STEP, a keeper that uses lockTime = MTP - 1 gets
 * about one live cycle per block and no clock lag. Stepping by exactly
 * lastTime + 60 allows up to about 10 cycles per block (MTP moves about
 * 600 s per block), but lastTime then trails MTP, and that lag brings the
 * dead-man closer in real time.
 * Any honest cycle at MTP - 1 removes the lag.
 *
 * The functions here are pure plumbing; the economics live in the contract.
 */

import {
    Addr,
    FixedArray,
    MethodCallOptions,
    StatefulNext,
    bsv,
    toByteString,
} from 'scrypt-ts'
import { randomBytes } from 'crypto'
import { RabinPubKey, RabinSig } from 'scrypt-ts-lib'
import { K17Machine, FIXED_ROSTER_SLOTS } from './contracts/k17Machine'
import {
    K17State,
    PaySlot,
    StepEnv,
    TreeOp,
    deadManDue,
    initialState,
    stepK,
    whoOf,
} from './k17/vm'
import { MEM_CELLS, CELL, Op, encodeCell } from './k17/isa'
import { NO_SIG, canonicalSig, pubKeyBytes } from './k17/attest'

/** Economic parameters fixed at deployment. */
export interface Economics {
    beneficiary: Addr
    rewardMin: bigint
    /** sats per second */
    slope: bigint
    rewardMax: bigint
    /**
     * Dead-man interval in seconds (v3.1): a cycle at nLockTime
     * >= lastTime + deadMan halts the machine and refunds the beneficiary,
     * whatever the program waits for. Optional; 0 (the default) disables it.
     */
    deadMan?: bigint
    /**
     * Test-only escape: allow 0 < deadMan < DEAD_MAN_FLOOR (it must still be
     * above MIN_STEP). Default false.
     */
    allowShortDeadMan?: boolean
}

/**
 * Smallest dead-man interval newMachine accepts without
 * `econ.allowShortDeadMan`: 6 hours, in seconds. A shorter interval lets
 * any keeper kill a healthy machine after an ordinary MTP jump (see the
 * module header).
 */
export const DEAD_MAN_FLOOR = 6n * 3600n

/** Fixed SIGVERIFY roster as the contract wants it: exactly FIXED_ROSTER_SLOTS keys. */
export type Roster = FixedArray<RabinPubKey, typeof FIXED_ROSTER_SLOTS>

/**
 * Pad a list of attester public keys to a full fixed (SIGVERIFY) roster with
 * zero (empty) slots. Input: up to FIXED_ROSTER_SLOTS keys. Output: roster.
 */
export function rosterOf(keys: RabinPubKey[] = []): Roster {
    if (keys.length > FIXED_ROSTER_SLOTS)
        throw new Error('too many roster keys')
    const r: RabinPubKey[] = []
    for (let i = 0; i < FIXED_ROSTER_SLOTS; i++) r.push(keys[i] ?? 0n)
    return r as unknown as Roster
}

/**
 * Fresh random instance id for a new machine. Random rather than derived
 * from the deployment, so two identical deployments never share an id.
 * Input: none. Output: 64 lowercase hex chars (32 random bytes).
 */
export function randomInstanceId(): string {
    return randomBytes(32).toString('hex')
}

/**
 * Create a fresh (not yet deployed) machine for a program.
 * Input: program hex, economics, deployment time (unix seconds), optional
 * fixed SIGVERIFY roster, optional initial memory image (MEM_CELLS cells as
 * hex, e.g. with memory roster slot 0 pre-filled; see `withSlot`), optional
 * 32-byte instance id as 64 lowercase hex chars (default: randomInstanceId;
 * pass a fixed id for deterministic tests), optional roster-tree settings:
 * `rosterRoot` (the starting tree root, default EMPTY_HASHES[16], the empty
 * tree) and `sponsorKeyHash` (sha256 of the sponsor's Rabin key, default 32
 * zero bytes = no sponsor), each 64 lowercase hex chars. Throws unless the
 * id is exactly 64 lowercase hex chars, or on a malformed tree setting.
 * ATTEST and ENDORSE signatures bind the instance id, and it is random, so
 * attesters must read `instanceId` from the deployed machine (the contract
 * instance or its locking script) before they sign anything for it.
 * Output: contract instance with empty stacks and the given (default zeroed)
 * memory. `econ.deadMan` (default 0n, disabled) becomes the immutable
 * dead-man interval, counted on the chain's MTP clock. It must be 0 or at
 * least DEAD_MAN_FLOOR (6 h); with `econ.allowShortDeadMan` (tests only)
 * any value above MIN_STEP is accepted. Anything else throws.
 * `econ.rewardMin` must be at least 1 sat (v3.1 canonical unlocking
 * script): then every cycle pays a keeper output, which pins the `keeper`
 * argument of `step` through hashOutputs. One edge stays: a PAYSLOT or
 * PAYLEAF payout (or a 1-sat balance) can clamp the reward to
 * value - 1 - N = 0, and then `keeper` is free (see README).
 */
export function newMachine(
    progHex: string,
    econ: Economics,
    deployTime: bigint,
    roster: Roster = rosterOf(),
    initialMemHex?: string,
    instanceIdHex?: string,
    tree: { rosterRoot?: string; sponsorKeyHash?: string } = {}
): K17Machine {
    const s = initialState(
        progHex,
        initialMemHex === undefined ? undefined : initialMemHex.toLowerCase(),
        tree
    )
    // With a zero reward no keeper output is built, so the keeper address
    // in the unlocking script would be free for a relayer to rewrite.
    if (econ.rewardMin < 1n) {
        throw new Error(
            'rewardMin must be at least 1 sat (a zero reward leaves the keeper argument unpinned)'
        )
    }
    const deadMan = econ.deadMan ?? 0n
    if (deadMan < 0n) throw new Error('deadMan must not be negative')
    // The contract accepts any value; the keeper refuses values that let
    // a keeper kill a healthy machine. With deadMan <= MIN_STEP no cycle
    // could ever stay alive; below DEAD_MAN_FLOOR an ordinary MTP jump makes
    // a kill due while honest keepers are still active.
    if (deadMan > 0n) {
        if (deadMan <= K17Machine.MIN_STEP) {
            throw new Error(
                `deadMan must be 0 (off) or above MIN_STEP (${K17Machine.MIN_STEP} s)`
            )
        }
        if (deadMan < DEAD_MAN_FLOOR && !econ.allowShortDeadMan) {
            throw new Error(
                `deadMan must be 0 (off) or at least DEAD_MAN_FLOOR (${DEAD_MAN_FLOOR} s); set allowShortDeadMan for tests`
            )
        }
    }
    const instanceId = instanceIdHex ?? randomInstanceId()
    if (!/^[0-9a-f]{64}$/.test(instanceId)) {
        throw new Error('instance id must be 32 bytes (64 lowercase hex chars)')
    }
    return new K17Machine(
        toByteString(progHex),
        econ.beneficiary,
        econ.rewardMin,
        econ.slope,
        econ.rewardMax,
        deadMan,
        roster,
        toByteString(instanceId),
        toByteString(s.sponsorKeyHash),
        s.pc,
        toByteString(s.ds),
        toByteString(s.rs),
        toByteString(s.mem),
        toByteString(s.out),
        deployTime,
        toByteString(s.rosterRoot),
        s.rosterSeq,
        toByteString(s.logHash)
    )
}

/**
 * Read the machine state out of a contract instance.
 * Input: contract instance. Output: the VM state, including the roster
 * tree state (rosterRoot, rosterSeq, logHash, sponsorKeyHash).
 */
export function stateOf(m: K17Machine): K17State {
    return {
        prog: m.prog,
        pc: m.pc,
        ds: m.ds,
        rs: m.rs,
        mem: m.mem,
        out: m.outLog,
        halted: false,
        rosterRoot: m.rosterRoot,
        rosterSeq: m.rosterSeq,
        logHash: m.logHash,
        sponsorKeyHash: m.sponsorKeyHash,
    }
}

/** Sanity check that memory has the size the contract expects. */
export function assertWellFormed(s: K17State): void {
    if (s.mem.length !== MEM_CELLS * CELL * 2)
        throw new Error('bad memory size')
}

/**
 * Mirror of the contract's reward accounting, so a keeper can predict the
 * reward without running the contract: `rewardFor(elapsed) + bountyDue`,
 * clamped so the machine keeps one satoshi, then (with a PAYSLOT payout)
 * clamped again so the slot payout is paid in full first.
 * Input: instance, nLockTime, UTXO value, released bounty, PAYSLOT sats
 * (0 = none; the caller handles payslotSats > value - 1 as a fault).
 * Output: the keeper's reward in sats (never negative).
 */
export function rewardAt(
    m: K17Machine,
    lockTime: bigint,
    value: bigint,
    bountyDue = 0n,
    payslotSats = 0n
): bigint {
    const elapsed = lockTime - m.lastTime
    if (elapsed < 0n) throw new Error('lockTime before lastTime')
    let r = m.rewardMin + m.slope * elapsed
    if (r > m.rewardMax) r = m.rewardMax
    r += bountyDue
    if (r > value - 1n) r = value - 1n
    if (payslotSats > 0n && r > value - 1n - payslotSats) {
        r = value - 1n - payslotSats
    }
    if (r < 0n) r = 0n
    return r
}

/**
 * Keys and payout the transaction supplies for ATTEST and ENDORSE. All
 * optional; a cycle that uses neither instruction passes `{}`.
 */
export interface CycleKeys {
    /** Rabin key the cycle's signature is made under (ATTEST, ENDORSE sponsor). */
    attestKey?: RabinPubKey
    /** New member's Rabin key (ENDORSE). */
    endorseKey?: RabinPubKey
    /** New member's 20-byte payout as 40 lowercase hex chars (ENDORSE). */
    payoutHex?: string
}

/**
 * The cycle's one roster-tree proof (see `src/k17/smt.ts`): leaf preimage
 * hex ('' for an empty leaf), 16-sibling proof hex (1024 chars, level 0
 * first) and the leaf index in [0, 65536). Usually `tree.proof(index)` of
 * the off-chain SparseMerkleTree that matches the machine's rosterRoot.
 */
export interface CycleTree {
    leafPre: string
    proof: string
    leafIndex: bigint
}

/** What one cycle will produce, computed off-chain before broadcasting. */
export interface CyclePlan {
    halted: boolean
    /**
     * True when the dead-man fired (v3.1): nLockTime >= lastTime + deadMan
     * with deadMan > 0, so the cycle halted before its first instruction.
     * Implies `halted`.
     */
    deadManHalt: boolean
    /** Total paid to the spender: auction reward plus released bounty. */
    reward: bigint
    /** Bounty portion of `reward` released by BOUNTY instructions. */
    bounty: bigint
    /** Witness cells for the unlocking script (hex): only the cells IN consumed. */
    witnessHex: string
    /**
     * Signature for the unlocking script: NO_SIG when no signature
     * instruction ran, else the given signature in canonical form
     * (canonicalSig, 0 < s < n/2).
     */
    sig: RabinSig
    /** `keyA` argument of `step`: pubKeyBytes(attestKey) when ATTEST, ENDORSE, ATTESTM, ADMIT or REMOVE ran, else '' (hex). */
    keyAHex: string
    /** `keyB` argument of `step`: pubKeyBytes(endorseKey) when ENDORSE or ADMIT ran, else '' (hex). */
    keyBHex: string
    /** `payout` argument of `step`: the ENDORSE or ADMIT payout when one ran, else '' (hex). */
    payoutHex: string
    /** `leafPre` argument of `step`: the tree leaf preimage when a tree instruction ran, else '' (hex). */
    leafPre: string
    /** `proof` argument of `step`: the 16-sibling tree proof when a tree instruction ran, else '' (hex). */
    proof: string
    /** `leafIndex` argument of `step` (a bigint, not a cell); 0 when unused. */
    leafIndex: bigint
    /** The tree operation the cycle ran ('none' when no tree instruction). */
    treeOp: TreeOp
    /**
     * The PAYSLOT or PAYLEAF payout this cycle; undefined when none
     * (`slot` is -1 for a PAYLEAF payout and is not used for the output).
     * Its output follows the keeper reward output when one exists (output
     * 1 when the reward is 0).
     */
    payslot?: PaySlot
    /** Next contract instance (undefined when halted). */
    next?: K17Machine
    nextState: K17State
    /**
     * Satoshis in the state output or the beneficiary payout: value less
     * reward less the PAYSLOT payout.
     */
    remaining: bigint
}

/**
 * Compute the plan for a cycle: next state, reward, PAYSLOT payout,
 * remaining value.
 * Input: current instance, its UTXO value (also what VALUE pushes), nLockTime
 * to use, keeper address, witness cells, optional signature, optional keys
 * and payout for ATTEST/ATTESTM/ENDORSE, optional roster-tree proof for
 * MEMBER (leafPre and proof hex in either case; the plan carries them
 * lowercased). The VM starts from the instance's rosterRoot, rosterSeq, logHash
 * and sponsorKeyHash. Output: the CyclePlan; `next` carries the predicted
 * rosterRoot, rosterSeq and logHash. Throws when the cycle cannot form a
 * valid transaction (missing or rejected witness, signature, key or tree
 * proof). A PAYSLOT or PAYLEAF payout has priority over the keeper reward,
 * which shrinks (down to 0) so the payout is paid in full; only
 * N > value - 1 is a fault, as on chain: the plan is halted and carries no
 * payslot. The VM gets the instance's deadMan and lastTime, so a due
 * dead-man gives a halted plan with `deadManHalt` set (v3.1).
 * Canonical arguments (v3.1): the plan carries only the unlocking
 * arguments the cycle used (consumed witness cells; keys, payout, tree
 * proof and signature only for the instructions that read them; '' and 0
 * otherwise) and the signature in canonical form, because the contract
 * refuses any other unlocking script. Extra inputs are dropped, not an
 * error.
 * Errors, in the order they are checked: 'lockTime before lastTime'
 * (before the VM runs); then the VM's 'needs a witness' or 'witness
 * rejected'; then the MIN_STEP error for a cycle that stays alive with a
 * lockTime earlier than lastTime + K17Machine.MIN_STEP (the contract
 * refuses it; v3.1).
 */
export function planCycle(
    m: K17Machine,
    value: bigint,
    lockTime: bigint,
    keeper?: bsv.Address,
    witness: bigint[] = [],
    sig: RabinSig = NO_SIG,
    keys: CycleKeys = {},
    tree?: CycleTree
): CyclePlan {
    // Checked first, before the VM, so callers can match it reliably.
    if (lockTime < m.lastTime) throw new Error('lockTime before lastTime')
    const cur = stateOf(m)
    assertWellFormed(cur)
    // The VM accepts only lowercase leafPre and proof hex, while the chain
    // reads the bytes and ignores the case of the hex: lowercase them here
    // so a keeper that passes uppercase hex is not refused.
    const treeArg: CycleTree | undefined = tree && {
        leafPre: tree.leafPre.toLowerCase(),
        proof: tree.proof.toLowerCase(),
        leafIndex: tree.leafIndex,
    }
    const env: StepEnv = {
        lockTime,
        who: keeper ? whoOf(keeper.toObject().hash) : 0n,
        witness,
        roster: (m.roster as unknown as RabinPubKey[]).slice(),
        sig: sig.s === 0n ? undefined : sig,
        attestKey: keys.attestKey,
        endorseKey: keys.endorseKey,
        payout: keys.payoutHex,
        value,
        instanceId: m.instanceId,
        tree: treeArg,
        deadMan: m.deadMan,
        lastTime: m.lastTime,
    }
    const deadManHalt = deadManDue(env)
    // The contract faults a machine whose instanceId is not 32 bytes before
    // its first instruction; mirror that here.
    const outcome = /^[0-9a-fA-F]{64}$/.test(m.instanceId)
        ? stepK(cur, env, K17Machine.K)
        : {
              state: { ...cur, halted: true },
              status: 'halted' as const,
              witnessUsed: 0,
              bountyDue: 0n,
              payslot: undefined,
              treeOp: 'none' as TreeOp,
          }
    if (outcome.status === 'need_witness') {
        throw new Error('cycle needs a witness cell the solver did not supply')
    }
    if (outcome.status === 'verify_failed') {
        throw new Error(
            'witness rejected by VERIFY, SIGVERIFY, ATTEST, ENDORSE or a tree instruction'
        )
    }
    let nextState = outcome.state
    let payslot = outcome.payslot
    if (payslot && value - 1n - payslot.sats < 0n) {
        // The contract faults a PAYSLOT the balance cannot cover even with
        // no keeper reward (the VM leaves this to the planner): the machine
        // halts, the payout is dropped, the beneficiary is refunded.
        nextState = { ...nextState, halted: true }
        payslot = undefined
    }
    if (!nextState.halted && lockTime < m.lastTime + K17Machine.MIN_STEP) {
        // The contract asserts the minimum clock advance on the alive path
        // only; a halting cycle may use any nLockTime from lastTime on.
        throw new Error(
            `a cycle that keeps the machine alive needs lockTime >= lastTime + ${K17Machine.MIN_STEP} (MIN_STEP)`
        )
    }
    // The slot payout has priority over the auction reward.
    const reward = rewardAt(
        m,
        lockTime,
        value,
        outcome.bountyDue,
        payslot?.sats ?? 0n
    )
    const remaining = value - reward - (payslot?.sats ?? 0n)
    // Canonical unlocking arguments (v3.1): the contract refuses any
    // argument the cycle did not use, so send only what ran. The witness is
    // the cells IN consumed; keyA only for a signature instruction other
    // than SIGVERIFY; keyB and payout only for ENDORSE and ADMIT; the tree
    // proof only when a tree instruction ran; the signature only when one
    // was used, with s in its canonical form (0 < s < n/2).
    const sigOp = outcome.sigOp
    const keyAUsed = sigOp !== undefined && sigOp !== Op.SIGVERIFY
    const keyBUsed = sigOp === Op.ENDORSE || sigOp === Op.ADMIT
    const treeUsed = outcome.treeOp !== 'none'
    const witnessHex = witness
        .slice(0, outcome.witnessUsed)
        .map((w) => encodeCell(w))
        .join('')
    const common = {
        deadManHalt,
        reward,
        bounty: outcome.bountyDue,
        nextState,
        remaining,
        witnessHex,
        sig:
            sigOp === undefined || outcome.sigKey === undefined
                ? NO_SIG
                : canonicalSig(sig, outcome.sigKey),
        keyAHex:
            keyAUsed && keys.attestKey !== undefined
                ? pubKeyBytes(keys.attestKey)
                : '',
        keyBHex:
            keyBUsed && keys.endorseKey !== undefined
                ? pubKeyBytes(keys.endorseKey)
                : '',
        payoutHex: keyBUsed ? keys.payoutHex ?? '' : '',
        leafPre: treeUsed ? treeArg?.leafPre ?? '' : '',
        proof: treeUsed ? treeArg?.proof ?? '' : '',
        leafIndex: treeUsed ? treeArg?.leafIndex ?? 0n : 0n,
        treeOp: outcome.treeOp,
        payslot,
    }
    if (nextState.halted) {
        return { halted: true, ...common }
    }
    const next = m.next()
    next.pc = nextState.pc
    next.ds = toByteString(nextState.ds)
    next.rs = toByteString(nextState.rs)
    next.mem = toByteString(nextState.mem)
    next.outLog = toByteString(nextState.out)
    next.lastTime = lockTime
    next.rosterRoot = toByteString(nextState.rosterRoot)
    next.rosterSeq = nextState.rosterSeq
    next.logHash = toByteString(nextState.logHash)
    return { halted: false, next, ...common }
}

/** Options the test harness may override to build deliberately bad txs. */
export interface CycleOverrides {
    /** Pay this reward instead of the permitted one. */
    reward?: bigint
    /** Use this next instance instead of the computed one (tampering). */
    next?: K17Machine
    /** nSequence for the contract input. */
    sequence?: number
    /** Put this many fee inputs BEFORE the machine input (attack shape). */
    leadingFeeInputs?: number
}

/**
 * Install a transaction builder on `m` for one call of `step` that lays the
 * outputs out exactly as the contract expects:
 *   output 0: next state, or P2PKH to the beneficiary when halted
 *   output 1: reward to the keeper (omitted when the reward is 0)
 *   next:     PAYSLOT/PAYLEAF payout to its address (omitted when none);
 *             output 2, or output 1 when the reward is 0
 *   then:     change
 * Input: instance, plan, keeper address, overrides. Output: MethodCallOptions
 * to pass to `m.methods.step`.
 *
 * Change-output rule (v3.1 canonical unlocking script): a cycle
 * transaction must carry a positive change output. scrypt-ts passes the
 * change amount and address as hidden `step` arguments and builds no
 * change output when the amount is 0 or less, so without a change output a
 * relayer could rewrite both without changing the txid's outputs. With a
 * change output, hashOutputs pins them. In the normal path scrypt-ts adds
 * the fee inputs and sizes the change output after this builder returns
 * (`autoPayfee`, which reserves at least 1 sat of change), so the builder
 * can only check the inputs it adds itself: it throws (assertChangeOutput)
 * when it built more than one input and there is no change output. Callers
 * that add inputs in another way should call assertChangeOutput on the
 * final transaction before they broadcast it.
 */
export function bindCycleBuilder(
    m: K17Machine,
    plan: CyclePlan,
    keeper: bsv.Address,
    lockTime: bigint,
    overrides: CycleOverrides = {}
): MethodCallOptions<K17Machine> {
    const reward = overrides.reward ?? plan.reward
    const nextInstance = overrides.next ?? plan.next
    const payslotSats = plan.payslot?.sats ?? 0n
    const value = plan.remaining + plan.reward + payslotSats
    const remaining = value - reward - payslotSats

    m.bindTxBuilder(
        'step',
        async (current: K17Machine, options: MethodCallOptions<K17Machine>) => {
            const tx = new bsv.Transaction()
            const leading = overrides.leadingFeeInputs ?? 0
            if (leading > 0) {
                // Synthetic P2PKH inputs owned by the signer, placed ahead of
                // the machine. Only used by tests to build the attack shape.
                const feeAddress = await current.signer.getDefaultAddress()
                for (let i = 0; i < leading; i++) {
                    tx.from({
                        txId: randomBytes(32).toString('hex'),
                        outputIndex: 0,
                        script: bsv.Script.fromAddress(feeAddress).toHex(),
                        satoshis: 100000,
                    })
                }
            }
            tx.addInput(current.buildContractInput(options.fromUTXO))
            const atInputIndex = leading
            const nexts: StatefulNext<K17Machine>[] = []
            if (plan.halted || !nextInstance) {
                tx.addOutput(
                    new bsv.Transaction.Output({
                        script: bsv.Script.buildPublicKeyHashOut(
                            bsv.Address.fromPublicKeyHash(
                                Buffer.from(current.beneficiary, 'hex'),
                                keeper.network
                            )
                        ),
                        satoshis: Number(remaining),
                    })
                )
            } else {
                tx.addOutput(
                    new bsv.Transaction.Output({
                        script: nextInstance.lockingScript,
                        satoshis: Number(remaining),
                    })
                )
                nexts.push({
                    instance: nextInstance,
                    balance: Number(remaining),
                    atOutputIndex: 0,
                })
            }
            if (reward > 0n) {
                tx.addOutput(
                    new bsv.Transaction.Output({
                        script: bsv.Script.buildPublicKeyHashOut(keeper),
                        satoshis: Number(reward),
                    })
                )
            }
            if (plan.payslot) {
                tx.addOutput(
                    new bsv.Transaction.Output({
                        script: bsv.Script.buildPublicKeyHashOut(
                            bsv.Address.fromPublicKeyHash(
                                Buffer.from(plan.payslot.payoutHex, 'hex'),
                                keeper.network
                            )
                        ),
                        satoshis: Number(plan.payslot.sats),
                    })
                )
            }
            tx.change(
                options.changeAddress ||
                    (await current.signer.getDefaultAddress())
            )
            tx.setInputSequence(atInputIndex, overrides.sequence ?? 0xfffffffe)
            tx.setLockTime(Number(lockTime))
            assertChangeOutput(tx)
            return { tx, atInputIndex, nexts, next: nexts[0] }
        }
    )

    return {
        lockTime: Number(lockTime),
        sequence: overrides.sequence ?? 0xfffffffe,
        next:
            nextInstance && !plan.halted
                ? {
                      instance: nextInstance,
                      balance: Number(remaining),
                      atOutputIndex: 0,
                  }
                : undefined,
    }
}

/**
 * Check the change-output rule of a cycle transaction (v3.1 canonical
 * unlocking script; see bindCycleBuilder).
 * Input: the transaction. Output: none. Throws when the transaction has
 * fee inputs (more than one input) but no change output, because the
 * hidden changeAmount and changeAddress arguments of `step` are then not
 * pinned by the outputs. A transaction with the machine input only (the
 * state before scrypt-ts adds fee inputs) passes.
 */
export function assertChangeOutput(tx: bsv.Transaction): void {
    if (tx.inputs.length > 1 && tx.getChangeOutput() === null) {
        throw new Error(
            'cycle transaction has fee inputs but no change output (the change arguments of step would be unpinned)'
        )
    }
}

/** Address -> Addr (hex pubkey hash) for contract arguments. */
export function addrOf(address: bsv.Address): Addr {
    return Addr(address.toObject().hash)
}
