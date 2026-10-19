/**
 * Keeper helpers: everything an off-chain party needs to advance a
 * K17Machine UTXO by one cycle.
 *
 * A keeper
 *   1. reads the machine state out of the current contract instance,
 *   2. runs the reference VM for K instructions,
 *   3. works out the reward the Dutch auction allows at the chosen nLockTime,
 *   4. builds the spending transaction: state (or beneficiary payout), reward
 *      to itself, the PAYSLOT payout (if the cycle made one), change.
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
import { createHash, randomBytes } from 'crypto'
import { RabinPubKey, RabinSig } from 'scrypt-ts-lib'
import { K17Machine, FIXED_ROSTER_SLOTS } from './contracts/k17Machine'
import {
    K17State,
    PaySlot,
    StepEnv,
    initialState,
    stepK,
    whoOf,
} from './k17/vm'
import { MEM_CELLS, CELL, encodeCell } from './k17/isa'
import { NO_SIG, pubKeyBytes } from './k17/attest'

/** Economic parameters fixed at deployment. */
export interface Economics {
    beneficiary: Addr
    rewardMin: bigint
    /** sats per second */
    slope: bigint
    rewardMax: bigint
}

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
 * Default instance id of a machine: sha256 over the program bytes, the
 * initial memory image and cell(deployTime).
 * Input: program hex, memory image hex (MEM_CELLS cells), deployment time.
 * Output: 64 lowercase hex chars.
 */
export function defaultInstanceId(
    progHex: string,
    memHex: string,
    deployTime: bigint
): string {
    return createHash('sha256')
        .update(Buffer.from(progHex + memHex + encodeCell(deployTime), 'hex'))
        .digest('hex')
}

/**
 * Create a fresh (not yet deployed) machine for a program.
 * Input: program hex, economics, deployment time (unix seconds), optional
 * fixed SIGVERIFY roster, optional initial memory image (MEM_CELLS cells as
 * hex, e.g. with memory roster slot 0 pre-filled; see `withSlot`), optional
 * 32-byte instance id hex (default `defaultInstanceId`; ATTEST and ENDORSE
 * signatures bind it). Throws if the instance id is not 32 bytes.
 * Output: contract instance with empty stacks and the given (default zeroed)
 * memory.
 */
export function newMachine(
    progHex: string,
    econ: Economics,
    deployTime: bigint,
    roster: Roster = rosterOf(),
    initialMemHex?: string,
    instanceIdHex?: string
): K17Machine {
    const s = initialState(
        progHex,
        initialMemHex === undefined ? undefined : initialMemHex.toLowerCase()
    )
    const instanceId = (
        instanceIdHex ?? defaultInstanceId(progHex, s.mem, deployTime)
    ).toLowerCase()
    if (!/^[0-9a-f]{64}$/.test(instanceId)) {
        throw new Error('instance id must be 32 bytes (64 hex chars)')
    }
    return new K17Machine(
        toByteString(progHex),
        econ.beneficiary,
        econ.rewardMin,
        econ.slope,
        econ.rewardMax,
        roster,
        toByteString(instanceId),
        s.pc,
        toByteString(s.ds),
        toByteString(s.rs),
        toByteString(s.mem),
        toByteString(s.out),
        deployTime
    )
}

/** Read the machine state out of a contract instance. */
export function stateOf(m: K17Machine): K17State {
    return {
        prog: m.prog,
        pc: m.pc,
        ds: m.ds,
        rs: m.rs,
        mem: m.mem,
        out: m.outLog,
        halted: false,
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

/** What one cycle will produce, computed off-chain before broadcasting. */
export interface CyclePlan {
    halted: boolean
    /** Total paid to the spender: auction reward plus released bounty. */
    reward: bigint
    /** Bounty portion of `reward` released by BOUNTY instructions. */
    bounty: bigint
    /** Witness cells for the unlocking script (hex). */
    witnessHex: string
    /** Attestation signature for the unlocking script (NO_SIG when none). */
    sig: RabinSig
    /** `keyA` argument of `step`: pubKeyBytes(attestKey) or '' (hex). */
    keyAHex: string
    /** `keyB` argument of `step`: pubKeyBytes(endorseKey) or '' (hex). */
    keyBHex: string
    /** `payout` argument of `step`: the ENDORSE payout or '' (hex). */
    payoutHex: string
    /** The PAYSLOT payout this cycle (output 2); undefined when none. */
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
 * and payout for ATTEST/ENDORSE. Output: the CyclePlan. Throws when the cycle
 * cannot form a valid transaction (missing or rejected witness, signature or
 * key). A PAYSLOT payout has priority over the keeper reward, which shrinks
 * (down to 0) so the payout is paid in full; only N > value - 1 is a fault,
 * as on chain: the plan is halted and carries no payslot.
 */
export function planCycle(
    m: K17Machine,
    value: bigint,
    lockTime: bigint,
    keeper?: bsv.Address,
    witness: bigint[] = [],
    sig: RabinSig = NO_SIG,
    keys: CycleKeys = {}
): CyclePlan {
    const cur = stateOf(m)
    assertWellFormed(cur)
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
    }
    const outcome = stepK(cur, env, K17Machine.K)
    if (outcome.status === 'need_witness') {
        throw new Error('cycle needs a witness cell the solver did not supply')
    }
    if (outcome.status === 'verify_failed') {
        throw new Error(
            'witness rejected by VERIFY, SIGVERIFY, ATTEST or ENDORSE'
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
    // The slot payout has priority over the auction reward.
    const reward = rewardAt(
        m,
        lockTime,
        value,
        outcome.bountyDue,
        payslot?.sats ?? 0n
    )
    const remaining = value - reward - (payslot?.sats ?? 0n)
    const witnessHex = witness.map((w) => encodeCell(w)).join('')
    const common = {
        reward,
        bounty: outcome.bountyDue,
        nextState,
        remaining,
        witnessHex,
        sig,
        keyAHex:
            keys.attestKey === undefined ? '' : pubKeyBytes(keys.attestKey),
        keyBHex:
            keys.endorseKey === undefined ? '' : pubKeyBytes(keys.endorseKey),
        payoutHex: keys.payoutHex ?? '',
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
 *   output 2: PAYSLOT payout to the slot's address (omitted when none)
 *   then:     change
 * Input: instance, plan, keeper address, overrides. Output: MethodCallOptions
 * to pass to `m.methods.step`.
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

/** Address -> Addr (hex pubkey hash) for contract arguments. */
export function addrOf(address: bsv.Address): Addr {
    return Addr(address.toObject().hash)
}
