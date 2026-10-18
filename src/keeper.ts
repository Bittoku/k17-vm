/**
 * Keeper helpers: everything an off-chain party needs to advance a
 * K17Machine UTXO by one cycle.
 *
 * A keeper
 *   1. reads the machine state out of the current contract instance,
 *   2. runs the reference VM for K instructions,
 *   3. works out the reward the Dutch auction allows at the chosen nLockTime,
 *   4. builds the spending transaction: state (or beneficiary payout), reward
 *      to itself, change.
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
import { K17Machine, ROSTER_SLOTS } from './contracts/k17Machine'
import { K17State, StepEnv, initialState, stepK, whoOf } from './k17/vm'
import { MEM_CELLS, CELL, encodeCell } from './k17/isa'
import { NO_SIG } from './k17/attest'

/** Economic parameters fixed at deployment. */
export interface Economics {
    beneficiary: Addr
    rewardMin: bigint
    /** sats per second */
    slope: bigint
    rewardMax: bigint
}

/** Roster as the contract wants it: exactly ROSTER_SLOTS keys. */
export type Roster = FixedArray<RabinPubKey, typeof ROSTER_SLOTS>

/**
 * Pad a list of attester public keys to a full roster with zero (empty)
 * slots. Input: up to ROSTER_SLOTS keys. Output: roster.
 */
export function rosterOf(keys: RabinPubKey[] = []): Roster {
    if (keys.length > ROSTER_SLOTS) throw new Error('too many roster keys')
    const r: RabinPubKey[] = []
    for (let i = 0; i < ROSTER_SLOTS; i++) r.push(keys[i] ?? 0n)
    return r as unknown as Roster
}

/**
 * Create a fresh (not yet deployed) machine for a program.
 * Input: program hex, economics, deployment time (unix seconds), optional
 * attester roster. Output: contract instance with empty stacks and zeroed
 * memory.
 */
export function newMachine(
    progHex: string,
    econ: Economics,
    deployTime: bigint,
    roster: Roster = rosterOf()
): K17Machine {
    const s = initialState(progHex)
    return new K17Machine(
        toByteString(progHex),
        econ.beneficiary,
        econ.rewardMin,
        econ.slope,
        econ.rewardMax,
        roster,
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
 * Mirror of `K17Machine.rewardFor` plus the one-satoshi floor, so a keeper
 * can predict the reward without running the contract.
 */
export function rewardAt(
    m: K17Machine,
    lockTime: bigint,
    value: bigint,
    bountyDue = 0n
): bigint {
    const elapsed = lockTime - m.lastTime
    if (elapsed < 0n) throw new Error('lockTime before lastTime')
    let r = m.rewardMin + m.slope * elapsed
    if (r > m.rewardMax) r = m.rewardMax
    r += bountyDue
    if (r > value - 1n) r = value - 1n
    return r
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
    /** Next contract instance (undefined when halted). */
    next?: K17Machine
    nextState: K17State
    /** Satoshis in the state output or the beneficiary payout. */
    remaining: bigint
}

/**
 * Compute the plan for a cycle: next state, reward, remaining value.
 * Input: current instance, its UTXO value, nLockTime to use, keeper address,
 * witness cells, optional attestation signature.
 */
export function planCycle(
    m: K17Machine,
    value: bigint,
    lockTime: bigint,
    keeper?: bsv.Address,
    witness: bigint[] = [],
    sig: RabinSig = NO_SIG
): CyclePlan {
    const cur = stateOf(m)
    assertWellFormed(cur)
    const env: StepEnv = {
        lockTime,
        who: keeper ? whoOf(keeper.toObject().hash) : 0n,
        witness,
        roster: (m.roster as unknown as RabinPubKey[]).slice(),
        sig: sig.s === 0n ? undefined : sig,
    }
    const outcome = stepK(cur, env, K17Machine.K)
    if (outcome.status === 'need_witness') {
        throw new Error('cycle needs a witness cell the solver did not supply')
    }
    if (outcome.status === 'verify_failed') {
        throw new Error('witness rejected by VERIFY or SIGVERIFY')
    }
    const nextState = outcome.state
    const reward = rewardAt(m, lockTime, value, outcome.bountyDue)
    const remaining = value - reward
    const witnessHex = witness.map((w) => encodeCell(w)).join('')
    if (nextState.halted) {
        return {
            halted: true,
            reward,
            bounty: outcome.bountyDue,
            nextState,
            remaining,
            witnessHex,
            sig,
        }
    }
    const next = m.next()
    next.pc = nextState.pc
    next.ds = toByteString(nextState.ds)
    next.rs = toByteString(nextState.rs)
    next.mem = toByteString(nextState.mem)
    next.outLog = toByteString(nextState.out)
    next.lastTime = lockTime
    return {
        halted: false,
        reward,
        bounty: outcome.bountyDue,
        next,
        nextState,
        remaining,
        witnessHex,
        sig,
    }
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
 *   output 2: change
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
    const value = plan.remaining + plan.reward
    const remaining = value - reward

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
