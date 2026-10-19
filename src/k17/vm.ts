/**
 * K17 reference virtual machine (off-chain).
 *
 * This is the executable specification of the K17 machine. Keepers and
 * solvers use it to compute the next state before building a spending
 * transaction, and the tests use it to cross-check the on-chain sCrypt
 * interpreter. Its semantics must match `contracts/k17Machine.ts` exactly;
 * the differential tests in `tests/k17Machine.test.ts` enforce that.
 *
 * All state fields are hex strings or bigints so they can be passed straight
 * into sCrypt contract properties.
 */

import { createHash } from 'crypto'
import { RabinPubKey, RabinSig, RabinVerifier } from 'scrypt-ts-lib'
import { toByteString } from 'scrypt-ts'
import {
    CELL,
    CELL_MOD,
    DS_MAX,
    HAS_OPERAND,
    MEM_CELLS,
    OUT_MAX,
    Op,
    ROSTER_MAX,
    ROSTER_BASE,
    ROSTER_SLOTS,
    RS_MAX,
    SLOT_CELLS,
    attestMessage,
    decodeCell,
    encodeCell,
    slotCells,
    slotOffset,
} from './isa'
import { keyHash, endorseMessage, attestMessageFor } from './attest'

/** Complete machine state. Everything the contract carries between cycles. */
export interface K17State {
    /** Immutable program bytes (hex). */
    prog: string
    /** Program counter, byte offset into prog. */
    pc: bigint
    /** Data stack, cells, top at end (hex). */
    ds: string
    /** Return stack, cells, top at end (hex). */
    rs: string
    /** Memory, MEM_CELLS cells (hex). */
    mem: string
    /** Output log, cells, append-only (hex). */
    out: string
    /** True once HALT or a fault has been executed. */
    halted: boolean
}

/** Per-transaction environment visible to the program. */
export interface StepEnv {
    /** nLockTime of the spending transaction (TIME). */
    lockTime: bigint
    /** First 4 bytes of the spender's address as a cell (WHO). */
    who: bigint
    /** Witness cells supplied in the unlocking script (IN). */
    witness: bigint[]
    /** Roster public keys of the machine (SIGVERIFY); zero = empty slot. */
    roster?: RabinPubKey[]
    /** The one Rabin signature carried by this transaction (SIGVERIFY). */
    sig?: RabinSig
    /** The Rabin public key `sig` is made under (ATTEST); its hash must match the slot. */
    attestKey?: RabinPubKey
    /** The new member's Rabin public key (ENDORSE); its hash is written to the new slot. */
    endorseKey?: RabinPubKey
    /** The new member's payout, 20 bytes as 40 lowercase hex chars (ENDORSE). */
    payout?: string
    /** The machine's 32-byte instance id as 64 hex chars (ATTEST, ENDORSE messages). */
    instanceId?: string
    /** Balance of the machine output being spent, in satoshis (VALUE); default 0. */
    value?: bigint
}

/** Build an environment; `lockTime` alone is enough for programs without I/O. */
export function envOf(
    lockTime: bigint,
    who = 0n,
    witness: bigint[] = []
): StepEnv {
    return { lockTime, who, witness }
}

/**
 * Check a Rabin attestation exactly as the contract does.
 * Input: tag and value cells, signature, roster public key. Output: true
 * when `sig` signs attestMessage(tag, value) under `pub`.
 */
export function verifyAttestation(
    tag: bigint,
    value: bigint,
    sig: RabinSig,
    pub: RabinPubKey
): boolean {
    return RabinVerifier.verifySig(
        toByteString(attestMessage(tag, value)),
        sig,
        pub
    )
}

/**
 * Check an ATTEST signature exactly as the contract does.
 * Input: instance id hex, tag and value cells, signature, member key.
 * Output: true when `sig` signs attestMessageFor(instanceId, tag, value)
 * under `pub`.
 */
export function verifyAttestationFor(
    instanceIdHex: string,
    tag: bigint,
    value: bigint,
    sig: RabinSig,
    pub: RabinPubKey
): boolean {
    return RabinVerifier.verifySig(
        toByteString(attestMessageFor(instanceIdHex, tag, value)),
        sig,
        pub
    )
}

/**
 * Check a roster endorsement signature.
 * Input: instance id hex, tag cell, new member key, payout hex, target slot
 * cell, signature, endorser's key.
 * Output: true when `sig` signs endorseMessage(instanceId, tag, newPub,
 * payoutHex, newSlot) under `endorser`.
 */
export function verifyEndorsement(
    instanceIdHex: string,
    tag: bigint,
    newPub: RabinPubKey,
    payoutHex: string,
    newSlot: bigint,
    sig: RabinSig,
    endorser: RabinPubKey
): boolean {
    return RabinVerifier.verifySig(
        toByteString(
            endorseMessage(instanceIdHex, tag, newPub, payoutHex, newSlot)
        ),
        sig,
        endorser
    )
}

/**
 * Outcome of one instruction.
 *   ok             state advanced
 *   halted         HALT executed (state.halted = true)
 *   fault          illegal operation; treated as HALT (state.halted = true)
 *   need_witness   IN with no witness left: the transaction would be invalid
 *   verify_failed  VERIFY saw zero: the transaction would be invalid
 *   yield          YIELD executed: state advanced, cycle ends here
 */
export type Status =
    | 'ok'
    | 'halted'
    | 'fault'
    | 'need_witness'
    | 'verify_failed'
    | 'yield'

/** A payout recorded by PAYSLOT: roster slot, its payout hash (hex) and satoshis. */
export interface PaySlot {
    slot: number
    payoutHex: string
    sats: bigint
}

/** Result of executing one instruction. */
export interface StepResult {
    state: K17State
    status: Status
    /** Convenience: status is 'fault'. */
    faulted: boolean
    /** Witness cells consumed so far (index into env.witness). */
    witnessIndex: number
    /** Extra satoshis authorised to the spender so far by BOUNTY. */
    bountyDue: bigint
    /** True once SIGVERIFY has consumed this transaction's signature. */
    sigUsed: boolean
    /** The payout recorded by PAYSLOT this cycle, if any. */
    payslot?: PaySlot
}

/**
 * Build the initial state for a program: empty stacks, memory zeroed or
 * taken from an optional pre-filled image.
 * Input: program hex; optional memory image hex of exactly MEM_CELLS * CELL * 2
 * characters (throws otherwise). Output: the starting K17State.
 */
export function initialState(progHex: string, memHex?: string): K17State {
    if (
        memHex !== undefined &&
        !new RegExp(`^([0-9a-fA-F]{2}){${MEM_CELLS * CELL}}$`).test(memHex)
    ) {
        throw new Error(
            `memory image must be ${MEM_CELLS * CELL * 2} hex characters`
        )
    }
    return {
        prog: progHex,
        pc: 0n,
        ds: '',
        rs: '',
        mem: memHex ?? '00'.repeat(MEM_CELLS * CELL),
        out: '',
        halted: false,
    }
}

/** Number of cells in a cell byte string. */
function depth(hex: string): number {
    return hex.length / (CELL * 2)
}

/** Read cell `index` (0-based) from a cell byte string. */
function cellAt(hex: string, index: number): bigint {
    return decodeCell(hex.slice(index * CELL * 2, (index + 1) * CELL * 2))
}

/** Replace cell `index` in a cell byte string. */
function setCell(hex: string, index: number, value: bigint): string {
    const start = index * CELL * 2
    return hex.slice(0, start) + encodeCell(value) + hex.slice(start + CELL * 2)
}

/**
 * Write a roster slot into a memory image.
 * Input: memory hex, slot number, SLOT_CELLS cell values (see slotCells).
 * Output: the memory hex with those cells written at slotOffset(slot).
 */
export function withSlot(
    memHex: string,
    slot: number,
    cells: bigint[]
): string {
    if (cells.length !== SLOT_CELLS) {
        throw new Error(`a slot is ${SLOT_CELLS} cells, got ${cells.length}`)
    }
    const base = slotOffset(slot)
    let mem = memHex
    cells.forEach((value, i) => {
        mem = setCell(mem, base + i, value)
    })
    return mem
}

/**
 * Read a roster slot out of a memory image.
 * Input: memory hex, slot number. Output: the 32-byte key hash (hex), the
 * 20-byte payout hash (hex) and whether the slot is empty (all eight hash
 * cells zero).
 */
export function readSlot(
    mem: string,
    slot: number
): { hashHex: string; payoutHex: string; empty: boolean } {
    const base = slotOffset(slot)
    const hashHex = mem.slice(base * CELL * 2, (base + 8) * CELL * 2)
    const payoutHex = mem.slice(
        (base + 8) * CELL * 2,
        (base + SLOT_CELLS) * CELL * 2
    )
    return { hashHex, payoutHex, empty: /^0*$/.test(hashHex) }
}

/** HASH instruction: first 4 bytes of sha256 over the 4-byte cell, as a cell. */
export function hashCell(value: bigint): bigint {
    const digest = createHash('sha256')
        .update(Buffer.from(encodeCell(value), 'hex'))
        .digest('hex')
    return decodeCell(digest.slice(0, CELL * 2))
}

/** WHO value for an address hash (20-byte hex): its first 4 bytes as a cell. */
export function whoOf(addressHashHex: string): bigint {
    return decodeCell(addressHashHex.slice(0, CELL * 2))
}

/**
 * Execute exactly one instruction.
 *
 * Input: current state, environment, witness index consumed so far, bounty
 * authorised so far, whether the cycle's signature is already consumed, and
 * the payout PAYSLOT already recorded this cycle (if any).
 * Output: new state and status. Faults set `halted`; they are never thrown.
 * `need_witness` and `verify_failed` leave the state unchanged and mean the
 * enclosing transaction cannot be valid (SIGVERIFY reports `need_witness`
 * when no signature is left and `verify_failed` when it does not check).
 */
export function step(
    s: K17State,
    env: StepEnv | bigint,
    witnessIndex = 0,
    bountyDue = 0n,
    sigUsed = false,
    payslot?: PaySlot
): StepResult {
    const e: StepEnv = typeof env === 'bigint' ? envOf(env) : env
    const unchanged = (status: Status): StepResult => ({
        state: s,
        status,
        faulted: false,
        witnessIndex,
        bountyDue,
        sigUsed,
        payslot,
    })
    if (s.halted) return unchanged('halted')

    const prog = Buffer.from(s.prog, 'hex')
    const pc = Number(s.pc)
    const fault = (): StepResult => ({
        state: { ...s, halted: true },
        status: 'fault',
        faulted: true,
        witnessIndex,
        bountyDue,
        sigUsed,
        payslot,
    })

    if (pc >= prog.length) return fault()
    const op = prog[pc] as Op
    let operand = 0n
    let nextPc = BigInt(pc + 1)
    if (HAS_OPERAND.has(op)) {
        if (pc + 1 + CELL > prog.length) return fault()
        operand = BigInt(prog.readUInt32LE(pc + 1))
        nextPc = BigInt(pc + 1 + CELL)
    }

    let ds = s.ds
    let rs = s.rs
    let mem = s.mem
    let out = s.out
    let halted = false
    let yielded = false
    let wi = witnessIndex
    let bounty = bountyDue
    let su = sigUsed
    let ps = payslot

    const dsDepth = depth(ds)
    const rsDepth = depth(rs)
    const pop = (): bigint => {
        const v = cellAt(ds, depth(ds) - 1)
        ds = ds.slice(0, ds.length - CELL * 2)
        return v
    }
    const push = (v: bigint): void => {
        ds += encodeCell(((v % CELL_MOD) + CELL_MOD) % CELL_MOD)
    }

    switch (op) {
        case Op.HALT:
            halted = true
            break
        case Op.STORE: {
            if (dsDepth < 2) return fault()
            const addr = pop()
            const value = pop()
            if (addr >= BigInt(ROSTER_BASE)) return fault() // roster is write-protected
            mem = setCell(mem, Number(addr), value)
            break
        }
        case Op.ADD: {
            if (dsDepth < 2) return fault()
            const n2 = pop()
            const n1 = pop()
            push(n1 + n2)
            break
        }
        case Op.SUB: {
            if (dsDepth < 2) return fault()
            const n2 = pop()
            const n1 = pop()
            push(n1 - n2)
            break
        }
        case Op.TO_R: {
            if (dsDepth < 1) return fault()
            if (rsDepth >= RS_MAX) return fault()
            rs += encodeCell(pop())
            break
        }
        case Op.FETCH: {
            if (dsDepth < 1) return fault()
            const addr = pop()
            if (addr >= BigInt(MEM_CELLS)) return fault()
            push(cellAt(mem, Number(addr)))
            break
        }
        case Op.AND: {
            if (dsDepth < 2) return fault()
            const n2 = pop()
            const n1 = pop()
            push(n1 & n2)
            break
        }
        case Op.DROP: {
            if (dsDepth < 1) return fault()
            pop()
            break
        }
        case Op.DUP: {
            if (dsDepth < 1) return fault()
            if (dsDepth >= DS_MAX) return fault()
            const n1 = pop()
            push(n1)
            push(n1)
            break
        }
        case Op.OR: {
            if (dsDepth < 2) return fault()
            const n2 = pop()
            const n1 = pop()
            push(n1 | n2)
            break
        }
        case Op.OVER: {
            if (dsDepth < 2) return fault()
            if (dsDepth >= DS_MAX) return fault()
            const n2 = pop()
            const n1 = pop()
            push(n1)
            push(n2)
            push(n1)
            break
        }
        case Op.R_FROM: {
            if (rsDepth < 1) return fault()
            if (dsDepth >= DS_MAX) return fault()
            const v = cellAt(rs, rsDepth - 1)
            rs = rs.slice(0, rs.length - CELL * 2)
            push(v)
            break
        }
        case Op.SWAP: {
            if (dsDepth < 2) return fault()
            const n2 = pop()
            const n1 = pop()
            push(n2)
            push(n1)
            break
        }
        case Op.XOR: {
            if (dsDepth < 2) return fault()
            const n2 = pop()
            const n1 = pop()
            push(n1 ^ n2)
            break
        }
        case Op.IF: {
            if (dsDepth < 1) return fault()
            const flag = pop()
            if (flag === 0n) nextPc = operand
            break
        }
        case Op.CALL: {
            if (rsDepth >= RS_MAX) return fault()
            rs += encodeCell(nextPc)
            nextPc = operand
            break
        }
        case Op.EXIT: {
            if (rsDepth < 1) return fault()
            nextPc = cellAt(rs, rsDepth - 1)
            rs = rs.slice(0, rs.length - CELL * 2)
            break
        }
        case Op.LIT: {
            if (dsDepth >= DS_MAX) return fault()
            push(operand)
            break
        }
        case Op.ZEQ: {
            if (dsDepth < 1) return fault()
            const n1 = pop()
            push(n1 === 0n ? 1n : 0n)
            break
        }
        case Op.OUT: {
            if (dsDepth < 1) return fault()
            if (depth(out) >= OUT_MAX) return fault()
            out += encodeCell(pop())
            break
        }
        case Op.TIME: {
            if (dsDepth >= DS_MAX) return fault()
            push(e.lockTime % CELL_MOD)
            break
        }
        case Op.IN: {
            if (dsDepth >= DS_MAX) return fault()
            if (wi >= e.witness.length) return unchanged('need_witness')
            push(e.witness[wi])
            wi++
            break
        }
        case Op.VERIFY: {
            if (dsDepth < 1) return fault()
            const flag = pop()
            if (flag === 0n) return unchanged('verify_failed')
            break
        }
        case Op.BOUNTY: {
            bounty += operand
            break
        }
        case Op.MUL: {
            if (dsDepth < 2) return fault()
            const n2 = pop()
            const n1 = pop()
            push(n1 * n2)
            break
        }
        case Op.HASH: {
            if (dsDepth < 1) return fault()
            push(hashCell(pop()))
            break
        }
        case Op.WHO: {
            if (dsDepth >= DS_MAX) return fault()
            push(e.who)
            break
        }
        case Op.YIELD: {
            yielded = true
            break
        }
        case Op.MIN: {
            if (dsDepth < 2) return fault()
            const n2 = pop()
            const n1 = pop()
            push(n1 < n2 ? n1 : n2)
            break
        }
        case Op.MAX: {
            if (dsDepth < 2) return fault()
            const n2 = pop()
            const n1 = pop()
            push(n1 > n2 ? n1 : n2)
            break
        }
        case Op.DIV: {
            if (dsDepth < 2) return fault()
            const n2 = pop()
            const n1 = pop()
            if (n2 === 0n) return fault()
            push(n1 / n2)
            break
        }
        case Op.SIGVERIFY: {
            // TAG VAL --   tx invalid unless sig signs cell(TAG)||cell(VAL)
            if (dsDepth < 2) return fault()
            if (operand >= BigInt(ROSTER_MAX)) return fault()
            const pub = e.roster?.[Number(operand)] ?? 0n
            if (pub === 0n) return fault()
            if (su || !e.sig) return unchanged('need_witness')
            const value = pop()
            const tag = pop()
            if (!verifyAttestation(tag, value, e.sig, pub)) {
                return unchanged('verify_failed')
            }
            su = true
            break
        }
        case Op.ATTEST: {
            // TAG VAL SLOT --   the environment's key must hash to the slot's
            // key hash and its signature must cover cell(TAG)||cell(VAL)
            if (dsDepth < 3) return fault()
            const slot = cellAt(ds, dsDepth - 1)
            if (slot >= BigInt(ROSTER_SLOTS)) return fault()
            const entry = readSlot(mem, Number(slot))
            if (entry.empty) return fault()
            if (
                su ||
                !e.sig ||
                e.attestKey === undefined ||
                e.instanceId === undefined
            ) {
                return unchanged('need_witness')
            }
            if (keyHash(e.attestKey) !== entry.hashHex) {
                return unchanged('verify_failed')
            }
            pop()
            const value = pop()
            const tag = pop()
            if (
                !verifyAttestationFor(
                    e.instanceId,
                    tag,
                    value,
                    e.sig,
                    e.attestKey
                )
            ) {
                return unchanged('verify_failed')
            }
            su = true
            break
        }
        case Op.ENDORSE: {
            // TAG SLOT NEWSLOT --   the member at SLOT vouches for a new member,
            // whose slot cells are written into the empty slot NEWSLOT
            if (dsDepth < 3) return fault()
            const newSlot = cellAt(ds, dsDepth - 1)
            const slot = cellAt(ds, dsDepth - 2)
            if (slot >= BigInt(ROSTER_SLOTS)) return fault()
            const sponsor = readSlot(mem, Number(slot))
            if (sponsor.empty) return fault()
            if (newSlot >= BigInt(ROSTER_SLOTS)) return fault()
            if (!readSlot(mem, Number(newSlot)).empty) return fault()
            if (
                su ||
                !e.sig ||
                e.attestKey === undefined ||
                e.endorseKey === undefined ||
                e.payout === undefined ||
                e.instanceId === undefined
            ) {
                return unchanged('need_witness')
            }
            if (!/^[0-9a-f]{40}$/.test(e.payout)) {
                return unchanged('verify_failed')
            }
            if (keyHash(e.attestKey) !== sponsor.hashHex) {
                return unchanged('verify_failed')
            }
            pop()
            pop()
            const tag = pop()
            if (
                !verifyEndorsement(
                    e.instanceId,
                    tag,
                    e.endorseKey,
                    e.payout,
                    newSlot,
                    e.sig,
                    e.attestKey
                )
            ) {
                return unchanged('verify_failed')
            }
            mem = withSlot(
                mem,
                Number(newSlot),
                slotCells(keyHash(e.endorseKey), e.payout)
            )
            su = true
            break
        }
        case Op.VALUE: {
            if (dsDepth >= DS_MAX) return fault()
            push((e.value ?? 0n) % CELL_MOD)
            break
        }
        case Op.PAYSLOT: {
            // N SLOT --   pay N sats to the roster slot's payout address.
            // Every refusal here is caused by the program, so it is a fault
            // and drops the payout; it never invalidates the transaction.
            // (The contract also faults when N >= the balance; the VM leaves
            // that check to planCycle, next to the reward accounting.)
            // A second PAYSLOT is checked first: it always drops the
            // payout, however malformed it is.
            if (ps) return { ...fault(), payslot: undefined }
            if (dsDepth < 2) return fault()
            const slot = pop()
            const sats = pop()
            if (slot >= BigInt(ROSTER_SLOTS)) return fault()
            const entry = readSlot(mem, Number(slot))
            if (entry.empty) return fault()
            if (sats === 0n) return fault()
            ps = { slot: Number(slot), payoutHex: entry.payoutHex, sats }
            break
        }
        default:
            return fault()
    }

    return {
        state: { ...s, pc: nextPc, ds, rs, mem, out, halted },
        status: halted ? 'halted' : yielded ? 'yield' : 'ok',
        faulted: false,
        witnessIndex: wi,
        bountyDue: bounty,
        sigUsed: su,
        payslot: ps,
    }
}

/** Result of a whole cycle (K instructions). */
export interface CycleOutcome {
    state: K17State
    /** 'ok' or 'halted' means a valid transaction can be built (a YIELD reports 'ok'). */
    status: Status
    witnessUsed: number
    bountyDue: bigint
    /** The payout PAYSLOT recorded this cycle; undefined when none. */
    payslot?: PaySlot
}

/**
 * Execute up to `k` instructions, stopping early once halted or blocked.
 * This mirrors one on-chain cycle transaction with K unrolled steps.
 */
export function stepK(
    s: K17State,
    env: StepEnv | bigint,
    k: number
): CycleOutcome {
    const e: StepEnv = typeof env === 'bigint' ? envOf(env) : env
    let cur = s
    let wi = 0
    let bounty = 0n
    let su = false
    let ps: PaySlot | undefined
    let status: Status = cur.halted ? 'halted' : 'ok'
    for (let i = 0; i < k && status === 'ok'; i++) {
        const r = step(cur, e, wi, bounty, su, ps)
        if (r.status === 'need_witness' || r.status === 'verify_failed') {
            return {
                state: cur,
                status: r.status,
                witnessUsed: wi,
                bountyDue: bounty,
                payslot: ps,
            }
        }
        cur = r.state
        wi = r.witnessIndex
        bounty = r.bountyDue
        su = r.sigUsed
        ps = r.payslot
        status = r.status === 'fault' ? 'halted' : r.status
    }
    // A yield is a normal end of cycle from the transaction's point of view.
    if (status === 'yield') status = 'ok'
    return {
        state: cur,
        status,
        witnessUsed: wi,
        bountyDue: bounty,
        payslot: ps,
    }
}

/**
 * Run until HALT/fault/block or until `maxSteps` instructions have executed.
 * Input: state, environment, maxSteps. Output: final state, status, steps.
 */
export function run(
    s: K17State,
    env: StepEnv | bigint,
    maxSteps = 100_000
): {
    state: K17State
    steps: number
    status: Status
    bountyDue: bigint
    payslot?: PaySlot
} {
    const e: StepEnv = typeof env === 'bigint' ? envOf(env) : env
    let cur = s
    let steps = 0
    let wi = 0
    let bounty = 0n
    let su = false
    let ps: PaySlot | undefined
    let status: Status = cur.halted ? 'halted' : 'ok'
    while (status === 'ok' && steps < maxSteps) {
        const r = step(cur, e, wi, bounty, su, ps)
        if (r.status === 'need_witness' || r.status === 'verify_failed') {
            return {
                state: cur,
                steps,
                status: r.status,
                bountyDue: bounty,
                payslot: ps,
            }
        }
        cur = r.state
        wi = r.witnessIndex
        bounty = r.bountyDue
        su = r.sigUsed
        ps = r.payslot
        status =
            r.status === 'fault'
                ? 'halted'
                : r.status === 'yield'
                ? 'ok'
                : r.status
        steps++
    }
    return { state: cur, steps, status, bountyDue: bounty, payslot: ps }
}

/** Decode the output log into a list of cell values. */
export function outputLog(s: K17State): bigint[] {
    const cells: bigint[] = []
    for (let i = 0; i < depth(s.out); i++) cells.push(cellAt(s.out, i))
    return cells
}
