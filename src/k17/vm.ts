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
import {
    EMPTY_HASHES,
    SparseMerkleTree,
    decodeLeafPre,
    encodeLeafPre,
} from './smt'
import {
    keyHash,
    endorseMessage,
    attestMessageFor,
    memberMessage,
    admitMessage,
    removeMessage,
} from './attest'

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
    /** Merkle root (64 lowercase hex) of the member roster tree; default EMPTY_HASHES[16]. */
    rosterRoot: string
    /** Count of roster mutations (admissions and removals) so far. */
    rosterSeq: bigint
    /** Running output-log hash (64 hex), advanced by OUTH; default all zero. */
    logHash: string
    /** sha256 of the sponsor's Rabin key (64 hex); all zero means no sponsor. */
    sponsorKeyHash: string
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
    /**
     * The cycle's single Merkle proof, consumed by MEMBER, ADMIT and REMOVE:
     * the leaf preimage hex ('' for an empty leaf), the 16-sibling proof hex
     * and the leaf index.
     */
    tree?: { leafPre: string; proof: string; leafIndex: bigint }
    /**
     * The machine's dead-man interval in seconds (contract `deadMan`,
     * v3.1); 0 or undefined disables it. Read by stepK and run only.
     */
    deadMan?: bigint
    /**
     * nLockTime of the transaction that produced the machine's current
     * state (contract `lastTime`). Needed with `deadMan`; the dead-man
     * check is off when it is undefined.
     */
    lastTime?: bigint
}

/**
 * Whether the dead-man halt fires for this transaction (v3.1), exactly as
 * the contract checks it at the top of `step`: deadMan > 0 and
 * lockTime >= lastTime + deadMan.
 * Input: the cycle's environment. Output: true when the cycle must halt
 * before its first instruction; false when deadMan or lastTime is unset.
 */
export function deadManDue(e: StepEnv): boolean {
    return (
        e.deadMan !== undefined &&
        e.lastTime !== undefined &&
        e.deadMan > 0n &&
        e.lockTime >= e.lastTime + e.deadMan
    )
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
 * Check an ATTESTM signature exactly as the contract does.
 * Input: instance id hex, tag and value cells, signature, member key.
 * Output: true when `sig` signs memberMessage(instanceId, tag, value)
 * (domain "K17T") under `pub`.
 */
export function verifyMemberAttestation(
    instanceIdHex: string,
    tag: bigint,
    value: bigint,
    sig: RabinSig,
    pub: RabinPubKey
): boolean {
    return RabinVerifier.verifySig(
        toByteString(memberMessage(instanceIdHex, tag, value)),
        sig,
        pub
    )
}

/**
 * Check an ADMIT signature exactly as the contract does.
 * Input: instance id hex, tag cell, roster sequence number, leaf index,
 * the new member's key, payout hex, signature, sponsor's key.
 * Output: true when `sig` signs admitMessage(instanceId, tag, seq,
 * leafIndex, newPub, payoutHex) under `sponsor`.
 */
export function verifyAdmission(
    instanceIdHex: string,
    tag: bigint,
    seq: bigint,
    leafIndex: bigint,
    newPub: RabinPubKey,
    payoutHex: string,
    sig: RabinSig,
    sponsor: RabinPubKey
): boolean {
    return RabinVerifier.verifySig(
        toByteString(
            admitMessage(instanceIdHex, tag, seq, leafIndex, newPub, payoutHex)
        ),
        sig,
        sponsor
    )
}

/**
 * Check a REMOVE signature exactly as the contract does (v3.1 layout).
 * Input: instance id hex, tag cell, roster sequence number, leaf index,
 * the removed member's key hash (64 hex) and payout (40 hex), signature,
 * sponsor's key.
 * Output: true when `sig` signs removeMessage(instanceId, tag, seq,
 * leafIndex, keyHashHex, payoutHex) under `sponsor`. Throws as
 * removeMessage does on a malformed key hash or payout.
 */
export function verifyRemoval(
    instanceIdHex: string,
    tag: bigint,
    seq: bigint,
    leafIndex: bigint,
    keyHashHex: string,
    payoutHex: string,
    sig: RabinSig,
    sponsor: RabinPubKey
): boolean {
    return RabinVerifier.verifySig(
        toByteString(
            removeMessage(
                instanceIdHex,
                tag,
                seq,
                leafIndex,
                keyHashHex,
                payoutHex
            )
        ),
        sig,
        sponsor
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

/**
 * A payout recorded by PAYSLOT or PAYLEAF: roster slot (-1 for a PAYLEAF
 * payout to a tree member), its payout hash (hex) and satoshis.
 */
export interface PaySlot {
    slot: number
    payoutHex: string
    sats: bigint
}

/** Which Merkle-tree operation a cycle has performed (at most one). */
export type TreeOp = 'none' | 'member' | 'admit' | 'remove'

/**
 * The roster member a cycle's MEMBER instruction bound.
 * Purpose: carries the verified leaf (its fields, preimage and proof) to the
 * later instructions of the same cycle (LASTROUND, ATTESTM, PAYLEAF; a bound
 * member makes a later ADMIT or REMOVE fault). Output of `step`/`stepK`;
 * never stored in the machine state.
 */
export interface BoundMember {
    /** sha256 of the member's Rabin key, 64 lowercase hex. */
    keyHash: string
    /** The member's 20-byte payout address, 40 lowercase hex. */
    payoutHex: string
    /** Last round the member was paid in (its admission round until then). */
    lastRound: bigint
    /** Leaf flags cell. */
    flags: bigint
    /** Leaf position in the tree, in [0, 65536). */
    leafIndex: bigint
    /** The 120-hex-char leaf preimage that was verified. */
    leafPre: string
    /** The 16-sibling proof hex (1024 chars) that was verified. */
    proof: string
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
    /** The tree operation performed so far this cycle; 'none' until MEMBER, ADMIT or REMOVE runs. */
    treeOp: TreeOp
    /** The member bound by MEMBER this cycle, if any. */
    member?: BoundMember
    /**
     * The leaf preimage hex this cycle wrote to the roster: the new 120-hex
     * leaf after PAYLEAF or ADMIT, '' (an empty leaf) after REMOVE, and
     * undefined when no leaf was written (including MEMBER alone). It
     * matches `state.rosterRoot`, so a mirror of the tree can apply it at
     * the cycle's leaf index. A fault after the write keeps it, as the
     * state at a fault keeps the new root.
     */
    leafAfter?: string
}

/**
 * Build the initial state for a program: empty stacks, memory zeroed or
 * taken from an optional pre-filled image.
 * Input: program hex; optional memory image hex of exactly MEM_CELLS * CELL * 2
 * characters (throws otherwise; either case, stored lowercase).
 * Optional `opts` sets the starting rosterRoot (default: the empty tree
 * root) and sponsorKeyHash (default: 32 zero bytes); each must be 64
 * lowercase hex chars or this throws.
 * Output: the starting K17State.
 */
export function initialState(
    progHex: string,
    memHex?: string,
    opts: { rosterRoot?: string; sponsorKeyHash?: string } = {}
): K17State {
    for (const [name, value] of Object.entries(opts)) {
        if (value !== undefined && !/^[0-9a-f]{64}$/.test(value)) {
            throw new Error(`${name} must be 64 lowercase hex characters`)
        }
    }
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
        // Lowercase so the image matches the contract's byte comparisons
        // and readSlot's hex comparisons.
        mem: memHex?.toLowerCase() ?? '00'.repeat(MEM_CELLS * CELL),
        out: '',
        halted: false,
        rosterRoot: opts.rosterRoot ?? EMPTY_HASHES[16],
        rosterSeq: 0n,
        logHash: '00'.repeat(32),
        sponsorKeyHash: opts.sponsorKeyHash ?? '00'.repeat(32),
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
 * when the transaction carries no signature and `verify_failed` when it does
 * not check). A second signature instruction in one cycle (SIGVERIFY,
 * ATTEST, ENDORSE, ATTESTM, ADMIT, REMOVE) is a fault (v3.1).
 */
export function step(
    s: K17State,
    env: StepEnv | bigint,
    witnessIndex = 0,
    bountyDue = 0n,
    sigUsed = false,
    payslot?: PaySlot,
    treeOp: TreeOp = 'none',
    member?: BoundMember,
    leafAfter?: string
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
        treeOp,
        member,
        leafAfter,
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
        treeOp,
        member,
        leafAfter,
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
    let nextTreeOp = treeOp
    let mb = member
    let nextLeafAfter = leafAfter
    let logHash = s.logHash
    let rosterRoot = s.rosterRoot
    let rosterSeq = s.rosterSeq

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
            // A second signature this cycle is the program's fault.
            if (su) return fault()
            const pub = e.roster?.[Number(operand)] ?? 0n
            if (pub === 0n) return fault()
            if (!e.sig) return unchanged('need_witness')
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
            // A second signature this cycle is the program's fault.
            if (su) return fault()
            const entry = readSlot(mem, Number(slot))
            if (entry.empty) return fault()
            if (
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
            // A second signature this cycle is the program's fault.
            if (su) return fault()
            const sponsor = readSlot(mem, Number(slot))
            if (sponsor.empty) return fault()
            if (newSlot >= BigInt(ROSTER_SLOTS)) return fault()
            if (!readSlot(mem, Number(newSlot)).empty) return fault()
            if (
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
        case Op.MEMBER: {
            // -- IDX   verify the cycle's Merkle proof against rosterRoot and
            // bind the proven leaf. A second MEMBER, or a member op after an
            // admin op, is the program's fault. A missing or invalid witness
            // (index out of range, malformed preimage, failed proof, empty
            // slot) is the transaction's fault: the VM mirrors the contract,
            // which treats those as an invalid transaction.
            if (treeOp !== 'none') return fault()
            if (!e.tree) return unchanged('need_witness')
            const { leafPre, proof, leafIndex } = e.tree
            if (leafIndex < 0n || leafIndex >= 65536n) {
                return unchanged('verify_failed')
            }
            if (!/^[0-9a-f]{120}$/.test(leafPre)) {
                return unchanged('verify_failed')
            }
            if (
                !SparseMerkleTree.verify(
                    s.rosterRoot,
                    leafPre,
                    proof,
                    leafIndex
                )
            ) {
                return unchanged('verify_failed')
            }
            // A full data stack faults after the proof was checked. The
            // contract has then already recorded the tree operation (and
            // checks the proof after its loop), so report 'member': the
            // keeper must still send the proof (v3.1 canonical arguments).
            if (dsDepth >= DS_MAX) return { ...fault(), treeOp: 'member' }
            const fields = decodeLeafPre(leafPre)
            nextTreeOp = 'member'
            mb = {
                keyHash: fields.keyHashHex,
                payoutHex: fields.payoutHex,
                lastRound: fields.lastRound,
                flags: fields.flags,
                leafIndex,
                leafPre,
                proof,
            }
            push(leafIndex)
            break
        }
        case Op.LASTROUND: {
            // -- R   push the bound member's lastRound; faults without MEMBER.
            if (!mb) return fault()
            if (dsDepth >= DS_MAX) return fault()
            push(mb.lastRound)
            break
        }
        case Op.ATTESTM: {
            // TAG VAL --   ATTEST under the key of the member MEMBER bound.
            // No member, or a second signature this cycle, is the program's
            // fault; a missing signature or key,
            // a key that does not hash to the member's leaf, or a bad
            // signature over memberMessage(instanceId, TAG, VAL) makes the
            // transaction invalid (state and stack unchanged). Success
            // consumes the cycle's one signature.
            if (dsDepth < 2) return fault()
            if (!mb) return fault()
            // A second signature this cycle is the program's fault.
            if (su) return fault()
            if (
                !e.sig ||
                e.attestKey === undefined ||
                e.instanceId === undefined
            ) {
                return unchanged('need_witness')
            }
            if (keyHash(e.attestKey) !== mb.keyHash) {
                return unchanged('verify_failed')
            }
            const value = pop()
            const tag = pop()
            if (
                !verifyMemberAttestation(
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
        case Op.PAYLEAF: {
            // N ROUND --   pay N sats to the bound member's payout address
            // and advance its leaf to lastRound := ROUND, updating
            // rosterRoot from the proof MEMBER verified. Program errors
            // (second payment, underflow, no member, N == 0) are faults, a
            // second payment dropping the first, as in PAYSLOT. A ROUND not
            // above the stored lastRound invalidates the transaction (state
            // and stack unchanged). Whether N is affordable is NOT checked
            // here: planCycle and the contract check it at payout
            // accounting, exactly as for PAYSLOT.
            if (ps) return { ...fault(), payslot: undefined }
            if (dsDepth < 2) return fault()
            if (!mb) return fault()
            const round = pop()
            const sats = pop()
            if (sats === 0n) return fault()
            if (round <= mb.lastRound) return unchanged('verify_failed')
            ps = { slot: -1, payoutHex: mb.payoutHex, sats }
            nextLeafAfter = encodeLeafPre(
                mb.keyHash,
                mb.payoutHex,
                round,
                mb.flags
            )
            rosterRoot = SparseMerkleTree.rootAfter(
                nextLeafAfter,
                mb.proof,
                mb.leafIndex
            )
            mb = { ...mb, lastRound: round }
            break
        }
        case Op.ADMIT: {
            // TAG ROUND --   the sponsor admits e.endorseKey into the empty
            // leaf the cycle's proof names, with lastRound := ROUND. A member
            // or admin op already this cycle, a short stack, or a second
            // signature this cycle, is the program's fault. Missing witnesses are need_witness; every
            // other failure (index range, occupied leaf, proof not against
            // rosterRoot, malformed payout, signer not the sponsor, bad
            // signature over admitMessage with the current rosterSeq) makes
            // the transaction invalid with state unchanged. A sponsorKeyHash
            // of all zeros (no sponsor) can never match keyHash(attestKey),
            // so ADMIT then always fails verification. TAG is peeked, and
            // ROUND and TAG are popped only on the way to success.
            if (dsDepth < 2) return fault()
            if (treeOp !== 'none') return fault()
            // A second signature this cycle is the program's fault.
            if (su) return fault()
            if (
                !e.tree ||
                !e.sig ||
                e.attestKey === undefined ||
                e.endorseKey === undefined ||
                e.payout === undefined ||
                e.instanceId === undefined
            ) {
                return unchanged('need_witness')
            }
            const { leafPre, proof, leafIndex } = e.tree
            if (leafIndex < 0n || leafIndex >= 65536n) {
                return unchanged('verify_failed')
            }
            if (leafPre !== '') return unchanged('verify_failed')
            if (!SparseMerkleTree.verify(s.rosterRoot, '', proof, leafIndex)) {
                return unchanged('verify_failed')
            }
            if (!/^[0-9a-f]{40}$/.test(e.payout)) {
                return unchanged('verify_failed')
            }
            if (keyHash(e.attestKey) !== s.sponsorKeyHash) {
                return unchanged('verify_failed')
            }
            const admitTag = cellAt(ds, dsDepth - 2)
            if (
                !verifyAdmission(
                    e.instanceId,
                    admitTag,
                    s.rosterSeq,
                    leafIndex,
                    e.endorseKey,
                    e.payout,
                    e.sig,
                    e.attestKey
                )
            ) {
                return unchanged('verify_failed')
            }
            const admitRound = pop()
            pop()
            nextLeafAfter = encodeLeafPre(
                keyHash(e.endorseKey),
                e.payout,
                admitRound,
                0n
            )
            rosterRoot = SparseMerkleTree.rootAfter(
                nextLeafAfter,
                proof,
                leafIndex
            )
            rosterSeq = s.rosterSeq + 1n
            su = true
            nextTreeOp = 'admit'
            break
        }
        case Op.REMOVE: {
            // TAG --   the sponsor removes the member at the leaf the
            // cycle's proof names. Same fault / need_witness / verify_failed
            // split as ADMIT, except the leaf must be occupied (120 lowercase
            // hex; an empty leaf cannot be removed) and the signature covers
            // removeMessage with the member's key hash and payout (the
            // first 52 bytes of the leaf, which PAYLEAF never changes, so
            // a removal signed before a payment still verifies after it;
            // rosterSeq stops a replay). A sponsorKeyHash of all
            // zeros means no sponsor, so REMOVE then never verifies. TAG is
            // peeked and popped only on success.
            if (dsDepth < 1) return fault()
            if (treeOp !== 'none') return fault()
            // A second signature this cycle is the program's fault.
            if (su) return fault()
            if (
                !e.tree ||
                !e.sig ||
                e.attestKey === undefined ||
                e.instanceId === undefined
            ) {
                return unchanged('need_witness')
            }
            const { leafPre, proof, leafIndex } = e.tree
            if (leafIndex < 0n || leafIndex >= 65536n) {
                return unchanged('verify_failed')
            }
            if (!/^[0-9a-f]{120}$/.test(leafPre)) {
                return unchanged('verify_failed')
            }
            if (
                !SparseMerkleTree.verify(
                    s.rosterRoot,
                    leafPre,
                    proof,
                    leafIndex
                )
            ) {
                return unchanged('verify_failed')
            }
            if (keyHash(e.attestKey) !== s.sponsorKeyHash) {
                return unchanged('verify_failed')
            }
            const removeTag = cellAt(ds, dsDepth - 1)
            // leafPre is 120 lowercase hex (checked above), so decoding
            // cannot throw and both fields pass removeMessage's checks.
            const removed = decodeLeafPre(leafPre)
            if (
                !verifyRemoval(
                    e.instanceId,
                    removeTag,
                    s.rosterSeq,
                    leafIndex,
                    removed.keyHashHex,
                    removed.payoutHex,
                    e.sig,
                    e.attestKey
                )
            ) {
                return unchanged('verify_failed')
            }
            pop()
            nextLeafAfter = ''
            rosterRoot = SparseMerkleTree.rootAfter('', proof, leafIndex)
            rosterSeq = s.rosterSeq + 1n
            su = true
            nextTreeOp = 'remove'
            break
        }
        case Op.OUTH: {
            // N1 --   logHash := sha256(logHash || cell(N1)). The output log
            // `out` is untouched, so OUT_MAX does not apply.
            if (dsDepth < 1) return fault()
            const n1 = pop()
            logHash = createHash('sha256')
                .update(Buffer.from(s.logHash + encodeCell(n1), 'hex'))
                .digest('hex')
            break
        }
        default:
            return fault()
    }

    return {
        state: {
            ...s,
            pc: nextPc,
            ds,
            rs,
            mem,
            out,
            halted,
            logHash,
            rosterRoot,
            rosterSeq,
        },
        status: halted ? 'halted' : yielded ? 'yield' : 'ok',
        faulted: false,
        witnessIndex: wi,
        bountyDue: bounty,
        sigUsed: su,
        payslot: ps,
        treeOp: nextTreeOp,
        member: mb,
        leafAfter: nextLeafAfter,
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
    /** The tree operation this cycle performed. */
    treeOp: TreeOp
    /** The member MEMBER bound this cycle; undefined when none. */
    member?: BoundMember
    /**
     * The leaf preimage hex this cycle wrote to the roster: the new 120-hex
     * leaf after PAYLEAF or ADMIT, '' (an empty leaf) after REMOVE, and
     * undefined when no leaf was written (including MEMBER alone). It
     * matches `state.rosterRoot`, so a mirror of the tree can apply it at
     * the cycle's leaf index. A fault after the write keeps it, as the
     * state at a fault keeps the new root.
     */
    leafAfter?: string
    /**
     * The opcode of the instruction that used the cycle's one signature
     * (SIGVERIFY, ATTEST, ENDORSE, ATTESTM, ADMIT or REMOVE); undefined when
     * no signature was used. planCycle reads it to send only the unlocking
     * arguments that instruction reads (v3.1 canonical arguments).
     */
    sigOp?: Op
    /**
     * The Rabin public key the signature was verified under: the roster
     * key named by SIGVERIFY's operand, else env.attestKey. Undefined when
     * sigOp is undefined. planCycle uses it to put the signature in its
     * canonical form.
     */
    sigKey?: RabinPubKey
}

/**
 * Execute up to `k` instructions, stopping early once halted or blocked.
 * This mirrors one on-chain cycle transaction with K unrolled steps.
 * When `env` carries `deadMan` and `lastTime` and the dead-man is due
 * (deadManDue), no instruction runs: the outcome is 'halted' with
 * `state.halted` set, as on chain (v3.1). The MIN_STEP clock rule is a
 * transaction rule, not a VM rule; planCycle enforces it.
 */
export function stepK(
    s: K17State,
    env: StepEnv | bigint,
    k: number
): CycleOutcome {
    const e: StepEnv = typeof env === 'bigint' ? envOf(env) : env
    // Dead-man halt (v3.1): the cycle halts before its first instruction.
    if (deadManDue(e)) {
        return {
            state: { ...s, halted: true },
            status: 'halted',
            witnessUsed: 0,
            bountyDue: 0n,
            treeOp: 'none',
        }
    }
    let cur = s
    let wi = 0
    let bounty = 0n
    let su = false
    let ps: PaySlot | undefined
    let treeOp: TreeOp = 'none'
    let member: BoundMember | undefined
    let leafAfter: string | undefined
    let sigOp: Op | undefined
    let sigKey: RabinPubKey | undefined
    let status: Status = cur.halted ? 'halted' : 'ok'
    for (let i = 0; i < k && status === 'ok'; i++) {
        const r = step(cur, e, wi, bounty, su, ps, treeOp, member, leafAfter)
        if (r.status === 'need_witness' || r.status === 'verify_failed') {
            return {
                state: cur,
                status: r.status,
                witnessUsed: wi,
                bountyDue: bounty,
                payslot: ps,
                treeOp,
                member,
                leafAfter,
                sigOp,
                sigKey,
            }
        }
        if (r.sigUsed && !su) {
            // This instruction used the signature: record which one, and
            // the key it was verified under.
            const prog = Buffer.from(cur.prog, 'hex')
            const pc = Number(cur.pc)
            sigOp = prog[pc] as Op
            sigKey =
                sigOp === Op.SIGVERIFY
                    ? e.roster?.[prog.readUInt32LE(pc + 1)]
                    : e.attestKey
        }
        cur = r.state
        wi = r.witnessIndex
        bounty = r.bountyDue
        su = r.sigUsed
        ps = r.payslot
        treeOp = r.treeOp
        member = r.member
        leafAfter = r.leafAfter
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
        treeOp,
        member,
        leafAfter,
        sigOp,
        sigKey,
    }
}

/**
 * Run until HALT/fault/block or until `maxSteps` instructions have executed.
 * A due dead-man (deadManDue) halts before the first instruction (v3.1).
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
    treeOp: TreeOp
    member?: BoundMember
    /** The leaf preimage hex the run wrote to the roster (see StepResult.leafAfter). */
    leafAfter?: string
} {
    const e: StepEnv = typeof env === 'bigint' ? envOf(env) : env
    // Dead-man halt (v3.1): nothing executes. `run` uses one environment
    // for every step, so this is checked once, before the first one.
    if (deadManDue(e)) {
        return {
            state: { ...s, halted: true },
            steps: 0,
            status: 'halted',
            bountyDue: 0n,
            treeOp: 'none',
        }
    }
    let cur = s
    let steps = 0
    let wi = 0
    let bounty = 0n
    let su = false
    let ps: PaySlot | undefined
    let treeOp: TreeOp = 'none'
    let member: BoundMember | undefined
    let leafAfter: string | undefined
    let status: Status = cur.halted ? 'halted' : 'ok'
    while (status === 'ok' && steps < maxSteps) {
        const r = step(cur, e, wi, bounty, su, ps, treeOp, member, leafAfter)
        if (r.status === 'need_witness' || r.status === 'verify_failed') {
            return {
                state: cur,
                steps,
                status: r.status,
                bountyDue: bounty,
                payslot: ps,
                treeOp,
                member,
                leafAfter,
            }
        }
        cur = r.state
        wi = r.witnessIndex
        bounty = r.bountyDue
        su = r.sigUsed
        ps = r.payslot
        treeOp = r.treeOp
        member = r.member
        leafAfter = r.leafAfter
        status =
            r.status === 'fault'
                ? 'halted'
                : r.status === 'yield'
                ? 'ok'
                : r.status
        steps++
    }
    return {
        state: cur,
        steps,
        status,
        bountyDue: bounty,
        payslot: ps,
        treeOp,
        member,
        leafAfter,
    }
}

/** Decode the output log into a list of cell values. */
export function outputLog(s: K17State): bigint[] {
    const cells: bigint[] = []
    for (let i = 0; i < depth(s.out); i++) cells.push(cellAt(s.out, i))
    return cells
}
