/**
 * K17 reference virtual machine (off-chain).
 *
 * This is the executable specification of the K17 machine. Keepers use it to
 * compute the next state before building a spending transaction, and the
 * tests use it to cross-check the on-chain sCrypt interpreter. Its semantics
 * must match `contracts/k17Machine.ts` exactly; the differential test in
 * `tests/k17Machine.test.ts` enforces that.
 *
 * All state fields are hex strings or bigints so they can be passed straight
 * into sCrypt contract properties.
 */

import {
    CELL,
    CELL_MOD,
    DS_MAX,
    HAS_OPERAND,
    MEM_CELLS,
    OUT_MAX,
    Op,
    RS_MAX,
    decodeCell,
    encodeCell,
} from './isa'

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

/** Build the initial state for a program: empty stacks, zeroed memory. */
export function initialState(progHex: string): K17State {
    return {
        prog: progHex,
        pc: 0n,
        ds: '',
        rs: '',
        mem: '00'.repeat(MEM_CELLS * CELL),
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

/** Result of executing one instruction. */
export type StepResult = { state: K17State; faulted: boolean }

/**
 * Execute exactly one instruction.
 *
 * Input: current state and the nLockTime of the transaction performing the
 * cycle (consumed by TIME). Output: the new state. A fault sets `halted` and
 * is reported in `faulted`; it is never thrown.
 */
export function step(s: K17State, lockTime: bigint): StepResult {
    if (s.halted) return { state: s, faulted: false }

    const prog = Buffer.from(s.prog, 'hex')
    const pc = Number(s.pc)
    const fault = (): StepResult => ({
        state: { ...s, halted: true },
        faulted: true,
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
            if (addr >= BigInt(MEM_CELLS)) return fault()
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
            push(lockTime % CELL_MOD)
            break
        }
        default:
            return fault()
    }

    return {
        state: { ...s, pc: nextPc, ds, rs, mem, out, halted },
        faulted: false,
    }
}

/**
 * Execute up to `k` instructions, stopping early once halted.
 * This mirrors one on-chain cycle transaction with K unrolled steps.
 * Input: state, nLockTime, k. Output: new state.
 */
export function stepK(s: K17State, lockTime: bigint, k: number): K17State {
    let cur = s
    for (let i = 0; i < k && !cur.halted; i++) {
        cur = step(cur, lockTime).state
    }
    return cur
}

/**
 * Run until HALT/fault or until `maxSteps` instructions have executed.
 * Input: state, nLockTime, maxSteps. Output: final state and step count.
 */
export function run(
    s: K17State,
    lockTime: bigint,
    maxSteps = 100_000
): { state: K17State; steps: number } {
    let cur = s
    let steps = 0
    while (!cur.halted && steps < maxSteps) {
        cur = step(cur, lockTime).state
        steps++
    }
    return { state: cur, steps }
}

/** Decode the output log into a list of cell values. */
export function outputLog(s: K17State): bigint[] {
    const cells: bigint[] = []
    for (let i = 0; i < depth(s.out); i++) cells.push(cellAt(s.out, i))
    return cells
}
