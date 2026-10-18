/**
 * K17 instruction set architecture.
 *
 * This module defines the bytecode that both the off-chain reference VM
 * (`vm.ts`) and the on-chain sCrypt interpreter (`contracts/k17Machine.ts`)
 * execute. The two implementations MUST agree byte-for-byte on state
 * encoding, which is why every constant lives here and nowhere else.
 *
 * The ISA is Koopman's Canonical Stack Machine (Stack Computers: The New
 * Wave, 1989, Table 3.1), 17 instructions, plus HALT, 0=, OUT, TIME and the
 * job-bounty extension: IN, VERIFY, BOUNTY, *, HASH, WHO, YIELD.
 *
 * YIELD ends the current cycle early. A job stage written as
 * `YIELD IN ... VERIFY ... BOUNTY n YIELD` therefore executes atomically in
 * one transaction: whoever supplies the witnesses is the one who collects.
 *
 * Two outcomes are NOT faults: IN with no witness left, and VERIFY of zero.
 * Those make the spending transaction invalid instead, so a program that is
 * waiting for an answer cannot be killed by a keeper who has none, and a
 * wrong answer is simply rejected.
 *
 * Encoding
 *   - Program: a byte string. Each instruction is one opcode byte. LIT, IF,
 *     CALL and BOUNTY are followed by a 4-byte little-endian unsigned operand.
 *   - Cell: unsigned 32-bit integer, 4 bytes little-endian. All arithmetic
 *     wraps modulo 2^32.
 *   - Stacks: byte strings of cells, top of stack at the END (highest
 *     offset), so push = append, pop = truncate.
 *   - Memory: MEM_CELLS cells, byte string, addressed by cell index.
 *   - Output log: byte string of cells, append-only, capped at OUT_MAX cells.
 *   - Program counter: byte offset into the program.
 *
 * Any violation (stack underflow/overflow, bad address, unknown opcode, PC
 * past the end, output log full) is a FAULT. A fault is treated exactly as
 * HALT: the machine stops and the contract releases its funds to the
 * beneficiary. Faults never make the spending transaction invalid, because
 * an unspendable program would freeze its funds forever.
 */

/** Width of one data cell in bytes. */
export const CELL = 4
/** Modulus for cell arithmetic (2^32). */
export const CELL_MOD = 0x1_0000_0000n
/** Maximum data-stack depth in cells (Koopman §6.4.1: 32 is enough). */
export const DS_MAX = 32
/** Maximum return-stack depth in cells. */
export const RS_MAX = 32
/** Number of memory cells. */
export const MEM_CELLS = 64
/** Maximum number of cells in the output log. */
export const OUT_MAX = 64

/** Opcode byte values. Mnemonics follow Koopman's Forth notation. */
export enum Op {
    HALT = 0x00,
    STORE = 0x01, //  !      N1 ADDR --        mem[ADDR] = N1
    ADD = 0x02, //    +      N1 N2 -- N3       N3 = N1 + N2
    SUB = 0x03, //    -      N1 N2 -- N3       N3 = N1 - N2
    TO_R = 0x04, //   >R     N1 --             push N1 on return stack
    FETCH = 0x05, //  @      ADDR -- N1        N1 = mem[ADDR]
    AND = 0x06, //    AND    N1 N2 -- N3
    DROP = 0x07, //   DROP   N1 --
    DUP = 0x08, //    DUP    N1 -- N1 N1
    OR = 0x09, //     OR     N1 N2 -- N3
    OVER = 0x0a, //   OVER   N1 N2 -- N1 N2 N1
    R_FROM = 0x0b, // R>     -- N1             pop return stack to data stack
    SWAP = 0x0c, //   SWAP   N1 N2 -- N2 N1
    XOR = 0x0d, //    XOR    N1 N2 -- N3
    IF = 0x0e, //     [IF]   N1 --             if N1 == 0 then PC = operand
    CALL = 0x0f, //   [CALL] --                push PC_after on RS; PC = operand
    EXIT = 0x10, //   [EXIT] --                PC = pop RS
    LIT = 0x11, //    [LIT]  -- N1             push operand
    ZEQ = 0x12, //    0=     N1 -- FLAG        FLAG = (N1 == 0) ? 1 : 0
    OUT = 0x13, //    OUT    N1 --             append N1 to output log
    TIME = 0x14, //   TIME   -- T              push the transaction nLockTime
    IN = 0x15, //     IN     -- W              push next witness cell; tx invalid if none
    VERIFY = 0x16, // VERIFY N1 --             tx invalid if N1 == 0 (not a fault)
    BOUNTY = 0x17, // BOUNTY --                authorise operand sats extra to the spender
    MUL = 0x18, //    *      N1 N2 -- N3       N3 = N1 * N2
    HASH = 0x19, //   HASH   N1 -- H           H = first 4 bytes of sha256(cell(N1))
    WHO = 0x1a, //    WHO    -- A              A = first 4 bytes of the spender's address
    YIELD = 0x1b, //  YIELD  --                end this cycle now; next tx resumes after it
}

/** Opcodes that carry a 4-byte operand. */
export const HAS_OPERAND: ReadonlySet<Op> = new Set([
    Op.IF,
    Op.CALL,
    Op.LIT,
    Op.BOUNTY,
])

/** Mnemonic table used by the assembler and the disassembler. */
export const MNEMONIC: Record<string, Op> = {
    HALT: Op.HALT,
    '!': Op.STORE,
    '+': Op.ADD,
    '-': Op.SUB,
    '>R': Op.TO_R,
    '@': Op.FETCH,
    AND: Op.AND,
    DROP: Op.DROP,
    DUP: Op.DUP,
    OR: Op.OR,
    OVER: Op.OVER,
    'R>': Op.R_FROM,
    SWAP: Op.SWAP,
    XOR: Op.XOR,
    IF: Op.IF,
    CALL: Op.CALL,
    EXIT: Op.EXIT,
    LIT: Op.LIT,
    '0=': Op.ZEQ,
    OUT: Op.OUT,
    TIME: Op.TIME,
    IN: Op.IN,
    VERIFY: Op.VERIFY,
    BOUNTY: Op.BOUNTY,
    '*': Op.MUL,
    HASH: Op.HASH,
    WHO: Op.WHO,
    YIELD: Op.YIELD,
}

/**
 * Encode an unsigned 32-bit value as a 4-byte little-endian hex cell.
 * Input: value in [0, 2^32). Output: 8 hex characters.
 */
export function encodeCell(value: bigint): string {
    if (value < 0n || value >= CELL_MOD) {
        throw new Error(`cell out of range: ${value}`)
    }
    const b = Buffer.alloc(CELL)
    b.writeUInt32LE(Number(value))
    return b.toString('hex')
}

/**
 * Decode a 4-byte little-endian hex cell to an unsigned bigint.
 * Input: 8 hex characters. Output: value in [0, 2^32).
 */
export function decodeCell(hex: string): bigint {
    if (hex.length !== CELL * 2) throw new Error(`bad cell: ${hex}`)
    return BigInt(Buffer.from(hex, 'hex').readUInt32LE())
}

/**
 * Assemble a program from a list of tokens.
 *
 * Tokens are mnemonics (see MNEMONIC), decimal numbers (operands), or
 * labels. A label is defined with a trailing colon (`loop:`) and referenced
 * by bare name as the operand of IF or CALL. Operands may also be numbers.
 *
 * Input: array of tokens, e.g. ['LIT', 5, 'loop:', 'DUP', 'OUT', 'LIT', 1,
 *        '-', 'DUP', 'IF', 'end', 'LIT', 0, 'IF', 'loop', 'end:', 'HALT'].
 * Output: program bytes as a hex string.
 */
export function assemble(tokens: (string | number)[]): string {
    // Pass 1: compute byte offsets of labels.
    const labels = new Map<string, number>()
    let offset = 0
    let i = 0
    while (i < tokens.length) {
        const t = tokens[i]
        if (typeof t === 'string' && t.endsWith(':')) {
            labels.set(t.slice(0, -1), offset)
            i++
            continue
        }
        const op = lookupOp(t)
        offset += 1
        i++
        if (HAS_OPERAND.has(op)) {
            if (i >= tokens.length) throw new Error(`missing operand for ${t}`)
            offset += CELL
            i++
        }
    }
    // Pass 2: emit bytes.
    const out: string[] = []
    i = 0
    while (i < tokens.length) {
        const t = tokens[i]
        if (typeof t === 'string' && t.endsWith(':')) {
            i++
            continue
        }
        const op = lookupOp(t)
        out.push(op.toString(16).padStart(2, '0'))
        i++
        if (HAS_OPERAND.has(op)) {
            const operand = tokens[i++]
            let value: bigint
            if (typeof operand === 'number') {
                value = BigInt(operand)
            } else if (labels.has(operand)) {
                value = BigInt(labels.get(operand) as number)
            } else if (/^-?\d+$/.test(operand)) {
                value = BigInt(operand)
            } else {
                throw new Error(`unknown label or operand: ${operand}`)
            }
            if (value < 0n) value += CELL_MOD
            out.push(encodeCell(value))
        }
    }
    return out.join('')
}

/** Resolve a mnemonic token to its opcode or throw. */
function lookupOp(t: string | number): Op {
    if (typeof t !== 'string' || !(t in MNEMONIC)) {
        throw new Error(`unknown mnemonic: ${t}`)
    }
    return MNEMONIC[t]
}

/**
 * Disassemble program bytes for debugging.
 * Input: program hex. Output: one line per instruction, `offset: MNEMONIC [operand]`.
 */
export function disassemble(progHex: string): string {
    const names = Object.fromEntries(
        Object.entries(MNEMONIC).map(([m, o]) => [o, m])
    )
    const lines: string[] = []
    let pc = 0
    const bytes = Buffer.from(progHex, 'hex')
    while (pc < bytes.length) {
        const op = bytes[pc] as Op
        const name = names[op] ?? `??${op.toString(16)}`
        if (HAS_OPERAND.has(op)) {
            const operand = bytes.readUInt32LE(pc + 1)
            lines.push(`${pc}: ${name} ${operand}`)
            pc += 1 + CELL
        } else {
            lines.push(`${pc}: ${name}`)
            pc += 1
        }
    }
    return lines.join('\n')
}
