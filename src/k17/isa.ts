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
 * K17+ adds the DC4CD-port extension: MIN and MAX (fuzzy AND/OR over truth
 * values), unsigned division (/), and SIGVERIFY k, which accepts a cycle
 * only if the Rabin signature carried in the unlocking script, under roster
 * key k, signs the two cells on top of the stack. This is how an off-chain
 * sensor node attests a reading: the keeper who relays the reading need not be the node that
 * measured it. One signature per cycle; a second signature instruction in
 * the same cycle (SIGVERIFY, ATTEST, ENDORSE, ATTESTM, ADMIT or REMOVE) is
 * a fault (v3.1; it made the transaction invalid before, which let a
 * program freeze its own funds).
 *
 * Three outcomes are NOT faults: IN with no witness left, VERIFY of zero,
 * and SIGVERIFY with a missing or wrong signature. Those make the spending
 * transaction invalid instead, so a program that is waiting for an answer
 * cannot be killed by a keeper who has none (until the dead-man interval
 * passes, when deadMan > 0), and a wrong answer is simply rejected.
 *
 * Encoding
 *   - Program: a byte string. Each instruction is one opcode byte. LIT, IF,
 *     CALL, BOUNTY and SIGVERIFY are followed by a 4-byte little-endian
 *     unsigned operand.
 *   - Cell: unsigned 32-bit integer, 4 bytes little-endian. All arithmetic
 *     wraps modulo 2^32.
 *   - Stacks: byte strings of cells, top of stack at the END (highest
 *     offset), so push = append, pop = truncate.
 *   - Memory: MEM_CELLS cells, byte string, addressed by cell index.
 *   - Output log: byte string of cells, append-only, capped at OUT_MAX cells.
 *   - Program counter: byte offset into the program.
 *
 * Roster (v2 machine). The top of memory holds ROSTER_SLOTS roster slots of
 * SLOT_CELLS cells each, starting at cell ROSTER_BASE (slot k starts at
 * ROSTER_BASE + k * SLOT_CELLS). A slot is the 32-byte key hash as 8
 * little-endian cells followed by the 20-byte payout hash as 5 cells.
 * ROSTER_BASE + ROSTER_SLOTS * SLOT_CELLS == MEM_CELLS, so the roster
 * occupies cells 152..255 and programs use cells 0..151.
 *
 * Roster instructions. The transaction supplies keyA, keyB, payout and one
 * Rabin signature; I is the machine's 32-byte instance id.
 *   ATTEST  (0x20)  TAG VAL SLOT --
 *       keyA must hash to slot SLOT's key hash and sign
 *       "K17M" || I || cell(TAG) || cell(VAL).
 *       Fault: underflow, SLOT >= ROSTER_SLOTS, a second signature in the
 *       cycle, empty slot.
 *       Invalid tx: no witness, a hash or signature mismatch.
 *   ENDORSE (0x21)  TAG SLOT NEWSLOT --
 *       keyA must hash to slot SLOT's key hash and sign
 *       "K17E" || I || cell(TAG) || cell(NEWSLOT) || sha256(keyB) || payout;
 *       then sha256(keyB) || payout is written into slot NEWSLOT.
 *       Fault: underflow, SLOT >= ROSTER_SLOTS, a second signature in the
 *       cycle, empty SLOT, NEWSLOT >= ROSTER_SLOTS, filled NEWSLOT.
 *       Invalid tx: no witness, a payout
 *       that is not 20 bytes (40 lowercase hex chars in the VM), a hash or
 *       signature mismatch.
 *   PAYSLOT (0x22)  N SLOT --
 *       Pays N sats to slot SLOT's payout address. The payout has priority
 *       over the keeper's reward, which shrinks to make room.
 *       Fault (payout dropped): a second PAYSLOT in the cycle (checked
 *       first), underflow, SLOT >= ROSTER_SLOTS, empty slot, N == 0, and
 *       (at payout accounting, in planCycle and the contract) N greater
 *       than the balance less one satoshi. Never an invalid tx.
 *   VALUE   (0x23)  -- V
 *       Pushes the value of the spent output (mod 2^32).
 * None of the four carries an operand.
 *
 * v3 machine: Merkle roster. The roster is a sparse Merkle tree (smt.ts)
 * whose root lives in the machine state; each cycle carries one Merkle
 * proof. None of these seven carries an operand.
 *   MEMBER    (0x24)  -- IDX
 *       Verifies the cycle's proof against rosterRoot and binds that
 *       member for the cycle; pushes the leaf index.
 *   LASTROUND (0x25)  -- R
 *       Pushes the bound member's lastRound.
 *   ATTESTM   (0x26)  TAG VAL --
 *       ATTEST under the bound member's key; message domain "K17T".
 *   PAYLEAF   (0x27)  N ROUND --
 *       Pays N sats to the bound member and sets lastRound := ROUND; the
 *       root is recomputed.
 *   ADMIT     (0x28)  TAG ROUND --
 *       Sponsor-signed insertion of a new member; message domain "K17D".
 *   REMOVE    (0x29)  TAG --
 *       Sponsor-signed deletion of a member; message domain "K17X".
 *       The message binds the member's keyHash and payout (leafPre bytes
 *       0..52), not the leaf hash, so a PAYLEAF does not invalidate it.
 *   OUTH      (0x2a)  N1 --
 *       logHash := sha256(logHash || cell(N1)). Never faults on capacity.
 * Programs must derive ROUND (for PAYLEAF and ADMIT) from TIME, never from
 * IN: a keeper controls IN, but nLockTime never decreases.
 *
 * Any violation (stack underflow/overflow, bad address, unknown opcode, PC
 * past the end, output log full, a second signature instruction in the
 * cycle) is a FAULT. A fault is treated exactly as
 * HALT: the machine stops and the contract releases its funds to the
 * beneficiary. Faults never make the spending transaction invalid, because
 * an unspendable program would freeze its funds forever.
 *
 * Canonical unlocking script (v3.1, a transaction rule, not a VM rule).
 * The transaction is also invalid when an unlocking argument the cycle did
 * not use is not empty (or 0): the witness must hold exactly the cells IN
 * consumed; leafPre, proof and leafIndex must be empty and 0 unless a tree
 * instruction ran; sigS, sigPad and keyA must be 0 and empty unless a
 * signature instruction ran, and keyA also for SIGVERIFY; keyB and payout
 * must be empty unless ENDORSE or ADMIT ran. A used Rabin signature must
 * have 0 < s < n/2. This stops a relayer from changing a cycle's txid.
 *
 * Dead-man halt (v3.1, not an instruction). A machine deployed with
 * deadMan > 0 halts before its first instruction in any cycle whose
 * nLockTime is at least lastTime + deadMan, exactly like a fault: refund to
 * the beneficiary, keeper reward paid, no witness needed. This frees a
 * program that waits for a witness nobody supplies. A cycle that keeps the
 * machine alive must advance nLockTime by at least 60 s (MIN_STEP, a
 * transaction rule enforced by the contract and planCycle, not by the VM).
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
export const MEM_CELLS = 256
/** Maximum number of cells in the output log. */
export const OUT_MAX = 256

/** Opcode byte values. Mnemonics follow Koopman's Forth notation. */
export enum Op {
    HALT = 0x00,
    STORE = 0x01, //  !      N1 ADDR --        mem[ADDR] = N1; faults if ADDR >= ROSTER_BASE
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
    // ---- K17+ (DC4CD port): attested inputs and fuzzy operators ----
    MIN = 0x1c, //    MIN    N1 N2 -- N3       N3 = min(N1, N2)   (fuzzy AND)
    MAX = 0x1d, //    MAX    N1 N2 -- N3       N3 = max(N1, N2)   (fuzzy OR)
    SIGVERIFY = 0x1e, // SIGVERIFY k  TAG VAL --  tx invalid unless the cycle's Rabin
    //                  signature, under roster key k, signs cell(TAG)||cell(VAL)
    DIV = 0x1f, //    /      N1 N2 -- N3       N3 = floor(N1 / N2); fault if N2 == 0
    // ---- v2 machine: roster attestation, endorsement and payout ----
    ATTEST = 0x20, //  ATTEST  verify an attested reading (no operand)
    ENDORSE = 0x21, // ENDORSE verify a roster endorsement (no operand)
    PAYSLOT = 0x22, // PAYSLOT pay a roster slot's payout (no operand)
    VALUE = 0x23, //   VALUE  -- V   push the value of the spent output
    // ---- v3 machine: Merkle roster (no operands) ----
    MEMBER = 0x24, //    MEMBER    -- IDX      verify the cycle's proof, bind the member
    LASTROUND = 0x25, // LASTROUND -- R        push the bound member's lastRound
    ATTESTM = 0x26, //   ATTESTM   TAG VAL --  ATTEST under the bound member's key
    PAYLEAF = 0x27, //   PAYLEAF   N ROUND --  pay the member, set lastRound := ROUND
    ADMIT = 0x28, //     ADMIT     TAG ROUND -- sponsor-signed insertion
    REMOVE = 0x29, //    REMOVE    TAG --      sponsor-signed deletion
    OUTH = 0x2a, //      OUTH      N1 --       logHash := sha256(logHash || cell(N1))
}

/**
 * Number of roster slots in the contract. A program may reference roster
 * indices 0..ROSTER_MAX-1 as the operand of SIGVERIFY; a higher index, or a
 * slot holding the zero key, is a fault.
 */
export const ROSTER_MAX = 4

/** Number of roster slots held at the top of memory. */
export const ROSTER_SLOTS = 8
/** Cells per roster slot: 8 for the 32-byte key hash, 5 for the 20-byte payout. */
export const SLOT_CELLS = 13
/** Cell index of roster slot 0; slot k starts at ROSTER_BASE + k * SLOT_CELLS. */
export const ROSTER_BASE = 152

/**
 * Domain prefix of every endorsement message, ASCII "K17E". Separates
 * endorsement signatures from attestations (ATTEST_DOMAIN).
 */
export const ENDORSE_DOMAIN = '4b313745'

/**
 * Domain prefix of every attestation message, ASCII "K17A". It stops a
 * roster key that also signs other things (oracle feeds, other protocols)
 * from having those signatures replayed as K17 attestations.
 */
export const ATTEST_DOMAIN = '4b313741'

/**
 * Message bytes that an attester signs for `TAG VAL SIGVERIFY k`:
 * ATTEST_DOMAIN || cell(TAG) || cell(VAL), 12 bytes, as hex. The message is
 * fixed-length, so the signature padding that follows it cannot move a field
 * boundary. Programs push TAG as a literal that includes a per-deployment
 * epoch (so a signature cannot be replayed into another instance with the
 * same roster) plus the hop or sample index; VAL is the attested reading.
 */
export function attestMessage(tag: bigint, value: bigint): string {
    return ATTEST_DOMAIN + encodeCell(tag) + encodeCell(value)
}

/** Opcodes that carry a 4-byte operand. */
export const HAS_OPERAND: ReadonlySet<Op> = new Set([
    Op.IF,
    Op.CALL,
    Op.LIT,
    Op.BOUNTY,
    Op.SIGVERIFY,
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
    MIN: Op.MIN,
    MAX: Op.MAX,
    SIGVERIFY: Op.SIGVERIFY,
    '/': Op.DIV,
    ATTEST: Op.ATTEST,
    ENDORSE: Op.ENDORSE,
    PAYSLOT: Op.PAYSLOT,
    VALUE: Op.VALUE,
    MEMBER: Op.MEMBER,
    LASTROUND: Op.LASTROUND,
    ATTESTM: Op.ATTESTM,
    PAYLEAF: Op.PAYLEAF,
    ADMIT: Op.ADMIT,
    REMOVE: Op.REMOVE,
    OUTH: Op.OUTH,
}

/**
 * Cell index of the first cell of a roster slot.
 * Input: slot number (0..ROSTER_SLOTS-1). Output: ROSTER_BASE + slot * SLOT_CELLS.
 */
export function slotOffset(slot: number): number {
    if (!Number.isInteger(slot) || slot < 0 || slot >= ROSTER_SLOTS) {
        throw new Error(`roster slot out of range: ${slot}`)
    }
    return ROSTER_BASE + slot * SLOT_CELLS
}

/**
 * Memory cells that describe one roster slot.
 * Input: keyHashHex (32 bytes, 64 hex chars), payoutHex (20 bytes, 40 hex chars).
 * Output: SLOT_CELLS bigints; the key hash as 8 little-endian 4-byte cells
 * followed by the payout as 5 little-endian 4-byte cells.
 */
export function slotCells(keyHashHex: string, payoutHex: string): bigint[] {
    if (!/^([0-9a-fA-F]{2}){32}$/.test(keyHashHex)) {
        throw new Error(`bad key hash: ${keyHashHex}`)
    }
    if (!/^([0-9a-fA-F]{2}){20}$/.test(payoutHex)) {
        throw new Error(`bad payout: ${payoutHex}`)
    }
    const bytes = Buffer.from(keyHashHex + payoutHex, 'hex')
    const cells: bigint[] = []
    for (let i = 0; i < bytes.length; i += CELL) {
        cells.push(BigInt(bytes.readUInt32LE(i)))
    }
    return cells
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
