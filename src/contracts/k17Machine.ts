/**
 * K17Machine: a UTXO-chained Koopman canonical stack machine on Bitcoin SV.
 *
 * One UTXO locked by this contract is one suspended K17 process. Anyone may
 * spend it. The spend is valid only if:
 *   1. output 0 carries this same contract with the state advanced by exactly
 *      K instructions (or a P2PKH to the beneficiary if the machine halted
 *      or faulted during those K instructions), and
 *   2. output 1 pays the spender ("keeper") the reward that the liveness
 *      Dutch auction permits at this transaction's nLockTime, and
 *   3. output 2 pays the roster slot named by PAYSLOT, if the cycle ran one,
 *      and no satoshis leave the machine except the reward and that payout,
 *      and
 *   4. the machine is input 0, so two machines can never share one output set.
 *
 * Job bounties: a program may read witness cells from the unlocking script
 * (IN), reject the transaction when a check fails (VERIFY), and authorise an
 * extra payout to the spender (BOUNTY n). YIELD ends a cycle early, so a
 * stage bracketed by YIELDs executes atomically and the party that supplied
 * the witnesses is the party that collects the bounty. WHO exposes the first
 * four bytes of the spender's address so programs can bind commitments to
 * the eventual payee (commit-reveal against mempool front-running).
 *
 * K17+ (DC4CD port): MIN and MAX give fuzzy AND/OR; SIGVERIFY k accepts the
 * cycle only if the Rabin signature passed in the unlocking script, under the
 * roster key in slot k, signs the two cells on top of the stack. An
 * off-chain attester (sensor node, oracle) signs a reading once and any
 * keeper may relay it; the keeper is paid by the auction, the attester is
 * trusted only for the reading.
 *
 * v2 machine: the top of memory (cells ROSTER_BASE..MEM_CELLS-1) holds
 * ROSTER_SLOTS_MEM roster slots of SLOT_CELLS cells each (32-byte key hash,
 * then 20-byte payout address hash). The region is write-protected: STORE
 * into it faults. ATTEST checks a reading signed by the key whose hash is
 * in a slot (keyA); ENDORSE checks that a slot member signed for a new
 * member (keyB, payout) and writes sha256(keyB) || payout into an empty
 * slot. Both messages include the machine's instanceId. SIGVERIFY, ATTEST
 * and ENDORSE share one signature per cycle; a bad key or signature
 * invalidates the transaction. VALUE pushes the balance of the machine
 * output being spent. PAYSLOT pays N sats to slot k's payout address in the
 * output after the keeper's reward; the payout has priority and the reward
 * shrinks to make room. A PAYSLOT the program gets wrong (a second one in a
 * cycle, N == 0, or N larger than the balance less one satoshi) is a fault:
 * the machine halts, the payout is dropped and the beneficiary is refunded.
 *
 * Liveness Dutch auction: the reward grows linearly with the time elapsed
 * since the previous cycle (`rewardMin + slope * elapsed`, capped at
 * `rewardMax`). Elapsed time is read from nLockTime, which miners enforce as
 * a lower bound on block time, so a keeper who wants a bigger reward must
 * wait longer before the transaction becomes mineable. Cheap keepers step
 * early for little; expensive keepers only win when the cheap ones are gone.
 *
 * Semantics are defined by `src/k17/isa.ts` and the reference VM in
 * `src/k17/vm.ts`; this file must agree with them exactly.
 *
 * Faults (underflow, overflow, bad address, bad opcode, PC overrun, full
 * output log) never fail the transaction. They halt the machine so the funds
 * can always be released.
 */

import {
    Addr,
    ByteString,
    FixedArray,
    SmartContract,
    Utils,
    and,
    assert,
    byteString2Int,
    hash256,
    int2ByteString,
    len,
    method,
    or,
    prop,
    sha256,
    slice,
    toByteString,
    xor,
} from 'scrypt-ts'
import { RabinPubKey, RabinSig, RabinVerifier } from 'scrypt-ts-lib'

/**
 * Number of attester slots in the fixed SIGVERIFY roster (compile-time
 * constant). Not to be confused with the ISA's ROSTER_SLOTS, the number of
 * memory roster slots.
 */
export const FIXED_ROSTER_SLOTS = 4

export class K17Machine extends SmartContract {
    /** Instructions executed per cycle transaction (compile-time constant). */
    static readonly K = 40

    /** Cell arithmetic modulus, 2^32. */
    @prop()
    static readonly MOD: bigint = 4294967296n
    /** Maximum data-stack size in bytes (32 cells). */
    @prop()
    static readonly DS_MAX_BYTES: bigint = 128n
    /** Maximum return-stack size in bytes (32 cells). */
    @prop()
    static readonly RS_MAX_BYTES: bigint = 128n
    /** Number of memory cells. */
    @prop()
    static readonly MEM_CELLS: bigint = 256n
    /** Maximum output-log size in bytes (256 cells). */
    @prop()
    static readonly OUT_MAX_BYTES: bigint = 1024n
    /** nLockTime values at or above this are unix timestamps, not heights. */
    @prop()
    static readonly UNIX_TIME_MIN: bigint = 500000000n
    /** First memory cell of the write-protected roster region (ISA ROSTER_BASE). */
    @prop()
    static readonly ROSTER_BASE: bigint = 152n
    /** Number of memory roster slots (ISA ROSTER_SLOTS). */
    @prop()
    static readonly ROSTER_SLOTS_MEM: bigint = 8n
    /** Cells per memory roster slot: 8 key-hash cells, 5 payout cells (ISA SLOT_CELLS). */
    @prop()
    static readonly SLOT_CELLS: bigint = 13n
    /** Key hash of an empty roster slot: 32 zero bytes. */
    @prop()
    static readonly EMPTY_HASH: ByteString = toByteString(
        '0000000000000000000000000000000000000000000000000000000000000000'
    )

    // ---- immutable program and economics -------------------------------

    /** K17 bytecode. */
    @prop()
    readonly prog: ByteString
    /** Receives the remaining balance when the machine halts or faults. */
    @prop()
    readonly beneficiary: Addr
    /** Reward (sats) for a cycle that follows the previous one immediately. */
    @prop()
    readonly rewardMin: bigint
    /** Reward growth in sats per second of elapsed time. */
    @prop()
    readonly slope: bigint
    /** Reward ceiling in sats. */
    @prop()
    readonly rewardMax: bigint
    /**
     * Rabin public keys of the attesters a program may name with
     * SIGVERIFY k (k in 0..3). Fixed at deployment; a zero entry is an empty
     * slot and faults any program that references it.
     */
    @prop()
    readonly roster: FixedArray<RabinPubKey, typeof FIXED_ROSTER_SLOTS>
    /**
     * 32-byte id of this machine instance (random by default, see
     * newMachine). ATTEST and ENDORSE messages include it, so a signature
     * made for one machine cannot be replayed into another machine that
     * shares a roster key. `step` refuses any other length.
     */
    @prop()
    readonly instanceId: ByteString

    // ---- mutable machine state ----------------------------------------

    /** Program counter, byte offset into prog. */
    @prop(true)
    pc: bigint
    /** Data stack, 4-byte cells, top at the end. */
    @prop(true)
    ds: ByteString
    /** Return stack, 4-byte cells, top at the end. */
    @prop(true)
    rs: ByteString
    /** Memory image, MEM_CELLS cells. */
    @prop(true)
    mem: ByteString
    /** Output log, 4-byte cells, append-only. */
    @prop(true)
    outLog: ByteString
    /** nLockTime of the transaction that produced this state. */
    @prop(true)
    lastTime: bigint

    constructor(
        prog: ByteString,
        beneficiary: Addr,
        rewardMin: bigint,
        slope: bigint,
        rewardMax: bigint,
        roster: FixedArray<RabinPubKey, typeof FIXED_ROSTER_SLOTS>,
        instanceId: ByteString,
        pc: bigint,
        ds: ByteString,
        rs: ByteString,
        mem: ByteString,
        outLog: ByteString,
        lastTime: bigint
    ) {
        super(...arguments)
        this.prog = prog
        this.beneficiary = beneficiary
        this.rewardMin = rewardMin
        this.slope = slope
        this.rewardMax = rewardMax
        this.roster = roster
        this.instanceId = instanceId
        this.pc = pc
        this.ds = ds
        this.rs = rs
        this.mem = mem
        this.outLog = outLog
        this.lastTime = lastTime
    }

    // ---- cell helpers --------------------------------------------------

    /** Encode an unsigned value in [0, 2^32) as a 4-byte little-endian cell. */
    @method()
    static cell(v: bigint): ByteString {
        // int2ByteString with size 5 yields LE sign-magnitude with a spare
        // sign byte; dropping that byte gives the unsigned 4-byte cell.
        return slice(int2ByteString(v, 5n), 0n, 4n)
    }

    /** Decode a 4-byte cell as an unsigned value. */
    @method()
    static uncell(b: ByteString): bigint {
        return byteString2Int(b + toByteString('00'))
    }

    /** Reduce an integer into [0, 2^32). */
    @method()
    static wrap(v: bigint): bigint {
        let r = v % K17Machine.MOD
        if (r < 0n) {
            r += K17Machine.MOD
        }
        return r
    }

    /**
     * The liveness Dutch auction. Returns the reward (sats) a keeper may take
     * for a cycle performed `elapsed` seconds after the previous one.
     *
     * DESIGN POINT: this function is the whole economic policy of the
     * machine. Linear-with-cap is the simplest thing that makes cheap keepers
     * win early and expensive keepers win only when the cheap ones are gone.
     */
    @method()
    rewardFor(elapsed: bigint): bigint {
        let r = this.rewardMin + this.slope * elapsed
        if (r > this.rewardMax) {
            r = this.rewardMax
        }
        return r
    }

    /**
     * Advance the machine by K instructions and pay the keeper.
     * @param keeper address that receives this cycle's reward
     * @param witness cells consumed by IN, concatenated
     * @param sigS Rabin signature value consumed by the cycle's one
     *        SIGVERIFY, ATTEST or ENDORSE (0 if none)
     * @param sigPad Rabin signature padding for sigS
     * @param keyA Rabin key (pubKeyBytes form, 384 bytes) that signs for
     *        ATTEST or sponsors for ENDORSE; empty when unused
     * @param keyB new member's Rabin key (pubKeyBytes form) for ENDORSE;
     *        empty when unused
     * @param payout new member's 20-byte payout address hash for ENDORSE;
     *        empty when unused
     */
    @method()
    public step(
        keeper: Addr,
        witness: ByteString,
        sigS: bigint,
        sigPad: ByteString,
        keyA: ByteString,
        keyB: ByteString,
        payout: ByteString
    ) {
        assert(len(this.instanceId) == 32n, 'instanceId must be 32 bytes')
        const progLen = len(this.prog)
        const value = this.ctx.utxo.value
        const witnessLen = len(witness)
        const who = K17Machine.uncell(slice(keeper, 0n, 4n))
        const sig: RabinSig = { s: sigS, padding: sigPad }
        let pc = this.pc
        let ds = this.ds
        let rs = this.rs
        let mem = this.mem
        let outLog = this.outLog
        let halted = false
        let yielded = false
        let wi = 0n
        let bountyDue = 0n
        let sigUsed = false
        let payslotUsed = false
        let payslotSats = 0n
        // Placeholder until PAYSLOT runs; only read when payslotUsed.
        let payslotAddr: Addr = this.beneficiary

        for (let i = 0; i < K17Machine.K; i++) {
            if (!halted && !yielded) {
                if (pc >= progLen) {
                    halted = true
                } else {
                    const op = byteString2Int(slice(this.prog, pc, pc + 1n))
                    let nextPc = pc + 1n
                    let operand = 0n
                    let decodeOk = true
                    if (
                        op == 14n ||
                        op == 15n ||
                        op == 17n ||
                        op == 23n ||
                        op == 30n
                    ) {
                        if (pc + 5n > progLen) {
                            decodeOk = false
                        } else {
                            operand = K17Machine.uncell(
                                slice(this.prog, pc + 1n, pc + 5n)
                            )
                            nextPc = pc + 5n
                        }
                    }
                    if (!decodeOk) {
                        halted = true
                    } else {
                        // SIGVERIFY, ATTEST and ENDORSE set these instead of
                        // calling RabinVerifier themselves; the one check
                        // after the handlers keeps a single verifier per
                        // unrolled step in the script.
                        let verifyNeeded = false
                        let verifyMsg = toByteString('')
                        let verifyKey: RabinPubKey = 0n
                        const n = len(ds)
                        const r = len(rs)
                        // Top two data cells, valid only when n >= 8.
                        const top =
                            n >= 4n
                                ? K17Machine.uncell(slice(ds, n - 4n, n))
                                : 0n
                        const second =
                            n >= 8n
                                ? K17Machine.uncell(slice(ds, n - 8n, n - 4n))
                                : 0n
                        const ds1 = n >= 4n ? slice(ds, 0n, n - 4n) : ds
                        const ds2 = n >= 8n ? slice(ds, 0n, n - 8n) : ds

                        if (op == 0n) {
                            // HALT
                            halted = true
                        } else if (op == 1n) {
                            // !  : N1 ADDR --   the roster region is write-protected
                            if (n < 8n || top >= K17Machine.ROSTER_BASE) {
                                halted = true
                            } else {
                                mem =
                                    slice(mem, 0n, top * 4n) +
                                    K17Machine.cell(second) +
                                    slice(mem, top * 4n + 4n)
                                ds = ds2
                            }
                        } else if (op == 2n) {
                            // +
                            if (n < 8n) {
                                halted = true
                            } else {
                                ds =
                                    ds2 +
                                    K17Machine.cell(
                                        K17Machine.wrap(second + top)
                                    )
                            }
                        } else if (op == 3n) {
                            // -
                            if (n < 8n) {
                                halted = true
                            } else {
                                ds =
                                    ds2 +
                                    K17Machine.cell(
                                        K17Machine.wrap(second - top)
                                    )
                            }
                        } else if (op == 4n) {
                            // >R
                            if (n < 4n || r >= K17Machine.RS_MAX_BYTES) {
                                halted = true
                            } else {
                                rs = rs + K17Machine.cell(top)
                                ds = ds1
                            }
                        } else if (op == 5n) {
                            // @ : ADDR -- N1
                            if (n < 4n || top >= K17Machine.MEM_CELLS) {
                                halted = true
                            } else {
                                ds = ds1 + slice(mem, top * 4n, top * 4n + 4n)
                            }
                        } else if (op == 6n) {
                            // AND
                            if (n < 8n) {
                                halted = true
                            } else {
                                ds = ds2 + K17Machine.cell(and(second, top))
                            }
                        } else if (op == 7n) {
                            // DROP
                            if (n < 4n) {
                                halted = true
                            } else {
                                ds = ds1
                            }
                        } else if (op == 8n) {
                            // DUP
                            if (n < 4n || n >= K17Machine.DS_MAX_BYTES) {
                                halted = true
                            } else {
                                ds = ds + K17Machine.cell(top)
                            }
                        } else if (op == 9n) {
                            // OR
                            if (n < 8n) {
                                halted = true
                            } else {
                                ds = ds2 + K17Machine.cell(or(second, top))
                            }
                        } else if (op == 10n) {
                            // OVER : N1 N2 -- N1 N2 N1
                            if (n < 8n || n >= K17Machine.DS_MAX_BYTES) {
                                halted = true
                            } else {
                                ds = ds + K17Machine.cell(second)
                            }
                        } else if (op == 11n) {
                            // R>
                            if (r < 4n || n >= K17Machine.DS_MAX_BYTES) {
                                halted = true
                            } else {
                                ds = ds + slice(rs, r - 4n, r)
                                rs = slice(rs, 0n, r - 4n)
                            }
                        } else if (op == 12n) {
                            // SWAP
                            if (n < 8n) {
                                halted = true
                            } else {
                                ds =
                                    ds2 +
                                    K17Machine.cell(top) +
                                    K17Machine.cell(second)
                            }
                        } else if (op == 13n) {
                            // XOR
                            if (n < 8n) {
                                halted = true
                            } else {
                                ds = ds2 + K17Machine.cell(xor(second, top))
                            }
                        } else if (op == 14n) {
                            // [IF] : N1 --  branch when N1 == 0
                            if (n < 4n) {
                                halted = true
                            } else {
                                ds = ds1
                                if (top == 0n) {
                                    nextPc = operand
                                }
                            }
                        } else if (op == 15n) {
                            // [CALL]
                            if (r >= K17Machine.RS_MAX_BYTES) {
                                halted = true
                            } else {
                                rs = rs + K17Machine.cell(nextPc)
                                nextPc = operand
                            }
                        } else if (op == 16n) {
                            // [EXIT]
                            if (r < 4n) {
                                halted = true
                            } else {
                                nextPc = K17Machine.uncell(slice(rs, r - 4n, r))
                                rs = slice(rs, 0n, r - 4n)
                            }
                        } else if (op == 17n) {
                            // [LIT]
                            if (n >= K17Machine.DS_MAX_BYTES) {
                                halted = true
                            } else {
                                ds = ds + K17Machine.cell(operand)
                            }
                        } else if (op == 18n) {
                            // 0=
                            if (n < 4n) {
                                halted = true
                            } else {
                                ds = ds1 + K17Machine.cell(top == 0n ? 1n : 0n)
                            }
                        } else if (op == 19n) {
                            // OUT
                            if (
                                n < 4n ||
                                len(outLog) >= K17Machine.OUT_MAX_BYTES
                            ) {
                                halted = true
                            } else {
                                outLog = outLog + K17Machine.cell(top)
                                ds = ds1
                            }
                        } else if (op == 20n) {
                            // TIME
                            if (n >= K17Machine.DS_MAX_BYTES) {
                                halted = true
                            } else {
                                ds =
                                    ds +
                                    K17Machine.cell(
                                        K17Machine.wrap(this.ctx.locktime)
                                    )
                            }
                        } else if (op == 21n) {
                            // IN : -- W   (no witness left => tx invalid, not a fault)
                            if (n >= K17Machine.DS_MAX_BYTES) {
                                halted = true
                            } else {
                                assert(
                                    wi + 4n <= witnessLen,
                                    'witness required'
                                )
                                ds = ds + slice(witness, wi, wi + 4n)
                                wi += 4n
                            }
                        } else if (op == 22n) {
                            // VERIFY : N1 --   (zero => tx invalid, not a fault)
                            if (n < 4n) {
                                halted = true
                            } else {
                                assert(top != 0n, 'verify failed')
                                ds = ds1
                            }
                        } else if (op == 23n) {
                            // BOUNTY n
                            bountyDue += operand
                        } else if (op == 24n) {
                            // *
                            if (n < 8n) {
                                halted = true
                            } else {
                                ds =
                                    ds2 +
                                    K17Machine.cell(
                                        K17Machine.wrap(second * top)
                                    )
                            }
                        } else if (op == 25n) {
                            // HASH : N1 -- first 4 bytes of sha256(cell(N1))
                            if (n < 4n) {
                                halted = true
                            } else {
                                ds =
                                    ds1 +
                                    slice(sha256(K17Machine.cell(top)), 0n, 4n)
                            }
                        } else if (op == 26n) {
                            // WHO
                            if (n >= K17Machine.DS_MAX_BYTES) {
                                halted = true
                            } else {
                                ds = ds + K17Machine.cell(who)
                            }
                        } else if (op == 27n) {
                            // YIELD : end the cycle after this instruction
                            yielded = true
                        } else if (op == 28n) {
                            // MIN
                            if (n < 8n) {
                                halted = true
                            } else {
                                ds =
                                    ds2 +
                                    K17Machine.cell(second < top ? second : top)
                            }
                        } else if (op == 29n) {
                            // MAX
                            if (n < 8n) {
                                halted = true
                            } else {
                                ds =
                                    ds2 +
                                    K17Machine.cell(second > top ? second : top)
                            }
                        } else if (op == 31n) {
                            // /  : unsigned division, zero divisor is a fault
                            if (n < 8n || top == 0n) {
                                halted = true
                            } else {
                                ds = ds2 + K17Machine.cell(second / top)
                            }
                        } else if (op == 30n) {
                            // SIGVERIFY k : TAG VAL --
                            // Bad roster index or empty slot: fault. Missing,
                            // reused or wrong signature: tx invalid.
                            if (n < 8n || operand >= 4n) {
                                halted = true
                            } else {
                                const pub = this.roster[Number(operand)]
                                if (pub == 0n) {
                                    halted = true
                                } else {
                                    assert(
                                        !sigUsed,
                                        'one attestation per cycle'
                                    )
                                    sigUsed = true
                                    // ATTEST_DOMAIN ("K17A") || cell(TAG) || cell(VAL)
                                    verifyNeeded = true
                                    verifyMsg =
                                        toByteString('4b313741') +
                                        slice(ds, n - 8n, n)
                                    verifyKey = pub
                                    ds = ds2
                                }
                            }
                        } else if (op == 32n) {
                            // ATTEST : TAG VAL SLOT --
                            // Underflow, bad slot or empty slot: fault. A
                            // second signature, a key that is not 384 bytes
                            // or not the slot's, or a bad signature: tx
                            // invalid.
                            if (n < 12n || top >= K17Machine.ROSTER_SLOTS_MEM) {
                                halted = true
                            } else {
                                const slotByte =
                                    (K17Machine.ROSTER_BASE +
                                        top * K17Machine.SLOT_CELLS) *
                                    4n
                                const slotHash = slice(
                                    mem,
                                    slotByte,
                                    slotByte + 32n
                                )
                                if (slotHash == K17Machine.EMPTY_HASH) {
                                    halted = true
                                } else {
                                    assert(
                                        !sigUsed,
                                        'one attestation per cycle'
                                    )
                                    assert(
                                        len(keyA) == 384n,
                                        'key must be 384 bytes'
                                    )
                                    assert(
                                        sha256(keyA) == slotHash,
                                        'key not in roster slot'
                                    )
                                    sigUsed = true
                                    // "K17M" || instanceId || cell(TAG) || cell(VAL)
                                    verifyNeeded = true
                                    verifyMsg =
                                        toByteString('4b31374d') +
                                        this.instanceId +
                                        slice(ds, n - 12n, n - 4n)
                                    verifyKey = Utils.fromLEUnsigned(keyA)
                                    ds = slice(ds, 0n, n - 12n)
                                }
                            }
                        } else if (op == 33n) {
                            // ENDORSE : TAG SLOT NEWSLOT --
                            // Underflow, bad or empty SLOT, bad or filled
                            // NEWSLOT: fault. A second signature, keys that
                            // are not 384 bytes, a payout that is not 20
                            // bytes, a sponsor key that is not SLOT's, or a
                            // bad signature: tx invalid.
                            if (
                                n < 12n ||
                                second >= K17Machine.ROSTER_SLOTS_MEM
                            ) {
                                halted = true
                            } else {
                                const sponsorByte =
                                    (K17Machine.ROSTER_BASE +
                                        second * K17Machine.SLOT_CELLS) *
                                    4n
                                const sponsorHash = slice(
                                    mem,
                                    sponsorByte,
                                    sponsorByte + 32n
                                )
                                const newByte =
                                    (K17Machine.ROSTER_BASE +
                                        top * K17Machine.SLOT_CELLS) *
                                    4n
                                if (sponsorHash == K17Machine.EMPTY_HASH) {
                                    halted = true
                                } else if (top >= K17Machine.ROSTER_SLOTS_MEM) {
                                    halted = true
                                } else if (
                                    slice(mem, newByte, newByte + 32n) !=
                                    K17Machine.EMPTY_HASH
                                ) {
                                    halted = true
                                } else {
                                    assert(
                                        !sigUsed,
                                        'one attestation per cycle'
                                    )
                                    assert(
                                        len(keyA) == 384n,
                                        'key must be 384 bytes'
                                    )
                                    assert(
                                        len(keyB) == 384n,
                                        'new key must be 384 bytes'
                                    )
                                    assert(
                                        len(payout) == 20n,
                                        'payout must be 20 bytes'
                                    )
                                    assert(
                                        sha256(keyA) == sponsorHash,
                                        'key not in roster slot'
                                    )
                                    sigUsed = true
                                    const newHash = sha256(keyB)
                                    // "K17E" || instanceId || cell(TAG) ||
                                    // cell(NEWSLOT) || sha256(keyB) || payout
                                    verifyNeeded = true
                                    verifyMsg =
                                        toByteString('4b313745') +
                                        this.instanceId +
                                        slice(ds, n - 12n, n - 8n) +
                                        slice(ds, n - 4n, n) +
                                        newHash +
                                        payout
                                    verifyKey = Utils.fromLEUnsigned(keyA)
                                    mem =
                                        slice(mem, 0n, newByte) +
                                        newHash +
                                        payout +
                                        slice(mem, newByte + 52n)
                                    ds = slice(ds, 0n, n - 12n)
                                }
                            }
                        } else if (op == 34n) {
                            // PAYSLOT : N SLOT --
                            // A second PAYSLOT this cycle (checked first,
                            // however malformed): fault that drops the
                            // payout. Underflow, bad slot, empty slot or
                            // N == 0: fault. Never tx-invalid.
                            if (payslotUsed) {
                                halted = true
                                payslotUsed = false
                                payslotSats = 0n
                            } else if (
                                n < 8n ||
                                top >= K17Machine.ROSTER_SLOTS_MEM
                            ) {
                                halted = true
                            } else {
                                const slotByte =
                                    (K17Machine.ROSTER_BASE +
                                        top * K17Machine.SLOT_CELLS) *
                                    4n
                                if (
                                    slice(mem, slotByte, slotByte + 32n) ==
                                    K17Machine.EMPTY_HASH
                                ) {
                                    halted = true
                                } else if (second == 0n) {
                                    halted = true
                                } else {
                                    payslotUsed = true
                                    payslotSats = second
                                    payslotAddr = Addr(
                                        slice(
                                            mem,
                                            slotByte + 32n,
                                            slotByte + 52n
                                        )
                                    )
                                    ds = ds2
                                }
                            }
                        } else if (op == 35n) {
                            // VALUE : -- V
                            if (n >= K17Machine.DS_MAX_BYTES) {
                                halted = true
                            } else {
                                ds =
                                    ds + K17Machine.cell(K17Machine.wrap(value))
                            }
                        } else {
                            // unknown opcode
                            halted = true
                        }

                        if (verifyNeeded) {
                            assert(
                                RabinVerifier.verifySig(
                                    verifyMsg,
                                    sig,
                                    verifyKey
                                ),
                                'signature check failed'
                            )
                        }

                        if (!halted) {
                            pc = nextPc
                        }
                    }
                }
            }
        }

        // ---- anti output-sharing ------------------------------------
        // Two machines with identical scripts and values could otherwise be
        // spent together, both accepting one shared state output while the
        // keeper pockets the second balance as change. Requiring this input
        // to be input 0 means at most one machine can be spent per tx.
        const prevouts = this.prevouts
        assert(
            hash256(prevouts) == this.ctx.hashPrevouts,
            'prevouts do not match hashPrevouts'
        )
        const selfOutpoint =
            this.ctx.utxo.outpoint.txid +
            int2ByteString(this.ctx.utxo.outpoint.outputIndex, 4n)
        assert(
            slice(prevouts, 0n, 36n) == selfOutpoint,
            'machine must be input 0'
        )

        // ---- liveness Dutch auction ----------------------------------
        assert(
            this.ctx.sequence < 0xffffffffn,
            'nSequence must be below 0xffffffff so nLockTime is enforced'
        )
        const now = this.ctx.locktime
        assert(
            now >= K17Machine.UNIX_TIME_MIN,
            'nLockTime must be a unix timestamp'
        )
        const elapsed = now - this.lastTime
        assert(elapsed >= 0n, 'time must not go backwards')

        // Keeper reward from the auction plus any bounty the program released.
        let reward = this.rewardFor(elapsed) + bountyDue
        if (reward > value - 1n) {
            // Never drain the machine below one satoshi.
            reward = value - 1n
        }
        if (payslotUsed) {
            // The slot payout has priority over the keeper's reward: the
            // reward shrinks (to 0 at worst) so the payout is paid in full.
            // Only a payout the balance cannot cover with one satoshi left,
            // which no keeper can cause, is a fault: halt, drop the payout,
            // refund the beneficiary.
            const cap = value - 1n - payslotSats
            if (cap < 0n) {
                halted = true
                payslotUsed = false
                payslotSats = 0n
            } else if (reward > cap) {
                reward = cap
            }
        }
        const remaining = value - reward - payslotSats

        // ---- outputs -------------------------------------------------
        let outputs = toByteString('')
        if (halted) {
            outputs = Utils.buildPublicKeyHashOutput(
                this.beneficiary,
                remaining
            )
        } else {
            this.pc = pc
            this.ds = ds
            this.rs = rs
            this.mem = mem
            this.outLog = outLog
            this.lastTime = now
            outputs = this.buildStateOutput(remaining)
        }
        if (reward > 0n) {
            outputs += Utils.buildPublicKeyHashOutput(keeper, reward)
        }
        if (payslotUsed) {
            outputs += Utils.buildPublicKeyHashOutput(payslotAddr, payslotSats)
        }
        outputs += this.buildChangeOutput()
        assert(hash256(outputs) == this.ctx.hashOutputs, 'outputs mismatch')
    }
}
