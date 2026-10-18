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
 *   3. no satoshis leave the machine except that reward, and
 *   4. the machine is input 0, so two machines can never share one output set.
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
    slice,
    toByteString,
    xor,
} from 'scrypt-ts'

export class K17Machine extends SmartContract {
    /** Instructions executed per cycle transaction (compile-time constant). */
    static readonly K = 4

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
    static readonly MEM_CELLS: bigint = 64n
    /** Maximum output-log size in bytes (64 cells). */
    @prop()
    static readonly OUT_MAX_BYTES: bigint = 256n
    /** nLockTime values at or above this are unix timestamps, not heights. */
    @prop()
    static readonly UNIX_TIME_MIN: bigint = 500000000n

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
     */
    @method()
    public step(keeper: Addr) {
        const progLen = len(this.prog)
        let pc = this.pc
        let ds = this.ds
        let rs = this.rs
        let mem = this.mem
        let outLog = this.outLog
        let halted = false

        for (let i = 0; i < K17Machine.K; i++) {
            if (!halted) {
                if (pc >= progLen) {
                    halted = true
                } else {
                    const op = byteString2Int(slice(this.prog, pc, pc + 1n))
                    let nextPc = pc + 1n
                    let operand = 0n
                    let decodeOk = true
                    if (op == 14n || op == 15n || op == 17n) {
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
                            // !  : N1 ADDR --
                            if (n < 8n || top >= K17Machine.MEM_CELLS) {
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
                        } else {
                            // unknown opcode
                            halted = true
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

        const value = this.ctx.utxo.value
        let reward = this.rewardFor(elapsed)
        if (reward > value - 1n) {
            // Never drain the machine below one satoshi.
            reward = value - 1n
        }

        // ---- outputs -------------------------------------------------
        let outputs = toByteString('')
        if (halted) {
            outputs = Utils.buildPublicKeyHashOutput(
                this.beneficiary,
                value - reward
            )
        } else {
            this.pc = pc
            this.ds = ds
            this.rs = rs
            this.mem = mem
            this.outLog = outLog
            this.lastTime = now
            outputs = this.buildStateOutput(value - reward)
        }
        if (reward > 0n) {
            outputs += Utils.buildPublicKeyHashOutput(keeper, reward)
        }
        outputs += this.buildChangeOutput()
        assert(hash256(outputs) == this.ctx.hashOutputs, 'outputs mismatch')
    }
}
