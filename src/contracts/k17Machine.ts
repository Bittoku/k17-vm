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
 *   3. the payout output pays the roster slot named by PAYSLOT, if the cycle
 *      ran one; it follows the keeper reward output when one exists (it is
 *      output 1 when the reward is 0), and no satoshis leave the machine
 *      except the reward and that payout, and
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
 * invalidates the transaction, and a second signature instruction in the
 * cycle is a fault (v3.1). VALUE pushes the balance of the machine
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
 * v3 machine (Merkle roster): the roster also lives in a depth-16 sparse
 * Merkle tree whose root is the mutable `rosterRoot` (see `src/k17/smt.ts`
 * for the leaf and proof format). Each cycle carries at most one tree proof
 * in the unlocking script (`leafPre`, `proof`, `leafIndex`). MEMBER binds the
 * proven leaf and pushes its index; LASTROUND pushes the bound member's
 * lastRound; ATTESTM checks a reading signed by the bound member's key
 * ("K17T" || instanceId || cell(TAG) || cell(VAL)); PAYLEAF pays the bound
 * member through the PAYSLOT accounting and advances its lastRound, which
 * changes the leaf and so the root; OUTH folds a cell into the running
 * `logHash`. Handlers inside the unrolled loop only record what they need
 * (`treeOp`, the member's lastRound, whether ATTESTM ran and whether the
 * leaf changed). ADMIT (TAG ROUND --) lets the sponsor (the key whose
 * hash is `sponsorKeyHash`) put a new member into an empty leaf with
 * lastRound := ROUND; REMOVE (TAG --) lets the sponsor empty an occupied
 * leaf. Both sign a message that includes `rosterSeq`, and both add one to
 * `rosterSeq`, so a sponsor signature works once only. After the loop,
 * before the Rabin check, the proof is checked once against the old root,
 * the ATTESTM key is checked against the leaf's key hash, the ADMIT or
 * REMOVE witnesses and message are checked and built, and, when the leaf
 * changed, the new leaf hash is walked up the same proof to give the new
 * root. A missing or wrong proof, preimage, index, key or signature
 * invalidates the transaction; a tree instruction the program misuses (a
 * short stack, a second tree instruction in the cycle, no bound member) is
 * a fault. One tree instruction, one signature and one payment per cycle.
 *
 * v3.1: a second signature instruction in one cycle (SIGVERIFY, ATTEST,
 * ENDORSE, ATTESTM, ADMIT or REMOVE after any of them) is a fault, checked
 * in the same condition as the handler's stack underflow, so a program can
 * never make the machine unspendable that way.
 *
 * Semantics are defined by `src/k17/isa.ts` and the reference VM in
 * `src/k17/vm.ts`; this file must agree with them exactly.
 *
 * v3.1 freeze escape: an immutable `deadMan` (seconds, 0 = off) halts the
 * machine at the top of `step`, before any instruction, witness, signature
 * or tree check, once nLockTime >= lastTime + deadMan; the cycle then takes
 * the refund path and pays the keeper its reward. A cycle that keeps the
 * machine alive must advance the clock by at least MIN_STEP (60 s), so a
 * keeper cannot pin lastTime; halting cycles are exempt.
 *
 * Faults (underflow, overflow, bad address, bad opcode, PC overrun, full
 * output log, a second signature instruction) never fail the transaction. They halt the machine so the funds
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
    /**
     * 32 zero bytes: the key hash of an empty memory roster slot, and the
     * hash of an empty tree leaf (smt EMPTY_HASHES[0]). The contract reads
     * no other empty-subtree hash; proofs carry the siblings.
     */
    @prop()
    static readonly EMPTY_HASH: ByteString = toByteString(
        '0000000000000000000000000000000000000000000000000000000000000000'
    )
    /** Levels of the roster Merkle tree (compile-time constant, smt TREE_DEPTH). */
    static readonly TREE_DEPTH = 16
    /** Bytes of a tree proof: TREE_DEPTH sibling hashes of 32 bytes. */
    @prop()
    static readonly PROOF_BYTES: bigint = 512n
    /** Number of leaves of the roster tree, 2^TREE_DEPTH. */
    @prop()
    static readonly TREE_LEAVES: bigint = 65536n
    /** Bytes of a leaf preimage: keyHash(32) || payout(20) || cell(lastRound) || cell(flags). */
    @prop()
    static readonly LEAF_PRE_BYTES: bigint = 60n
    /** Domain prefix of a leaf hash, ASCII "K17L" (smt LEAF_DOMAIN). */
    @prop()
    static readonly LEAF_DOMAIN: ByteString = toByteString('4b31374c')
    /** Domain prefix of an ATTESTM message, ASCII "K17T" (attest MEMBER_DOMAIN). */
    @prop()
    static readonly MEMBER_DOMAIN: ByteString = toByteString('4b313754')
    /** Domain prefix of an ADMIT message, ASCII "K17D" (attest ADMIT_DOMAIN). */
    @prop()
    static readonly ADMIT_DOMAIN: ByteString = toByteString('4b313744')
    /** Domain prefix of a REMOVE message, ASCII "K17X" (attest REMOVE_DOMAIN). */
    @prop()
    static readonly REMOVE_DOMAIN: ByteString = toByteString('4b313758')
    /** Bytes of a Rabin public key in pubKeyBytes form. */
    @prop()
    static readonly KEY_BYTES: bigint = 384n
    /** Bytes of a payout address hash. */
    @prop()
    static readonly PAYOUT_BYTES: bigint = 20n
    /**
     * Minimum clock advance, in seconds, of a cycle that keeps the machine
     * alive (v3.1): its nLockTime must be at least lastTime + MIN_STEP. A
     * keeper therefore cannot hold the clock still while it drives the
     * machine (which would bring the dead-man halt earlier in real time,
     * since lastTime would lag behind the chain's clock), and a chain of
     * unconfirmed cycles cannot run the program with a frozen clock. A
     * cycle that halts (HALT, a fault or the dead-man) is exempt, so this
     * rule never blocks a refund.
     */
    @prop()
    static readonly MIN_STEP: bigint = 60n

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
     * Dead-man interval in seconds (v3.1); 0 disables it. A cycle whose
     * nLockTime is at least lastTime + deadMan halts the machine before its
     * first instruction: it takes the fault path (refund to the
     * beneficiary, keeper reward paid) and needs no witness, signature or
     * tree proof. So a machine that waits for a witness nobody supplies
     * (IN, MEMBER on an empty tree) is refunded after deadMan seconds
     * without a cycle, instead of being frozen. Fixed at deployment.
     */
    @prop()
    readonly deadMan: bigint
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
     * shares a roster key. Any other length faults the machine at its
     * first cycle (refund to the beneficiary).
     */
    @prop()
    readonly instanceId: ByteString
    /**
     * sha256 of the sponsor's Rabin key (32 bytes, pubKeyBytes form), the
     * key that signs ADMIT and REMOVE. All zero means the machine has no
     * sponsor: no key hashes to it, so ADMIT and REMOVE can never verify.
     * Fixed at deployment.
     */
    @prop()
    readonly sponsorKeyHash: ByteString

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
    /**
     * Root of the roster Merkle tree (32 bytes). Every MEMBER proof is
     * checked against it; PAYLEAF (and ADMIT/REMOVE) replace it with the
     * root after their leaf change. The empty tree's root is smt
     * EMPTY_HASHES[16].
     */
    @prop(true)
    rosterRoot: ByteString
    /**
     * Count of roster mutations (ADMIT and REMOVE) so far. ADMIT and REMOVE
     * messages include it and each adds one, so a sponsor signature cannot
     * be replayed.
     */
    @prop(true)
    rosterSeq: bigint
    /**
     * Running hash of the cells OUTH emitted (32 bytes, starts all zero):
     * logHash := sha256(logHash || cell(N1)) per OUTH.
     */
    @prop(true)
    logHash: ByteString

    constructor(
        prog: ByteString,
        beneficiary: Addr,
        rewardMin: bigint,
        slope: bigint,
        rewardMax: bigint,
        deadMan: bigint,
        roster: FixedArray<RabinPubKey, typeof FIXED_ROSTER_SLOTS>,
        instanceId: ByteString,
        sponsorKeyHash: ByteString,
        pc: bigint,
        ds: ByteString,
        rs: ByteString,
        mem: ByteString,
        outLog: ByteString,
        lastTime: bigint,
        rosterRoot: ByteString,
        rosterSeq: bigint,
        logHash: ByteString
    ) {
        super(...arguments)
        this.prog = prog
        this.beneficiary = beneficiary
        this.rewardMin = rewardMin
        this.slope = slope
        this.rewardMax = rewardMax
        this.deadMan = deadMan
        this.roster = roster
        this.instanceId = instanceId
        this.sponsorKeyHash = sponsorKeyHash
        this.pc = pc
        this.ds = ds
        this.rs = rs
        this.mem = mem
        this.outLog = outLog
        this.lastTime = lastTime
        this.rosterRoot = rosterRoot
        this.rosterSeq = rosterSeq
        this.logHash = logHash
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
     * Fold a leaf hash up the roster tree along a proof (smt foldRoot).
     * At level k the sibling is bytes [32k, 32k + 32) of `proof`; bit k of
     * `leafIndex` set means the current node is the right child, so the
     * parent is sha256(sibling || node), else sha256(node || sibling).
     * Input: 32-byte leaf hash, 512-byte proof (level 0 first), leaf index
     * in [0, 2^TREE_DEPTH). The caller checks both ranges.
     * Output: the 32-byte root the proof leads to.
     */
    @method()
    static treeRoot(
        leafHash: ByteString,
        proof: ByteString,
        leafIndex: bigint
    ): ByteString {
        let node = leafHash
        let indexBits = leafIndex
        let siblingOffset = 0n
        for (let level = 0; level < K17Machine.TREE_DEPTH; level++) {
            const sibling = slice(proof, siblingOffset, siblingOffset + 32n)
            if (indexBits % 2n == 1n) {
                node = sha256(sibling + node)
            } else {
                node = sha256(node + sibling)
            }
            indexBits = indexBits / 2n
            siblingOffset += 32n
        }
        return node
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
     *        SIGVERIFY, ATTEST, ENDORSE, ATTESTM, ADMIT or REMOVE (0 if
     *        none)
     * @param sigPad Rabin signature padding for sigS
     * @param keyA Rabin key (pubKeyBytes form, 384 bytes) that signs for
     *        ATTEST or ATTESTM, sponsors for ENDORSE, or is the sponsor key
     *        for ADMIT and REMOVE; empty when unused
     * @param keyB new member's Rabin key (pubKeyBytes form) for ENDORSE or
     *        ADMIT; empty when unused
     * @param payout new member's 20-byte payout address hash for ENDORSE or
     *        ADMIT; empty when unused
     * @param leafPre the cycle's one roster-tree leaf preimage: 60 bytes
     *        (keyHash || payout || cell(lastRound) || cell(flags)) for
     *        MEMBER and REMOVE, empty for ADMIT (the leaf must be empty) and
     *        when no tree instruction runs
     * @param proof the 16 sibling hashes of that leaf, level 0 first
     *        (512 bytes); empty when no tree instruction runs
     * @param leafIndex the leaf's position in [0, 65536); 0 when unused.
     *        The three tree arguments are only checked when the cycle ran a
     *        tree instruction (treeOp != 0).
     */
    @method()
    public step(
        keeper: Addr,
        witness: ByteString,
        sigS: bigint,
        sigPad: ByteString,
        keyA: ByteString,
        keyB: ByteString,
        payout: ByteString,
        leafPre: ByteString,
        proof: ByteString,
        leafIndex: bigint
    ) {
        // Tree-instruction bookkeeping is declared first so it sits deep on
        // the stack and the hot loop variables below stay shallow (cheaper
        // stack access in every unrolled iteration).
        // Roster-tree operation of this cycle: 0 none, 1 MEMBER, 2 ADMIT,
        // 3 REMOVE. At most one per cycle; the proof is checked once after
        // the loop when treeOp != 0.
        let treeOp = 0n
        // lastRound of the leaf MEMBER bound (only read when treeOp == 1);
        // PAYLEAF advances it to ROUND. The other member fields are sliced
        // from leafPre where needed, so the loop carries no copies of them.
        let memberLastRound = 0n
        // The operand cells of ADMIT (cell(TAG) || cell(ROUND)) or REMOVE
        // (cell(TAG)), as they were on the stack; the message and new leaf
        // are built from them after the loop.
        let treeArgs = toByteString('')
        // True once PAYLEAF, ADMIT or REMOVE replaced the leaf; the new
        // leaf hash and root are computed after the loop only then.
        let leafChanged = false
        // True once ATTESTM ran; its key-to-leaf check runs after the loop.
        let memberKeyCheck = false
        let logHash = this.logHash
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
        // A malformed deployment (instanceId not 32 bytes) faults before the
        // first instruction, so its balance is refunded, never frozen.
        let halted = len(this.instanceId) != 32n
        // Dead-man halt (v3.1): when deadMan seconds have passed since the
        // last cycle, this cycle halts before its first instruction. treeOp,
        // verifyNeeded and memberKeyCheck then stay unset, so no witness,
        // signature or tree check runs and the refund is always spendable.
        if (
            this.deadMan > 0n &&
            this.ctx.locktime >= this.lastTime + this.deadMan
        ) {
            halted = true
        }
        let yielded = false
        let wi = 0n
        let bountyDue = 0n
        let sigUsed = false
        let payslotUsed = false
        let payslotSats = 0n
        // Placeholder until PAYSLOT runs; only read when payslotUsed.
        let payslotAddr: Addr = this.beneficiary
        // SIGVERIFY, ATTEST, ENDORSE and ATTESTM record the message and key
        // here in the loop; ADMIT and REMOVE record them after the loop, in
        // the tree block. None of them calls RabinVerifier itself. sigUsed
        // allows one signature per cycle, so one verification covers it and
        // the verifier appears once in the script. That verification runs
        // after the tree block, because the tree block builds the ADMIT and
        // REMOVE message.
        let verifyNeeded = false
        let verifyMsg = toByteString('')
        let verifyKey: RabinPubKey = 0n

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
                            // Underflow, bad roster index, a second signature
                            // this cycle or an empty slot: fault. Missing or
                            // wrong signature: tx invalid.
                            if (n < 8n || operand >= 4n || sigUsed) {
                                halted = true
                            } else {
                                const pub = this.roster[Number(operand)]
                                if (pub == 0n) {
                                    halted = true
                                } else {
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
                            // Underflow, bad slot, a second signature this
                            // cycle or empty slot: fault. A key that is not
                            // 384 bytes or not the slot's, or a bad
                            // signature: tx invalid.
                            if (
                                n < 12n ||
                                top >= K17Machine.ROSTER_SLOTS_MEM ||
                                sigUsed
                            ) {
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
                            // Underflow, bad or empty SLOT, a second
                            // signature this cycle, bad or filled NEWSLOT:
                            // fault. Keys that are not 384 bytes, a payout
                            // that is not 20 bytes, a sponsor key that is not
                            // SLOT's, or a bad signature: tx invalid.
                            if (
                                n < 12n ||
                                second >= K17Machine.ROSTER_SLOTS_MEM ||
                                sigUsed
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
                        } else if (op == 36n) {
                            // MEMBER : -- IDX
                            // A second tree instruction this cycle: fault.
                            // A leafPre that is not 60 bytes: tx invalid.
                            // The proof and index are checked after the
                            // loop (tx invalid when wrong), even when a
                            // full data stack faults here, as in the VM.
                            if (treeOp != 0n) {
                                halted = true
                            } else {
                                assert(
                                    len(leafPre) == K17Machine.LEAF_PRE_BYTES,
                                    'leaf preimage must be 60 bytes'
                                )
                                treeOp = 1n
                                memberLastRound = K17Machine.uncell(
                                    slice(leafPre, 52n, 56n)
                                )
                                if (n >= K17Machine.DS_MAX_BYTES) {
                                    halted = true
                                } else {
                                    ds = ds + K17Machine.cell(leafIndex)
                                }
                            }
                        } else if (op == 37n) {
                            // LASTROUND : -- R   no bound member: fault
                            if (treeOp != 1n || n >= K17Machine.DS_MAX_BYTES) {
                                halted = true
                            } else {
                                ds = ds + K17Machine.cell(memberLastRound)
                            }
                        } else if (op == 38n) {
                            // ATTESTM : TAG VAL --
                            // Underflow, no bound member or a second
                            // signature this cycle: fault. A key that is not
                            // the member's, or a bad signature: tx invalid.
                            if (n < 8n || treeOp != 1n || sigUsed) {
                                halted = true
                            } else {
                                // sha256(keyA) must equal the leaf's key
                                // hash: checked after the loop. That check
                                // pins keyA, so no length check is needed.
                                memberKeyCheck = true
                                sigUsed = true
                                // "K17T" || instanceId || cell(TAG) || cell(VAL)
                                verifyNeeded = true
                                verifyMsg =
                                    K17Machine.MEMBER_DOMAIN +
                                    this.instanceId +
                                    slice(ds, n - 8n, n)
                                verifyKey = Utils.fromLEUnsigned(keyA)
                                ds = ds2
                            }
                        } else if (op == 39n) {
                            // PAYLEAF : N ROUND --
                            // A second payment this cycle (checked first):
                            // fault that drops the payout. Underflow, no
                            // bound member or N == 0: fault. ROUND not above
                            // the member's lastRound: tx invalid.
                            if (payslotUsed) {
                                halted = true
                                payslotUsed = false
                                payslotSats = 0n
                            } else if (n < 8n || treeOp != 1n) {
                                halted = true
                            } else if (second == 0n) {
                                halted = true
                            } else {
                                assert(
                                    top > memberLastRound,
                                    'round must be above lastRound'
                                )
                                payslotUsed = true
                                payslotSats = second
                                payslotAddr = Addr(slice(leafPre, 32n, 52n))
                                // The new leaf hash (lastRound := ROUND) is
                                // computed after the loop.
                                leafChanged = true
                                memberLastRound = top
                                ds = ds2
                            }
                        } else if (op == 40n || op == 41n) {
                            // ADMIT (0x28) : TAG ROUND --
                            // REMOVE (0x29) : TAG --
                            // Underflow, a second tree instruction or a
                            // second signature this cycle: fault.
                            // The leaf, proof, keys, payout and signature
                            // are checked after the loop (tx invalid when
                            // wrong). treeOp becomes 2 (ADMIT) or 3 (REMOVE).
                            const need: bigint = op == 40n ? 8n : 4n
                            if (n < need || treeOp != 0n || sigUsed) {
                                halted = true
                            } else {
                                sigUsed = true
                                treeOp = op - 38n
                                treeArgs = slice(ds, n - need, n)
                                ds = slice(ds, 0n, n - need)
                            }
                        } else if (op == 42n) {
                            // OUTH : N1 --   logHash := sha256(logHash || cell(N1))
                            // Underflow: fault. No capacity limit.
                            if (n < 4n) {
                                halted = true
                            } else {
                                logHash = sha256(logHash + K17Machine.cell(top))
                                ds = ds1
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

        // ---- the cycle's one roster-tree proof -----------------------
        // Checked whenever a tree instruction ran, halted or not: the VM
        // refuses a bad proof at the instruction, before any later fault.
        // rosterSeq is written to the next state only on the alive path.
        let rosterSeq = this.rosterSeq
        if (treeOp != 0n) {
            assert(
                leafIndex >= 0n && leafIndex < K17Machine.TREE_LEAVES,
                'leaf index out of range'
            )
            assert(
                len(proof) == K17Machine.PROOF_BYTES,
                'proof must be 512 bytes'
            )
            const oldLeafHash =
                len(leafPre) == 0n
                    ? K17Machine.EMPTY_HASH
                    : sha256(K17Machine.LEAF_DOMAIN + leafPre)
            assert(
                K17Machine.treeRoot(oldLeafHash, proof, leafIndex) ==
                    this.rosterRoot,
                'proof does not match rosterRoot'
            )
            if (memberKeyCheck) {
                // ATTESTM: the signing key is the bound member's key.
                assert(
                    sha256(keyA) == slice(leafPre, 0n, 32n),
                    'key is not the member key'
                )
            }
            // New leaf hash when the leaf changes; REMOVE keeps the empty
            // leaf hash.
            let newLeafHash = K17Machine.EMPTY_HASH
            if (treeOp == 1n) {
                // PAYLEAF: the leaf keeps keyHash, payout and flags;
                // lastRound becomes ROUND (memberLastRound after PAYLEAF).
                // Unused when leafChanged is false.
                newLeafHash = sha256(
                    K17Machine.LEAF_DOMAIN +
                        slice(leafPre, 0n, 52n) +
                        K17Machine.cell(memberLastRound) +
                        slice(leafPre, 56n, 60n)
                )
            } else {
                // ADMIT or REMOVE: the signer is the sponsor. The hash
                // check pins keyA, so no length check is needed.
                assert(
                    sha256(keyA) == this.sponsorKeyHash,
                    'key is not the sponsor key'
                )
                // "K17D" or "K17X" || instanceId || cell(TAG) ||
                // cell(rosterSeq) || cell(leafIndex) || (the rest below)
                const msgHead =
                    this.instanceId +
                    slice(treeArgs, 0n, 4n) +
                    K17Machine.cell(this.rosterSeq) +
                    K17Machine.cell(leafIndex)
                if (treeOp == 2n) {
                    // ADMIT: the leaf must be empty (the old-root check
                    // above used the empty leaf hash for it).
                    assert(len(leafPre) == 0n, 'leaf must be empty')
                    assert(
                        len(payout) == K17Machine.PAYOUT_BYTES,
                        'payout must be 20 bytes'
                    )
                    assert(
                        len(keyB) == K17Machine.KEY_BYTES,
                        'new key must be 384 bytes'
                    )
                    const newKeyHash = sha256(keyB)
                    // ... || sha256(keyB) || payout
                    verifyMsg =
                        K17Machine.ADMIT_DOMAIN + msgHead + newKeyHash + payout
                    // New leaf: keyHash || payout || cell(ROUND) || cell(0)
                    newLeafHash = sha256(
                        K17Machine.LEAF_DOMAIN +
                            newKeyHash +
                            payout +
                            slice(treeArgs, 4n, 8n) +
                            K17Machine.cell(0n)
                    )
                } else {
                    // REMOVE: the leaf must be occupied.
                    assert(
                        len(leafPre) == K17Machine.LEAF_PRE_BYTES,
                        'leaf preimage must be 60 bytes'
                    )
                    // ... || keyHash32 || payout20, the first 52 bytes of
                    // leafPre (v3.1). PAYLEAF never changes them, so a
                    // removal signed before a payment still verifies.
                    verifyMsg =
                        K17Machine.REMOVE_DOMAIN +
                        msgHead +
                        slice(leafPre, 0n, 52n)
                }
                verifyNeeded = true
                verifyKey = Utils.fromLEUnsigned(keyA)
                leafChanged = true
                rosterSeq = this.rosterSeq + 1n
            }
            if (leafChanged) {
                this.rosterRoot = K17Machine.treeRoot(
                    newLeafHash,
                    proof,
                    leafIndex
                )
            }
        }

        // ---- the cycle's one signature --------------------------------
        // After the tree block, which builds the ADMIT and REMOVE message.
        if (verifyNeeded) {
            assert(
                RabinVerifier.verifySig(verifyMsg, sig, verifyKey),
                'signature check failed'
            )
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
            // A cycle that keeps the machine alive must advance the clock by
            // MIN_STEP seconds (v3.1). The halted branch above is exempt.
            assert(
                now >= this.lastTime + K17Machine.MIN_STEP,
                'a live cycle must advance the clock by MIN_STEP'
            )
            this.pc = pc
            this.ds = ds
            this.rs = rs
            this.mem = mem
            this.outLog = outLog
            this.lastTime = now
            this.logHash = logHash
            this.rosterSeq = rosterSeq
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
