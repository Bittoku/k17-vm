/**
 * Tests for the off-chain K17 reference VM and assembler.
 * These run without the sCrypt compiler and pin down the ISA semantics that
 * the on-chain interpreter must reproduce.
 */
import { expect } from 'chai'
import { createHash } from 'crypto'
import {
    assemble,
    disassemble,
    encodeCell,
    decodeCell,
    Op,
    DS_MAX,
    CELL_MOD,
    HAS_OPERAND,
    MEM_CELLS,
    OUT_MAX,
    ROSTER_BASE,
    ROSTER_SLOTS,
    SLOT_CELLS,
    slotCells,
    slotOffset,
} from '../src/k17/isa'
import {
    initialState,
    run,
    step,
    stepK,
    outputLog,
    envOf,
    StepEnv,
    TreeOp,
    BoundMember,
    hashCell,
    readSlot,
    withSlot,
    K17State,
    deadManDue,
} from '../src/k17/vm'
import {
    EMPTY_HASHES,
    SparseMerkleTree,
    decodeLeafPre,
    encodeLeafPre,
} from '../src/k17/smt'
import {
    countdownProgram,
    fibonacciProgram,
    heartbeatProgram,
    attestProgram,
} from '../src/k17/programs'
import {
    newAttester,
    signReading,
    signReadingFor,
    KEY_BYTES,
    pubKeyBytes,
    pubKeyFromBytes,
    keyHash,
    endorseMessage,
    signEndorsement,
    payoutOf,
    signMemberReading,
    signAdmission,
    signRemoval,
} from '../src/k17/attest'
import { RabinSig, RabinVerifier } from 'scrypt-ts-lib'
import { bsv, toByteString, Utils } from 'scrypt-ts'

/** Instance id used by the ATTEST and ENDORSE tests (any 32 bytes). */
const ID = 'cd'.repeat(32)
/** A second instance id, for replay tests. */
const OTHER_ID = 'ef'.repeat(32)

describe('K17 ISA encoding', () => {
    it('round-trips cells', () => {
        for (const v of [0n, 1n, 255n, 256n, 0xdeadbeefn, CELL_MOD - 1n]) {
            expect(decodeCell(encodeCell(v))).to.equal(v)
        }
        expect(encodeCell(1n)).to.equal('01000000')
    })

    it('assembles labels into byte offsets', () => {
        const hex = assemble(['LIT', 7, 'top:', 'DUP', 'IF', 'top', 'HALT'])
        // LIT(1+4) DUP(1) IF(1+4) HALT(1) = 12 bytes; 'top' = offset 5
        expect(hex.length / 2).to.equal(12)
        expect(hex.slice(0, 2)).to.equal(Op.LIT.toString(16).padStart(2, '0'))
        expect(disassemble(hex)).to.equal('0: LIT 7\n5: DUP\n6: IF 5\n11: HALT')
    })

    it('roster layout: slot cells and offsets', () => {
        expect(ROSTER_BASE + ROSTER_SLOTS * SLOT_CELLS).to.equal(MEM_CELLS)
        expect(slotOffset(0)).to.equal(152)
        expect(slotOffset(7)).to.equal(243)
        const cells = slotCells('00'.repeat(31) + '01', 'ab'.repeat(20))
        expect(cells.length).to.equal(13)
        expect(cells[7]).to.equal(0x01000000n) // last 4 hash bytes, little-endian
        expect(cells[8]).to.equal(0xababababn)
    })

    it('new opcodes have no operand and assemble', () => {
        for (const op of [Op.ATTEST, Op.ENDORSE, Op.PAYSLOT, Op.VALUE]) {
            expect(HAS_OPERAND.has(op)).to.be.false
        }
        expect(assemble(['VALUE', 'ATTEST', 'ENDORSE', 'PAYSLOT'])).to.equal(
            '23202122'
        )
    })
})

describe('K17 v3 tree opcodes and state', function () {
    const NEW_OPS = [
        Op.MEMBER,
        Op.LASTROUND,
        Op.ATTESTM,
        Op.PAYLEAF,
        Op.ADMIT,
        Op.REMOVE,
        Op.OUTH,
    ]
    const NEW_MNEMONICS = [
        'MEMBER',
        'LASTROUND',
        'ATTESTM',
        'PAYLEAF',
        'ADMIT',
        'REMOVE',
        'OUTH',
    ]

    it('seven new opcodes have no operand and assemble to 24..2a', () => {
        for (const op of NEW_OPS) expect(HAS_OPERAND.has(op)).to.be.false
        expect(assemble(NEW_MNEMONICS)).to.equal('2425262728292a')
    })

    it('initialState has the v3 defaults', () => {
        const s = initialState(assemble(['HALT']))
        expect(s.rosterRoot).to.equal(EMPTY_HASHES[16])
        expect(s.rosterSeq).to.equal(0n)
        expect(s.logHash).to.equal('00'.repeat(32))
        expect(s.sponsorKeyHash).to.equal('00'.repeat(32))
    })

    it('initialState accepts options and validates them', () => {
        const root = 'ab'.repeat(32)
        const sponsor = 'cd'.repeat(32)
        const s = initialState(assemble(['HALT']), undefined, {
            rosterRoot: root,
            sponsorKeyHash: sponsor,
        })
        expect(s.rosterRoot).to.equal(root)
        expect(s.sponsorKeyHash).to.equal(sponsor)
        expect(() =>
            initialState(assemble(['HALT']), undefined, { rosterRoot: 'ab' })
        ).to.throw()
        expect(() =>
            initialState(assemble(['HALT']), undefined, {
                sponsorKeyHash: 'AB'.repeat(32),
            })
        ).to.throw()
    })

    it('treeOp starts as none in step and stepK', () => {
        const s = initialState(assemble(['HALT']))
        expect(step(s, 0n).treeOp).to.equal('none')
        expect(stepK(s, 0n, 4).treeOp).to.equal('none')
    })
})

describe('K17 reference VM', () => {
    it('runs Fibonacci and halts', () => {
        const { state, steps } = run(
            initialState(fibonacciProgram(10)),
            1_700_000_000n
        )
        expect(state.halted).to.be.true
        expect(outputLog(state)).to.deep.equal([
            0n,
            1n,
            1n,
            2n,
            3n,
            5n,
            8n,
            13n,
            21n,
            34n,
        ])
        expect(state.ds).to.equal('')
        expect(steps).to.be.greaterThan(100)
    })

    it('runs a subroutine countdown', () => {
        const { state } = run(initialState(countdownProgram(5)), 0n)
        expect(outputLog(state)).to.deep.equal([5n, 4n, 3n, 2n, 1n])
        expect(state.rs).to.equal('')
    })

    it('TIME pushes the lock time and the heartbeat faults when the log fills', () => {
        const { state } = run(
            initialState(heartbeatProgram()),
            1_700_000_123n,
            10_000
        )
        expect(state.halted).to.be.true
        const log = outputLog(state)
        expect(log.length).to.equal(OUT_MAX)
        expect(log[0]).to.equal(1_700_000_123n)
    })

    it('wraps arithmetic modulo 2^32', () => {
        const { state } = run(
            initialState(assemble(['LIT', 0, 'LIT', 1, '-', 'OUT', 'HALT'])),
            0n
        )
        expect(outputLog(state)).to.deep.equal([CELL_MOD - 1n])
    })

    it('faults on stack underflow without throwing and leaves state intact', () => {
        const s0 = initialState(assemble(['DROP', 'HALT']))
        const r = step(s0, 0n)
        expect(r.faulted).to.be.true
        expect(r.state.halted).to.be.true
        expect(r.state.pc).to.equal(0n)
    })

    it('faults on data stack overflow', () => {
        const tokens: (string | number)[] = []
        for (let i = 0; i <= DS_MAX; i++) tokens.push('LIT', i)
        tokens.push('HALT')
        const { state } = run(initialState(assemble(tokens)), 0n)
        expect(state.halted).to.be.true
        expect(state.ds.length / 8).to.equal(DS_MAX)
    })

    it('faults on bad memory address and unknown opcode', () => {
        expect(
            step(initialState(assemble(['LIT', 64, '@', 'HALT'])), 0n).state
                .halted
        ).to.be.false
        const bad = run(
            initialState(assemble(['LIT', 64, '@', 'HALT'])),
            0n
        ).state
        expect(bad.halted).to.be.true
        expect(bad.out).to.equal('')
        expect(step(initialState('ff'), 0n).faulted).to.be.true
        expect(step(initialState(''), 0n).faulted).to.be.true
    })

    it('IN blocks without a witness, VERIFY rejects zero, BOUNTY accumulates', () => {
        const prog = assemble([
            'IN',
            'DUP',
            'VERIFY',
            'BOUNTY',
            500,
            'OUT',
            'HALT',
        ])
        expect(run(initialState(prog), envOf(0n)).status).to.equal(
            'need_witness'
        )
        expect(run(initialState(prog), envOf(0n, 0n, [0n])).status).to.equal(
            'verify_failed'
        )
        const ok = run(initialState(prog), envOf(0n, 0n, [7n]))
        expect(ok.status).to.equal('halted')
        expect(ok.bountyDue).to.equal(500n)
        expect(outputLog(ok.state)).to.deep.equal([7n])
    })

    it('YIELD ends a cycle early but is not a halt', () => {
        const prog = assemble([
            'LIT',
            1,
            'OUT',
            'YIELD',
            'LIT',
            2,
            'OUT',
            'HALT',
        ])
        const c1 = stepK(initialState(prog), 0n, 40)
        expect(c1.status).to.equal('ok')
        expect(c1.state.halted).to.be.false
        expect(outputLog(c1.state)).to.deep.equal([1n])
        const c2 = stepK(c1.state, 0n, 40)
        expect(c2.status).to.equal('halted')
        expect(outputLog(c2.state)).to.deep.equal([1n, 2n])
    })

    it('MUL wraps, HASH matches sha256 prefix, WHO reads the env', () => {
        const prog = assemble([
            'LIT',
            65536,
            'LIT',
            65536,
            '*',
            'OUT',
            'LIT',
            1,
            'HASH',
            'OUT',
            'WHO',
            'OUT',
            'HALT',
        ])
        const r = run(initialState(prog), envOf(0n, 0xdeadbeefn))
        expect(outputLog(r.state)).to.deep.equal([
            0n,
            hashCell(1n),
            0xdeadbeefn,
        ])
        const digest = createHash('sha256')
            .update(Buffer.from('01000000', 'hex'))
            .digest()
        expect(hashCell(1n)).to.equal(BigInt(digest.readUInt32LE(0)))
    })

    it('stepK stops at halt', () => {
        const s = stepK(
            initialState(assemble(['LIT', 1, 'OUT', 'HALT', 'LIT', 2, 'OUT'])),
            0n,
            10
        )
        expect(s.state.halted).to.be.true
        expect(outputLog(s.state)).to.deep.equal([1n])
    })

    // ---- K17+ ------------------------------------------------------------

    it('MIN and MAX pick the smaller and larger unsigned cell', () => {
        // prettier-ignore
        const prog = assemble([
            'LIT', 7, 'LIT', 3, 'MIN', 'OUT',
            'LIT', 7, 'LIT', 3, 'MAX', 'OUT',
            'LIT', 0xffffffff, 'LIT', 1, 'MAX', 'OUT',
            'HALT',
        ])
        const r = run(initialState(prog), 0n)
        expect(outputLog(r.state)).to.deep.equal([3n, 7n, 0xffffffffn])
    })

    it('DIV floors unsigned quotients and faults on a zero divisor', () => {
        const ok = run(
            initialState(assemble(['LIT', 17, 'LIT', 5, '/', 'OUT', 'HALT'])),
            0n
        )
        expect(outputLog(ok.state)).to.deep.equal([3n])
        const bad = run(
            initialState(
                assemble([
                    'LIT',
                    1,
                    'OUT',
                    'LIT',
                    17,
                    'LIT',
                    0,
                    '/',
                    'OUT',
                    'HALT',
                ])
            ),
            0n
        )
        expect(bad.status).to.equal('halted')
        expect(outputLog(bad.state)).to.deep.equal([1n])
    })

    it('SIGVERIFY accepts a roster signature, rejects a wrong one, blocks without one, faults on a bad slot', function () {
        this.timeout(120_000) // two 3072-bit Rabin key generations
        const a = newAttester(Buffer.alloc(32, 7))
        const b = newAttester(Buffer.alloc(32, 8))
        const roster = [a.pub, b.pub, 0n, 0n]
        const prog = attestProgram(1)
        const base = { lockTime: 0n, who: 0n, witness: [5n, 2231n], roster }

        const ok = run(initialState(prog), {
            ...base,
            sig: signReading(b, 5n, 2231n),
        })
        expect(ok.status).to.equal('halted')
        expect(outputLog(ok.state)).to.deep.equal([5n, 2231n])

        const wrongKey = run(initialState(prog), {
            ...base,
            sig: signReading(a, 5n, 2231n),
        })
        expect(wrongKey.status).to.equal('verify_failed')

        const replay = run(initialState(prog), {
            ...base,
            witness: [6n, 2231n],
            sig: signReading(b, 5n, 2231n),
        })
        expect(replay.status).to.equal('verify_failed')

        const missing = run(initialState(prog), base)
        expect(missing.status).to.equal('need_witness')

        const emptySlot = run(initialState(attestProgram(2)), {
            ...base,
            sig: signReading(b, 5n, 2231n),
        })
        expect(emptySlot.status).to.equal('halted')
        expect(outputLog(emptySlot.state)).to.deep.equal([])
    })

    it('a second SIGVERIFY in one cycle is a fault (v3.1)', function () {
        this.timeout(120_000)
        const b = newAttester(Buffer.alloc(32, 9))
        // prettier-ignore
        const prog = assemble([
            'IN', 'IN', 'OVER', 'OVER', 'OVER', 'OVER',
            'SIGVERIFY', 0, 'SIGVERIFY', 0, 'HALT',
        ])
        const r = run(initialState(prog), {
            lockTime: 0n,
            who: 0n,
            witness: [1n, 2n],
            roster: [b.pub, 0n, 0n, 0n],
            sig: signReading(b, 1n, 2n),
        })
        // The first SIGVERIFY verified; the second one faults, so the
        // machine halts (refund) with its operands still on the stack.
        expect(r.status).to.equal('halted')
        expect(r.state.halted).to.equal(true)
        expect(r.state.pc).to.equal(11n)
        expect(r.state.ds).to.equal(
            encodeCell(1n) + encodeCell(2n) + encodeCell(1n) + encodeCell(2n)
        )
    })
})

describe('K17 VALUE, PAYSLOT and roster write-protection', function () {
    const keyHash = 'ab'.repeat(32)
    const payout = '12'.repeat(20)
    /** State with roster slot 2 filled and the given program loaded. */
    const withSlot2 = (prog: string) => {
        const s = initialState(prog)
        return { ...s, mem: withSlot(s.mem, 2, slotCells(keyHash, payout)) }
    }

    it('VALUE pushes the balance', () => {
        const prog = assemble(['VALUE', 'OUT', 'HALT'])
        const r = run(initialState(prog), { ...envOf(0n), value: 123456n })
        expect(r.status).to.equal('halted')
        expect(outputLog(r.state)).to.deep.equal([123456n])
        // default balance is zero; larger balances wrap modulo 2^32
        const d = run(initialState(prog), envOf(0n))
        expect(outputLog(d.state)).to.deep.equal([0n])
        const w = run(initialState(prog), {
            ...envOf(0n),
            value: CELL_MOD + 7n,
        })
        expect(outputLog(w.state)).to.deep.equal([7n])
    })

    it('VALUE faults on data-stack overflow', () => {
        const prog = assemble(['LIT', 1, 'VALUE', 'HALT'])
        let s = initialState(prog)
        s = { ...s, ds: encodeCell(0n).repeat(DS_MAX - 1) }
        const ok = step(step(s, envOf(0n)).state, envOf(0n))
        expect(ok.status).to.equal('fault')
    })

    it('PAYSLOT records slot payout', () => {
        const prog = assemble(['LIT', 5000, 'LIT', 2, 'PAYSLOT', 'HALT'])
        const r = stepK(withSlot2(prog), envOf(0n), 10)
        expect(r.status).to.equal('halted')
        expect(r.payslot).to.deep.equal({
            slot: 2,
            payoutHex: payout,
            sats: 5000n,
        })
        expect(r.state.ds).to.equal('')
        const slot = readSlot(r.state.mem, 2)
        expect(slot).to.deep.equal({
            hashHex: keyHash,
            payoutHex: payout,
            empty: false,
        })
        expect(readSlot(r.state.mem, 3).empty).to.equal(true)
    })

    it('PAYSLOT on an empty slot faults', () => {
        const prog = assemble(['LIT', 5000, 'LIT', 3, 'PAYSLOT', 'HALT'])
        const r = stepK(withSlot2(prog), envOf(0n), 10)
        expect(r.status).to.equal('halted')
        expect(r.payslot).to.equal(undefined)
        expect(r.state.halted).to.equal(true)
        expect(r.state.pc).to.equal(10n) // stopped at the PAYSLOT
    })

    it('PAYSLOT faults on underflow and on a slot out of range', () => {
        const under = step(
            withSlot2(assemble(['LIT', 1, 'PAYSLOT'])),
            envOf(0n)
        )
        expect(step(under.state, envOf(0n)).status).to.equal('fault')
        const prog = assemble(['LIT', 1, 'LIT', ROSTER_SLOTS, 'PAYSLOT'])
        const r = stepK(withSlot2(prog), envOf(0n), 3)
        expect(r.status).to.equal('halted')
        expect(r.payslot).to.equal(undefined)
    })

    it('a second PAYSLOT in one cycle faults and drops the payout', () => {
        // prettier-ignore
        const prog = assemble([
            'LIT', 1, 'LIT', 2, 'PAYSLOT', 'LIT', 1, 'LIT', 2, 'PAYSLOT', 'HALT',
        ])
        const r = stepK(withSlot2(prog), envOf(0n), 10)
        expect(r.status).to.equal('halted')
        expect(r.state.halted).to.equal(true)
        expect(r.payslot).to.equal(undefined)
        expect(r.state.pc).to.equal(21n) // stopped at the second PAYSLOT
        const full = run(withSlot2(prog), envOf(0n))
        expect(full.status).to.equal('halted')
        expect(full.payslot).to.equal(undefined)
    })

    it('a second PAYSLOT drops the payout even when it is malformed', () => {
        // the second PAYSLOT underflows: still a payout-dropping fault
        // prettier-ignore
        const prog = assemble([
            'LIT', 1, 'LIT', 2, 'PAYSLOT', 'PAYSLOT', 'HALT',
        ])
        const r = stepK(withSlot2(prog), envOf(0n), 10)
        expect(r.status).to.equal('halted')
        expect(r.payslot).to.equal(undefined)
        expect(r.state.pc).to.equal(11n)
    })

    it('PAYSLOT then an unrelated fault keeps the payout', () => {
        // prettier-ignore
        const prog = assemble([
            'LIT', 700, 'LIT', 2, 'PAYSLOT', 'DROP', 'DROP', 'DROP', 'YIELD',
        ])
        const r = stepK(withSlot2(prog), envOf(0n), 10)
        expect(r.status).to.equal('halted')
        expect(r.state.pc).to.equal(11n) // faulted at the first DROP
        expect(r.payslot).to.deep.equal({
            slot: 2,
            payoutHex: payout,
            sats: 700n,
        })
    })

    it('PAYSLOT 0 faults', () => {
        const prog = assemble(['LIT', 0, 'LIT', 2, 'PAYSLOT', 'HALT'])
        const r = stepK(withSlot2(prog), envOf(0n), 10)
        expect(r.status).to.equal('halted')
        expect(r.state.halted).to.equal(true)
        expect(r.payslot).to.equal(undefined)
        expect(r.state.pc).to.equal(10n) // stopped at the PAYSLOT
    })

    it('STORE into the roster region faults', () => {
        const bad = run(
            initialState(assemble(['LIT', 9, 'LIT', ROSTER_BASE, '!', 'HALT'])),
            envOf(0n)
        )
        expect(bad.status).to.equal('halted')
        expect(bad.state.mem).to.equal(initialState('').mem)
        const good = run(
            initialState(
                assemble(['LIT', 9, 'LIT', ROSTER_BASE - 1, '!', 'HALT'])
            ),
            envOf(0n)
        )
        expect(
            good.state.mem.slice((ROSTER_BASE - 1) * 8, ROSTER_BASE * 8)
        ).to.equal(encodeCell(9n))
    })

    it('initialState validates the memory image', () => {
        expect(() => initialState('', '00')).to.throw()
        expect(initialState('', '11'.repeat(MEM_CELLS * 4)).mem).to.have.length(
            MEM_CELLS * 8
        )
        // an uppercase image is stored lowercase, so roster slots compare
        // the same way as on chain
        const upper = withSlot(
            initialState('').mem,
            2,
            slotCells('ab'.repeat(32), '12'.repeat(20))
        ).toUpperCase()
        const st = initialState('', upper)
        expect(st.mem).to.equal(upper.toLowerCase())
        expect(readSlot(st.mem, 2).hashHex).to.equal('ab'.repeat(32))
    })
})

describe('K17 roster key encoding and endorsement', function () {
    this.timeout(120_000)

    it('encodes keys, hashes them and signs endorsements', function () {
        const endorser = newAttester(Buffer.alloc(32, 1))
        const successor = newAttester(Buffer.alloc(32, 2))
        const hex = pubKeyBytes(endorser.pub)
        expect(KEY_BYTES).to.equal(384)
        expect(hex.length).to.equal(768)
        expect(pubKeyFromBytes(hex)).to.equal(endorser.pub)
        expect(keyHash(endorser.pub)).to.equal(
            createHash('sha256').update(Buffer.from(hex, 'hex')).digest('hex')
        )

        const payout = payoutOf(bsv.PrivateKey.fromRandom().toAddress())
        expect(payout.length).to.equal(40)
        const other = '11'.repeat(20)
        const message = endorseMessage(ID, 5n, successor.pub, payout, 3n)
        expect(message).to.equal(
            '4b313745' +
                ID +
                encodeCell(5n) +
                encodeCell(3n) +
                keyHash(successor.pub) +
                payout
        )
        const sig = signEndorsement(endorser, ID, 5n, successor.pub, payout, 3n)
        expect(
            RabinVerifier.verifySig(toByteString(message), sig, endorser.pub)
        ).to.equal(true)
        expect(
            RabinVerifier.verifySig(
                toByteString(endorseMessage(ID, 5n, successor.pub, other, 3n)),
                sig,
                endorser.pub
            )
        ).to.equal(false)
        // the target slot is bound: the same endorsement for slot 4 fails
        expect(
            RabinVerifier.verifySig(
                toByteString(endorseMessage(ID, 5n, successor.pub, payout, 4n)),
                sig,
                endorser.pub
            )
        ).to.equal(false)
    })
})

describe('K17 ATTEST against a roster slot', function () {
    this.timeout(120_000)
    const attester = newAttester(Buffer.alloc(32, 21))
    const stranger = newAttester(Buffer.alloc(32, 22))
    const payout = 'ab'.repeat(20)
    const prog = assemble(['LIT', 5, 'LIT', 2231, 'LIT', 1, 'ATTEST', 'HALT'])
    /** Single-step until an instruction does not return 'ok'; returns that StepResult. */
    const stepUntilStop = (
        start: ReturnType<typeof initialState>,
        env: StepEnv
    ) => {
        let cur = start
        for (;;) {
            const r = step(cur, env)
            if (r.status !== 'ok') return r
            cur = r.state
        }
    }
    const installed = () => {
        const s = initialState(prog)
        return {
            ...s,
            mem: withSlot(s.mem, 1, slotCells(keyHash(attester.pub), payout)),
        }
    }

    it('encodes keys as the contract will read them', function () {
        expect(
            Utils.fromLEUnsigned(toByteString(pubKeyBytes(attester.pub)))
        ).to.equal(attester.pub)
    })

    it('accepts the slot key signing the reading and pops the three cells', function () {
        const r = run(installed(), {
            ...envOf(0n),
            sig: signReadingFor(attester, ID, 5n, 2231n),
            attestKey: attester.pub,
            instanceId: ID,
        })
        expect(r.status).to.equal('halted')
        expect(r.state.ds).to.equal('')
    })

    it('rejects a key whose hash is not the slot hash', function () {
        const r = run(installed(), {
            ...envOf(0n),
            sig: signReadingFor(stranger, ID, 5n, 2231n),
            attestKey: stranger.pub,
            instanceId: ID,
        })
        expect(r.status).to.equal('verify_failed')
    })

    it('rejects a signature over a different value', function () {
        const r = run(installed(), {
            ...envOf(0n),
            sig: signReadingFor(attester, ID, 5n, 2232n),
            attestKey: attester.pub,
            instanceId: ID,
        })
        expect(r.status).to.equal('verify_failed')
    })

    it('faults on an empty slot and on a slot beyond the roster', function () {
        const env = {
            ...envOf(0n),
            sig: signReadingFor(attester, ID, 5n, 2231n),
            attestKey: attester.pub,
            instanceId: ID,
        }
        expect(stepUntilStop(initialState(prog), env).faulted).to.equal(true)
        const high = assemble(['LIT', 5, 'LIT', 2231, 'LIT', 8, 'ATTEST'])
        expect(stepUntilStop(initialState(high), env).faulted).to.equal(true)
        const shallow = assemble(['LIT', 2231, 'LIT', 1, 'ATTEST'])
        expect(stepUntilStop(initialState(shallow), env).faulted).to.equal(true)
    })

    it('needs a witness without a signature or a key; a second ATTEST faults', function () {
        const sig = signReadingFor(attester, ID, 5n, 2231n)
        expect(
            run(installed(), {
                ...envOf(0n),
                attestKey: attester.pub,
                instanceId: ID,
            }).status
        ).to.equal('need_witness')
        expect(
            run(installed(), { ...envOf(0n), sig, instanceId: ID }).status
        ).to.equal('need_witness')
        // no instance id: the message cannot be formed
        expect(
            run(installed(), { ...envOf(0n), sig, attestKey: attester.pub })
                .status
        ).to.equal('need_witness')
        const twice = assemble([
            'LIT',
            5,
            'LIT',
            2231,
            'LIT',
            1,
            'ATTEST',
            'LIT',
            5,
            'LIT',
            2231,
            'LIT',
            1,
            'ATTEST',
            'HALT',
        ])
        const s = initialState(twice)
        const r = run(
            { ...s, mem: installed().mem },
            { ...envOf(0n), sig, attestKey: attester.pub, instanceId: ID }
        )
        // v3.1: the second ATTEST is a fault, not a missing witness.
        expect(r.status).to.equal('halted')
        expect(r.state.halted).to.equal(true)
        expect(r.state.pc).to.equal(31n)
    })

    it('refuses a reading signed for another instance', function () {
        const r = run(installed(), {
            ...envOf(0n),
            sig: signReadingFor(attester, ID, 5n, 2231n),
            attestKey: attester.pub,
            instanceId: OTHER_ID,
        })
        expect(r.status).to.equal('verify_failed')
        // a SIGVERIFY-style ("K17A") signature is not accepted either
        const k17a = run(installed(), {
            ...envOf(0n),
            sig: signReading(attester, 5n, 2231n),
            attestKey: attester.pub,
            instanceId: ID,
        })
        expect(k17a.status).to.equal('verify_failed')
    })
})

describe('K17 ENDORSE writes a new roster slot', function () {
    this.timeout(120_000)
    const sponsor = newAttester(Buffer.alloc(32, 31))
    const newcomer = newAttester(Buffer.alloc(32, 32))
    const stranger = newAttester(Buffer.alloc(32, 33))
    const payout = payoutOf(bsv.PrivateKey.fromRandom().toAddress())
    const tagE = 77n
    const endorseProg = assemble([
        'LIT',
        Number(tagE),
        'LIT',
        0,
        'LIT',
        1,
        'ENDORSE',
        'HALT',
    ])
    /** State with the sponsor installed in slot 0. */
    const withSponsor = (prog: string) => {
        const s = initialState(prog)
        return {
            ...s,
            mem: withSlot(s.mem, 0, slotCells(keyHash(sponsor.pub), payout)),
        }
    }
    /** Environment carrying a valid sponsor endorsement of the newcomer. */
    const goodEnv = (): StepEnv => ({
        ...envOf(0n),
        instanceId: ID,
        sig: signEndorsement(sponsor, ID, tagE, newcomer.pub, payout, 1n),
        attestKey: sponsor.pub,
        endorseKey: newcomer.pub,
        payout,
    })
    /** Single-step until an instruction does not return 'ok'. */
    const stepUntilStop = (
        start: ReturnType<typeof initialState>,
        env: StepEnv
    ) => {
        let cur = start
        for (;;) {
            const r = step(cur, env)
            if (r.status !== 'ok') return r
            cur = r.state
        }
    }

    it('writes the newcomer into the named slot and pops three cells', function () {
        const r = run(withSponsor(endorseProg), goodEnv())
        expect(r.status).to.equal('halted')
        expect(r.state.ds).to.equal('')
        expect(readSlot(r.state.mem, 1)).to.deep.equal({
            hashHex: keyHash(newcomer.pub),
            payoutHex: payout,
            empty: false,
        })
    })

    it('lets the newcomer attest in the next cycle', function () {
        const prog = assemble([
            'LIT',
            Number(tagE),
            'LIT',
            0,
            'LIT',
            1,
            'ENDORSE',
            'YIELD',
            'LIT',
            9,
            'IN',
            'LIT',
            1,
            'ATTEST',
            'HALT',
        ])
        const c1 = stepK(withSponsor(prog), goodEnv(), 8)
        expect(c1.status).to.equal('ok')
        const c2 = stepK(
            c1.state,
            {
                ...envOf(0n, 0n, [123n]),
                sig: signReadingFor(newcomer, ID, 9n, 123n),
                attestKey: newcomer.pub,
                instanceId: ID,
            },
            8
        )
        expect(c2.status).to.equal('halted')
        expect(c2.state.ds).to.equal('')
    })

    it('ENDORSE after ATTEST in one cycle faults (v3.1)', function () {
        const prog = assemble([
            'LIT',
            5,
            'LIT',
            2231,
            'LIT',
            0,
            'ATTEST',
            'LIT',
            Number(tagE),
            'LIT',
            0,
            'LIT',
            1,
            'ENDORSE',
            'HALT',
        ])
        const r = stepK(
            withSponsor(prog),
            {
                ...goodEnv(),
                sig: signReadingFor(sponsor, ID, 5n, 2231n),
            },
            16
        )
        // ATTEST used the cycle's signature; ENDORSE (pc 31) faults with
        // its three operands on the stack and slot 1 left empty.
        expect(r.status).to.equal('halted')
        expect(r.state.halted).to.equal(true)
        expect(r.state.pc).to.equal(31n)
        expect(r.state.ds).to.equal(
            encodeCell(tagE) + encodeCell(0n) + encodeCell(1n)
        )
        expect(readSlot(r.state.mem, 1).empty).to.equal(true)
    })

    it('rejects a payout that is not 40 hex characters', function () {
        const short = payout.slice(0, 38)
        const r = run(withSponsor(endorseProg), {
            ...goodEnv(),
            sig: signEndorsement(sponsor, ID, tagE, newcomer.pub, short, 1n),
            payout: short,
        })
        expect(r.status).to.equal('verify_failed')
    })

    it('rejects uppercase hex in the payout', function () {
        const upper = payout.toUpperCase()
        const r = run(withSponsor(endorseProg), {
            ...goodEnv(),
            sig: signEndorsement(sponsor, ID, tagE, newcomer.pub, upper, 1n),
            payout: upper,
        })
        expect(r.status).to.equal('verify_failed')
    })

    it('faults when NEWSLOT is filled, out of range, or SLOT is empty or low on stack', function () {
        const into0 = assemble([
            'LIT',
            Number(tagE),
            'LIT',
            0,
            'LIT',
            0,
            'ENDORSE',
        ])
        expect(stepUntilStop(withSponsor(into0), goodEnv()).faulted).to.equal(
            true
        )
        const into8 = assemble([
            'LIT',
            Number(tagE),
            'LIT',
            0,
            'LIT',
            8,
            'ENDORSE',
        ])
        expect(stepUntilStop(withSponsor(into8), goodEnv()).faulted).to.equal(
            true
        )
        const emptySponsor = assemble([
            'LIT',
            Number(tagE),
            'LIT',
            2,
            'LIT',
            1,
            'ENDORSE',
        ])
        expect(
            stepUntilStop(withSponsor(emptySponsor), goodEnv()).faulted
        ).to.equal(true)
        const shallow = assemble(['LIT', 0, 'LIT', 1, 'ENDORSE'])
        expect(stepUntilStop(withSponsor(shallow), goodEnv()).faulted).to.equal(
            true
        )
    })

    it('needs a witness when endorseKey is missing', function () {
        const env = goodEnv()
        delete env.endorseKey
        expect(run(withSponsor(endorseProg), env).status).to.equal(
            'need_witness'
        )
    })

    it('rejects a signer whose hash is not the one at SLOT', function () {
        const r = run(withSponsor(endorseProg), {
            ...goodEnv(),
            sig: signEndorsement(stranger, ID, tagE, newcomer.pub, payout, 1n),
            attestKey: stranger.pub,
        })
        expect(r.status).to.equal('verify_failed')
    })

    it('rejects a signature over a different tag', function () {
        const r = run(withSponsor(endorseProg), {
            ...goodEnv(),
            sig: signEndorsement(
                sponsor,
                ID,
                tagE + 1n,
                newcomer.pub,
                payout,
                1n
            ),
        })
        expect(r.status).to.equal('verify_failed')
    })

    it('rejects an endorsement signed for slot 1 presented with NEWSLOT 2', function () {
        const into2 = assemble([
            'LIT',
            Number(tagE),
            'LIT',
            0,
            'LIT',
            2,
            'ENDORSE',
            'HALT',
        ])
        const r = run(withSponsor(into2), goodEnv())
        expect(r.status).to.equal('verify_failed')
        expect(readSlot(r.state.mem, 2).empty).to.equal(true)
    })
})

/** Decode a data-stack hex string into cell values, bottom first. */
function outputOf(stackHex: string): bigint[] {
    const cells: bigint[] = []
    for (let i = 0; i < stackHex.length; i += 8) {
        cells.push(decodeCell(stackHex.slice(i, i + 8)))
    }
    return cells
}

describe('K17 v3 MEMBER, LASTROUND, OUTH', () => {
    const KEY_5 = '11'.repeat(32)
    const KEY_HIGH = '22'.repeat(32)
    const PAYOUT = '33'.repeat(20)
    const tree = new SparseMerkleTree()
    tree.set(5, encodeLeafPre(KEY_5, PAYOUT, 7n, 1n))
    tree.set(40000, encodeLeafPre(KEY_HIGH, PAYOUT, 99n))

    /** Fresh state for `mnemonics` whose rosterRoot is the test tree's root. */
    const machine = (mnemonics: (string | number)[]) =>
        initialState(assemble(mnemonics), undefined, {
            rosterRoot: tree.root(),
        })
    /** Environment carrying the proof for leaf `index`. */
    const envFor = (index: number): StepEnv => ({
        ...envOf(0n),
        tree: tree.proof(index),
    })

    it('MEMBER pushes the index and binds the member (index 5 and 40000)', () => {
        for (const [index, lastRound, key] of [
            [5, 7n, KEY_5],
            [40000, 99n, KEY_HIGH],
        ] as const) {
            const r = step(machine(['MEMBER', 'HALT']), envFor(index))
            expect(r.status).to.equal('ok')
            expect(outputOf(r.state.ds)).to.deep.equal([BigInt(index)])
            expect(r.treeOp).to.equal('member')
            expect(r.member?.lastRound).to.equal(lastRound)
            expect(r.member?.keyHash).to.equal(key)
            expect(r.member?.leafIndex).to.equal(BigInt(index))
        }
    })

    it('a flipped proof byte gives verify_failed with the state unchanged', () => {
        const s = machine(['MEMBER', 'HALT'])
        const good = tree.proof(5)
        const flipped =
            (good.proof[0] === '0' ? '1' : '0') + good.proof.slice(1)
        const r = step(s, { ...envOf(0n), tree: { ...good, proof: flipped } })
        expect(r.status).to.equal('verify_failed')
        expect(r.state).to.equal(s)
        expect(r.treeOp).to.equal('none')
        expect(r.member).to.equal(undefined)
    })

    it('an empty leaf is verify_failed even with a valid emptiness proof', () => {
        const r = step(machine(['MEMBER', 'HALT']), {
            ...envOf(0n),
            tree: tree.proof(6),
        })
        expect(tree.proof(6).leafPre).to.equal('')
        expect(r.status).to.equal('verify_failed')
    })

    it('an out-of-range index or truncated preimage is verify_failed', () => {
        const good = tree.proof(5)
        expect(
            step(machine(['MEMBER']), {
                ...envOf(0n),
                tree: { ...good, leafIndex: 65536n },
            }).status
        ).to.equal('verify_failed')
        expect(
            step(machine(['MEMBER']), {
                ...envOf(0n),
                tree: { ...good, leafPre: good.leafPre.slice(2) },
            }).status
        ).to.equal('verify_failed')
    })

    it('MEMBER without env.tree is need_witness', () => {
        expect(step(machine(['MEMBER']), envOf(0n)).status).to.equal(
            'need_witness'
        )
    })

    it('MEMBER MEMBER faults', () => {
        const r = stepK(machine(['MEMBER', 'MEMBER', 'HALT']), envFor(5), 2)
        expect(r.status).to.equal('halted')
        expect(r.state.halted).to.equal(true)
        expect(r.state.pc).to.equal(1n) // second MEMBER did not advance
    })

    it('LASTROUND without MEMBER faults', () => {
        const r = step(machine(['LASTROUND', 'HALT']), envFor(5))
        expect(r.status).to.equal('fault')
    })

    it('MEMBER DROP LASTROUND pushes lastRound, threaded through stepK and run', () => {
        const program = ['MEMBER', 'DROP', 'LASTROUND', 'HALT']
        const cycle = stepK(machine(program), envFor(5), 4)
        expect(outputOf(cycle.state.ds)).to.deep.equal([7n])
        expect(cycle.treeOp).to.equal('member')
        expect(cycle.member?.lastRound).to.equal(7n)
        const whole = run(machine(program), envFor(5))
        expect(outputOf(whole.state.ds)).to.deep.equal([7n])
        expect(whole.member?.lastRound).to.equal(7n)
    })

    it('OUTH twice matches an inline sha256 chain', () => {
        const r = run(machine(['LIT', 5, 'OUTH', 'LIT', 9, 'OUTH', 'HALT']), 0n)
        let expected = '00'.repeat(32)
        for (const n of [5n, 9n]) {
            expected = createHash('sha256')
                .update(Buffer.from(expected + encodeCell(n), 'hex'))
                .digest('hex')
        }
        expect(r.state.logHash).to.equal(expected)
        expect(r.state.out).to.equal('')
    })

    it('OUTH underflow faults', () => {
        expect(step(machine(['OUTH']), 0n).status).to.equal('fault')
    })

    it('OUTH still works after the output log is full; OUT then faults', () => {
        const fill = ['LIT', 1, 'OUT']
        const body: (string | number)[] = []
        for (let i = 0; i < OUT_MAX; i++) body.push(...fill)
        const s = machine([...body, 'LIT', 2, 'OUTH', 'LIT', 3, 'OUT', 'HALT'])
        const r = run(s, 0n, 10_000)
        // 256 OUTs filled the log; OUTH succeeded; the 257th OUT faulted.
        expect(r.state.logHash).to.not.equal('00'.repeat(32))
        expect(outputLog(r.state).length).to.equal(OUT_MAX)
        expect(r.state.halted).to.equal(true)
        expect(r.state.pc < BigInt(r.state.prog.length / 2)).to.equal(true)
    })
})

describe('K17 v3 ATTESTM and PAYLEAF', function () {
    this.timeout(120_000)
    const attester = newAttester(Buffer.alloc(32, 41))
    const stranger = newAttester(Buffer.alloc(32, 42))
    const PAYOUT = '44'.repeat(20)
    const OTHER_PAYOUT = '55'.repeat(20)
    const OTHER_KEY = '66'.repeat(32)
    const MEMBER_INDEX = 9
    const OTHER_INDEX = 300
    const LAST_ROUND = 7n
    const buildTree = (): SparseMerkleTree => {
        const t = new SparseMerkleTree()
        t.set(
            MEMBER_INDEX,
            encodeLeafPre(keyHash(attester.pub), PAYOUT, LAST_ROUND, 1n)
        )
        t.set(OTHER_INDEX, encodeLeafPre(OTHER_KEY, OTHER_PAYOUT, 3n))
        return t
    }
    const tree = buildTree()
    const machine = (mnemonics: (string | number)[], root = tree.root()) =>
        initialState(assemble(mnemonics), undefined, { rosterRoot: root })
    /** Environment with the proof for `index` and a valid ATTESTM signature. */
    const envFor = (
        index: number,
        extra: Partial<StepEnv> = {},
        proofTree: SparseMerkleTree = tree
    ): StepEnv => ({
        ...envOf(0n),
        tree: proofTree.proof(index),
        sig: signMemberReading(attester, ID, 5n, 2231n),
        attestKey: attester.pub,
        instanceId: ID,
        ...extra,
    })

    it('full member cycle: MEMBER DROP LASTROUND ... ATTESTM OUTH PAYLEAF', () => {
        // prettier-ignore
        const prog = [
            'MEMBER', 'DROP', 'LASTROUND', 'DROP',
            'LIT', 5, 'LIT', 2231, 'ATTESTM',
            'LIT', 8, 'OUTH',
            'LIT', 25, 'LIT', 8, 'PAYLEAF', 'HALT',
        ]
        const r = stepK(machine(prog), envFor(MEMBER_INDEX), 40)
        expect(r.status).to.equal('halted')
        expect(r.treeOp).to.equal('member')
        expect(r.payslot).to.deep.equal({
            slot: -1,
            payoutHex: PAYOUT,
            sats: 25n,
        })
        const expected = buildTree()
        expected.set(
            MEMBER_INDEX,
            encodeLeafPre(keyHash(attester.pub), PAYOUT, 8n, 1n)
        )
        expect(r.state.rosterRoot).to.equal(expected.root())
        expect(r.state.rosterRoot).to.not.equal(tree.root())
        expect(r.member?.lastRound).to.equal(8n)
        expect(r.state.ds).to.equal('')
    })

    it('ATTESTM with a wrong key is verify_failed', () => {
        const bad = run(
            machine(['MEMBER', 'LIT', 5, 'LIT', 2231, 'ATTESTM', 'HALT']),
            envFor(MEMBER_INDEX, {
                attestKey: stranger.pub,
                sig: signMemberReading(stranger, ID, 5n, 2231n),
            })
        )
        expect(bad.status).to.equal('verify_failed')
    })

    it('ATTESTM with a signature over the wrong tag is verify_failed', () => {
        const bad = run(
            machine(['MEMBER', 'LIT', 5, 'LIT', 2231, 'ATTESTM', 'HALT']),
            envFor(MEMBER_INDEX, {
                sig: signMemberReading(attester, ID, 6n, 2231n),
            })
        )
        expect(bad.status).to.equal('verify_failed')
    })

    it('ATTESTM without MEMBER faults', () => {
        const r = run(
            machine(['LIT', 5, 'LIT', 2231, 'ATTESTM', 'HALT']),
            envFor(MEMBER_INDEX)
        )
        expect(r.status).to.equal('halted')
        // stopped at the ATTESTM fault, not at the HALT
        expect(r.state.pc).to.equal(10n)
    })

    it('ATTESTM when the signature was already used faults (v3.1)', () => {
        const r = run(
            machine([
                'MEMBER',
                'LIT',
                5,
                'LIT',
                2231,
                'ATTESTM',
                'LIT',
                5,
                'LIT',
                2231,
                'ATTESTM',
                'HALT',
            ]),
            envFor(MEMBER_INDEX)
        )
        // halted at the second ATTESTM (pc 22), not at the HALT
        expect(r.status).to.equal('halted')
        expect(r.state.halted).to.equal(true)
        expect(r.state.pc).to.equal(22n)
    })

    it('ATTESTM with missing signature material is need_witness', () => {
        const r = run(
            machine(['MEMBER', 'LIT', 5, 'LIT', 2231, 'ATTESTM', 'HALT']),
            envFor(MEMBER_INDEX, { sig: undefined })
        )
        expect(r.status).to.equal('need_witness')
    })

    it('PAYLEAF reports the written leaf; MEMBER alone reports none', () => {
        const prog = ['MEMBER', 'DROP', 'LIT', 1, 'LIT', 8, 'PAYLEAF', 'HALT']
        const r = stepK(machine(prog), envFor(MEMBER_INDEX), 40)
        expect(r.leafAfter).to.equal(
            encodeLeafPre(keyHash(attester.pub), PAYOUT, 8n, 1n)
        )
        expect(r.leafAfter).to.have.length(120)
        expect(
            SparseMerkleTree.rootAfter(
                r.leafAfter as string,
                tree.proof(MEMBER_INDEX).proof,
                BigInt(MEMBER_INDEX)
            )
        ).to.equal(r.state.rosterRoot)
        const only = stepK(
            machine(['MEMBER', 'DROP', 'HALT']),
            envFor(MEMBER_INDEX),
            40
        )
        expect(only.treeOp).to.equal('member')
        expect(only.leafAfter).to.equal(undefined)
    })

    /** sha256(prev || cell) folded over `cells`, as OUTH does. */
    const foldCells = (prev: string, cells: bigint[]): string =>
        cells.reduce(
            (acc, cell) =>
                createHash('sha256')
                    .update(Buffer.from(acc + encodeCell(cell), 'hex'))
                    .digest('hex'),
            prev
        )

    it('two OUTHs in one cycle report both cells in order, matching logHash', () => {
        const start = machine(['LIT', 5, 'OUTH', 'LIT', 9, 'OUTH', 'HALT'])
        const cycle = stepK(start, envFor(MEMBER_INDEX), 40)
        expect(cycle.outhCells).to.deep.equal([5n, 9n])
        expect(foldCells(start.logHash, cycle.outhCells)).to.equal(
            cycle.state.logHash
        )
        const whole = run(start, envFor(MEMBER_INDEX))
        expect(whole.outhCells).to.deep.equal([5n, 9n])
        expect(foldCells(start.logHash, whole.outhCells)).to.equal(
            whole.state.logHash
        )
        const none = stepK(machine(['LIT', 1, 'DROP', 'HALT']), envFor(9), 40)
        expect(none.outhCells).to.deep.equal([])
    })

    it('a verify_failed cycle reports no cells it did not keep', () => {
        // PAYLEAF at ROUND == lastRound is refused; nothing was folded.
        const refused = stepK(
            machine(['MEMBER', 'DROP', 'LIT', 1, 'LIT', 7, 'PAYLEAF', 'HALT']),
            envFor(MEMBER_INDEX),
            40
        )
        expect(refused.status).to.equal('verify_failed')
        expect(refused.outhCells).to.deep.equal([])
        // An OUTH that ran before the refusal is part of the kept state, so
        // its cell is reported and still agrees with the state's logHash.
        const start = machine([
            'LIT',
            5,
            'OUTH',
            'MEMBER',
            'DROP',
            'LIT',
            1,
            'LIT',
            7,
            'PAYLEAF',
            'HALT',
        ])
        const after = stepK(start, envFor(MEMBER_INDEX), 40)
        expect(after.status).to.equal('verify_failed')
        expect(foldCells(start.logHash, after.outhCells)).to.equal(
            after.state.logHash
        )
    })

    it('a fault after an OUTH keeps the cell, consistent with logHash', () => {
        // The second OUTH underflows: the state keeps the first fold only.
        const start = machine(['LIT', 5, 'OUTH', 'OUTH', 'HALT'])
        const r = stepK(start, envFor(MEMBER_INDEX), 40)
        expect(r.state.halted).to.equal(true)
        expect(r.outhCells).to.deep.equal([5n])
        expect(foldCells(start.logHash, r.outhCells)).to.equal(r.state.logHash)
    })

    it('a fault after PAYLEAF in the same cycle keeps leafAfter', () => {
        // prettier-ignore
        const prog = [
            'MEMBER', 'DROP',
            'LIT', 1, 'LIT', 8, 'PAYLEAF',
            'LIT', 1, 'LIT', 9, 'PAYLEAF', 'HALT',
        ]
        const r = stepK(machine(prog), envFor(MEMBER_INDEX), 40)
        expect(r.state.halted).to.equal(true)
        expect(r.leafAfter).to.equal(
            encodeLeafPre(keyHash(attester.pub), PAYOUT, 8n, 1n)
        )
        expect(
            SparseMerkleTree.rootAfter(
                r.leafAfter as string,
                tree.proof(MEMBER_INDEX).proof,
                BigInt(MEMBER_INDEX)
            )
        ).to.equal(r.state.rosterRoot)
    })

    it('PAYLEAF without MEMBER faults', () => {
        const r = run(machine(['LIT', 1, 'LIT', 8, 'PAYLEAF', 'HALT']), 0n)
        expect(r.status).to.equal('halted')
        expect(r.payslot).to.equal(undefined)
        expect(r.state.rosterRoot).to.equal(tree.root())
    })

    it('PAYLEAF with N == 0 faults', () => {
        const r = run(
            machine(['MEMBER', 'DROP', 'LIT', 0, 'LIT', 8, 'PAYLEAF', 'HALT']),
            envFor(MEMBER_INDEX)
        )
        expect(r.status).to.equal('halted')
        expect(r.payslot).to.equal(undefined)
        expect(r.state.rosterRoot).to.equal(tree.root())
    })

    it('PAYLEAF ROUND == lastRound is verify_failed; lastRound + 1 succeeds', () => {
        const same = run(
            machine(['MEMBER', 'DROP', 'LIT', 1, 'LIT', 7, 'PAYLEAF', 'HALT']),
            envFor(MEMBER_INDEX)
        )
        expect(same.status).to.equal('verify_failed')
        expect(same.payslot).to.equal(undefined)
        const next = run(
            machine(['MEMBER', 'DROP', 'LIT', 1, 'LIT', 8, 'PAYLEAF', 'HALT']),
            envFor(MEMBER_INDEX)
        )
        expect(next.status).to.equal('halted')
        expect(next.payslot?.sats).to.equal(1n)
    })

    it('PAYLEAF verify_failed leaves state and stack unchanged', () => {
        const env = envFor(MEMBER_INDEX)
        let cur = machine([
            'MEMBER',
            'DROP',
            'LIT',
            1,
            'LIT',
            7,
            'PAYLEAF',
            'HALT',
        ])
        let treeOp: TreeOp = 'none'
        let member: BoundMember | undefined
        for (let i = 0; i < 4; i++) {
            const r = step(cur, env, 0, 0n, false, undefined, treeOp, member)
            expect(r.status).to.equal('ok')
            cur = r.state
            treeOp = r.treeOp
            member = r.member
        }
        const r = step(cur, env, 0, 0n, false, undefined, treeOp, member)
        expect(r.status).to.equal('verify_failed')
        expect(r.state).to.equal(cur)
        expect(outputOf(r.state.ds)).to.deep.equal([1n, 7n])
    })

    it('a second PAYLEAF in one cycle faults and drops the first payslot', () => {
        // prettier-ignore
        const prog = [
            'MEMBER', 'DROP',
            'LIT', 1, 'LIT', 8, 'PAYLEAF',
            'LIT', 1, 'LIT', 9, 'PAYLEAF', 'HALT',
        ]
        const r = stepK(machine(prog), envFor(MEMBER_INDEX), 40)
        expect(r.status).to.equal('halted')
        expect(r.state.halted).to.equal(true)
        expect(r.payslot).to.equal(undefined)
    })

    it('LASTROUND after PAYLEAF sees the new round', () => {
        const r = run(
            machine([
                'MEMBER',
                'DROP',
                'LIT',
                1,
                'LIT',
                8,
                'PAYLEAF',
                'LASTROUND',
                'HALT',
            ]),
            envFor(MEMBER_INDEX)
        )
        expect(outputOf(r.state.ds)).to.deep.equal([8n])
    })

    it('a proof against the previous root fails after another member paid', () => {
        // Another member's PAYLEAF changes the root; the old proof no longer
        // verifies against it, so MEMBER fails with the stale proof.
        const first = run(
            machine(['MEMBER', 'DROP', 'LIT', 1, 'LIT', 4, 'PAYLEAF', 'HALT']),
            envFor(OTHER_INDEX)
        )
        expect(first.state.rosterRoot).to.not.equal(tree.root())
        const stale = step(
            machine(['MEMBER', 'HALT'], first.state.rosterRoot),
            envFor(MEMBER_INDEX)
        )
        expect(stale.status).to.equal('verify_failed')
        // a proof against the new tree still works
        const updated = buildTree()
        updated.set(OTHER_INDEX, encodeLeafPre(OTHER_KEY, OTHER_PAYOUT, 4n))
        expect(updated.root()).to.equal(first.state.rosterRoot)
        const fresh = step(
            machine(['MEMBER', 'HALT'], first.state.rosterRoot),
            envFor(MEMBER_INDEX, {}, updated)
        )
        expect(fresh.status).to.equal('ok')
    })

    it('the same member and round again is verify_failed', () => {
        const first = run(
            machine(['MEMBER', 'DROP', 'LIT', 1, 'LIT', 8, 'PAYLEAF', 'HALT']),
            envFor(MEMBER_INDEX)
        )
        const updated = buildTree()
        updated.set(
            MEMBER_INDEX,
            encodeLeafPre(keyHash(attester.pub), PAYOUT, 8n, 1n)
        )
        expect(first.state.rosterRoot).to.equal(updated.root())
        const again = run(
            machine(
                ['MEMBER', 'DROP', 'LIT', 1, 'LIT', 8, 'PAYLEAF', 'HALT'],
                first.state.rosterRoot
            ),
            envFor(MEMBER_INDEX, {}, updated)
        )
        expect(again.status).to.equal('verify_failed')
    })
})

describe('K17 v3 ADMIT and REMOVE', function () {
    this.timeout(180_000)
    const sponsor = newAttester(Buffer.alloc(32, 51))
    const newcomer = newAttester(Buffer.alloc(32, 52))
    const stranger = newAttester(Buffer.alloc(32, 53))
    const NEW_PAYOUT = '77'.repeat(20)
    const OLD_KEY = '88'.repeat(32)
    const OLD_PAYOUT = '99'.repeat(20)
    const OLD_INDEX = 12
    const NEW_INDEX = 4242
    const TAG = 5n
    const ADMIT_ROUND = 6n
    /** Off-chain mirror holding one existing member at OLD_INDEX. */
    const buildTree = (): SparseMerkleTree => {
        const t = new SparseMerkleTree()
        t.set(OLD_INDEX, encodeLeafPre(OLD_KEY, OLD_PAYOUT, 2n))
        return t
    }
    const newcomerLeaf = (round: bigint) =>
        encodeLeafPre(keyHash(newcomer.pub), NEW_PAYOUT, round, 0n)
    /** Machine whose sponsor is `sponsor`, at `root` and optional seq. */
    const machine = (
        mnemonics: (string | number)[],
        root: string,
        seq = 0n
    ) => {
        const s = initialState(assemble(mnemonics), undefined, {
            rosterRoot: root,
            sponsorKeyHash: keyHash(sponsor.pub),
        })
        return { ...s, rosterSeq: seq }
    }
    /** Environment for ADMIT at `index` signed for `seq`, overridable. */
    const admitEnv = (
        tree: SparseMerkleTree,
        index = NEW_INDEX,
        seq = 0n,
        extra: Partial<StepEnv> = {}
    ): StepEnv => ({
        ...envOf(0n),
        tree: tree.proof(index),
        sig: signAdmission(
            sponsor,
            ID,
            TAG,
            seq,
            BigInt(index),
            newcomer.pub,
            NEW_PAYOUT
        ),
        attestKey: sponsor.pub,
        endorseKey: newcomer.pub,
        payout: NEW_PAYOUT,
        instanceId: ID,
        ...extra,
    })
    /** Environment for REMOVE at `index` signed for `seq`, overridable. */
    const removeEnv = (
        tree: SparseMerkleTree,
        index = OLD_INDEX,
        seq = 0n,
        extra: Partial<StepEnv> = {}
    ): StepEnv => {
        const proof = tree.proof(index)
        // Sign over the member's keyHash || payout (v3.1) unless the caller
        // brings its own signature (an empty leaf has no member to sign).
        const sig =
            'sig' in extra
                ? extra.sig
                : (() => {
                      const member = decodeLeafPre(proof.leafPre)
                      return signRemoval(
                          sponsor,
                          ID,
                          TAG,
                          seq,
                          BigInt(index),
                          member.keyHashHex,
                          member.payoutHex
                      )
                  })()
        return {
            ...envOf(0n),
            tree: proof,
            sig,
            attestKey: sponsor.pub,
            instanceId: ID,
            ...extra,
        }
    }
    const ADMIT_PROG = ['LIT', 5, 'LIT', 6, 'ADMIT', 'HALT']
    const REMOVE_PROG = ['LIT', 5, 'REMOVE', 'HALT']

    it('admits into an empty index, then the member attests and is paid against the new root', () => {
        const tree = buildTree()
        // prettier-ignore
        const prog = [
            'LIT', 5, 'LIT', 6, 'ADMIT', 'YIELD',
            'MEMBER', 'DROP', 'LIT', 5, 'LIT', 2231, 'ATTESTM',
            'LIT', 9, 'LIT', 7, 'PAYLEAF', 'HALT',
        ]
        const first = stepK(machine(prog, tree.root()), admitEnv(tree), 40)
        expect(first.status).to.equal('ok')
        expect(first.treeOp).to.equal('admit')
        expect(first.state.rosterSeq).to.equal(1n)
        expect(first.state.ds).to.equal('')
        tree.set(NEW_INDEX, newcomerLeaf(ADMIT_ROUND))
        expect(first.state.rosterRoot).to.equal(tree.root())

        const second = stepK(
            first.state,
            {
                ...envOf(0n),
                tree: tree.proof(NEW_INDEX),
                sig: signMemberReading(newcomer, ID, 5n, 2231n),
                attestKey: newcomer.pub,
                instanceId: ID,
            },
            40
        )
        expect(second.status).to.equal('halted')
        expect(second.treeOp).to.equal('member')
        expect(second.payslot).to.deep.equal({
            slot: -1,
            payoutHex: NEW_PAYOUT,
            sats: 9n,
        })
        tree.set(NEW_INDEX, newcomerLeaf(7n))
        expect(second.state.rosterRoot).to.equal(tree.root())
        // the sponsor's roster counter does not move on a member payment
        expect(second.state.rosterSeq).to.equal(1n)
    })

    it('a member admitted in round r cannot be paid in r but can in r+1', () => {
        const tree = buildTree()
        const first = stepK(
            machine(ADMIT_PROG.slice(0, 5).concat('YIELD'), tree.root()),
            admitEnv(tree),
            40
        )
        expect(first.status).to.equal('ok')
        tree.set(NEW_INDEX, newcomerLeaf(ADMIT_ROUND))
        const payEnv = (): StepEnv => ({
            ...envOf(0n),
            tree: tree.proof(NEW_INDEX),
        })
        const payProg = (round: number) => [
            'MEMBER',
            'DROP',
            'LIT',
            1,
            'LIT',
            round,
            'PAYLEAF',
            'HALT',
        ]
        const withProg = (round: number) => ({
            ...first.state,
            prog: assemble(payProg(round)),
            pc: 0n,
        })
        const same = stepK(withProg(6), payEnv(), 40)
        expect(same.status).to.equal('verify_failed')
        const next = stepK(withProg(7), payEnv(), 40)
        expect(next.status).to.equal('halted')
        expect(next.payslot?.sats).to.equal(1n)
    })

    it('ADMIT reports the new leaf and REMOVE reports an empty one', () => {
        const tree = buildTree()
        const admitted = stepK(
            machine(ADMIT_PROG, tree.root()),
            admitEnv(tree),
            40
        )
        expect(admitted.leafAfter).to.equal(newcomerLeaf(ADMIT_ROUND))
        expect(admitted.leafAfter).to.have.length(120)
        expect(
            SparseMerkleTree.rootAfter(
                admitted.leafAfter as string,
                tree.proof(NEW_INDEX).proof,
                BigInt(NEW_INDEX)
            )
        ).to.equal(admitted.state.rosterRoot)

        const removed = stepK(
            machine(REMOVE_PROG, tree.root()),
            removeEnv(tree),
            40
        )
        expect(removed.treeOp).to.equal('remove')
        expect(removed.leafAfter).to.equal('')
        expect(
            SparseMerkleTree.rootAfter(
                removed.leafAfter as string,
                tree.proof(OLD_INDEX).proof,
                BigInt(OLD_INDEX)
            )
        ).to.equal(removed.state.rosterRoot)
    })

    it('ADMIT with a stale rosterSeq in the signed message is verify_failed', () => {
        const tree = buildTree()
        const s = machine(ADMIT_PROG, tree.root(), 3n)
        const stale = stepK(s, admitEnv(tree, NEW_INDEX, 2n), 40)
        expect(stale.status).to.equal('verify_failed')
        expect(stale.state.rosterRoot).to.equal(tree.root())
        expect(stale.state.rosterSeq).to.equal(3n)
        const fresh = stepK(s, admitEnv(tree, NEW_INDEX, 3n), 40)
        expect(fresh.status).to.equal('halted')
        expect(fresh.state.rosterSeq).to.equal(4n)
    })

    it('ADMIT onto an occupied index is verify_failed', () => {
        const tree = buildTree()
        const r = stepK(
            machine(ADMIT_PROG, tree.root()),
            admitEnv(tree, OLD_INDEX),
            40
        )
        expect(r.status).to.equal('verify_failed')
        expect(r.state.rosterRoot).to.equal(tree.root())
    })

    it('ADMIT signed by a non-sponsor key is verify_failed', () => {
        const tree = buildTree()
        const r = stepK(
            machine(ADMIT_PROG, tree.root()),
            admitEnv(tree, NEW_INDEX, 0n, {
                attestKey: stranger.pub,
                sig: signAdmission(
                    stranger,
                    ID,
                    TAG,
                    0n,
                    BigInt(NEW_INDEX),
                    newcomer.pub,
                    NEW_PAYOUT
                ),
            }),
            40
        )
        expect(r.status).to.equal('verify_failed')
    })

    it('ADMIT with no sponsor configured is verify_failed', () => {
        const tree = buildTree()
        const s = initialState(assemble(ADMIT_PROG), undefined, {
            rosterRoot: tree.root(),
        })
        expect(stepK(s, admitEnv(tree), 40).status).to.equal('verify_failed')
    })

    it('ADMIT with an uppercase payout is verify_failed', () => {
        const tree = buildTree()
        const upper = NEW_PAYOUT.replace(/7/g, 'A')
        const r = stepK(
            machine(ADMIT_PROG, tree.root()),
            admitEnv(tree, NEW_INDEX, 0n, { payout: upper }),
            40
        )
        expect(r.status).to.equal('verify_failed')
    })

    it('ADMIT needs a witness without a tree, signature or key, or after a signature', () => {
        const tree = buildTree()
        const s = machine(ADMIT_PROG, tree.root())
        for (const missing of [
            'tree',
            'sig',
            'attestKey',
            'endorseKey',
            'payout',
            'instanceId',
        ]) {
            const r = stepK(
                s,
                admitEnv(tree, NEW_INDEX, 0n, { [missing]: undefined }),
                40
            )
            expect(r.status, missing).to.equal('need_witness')
        }
        const twice = stepK(
            machine(
                ['LIT', 5, 'LIT', 6, 'ADMIT', 'LIT', 5, 'LIT', 6, 'ADMIT'],
                tree.root()
            ),
            admitEnv(tree),
            40
        )
        // second ADMIT: a member/admin op was already bound, so it faults
        expect(twice.status).to.equal('halted')
        expect(twice.treeOp).to.equal('admit')
        expect(twice.state.pc).to.equal(21n)
    })

    it('ADMIT with the signature already used this cycle faults (v3.1)', () => {
        const tree = buildTree()
        const s = {
            ...machine(['ADMIT', 'HALT'], tree.root()),
            ds: encodeCell(TAG) + encodeCell(ADMIT_ROUND),
        }
        const r = step(s, admitEnv(tree), 0, 0n, true)
        expect(r.status).to.equal('fault')
        expect(r.state.halted).to.equal(true)
        // a fault leaves the tree untouched
        expect(r.state.rosterRoot).to.equal(s.rosterRoot)
        expect(r.state.rosterSeq).to.equal(s.rosterSeq)
        expect(r.treeOp).to.equal('none')
    })

    it('REMOVE with the signature already used this cycle faults (v3.1)', () => {
        const tree = buildTree()
        const s = {
            ...machine(['REMOVE', 'HALT'], tree.root()),
            ds: encodeCell(TAG),
        }
        // the full REMOVE witness is present; only the used signature faults
        expect(step(s, removeEnv(tree), 0, 0n, false).status).to.equal('ok')
        const r = step(s, removeEnv(tree), 0, 0n, true)
        expect(r.status).to.equal('fault')
        expect(r.state.halted).to.equal(true)
        expect(r.state.rosterRoot).to.equal(s.rosterRoot)
        expect(r.state.rosterSeq).to.equal(s.rosterSeq)
        expect(r.state.ds).to.equal(encodeCell(TAG))
        expect(r.treeOp).to.equal('none')
    })

    it('ADMIT over a filled slot with an empty preimage and its real siblings is verify_failed', () => {
        const tree = buildTree()
        const s = machine(ADMIT_PROG, tree.root())
        const r = stepK(
            s,
            admitEnv(tree, OLD_INDEX, 0n, {
                tree: { ...tree.proof(OLD_INDEX), leafPre: '' },
            }),
            40
        )
        expect(r.status).to.equal('verify_failed')
        expect(r.state.rosterRoot).to.equal(tree.root())
        expect(r.state.rosterSeq).to.equal(0n)
    })

    describe('substitution under one genuine sponsor signature', () => {
        const OTHER_EMPTY_INDEX = 777
        const attack = (
            extra: (tree: SparseMerkleTree) => Partial<StepEnv>,
            program: (string | number)[] = ADMIT_PROG
        ) => {
            const tree = buildTree()
            const r = stepK(
                machine(program, tree.root()),
                admitEnv(tree, NEW_INDEX, 0n, extra(tree)),
                40
            )
            expect(r.status).to.equal('verify_failed')
            expect(r.state.rosterRoot).to.equal(tree.root())
            expect(r.state.rosterSeq).to.equal(0n)
        }
        it('swapped endorseKey', () =>
            attack(() => ({ endorseKey: stranger.pub })))
        it('swapped payout', () => attack(() => ({ payout: '78'.repeat(20) })))
        it('swapped proof and leafIndex to another empty index', () =>
            attack((tree) => ({ tree: tree.proof(OTHER_EMPTY_INDEX) })))
        it('different TAG on the stack', () =>
            attack(() => ({}), ['LIT', 6, 'LIT', 6, 'ADMIT', 'HALT']))
        it('attestKey is the sponsor but a stranger produced the signature', () =>
            attack(() => ({
                sig: signAdmission(
                    stranger,
                    ID,
                    TAG,
                    0n,
                    BigInt(NEW_INDEX),
                    newcomer.pub,
                    NEW_PAYOUT
                ),
            })))
    })

    it('an uppercase payout is rejected even under a signature that covers it', () => {
        const tree = buildTree()
        const upper = NEW_PAYOUT.replace(/7/g, 'A')
        const r = stepK(
            machine(ADMIT_PROG, tree.root()),
            admitEnv(tree, NEW_INDEX, 0n, {
                payout: upper,
                sig: signAdmission(
                    sponsor,
                    ID,
                    TAG,
                    0n,
                    BigInt(NEW_INDEX),
                    newcomer.pub,
                    upper
                ),
            }),
            40
        )
        expect(r.status).to.equal('verify_failed')
        expect(r.state.rosterRoot).to.equal(tree.root())
    })

    it('ADMIT faults on a short stack', () => {
        const tree = buildTree()
        const r = stepK(
            machine(['LIT', 5, 'ADMIT', 'HALT'], tree.root()),
            admitEnv(tree),
            40
        )
        expect(r.status).to.equal('halted')
        expect(r.state.rosterRoot).to.equal(tree.root())
    })

    it('MEMBER after ADMIT in one cycle faults', () => {
        const tree = buildTree()
        const r = stepK(
            machine(
                ['LIT', 5, 'LIT', 6, 'ADMIT', 'MEMBER', 'HALT'],
                tree.root()
            ),
            admitEnv(tree),
            40
        )
        expect(r.status).to.equal('halted')
        expect(r.treeOp).to.equal('admit')
        expect(r.state.pc).to.equal(11n)
    })

    it('ADMIT after MEMBER in one cycle faults', () => {
        const tree = buildTree()
        const r = stepK(
            machine(
                ['MEMBER', 'DROP', 'LIT', 5, 'LIT', 6, 'ADMIT', 'HALT'],
                tree.root()
            ),
            { ...admitEnv(tree, OLD_INDEX) },
            40
        )
        expect(r.status).to.equal('halted')
        expect(r.treeOp).to.equal('member')
        expect(r.state.rosterRoot).to.equal(tree.root())
    })

    it('removes a member and updates root and seq', () => {
        const tree = buildTree()
        const r = stepK(machine(REMOVE_PROG, tree.root()), removeEnv(tree), 40)
        expect(r.status).to.equal('halted')
        expect(r.treeOp).to.equal('remove')
        expect(r.state.rosterSeq).to.equal(1n)
        expect(r.state.ds).to.equal('')
        tree.set(OLD_INDEX, '')
        expect(r.state.rosterRoot).to.equal(tree.root())
    })

    it('after REMOVE the removed member proof and the original admission are verify_failed', () => {
        // admit in cycle 1, remove in cycle 2, then replay the admission
        const tree = buildTree()
        const admitted = stepK(
            machine(ADMIT_PROG.slice(0, 5).concat('YIELD'), tree.root()),
            admitEnv(tree),
            40
        )
        tree.set(NEW_INDEX, newcomerLeaf(ADMIT_ROUND))
        const removing = {
            ...admitted.state,
            prog: assemble(REMOVE_PROG),
            pc: 0n,
        }
        const removed = stepK(removing, removeEnv(tree, NEW_INDEX, 1n), 40)
        expect(removed.status).to.equal('halted')
        expect(removed.state.rosterSeq).to.equal(2n)
        const afterRemove = new SparseMerkleTree()
        afterRemove.set(OLD_INDEX, encodeLeafPre(OLD_KEY, OLD_PAYOUT, 2n))
        expect(removed.state.rosterRoot).to.equal(afterRemove.root())

        // the removed member's old proof no longer verifies
        const asMember = stepK(
            {
                ...removed.state,
                halted: false,
                prog: assemble(['MEMBER', 'HALT']),
                pc: 0n,
            },
            { ...envOf(0n), tree: tree.proof(NEW_INDEX) },
            40
        )
        expect(asMember.status).to.equal('verify_failed')

        // replaying the cycle-1 admission (seq 0) fails: stale seq
        const replay = stepK(
            {
                ...removed.state,
                halted: false,
                prog: assemble(ADMIT_PROG),
                pc: 0n,
            },
            admitEnv(afterRemove),
            40
        )
        expect(replay.status).to.equal('verify_failed')
        // a fresh admission at the current seq succeeds
        const fresh = stepK(
            {
                ...removed.state,
                halted: false,
                prog: assemble(ADMIT_PROG),
                pc: 0n,
            },
            admitEnv(afterRemove, NEW_INDEX, 2n),
            40
        )
        expect(fresh.status).to.equal('halted')
        expect(fresh.state.rosterSeq).to.equal(3n)
    })

    it('REMOVE with a wrong rosterSeq is verify_failed', () => {
        const tree = buildTree()
        const r = stepK(
            machine(REMOVE_PROG, tree.root(), 1n),
            removeEnv(tree, OLD_INDEX, 0n),
            40
        )
        expect(r.status).to.equal('verify_failed')
    })

    it('REMOVE on an empty index is verify_failed', () => {
        const tree = buildTree()
        const r = stepK(
            machine(REMOVE_PROG, tree.root()),
            removeEnv(tree, NEW_INDEX, 0n, {
                // a sponsor signature over an all-zero identity: the
                // empty leaf is refused before the signature is checked
                sig: signRemoval(
                    sponsor,
                    ID,
                    TAG,
                    0n,
                    BigInt(NEW_INDEX),
                    '00'.repeat(32),
                    '00'.repeat(20)
                ),
            }),
            40
        )
        expect(r.status).to.equal('verify_failed')
    })

    it('REMOVE signed by a non-sponsor key is verify_failed', () => {
        const tree = buildTree()
        const r = stepK(
            machine(REMOVE_PROG, tree.root()),
            removeEnv(tree, OLD_INDEX, 0n, {
                attestKey: stranger.pub,
                sig: signRemoval(
                    stranger,
                    ID,
                    TAG,
                    0n,
                    BigInt(OLD_INDEX),
                    OLD_KEY,
                    OLD_PAYOUT
                ),
            }),
            40
        )
        expect(r.status).to.equal('verify_failed')
    })

    it('v3.1: a removal replayed after re-admission of the same member at the same index is verify_failed', () => {
        // Under v3.1 the removal message binds keyHash || payout, which is
        // the same after the member is admitted again at the same index.
        // rosterSeq is then the only guard, and this test pins it.
        const tree = new SparseMerkleTree()
        tree.set(NEW_INDEX, newcomerLeaf(2n))
        const member = decodeLeafPre(newcomerLeaf(2n))
        // the sponsor signs the removal at seq 0
        const oldSig = signRemoval(
            sponsor,
            ID,
            TAG,
            0n,
            BigInt(NEW_INDEX),
            member.keyHashHex,
            member.payoutHex
        )
        // prettier-ignore
        const prog = [
            'LIT', 5, 'REMOVE', 'YIELD',
            'LIT', 5, 'LIT', 6, 'ADMIT', 'YIELD',
            'LIT', 5, 'REMOVE', 'HALT',
        ]
        // cycle 1: REMOVE (seq 0 -> 1)
        const removed = stepK(
            machine(prog, tree.root()),
            removeEnv(tree, NEW_INDEX, 0n, { sig: oldSig }),
            40
        )
        expect(removed.status).to.equal('ok')
        expect(removed.state.rosterSeq).to.equal(1n)
        tree.set(NEW_INDEX, '')
        expect(removed.state.rosterRoot).to.equal(tree.root())
        // cycle 2: ADMIT the same key and payout at the same index (1 -> 2)
        const readmitted = stepK(
            removed.state,
            admitEnv(tree, NEW_INDEX, 1n),
            40
        )
        expect(readmitted.status).to.equal('ok')
        expect(readmitted.state.rosterSeq).to.equal(2n)
        tree.set(NEW_INDEX, newcomerLeaf(ADMIT_ROUND))
        expect(readmitted.state.rosterRoot).to.equal(tree.root())
        // the 52-byte identity the removal binds is unchanged
        expect(tree.proof(NEW_INDEX).leafPre.slice(0, 104)).to.equal(
            newcomerLeaf(2n).slice(0, 104)
        )
        // cycle 3: the seq-0 removal with a fresh proof is refused
        const replay = stepK(
            readmitted.state,
            removeEnv(tree, NEW_INDEX, 0n, { sig: oldSig }),
            40
        )
        expect(replay.status).to.equal('verify_failed')
        expect(replay.state.rosterRoot).to.equal(readmitted.state.rosterRoot)
        expect(replay.state.rosterSeq).to.equal(2n)
        // control: a removal signed at the current seq is accepted
        const fresh = stepK(
            readmitted.state,
            removeEnv(tree, NEW_INDEX, 2n),
            40
        )
        expect(fresh.status).to.equal('halted')
        expect(fresh.state.rosterSeq).to.equal(3n)
    })

    describe('a removal signed before a PAYLEAF (v3.1)', () => {
        // One program, two cycles: cycle 1 pays the member at OLD_INDEX
        // (lastRound 2 -> 8, so the leaf and the root change), cycle 2
        // removes it with a signature made before cycle 1.
        // prettier-ignore
        const PAY_THEN_REMOVE = [
            'MEMBER', 'DROP', 'LIT', 1, 'LIT', 8, 'PAYLEAF', 'YIELD',
            'LIT', 5, 'REMOVE', 'HALT',
        ]
        /**
         * Run cycle 1 (the payment) from a fresh machine.
         * Input: the off-chain tree, which is updated to the paid leaf.
         * Output: the cycle result.
         */
        const payCycle = (tree: SparseMerkleTree) => {
            const paid = stepK(
                machine(PAY_THEN_REMOVE, tree.root()),
                { ...envOf(0n), tree: tree.proof(OLD_INDEX), instanceId: ID },
                40
            )
            tree.set(OLD_INDEX, encodeLeafPre(OLD_KEY, OLD_PAYOUT, 8n))
            return paid
        }
        /**
         * Run cycle 2 (the removal) with a fresh proof and `sig`.
         * Input: state after cycle 1, tree after cycle 1, signature.
         * Output: the cycle result.
         */
        const removeCycle = (
            state: K17State,
            tree: SparseMerkleTree,
            sig: RabinSig
        ) =>
            stepK(
                state,
                {
                    ...envOf(0n),
                    tree: tree.proof(OLD_INDEX),
                    sig,
                    attestKey: sponsor.pub,
                    instanceId: ID,
                },
                40
            )
        /** Sponsor signature at seq 0 for OLD_INDEX over key and payout. */
        const earlySig = (key: string, payout: string) =>
            signRemoval(sponsor, ID, TAG, 0n, BigInt(OLD_INDEX), key, payout)

        it('is accepted against the new root after the payment', () => {
            const tree = buildTree()
            const sig = earlySig(OLD_KEY, OLD_PAYOUT)
            const oldRoot = tree.root()
            const paid = payCycle(tree)
            expect(paid.status).to.equal('ok')
            expect(paid.state.rosterSeq).to.equal(0n)
            expect(paid.state.rosterRoot).to.not.equal(oldRoot)
            expect(paid.state.rosterRoot).to.equal(tree.root())
            const removed = removeCycle(paid.state, tree, sig)
            expect(removed.status).to.equal('halted')
            expect(removed.treeOp).to.equal('remove')
            expect(removed.state.rosterSeq).to.equal(1n)
            tree.set(OLD_INDEX, '')
            expect(removed.state.rosterRoot).to.equal(tree.root())
        })

        it('with a swapped payout (same key) is verify_failed', () => {
            const tree = buildTree()
            const paid = payCycle(tree)
            const r = removeCycle(
                paid.state,
                tree,
                earlySig(OLD_KEY, '78'.repeat(20))
            )
            expect(r.status).to.equal('verify_failed')
            expect(r.state.rosterRoot).to.equal(paid.state.rosterRoot)
        })

        it('with a swapped keyHash (same payout) is verify_failed', () => {
            const tree = buildTree()
            const paid = payCycle(tree)
            const r = removeCycle(
                paid.state,
                tree,
                earlySig('87'.repeat(32), OLD_PAYOUT)
            )
            expect(r.status).to.equal('verify_failed')
            expect(r.state.rosterRoot).to.equal(paid.state.rosterRoot)
        })
    })

    it('REMOVE needs a witness when the signature is missing and faults on an empty stack', () => {
        const tree = buildTree()
        expect(
            stepK(
                machine(REMOVE_PROG, tree.root()),
                removeEnv(tree, OLD_INDEX, 0n, { sig: undefined }),
                40
            ).status
        ).to.equal('need_witness')
        const empty = stepK(
            machine(['REMOVE', 'HALT'], tree.root()),
            removeEnv(tree),
            40
        )
        expect(empty.status).to.equal('halted')
        expect(empty.state.rosterRoot).to.equal(tree.root())
    })
})

describe('K17 v3.1 dead-man halt', function () {
    const LAST = 1_760_000_000n
    const DEAD = 3600n
    /** Program that needs a witness at its first instruction. */
    const waitIn = () => initialState(assemble(['IN', 'OUT', 'HALT']))
    /** Environment at `lockTime` with no witness and the given dead-man. */
    const envAt = (lockTime: bigint, deadMan?: bigint): StepEnv => ({
        ...envOf(lockTime),
        deadMan,
        lastTime: LAST,
    })

    it('deadManDue fires at exactly lastTime + deadMan, not one second earlier', () => {
        expect(deadManDue(envAt(LAST + DEAD - 1n, DEAD))).to.equal(false)
        expect(deadManDue(envAt(LAST + DEAD, DEAD))).to.equal(true)
        expect(deadManDue(envAt(LAST + DEAD + 1n, DEAD))).to.equal(true)
    })

    it('deadManDue is off for deadMan 0, undefined deadMan or undefined lastTime', () => {
        const far = LAST + 100n * 365n * 86_400n
        expect(deadManDue(envAt(far, 0n))).to.equal(false)
        expect(deadManDue(envAt(far))).to.equal(false)
        expect(deadManDue({ ...envOf(far), deadMan: DEAD })).to.equal(false)
    })

    it('stepK halts before the first instruction when due, and needs a witness one second earlier', () => {
        const early = stepK(waitIn(), envAt(LAST + DEAD - 1n, DEAD), 40)
        expect(early.status).to.equal('need_witness')
        const due = stepK(waitIn(), envAt(LAST + DEAD, DEAD), 40)
        expect(due.status).to.equal('halted')
        expect(due.state.halted).to.equal(true)
        // nothing executed
        expect(due.state.pc).to.equal(0n)
        expect(due.state.ds).to.equal('')
        expect(due.witnessUsed).to.equal(0)
        expect(due.bountyDue).to.equal(0n)
        expect(due.treeOp).to.equal('none')
        expect(due.payslot).to.equal(undefined)
    })

    it('run halts with zero steps when due; deadMan 0 never fires', () => {
        const due = run(waitIn(), envAt(LAST + DEAD, DEAD))
        expect(due.status).to.equal('halted')
        expect(due.steps).to.equal(0)
        expect(due.state.halted).to.equal(true)
        const off = run(waitIn(), envAt(LAST + 10n * DEAD, 0n))
        expect(off.status).to.equal('need_witness')
    })

    it('a machine blocked on MEMBER with an empty tree escapes via the dead-man', () => {
        const s = initialState(assemble(['MEMBER', 'OUT', 'HALT']))
        expect(stepK(s, envAt(LAST + 60n, DEAD), 40).status).to.equal(
            'need_witness'
        )
        const due = stepK(s, envAt(LAST + DEAD, DEAD), 40)
        expect(due.status).to.equal('halted')
        expect(due.state.rosterRoot).to.equal(EMPTY_HASHES[16])
    })

    it('a program that would bounty and pay does not when the dead-man fires', () => {
        const s = initialState(
            assemble(['BOUNTY', 500, 'VALUE', 'OUT', 'HALT'])
        )
        const due = stepK(s, { ...envAt(LAST + DEAD, DEAD), value: 9n }, 40)
        expect(due.status).to.equal('halted')
        expect(due.bountyDue).to.equal(0n)
        expect(outputLog(due.state)).to.deep.equal([])
    })
})

describe('K17 v3.1 canonical unlocking arguments (VM reporting)', () => {
    const KEY_5 = '11'.repeat(32)
    const PAYOUT = '33'.repeat(20)
    const tree = new SparseMerkleTree()
    tree.set(5, encodeLeafPre(KEY_5, PAYOUT, 7n, 1n))

    it('MEMBER on a full data stack faults but reports treeOp member (the contract still checks the proof)', () => {
        const fill: (string | number)[] = []
        for (let i = 0; i < DS_MAX; i++) fill.push('LIT', i)
        const s = initialState(
            assemble([...fill, 'MEMBER', 'HALT']),
            undefined,
            {
                rosterRoot: tree.root(),
            }
        )
        const r = stepK(s, { ...envOf(0n), tree: tree.proof(5) }, DS_MAX + 2)
        expect(r.status).to.equal('halted')
        expect(r.state.halted).to.equal(true)
        expect(r.treeOp).to.equal('member')
    })

    it('stepK reports the signature instruction and its key (sigOp, sigKey)', () => {
        const attester = newAttester(Buffer.alloc(32, 9))
        const roster = [0n, attester.pub]
        // no signature instruction: both undefined
        const none = stepK(initialState(assemble(['LIT', 1, 'HALT'])), 0n, 4)
        expect(none.sigOp).to.equal(undefined)
        expect(none.sigKey).to.equal(undefined)
        // SIGVERIFY 1: the roster key, not attestKey
        const r = stepK(
            initialState(
                assemble(['LIT', 5, 'LIT', 7, 'SIGVERIFY', 1, 'HALT'])
            ),
            {
                ...envOf(0n),
                roster,
                sig: signReading(attester, 5n, 7n),
                attestKey: 123n,
            },
            8
        )
        expect(r.status).to.equal('halted')
        expect(r.sigOp).to.equal(Op.SIGVERIFY)
        expect(r.sigKey).to.equal(attester.pub)
        // a SIGVERIFY that faults (empty roster slot) uses no signature
        const f = stepK(
            initialState(
                assemble(['LIT', 5, 'LIT', 7, 'SIGVERIFY', 0, 'HALT'])
            ),
            { ...envOf(0n), roster, sig: signReading(attester, 5n, 7n) },
            8
        )
        expect(f.state.halted).to.equal(true)
        expect(f.sigOp).to.equal(undefined)
    })
})
