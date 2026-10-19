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
    hashCell,
    readSlot,
    withSlot,
} from '../src/k17/vm'
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
} from '../src/k17/attest'
import { RabinVerifier } from 'scrypt-ts-lib'
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

    it('a second SIGVERIFY in one cycle invalidates the transaction', function () {
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
        expect(r.status).to.equal('need_witness')
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

    it('needs a witness without a signature or a key, or after one is used', function () {
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
        expect(r.status).to.equal('need_witness')
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

    it('needs a witness for ENDORSE after ATTEST in one cycle', function () {
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
        expect(r.status).to.equal('need_witness')
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
