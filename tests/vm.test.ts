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
} from '../src/k17/isa'
import {
    initialState,
    run,
    step,
    stepK,
    outputLog,
    envOf,
    hashCell,
} from '../src/k17/vm'
import {
    countdownProgram,
    fibonacciProgram,
    heartbeatProgram,
    attestProgram,
} from '../src/k17/programs'
import { newAttester, signReading } from '../src/k17/attest'

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
        expect(log.length).to.equal(64)
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
