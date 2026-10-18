/**
 * Tests for the off-chain K17 reference VM and assembler.
 * These run without the sCrypt compiler and pin down the ISA semantics that
 * the on-chain interpreter must reproduce.
 */
import { expect } from 'chai'
import {
    assemble,
    disassemble,
    encodeCell,
    decodeCell,
    Op,
    DS_MAX,
    CELL_MOD,
} from '../src/k17/isa'
import { initialState, run, step, stepK, outputLog } from '../src/k17/vm'
import {
    countdownProgram,
    fibonacciProgram,
    heartbeatProgram,
} from '../src/k17/programs'

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

    it('stepK stops at halt', () => {
        const s = stepK(
            initialState(assemble(['LIT', 1, 'OUT', 'HALT', 'LIT', 2, 'OUT'])),
            0n,
            10
        )
        expect(s.halted).to.be.true
        expect(outputLog(s)).to.deep.equal([1n])
    })
})
