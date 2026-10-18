/**
 * Sample K17 programs used by the tests and the demo keeper.
 *
 * Memory map convention for these programs:
 *   mem[0] = loop counter
 *   mem[1] = Fibonacci a
 *   mem[2] = Fibonacci b
 */

import { assemble } from './isa'

/**
 * Emit the first `n` Fibonacci numbers (0, 1, 1, 2, ...) to the output log,
 * then HALT. Input: n. Output: program hex.
 *
 * Forth-style listing:
 *   0 1 !   1 2 !   n 0 !
 *   loop:  1 @ OUT
 *          1 @ 2 @ +          ( a+b )
 *          1 @ 2 !            ( b = a )
 *          1 !                ( a = a+b )
 *          0 @ 1 - DUP 0 !    ( n = n-1, keep copy )
 *          IF end             ( branch when n == 0 )
 *          0 IF loop          ( unconditional jump )
 *   end:   HALT
 */
export function fibonacciProgram(n: number): string {
    // prettier-ignore
    return assemble([
        'LIT', 0, 'LIT', 1, '!',
        'LIT', 1, 'LIT', 2, '!',
        'LIT', n, 'LIT', 0, '!',
        'loop:',
        'LIT', 1, '@', 'OUT',
        'LIT', 1, '@', 'LIT', 2, '@', '+',
        'LIT', 1, '@', 'LIT', 2, '!',
        'LIT', 1, '!',
        'LIT', 0, '@', 'LIT', 1, '-', 'DUP', 'LIT', 0, '!',
        'IF', 'end',
        'LIT', 0, 'IF', 'loop',
        'end:', 'HALT',
    ])
}

/**
 * Count down from `n` to 1, emitting each value, using a subroutine for the
 * emit so CALL/EXIT and the return stack are exercised. Input: n.
 * Output: program hex.
 */
export function countdownProgram(n: number): string {
    // prettier-ignore
    return assemble([
        'LIT', n,
        'loop:',
        'DUP', 'CALL', 'emit',
        'LIT', 1, '-',
        'DUP', 'IF', 'end',
        'LIT', 0, 'IF', 'loop',
        'end:', 'DROP', 'HALT',
        'emit:', 'OUT', 'EXIT',
    ])
}

/**
 * Record the transaction time of every cycle it runs in, forever (until the
 * output log fills and the machine faults). A heartbeat / dead-man demo.
 * Output: program hex.
 */
export function heartbeatProgram(): string {
    return assemble(['loop:', 'TIME', 'OUT', 'LIT', 0, 'IF', 'loop'])
}
