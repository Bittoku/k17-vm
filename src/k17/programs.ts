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

/**
 * Job bounty: factor a 32-bit semiprime N. The solver supplies p and q as
 * witness cells. Both must be 16-bit (so the 32-bit product cannot wrap),
 * neither may be 1, and p*q must equal N. Pays `bounty` sats on success,
 * logs p and q, then HALTs so the remainder returns to the beneficiary.
 * Input: N, bounty. Output: program hex.
 */
export function factoringBountyProgram(n: number, bounty: number): string {
    // prettier-ignore
    return assemble([
        'YIELD',                                     // stage boundary
        'IN', 'IN',                                  // p q
        'OVER', 'LIT', 0xffff0000, 'AND', '0=', 'VERIFY',   // p < 2^16
        'DUP',  'LIT', 0xffff0000, 'AND', '0=', 'VERIFY',   // q < 2^16
        'OVER', 'LIT', 1, '-', 'VERIFY',             // p != 1
        'DUP',  'LIT', 1, '-', 'VERIFY',             // q != 1
        'OVER', 'OVER', '*', 'LIT', n, '-', '0=', 'VERIFY', // p*q == N
        'BOUNTY', bounty,
        'OUT', 'OUT',
        'HALT',
    ])
}

/**
 * Two-stage dependent job with commit-reveal against front-running, with
 * commit expiry against griefing and a global deadline against fund lock.
 *
 * Stage 1 (factoring, as above) pays bounty1 and stores p in mem[0].
 * Stage 2 asks for x such that HASH(x XOR p) == target; p is only known
 * after stage 1, so stage 2 depends on stage 1's answer. To stop an observer
 * from copying x out of the mempool and re-broadcasting with their own
 * address, stage 2 is split:
 *   2a. a solver commits c = HASH(x XOR WHO); mem[1] = c, mem[2] = TIME
 *   2b. a solver reveals x; the machine checks HASH(x XOR WHO) == c with the
 *       CURRENT spender's WHO, so only the committer's address collects.
 * Griefing: a bogus commit would block 2b forever, so a commit may be
 * overwritten once `commitTtl` seconds have passed (an honest committer
 * reveals in the very next transaction, well inside the TTL).
 * TTL sizing matters: if an honest reveal sits unconfirmed past the TTL, an
 * observer who read x from that pending reveal can overwrite the commit with
 * its own and collect. nLockTime cannot be set ahead of real time (miners
 * enforce it against median time past), so the attacker cannot shorten the
 * wait, but the TTL must comfortably exceed worst-case confirmation latency:
 * hours, not minutes. A confirmed reveal HALTs the machine, after which no
 * overwrite is possible. Fund lock: if
 * TIME reaches `deadline` the program HALTs and the escrow returns to the
 * beneficiary. Each stage-2 transaction first supplies a selector cell:
 * 0 = reveal, anything else = commit.
 *
 * Memory: mem[0] = p, mem[1] = commitment, mem[2] = commit time (0 = none).
 * Input: N, target, bounty1, bounty2, deadline (unix s), commitTtl (s).
 * Output: program hex.
 */
export function twoStageJobProgram(
    n: number,
    target: number,
    bounty1: number,
    bounty2: number,
    deadline: number,
    commitTtl: number
): string {
    const SIGN = 0x80000000
    // prettier-ignore
    return assemble([
        // ---- stage 1: factor N, keep p in mem[0]
        'YIELD',
        'IN', 'IN',
        'OVER', 'LIT', 0xffff0000, 'AND', '0=', 'VERIFY',
        'DUP',  'LIT', 0xffff0000, 'AND', '0=', 'VERIFY',
        'OVER', 'LIT', 1, '-', 'VERIFY',
        'DUP',  'LIT', 1, '-', 'VERIFY',
        'OVER', 'OVER', '*', 'LIT', n, '-', '0=', 'VERIFY',
        'BOUNTY', bounty1,
        'OUT',                                       // log q
        'LIT', 0, '!',                               // mem[0] = p
        'YIELD',
        // ---- stage 2 head: expired? (TIME - deadline has sign bit clear => TIME >= deadline)
        'stage2:',
        'TIME', 'LIT', deadline, '-', 'LIT', SIGN, 'AND', '0=',
        'IF', 'alive',                               // not expired -> alive
        'HALT',                                      // expired -> refund beneficiary
        'alive:',
        'IN', 'IF', 'reveal',                        // selector 0 -> reveal
        // ---- commit path: allowed if no commit yet or the old one has aged past the TTL
        'LIT', 2, '@', 'DUP', '0=', 'IF', 'aged',    // commit time != 0 -> check age
        'DROP', 'LIT', 0, 'IF', 'docommit',          // none yet -> commit
        'aged:',
        'TIME', 'SWAP', '-',                         // TIME - commitTime
        'LIT', commitTtl, '-', 'LIT', SIGN, 'AND', '0=',
        'VERIFY',                                    // tx invalid while the old commit is fresh
        'docommit:',
        'IN', 'LIT', 1, '!',                         // mem[1] = c
        'TIME', 'LIT', 2, '!',                       // mem[2] = TIME
        'YIELD',
        'LIT', 0, 'IF', 'stage2',                    // next tx re-enters the head
        // ---- reveal path
        'reveal:',
        'IN',                                        // x
        'LIT', 2, '@', 'VERIFY',                     // there must be a commit
        'DUP', 'WHO', 'XOR', 'HASH', 'LIT', 1, '@', '-', '0=', 'VERIFY', // HASH(x^WHO)==c
        'DUP', 'LIT', 0, '@', 'XOR', 'HASH', 'LIT', target, '-', '0=', 'VERIFY', // HASH(x^p)==target
        'BOUNTY', bounty2,
        'OUT',                                       // log x
        'HALT',
    ])
}
