# k17-vm

A proof of concept of a UTXO-chained stack computer on Bitcoin SV.

One UTXO locked by `K17Machine` is one suspended process of a 36-instruction
stack machine (Koopman's Canonical Stack Machine from _Stack Computers: The
New Wave_, 1989, plus HALT, 0=, OUT, TIME, the job-bounty extension IN,
VERIFY, BOUNTY, \*, HASH, WHO, YIELD, the K17+ attested-input extension
MIN, MAX, /, SIGVERIFY, and the v2 roster extension ATTEST, ENDORSE,
PAYSLOT, VALUE). Anyone can spend the UTXO. The
spend is valid only if the next output carries the same program with the
state advanced by exactly K instructions and the spender takes no more than
the reward that the liveness Dutch auction permits at the transaction's
nLockTime. Miners verify every cycle.

Design notes live in the Obsidian vault:
`notes/projects/Stack Computers/utxo-stack-vm-brainstorm.md`.

## Layout

| Path                          | Purpose                                                                                                                           |
| ----------------------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| `src/k17/isa.ts`              | Opcode table, cell encoding, assembler, disassembler. The single source of truth for the ISA.                                     |
| `src/k17/vm.ts`               | Off-chain reference VM. Executable specification; keepers use it to compute the next state.                                       |
| `src/k17/attest.ts`           | Rabin keys, key encoding and hashing, attestation and endorsement signing.                                                        |
| `src/k17/programs.ts`         | Sample programs: Fibonacci, countdown with CALL/EXIT, heartbeat, factoring bounty, two-stage commit-reveal job, enrol-and-attest. |
| `src/contracts/k17Machine.ts` | The sCrypt contract: on-chain interpreter, Dutch auction, output enforcement.                                                     |
| `src/keeper.ts`               | Helpers to plan a cycle and build the spending transaction.                                                                       |
| `tests/vm.test.ts`            | ISA and reference VM tests.                                                                                                       |
| `tests/k17Machine.test.ts`    | On-chain tests. Every cycle is verified with the bundled Bitcoin script interpreter.                                              |

## Requirements

- Node 20 or newer.
- Docker. The sCrypt compiler ships no Apple Silicon binary, so `npm run
compile` runs it in a `linux/arm64` container. On Linux or on Intel macOS
  use `npm run compile:native` instead.

## Commands

```bash
npm install
```

```bash
npm test
```

`npm test` builds, compiles the contract (Docker), then runs both test files
against the local script interpreter. No network access and no funded keys
are needed. The deploy script and `NETWORK=testnet` are unchanged from the
sCrypt scaffold and have not been used yet.

## Job bounties

A program may read witness cells from the unlocking script (`IN`), make the
transaction invalid when a check fails (`VERIFY`), and release extra satoshis
to the spender (`BOUNTY n`). `YIELD` ends a cycle early, so a stage written as
`YIELD IN ... VERIFY ... BOUNTY n YIELD` runs atomically in one transaction
and the party that supplied the witnesses is the party that is paid. `WHO`
pushes the first four bytes of the spender's address, which lets a program
bind a commitment to the eventual payee (see `twoStageJobProgram`). K is 40
so a stage of up to 40 instructions fits in one transaction.

## Attested inputs (K17+)

`TAG VAL SIGVERIFY k` accepts the cycle only if the Rabin signature carried
in the unlocking script, under the roster key in slot `k` (four slots, fixed
at deployment), signs the eight bytes `cell(TAG) || cell(VAL)`. A missing or
wrong signature makes the transaction invalid; an empty slot or a bad index
is a fault. One signature per cycle. This separates the party that vouches
for a reading (a sensor node, an oracle) from the party that relays it and
is paid by the auction. `MIN`, `MAX` and `/` were added for the fuzzy and
aggregation programs in the companion repository `k17-dc4cd`. Signing
helpers are in `src/k17/attest.ts`; the verifier is scrypt-ts-lib's
`RabinVerifier` (3072-bit modulus).

## Roster in memory (v2 machine)

The top of memory holds the roster: 8 slots of 13 cells each, at cells
152..255 (slot k starts at cell `152 + 13k`). A slot is the SHA-256 hash of
a member's Rabin public key (32 bytes, 8 cells) followed by the member's
20-byte payout address hash (5 cells). A slot whose 8 hash cells are all
zero is empty. Programs use cells 0..151.

- Write-guard. `!` (STORE) into cell 152 or higher is a fault. Only
  `ENDORSE` writes roster cells. Slot 0 (the sponsor) is pre-filled in the
  deployment's initial memory image: `newMachine(prog, econ, time, roster,
initialMemHex)` with `withSlot(...)`.
- `TAG VAL SLOT ATTEST`. The transaction supplies a 384-byte key (`keyA`)
  and one signature. The key must hash to the slot's hash, and the
  signature must sign `"K17A" || cell(TAG) || cell(VAL)`.
- `TAG SLOT NEWSLOT ENDORSE`. The member at `SLOT` (key `keyA`) vouches for
  a new member (key `keyB`, payout `payout`). The signature must sign
  `"K17E" || cell(TAG) || cell(NEWSLOT) || sha256(keyB) || payout`. The
  contract then writes `sha256(keyB) || payout` into the empty slot
  `NEWSLOT`. The message binds `NEWSLOT`, so a relayer cannot move the
  new member to another slot.
- `N SLOT PAYSLOT`. Pays `N` sats to the slot's payout address in output 2
  of the cycle transaction, whoever relays it.
- `VALUE`. Pushes the balance of the machine output being spent (mod 2^32).

`SIGVERIFY`, `ATTEST` and `ENDORSE` share one signature per cycle.
`src/k17/programs.ts` has `enrolAndAttestProgram`: the sponsor enrols a
landowner in cycle 1, and in cycle 2 the landowner attests a reading and
is paid a bounty.

A fault halts the machine and releases the balance to the beneficiary. An
invalid transaction cannot be mined; the machine waits for a correct one.
A condition that the program causes is a fault. A condition that the
witness (keys, signatures) causes makes the transaction invalid.

| Instruction | Fault (halt, refund the beneficiary)                                                                                                                              | Invalid transaction                                                                                                |
| ----------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------ |
| `!`         | address 152 or higher (roster), stack underflow                                                                                                                   | never                                                                                                              |
| `ATTEST`    | underflow, `SLOT` 8 or higher, empty slot                                                                                                                         | second signature in the cycle, missing key or signature, key not 384 bytes, key hash not the slot's, bad signature |
| `ENDORSE`   | underflow, `SLOT` or `NEWSLOT` 8 or higher, empty `SLOT`, filled `NEWSLOT`                                                                                        | as `ATTEST`, plus `keyB` not 384 bytes, payout not 20 bytes                                                        |
| `PAYSLOT`   | underflow, `SLOT` 8 or higher, empty slot, `N` = 0, second `PAYSLOT` in the cycle, `N` larger than the balance less the reward less 1 sat. The payout is dropped. | never                                                                                                              |
| `VALUE`     | full data stack                                                                                                                                                   | never                                                                                                              |

The reference VM does not know the auction reward, so it cannot see the
last `PAYSLOT` fault. `planCycle` checks it with `rewardAt` and marks the
cycle halted with no payout, as the contract does.

## Measurements (K = instructions per cycle)

| K   | Handlers | Locking script | Cycle transaction |
| --- | -------- | -------------- | ----------------- |
| 1   | 21       | 9 026 bytes    | 9 574 bytes       |
| 4   | 21       | 16 247 bytes   | 16 802 bytes      |
| 40  | 28       | 159 003 bytes  | about 160 KB      |
| 40  | 32       | 202 468 bytes  | about 204 KB      |
| 40  | 36       | 362 432 bytes  | about 363 KB      |

Roughly 2.4 KB (21 handlers) to 3.8 KB (28 handlers) to 4.9 KB (32 handlers,
of which SIGVERIFY alone is about 0.8 KB) to 9 KB (36 handlers, with the
roster in memory) of script per unrolled instruction, plus a fixed part
(preimage verification, state tail with the memory image, output
construction). The cycle transaction column is the final (halting) cycle.
A cycle that continues also carries the next state output, so it is about
twice the locking script: the enrolment cycle of `enrolAndAttestProgram` is
725 470 bytes at K=40. Fibonacci(10) is 247
instructions: 62 cycles at K=4, 7 cycles at K=40. The dispatch chain is the
obvious optimisation target.

## Economics knob

`K17Machine.rewardFor(elapsed)` is the whole economic policy. It is linear
with a cap in this prototype: `min(rewardMin + slope * elapsed, rewardMax)`.
The keeper reads elapsed time from nLockTime, which miners enforce as a
lower bound on block time, so claiming a larger reward means waiting longer
before the transaction can be mined.
