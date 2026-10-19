# k17-vm

A proof of concept of a UTXO-chained stack computer on Bitcoin SV.

One UTXO locked by `K17Machine` is one suspended process of a 43-instruction
stack machine (Koopman's Canonical Stack Machine from _Stack Computers: The
New Wave_, 1989, plus HALT, 0=, OUT, TIME, the job-bounty extension IN,
VERIFY, BOUNTY, \*, HASH, WHO, YIELD, the K17+ attested-input extension
MIN, MAX, /, SIGVERIFY, the v2 roster extension ATTEST, ENDORSE,
PAYSLOT, VALUE, and the v3 tree roster extension MEMBER, LASTROUND,
ATTESTM, PAYLEAF, ADMIT, REMOVE, OUTH). Anyone can spend the UTXO. The
spend is valid only if the next output carries the same program with the
state advanced by exactly K instructions and the spender takes no more than
the reward that the liveness Dutch auction permits at the transaction's
nLockTime. Miners verify every cycle.

Design notes live in the Obsidian vault:
`notes/projects/Stack Computers/utxo-stack-vm-brainstorm.md`.

## Layout

| Path                          | Purpose                                                                                                                                                  |
| ----------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `src/k17/isa.ts`              | Opcode table, cell encoding, assembler, disassembler. The single source of truth for the ISA.                                                            |
| `src/k17/vm.ts`               | Off-chain reference VM. Executable specification; keepers use it to compute the next state.                                                              |
| `src/k17/attest.ts`           | Rabin keys, key encoding and hashing, attestation, endorsement, admission and removal signing.                                                           |
| `src/k17/smt.ts`              | Sparse Merkle tree of the roster (depth 16): leaf encoding, proofs, roots.                                                                               |
| `src/k17/programs.ts`         | Sample programs: Fibonacci, countdown with CALL/EXIT, heartbeat, factoring bounty, two-stage commit-reveal job, enrol-and-attest, tree-consortium smoke. |
| `src/contracts/k17Machine.ts` | The sCrypt contract: on-chain interpreter, Dutch auction, output enforcement.                                                                            |
| `src/keeper.ts`               | Helpers to plan a cycle and build the spending transaction.                                                                                              |
| `tests/vm.test.ts`            | ISA and reference VM tests.                                                                                                                              |
| `tests/k17Machine.test.ts`    | On-chain tests. Every cycle is verified with the bundled Bitcoin script interpreter.                                                                     |

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
is a fault. One signature per cycle: a second signature instruction in the
cycle is a fault (v3.1). This separates the party that vouches
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
  initial memory image of the deployment: pass `initialMemHex` to
  `newMachine` and build it with `withSlot`.
- Instance id. Each machine has an immutable 32-byte `instanceId`.
  `newMachine` makes a random one unless you give one. `ATTEST` and
  `ENDORSE` signatures include it, so a signature for one machine is not
  valid on another machine. An attester must read `instanceId` from the
  deployed machine before it signs.
- `TAG VAL SLOT ATTEST`. The transaction supplies a 384-byte key (`keyA`)
  and one signature. The key must hash to the slot's hash, and the
  signature must sign `"K17M" || instanceId || cell(TAG) || cell(VAL)`.
  (`SIGVERIFY` keeps its own `"K17A"` message.)
- `TAG SLOT NEWSLOT ENDORSE`. The member at `SLOT` (key `keyA`) vouches for
  a new member (key `keyB`, payout `payout`). The signature must sign this
  message:

  ```
  "K17E" || instanceId || cell(TAG) || cell(NEWSLOT) || sha256(keyB) || payout
  ```

  The contract then writes `sha256(keyB) || payout` into the
  empty slot `NEWSLOT`. The message includes `NEWSLOT`, so a relayer
  cannot move the new member to a different slot.

- `N SLOT PAYSLOT`. Pays `N` sats to the slot's payout address, whoever
  relays the cycle. The payout output comes after the keeper's reward
  output. The payout has priority: if the balance cannot pay the full
  reward, the payout and one satoshi, the keeper's reward becomes smaller
  (to zero, when there is no reward output). A late keeper can thus not
  make the payout fail.
- `VALUE`. Pushes the balance of the machine output being spent (mod 2^32).

`SIGVERIFY`, `ATTEST` and `ENDORSE` share one signature per cycle. A
second one in the cycle is a fault (v3.1).
`src/k17/programs.ts` has `enrolAndAttestProgram`: the sponsor enrols a
landowner in cycle 1, and in cycle 2 the landowner attests a reading and
gets a bounty.

A fault halts the machine and releases the balance to the beneficiary. An
invalid transaction cannot be mined; the machine waits for a correct one.
A condition that the program causes is a fault. A condition that the
witness (keys, signatures) causes makes the transaction invalid.

| Instruction | Fault (halt, refund the beneficiary)                                                                                                                                                                          | Invalid transaction                                                                 |
| ----------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------- |
| `!`         | address 152 or higher (roster), stack underflow                                                                                                                                                               | never                                                                               |
| `ATTEST`    | underflow, `SLOT` 8 or higher, second signature in the cycle, empty slot                                                                                                                                      | missing key or signature, key not 384 bytes, key hash not the slot's, bad signature |
| `ENDORSE`   | underflow, `SLOT` or `NEWSLOT` 8 or higher, second signature in the cycle, empty `SLOT`, filled `NEWSLOT`                                                                                                     | as `ATTEST`, plus `keyB` not 384 bytes, payout not 20 bytes                         |
| `PAYSLOT`   | always a fault, and the payout is dropped: a second `PAYSLOT` in the cycle (checked first, whatever its operands), underflow, `SLOT` 8 or higher, empty slot, `N` = 0, `N` larger than the balance less 1 sat | never                                                                               |
| `VALUE`     | full data stack                                                                                                                                                                                               | never                                                                               |

A fault that comes later in the cycle, after a `PAYSLOT` that succeeded,
does not drop that payout.

A program that takes `SLOT` (or `N`) from a witness with `IN` must check
it with `VERIFY` (in range and filled) before `ATTEST` or `PAYSLOT`. If it
does not, any keeper can supply a bad slot number, halt the machine with a
fault, and still collect the auction reward.

The reference VM does not know the balance rules of the contract, so it
cannot see the last `PAYSLOT` fault. `planCycle` checks it and calculates
the smaller reward with `rewardAt`, as the contract does.

## Tree roster (v3 machine)

The v3 machine keeps its roster in a sparse Merkle tree, not in memory. The
tree has depth 16, so it has 65 536 leaves. Only the root is in the machine
state. Each cycle can carry one Merkle proof in the unlocking script.

### State

| Property         | Kind      | Content                                                                                                     |
| ---------------- | --------- | ----------------------------------------------------------------------------------------------------------- |
| `sponsorKeyHash` | immutable | SHA-256 of the sponsor's 384-byte Rabin key. The sponsor signs `ADMIT` and `REMOVE`. All zeros: no sponsor. |
| `rosterRoot`     | mutable   | Root of the roster tree. The empty tree has root `EMPTY_HASHES[16]`.                                        |
| `rosterSeq`      | mutable   | Number of `ADMIT` and `REMOVE` operations so far. It starts at 0.                                           |
| `logHash`        | mutable   | Running hash of the `OUTH` cells. It starts at 32 zero bytes.                                               |

### Leaf and proof format

- Leaf preimage (60 bytes): `keyHash(32) || payout(20) || cell(lastRound) || cell(flags)`.
  `keyHash` is the SHA-256 of the member's 384-byte Rabin key.
- Leaf hash: `sha256("K17L" || leafPre)`. An empty leaf has the hash of 32
  zero bytes.
- Proof (512 bytes): 16 sibling hashes of 32 bytes. The level-0 sibling is
  first.
- Leaf index: an integer in `[0, 65536)`. Bit k of the index is 1 when the
  node at level k is the right child. Then the parent is
  `sha256(sibling || node)`. Else the parent is `sha256(node || sibling)`.
- `step` takes the proof as its last three arguments: `leafPre`, `proof`
  and `leafIndex`. For `ADMIT`, `leafPre` is empty, because the leaf must
  be empty. When the cycle runs no tree instruction, pass `''`, `''` and 0.

`src/k17/smt.ts` builds the tree, the proofs and the roots off chain.

### Instructions

| Instruction | Stack effect   | Function                                                                                                               |
| ----------- | -------------- | ---------------------------------------------------------------------------------------------------------------------- |
| `MEMBER`    | `-- IDX`       | Checks the proof against `rosterRoot` and binds that member for the cycle. Pushes the leaf index.                      |
| `LASTROUND` | `-- R`         | Pushes the bound member's `lastRound`.                                                                                 |
| `ATTESTM`   | `TAG VAL --`   | Checks a reading that the bound member signed with `keyA`.                                                             |
| `PAYLEAF`   | `N ROUND --`   | Pays `N` sats to the bound member and sets its `lastRound` to `ROUND`. The root changes.                               |
| `ADMIT`     | `TAG ROUND --` | The sponsor puts a new member (`keyB`, `payout`) into an empty leaf with `lastRound` = `ROUND`. Adds 1 to `rosterSeq`. |
| `REMOVE`    | `TAG --`       | The sponsor empties an occupied leaf. Adds 1 to `rosterSeq`.                                                           |
| `OUTH`      | `N1 --`        | Sets `logHash` to the SHA-256 of `logHash` followed by `cell(N1)`. It does not write the output log.                   |

### Signed messages

`I` is the machine's 32-byte `instanceId`. `seq` is `rosterSeq` before the
cycle.

```
ATTESTM  "K17T" || I || cell(TAG) || cell(VAL)
ADMIT    "K17D" || I || cell(TAG) || cell(seq) || cell(leafIndex) || sha256(keyB) || payout
REMOVE   "K17X" || I || cell(TAG) || cell(seq) || cell(leafIndex) || keyHash || payout
```

`ADMIT` and `REMOVE` messages include `rosterSeq`, and each of them adds 1
to it. Thus a sponsor signature is valid for one operation only. If a
member is removed, nobody can replay the old admission. The `ADMIT`
message includes the leaf index and the new member's key and payout, so a
relayer cannot move the member or change its key.

The `REMOVE` message ends with the removed member's `keyHash` (32 bytes)
and `payout` (20 bytes). These are the first 52 bytes of `leafPre`. It does
not include `lastRound`. `PAYLEAF` changes `lastRound` but not these 52
bytes. Thus a removal that the sponsor signs before a payment to the member
is still valid after that payment. The sponsor does not have to wait for the
payments of a round to stop (v3.1).

### Fault or invalid transaction

The rule of the v2 roster applies. A condition that the program causes is a
fault. A condition that the witness (proof, keys, signature) causes makes
the transaction invalid.

| Instruction | Fault (halt, refund the beneficiary)                                                                                                                                      | Invalid transaction                                                                                                                                                                 |
| ----------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `MEMBER`    | a second tree instruction in the cycle, full data stack (the proof is checked first)                                                                                      | no proof, `leafPre` not 60 bytes, index out of range, proof not 512 bytes, proof does not lead to `rosterRoot`                                                                      |
| `LASTROUND` | no bound member, full data stack                                                                                                                                          | never                                                                                                                                                                               |
| `ATTESTM`   | underflow, no bound member, second signature in the cycle                                                                                                                 | missing key or signature, key hash not the leaf's, bad signature                                                                                                                    |
| `PAYLEAF`   | the payout is dropped: a second payment in the cycle (`PAYSLOT` or `PAYLEAF`, checked first), underflow, no bound member, `N` = 0, `N` larger than the balance less 1 sat | `ROUND` not above the member's `lastRound`                                                                                                                                          |
| `ADMIT`     | underflow, a second tree instruction in the cycle, second signature in the cycle                                                                                          | missing or wrong proof or index, `leafPre` not empty (occupied leaf), payout not 20 bytes, `keyB` not 384 bytes, `keyA` not the sponsor's, bad signature (also a wrong `rosterSeq`) |
| `REMOVE`    | underflow, a second tree instruction in the cycle, second signature in the cycle                                                                                          | missing or wrong proof or index, `leafPre` not 60 bytes (empty leaf), `keyA` not the sponsor's, bad signature                                                                       |
| `OUTH`      | underflow                                                                                                                                                                 | never                                                                                                                                                                               |

### Rules for each cycle

- One tree instruction. `MEMBER`, `ADMIT` and `REMOVE` share one proof. A
  second one in the cycle is a fault.
- One signature. `SIGVERIFY`, `ATTEST`, `ENDORSE`, `ATTESTM`, `ADMIT` and
  `REMOVE` share it. A second one is a fault: the machine halts and the
  beneficiary is refunded (v3.1). Before v3.1 it made the transaction
  invalid, and no witness could repair that, so a program could freeze its
  own funds. The contract tests the condition together with the stack
  underflow of each of these instructions.
- One payment. `PAYSLOT` and `PAYLEAF` share it. A second one is a fault
  and drops the payout.
- `MEMBER`'s `IDX` and `LASTROUND`'s value are chosen by the relayer: it
  chooses which member it proves. Do not use them as a memory address or a
  loop bound without bounding them first (for example with `VERIFY`), as
  for a `SLOT` from `IN`.
- Clock. A cycle that keeps the machine alive must have nLockTime at least
  `lastTime + 60` (`MIN_STEP`, v3.1). A cycle that halts (`HALT`, a fault
  or the dead-man) needs only nLockTime at or after `lastTime`. Trade-off:
  nLockTime = MTP - 1 gives about one live cycle per block and no clock
  lag; steps of exactly 60 seconds give up to about 10 cycles per block but
  let `lastTime` trail MTP, which brings the dead-man closer in real time.
  Any honest cycle at MTP - 1 removes the lag.
- Dead-man. When the machine has `deadMan` > 0 and nLockTime is at least
  `lastTime + deadMan`, the cycle halts before its first instruction (v3.1).
  See "Freeze escape" below.
- Get `ROUND` from `TIME`, never from `IN`. The keeper controls `IN`. The
  contract does not let nLockTime go backwards. A member admitted in round
  r can be paid in round r + 1 at the earliest, because `PAYLEAF` requires
  `ROUND` above `lastRound`.

`src/k17/programs.ts` has `treeConsortiumSmokeProgram`. In cycle 1 the
sponsor admits a member. In cycle 2 the member attests a reading, the
reading goes into `logHash`, and the member gets a bounty.

### Cost

The contract checks the proof once per cycle, after the instruction loop.
The check walks the proof from the old leaf to `rosterRoot`: 16 SHA-256
operations. `PAYLEAF`, `ADMIT` and `REMOVE` change the leaf, so the
contract walks the same proof again from the new leaf to get the new root.
Thus a cycle with `PAYLEAF`, `ADMIT` or `REMOVE` costs 32 SHA-256
operations, and a cycle with only `MEMBER` costs 16.

Each `PAYLEAF` changes the root. Thus readings on one machine are
sequential: one reading per cycle. A cycle that keeps the machine alive is
about twice the locking script (see the measurements below). A round of
1 000 members is 1 000 chained cycle transactions, with their fees. The
design is correct at that size, but the cost is too high until the
interpreter gets smaller or one cycle can carry more than one reading. v1
is for hundreds of members, one reading per member per round, and rounds of
a day or more.

## Freeze escape (v3.1)

K17 must never let a program lock the deposit. Before v3.1 two cases broke
that rule. Both come from the program, not from the relayer:

1. A second signature instruction in one cycle. It was an `assert`, and no
   witness can satisfy it. It is now a fault (see "Rules for each cycle").
2. A program that waits for a witness that nobody can supply: `IN` with no
   relayer that has the data, or `MEMBER` on a tree with no members.

For case 2 the machine has an immutable dead-man interval, `deadMan`, in
seconds. It is set at deployment (`newMachine(prog, { ...econ, deadMan })`);
0 (the default) disables it. At the top of `step`, before the instruction
loop:

```
if (deadMan > 0 && nLockTime >= lastTime + deadMan) halted = true
```

The cycle then takes the fault path: the balance goes to the beneficiary
and the keeper gets its auction reward. No instruction runs, so no witness,
signature or tree proof is checked. Any keeper can send it. The checks that
stay are the ones that every cycle has: prevouts, machine at input 0,
nSequence, nLockTime is a unix time, nLockTime not before `lastTime`, and
the outputs. The reference VM does the same check in `stepK` and `run` when
`StepEnv` has `deadMan` and `lastTime`; `planCycle` passes both and sets
`CyclePlan.deadManHalt`.

Minimum clock advance. `lastTime` is the nLockTime of the last cycle, and
consensus does not bound nLockTime from below. Without a rule, a keeper that
can drive the machine could keep `nLockTime = lastTime` on every cycle.
Then `lastTime` would fall behind real time, and the dead-man would become
due earlier in real time than `deadMan` after the last real progress. Thus a cycle that keeps the machine alive
must advance the clock by `MIN_STEP` = 60 seconds:
`nLockTime >= lastTime + 60`. The contract asserts this on the alive path
only; a halting cycle is exempt, so the rule never blocks a refund.
`planCycle` refuses a live cycle that breaks it. The rule also applies to
the first cycle: it must be at least 60 seconds after the deployment time.
Throughput and clock lag. Consensus bounds nLockTime above by the median
time past (MTP) of the chain. A keeper that uses `nLockTime = MTP - 1` gets
about one live cycle per block, and `lastTime` does not lag. A keeper that
steps by exactly `lastTime + 60` can get up to about 10 cycles per block
(MTP moves about 600 seconds per block), but `lastTime` then trails MTP,
and this lag brings the dead-man closer in real time. Any honest cycle at `MTP - 1` removes the lag. The measurements below are
per cycle; a machine's throughput is bounded by this clock rule, not by
script size.

Choosing `deadMan`. `deadMan` counts on the chain's MTP clock, not on wall
time. When `MTP - 1 >= lastTime + deadMan`, the dead-man cycle can be
mined, and from then on a kill is the profitable move for any keeper: it
pays the same capped reward as a live cycle with about half the fee (there
is no state output). Honest keepers cannot push `lastTime` past MTP, so an
MTP jump of `deadMan` or more lets any keeper kill a healthy machine.
Choose `deadMan` as a multiple of the round length, for example 30 days for
daily rounds. `newMachine` refuses a `deadMan` below `DEAD_MAN_FLOOR`
(6 hours) unless `econ.allowShortDeadMan` is true (for tests), and always
refuses a value from 1 to 60, because then no cycle could stay alive.

A keeper that pins the clock with 60-second steps must still win every
cycle and pay the fee of each, and the result is only an early refund of
the beneficiary's own deposit.

## Measurements (K = instructions per cycle)

Throughput is set by the clock as well as by size (v3.1): about one live
cycle per block at nLockTime = MTP - 1, or up to about 10 per block with
60-second steps at the cost of clock lag (see "Freeze escape").

| K   | Handlers                                | Locking script | Cycle transaction |
| --- | --------------------------------------- | -------------- | ----------------- |
| 1   | 21                                      | 9 026 bytes    | 9 574 bytes       |
| 4   | 21                                      | 16 247 bytes   | 16 802 bytes      |
| 40  | 28                                      | 159 003 bytes  | about 160 KB      |
| 40  | 32                                      | 202 468 bytes  | about 204 KB      |
| 40  | 43                                      | 469 386 bytes  | about 470 KB      |
| 40  | 43 (v3.1, second signature faults)      | 469 666 bytes  | about 470 KB      |
| 40  | 43 (v3.1, plus dead-man and `MIN_STEP`) | 469 918 bytes  | about 470 KB      |

Roughly 2.4 KB (21 handlers) to 3.8 KB (28 handlers) to 4.9 KB (32 handlers,
of which SIGVERIFY alone is about 0.8 KB) to 9 KB (36 handlers, with the
roster in memory) to about 12 KB (43 handlers, with the tree roster) of
script per unrolled instruction, plus a fixed part
(preimage verification, state tail with the memory image, output
construction). The cycle transaction column is the final (halting) cycle.
A cycle that continues also carries the next state output, so it is about
twice the locking script: the enrolment cycle of `enrolAndAttestProgram` is
939 311 bytes at K=40 (43 handlers). Set `K17_SIZES=1` to print these sizes during
`npm test`. Fibonacci(10) is 247
instructions: 62 cycles at K=4, 7 cycles at K=40. The dispatch chain is the
obvious optimisation target.

## Economics knob

`K17Machine.rewardFor(elapsed)` is the whole economic policy. It is linear
with a cap in this prototype: `min(rewardMin + slope * elapsed, rewardMax)`.
The keeper reads elapsed time from nLockTime, which miners enforce as a
lower bound on block time, so claiming a larger reward means waiting longer
before the transaction can be mined. Because of `MIN_STEP` (v3.1), the
smallest reward of a cycle that keeps the machine alive is
`rewardMin + 60 * slope`.
