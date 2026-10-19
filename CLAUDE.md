# k17-vm — agent notes

Proof of concept of a UTXO-chained stack machine on Bitcoin SV (sCrypt / TypeScript).
Read `README.md` first; design and research documents live in the Obsidian vault at
`notes/projects/Stack Computers/`, not here. Only code, tests, configs and the defensive
publication belong in this repo.

## Working rules

- `npm test` builds, compiles the contract in a `linux/arm64` Docker container (the sCrypt
  compiler ships no Apple Silicon binary) and runs both test files against the bundled Bitcoin
  script interpreter. No network, no funded keys. Every on-chain test must keep calling
  `tx.verifyInputScript` so the differential check against the reference VM stays real.
- `src/k17/isa.ts` is the single source of truth for the ISA. A change there must be mirrored
  in `src/k17/vm.ts` (reference VM) and `src/contracts/k17Machine.ts` (on-chain interpreter),
  and covered by a test in both `tests/vm.test.ts` and `tests/k17Machine.test.ts`.
- Faults halt the machine and release funds; `IN` without a witness, `VERIFY` of zero and
  `SIGVERIFY`, `ATTEST`, `ENDORSE`, `ATTESTM`, `ADMIT` or `REMOVE` with a missing or wrong
  signature or key, and a missing or wrong tree proof, invalidate the transaction. Do not blur
  that distinction. A second signature instruction in a cycle is a fault (v3.1), not an
  invalid transaction.
- `SIGVERIFY` verifies a Rabin signature (scrypt-ts-lib `RabinVerifier`, security level 6);
  `src/k17/attest.ts` signs with the same parameters. One signature per cycle, shared by
  `SIGVERIFY`, `ATTEST`, `ENDORSE`, `ATTESTM`, `ADMIT` and `REMOVE`: a second one in a cycle
  is a fault (v3.1). The contract folds `sigUsed` into each handler's existing fault condition
  (`if (<underflow> || ... || sigUsed) halted = true`); do not wrap handler bodies in a new
  `if`/`else`, which costs about 14 KB at K=40. The VM returns `fault` for `sigUsed` before any
  `need_witness` check.
- Roster in memory (v2 machine): 8 slots of 13 cells at cells 152..255 (slot k at
  `152 + 13k`): 8 cells of SHA-256 key hash, then 5 cells of payout address hash. All-zero
  hash cells mean an empty slot. `!` into cell 152 or higher faults; only `ENDORSE` writes
  roster cells. Slot 0 is pre-filled through `newMachine(..., initialMemHex)`.
- Instance binding: the contract has an immutable 32-byte `instanceId` (random by default in
  `newMachine`; tests pass a fixed id; any other length faults the machine at its first
  cycle). ATTEST signs
  `"K17M" || instanceId || cell(TAG) || cell(VAL)`; ENDORSE signs
  `"K17E" || instanceId || cell(TAG) || cell(NEWSLOT) || sha256(keyB) || payout`. SIGVERIFY
  keeps `"K17A" || cell(TAG) || cell(VAL)`. Attesters read `instanceId` from the deployed
  machine before they sign.
- `step` has 10 parameters:
  `step(keeper, witness, sigS, sigPad, keyA, keyB, payout, leafPre, proof, leafIndex)`. `keyA`
  is the 384-byte key that signs for `ATTEST` or `ATTESTM`, sponsors for `ENDORSE`, or is the
  sponsor key for `ADMIT` and `REMOVE`; `keyB` the new member's key, `payout` the new member's
  20-byte payout hash (`ENDORSE`, `ADMIT`). `leafPre`, `proof` and `leafIndex` are the cycle's
  one tree proof (60-byte leaf preimage, or empty for `ADMIT`; 512 bytes of siblings, level 0
  first; index in `[0, 65536)`). Pass empty byte strings and 0 when unused.
- Tree roster (v3 machine): state `sponsorKeyHash` (immutable), `rosterRoot`, `rosterSeq`,
  `logHash`. Handlers in the unrolled loop only record (`treeOp`, the ADMIT/REMOVE operand cells, flags); the proof,
  the `ADMIT`/`REMOVE` keys and message, and the new root are checked and built once after the
  loop, before the one Rabin verification. Rules:
  - Programs derive `ROUND` (for `PAYLEAF` and `ADMIT`) from `TIME`, never from `IN`.
  - One tree instruction per cycle (`MEMBER`, `ADMIT`, `REMOVE`); a second one is a fault.
    `LASTROUND`, `ATTESTM` and `PAYLEAF` without `MEMBER` fault.
  - Witness-caused failures (proof, index, leaf preimage, key, payout, signature, `ROUND` not
    above `lastRound`) are `assert`s; only stack and tree-op conditions in the loop fault.
  - Sponsor messages (`H` = `instanceId || cell(TAG) || cell(rosterSeq) || cell(leafIndex)`):
    `ADMIT` signs `"K17D" || H || sha256(keyB) || payout`; `REMOVE` signs
    `"K17X" || H || keyHash32 || payout20` (v3.1: `leafPre[0..52]`, so `lastRound` is not
    signed and a `PAYLEAF` does not invalidate a pending removal). Each adds 1 to
    `rosterSeq`, so a sponsor signature cannot be replayed.
  - `PAYSLOT` and `PAYLEAF` share the one payment per cycle; the signature instructions share
    the one signature per cycle.
- `PAYSLOT` errors are faults, never invalid transactions: a second `PAYSLOT` in a cycle
  (checked first, whatever its operands), `N == 0`, and `N > value - 1` halt, drop the payout
  and refund the beneficiary. A later unrelated fault in the same cycle keeps the payout. The
  slot payout has priority over the keeper reward: the reward is clamped to
  `value - 1 - N` (down to 0), so a keeper cannot make a PAYSLOT fail by waiting. The VM does
  not do the balance check; `planCycle`/`rewardAt` mirror the contract. Keep `assert` for
  signature and key conditions only.
- A program that takes `SLOT` (or `N`) from a witness must check it with `VERIFY` (in range
  and filled) before `ATTEST` or `PAYSLOT`; otherwise any keeper can halt the machine with a
  bad slot number and still collect the auction reward.
- The same applies to `MEMBER`'s `IDX` and `LASTROUND`'s value: the relayer chooses which
  member it proves, so both are relayer-chosen. Do not use them as a memory address or a loop
  bound without bounding them first (for example with `VERIFY`), as for `SLOT`.
- The contract requires the machine at input index 0 (`this.prevouts`). Keep it.
- Freeze escape (v3.1): immutable `deadMan` (seconds, 0 = off; constructor argument after
  `rewardMax`, `econ.deadMan` in `newMachine`). At the top of `step`, before the loop,
  `deadMan > 0 && locktime >= lastTime + deadMan` sets `halted`, so the cycle takes the refund
  path with no witness, signature or tree check. The VM mirrors it in `stepK`/`run` via
  `StepEnv.deadMan` and `StepEnv.lastTime` (`deadManDue`); `planCycle` passes both and reports
  `CyclePlan.deadManHalt`.
- `MIN_STEP` = 60 s: a cycle that keeps the machine alive needs
  `locktime >= lastTime + MIN_STEP` (an `assert` on the alive path only). Halting cycles are
  exempt, so a refund is never blocked. It is a transaction rule, not a VM rule: `planCycle`
  enforces it. Tests must space live cycles at least 60 s apart, the first one 60 s after the
  deployment time `T0`.
- `K17Machine.K` is a compile-time constant; raising it multiplies script size by about
  12 KB per instruction with the current 43 handlers (469 918 bytes at K=40). A cycle that
  keeps the machine alive is about twice that (the preimage plus the next state output).
- The companion repository `../k17-dc4cd` depends on this package via `file:../k17-vm` and
  imports the compiled artifact from `artifacts/`; after an ISA change, rebuild and recompile
  here before running its tests.
- Commit messages carry no AI attribution lines (user rule).

## IP notes

- `docs/K17-DEFENSIVE-PUBLICATION.md` is published FIRST (decision 2026-10-18): TDCommons, this
  repository made public, on-chain hash anchor, each on Dave's explicit go. Do not edit the file;
  its SHA-256 is recorded in script-verify candidate-25. A US filing stays open for 12 months
  from the publication date under 35 USC 102(b)(1)(A) and must be made by a registered patent
  practitioner. See candidate-25 `PUBLICATION-PLAN.md`.
- nChain US 12,020,249 B2 and continuations read on this architecture. Freedom-to-operate
  opinion required before any commercial use.
