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
  `SIGVERIFY`, `ATTEST` or `ENDORSE` with a missing or wrong signature or key invalidate the
  transaction. Do not blur that distinction.
- `SIGVERIFY` verifies a Rabin signature (scrypt-ts-lib `RabinVerifier`, security level 6);
  `src/k17/attest.ts` signs with the same parameters. One signature per cycle, shared by
  `SIGVERIFY`, `ATTEST` and `ENDORSE`: a second one in a cycle invalidates the transaction.
- Roster in memory (v2 machine): 8 slots of 13 cells at cells 152..255 (slot k at
  `152 + 13k`): 8 cells of SHA-256 key hash, then 5 cells of payout address hash. All-zero
  hash cells mean an empty slot. `!` into cell 152 or higher faults; only `ENDORSE` writes
  roster cells. Slot 0 is pre-filled through `newMachine(..., initialMemHex)`. The
  endorsement message binds the target slot:
  `"K17E" || cell(TAG) || cell(NEWSLOT) || sha256(keyB) || payout`.
- `step(keeper, witness, sigS, sigPad, keyA, keyB, payout)`: `keyA` is the 384-byte key that
  signs for `ATTEST` or sponsors for `ENDORSE`, `keyB` the new member's key, `payout` the new
  member's 20-byte payout hash. Pass empty byte strings when unused.
- `PAYSLOT` errors are faults, never invalid transactions: `N == 0`, a second `PAYSLOT` in a
  cycle, and an unaffordable `PAYSLOT` (`value - reward - N < 1`) halt, drop the payout and
  refund the beneficiary. The VM does not know the reward, so `planCycle` detects the
  unaffordable case. Keep `assert` for signature and key conditions only.
- The contract requires the machine at input index 0 (`this.prevouts`). Keep it.
- `K17Machine.K` is a compile-time constant; raising it multiplies script size by about
  9 KB per instruction with the current 36 handlers (362 432 bytes at K=40). A cycle that
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
