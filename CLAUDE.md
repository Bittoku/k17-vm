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
  `SIGVERIFY` with a missing or wrong signature invalidate the transaction. Do not blur that
  distinction.
- `SIGVERIFY` verifies a Rabin signature (scrypt-ts-lib `RabinVerifier`, security level 6);
  `src/k17/attest.ts` signs with the same parameters. One signature per cycle.
- The contract requires the machine at input index 0 (`this.prevouts`). Keep it.
- `K17Machine.K` is a compile-time constant; raising it multiplies script size by about
  4.9 KB per instruction with the current 32 handlers (202 468 bytes at K=40).
- The companion repository `../k17-dc4cd` depends on this package via `file:../k17-vm` and
  imports the compiled artifact from `artifacts/`; after an ISA change, rebuild and recompile
  here before running its tests.
- Commit messages carry no AI attribution lines (user rule).

## IP notes

- `docs/K17-DEFENSIVE-PUBLICATION.md` is to be published only after the related provisional
  (script-verify candidate-25) is filed. See that candidate's `PUBLICATION-PLAN.md`.
- nChain US 12,020,249 B2 and continuations read on this architecture. Freedom-to-operate
  opinion required before any commercial use.
