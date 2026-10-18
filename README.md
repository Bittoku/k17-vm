# k17-vm

A proof of concept of a UTXO-chained stack computer on Bitcoin SV.

One UTXO locked by `K17Machine` is one suspended process of a 21-instruction
stack machine (Koopman's Canonical Stack Machine from *Stack Computers: The
New Wave*, 1989, plus HALT, 0=, OUT and TIME). Anyone can spend the UTXO. The
spend is valid only if the next output carries the same program with the
state advanced by exactly K instructions and the spender takes no more than
the reward that the liveness Dutch auction permits at the transaction's
nLockTime. Miners verify every cycle.

Design notes live in the Obsidian vault:
`notes/projects/Stack Computers/utxo-stack-vm-brainstorm.md`.

## Layout

| Path | Purpose |
|---|---|
| `src/k17/isa.ts` | Opcode table, cell encoding, assembler, disassembler. The single source of truth for the ISA. |
| `src/k17/vm.ts` | Off-chain reference VM. Executable specification; keepers use it to compute the next state. |
| `src/k17/programs.ts` | Sample programs: Fibonacci, countdown with CALL/EXIT, heartbeat. |
| `src/contracts/k17Machine.ts` | The sCrypt contract: on-chain interpreter, Dutch auction, output enforcement. |
| `src/keeper.ts` | Helpers to plan a cycle and build the spending transaction. |
| `tests/vm.test.ts` | ISA and reference VM tests. |
| `tests/k17Machine.test.ts` | On-chain tests. Every cycle is verified with the bundled Bitcoin script interpreter. |

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

## Measurements (K = instructions per cycle)

| K | Locking script | Cycle transaction |
|---|---|---|
| 1 | 9 026 bytes | 9 574 bytes |
| 4 | 16 247 bytes | 16 802 bytes |

About 2.4 KB of script per unrolled instruction plus about 6.6 KB fixed
(preimage verification, state tail with a 256-byte memory image, output
construction). Fibonacci(10) is 247 instructions: 62 cycles at K=4.

## Economics knob

`K17Machine.rewardFor(elapsed)` is the whole economic policy. It is linear
with a cap in this prototype: `min(rewardMin + slope * elapsed, rewardMax)`.
The keeper reads elapsed time from nLockTime, which miners enforce as a
lower bound on block time, so claiming a larger reward means waiting longer
before the transaction can be mined.
