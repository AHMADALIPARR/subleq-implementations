# Benchmark Scripts

These scripts wrap the existing Racket benchmarks for easy local and CI use.

## Prerequisites
- Racket 9.3 + Rosette
- Factor, gforth, Lean (for full matrix in `bench.rkt`)

## Scripts

| Script | Purpose |
|--------|---------|
| `run-all.sh` | Full suite (`bench/bench.rkt`). Writes timestamped markdown under `verification-results/`. |
| `verify-microcode.sh` | Times the native Rosette harness + mutation self-test. |
| `differential.sh` | Differential suite at a chosen random-program scale. |
| `crypto.sh` | SHA-256 NIST vectors + keystream generator. |

## Examples
```bash
./scripts/bench/run-all.sh --repeat 5
./scripts/bench/run-all.sh --only racket,lean
./scripts/bench/differential.sh 500
./scripts/bench/verify-microcode.sh
./scripts/bench/crypto.sh
```

Results from `run-all.sh` land in `verification-results/bench-YYYYMMDD-HHMMSS.md`.
