<!-- SPDX-License-Identifier: AGPL-3.0-or-later -->
# SUBLEQ Implementations

[![CI](https://github.com/AHMADALIPARR/subleq-implementations/actions/workflows/formal-verification.yml/badge.svg)](https://github.com/AHMADALIPARR/subleq-implementations/actions/workflows/formal-verification.yml)
[![License: AGPL v3](https://img.shields.io/badge/License-AGPL_v3-blue.svg)](LICENSE)

Collection of SUBLEQ (Subtract and Branch if Less or Equal) virtual machine
implementations and related code.

## Semantics

The Racket (`racket/subleq.rkt`), Factor, Forth and Lean machines all follow
one specification: [`semantics/subleq-spec.md`](semantics/subleq-spec.md).
In short:

- cells are 32-bit signed integers and subtraction wraps modulo 2^32;
- the branch is taken when the **wrapped** result is `<= 0`, to the absolute address `c`;
- the machine halts after executing an instruction whose `c` is `-1`;
- `a = -2` is a trap (records `b`), `a = -1` reads input into `M[b]`,
  `b < 0` writes `M[a]` to the output, in that priority order;
- out-of-range reads give 0, out-of-range writes are discarded, and a PC that
  cannot fetch three cells is a fault.

The original unbounded-integer interpreter is kept unchanged in behaviour as
`racket/subleq-original.rkt`, as a benchmark baseline. It does not follow the
specification above.

## Languages / Targets

| Directory | What | Status |
|---|---|---|
| `racket/subleq.rkt` | Racket reference interpreter for the spec, rackunit tests, CLI | tested |
| `racket/subleq-original.rkt` | Original SUBLEQ baseline (unbounded integers, no I/O) | tested |
| `factor/` | Factor machine (`subleq-step`), tests, CLI | tested |
| `forth/` | Forth machine (`subleq`, `step`, `run`) for gforth, tests, CLI | tested |
| `lean/` | Lean 4 model of the spec, theorems, executable | builds; theorems checked by Lean |
| `racket/model.rkt`, `microcode.rkt`, `riscv.rkt`, `verify.rkt` | Rosette model of a microcoded SUBLEQ core running RISC-V instructions | 4 routines verified (ADD/ADDI/LUI, SUB, AUIPC, JAL) |
| `racket/oisc-add.rkt` | Small OISC ADD/SUB experiment (Rosette) | verified |
| `racket/disassemble.rkt` | Disassembler for the microcode | not tested |
| `nasm/` | x86 fragment of the core step | fragment only, not assembled |
| `microcode/` | Gate-level notes (plus ATS2 sketch) | documentation only |
| `riscv/` | Source form of the RISC-V-on-SUBLEQ routines | not checked against `microcode.rkt` |
| `examples/` | Example SUBLEQ programs | `countdown.subleq` runs under the spec |

Loads and stores (LB/LH/LW/LBU/LHU/SB/SH/SW) in `racket/microcode.rkt` are
stubs that point at the ADD routine. They are not verified.

## Verification

- `verification/fixtures/*.json`: edge-case programs with hand-written expected results.
- `verification/differential.rkt`: runs the Racket, Factor, Forth and Lean
  command-line machines on every fixture and on seeded random programs and
  compares their canonical output.
- `lean/Subleq/Theorems.lean`: theorems about the Lean `step`/`run`
  (see [`docs/verification-report.md`](docs/verification-report.md)).
  The Lean proofs are about the Lean model only; that the other three
  implementations agree with it is **tested**, not proved.

Details and current results: [`docs/verification-report.md`](docs/verification-report.md).

## Running

Toolchains used: Racket 9.3 (CS) with Rosette, Factor 0.102, gforth 0.7.3,
Lean 4 v4.35.0 (pinned in `lean/lean-toolchain`, installed with elan).

```bash
make test-racket      # rackunit
make test-forth       # gforth
make test-factor      # Factor (FACTOR=/path/to/factor)
make verify           # Rosette microcode checks; exits 1 if any FAIL
make oisc             # Rosette OISC experiment; exits 1 on FAIL/UNKNOWN
make lean-check       # lake build + no escape hatches + axiom check
make differential     # all four machines, fixtures + 200 random programs
make test             # everything above
```

Run one program (input format in the spec, §6):

```bash
racket racket/subleq.rkt prog.txt
gforth forth/main.fs prog.txt
factor factor/subleq-main.factor prog.txt
lean/.lake/build/bin/subleq-lean prog.txt
```

## License

GNU Affero General Public License v3.0 or later (`AGPL-3.0-or-later`); see [LICENSE](LICENSE).
