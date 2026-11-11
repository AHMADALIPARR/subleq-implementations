<!--
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only
-->

# Verification report

**Overall status: PARTIALLY VERIFIED**

The theorems about the Lean model of the specification are checked by Lean. The
Racket, Factor and Forth machines are **tested** against it (unit tests,
hand-written fixtures and seeded random programs), not proved equivalent.
The trusted Rosette harness (`racket/microcode/`, `make verify-microcode`)
checks five directive-machine sequences (Zero, Move, Add, Load, Store). It
does not claim RV32I conformance. Correspondence with Lean is tested on
concrete programs against `racket/subleq.rkt`, not mechanized. The previous
Goldcrest layer is quarantined in `racket/microcode-legacy/` and is not part
of this claim.

All results below are from local runs on 2026-11-10 (Debian 13, x86_64) with
the toolchains listed. Hosted CI results are on the pull request.

## Toolchains

| Tool | Version |
|---|---|
| Racket | 9.3 [cs] (installer `racket-9.3-x86_64-linux-buster-cs.sh`), rackunit from the full distribution |
| Rosette | from pkgs.racket-lang.org, installed with `raco pkg install rosette`; solver Z3 as bundled by Rosette |
| Factor | 0.102 (`factor-linux-x86-64-0.102.tar.gz`, git id 6f604bb0fa28362bb2f20ddb133bc73b19b6a50f) |
| gforth | 0.7.3 (Ubuntu package 0.7.3+dfsg-9build4.1, the same package CI installs on ubuntu-24.04) |
| Lean 4 | v4.35.0 (commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc), elan 4.2.4, pinned in `lean/lean-toolchain` |

## Results by stage (`make test`, exit status 0)

| Stage | Command | Result |
|---|---|---|
| Racket unit tests | `raco test racket/subleq.rkt racket/subleq-original.rkt` | 41 tests passed (37 spec, 4 baseline) |
| Forth unit tests | `gforth forth/test-subleq.fs` | 35 checks, 0 failed |
| Factor unit tests | `factor factor/subleq-tests.factor` | 24 checks, 0 failed |
| Rosette microcode (historical, now quarantined) | `racket racket/riscv.rkt` | register-effect specs for ADD/ADDI/LUI, SUB, AUIPC, JAL: PASS (4 checks, 0 failed); RV32I conformance not checked. Superseded by the milestone 1 harness below |
| Rosette OISC | `racket racket/oisc-add.rkt` | ADD PASS, SUB PASS |
| Lean build | `lake build` | success, 0 errors, 0 warnings |
| Lean trusted path | `scripts/check-lean-trusted.sh` | 26 theorems; no `sorry`/`admit`/`axiom`/`unsafe`/`native_decide`/`implemented_by`/`extern`; axioms used are only `propext`, `Classical.choice`, `Quot.sound` |
| Differential | `racket verification/differential.rkt --random 200 --seed 20261110` | 33 fixtures + 200 random programs × 4 implementations, 965 checks, 0 failures |

A separate local run with `--random 500` (same seed) also gave 0 failures
(2165 checks). Outcomes of the 200 random programs according to the reference:
70 halted, 40 trap, 63 fault:pc-out-of-range, 19 fault:input-exhausted,
8 step-limit.

### Checks that the checks can fail

Each of these was done locally and then reverted:

- Forth `wrap32` replaced by a no-op: 5 differential mismatches (fixtures + 30 random).
- Factor branch test `0 <=` changed to `0 <`: 8 differential mismatches (fixtures + 30 random).
- Lean branch test `r ≤ 0` changed to `r < 0`: `lake build` fails (2 errors in
  `Subleq/Theorems.lean`), and the executable gives 7 differential mismatches (fixtures + 20 random).
- A deliberately wrong check in a copy of the Forth and of the Factor test
  file: exit status 1.
- ADD spec in `racket/riscv.rkt` changed to use `SRC1`: FAIL, exit status 1.
- The README-oisc bug (`(insn 0 3 5)`): SUB FAIL, exit status 1.
- A `sorry` theorem added to Lean: rejected by `scripts/check-lean-trusted.sh`.
- One fixture expectation was mistyped while writing this PR; the
  differential runner reported it (5 mismatches) and it was corrected.

## Lean theorems (`lean/Subleq/Theorems.lean`)

The directive's own theorem list (A–K) was not available when this was
written, so the names below are this PR's, not a mapping to A–K.

| Theorem | Statement (informal) |
|---|---|
| `wrap32_bounds` | `-2^31 ≤ wrap32 x < 2^31` |
| `wrap32_of_bounds` | `wrap32 x = x` for `x` in range |
| `wrap32_congr` | `wrap32 (x + 2^32·k) = wrap32 x` |
| `wrap32_idem` | `wrap32 (wrap32 x) = wrap32 x` |
| `rd_oob` | out-of-range read is 0 |
| `wr_oob` | out-of-range write leaves memory unchanged |
| `rd_wr_same` | in-range write then read returns the value |
| `wr_size` | writes keep the memory size |
| `step_size` | `step` keeps the memory size |
| `step_stopped` | a non-running state is a fixed point of `step` |
| `step_badpc` | `PC < 0 ∨ N ≤ PC + 2` gives `fault pc-out-of-range`, nothing else changes |
| `step_trap` | priority 1: `a = -2` traps with code `b` (any `b`, any `c`) |
| `step_input_empty` | priority 2: `a = -1` with no input gives `fault input-exhausted` |
| `step_input` | priority 2: `a = -1` writes `wrap32 v` to `M[b]`, `PC + 3`, halt rule |
| `step_output` | priority 3: `a ∉ {-1,-2}`, `b < 0` appends `read(a)`, `PC + 3`, halt rule |
| `step_ordinary` | priority 4: `r = wrap32 (read b − read a)`, write, branch to absolute `c` iff `r ≤ 0`, halt rule |
| `haltOn_neg_one` | the halt rule with `c = -1` always halts (branch taken or not) |
| `haltOn_other` | with `c ≠ -1` the halt rule changes nothing |
| `step_steps` | a step adds 0 or 1 to the step counter |
| `wr_cells32`, `step_cells32`, `init_cells32`, `run_cells32` | every cell stays a 32-bit value from `init` through any `run` |
| `run_stops` | `run` never ends in `running` |
| `run_stopped` | `run` does nothing to a stopped state |
| `run_succ` | with fuel left, `run (n+1) s = run n (step s)` |

Determinism needs no theorem: `step` and `run` are total Lean functions.

### Correspondence (the directive's "Theorem L")

**Tested, not mechanized.** There is no proof that the Racket, Factor or
Forth programs implement `Subleq.step`. Agreement is checked by the
differential runner on 33 hand-written fixtures and seeded random programs.
The Lean executable runs the very `step`/`run` definitions the theorems are
about; its input parser and printer in `lean/Main.lean` are not proved.

## Directive-machine microcode (milestone 1)

Local run on 2026-11-11 (Ubuntu 24.04, x86_64).

| Tool | Version |
|---|---|
| Racket | 9.3 [cs] |
| Rosette | commit `373c8c35e4a7667f38fce10cf0b74ae17de07f1d` (pkgs.racket-lang.org, Racket 9.3 catalog) |
| Z3 | 4.8.8, the binary bundled with that Rosette install |

`make verify-microcode` (`racket racket/microcode/verify.rkt`) exited 0:
103 checks, 0 failed, 0 harness errors.

| Check | Count | Result |
|---|---|---|
| `wrap32` agreement with `racket/subleq.rkt` on edge integers | 14 | pass |
| Concrete differential, model vs `run-subleq`, edge programs (branch, wrap, trap, input, output with `b < 0`, faults, step-limit, self-modified `c`) | 14 | pass |
| Symbolic post-condition (`verify` returned unsat) for Zero, Move, Add, Load, Store | 5 | pass (about 0–3 ms each) |
| Concrete post-conditions, 7 input vectors per sequence | 35 | pass |
| Same concrete vectors, model vs `run-subleq` | 35 | pass |

Scope of that claim:

- Sequences and specs live in `racket/microcode/`. The model is a Rosette re-implementation of `semantics/subleq-spec.md` (32-bit two's-complement bitvectors, `bvsub` = `wrap32`, branch on signed `r ≤ 0`, absolute `c`, Lean precedence, `c = -1` halt rule).
- Zero is one instruction. Move, Add, Load, and Store are the directive scratch idiom (clear, negate, subtract, clear). Load and Store use fixed absolute addresses. None of the five is self-modifying. Entry PC, fuel, contract, and the self-modifying flag are in `sequences.rkt` and printed by the harness.
- Exit status: 0 all checks passed, 1 counterexample or concrete failure, 2 harness error (unknown mutation, bad arguments, solver `unknown` / timeout, symbolic PC). A timeout is not a pass.

### Mutation test

`make verify-microcode-mutations` runs each fault in a child process. The self-test exits 0 only when every child exits 1 and prints a `symbolic sat FAIL` or `concrete FAIL`. Result: all 6 faults caught, self-test exit 0.

| Id | Fault | Child exit | Counterexample the child printed |
|---|---|---|---|
| `zero-wrong-target` | instruction zeros FRAME instead of X | 1 | X = −1 stays −1 (`sat`) |
| `add-subtract` | cell 6 selects A, so B ← B − A | 1 | A = 1065353216, B = 0, final B = −1065353216 |
| `move-skip-clear` | B is not cleared, so B ← B + A | 1 | A = 0, B = −1, final B = −1 |
| `load-wrong-source` | RD ← MEM2 | 1 | SRC = −1, MEM2 = 0, final RD = 0 |
| `store-clobber` | halting instruction writes OTHER | 1 | RS = 0, OTHER = 1, final PC = 15 rather than −1 |
| `zero-spec-identity` | Zero spec requires X unchanged | 1 | X = −1 becomes 0 |

`store-clobber` and `zero-wrong-target` still satisfy the spec on the all-zero vector. The symbolic check is what rejects them for every input. The all-zero concrete case is not enough.

## Legacy Goldcrest layer (not on the trusted path)

Moved unchanged to `racket/microcode-legacy/` (`microcode.rkt`, `model.rkt`, `riscv.rkt`, `verify.rkt`). `make verify` still runs it. It is not evidence about the directive machine. The notes below describe that artifact as it stood before the move.

- `microcode.rkt` is upstream's `compliant.rkt` from
  ics-jku/goldcrest-microcode-verification. The previous specs came from
  upstream's `riscv.rkt`, which targets upstream's other microcode file.
  Against this microcode all four printed FAIL, and the program still exited 0.
- The specs now state the **register effect** of each routine: the result in
  `RSLT` (= `SRC2`, as `model.rkt` defines it) and the next PC in `RVPC`:
  ADD/ADDI/LUI `RSLT = SRC2 + IMMI`; SUB `RSLT = SRC2 - IMMI`;
  AUIPC `RSLT = RVPC + IMMI`; JAL `RSLT = RVPC + 4`, `RVPC = RVPC + IMMI`;
  the others `RVPC = RVPC + 4`. All four pass; any FAIL now exits 1.
- **Not checked: RV32I conformance.** That depends on how the Goldcrest VP
  loads `rs1`/`rs2`/`imm` into the registers, which is not in this repository.
  `SUBLEQ_AUDIT_REPORT.md` (finding SUBLEQ-02) says SUB computes `rs2 - rs1`
  under that convention; this PR did not re-check that claim and did not
  change the microcode.
- **Verification boundary:** LB/LH/LW/LBU/LHU/SB/SH/SW are stubs whose entry
  points are the ADD routine. They are not verified, and no memory-access
  microcode was written. The other ~30 instructions in `microcode.rkt` have
  no specs.
- `model.rkt` branches on the exact (XLEN+1)-bit difference while storing the
  wrapped value (SUBLEQ-07 in `SUBLEQ_AUDIT_REPORT.md`). This is the Rosette
  model of the Goldcrest core, separate from the directive machine, and was
  not changed.
- `riscv/subleq_riscv.s` is not checked.

## Not verified / known limits

- No proof of correspondence between Lean and the other implementations (above).
- No mechanized proof that `racket/microcode/model.rkt` implements Lean `step`.
  Agreement with `racket/subleq.rkt` is tested, on the edge programs and the
  five sequences' concrete vectors listed above.
- The milestone 1 harness does not verify data-dependent branch targets
  (a symbolic PC at fetch is a harness error), register-indirect addressing,
  or any sequence besides Zero, Move, Add, Load, and Store. Load and Store
  are fixed absolute addresses, not RV32I loads and stores.
- Forth: fixed capacity of 1000 memory cells and 1000 input words; output
  buffer of 100000 words (overflow aborts with an error message).
- `racket/disassemble.rkt` still loads the quarantined Goldcrest model (only
  its require path changed). `nasm/subleq.asm`, `microcode/subleq_microcode.md`
  and `riscv/subleq_riscv.s` are not tested.
- `racket/subleq-original.rkt` is the original semantics and is deliberately
  not compared with the spec.
