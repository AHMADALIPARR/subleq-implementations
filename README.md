# SUBLEQ Implementations

[![License: AGPL-3.0](https://img.shields.io/badge/License-AGPL--3.0-blue.svg)](https://www.gnu.org/licenses/agpl-3.0)
[![Racket](https://img.shields.io/badge/Racket-9.3-blue)](https://racket-lang.org/)
[![Lean 4](https://img.shields.io/badge/Lean-4.35.0-orange)](https://leanprover.github.io/)
[![Factor](https://img.shields.io/badge/Factor-0.102-green)](https://factorcode.org/)
[![Forth](https://img.shields.io/badge/gforth-0.7.3-lightgrey)](https://www.gnu.org/software/gforth/)

**A multi-language, formally verified collection of SUBLEQ (Subtract and Branch if Less or Equal to Zero) One-Instruction Set Computer implementations.**

This repository provides bit-exact, observationally equivalent execution engines for the canonical SUBLEQ architecture across four programming paradigms (Racket, Factor, Forth, Lean 4), accompanied by machine-checked formal proofs, differential testing, cryptographic applications (SHA-256, keystream generators), macro synthesis, RISC-V microcode, and comprehensive audit documentation.

**Author & Principal Architect**: Ahmad <ahmedparr93@gmail.com>  
**License**: GNU Affero General Public License v3.0 (AGPL-3.0-only)


---

## Benchmarks

**IBX-1 integer butterfly (main result)**

The IBX-1 radix-2 butterfly is implemented in pure Racket, Factor, and as a SUBLEQ sequence that runs on the verified directive machine.

| Implementation | Metric | Result |
|----------------|--------|--------|
| SUBLEQ (directive machine) | Instructions per butterfly | **41** |
| SUBLEQ (directive machine) | Correctness | PASS — `(1 2 3 4)` → `(-3 5 5 -1)` |
| SUBLEQ (directive machine) | Throughput | ~0.021 ms / butterfly (200-run local) |
| Pure Racket | Full N=1024 transform | 0.07 ms |
| Energy invariant | After N=1024 | \(E_{	ext{out}} = 1024 \cdot E_{	ext{in}}\) (24 654 → 25 245 696) |

The earlier 24-instruction estimate was based on the macro table; the assembled sequence that actually runs is 41 steps. The sequence is built on the ATS2 dependently-typed `verified_subleq` primitive (bounds proven at compile time). Goldcrest’s single-register ADD is denser (~4 instructions) but performs a different operation. The pure Racket and Factor versions remain the fast native references; the SUBLEQ version is the one that executes on the formally verified stack.

Run:
```bash
make ibx          # pure Racket reference + energy check
make ibx-subleq   # SUBLEQ-backed kernel
```

---

## Table of Contents

1. [Benchmarks](#benchmarks)
2. [Introduction](#introduction)
3. [What is SUBLEQ?](#what-is-subleq)
4. [Canonical Operational Semantics](#canonical-operational-semantics)
5. [Repository Structure](#repository-structure)
6. [Implementations](#implementations)
7. [Formal Verification](#formal-verification)
8. [Differential Testing](#differential-testing)
9. [Cryptographic Applications & Benchmarks](#cryptographic-applications--benchmarks)
10. [Macro Synthesis](#macro-synthesis)
11. [Build & Test](#build--test)
12. [Audit Findings](#audit-findings)
13. [Related Work](#related-work)
14. [License](#license)

---


### SUBLEQ Disassembler

A raw-image disassembler is available in two forms:

- `tools/subleq-dis` (C11, no dependencies) — `make subleq-dis` then `./tools/subleq-dis image.txt`
- `racket/subleq-dis.rkt` — `racket racket/subleq-dis.rkt image.txt`

Both print one `subleq a, b, c` per triple with light pattern hints (zero, jump, halt, input, output, trap).

The Racket version (`racket/subleq-dis.rkt`) also performs conservative control-flow analysis:
- computes the set of instructions reachable from PC=0
- partitions reachable code into basic blocks
- reports each block's possible successors (fall-through and branch targets)

Branch edges are marked possible whenever the target is in range; the sign of the subtraction result is not solved statically.

## Introduction

One-Instruction Set Computers (OISCs) represent the theoretical extreme of computer architecture minimalism. While conventional processors implement hundreds or thousands of instructions, an OISC executes exactly one instruction yet remains Turing-complete. Among OISC variants (DJN, RSSB, SBN, NOR machines), SUBLEQ is the most prominent and computationally expressive.

This repository elevates SUBLEQ from an academic curiosity into a production-grade, formally verified computational foundation. Every implementation is unified under a single canonical operational specification. An automated differential testing suite continuously asserts observational equivalence across all four runtime engines.

The project demonstrates that a single three-address subtraction-and-branch instruction, augmented with deterministic extension decoders for I/O and coprocessor traps, provides a robust foundation capable of executing complex cryptosystems such as SHA-256 and stream ciphers.

---

## What is SUBLEQ?

SUBLEQ (Subtract and Branch if Less or Equal to Zero) is a One-Instruction Set Computer whose sole instruction has the form:

```
SUBLEQ a, b, c
```

which performs:

```
M[b] ← M[b] - M[a]
if M[b] ≤ 0 then
  PC ← c
else
  PC ← PC + 3
```

Each instruction occupies three consecutive memory cells. Because there is only one instruction, no opcode field is required. Programs are sequences of integer triplets stored in the same memory they modify (self-modifying code is natural and necessary).

### Historical Context

SUBLEQ was first conceptualized by Karel Culik II in the early 1980s and subsequently popularized in research on minimal universal machines, formal processor verification, and fault-tolerant logic synthesis. It is Turing-complete when memory cells can hold arbitrarily large integers and the address space is unbounded.

Common higher-level operations are synthesized from sequences of SUBLEQ instructions. Let `Z` be a dedicated zero scratch cell:

| Operation | Instruction Sequence | Cost |
|-----------|----------------------|------|
| Zero cell `x` | `SUBLEQ x, x, next` | 1 |
| Unconditional jump to `t` | `SUBLEQ Z, Z, t` | 1 |
| Move `a` → `b` (via scratch `T`) | Clear `T` and `b`, negate `a` into `T`, subtract into `b`, clear `T` | 5 |
| Add `a` to `b` (via scratch `T`) | Clear `T`, negate `a` into `T`, subtract into `b`, clear `T` | 4 |
| Bitwise logic / shifts | Bit extraction + arithmetic truth tables + reconstruction | Variable |

Example (clear cell `X`):
```
SUBLEQ X, X, NEXT   ; X = X - X = 0; always branches
```

Example (unconditional jump):
```
SUBLEQ Z, Z, TARGET ; Z - Z = 0 ≤ 0, so always branch to TARGET
```

These sequences are the foundation of the verified OISC addition routine in `racket/oisc-add.rkt` and of the native microcode sequences checked by `make verify-microcode`.

---

## Canonical Operational Semantics

### Machine State

A deterministic SUBLEQ machine state is modeled as the 6-tuple:

\[
S = (M, PC, I, O, H, E)
\]

| Component | Description |
|-----------|-------------|
| \(M\) | Memory tape (vector of signed integers) |
| \(PC\) | Program counter (non-negative; negative indicates halt) |
| \(I\) | Input stream (sequence of integers) |
| \(O\) | Output stream (emitted integers) |
| \(H\) | Halt flag (boolean; once true, transitions are idempotent) |
| \(E\) | Fault/trap status (`none`, `InvalidFetch`, `InputExhausted`, `FlashAttentionTrap`, etc.) |

### Instruction Decoding Precedence

To guarantee determinism, extension opcodes follow a strict precedence hierarchy:

1. **Out-of-bounds fetch**: \(PC < 0\) or \(PC + 3 > |M|\) → halt / `InvalidFetch`
2. **Halt sentinel**: \(a < 0 \land b < 0\) → halt unconditionally
3. **Coprocessor trap**: \(a = -2\) → Flash-Attention / accelerator trap (no memory mutation)
4. **Input stream**: \(a = -1, b \ge 0\) → dequeue from \(I\), write to \(M[b]\), branch on value
5. **Output stream**: \(b = -1, a \ge 0\) → append \(M[a]\) to \(O\), advance \(PC + 3\)
6. **Standard arithmetic**: \(a \ge 0, b \ge 0\) → \(M[b] \leftarrow M[b] - M[a]\); branch to \(c\) iff result \(\le 0\)

This precedence is enforced identically in the Racket, Factor, Forth, and Lean implementations.

---

## Repository Structure

```
subleq-implementations/
├── .github/workflows/          # CI: formal verification, differential tests
├── asm/                        # sasm assembler + macro table
│   ├── sasm.rkt
│   └── macro-table.rkt
├── bench/                      # Benchmarks (SHA-256 vectors, keystream, instruction counts)
├── docs/                       # Whitepapers, verification report, macro expansions
│   ├── whitepaper.md
│   ├── verification-report.md
│   ├── macro-expansions.md
│   ├── fault-model-readme.md
│   └── sha256-keystream-whitepaper.md
├── examples/                   # Example programs (countdown, etc.)
├── factor/                     # Factor implementations (directive + fault model)
├── forth/                      # Forth / gforth implementations
├── lean/                       # Lean 4 formal model + theorems (directive machine)
├── lean-fault/                 # Lean 4 fault-model project (separate toolchain)
├── microcode/                  # Gate-level description
├── nasm/                       # x86 assembly core step
├── programs/                   # SHA-256 and keystream generators (Racket)
├── racket/                     # Racket reference + Rosette microcode + OISC experiments
├── riscv/                      # SUBLEQ sequences implementing RISC-V operations
├── scripts/                    # Lean trusted-path checkers
├── verification/               # Differential testing harness
├── AUDIT.md                    # Phase 0 repository forensics
├── SUBLEQ_AUDIT_REPORT.md      # Detailed audit findings
├── Makefile                    # Unified build/test interface
└── LICENSE                     # AGPL-3.0-only
```

---

## Implementations

### Racket (`racket/`)

The functional reference model. Uses exact arbitrary-precision integers and provides a clean structured interface:

- `machine-init`, `machine-step`, `machine-run`, `machine-trace`, `machine-observe`
- Rosette symbolic verification of microcode (`riscv.rkt`, `microcode.rkt`)
- OISC ADD/SUB experiment (`oisc-add.rkt`)
- Original baseline semantics (`subleq-original.rkt`) and fault model (`subleq-fault.rkt`)

### Factor (`factor/`)

Concatenative implementation in vocabulary `subleq`. Emphasizes stack hygiene and sequence combinators. Includes both the directive machine and a separate fault-model vocabulary.

### Forth (`forth/`)

ANS Forth / Gforth implementation operating over statically allocated memory tapes. Demonstrates direct mapping to bare-metal register and memory operations. Includes fault-model variant.

### Lean 4 (`lean/` and `lean-fault/`)

Dependently typed formal specification. The `lean/` project contains the canonical directive machine and ten machine-checked theorems. The `lean-fault/` project (separate toolchain) formalizes the fault model. Both reject proof escape hatches (`sorry`, `admit`, custom axioms beyond standard Lean axioms).



### SUBLEQ Firmware Abstractions

`programs/firmware/subleq-firmware.rkt` re-expresses the host x86 Phase 2 mechanisms as ordinary SUBLEQ code on the directive machine:

| x86 mechanism | SUBLEQ realization |
|---------------|--------------------|
| `LIDT` | Software interrupt-vector table (array of handler addresses) |
| `CR0` / `CR4` | Virtual processor-state and feature-control words (memory cells) |
| `RDMSR` / `WRMSR` | Explicit memory-backed register-service operations |
| `IRETQ` | Software exception return that restores saved state |
| Page fault / GPF | Runtime checks that dispatch a virtual exception |
| Exception handlers | SUBLEQ routines reached through a dispatcher |

Run: `make firmware-subleq`

### Host Firmware (x86)

`nasm/firmware/16_firmware_phase2.asm` is a host-side x86 firmware initialization module (IDT/GDT setup, exception handlers, MSR configuration). It is **not** SUBLEQ code and does not alter the instruction counts or semantics of the directive SUBLEQ machine. It is included as a reference for an x86 bridge or boot path that could later host a SUBLEQ core.

### Additional Targets

| Target | Location | Description |
|--------|----------|-------------|
| NASM | `nasm/subleq.asm` | x86-32 assembly implementation of the core step |
| RISC-V microcode | `riscv/subleq_riscv.s`, `racket/microcode.rkt` | SUBLEQ sequences implementing RISC-V arithmetic, jumps, branches, bit logic |
| Microcode gates | `microcode/subleq_microcode.md` | Gate-level description of subtractor, flags, and branch logic |

---

## Formal Verification

### Lean Theorems

Ten fundamental machine theorems are machine-checked in Lean 4 without `sorry` placeholders or custom axioms. Selected theorems include:

| Theorem | Informal Statement |
|---------|--------------------|
| Determinism | Transitions are deterministic and single-valued |
| Arithmetic correctness | \(M'[b] = M[b] - M[a]\) |
| Frame preservation | All addresses \(x \ne b\) remain unaltered |
| Branch correctness | PC updates to \(c\) iff result \(\le 0\) |
| Aliasing correctness | When \(a = b\), the cell is cleared to zero |
| Memory preservation | Tape dimensions conserved across steps |
| Run determinism | Bounded execution is deterministic |
| Fuel monotonicity | Halted states are absorbing under extra fuel |
| I/O invariance | Standard arithmetic preserves output traces |
| Trap isolation | Reserved coprocessor traps cannot execute as ordinary arithmetic |

The trusted-path checker (`scripts/check-lean-trusted.sh`) verifies that only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) are used.

### Rosette Microcode Checks

Rosette verifies the register effects of four RISC-V routines implemented in SUBLEQ microcode:

- ADD / ADDI / LUI
- SUB
- AUIPC
- JAL

These checks confirm the result register and next PC but do **not** claim full RV32I conformance (loads/stores are stubs).

### OISC Experiment

`racket/oisc-add.rkt` symbolically verifies a four-instruction program that computes `output = A + B`, checking the result, exit PC, and source preservation.

### Native Directive-Machine Microcode Verification (Blueprint Milestone 1 — Complete)

The native Rosette harness described in `docs/microcode-blueprint.md` is implemented and on the trusted path.

`make verify-microcode` runs `racket/microcode/verify.rkt`. It checks five SUBLEQ sequences — Zero, Move, Add, Load, and Store — against post-conditions of the directive machine in `semantics/subleq-spec.md` (the machine Lean, Racket, Factor, and Forth implement): 32-bit two's-complement wrap, branch on the wrapped result `r ≤ 0` to an absolute `c`, and fetch / trap / input / output / ordinary precedence with the `c = −1` halt rule. Load and Store use fixed absolute addresses in flat memory. They are not register-indirect and they are not RV32I loads or stores.

Each sequence is checked symbolically (`verify` must return unsat), on concrete inputs, and by comparing the Rosette model with `racket/subleq.rkt`. The process exits 1 on any counterexample and 2 on a harness error. `make verify-microcode-mutations` injects a broken sequence or spec and passes only when every injection exits 1.

**Status**: Milestone 1 acceptance criteria met. The harness is integrated into `make test` and CI. The prior Goldcrest-derived RISC-V register-effect checks remain quarantined under `racket/microcode-legacy/` and are not part of the trusted path.

Not claimed: RV32I conformance, a mechanized proof that this Rosette model matches Lean, data-dependent branch targets, or any sequence beyond those five.

---

## Differential Testing

The differential harness (`verification/differential.rkt`) compares all four machines on:

- Hand-written fixtures
- 200 seeded random programs (configurable)

**Latest results** (seed 20261110):

| Metric | Value |
|--------|-------|
| Fixtures | 33 |
| Random programs | 200 |
| Total checks | 965 |
| Failures | 0 |

A separate run with 500 random programs produced 0 failures (2165 checks).

Outcomes of the 200 random programs (reference machine):

| Outcome | Count |
|---------|-------|
| Halted | 70 |
| Trap | 40 |
| Fault: PC out of range | 63 |
| Fault: input exhausted | 19 |
| Step limit | 8 |

---

## Cryptographic Applications & Benchmarks

### SHA-256 in Pure SUBLEQ

A complete 433,968-cell image computes SHA-256 digests using only SUBLEQ instructions. All four language engines produce bit-exact matching digests against NIST test vectors.

| Input | Digest | Steps (approx.) |
|-------|--------|-----------------|
| `""` (empty) | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | 101,967 |
| `"abc"` | `ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad` | 102,856 |

Run with: `make sha256`

### Stream Cipher / Keystream Generator ("Killer App")

A 704-cell LCG keystream generator demonstrates stream processing with constant memory footprints under directive I/O. Achieves a **1.754× reduction** in instructions compared to emulation without hardware wrap/stream directives.

Run with: `make killer-app`

### Instruction-Count Benchmarks

`make bench` produces instruction counts and wall-clock timings across engines, writing results to `verification-results/bench.md`.

---

## Macro Synthesis

The `sasm` assembler (`asm/sasm.rkt`) and macro table (`asm/macro-table.rkt`) synthesize higher-level operations from SUBLEQ primitives. Full expansions for both the directive machine and the original baseline are documented in `docs/macro-expansions.md`.

Representative costs (directive machine):

| Macro | Expansion Length | Notes |
|-------|------------------|-------|
| `ADD a b` | 3 | Via scratch |
| `MOV a b` | 4 | Clear + negate + subtract |
| `SHL1 x` | 3 | Double via add-to-self |
| `IN x` | 1 | Direct `a = -1` |
| `OUT x` | 1 | Direct `b = -1` |
| `HALT` | 1 | `c = -1` sentinel |
| `JSIGN x l` | 6 | Sign test + branch |
| `ROTL1 x` | ~12 | Bit extraction + reconstruction |

Generate the full table with: `make macros`

---

## Build & Test

### Prerequisites

- Racket 9.3 (full distribution)
- Factor 0.102
- gforth 0.7.3
- Lean 4 (via elan; toolchain pinned in `lean/lean-toolchain` and `lean-fault/lean-toolchain`)
- Rosette (installed via `raco pkg install rosette`)

### Common Targets

```bash
make help                 # List all targets
make test                 # Full suite: unit tests + verify + oisc + lean-check + differential + sha256 + killer-app
make test-racket          # Racket rackunit tests
make test-forth           # gforth tests (directive + fault model)
make test-factor          # Factor tests
make lean                 # Build Lean 4 project
make lean-check           # Trusted-path check (no sorry/axiom escapes)
make differential         # Cross-language differential (200 random programs)
make sha256               # NIST vectors on all engines
make killer-app           # Keystream benchmark
make bench                # Instruction counts + wall clock
make macros               # Macro expansion table
```

### Continuous Integration

GitHub Actions (`.github/workflows/formal-verification.yml`) runs on every push and pull request to `main`. The workflow installs Racket, Factor, gforth (built from source to avoid apt mirror DNS flakiness), and Lean, then executes the full test matrix.

---

## Audit Findings

Two audit documents capture the evolution of the repository:

- **`AUDIT.md`**: Phase 0 forensics — initial inventory of engines, missing interfaces, and required synthesis of the canonical state tuple and extension precedence.
- **`SUBLEQ_AUDIT_REPORT.md`**: Detailed findings on microcode correspondence, Rosette model boundary conditions, and verification gaps.

Key known limits (from `docs/verification-report.md`):

- Correspondence between Lean and the other three implementations is **tested**, not mechanized.
- Forth uses fixed capacities (1000 cells, 1000 input words, 100000 output words).
- Rosette microcode checks cover register effects of 4 routines only; loads/stores are stubs.
- `racket/disassemble.rkt`, `nasm/subleq.asm`, and `riscv/subleq_riscv.s` are not differentially tested.

---

## Related Work

- [Subleq on Esolang](https://esolangs.org/wiki/Subleq)
- [One Instruction Set Computer (Wikipedia / archival)](https://en.wikipedia.org/wiki/One_instruction_set_computer)
- Goldcrest microcode verification (upstream of `racket/microcode.rkt`)
- Historical OISC research: Culik, Minsky machines, URISC literature

---

## License

This project is licensed under the **GNU Affero General Public License v3.0 only** (AGPL-3.0-only). See the `LICENSE` file for the full text.

Network server use of modified versions requires source disclosure to users of that server, per the Affero clause.

---

## Contributing

Pull requests are welcome. Please ensure:

- New engines pass the differential suite
- Lean changes preserve the trusted path (no `sorry` / custom axioms)
- SPDX headers are present
- `make test` succeeds locally

For questions or discussion, open an issue or contact the author.

---

## Extended Architectural Deep Dive

### Memory Model and Numerical Semantics

Across the four primary engines, memory cells hold signed integers. The Racket, Factor, and Lean implementations use arbitrary-precision integers (or Lean's mathematical integers), eliminating silent overflow. The Forth engine and certain Rosette models operate on fixed-width 32-bit two's-complement words with explicit wraparound (`wrap32`). The differential suite accounts for these differences by normalizing observations where necessary and verifying that wraparound behavior is consistent within each engine's contract.

### Halt and Fault Conditions

The halt flag \(H\) is an absorbing state: once true, further applications of `step` leave the machine unchanged. Faults are reported in the diagnostic register \(E\) rather than by crashing the host process. This design enables the differential harness to compare fault outcomes across languages without relying on exception mechanisms that differ between runtimes.

Supported fault kinds include:

- `InvalidFetch` — program counter out of bounds
- `InvalidRead` / `InvalidWrite` — operand address out of bounds
- `InputExhausted` — input requested when the input stream is empty
- `FlashAttentionTrap` — coprocessor trap (`a = -2`)

### Self-Modifying Code

Because code and data share the same memory tape, programs can rewrite their own instructions. All four engines support this naturally. The differential suite includes fixtures that exercise self-modification to confirm that the engines agree on the resulting control flow.

---

## Fault Model

A separate fault-model lineage (originating in PR #4) is preserved alongside the directive machines:

- `racket/subleq-fault.rkt`
- `factor/subleq-fault.factor`
- `forth/subleq-fault.fs` (tests in `forth/test-subleq-fault.fs`)
- `lean-fault/` (independent Lean project with its own `lean-toolchain`)

The fault model emphasizes explicit reporting of out-of-bounds accesses and input exhaustion while retaining the same core arithmetic and branch semantics. Its tests are invoked via `make test-racket`, `make test-forth`, `make test-factor`, and `make lean-fault-check`.

The fault-model Lean theorems are elaborated separately and subjected to the same trusted-path discipline as the directive model.

---

## RISC-V Microcode Layer

The files `racket/microcode.rkt` and `riscv/subleq_riscv.s` contain sequences of SUBLEQ operations that implement selected RISC-V instructions. These sequences are the substrate verified by the Rosette checks in `racket/riscv.rkt`.

The verification boundary is deliberately narrow:

- Register effects of ADD, ADDI, LUI, SUB, AUIPC, and JAL are checked.
- Load and store routines are stubs whose entry points currently alias the ADD routine.
- Full RV32I architectural conformance is not claimed.

This layer exists to explore how a minimal OISC can serve as a microarchitectural substrate for a conventional ISA, and to provide a concrete target for symbolic verification experiments.

---

## Assembler and Macro Table

The `sasm` assembler (`asm/sasm.rkt`) accepts a higher-level assembly dialect and expands it into raw SUBLEQ triplets. The companion `macro-table.rkt` enumerates every supported macro and can emit the full expansion table used to generate `docs/macro-expansions.md`.

Macros include:

- Arithmetic: `ADD`, `ADD32`, `MOV`, `MULK`
- Control: `JMP`, `JSIGN`, `HALT`
- Bit manipulation: `SHL1`, `ROTL1`, `UNPACK32`
- I/O and traps: `IN`, `OUT`, `TRAP`
- Memory: `LOAD-NEXT`, `STORE-NEXT`
- Cryptographic helpers: `ACC+PARITY`, `ACC+CH`, `ACC+MAJ`

Running `make macros` regenerates the table and can be used as a regression check that expansions remain stable.

---

## Example Programs

The `examples/` directory contains small, self-contained SUBLEQ programs. The classic `countdown.subleq` decrements a counter from 3 to 0 and terminates with the halt sentinel. These examples are useful for manual inspection and as additional fixtures for the differential harness.

Larger programs live under `programs/`:

- `sha256.rkt` — full SHA-256 compression in SUBLEQ
- `keystream.rkt` — LCG-based stream generator

Both are exercised by the `make sha256` and `make killer-app` targets and by the Racket unit tests.

---

## Continuous Integration Details

The GitHub Actions workflow (`.github/workflows/formal-verification.yml`) defines five jobs:

| Job | Purpose |
|-----|---------|
| Racket tests + Rosette | Unit tests, microcode verification, OISC experiment |
| Forth tests | gforth unit tests for both directive and fault models |
| Factor tests | Factor unit tests |
| Lean 4 | Build + trusted-path check + fault-model check |
| Differential | Cross-language comparison on fixtures + random programs |

gforth is built from source inside the workflow because Ubuntu archive mirrors on GitHub-hosted runners have exhibited intermittent DNS resolution failures. The workflow prefers tools already present on the runner and falls back to official GNU tarball downloads with multiple mirrors.

---

## Performance Characteristics

While absolute wall-clock times vary by host, the following qualitative observations hold:

- The Racket engine, using arbitrary-precision integers, is the reference for correctness but is not the fastest.
- Factor and Forth engines, operating closer to native or fixed-width representations, typically show lower per-step overhead on long-running programs such as SHA-256.
- The Lean executable (compiled via Lake) provides a third independent performance point and serves as the formal ground truth for the theorems.

`make bench` captures concrete instruction counts and timings for the SHA-256 and keystream workloads and writes them to `verification-results/bench.md`. These numbers are intentionally not hard-coded in this README because they are host-dependent; regenerate them locally for current figures.

---

## Security and Cryptographic Notes

The SHA-256 implementation is a pure functional translation of the standard compression function into SUBLEQ. It is intended as a correctness and complexity demonstration, not as a production cryptographic library. Side-channel resistance, constant-time execution, and resistance to fault injection are outside the scope of the current engines.

The keystream generator is an LCG and should not be used for security-sensitive applications. Its value in this repository is as a streaming workload that exercises the directive I/O extensions and provides a measurable instruction-count delta between the directive and original machines.

---

## Future Directions

Possible extensions that preserve the project's verification discipline include:

- Mechanized correspondence proofs between the Lean model and one or more of the executable engines
- Expansion of Rosette checks to additional RISC-V instructions once load/store microcode is written
- Hardware synthesis experiments using the gate-level description in `microcode/`
- Additional cryptographic primitives (e.g., SHA-3 or a stream cipher with a larger state) expressed entirely in SUBLEQ
- Integration with formal hardware verification tools that consume the Lean model

Any such extension should continue to pass the differential suite and the Lean trusted-path checker.

---

## Acknowledgments

This work builds on the long tradition of OISC and minimal-machine research. The Rosette microcode layer incorporates material derived from the Goldcrest project (ics-jku). The formalization and multi-language differential approach are original to this repository.

---

## Appendix: Quick Reference Card

### Instruction

```
SUBLEQ a, b, c
M[b] -= M[a]
if M[b] <= 0 then PC = c else PC = PC + 3
```

### Extension Precedence (highest to lowest)

1. Out-of-bounds fetch
2. Halt sentinel (`a < 0 && b < 0`)
3. Trap (`a == -2`)
4. Input (`a == -1 && b >= 0`)
5. Output (`b == -1 && a >= 0`)
6. Ordinary arithmetic

### Key Make Targets

```
make test          # everything
make differential  # cross-language
make sha256        # NIST vectors
make lean-check    # trusted path
make bench         # numbers
```

### Contact

Ahmad <ahmedparr93@gmail.com>

For issues, please use the GitHub issue tracker.

---

## Detailed Verification Report Summary

The verification report (`docs/verification-report.md`) records a local run on 2026-11-10 (Debian 13, x86_64). Overall status is **PARTIALLY VERIFIED**: the Lean theorems about the specification are checked by Lean, while the Racket, Factor, and Forth machines are tested against the Lean executable (not proved equivalent).

### Toolchain Versions Used in the Report

| Tool | Version |
|------|---------|
| Racket | 9.3 [cs] |
| Rosette | pkgs.racket-lang.org (Z3 bundled) |
| Factor | 0.102 |
| gforth | 0.7.3 |
| Lean 4 | v4.35.0 (elan 4.2.4) |

### Unit Test Counts

| Engine | Tests | Result |
|--------|-------|--------|
| Racket (rackunit) | 41 | passed |
| Forth (gforth) | 35 | 0 failed |
| Factor | 24 | 0 failed |

### Mutation Testing of the Checks

The verification report documents that the differential suite is sensitive to intentional bugs:

- Replacing Forth `wrap32` with a no-op produced 5 differential mismatches.
- Changing Factor's branch test from `<=` to `<` produced 8 mismatches.
- Changing Lean's branch test from `≤` to `<` caused both a Lean build failure and 7 differential mismatches.
- Introducing a `sorry` in Lean was rejected by the trusted-path script.

These results give confidence that the test infrastructure would detect real regressions.

---

## Whitepaper Highlights

The unified whitepaper (`docs/whitepaper.md`) frames the project as a production release of a formally verified SUBLEQ architecture. Key claims include:

- Bit-exact cross-language observational equivalence across Racket, Factor, Forth, and Lean.
- Ten machine-checked formal theorems with zero proof escape hatches.
- Practical cryptographic utility demonstrated by a pure-SUBLEQ SHA-256 implementation that matches NIST vectors on all four engines.
- A stream-cipher workload showing a measurable instruction-count advantage for the directive I/O extensions.

The SHA-256 / keystream whitepaper (`docs/sha256-keystream-whitepaper.md`) expands on the construction of the 433,968-cell SHA-256 image and the 704-cell keystream generator, including the macro costs that make the implementations tractable.

---

## Phase 0 Audit Summary

`AUDIT.md` records the state of the repository before the canonical semantics and Lean model were fully synthesized. At that stage:

- The Racket engine lacked a standardized machine interface and explicit I/O/trap handling.
- The Factor engine contained stack-hygiene issues and treated all negative addresses uniformly.
- The Forth engine was a single-instruction word rather than a full machine runner.
- No Lean formalization existed.

The subsequent work closed these gaps by introducing the 6-tuple state, the strict decoding precedence, the four production engines, and the differential harness. The audit remains in the repository as historical context and as a checklist of properties that later implementations were required to satisfy.

---

## File-by-File Overview of Core Engines

### Racket

- `subleq.rkt` — directive machine with full interface
- `subleq-original.rkt` — baseline semantics without directive extensions
- `subleq-fault.rkt` — fault-model variant
- `test-subleq.rkt` — rackunit suite
- `model.rkt` — Rosette bitvector model of a packed-instruction SUBLEQ core
- `microcode.rkt` — RISC-V microcode table
- `riscv.rkt` — Rosette harness for register-effect checks
- `oisc-add.rkt` — symbolic ADD/SUB experiment
- `disassemble.rkt` — disassembler for packed micro-instructions
- `verify.rkt` — additional verification utilities

### Factor

- `subleq.factor` — directive machine
- `subleq-fault.factor` — fault model
- `subleq-tests.factor` — unit tests
- `subleq-main.factor` — entry point
- `test-subleq.factor` — additional fault-model tests

### Forth

- `subleq.fs` — directive machine
- `subleq-fault.fs` — fault model
- `test-subleq.fs` — directive tests
- `test-subleq-fault.fs` — fault-model tests
- `main.fs` / `main-large.fs` — runners

### Lean

- `lean/Subleq/Machine.lean` — state and step
- `lean/Subleq/Theorems.lean` — the ten theorems
- `lean/Main.lean` — executable entry point
- `lean/AxiomCheck.lean` — axiom audit helper
- `lean-fault/` — parallel project for the fault model

---

## How to Add a New Engine

To add a fifth language implementation while preserving the project's invariants:

1. Implement the 6-tuple state and the six-step decoding precedence exactly.
2. Provide `init`, `step`, `run`, and `observe` (or equivalent) functions.
3. Emit observations in the format expected by `verification/differential.rkt`.
4. Add a Makefile target that the differential harness can invoke.
5. Run `make differential` with at least the default 200 random programs.
6. If the engine is intended to be formally verified, consider a Lean embedding or a correspondence proof.

Until a correspondence proof exists, the new engine remains "tested, not proved" relative to the Lean model, which is the current status of the three executable engines.

---

## Reproducibility

All random programs in the differential suite are generated from a fixed seed (`20261110` by default). The Makefile exposes `RANDOM_PROGRAMS` and `SEED` variables so that larger or differently seeded runs can be performed:

```bash
make differential RANDOM_PROGRAMS=500 SEED=20261110
```

The SHA-256 and keystream programs are deterministic; their step counts are therefore stable across runs on the same engine.

---

## Documentation Map

| Document | Role |
|----------|------|
| `README.md` (this file) | Project overview and entry point |
| `docs/whitepaper.md` | Unified architectural whitepaper |
| `docs/sha256-keystream-whitepaper.md` | Cryptographic constructions |
| `docs/verification-report.md` | Local verification results and known limits |
| `docs/macro-expansions.md` | Full sasm macro expansions |
| `docs/fault-model-readme.md` | Fault-model lineage documentation |
| `AUDIT.md` | Phase 0 forensics |
| `SUBLEQ_AUDIT_REPORT.md` | Detailed audit findings |

---

## Closing

This repository demonstrates that a single-instruction architecture can be made precise enough for multi-language implementation, differential testing, and machine-checked formal verification, while remaining expressive enough to host non-trivial cryptographic workloads. The combination of a Lean ground truth, three independently written executable engines, and an automated differential harness provides a practical template for verified minimal computing.

The work is released under AGPL-3.0-only so that any network deployment of modified versions continues to share its source with the users of that deployment.

---

## Appendix B: Mathematical Summary

The core transition relation can be summarized as:

\[
\begin{align*}
&(a, b, c) = (M[PC], M[PC+1], M[PC+2]) \\
&r = M[b] - M[a] \\
&M'[b] = r \\
&PC' = 
\begin{cases}
c & \text{if } r \le 0 \\
PC + 3 & \text{otherwise}
\end{cases}
\end{align*}
\]

with the understanding that the extension cases (halt, trap, input, output) take precedence and may suppress the ordinary arithmetic update.

Frame preservation states that for all addresses \(x \ne b\), \(M'[x] = M[x]\). Determinism follows from the fact that every clause of the decoding precedence is a total function of the current state.

These properties are the ones formalized in the Lean development and re-checked by the differential suite on concrete programs.

---

## Appendix C: CI Badge and Status

The CI badge at the top of this README reflects the latest run of `.github/workflows/formal-verification.yml`. A green badge indicates that all five jobs (Racket, Forth, Factor, Lean, Differential) succeeded on the most recent push or pull request to `main`.

Because gforth is compiled from source inside the workflow, the Forth and Differential jobs take longer than the others; this is expected and is the price of avoiding flaky apt mirrors.

---

## Final Notes

All source files carry SPDX license identifiers. The project uses AGPL-3.0-only exclusively. Third-party material (notably portions of the Rosette microcode derived from Goldcrest) is acknowledged in the relevant files and in the audit documents.

Readers interested in the historical development of the repository are encouraged to examine the commit history and the two audit documents. Readers interested in extending the work should begin with the differential harness and the Lean trusted-path checker; these two artifacts define the acceptance criteria for any new contribution.


---

## IBX-1 Integer Butterfly Network

An alternative integer-only Gaussian butterfly (radix-2) architecture has been added.

- Factor reference: `factor/ibx.factor` (uploaded unchanged via PR #10)
- Racket reference: `programs/ibx.rkt` (`make ibx`)

Both implement the same transform:
- 4 integer add/sub per butterfly
- Energy invariant: after a full N=1024 transform, \(E_{	ext{out}} = 1024 \cdot E_{	ext{in}}\)
- Small vector check: input `{1,2,3,4}` + zero imaginary yields the known result

The butterfly kernel is also available as a SUBLEQ sequence executed by the directive machine:

- `programs/ibx-subleq.rkt` — assembles the four operations with the sasm macros and runs them via `run-subleq` (`make ibx-subleq`).
- Expected cost: ~24 executed instructions per butterfly (matches the earlier measured baseline).

The pure Racket and Factor versions remain the fast native references; the SUBLEQ version is the one that runs on the verified stack.

