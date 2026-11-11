# AUDIT.md — Phase 0 Repository Forensics Audit

**Author / Maintainer**: Ahmad <ahmedparr93@gmail.com>
**License**: GNU Affero General Public License v3.0 (AGPL-3.0-only)
**Date**: November 2026

---

## 1. Executive Summary

This forensic audit evaluates the entire repository state for the SUBLEQ (Subtract and Branch if Less or Equal) One-Instruction Set Computer (OISC) project across implementations in Racket, Factor, Forth, Lean 4, NASM, Microcode, and RISC-V emulation.

Every source file, test artifact, build script, and manifest has been inspected to uncover instruction decoders, memory representation, numerical semantics, arithmetic models, halt conditions, extension traps (specifically I/O and Flash-Attention/FA traps), stubs, and inconsistencies.

---

## 2. Toolchain Inventory & Status

| Toolchain | Binary Path | Detected Version | Operational Status |
|:---|:---|:---|:---|
| **Racket** | `/usr/bin/racket` | Racket v8.10 [cs] | Fully operational. Standard library available. |
| **Gforth** | `/usr/bin/gforth` | gforth 0.7.3 | Fully operational ANS Forth system. |
| **Factor** | `/opt/factor/factor` | Factor 0.100 x86.64 | Fully operational concatenative language system. |
| **Lean 4** | `~/.elan/bin/lean` | Lean 4.8.0 / Lake 5.0.0 | Fully operational theorem proving platform. |
| **Python** | `/home/jules/.pyenv/shims/python3` | Python 3.12 | Available for differential testing harnesses. |

---

## 3. Repository Enumeration & Source Forensics

### 3.1. Core Engine Files

#### `racket/subleq.rkt`
- **Inspected Contents**: Vector-based interpreter for SUBLEQ.
- **Instruction Format**: Triplet `[a, b, c]`.
- **Fetch & Bounds**: Halts if `pc < 0` or `pc + 2 >= len`.
- **Arithmetic**: `res = mem[b] - mem[a]`.
- **Branching**: If `res <= 0` branches to `c`, else `pc + 3`.
- **Missing / Defects Identified**:
  - Missing standardized machine interface (`machine-init`, `machine-step`, `machine-run`, `machine-trace`, `machine-observe`).
  - Missing explicit I/O stream handling (negative addresses `a = -1` for input, `b = -1` for output).
  - Missing reserved trap dispatch (e.g., `a = -2` for Flash-Attention trap).
  - Lacked fault reporting (`MachineFault`).

#### `factor/subleq.factor`
- **Inspected Contents**: Concatenative SUBLEQ step definition in Factor vocabulary `subleq`.
- **Instruction Format**: Triplet `[a, b, c]`.
- **Missing / Defects Identified**:
  - **Syntax Error / Invalid Word**: Used `>r` and `r>` directly without vocabulary support.
  - Lacked complete machine state tuple or structure (`subleq-state`).
  - Missing `subleq-init`, `subleq-run`, `subleq-observe`, `subleq-trace`.
  - Negative address handling treated all `< 0` as 0, failing to distinguish I/O and traps.
  - No bounded execution or fault reporting.

#### `forth/subleq.fs`
- **Inspected Contents**: Minimal Forth sketch defining `VARIABLE IP`, `CREATE memory 1000 allot`, and word `: subleq ( a b c -- )`.
- **Missing / Defects Identified**:
  - Incomplete interpreter loop: only defined a single instruction word, not a full machine runner.
  - Conflated stacks: SUBLEQ operands manipulated on Forth data stack without encapsulation of machine state.
  - Lacked standard public words: `SUBLEQ-INIT`, `SUBLEQ-FETCH`, `SUBLEQ-DECODE`, `SUBLEQ-STEP`, `SUBLEQ-RUN`, `SUBLEQ-TRACE`, `SUBLEQ-OBSERVE`.
  - Lacked input/output stream integration and trap handling.

#### `lean/`
- **Initial Status**: Did not exist in the initial repository.
- **Requirements**:
  - Formalize canonical state $S = (M, PC, I, O, H, E)$.
  - Implement total deterministic transition function `step : MachineState -> MachineState`.
  - Machine-checked proofs of Theorems 1 through 10 with zero `sorry` or custom axioms.

### 3.2. Verification & Architecture Files

#### `racket/model.rkt`
- **Inspected Contents**: Rosette bitvector model of SUBLEQ micro-architecture for RISC-V emulation.
- **Instruction Format**: 16-bit packed word containing `src1` (4 bits), `src2` (4 bits), `jump` (8-bit signed offset).
- **Semantics**: `res = mem[src2] - mem[src1]`. Jump offset added to MPC if `res <= 0`, else MPC + 1.

#### `racket/microcode.rkt`
- **Inspected Contents**: 450-line microcode table implementing RISC-V instructions (`ADD`, `SUB`, `JAL`, `BEQ`, `AND`, etc.) mapped to SUBLEQ micro-operations.

#### `racket/oisc-add.rkt`
- **Inspected Contents**: Rosette symbolic verification script proving arithmetic correctness and source preservation for ADD and SUB routines on 4-cell and 5-cell SUBLEQ programs.

#### `racket/verify.rkt` & `racket/riscv.rkt`
- **Inspected Contents**: Rosette test harness verifying RISC-V instruction microcode against architectural specification.

#### `racket/disassemble.rkt`
- **Inspected Contents**: Disassembler from packed bitvector micro-instructions to human-readable assembly mnemonics.

#### `microcode/subleq_microcode.md`
- **Inspected Contents**: Hardware gate-level implementation (half-subtractor logic using NAND gates) and ATS2 verified primitive.

#### `nasm/subleq.asm`
- **Inspected Contents**: x86-32 assembly implementation of single SUBLEQ step.

#### `riscv/subleq_riscv.s`
- **Inspected Contents**: Assembly source definitions for RISC-V instruction emulation in SUBLEQ micro-assembly.

#### `examples/countdown.subleq`
- **Inspected Contents**: SUBLEQ program decrementing counter from 3 to 0 and halting with `-1 -1 -1`.

---

## 4. Canonical Specification & Phase 1 Synthesis

### 4.1. State Definition
$$S = (M, PC, I, O, H, E)$$
- $M$: Memory tape (vector of signed integers).
- $PC$: Instruction pointer (non-negative integer; negative indicates halt).
- $I$: Input stream (list of integers).
- $O$: Output stream (list of integers emitted).
- $H$: Boolean halt flag.
- $E$: Machine fault or trap status (`none`, `fault(kind)`, `trap(kind)`).

### 4.2. Extended Instruction Encodings & Decode Precedence
Instruction fetch at $PC$: $(a, b, c) = (M[PC], M[PC+1], M[PC+2])$.
1. **Halt Condition**:
   - If $PC < 0$ or $(a < 0 \land b < 0)$ or target is negative halt sentinel: state transitions to Halt.
2. **Flash-Attention Trap (FA Trap)**:
   - If $a = -2$: Dedicated extension trap. Does not modify ordinary memory; sets fault to FlashAttentionTrap and branches to $c$ (or halts if $c < 0$).
3. **Input Extension ($a = -1, b \ge 0$)**:
   - Ingests head of $I$ into $M[b]$. Result $r = \text{inVal}$. Branch if $r \le 0$ to $c$, else $PC + 3$. If $I$ is empty, faults with InputExhausted.
4. **Output Extension ($b = -1, a \ge 0$)**:
   - Emits $M[a]$ into $O$. Advances $PC' = PC + 3$.
5. **Standard Arithmetic ($a \ge 0, b \ge 0$)**:
   - $r = M[b] - M[a]$. $M'[b] = r$. If $r \le 0$ branch to $c$, else $PC + 3$.
6. **Machine Fault**:
   - Out-of-bounds accesses trigger InvalidFetch, InvalidRead, or InvalidWrite.
