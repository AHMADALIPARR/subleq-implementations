<!--
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only
-->

# Unified White Paper: Formally Verified SUBLEQ OISC Architecture, Macro Synthesis, and Multi-Language Execution

**Author & Principal Architect**: Ahmad <ahmedparr93@gmail.com>
**Version**: 1.0 (Production Release)
**License**: GNU Affero General Public License v3.0 (AGPL-3.0-only)

---

## Abstract

One-Instruction Set Computers (OISC) represent the theoretical extreme of computer architecture minimalism. In this paper, we present the formalization, operational semantics, multi-language implementations, and empirical performance analysis of the canonical SUBLEQ (Subtract and Branch if Less or Equal to Zero) architecture. We demonstrate that a single three-address subtraction-and-branch instruction, augmented with deterministic extension decoders for I/O and coprocessor traps, provides a robust, Turing-complete foundation capable of executing complex cryptosystems such as SHA-256 and stream ciphers. We establish bit-exact cross-language observational equivalence across functional (Racket), concatenative (Factor), stack-based (Forth), and dependently typed (Lean 4) runtimes, accompanied by ten machine-checked formal theorems verified without proof escape hatches.

---

## 1. Introduction and Architectural Motivation

Conventional microprocessors multiplex execution across hundreds or thousands of heterogeneous instructions. In contrast, the SUBLEQ architecture executes exactly one instruction:

$$\text{SUBLEQ}(a, b, c): \quad \mathcal{M}[b] \leftarrow \mathcal{M}[b] - \mathcal{M}[a]; \quad \text{if } \mathcal{M}[b] \le 0 \text{ goto } c \text{ else goto } \mathcal{PC} + 3$$

While historically regarded as an esoteric curiosity, SUBLEQ possesses distinctive properties that make it advantageous for formal hardware verification, trusted computing bases, fault-tolerant logic synthesis, and ultra-minimalist cryptographic accelerators.

---

## 2. Canonical Operational Semantics

We define the complete discrete machine state as a 6-tuple:
$$\mathcal{S} = (\mathcal{M}, \mathcal{PC}, \mathcal{I}, \mathcal{O}, \mathcal{H}, \mathcal{E})$$
where $\mathcal{M}$ is memory, $\mathcal{PC}$ is the instruction pointer, $\mathcal{I}$ is the input stream, $\mathcal{O}$ is the output stream, $\mathcal{H}$ is the halt status, and $\mathcal{E}$ is the diagnostic fault register.

### Deterministic Extension Decoding
To avoid ambiguity, extension opcodes adhere to a strict decoding precedence:
1. **Instruction Fetch**: Out-of-bounds $\mathcal{PC}$ halts or faults with `InvalidFetch`.
2. **Halt Sentinel**: $a < 0 \land b < 0$ transitions unconditionally to halted state $\mathcal{H} = \text{true}$.
3. **Coprocessor Trap**: $a = -2$ activates the dedicated Flash-Attention / accelerator trap without mutating memory.
4. **Input Stream**: $a = -1, b \ge 0$ dequeues from $\mathcal{I}$, writes to $\mathcal{M}[b]$, and branches on the ingested value.
5. **Output Stream**: $b = -1, a \ge 0$ extracts $\mathcal{M}[a]$, appends to $\mathcal{O}$, and advances $\mathcal{PC} + 3$.
6. **Standard Arithmetic**: $a \ge 0, b \ge 0$ computes $\mathcal{M}[b] - \mathcal{M}[a]$, writes to $\mathcal{M}[b]$, and branches if $r \le 0$.

---

## 3. High-Level Macro Synthesis

Higher-level control flow and arithmetic primitives are synthesized systematically:
- **Clear (`ZERO x`)**: `SUBLEQ x, x, +3` (Cost: 1 instruction).
- **Move (`MOV a, b`)**: Zero destination, negate source into scratch, subtract scratch into destination (Cost: 4 instructions).
- **Addition (`ADD a, b`)**: Invert source into scratch, subtract scratch from destination (Cost: 3 instructions).
- **Unconditional Jump (`JMP target`)**: Subtract zero scratch cell from itself to trigger branch (Cost: 1 instruction).
- **Bitwise Logic & Rotations**: Decompose 32-bit operands into individual bits via sign-testing, evaluate boolean expressions arithmetically, and reconstruct results through shift-addition.

---

## 4. Multi-Language Execution Engines

We construct bit-exact, observationally equivalent engines across four diverse programming paradigms:
1. **Racket**: Functional reference model featuring exact integers and symbolic analysis.
2. **Factor**: Concatenative implementation in vocabulary `subleq` ensuring complete stack isolation.
3. **Forth**: ANS Forth / Gforth implementation operating over static memory tapes.
4. **Lean 4**: Formally verified executable model compiled to native machine code via Lake.

---

## 5. Machine-Checked Formal Verification in Lean 4

All ten fundamental machine theorems are machine-checked in Lean 4 without `sorry` placeholders or custom axioms:
- **Theorem 1 (Determinism)**: Transitions are deterministic and single-valued.
- **Theorem 2 (Arithmetic Correctness)**: Memory writes strictly satisfy $\mathcal{M}'[b] = \mathcal{M}[b] - \mathcal{M}[a]$.
- **Theorem 3 (Frame Preservation)**: All addresses $x \ne b$ remain unaltered.
- **Theorem 4 (Branch Correctness)**: Program counter updates to $c$ if and only if $r \le 0$.
- **Theorem 5 (Aliasing Correctness)**: When $a = b$, the cell is unconditionally cleared to zero.
- **Theorem 6 (Memory Preservation)**: Memory tape dimensions are conserved across steps.
- **Theorem 7 (Run Determinism)**: Bounded execution $\text{run}(\mathcal{S}, n)$ is deterministic.
- **Theorem 8 (Fuel Monotonicity)**: Terminal halted states are absorbing attractors under extra fuel.
- **Theorem 9 (I/O Invariance)**: Standard arithmetic execution preserves output stream traces.
- **Theorem 10 (Trap Isolation)**: Reserved coprocessor traps cannot execute as standard arithmetic.

---

## 6. Cryptographic Applications & Empirical Benchmarks

### 6.1 SHA-256 in SUBLEQ
A complete 433,968-cell image computes SHA-256 digests in pure SUBLEQ instructions. When evaluated across NIST test vectors (including empty string, `"abc"`, and multi-block strings), all four language engines produce bit-exact matching digests:
- NIST `""`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (101,967 steps)
- NIST `"abc"`: `ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad` (102,856 steps)

### 6.2 Stream Cipher Benchmark ("Killer App")
A 704-cell LCG keystream generator demonstrates stream processing with constant memory footprints under directive I/O, achieving a 1.754x reduction in instructions compared to emulation without hardware wrap/stream directives.

---

## 7. Conclusion

By combining rigorous mathematical formalization in Lean 4 with production implementations in Racket, Factor, and Forth, this project proves that minimal One-Instruction Set Computing can achieve verifiable correctness, practical cryptographic utility, and complete cross-platform deterministic consensus.
