# Blueprint: Native Rosette Microcode Verification Layer

**Status**: Milestone 1 implemented  
**Owner**: Engineering / Agents  
**Related**: `racket/microcode.rkt`, `racket/riscv.rkt`, `docs/verification-report.md`, Goldcrest upstream  
**Goal**: Replace the incomplete Goldcrest-derived Rosette layer with a first-party verification harness that is aligned with the directive machine, fails closed, and is integrated into the test/CI matrix.

---

## 1. Problem Statement

The current Rosette microcode layer (`racket/microcode.rkt` + `racket/riscv.rkt`) is a lightly adapted copy of `compliant.rkt` from ics-jku/goldcrest-microcode-verification. Its limitations are documented in `docs/verification-report.md`:

- Specs only cover register effects of four routines (ADD/ADDI/LUI, SUB, AUIPC, JAL).
- Loads and stores are stubs that alias to ADD.
- No claim of RV32I conformance.
- Model is a separate bitvector model, not the directive machine used by Lean, Racket, Factor, and Forth.
- Original upstream specs failed against this microcode; the harness was later narrowed and made to exit non-zero on failure.

This layer is the weakest part of the verification story and does not strengthen the core SUBLEQ engines. It should be replaced or quarantined behind a clear “research artifact” boundary.

## 2. Objectives

1. Provide a first-party Rosette harness that verifies SUBLEQ microcode sequences against explicit post-conditions.
2. Align the model (register conventions, wraparound, branch polarity, memory effects) with the directive machine used by the rest of the repository.
3. Make the harness fail closed: any counterexample produces a non-zero exit and a clear report.
4. Start with a small, high-value subset (arithmetic + one memory operation) that can be expanded.
5. Integrate the new harness into `make` and the existing CI Racket job.
6. Document the exact scope and remaining gaps so the limitation is explicit.

Non-goals for the first milestone:
- Full RV32I conformance.
- Mechanized correspondence proof between Rosette and Lean (tested correspondence is acceptable).
- Replacement of the Lean formalization or the differential suite.

## 3. Recommended Approach

**Preferred path**: Align with the directive machine rather than continuing the Goldcrest RISC-V microcode line.

Rationale:
- The directive machine already has Lean theorems, four implementations, and a differential suite.
- A Rosette model of the same semantics lets us symbolically check microcode sequences that are intended to run on those engines.
- Avoids inheriting Goldcrest’s register file layout, stub loads/stores, and mismatched specs.

Alternative (lower priority): keep a pure RISC-V microcode research track in a separate directory (`racket/goldcrest/` or `research/`) and clearly mark it as non-blocking for the main verification claim.

## 4. Proposed File Layout

```
racket/
  microcode/                    # new directory
    model.rkt                   # Rosette model of directive machine (or thin adapter)
    sequences.rkt               # hand-written SUBLEQ sequences under our conventions
    specs.rkt                   # post-condition predicates
    verify.rkt                  # harness: symbolic runs, asserts, exit codes
  microcode-legacy/             # optional: move current goldcrest files here
    microcode.rkt
    riscv.rkt
    model.rkt
docs/
  microcode-blueprint.md        # this document
  verification-report.md        # update after implementation
```

Keep the existing `racket/microcode.rkt` and `racket/riscv.rkt` until the new harness is green; then either delete them or move them under a `legacy/` prefix with a README explaining they are not part of the trusted path.

## 5. Model Requirements

The Rosette model must support at least:

- Memory as a vector of bitvectors (or integers with explicit wrap32).
- Program counter, halt flag, and a small set of named registers (or a flat register file).
- The same instruction precedence as the directive machine:
  1. Out-of-bounds fetch → fault
  2. Halt sentinel
  3. Trap (`a = -2`)
  4. Input (`a = -1`)
  5. Output (`b = -1`)
  6. Standard arithmetic + branch on ≤ 0
- Deterministic wraparound behavior that matches the Lean/Racket engines (document the exact width).
- Ability to run a bounded number of steps (fuel) and inspect final state.

If a full re-implementation is too large for the first milestone, a thin adapter that reuses the existing Racket interpreter under Rosette’s symbolic execution is acceptable, provided the symbolic path is exercised and the adapter is documented.

## 6. Initial Instruction Subset

Milestone 1 sequences and specs:

| Operation | Post-condition (informal) | Notes |
|-----------|---------------------------|-------|
| Zero cell | `M[x] = 0` | 1-instruction sequence |
| Move | `M[b] = M[a]`, other cells preserved | via scratch |
| Add | `M[b] = M[b] + M[a]` (wrapped) | |
| Load-word (or equivalent) | destination register/cell receives memory value | requires address calculation or fixed address for v1 |
| Store-word (or equivalent) | memory cell updated, others preserved | |

Each sequence must document:
- Entry PC
- Register/memory contract (which cells are inputs, scratch, outputs)
- Maximum fuel required
- Whether it is self-modifying

## 7. Harness Requirements

`verify.rkt` must:

1. For each sequence, create symbolic inputs for the relevant cells/registers.
2. Execute the sequence under a sufficient fuel limit.
3. Assert the post-condition and frame conditions (untouched cells unchanged).
4. On `sat`, print the model and exit 1.
5. On `unsat` or timeout, report clearly.
6. Include a small set of concrete (non-symbolic) tests that run the same sequences.
7. Support a `--mutation` or manual fault-injection mode so the suite itself can be shown to fail when a sequence or spec is wrong (same discipline as the differential suite).

Exit status contract:
- 0 = all checks passed
- 1 = at least one counterexample or concrete failure
- 2 = harness error (solver missing, bad fuel, etc.)

## 8. Integration

- Add `make verify-microcode` that runs `racket racket/microcode/verify.rkt`.
- Include the target in `make test` (or in the Racket CI job if runtime is a concern).
- Update `.github/workflows/formal-verification.yml` Racket job to install Rosette if not already present and to run the new target.
- Update `docs/verification-report.md` with the new scope, toolchain versions, and results.
- Add a short section to the main README under Formal Verification.

## 9. Acceptance Criteria for Milestone 1

- [x] New harness exists under `racket/microcode/`.
- [x] At least the five operations in the table above have sequences and specs.
- [x] Harness exits 1 when a sequence or spec is deliberately broken (mutation test performed and recorded).
- [x] `make verify-microcode` is green on a clean machine and in CI.
- [x] `docs/verification-report.md` and README describe the exact scope and remaining gaps.
- [x] Legacy Goldcrest files are either removed or clearly marked as non-trusted.

Local `make verify-microcode` exited 0 (103 checks, 0 failed). The CI half of the fourth box is the Racket job on the milestone 1 pull request. See `docs/verification-report.md` for the run and the mutation table. Goldcrest files live in `racket/microcode-legacy/` with their original licence notices and a README that keeps them off the trusted path.

## 10. Risks and Mitigations

| Risk | Mitigation |
|------|------------|
| Rosette solver timeouts | Keep sequences short; start with small bit-widths or concrete bounds; increase fuel only as needed. |
| Model drift from directive machine | Document the exact semantics; add a small differential check between Rosette model and Racket interpreter on concrete programs. |
| Scope creep toward full RV32I | Milestone 1 is explicitly limited to the table in §6. Expansion requires a new milestone. |
| CI runtime | Run only the new harness in the Racket job; keep Lean and full differential as separate steps. |

## 11. Open Questions

1. Should the first memory operations use a flat memory model with absolute addresses, or a register-indirect model closer to RISC-V?
2. Do we want the Rosette model to be a pure re-implementation, or an adapter over the existing Racket interpreter?
3. What is the preferred bit-width for the first milestone (32-bit wrap to match Lean, or smaller for faster solving)?

### Decisions for Milestone 1

1. **Absolute addresses.** Load and Store are moves between a named register cell and a fixed memory cell in the flat image. The directive machine Lean checks is an `Array Int`, not a RISC-V register file, so a register-indirect model would not be that machine. This is the default in §12.
2. **Pure re-implementation, not the §12 adapter-first default.** `racket/subleq.rkt` branches with Racket `cond` and mutates a vector, so it cannot merge symbolic states. The step function is small enough to re-implement. `verify.rkt` compares the model with `run-subleq` on concrete programs, which is the drift mitigation in §10. An adapter that only called the concrete interpreter would not exercise a symbolic path.
3. **32-bit.** Memory cells are 32-bit two's-complement bitvectors. `bvsub` is Lean `wrap32` and `bvsle` is the signed `r ≤ 0` test. This is the §12 default. A narrower width would not be the machine the other engines run.
4. **Precedence follows Lean, not the enumerated list in §5.** That list names a halt sentinel and output on `b = -1`. `lean/Subleq/Machine.lean` and `semantics/subleq-spec.md` have no halt-sentinel opcode: halt is the `c = -1` rule after input, output, and ordinary steps; output is `b < 0`; trap ignores `c` and does not halt. The milestone 1 model follows Lean, because the goal is the machine the Lean, Racket, Factor, and Forth engines already share.
5. **Scratch is arbitrary on entry.** Move, Add, Load, and Store clear Z before using it and clear it again before halt. The sasm macros assume `K0` is already zero. Clearing it makes the post-condition hold for every initial scratch value.
6. **Solver `unknown` or timeout exits 2.** §7 says to report a timeout clearly and reserves exit 1 for a counterexample or concrete failure. A timeout is not a proof, so it is not exit 0.
7. **Legacy placement.** `racket/microcode.rkt`, `racket/model.rkt`, `racket/riscv.rkt`, and `racket/verify.rkt` moved byte-for-byte to `racket/microcode-legacy/` (the layout in §4, including `verify.rkt` because `riscv.rkt` requires it). Headers were not rewritten. `racket/disassemble.rkt` stayed put; only its require path changed. `make verify` still runs the legacy harness so the old command resolves. The CI Racket job runs `make verify-microcode` and `make verify-microcode-mutations` instead of `make metrics`.

## 12. Next Actions

1. Decide the three open questions above (or accept the defaults: absolute addresses, adapter-first, 32-bit).
2. Create the directory skeleton and a failing harness stub.
3. Implement the Zero and Move sequences + specs as the first green commit.
4. Add the remaining operations, mutation test, Make target, and CI hook.
5. Update documentation and mark the milestone complete.

---

*This blueprint is a living document. Update the status and acceptance criteria as work proceeds.*
