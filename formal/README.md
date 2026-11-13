# formal/ — isolated proofs for checked 16-bit integer formatting

This directory is self-contained. It does **not** participate in the
repository's existing `lean/` or `lean-fault/` Lake builds, and it must
not be used to modify those trees.

## Authoritative layer: Lean 4 (`formal/lean/`)

Standalone Lake project (`lakefile.lean`, `lean-toolchain` pinned to
Lean 4.35.0). Zero `sorry`, no user axioms. `#print axioms` reports only
standard Lean axioms (`propext`, `Quot.sound`, and in a few theorems
`Classical.choice`).

| Milestone | Theorem(s) | Kind |
|---|---|---|
| (1) Decimal correctness | `i16toa_eq_intToDec`, `value_uToDigits`, `divmodSub_eq` | Kernel proof (induction / `omega`) |
| (2) Min-int safety | `unsignedMag_eq_natAbs`, `i16toa_minInt` | Kernel proof; `-32768` uses unsigned 16-bit magnitude, not signed negation |
| (3) Buffer safety | `snprintf_buf_length`, `snprintf_index_lt_cap`, `snprintf_cap0`, `snprintf_cap1` | Kernel proof |
| (4) Output length | `snprintf_length` (untruncated); `snprintf_cap0` / `snprintf_cap1`; general `snprintf_nul` (`cap>0` writes a NUL at `min(len, cap-1)`) | Kernel proof |
| (5) SUBLEQ refinement | `subleqI16toa_refines_spec`, `putAll_i16toa` | Kernel proof of the *structured* PUT sequence. The assembled `intfmt.dec` is imported as `intfmtImage` with `runImage` over `Subleq.step`. Matching that image to the spec on all Int16 is **C-oracle evidence** (`test-oracle`, 131128 runs, 0 failures), not a kernel proof of the 2323-cell program. |
| (6) Execution safety | `Subleq.sub_defined`, `run_fuel0_halted`, `runImage_terminates`, `image_mem_in_range`, `intfmtFuel_gt_maxMeasured` (`2000 > 1266`) | Defined `UInt16` arithmetic and addressing; `run` always terminates. That every input *halts by program HALT* within 2000 steps is C-oracle evidence (measured max 1266). |

Supporting evidence (not a kernel axiom): `intfmt` executable enumerates
all 65536 `Int16` values. Recorded in `formal/results/intfmt-checkAll.log`
as `checkAll: PASS`.

Build (from `formal/lean/`):

```
lake build
./.lake/build/bin/intfmt
```

Axioms from the successful build are recorded in
`formal/results/lean-axioms.log`.

## Optional layer: Why3 (`formal/why3/`)

Why3 is an independent path, not the official proof layer. It is not
required to build the Lean project. If Why3 + Alt-Ergo/Z3/CVC5 are
installed, proofs can be added under `formal/why3/` later.

## CI

Do not edit `.github/workflows/formal-verification.yml` (that file
belongs to the existing `lean/` tree). Any CI for this project must be
a *new* workflow file.
