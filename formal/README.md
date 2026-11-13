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
| (5) SUBLEQ refinement (structured) | `subleqI16toa_refines_spec`, `putAll_i16toa` | Kernel proof of the *structured* PUT sequence, unchanged. |
| (5b) Concrete `.dec` program identity | `program_identity`, `loadImage_eq_aux`, `intfmtImage_size`, `intfmtImage_prefix16_eq_parse`, `parseDec_line0`, `parse_min_cell`, `image_cell_*` | Kernel proof: the Lean memory image is the 2323-cell assembled artifact (direct lookup, equal to the historical fold). Parser identity on the first 16-cell line, including `-32768`. Full `parseDecText intfmtDecText = intfmtImage` is not kernel-reduced (7239-character `include_str`); it is the deterministic `gen-image.sh` / `check-image.sh` procedure plus interpreter evidence in `formal/results/intfmt-parse-eq.log`. SHA-256 is `intfmtDecSha256` / `formal/results/intfmt.dec.sha256`. |
| (5c) Concrete `.dec` execution | `boot_jmp`, `step_JMP`, `step_ZERO`, `step_JLEZ`, `step_SUB`, `step_DEC`, `step_HALT`, `run_intfmtFuel_of_done` | Kernel proof that a prepared machine executes the boot `JMP START` (cells `0,0,48`) in one `Subleq.step` and lands at cell 48 with Z unchanged. Macro characterisations are in `IntFmt/Macros.lean`. The universal theorem `∀ n : Int16, output (run 2000 (loadIntfmtDec n)) = formatSpec n` is **not yet proved** and is not assumed. C-oracle evidence remains: `test-oracle`, 131128 runs, 0 failures. |
| (6) Execution safety | `Subleq.sub_defined`, `run_fuel0_halted`, `runImage_terminates`, `image_mem_in_range`, `intfmtFuel_gt_maxMeasured` (`2000 > 1266`), `safety_applies` | Defined `UInt16` arithmetic and addressing on this exact image; `run` always terminates. That every input *halts by program HALT* within 2000 steps is still C-oracle evidence (measured max 1266). `run_intfmtFuel_of_done` connects an already-halted state to `run` at fuel 2000. |

Supporting evidence (not a kernel axiom): `intfmt` executable enumerates
all 65536 `Int16` values. Recorded in `formal/results/intfmt-checkAll.log`
as `checkAll: PASS`.

### Deterministic loading of `intfmt.dec`

1. Assemble `microcode/tinyprintf/intfmt.s` with `microcode/tinyprintf/asm16`.
2. `formal/lean/gen-image.sh` (bash/awk, no Python) generates
   `formal/lean/IntFmt/Image.lean` from that `.dec`.
3. `formal/lean/IntFmt/intfmt.dec` is a byte-identical copy, also embedded
   in Lean via `include_str` and parsed by `parseDecText`.
4. `formal/lean/check-image.sh` checks the SHA-256, the copy, and that
   regenerating `Image.lean` is byte-identical.
5. SHA-256 of the official artifact:
   `bc8679df169f382114b779b54e97bdf21bccc94bf6341ca55374f357610f94c6`.

### Mutation tests

`formal/lean/mutation-test.sh` flips a boot branch target, the `'-'`
constant (`K45 = 45`), and the HALT target in a temporary copy of
`Image.lean` and records that `lake build` fails each time
(`formal/results/mutation-test.log`). Because the universal
output-correctness theorem is not yet in the kernel, these tests break
the image-identity / boot / constant-cell theorems that mention those
cells — not a `formatSpec` theorem.

Build (from `formal/lean/`):

```
bash check-image.sh
lake build
./.lake/build/bin/intfmt
bash mutation-test.sh
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
