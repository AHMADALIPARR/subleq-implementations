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
| (5b) Concrete `.dec` program identity | `program_identity`, `loadImage_eq_aux`, `intfmtImage_size`, `parse_lineXXX`, `image_chunkXXX`, `parse_atA/B/C`, `image_atA/B/C`, `parseDecText_append`, `extract_split` | Kernel proof of per-line identity: each of the 146 `.dec` lines parses (`rfl`) to the corresponding image extract, plus a kernel `parseDecText_append` lemma for newline-terminated fragments. The single composite theorem `parseDecText intfmtDecText = intfmtImage` is **not** in the built library: composing all 146 chunks in one module exceeded the kernel memory budget (~13 GiB). Draft composition lives in `formal/lean/wip/` and is not part of `lake build`. SHA-256 `intfmtDecSha256` is checked by `check-image.sh`, hooked into `lake build` as the `checkArtifact` extraDep target: a change to the official or embedded `.dec`, the expected digest, `Image.lean`, or the generated chunks/bind data fails the build. |
| (5c) Concrete `.dec` execution (block lemmas, **not** end-to-end) | `boot_jmp`, `start_zero_regs` / `start_zero_SIGN` in `StartBlock.lean` (real pc 48: four `ZERO`s clear SIGN/LEN/PAD/NDIG, exit pc 60), `start_mov_INPUT_N` in `StartMov.lean` (pc 60: `MOV INPUT N` leaves `N = input`, `Z = 0`, `pc = 72`), generic `runN_MOV` / `runN_ADD` / `runN_INC` in `Macros.lean`, `step_JMP`, `step_ZERO`, `step_JLEZ`, `step_SUB`, `step_DEC`, `step_HALT`, `run_intfmtFuel_of_done`, `k48_is_ascii_zero`, `k45_is_ascii_minus`, `formatSpec_neg_uses_minus`, `runN_add`, `runCounted` / `HaltKind` | Independently proved block and macro lemmas on the assembled image, at real listing addresses. They are **not** composed into the universal theorem `∀ n : Int16, (runCounted (loadIntfmtDec n) 2000).kind = programHalt ∧ output = formatSpec n`. Gaps: loop invariants for unsigned compare / repeated-subtraction divmod (`P0_LOOP`..`P3_DONE`), digit emit (`EMIT_DIGS`/`DIG_LOOP`), `I_PATH` sign handling, NUL/LEN writes; in-kernel halt-within-2000 for every `Int16` (C-oracle max 1266 is still evidence, not a kernel proof); kernel `parseDecText intfmtDecText = intfmtImage`. |
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
4. `formal/lean/gen-chunks.sh` and `gen-bind.sh` generate per-line parse
   and image-chunk lemmas (`DecChunksA/B/C.lean`, `DecBindData.lean`).
5. `formal/lean/check-image.sh` checks the SHA-256, the embedded copy,
   that `DecLoad.lean` quotes the same digest, and that regenerating
   `Image.lean`, the chunk modules, and `DecBindData.lean` is
   byte-identical. It is a `lake build` extraDep target (`checkArtifact`)
   — `#eval`-free, `native_decide`-free.
6. SHA-256 of the official artifact:
   `bc8679df169f382114b779b54e97bdf21bccc94bf6341ca55374f357610f94c6`.

### Mutation tests

`formal/lean/mutation-test.sh` records results in
`formal/results/mutation-test.log`.

* Artifact binding: flipping the boot target (`48→49`), ASCII `'0'`
  (`K48`, cell 8, `48→47`), ASCII `'-'` (`K45`, cell 9, `45→44`), or
  the HALT target (`32768→32767`) in `Image.lean` fails `lake build`
  (the extraDep hash/regen check or a cell theorem).
* Semantics: a deliberately altered program (cell 62 of `MOV INPUT N`,
  fall-through `63→64`) with a *matching updated hash* and consistently
  regenerated `Image.lean`, chunks, and bind data still leaves the
  identity modules (`DecLoad`, `Blocks`, `StartBlock`) compiling —
  that cell is not pinned by a public `image_cell_*` lemma — but
  `start_mov_INPUT_N` fails, because the execution theorem reads the
  fall-through from the 16-cell extract inside its proof.

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
