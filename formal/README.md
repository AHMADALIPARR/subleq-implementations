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
| (5b) Concrete `.dec` program identity | `program_identity`, `loadImage_eq_aux`, `intfmtImage_size`, `parse_lineXXX`, `image_chunkXXX`, `parse_atA/B/C`, `image_atA/B/C`, `parseDecText_append`, `extract_split` | Kernel proof of per-line identity: each of the 146 `.dec` lines parses (`rfl`) to the corresponding image extract, plus a kernel `parseDecText_append` lemma for newline-terminated fragments. The composite theorem `parseDecText intfmtDecText = intfmtImage` is in the built library (`ParseJoin.lean`): it composes the named `parse_lineXXX` / `image_chunkXXX` lemmas through `parseDecText_append` and `extract_split` in 5-line groups, then prefix-joins A/B/C, without reducing the 2323-cell literal or the `include_str` file copy. `intfmtDecText` is the concatenation of the generated newline-terminated line literals. SHA-256 `intfmtDecSha256` is checked by `check-image.sh`, hooked into `lake build` as the `checkArtifact` extraDep target: a change to the official or embedded `.dec`, the expected digest, `Image.lean`, or the generated chunks/bind data fails the build. |
| (5c) Concrete `.dec` execution (block lemmas, **not** end-to-end) | `boot_jmp`, `start_zero_regs` / `start_zero_SIGN` in `StartBlock.lean` (real pc 48: four `ZERO`s clear SIGN/LEN/PAD/NDIG, exit pc 60), `start_mov_INPUT_N` / `start_mov_get` in `StartMov.lean` (pc 60: `MOV INPUT N` leaves `N = input`, `Z = 0`, `pc = 72`), generic `runN_MOV` / `runN_ADD` / `runN_INC` in `Macros.lean`, `mode_mov_MODE_T`, `mode_dispatch_signed` / `mode_dispatch_unsigned` in `IPath.lean` (pc 72: 6 steps, signed mode to `I_PATH` at pc 93, unsigned mode to `DIGITS` at pc 174), `i_path_prelude`, `i_path_pos` / `i_path_zero` / `i_path_neg` in `IPathSign.lean` (from pc 93: positives 11 steps to `DIGITS` with `SIGN = 0` and `T = N`; zero 15 steps with `T = 1`; negatives 25 steps with `SIGN = 1` and `N = T = 0 - N`), `digits_zero_Qs`, `p0_ge_body`, `p0_exit_zero`, `p0_exit_small`, `p0_to_ge_hi`, `p0_to_ge_mid`, and `p0_to_ge_eq` in `Place0.lean` (five `ZERO`s at `DIGITS` reach `P0_LOOP` at pc 189 with `Q0..Q4 = 0`; one `P0_GE` body subtracts 10000 from `N`, increments `Q0`, and returns to `P0_LOOP` in 5 steps; the full `P0_LOOP` compare diamond is proved: `N = 0` exits to `P0_DONE` in 10 steps, `0 < N < 10000` exits in 16 steps, `N ≥ 32768` reaches `P0_GE` in 9 steps, `10000 < N < 32768` reaches `P0_GE` in 13 steps, and `N = 10000` reaches `P0_GE` in 16 steps, none of those arms changing `N` or `Q0`), `p0PlaceSteps` / `p0PlaceSteps_le` / `p0PlaceSteps_ge` (exact, unfolding, and ≤ `16 + 21 * (N / 10000)` step bounds), and `p0_loop` (the full P0 reconstruction invariant: from `P0_LOOP`, `p0PlaceSteps N` steps reach `P0_DONE` with remainder `N < 10000` and `Q0 * 10000 + N` equal to the entry magnitude). The four place loops share one 81-cell encoding: `placeTemplate` / `p1_image` / `p2_image` / `p3_image` in `PlaceImage.lean` prove the assembled image at `P1_LOOP` (270), `P2_LOOP` (351), and `P3_LOOP` (432) matches that template with constants `C1000`/`C100`/`TEN` and `Q1`/`Q2`/`Q3`; `placeSteps` / `placeSteps_ge` / `placeSteps_le` generalize the step count to any positive place constant; `place_loop` in `PlaceLoop.lean` is the parametric reconstruction invariant (well-founded on `N / c`); `p1_loop`, `p2_loop`, and `p3_loop` instantiate it at `P1_LOOP` (270, place 1000, `Q1`), `P2_LOOP` (351, place 100, `Q2`), and `P3_LOOP` (432, place 10, `Q3`). `ascii_convert` in `Ascii.lean` stores the ones remainder in `Q4` and adds `'0'` (48) to `Q0`..`Q4` in 19 steps from `P3_DONE` (pc 513) to pc 570. `ndig_five` / `ndig_four` / `ndig_three` / `ndig_two` / `ndig_one` in `Ndig.lean` are the leading-zero `NDIG` arms: from pc 570, after the ASCII conversion of `Q0`..`Q3`, they reach `HAVE_DIG` (pc 867) with `NDIG ∈ {1,2,3,4,5}` in 28, 31, 34, 37, or 29 steps respectively (`Q0 ≠ '0'` yields 5 digits; all of `Q0`..`Q3` equal to `'0'` yields 1). `have_dig_sign0` / `have_dig_sign_nz` in `PadLen.lean` set `RAW = NDIG` or `RAW = NDIG + 1` at `HAVE_DIG` (pc 867); `pad_len_width0` / `pad_len_le_raw` / `pad_len_gt_raw` compute `PAD`/`LEN` versus `WIDTH` and reach `LEN_OK` (pc 978); `cap0_halt` takes the `CAP==0` path through `DONE` to `pc = 32768` in 6 steps; `cap_nz_to_sploop` sets `ROOM = CAP - 1` and `IDX = 0` in 11 steps; `sp_loop_pad0` exits `SP_LOOP` immediately when `PAD = 0` and reaches `AFTER_PAD` (pc 1077) in 5 steps; `have_dig_to_after_pad_unsigned` composes the default `WIDTH = 0`, `SIGN = 0`, `CAP > 0` path from `HAVE_DIG` to `AFTER_PAD` in 35 steps (`LEN = NDIG`, `PAD = 0`, `ROOM = CAP - 1`, `IDX = 0`), `step_JMP`, `step_ZERO`, `step_JLEZ`, `step_SUB`, `step_DEC`, `step_HALT`, `run_intfmtFuel_of_done`, `k48_is_ascii_zero`, `k45_is_ascii_minus`, `formatSpec_neg_uses_minus`, `runN_add`, `runCounted` / `HaltKind` | Independently proved block and macro lemmas on the assembled image, at real listing addresses, composed through start-up, mode dispatch, and signed `I_PATH`. They are **not** composed into the universal theorem `∀ n : Int16, (runCounted (loadIntfmtDec n) 2000).kind = programHalt ∧ output = formatSpec n`. Gaps: the general pad-writing loop (`PAD > 0`, `WRITE_SPACE` through the unrolled `STORE_CH` table) and the sign-write path (`SIGN ≠ 0`, `WRITE_MINUS` / `STORE_CH`); `EMIT_DIGS`/`DIG_LOOP` (including per-`NDIG` `STORE_CH`); NUL/LEN writes (`WRITE_NUL`); in-kernel halt-within-2000 for every `Int16` (C-oracle max 1266 is still evidence, not a kernel proof); end-to-end `Halted ∧ output = formatSpec n` for signed and unsigned modes. These remain **block lemmas, not an end-to-end theorem**. |
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
