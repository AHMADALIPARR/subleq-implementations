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
| (5c) Concrete `.dec` execution (end-to-end at default `CAP = 8`, `WIDTH = 0`) | `boot_jmp`, `start_zero_regs` / `start_zero_SIGN` in `StartBlock.lean` (real pc 48: four `ZERO`s clear SIGN/LEN/PAD/NDIG, exit pc 60), `start_mov_INPUT_N` / `start_mov_get` in `StartMov.lean` (pc 60: `MOV INPUT N` leaves `N = input`, `Z = 0`, `pc = 72`), generic `runN_MOV` / `runN_ADD` / `runN_INC` in `Macros.lean`, `mode_mov_MODE_T`, `mode_dispatch_signed` / `mode_dispatch_unsigned` in `IPath.lean` (pc 72: 6 steps, signed mode to `I_PATH` at pc 93, unsigned mode to `DIGITS` at pc 174), `i_path_prelude`, `i_path_pos` / `i_path_zero` / `i_path_neg` in `IPathSign.lean` (from pc 93: positives 11 steps to `DIGITS` with `SIGN = 0` and `T = N`; zero 15 steps with `T = 1`; negatives 25 steps with `SIGN = 1` and `N = T = 0 - N`), `digits_zero_Qs`, `p0_ge_body`, `p0_exit_zero`, `p0_exit_small`, `p0_to_ge_hi`, `p0_to_ge_mid`, and `p0_to_ge_eq` in `Place0.lean` (five `ZERO`s at `DIGITS` reach `P0_LOOP` at pc 189 with `Q0..Q4 = 0`; one `P0_GE` body subtracts 10000 from `N`, increments `Q0`, and returns to `P0_LOOP` in 5 steps; the full `P0_LOOP` compare diamond is proved: `N = 0` exits to `P0_DONE` in 10 steps, `0 < N < 10000` exits in 16 steps, `N ≥ 32768` reaches `P0_GE` in 9 steps, `10000 < N < 32768` reaches `P0_GE` in 13 steps, and `N = 10000` reaches `P0_GE` in 16 steps, none of those arms changing `N` or `Q0`), `p0PlaceSteps` / `p0PlaceSteps_le` / `p0PlaceSteps_ge` (exact, unfolding, and ≤ `16 + 21 * (N / 10000)` step bounds), and `p0_loop` (the full P0 reconstruction invariant: from `P0_LOOP`, `p0PlaceSteps N` steps reach `P0_DONE` with remainder `N < 10000` and `Q0 * 10000 + N` equal to the entry magnitude). The four place loops share one 81-cell encoding: `placeTemplate` / `p1_image` / `p2_image` / `p3_image` in `PlaceImage.lean` prove the assembled image at `P1_LOOP` (270), `P2_LOOP` (351), and `P3_LOOP` (432) matches that template with constants `C1000`/`C100`/`TEN` and `Q1`/`Q2`/`Q3`; `placeSteps` / `placeSteps_ge` / `placeSteps_le` generalize the step count to any positive place constant; `place_loop` in `PlaceLoop.lean` is the parametric reconstruction invariant (well-founded on `N / c`); `p1_loop`, `p2_loop`, and `p3_loop` instantiate it at `P1_LOOP` (270, place 1000, `Q1`), `P2_LOOP` (351, place 100, `Q2`), and `P3_LOOP` (432, place 10, `Q3`). `digits_to_p3_done` / `placeAllSteps` in `PlaceDigits.lean` compose the `DIGITS` prelude with all four place loops to `P3_DONE` (pc 513) and recover the entry `N` as `Q0 = N/10000`, `Q1 = (N/1000)%10`, `Q2 = (N/100)%10`, `Q3 = (N/10)%10`, and ones remainder `N%10` (with `Q4` still 0). `unsigned_at_digits` / `signed_pos_at_digits` / `signed_zero_at_digits` / `signed_neg_at_digits` in `FrontPath.lean` run a prepared machine to `DIGITS` (15 unsigned steps; 26, 30, or 40 signed steps) with `N` the (absolute) input, `SIGN` set, `WIDTH = 0`, and the place-loop constants intact. `ascii_convert` in `Ascii.lean` stores the ones remainder in `Q4` and adds `'0'` (48) to `Q0`..`Q4` in 19 steps from `P3_DONE` (pc 513) to pc 570. `ndig_five` / `ndig_four` / `ndig_three` / `ndig_two` / `ndig_one` in `Ndig.lean` are the leading-zero `NDIG` arms: from pc 570, after the ASCII conversion of `Q0`..`Q3`, they reach `HAVE_DIG` (pc 867) with `NDIG ∈ {1,2,3,4,5}` in 28, 31, 34, 37, or 29 steps respectively (`Q0 ≠ '0'` yields 5 digits; all of `Q0`..`Q3` equal to `'0'` yields 1). `have_dig_sign0` / `have_dig_sign_nz` in `PadLen.lean` set `RAW = NDIG` or `RAW = NDIG + 1` at `HAVE_DIG` (pc 867); `pad_len_width0` / `pad_len_le_raw` / `pad_len_gt_raw` compute `PAD`/`LEN` versus `WIDTH` and reach `LEN_OK` (pc 978); `cap0_halt` takes the `CAP==0` path through `DONE` to `pc = 32768` in 6 steps; `cap_nz_to_sploop` sets `ROOM = CAP - 1` and `IDX = 0` in 11 steps; `sp_loop_pad0` exits `SP_LOOP` immediately when `PAD = 0` and reaches `AFTER_PAD` (pc 1077) in 5 steps; `have_dig_to_after_pad_unsigned` composes the default `WIDTH = 0`, `SIGN = 0`, `CAP > 0` path from `HAVE_DIG` to `AFTER_PAD` in 35 steps (`LEN = NDIG`, `PAD = 0`, `ROOM = CAP - 1`, `IDX = 0`). `after_pad_sign0` in `StoreCh.lean` takes `SIGN = 0` from `AFTER_PAD` (pc 1077) to `EMIT_DIGS` (pc 1575) in 6 steps; the unrolled `STORE_CH` encodings for `ST0`..`ST15` and `STORED`/`RET_*` are bound; `st0_store`..`st15_store` and `store_ch_idx0`..`store_ch_idx15` write `CH` to `BUF+IDX` and reach `STORED` for every `IDX` in `0..15`; `stored_ret_pad` / `stored_ret_sign` / `stored_ret_dig` dispatch on `RETID` from `STORED` to `SP_LOOP` (11 steps, `IDX += 1`, `PAD -= 1`), `AFTER_SIGN` (12 steps, `IDX += 1`), or `DIG_NEXT` (13 steps, `IDX += 1`). `write_space` / `write_minus` in `PadLoop.lean` set `CH` to `' '` or `'-'` and jump to `STORE_CH` in 5 steps; `sp_loop_to_write_space` takes `PAD > 0` and `IDX < ROOM` from `SP_LOOP` (pc 1011) to `WRITE_SPACE` in 20 steps with `RETID = 1`; `write_space_pad_idx0` / `pad_one_iter_idx0` write a space at `BUF+0` and return to `SP_LOOP` with `IDX = 1` and `PAD -= 1` (26 / 46 steps); `after_pad_to_write_minus` takes `SIGN ≠ 0` and `IDX < ROOM` from `AFTER_PAD` to `WRITE_MINUS` in 23 steps with `RETID = 2`; `write_minus_sign_idx0` writes `'-'` at `BUF+0` and returns to `AFTER_SIGN` with `IDX = 1` (27 steps); `after_sign_to_emit` is the 1-step `JMP EMIT_DIGS`; `after_pad_minus_to_emit_idx0` composes the default signed minus path from `AFTER_PAD` with `IDX = 0 < ROOM` to `EMIT_DIGS` in 51 steps (`BUF+0 = '-'`, `IDX = 1`). `emit_prelude` in `EmitDigs.lean` runs the `EMIT_DIGS` prelude in 22 steps to `DIG_LOOP` with `SK = 5 - NDIG` and `DI = 0`; `dig_loop_to_body` takes `DI < 5` from `DIG_LOOP` to `DIG_BODY` in 10 steps; `dig_loop_exit` takes `DI = 5` to `AFTER_DIGS` in 11 steps; `dig_next` increments `DI` and returns to `DIG_LOOP` in 4 steps; `dig_body_skip` takes `DI < SK` from `DIG_BODY` to `DIG_NEXT` in 11 steps with no store; `dig_body_take_eq` / `dig_body_take_gt` take `DI = SK` or `DI > SK` to `TAKE_DIG` in 11 or 7 steps; `take_dig_di0`..`take_dig_di4` dispatch `DI` onto `Q0`..`Q4` and reach `HAVE_CH`; `have_ch_to_store` takes `IDX < ROOM` to `STORE_CH` with `RETID = 3` in 21 steps; `take_store_next_di{0..4}_idx{0..5}` write that digit at `BUF+IDX` and return to `DIG_LOOP`; `skip_next` skips a leading place in 25 steps; `loop_take_eq_*` / `loop_take_gt_*` in `EmitNdig.lean` are the from-`DIG_LOOP` wrappers; `emit_ndig1_idx0`..`emit_ndig5_idx1` run the full `EMIT_DIGS` prelude, skips, and stores for `NDIG ∈ {1..5}` at starting `IDX ∈ {0,1}` and reach `AFTER_DIGS`. `after_digs_nul_at_len` in `WriteNul.lean` takes `LEN < CAP` from `AFTER_DIGS` (pc 1905) to `WRITE_NUL` in 15 steps with `IDX = LEN`; `write_nul_idx0`..`write_nul_idx7` write a NUL at `BUF+IDX` and reach `DONE` (pc 2316) in `11+2·IDX` steps; `write_nul_halt_idx*` / `write_nul_done_idx*` run the `HALT` at `DONE` (`pc = 32768`, then one more `runN` tick sets `halted`); `after_digs_write_nul_done_len0`..`len7` compose those for `LEN = 0..7 < CAP`; `emit_ndig{1..5}_idx{0,1}_write_nul_done` run `EMIT_DIGS` through `WRITE_NUL`/`DONE` to a halted machine with a NUL at `BUF+LEN`. `after_pad_sign0_ndig{1..4}_done` / `have_dig_unsigned_ndig{1..4}_done` / `after_pad_minus_ndig{1..4}_done` in `HaveDigHalt.lean` compose the default `WIDTH = 0` unsigned `HAVE_DIG` path and the signed `AFTER_PAD` minus path through `EMIT_DIGS`/`WRITE_NUL`/`DONE` for `NDIG ∈ {1,2,3,4}` (reaching `pc = 32768` with `halted` set). `write_space_pad_idx1`..`idx7` / `pad_one_iter_idx1`..`idx7` in `PadIter.lean` write one space at `BUF+IDX` for `IDX ∈ {1..7}` and return to `SP_LOOP`; `pad_{1..7}_spaces_idx0` and `pad_{1..7}_to_after_pad` unroll `PAD ∈ {1..7}` from `IDX = 0` through `AFTER_PAD`. `p3_done_unsigned_ndig{1..4}_done` in `AsciiHalt.lean` compose `ascii_convert`, the matching `ndig_*` arm, and `have_dig_unsigned_ndig{1..4}_done` from `P3_DONE` (pc 513) to a halted machine for the default unsigned `WIDTH = 0`, `SIGN = 0` path when the leading-zero pattern yields `NDIG ∈ {1,2,3,4}` (337, 405, 462, and 519 steps respectively). `have_dig_to_after_pad_signed` / `have_dig_signed_ndig{1..4}_done` / `p3_done_signed_ndig{1..4}_done` in `SignHalt.lean` are the matching `SIGN ≠ 0` path: `HAVE_DIG` reaches `AFTER_PAD` in 38 steps with `RAW = LEN = NDIG + 1`, then the minus path through halt, and the `P3_DONE` compositions (389, 459, 518, and 577 steps) write a leading `'-'`, the digits, and a NUL. `after_pad_sign0_ndig5_done` / `after_pad_minus_ndig5_done` / `have_dig_unsigned_ndig5_done` / `have_dig_signed_ndig5_done` / `p3_done_unsigned_ndig5_done` / `p3_done_signed_ndig5_done` in `HaveDigHalt5.lean` are the `NDIG = 5` analogues in both modes (576 unsigned and 636 signed steps from `P3_DONE`), split through intermediate `*_to_after_digs` lemmas so the elaborator does not apply the packaged `emit_ndig5_*_write_nul_done` theorems, `step_JMP`, `step_ZERO`, `step_JLEZ`, `step_SUB`, `step_DEC`, `step_HALT`, `run_intfmtFuel_of_done`, `k48_is_ascii_zero`, `k45_is_ascii_minus`, `formatSpec_neg_uses_minus`, `runN_add`, `runCounted` / `HaltKind` | Independently proved block and macro lemmas on the assembled image, at real listing addresses, composed through start-up, mode dispatch, signed `I_PATH`, the four place loops, ASCII/`NDIG` selection, the default `WIDTH = 0` emit/NUL path, and halt. At default `CAP = 8` and `WIDTH = 0` these are composed into the end-to-end theorems `intfmt_unsigned_e2e` (every `n : Word` in unsigned mode on `prepU n` = `prepMachine n 0 8`) and `intfmt_signed_e2e` / `intfmt_signed_e2e_load` (every `n : Int16` in signed mode on `loadIntfmtDec n` = `prepMachine` of its 16-bit pattern with `MODE = 1`, `CAP = 8`). Both prove `(runCounted _ 2000).kind = programHalt`, `steps ≤ 2000`, `halted`, and that the 8-cell `BUF` together with `LEN` equal `formatSpecUnsigned n` or `formatSpec n` respectively (decimal payload, a terminating NUL, and zero padding of the remainder of the cap-8 buffer; `LEN` is the untruncated payload length). The proved max-case step bounds are 1348 unsigned (`15 + placeAllSteps ≤ 757 + tail 576`) and 1433 signed-negative (`40 + placeAllSteps ≤ 757 + tail 636`), both `≤ 2000`. These theorems do **not** claim a general `WIDTH` or a well-founded pad-writing loop for arbitrary remaining `PAD` or starting `IDX > 7` (only the unrolled `PAD ∈ {1..7}` runs from `IDX = 0`, and one-iteration lemmas at `IDX ∈ {0..7}`, are proved). The default prepared machine has `WIDTH = 0` (so `PAD = 0`). |
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
