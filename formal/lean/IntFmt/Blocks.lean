/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Compositional lemmas for the *actual* assembled `intfmt.dec` program,
at the real program-counter addresses from `intfmt.lst`.

These lemmas are independently proved. They are **not** an end-to-end
correctness theorem: they have not been composed into

  ∀ n : Int16, (runCounted (loadIntfmtDec n) intfmtFuel).kind = programHalt
    ∧ outputBytes = formatSpec n

The remaining gaps are listed at the end of this module.
-/

import IntFmt.RefinementDec
import IntFmt.Exec
import IntFmt.Macros
import IntFmt.DecLoad
import IntFmt.DecChunksA
import IntFmt.Decimal

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! ## Real PC addresses (from `microcode/tinyprintf/intfmt.lst`) -/

def addrZ : Word := 0
def addrONE : Word := 3
def addrTEN : Word := 4
def addrC10000 : Word := 7
def addrK48 : Word := 8
def addrK45 : Word := 9
def addrK32 : Word := 10
def addrK32768 : Word := 11
def addrSTART : Word := 48
def addrUPath : Word := 90
def addrIPath : Word := 93
def addrDigits : Word := 174
def addrP0Loop : Word := 189
def addrP0Done : Word := 270
def addrP1Loop : Word := 270
def addrP3Done : Word := 513
def addrEmitDigs : Word := 1575
def addrDigLoop : Word := 1641
def addrWriteNul : Word := 1971
def addrDone : Word := 2316

/-! ## Artifact cells used as ASCII / branch constants

These theorems mention the concrete values `48` (ASCII `'0'`), `45`
(ASCII `'-'`), and the boot target `48`. A mutation of those cells that
keeps a matching SHA-256 still fails these lemmas.
-/

theorem k48_is_ascii_zero :
    intfmtImage[8]! = 48 ∧ '0'.toNat = 48 :=
  ⟨image_cell_K48, rfl⟩

theorem k45_is_ascii_minus :
    intfmtImage[9]! = 45 ∧ '-'.toNat = 45 :=
  ⟨image_cell_K45, rfl⟩

/-- Negative `intToDec` results begin with the ASCII minus that `K45`
stores in the assembled image. -/
theorem formatSpec_neg_uses_minus (n : Int) (hn : n < 0) :
    (intToDec n).toList.head? = some '-' ∧
    intfmtImage[9]! = 45 ∧ '-'.toNat = 45 := by
  refine ⟨?hsign, k45_is_ascii_minus.1, k45_is_ascii_minus.2⟩
  simp [intToDec, hn, String.toList_append]

/-! ## START (pc = 48): four ZERO macros

Entry (after the boot `JMP START`): `pc = 48`, `Z = 0`, not halted,
instruction cells are the assembled image. Exit after 4 steps:
`SIGN = LEN = PAD = NDIG = 0`, `pc = 60` (start of `MOV INPUT N`),
`Z` unchanged, remaining memory (except those four cells) unchanged
as far as the four `ZERO`s write only those destinations.

This is a **block lemma**, not an end-to-end theorem.
-/

/-- Read a cell of the assembled image from a 16-cell extract (cheap). -/
theorem image_cell_of_extract (s e i : Nat)
    (he : e ≤ intfmtImage.size) (hse : s ≤ e) (hi : i < e - s) :
    intfmtImage[s + i]! = (intfmtImage.extract s e)[i]! := by
  have hsz : (intfmtImage.extract s e).size = e - s := by
    simp [Array.size_extract, Nat.min_eq_left he]
  have hi' : i < (intfmtImage.extract s e).size := by simpa [hsz] using hi
  have hszi : s + i < intfmtImage.size := by omega
  have : intfmtImage[s + i] = (intfmtImage.extract s e)[i] := by
    simp [Array.getElem_extract]
  have hbang : intfmtImage[s + i]! = intfmtImage[s + i] := getElem!_pos intfmtImage (s + i) hszi
  have hbang' : (intfmtImage.extract s e)[i]! = (intfmtImage.extract s e)[i] :=
    getElem!_pos (intfmtImage.extract s e) i hi'
  exact hbang.trans (this.trans hbang'.symm)

private theorem start_extract :
    intfmtImage.extract 48 64 = decChunk003 := image_chunk003

private theorem start_cell (off : Nat) (h : off < 16) :
    intfmtImage[48 + off]! = decChunk003[off]! := by
  have he : 64 ≤ intfmtImage.size := by rw [intfmtImage_size]; decide
  have := image_cell_of_extract 48 64 off he (by decide) (by omega)
  simpa [start_extract] using this

private theorem chunk003 (off : Nat) (v : UInt16) (h : off < 16)
    (hv : decChunk003[off]! = v) :
    intfmtImage[48 + off]! = v :=
  (start_cell off h).trans hv

theorem image_start_ZERO_SIGN :
    intfmtImage[48]! = 19 ∧ intfmtImage[49]! = 19 ∧ intfmtImage[50]! = 51 :=
  ⟨chunk003 0 19 (by decide) rfl,
    chunk003 1 19 (by decide) rfl,
    chunk003 2 51 (by decide) rfl⟩

theorem image_start_ZERO_LEN :
    intfmtImage[51]! = 16 ∧ intfmtImage[52]! = 16 ∧ intfmtImage[53]! = 54 :=
  ⟨chunk003 3 16 (by decide) rfl,
    chunk003 4 16 (by decide) rfl,
    chunk003 5 54 (by decide) rfl⟩

theorem image_start_ZERO_PAD :
    intfmtImage[54]! = 27 ∧ intfmtImage[55]! = 27 ∧ intfmtImage[56]! = 57 :=
  ⟨chunk003 6 27 (by decide) rfl,
    chunk003 7 27 (by decide) rfl,
    chunk003 8 57 (by decide) rfl⟩

theorem image_start_ZERO_NDIG :
    intfmtImage[57]! = 25 ∧ intfmtImage[58]! = 25 ∧ intfmtImage[59]! = 60 :=
  ⟨chunk003 9 25 (by decide) rfl,
    chunk003 10 25 (by decide) rfl,
    chunk003 11 60 (by decide) rfl⟩

/-! ## Remaining gaps (honest, not assumed)

The following are **not** proved in-kernel for the 2323-cell program:

* `start_zero_regs` is proved in `StartBlock.lean` (four `ZERO`s at pc 48
  clear SIGN/LEN/PAD/NDIG and exit at pc 60), using the START encodings
  `image_start_ZERO_*` and `step_ZERO`, without reducing the 2323-cell literal.
* Concrete `MOV INPUT N` at pc 60 is proved in `StartMov.lean`
  (`start_mov_INPUT_N`: after the four START `ZERO`s, four more
  steps leave `N = input`, `Z = 0`, `pc = 72`). Generic
  `runN_MOV` / `runN_ADD` / `runN_INC` are proved in `Macros.lean`.
  The fall-through at cell 62 is read from the 16-cell extract
  inside the execution proof, not from a public identity lemma.
* Loop invariants for the unsigned compare / repeated-subtraction
  divmod at `P0_LOOP..P3_DONE` (pcs 189–513), the digit push / skip /
  pop+emit loop (`EMIT_DIGS` / `DIG_LOOP`, pcs 1575–1905), sign
  handling at `I_PATH` (pc 93), and the NUL / LEN writes
  (`WRITE_NUL`, pc 1971).
* Kernel parse/image identity `parseDecText intfmtDecText = intfmtImage`
  is proved in `ParseJoin.lean` by composing the named chunk lemmas.
* In-kernel termination: `∀ n, (runCounted (loadIntfmtDec n) 2000).kind
  = programHalt` with an explicit step count. The C-oracle bound
  (max 1266 < 2000) is still evidence, not a kernel proof.
* The end-to-end theorem
  `∀ n : Int16, Halted (run P n 2000) ∧ output = formatSpec n`.

`HaltKind` / `runCounted` in `Exec.lean` distinguish program HALT from
fuel exhaustion, ready to be used once the block lemmas compose.
-/

end IntFmt
