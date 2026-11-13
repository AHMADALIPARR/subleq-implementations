/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only
Kernel parse/image identity for lines 800–99 of intfmt.dec.
-/

import IntFmt.DecBindDataB

namespace IntFmt

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem get!_eq_getElem {α : Type _} [Inhabited α] (xs : Array α)
    (i : Nat) (h : i < xs.size) : xs[i]! = xs[i] := by
  exact getElem!_pos xs i h

theorem parse_mapB : decLinesB.map parseDecText = decChunksB := by
  refine map_eq_of_get parseDecText decLinesB decChunksB
    (decLinesB_size.trans decChunksB_size.symm) ?_
  intro i hi
  have hk : i < 50 := by simpa [decLinesB_size] using hi
  have hs : i < decChunksB.size := by simpa [decChunksB_size] using hk
  exact (get!_eq_getElem decLinesB i hi ▸
    get!_eq_getElem decChunksB i hs ▸ parse_atB i hk)

def decTextB : String := catStrings decLinesB 50
def decImageB : Array UInt16 := catArrays decChunksB 50

theorem ws_textB : listEndsWS decTextB.toList :=
  listEndsWS_catStrings decLinesB 50 (by rw [decLinesB_size]; exact Nat.le_refl _) (fun i hi =>
    get!_eq_getElem decLinesB i (by simpa [decLinesB_size] using hi) ▸
      linesB_ws i hi)

theorem parse_textB : parseDecText decTextB = decImageB :=
  (parseDecText_catStrings decLinesB 50 (by rw [decLinesB_size]; exact Nat.le_refl _) (fun i hi =>
    get!_eq_getElem decLinesB i (by simpa [decLinesB_size] using hi) ▸
      linesB_ws i hi)).trans (congrArg (catArrays · 50) parse_mapB)

theorem image_textB : intfmtImage.extract 800 1600 = decImageB := by
  have hle : 50 ≤ decChunksB.size := by rw [decChunksB_size]; exact Nat.le_refl _
  have hfit : 800 + 16 * 50 ≤ intfmtImage.size := by rw [intfmtImage_size]; decide
  have hch : ∀ i, (hi : i < 50) →
      intfmtImage.extract (800 + 16 * i) (800 + 16 * i + 16) =
        decChunksB[i]'(Nat.lt_of_lt_of_le hi hle) := by
    intro i hi
    have hsz : i < decChunksB.size := by simpa [decChunksB_size] using hi
    have h := image_atB i hi
    -- lineStartB i = 16*i, lineStopB i = 16*i+16
    change intfmtImage.extract (lineStartB i) (lineStopB i) = decChunksB[i]! at h
    exact (get!_eq_getElem decChunksB i hsz ▸ h)
  exact extract_chunks16_from intfmtImage decChunksB 800 50 hle hfit hch

end IntFmt
