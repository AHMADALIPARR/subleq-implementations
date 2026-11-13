/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only
Kernel parse/image identity for lines 0–49 of intfmt.dec.
-/

import IntFmt.DecBindDataA

namespace IntFmt

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem get!_eq_getElem {α : Type _} [Inhabited α] (xs : Array α)
    (i : Nat) (h : i < xs.size) : xs[i]! = xs[i] := by
  exact getElem!_pos xs i h

theorem parse_mapA : decLinesA.map parseDecText = decChunksA := by
  refine map_eq_of_get parseDecText decLinesA decChunksA
    (decLinesA_size.trans decChunksA_size.symm) ?_
  intro i hi
  have hk : i < 50 := by simpa [decLinesA_size] using hi
  have hs : i < decChunksA.size := by simpa [decChunksA_size] using hk
  exact (get!_eq_getElem decLinesA i hi ▸
    get!_eq_getElem decChunksA i hs ▸ parse_atA i hk)

def decTextA : String := catStrings decLinesA 50
def decImageA : Array UInt16 := catArrays decChunksA 50

theorem ws_textA : listEndsWS decTextA.toList :=
  listEndsWS_catStrings decLinesA 50 (by rw [decLinesA_size]; exact Nat.le_refl _) (fun i hi =>
    get!_eq_getElem decLinesA i (by simpa [decLinesA_size] using hi) ▸
      linesA_ws i hi)

theorem parse_textA : parseDecText decTextA = decImageA :=
  (parseDecText_catStrings decLinesA 50 (by rw [decLinesA_size]; exact Nat.le_refl _) (fun i hi =>
    get!_eq_getElem decLinesA i (by simpa [decLinesA_size] using hi) ▸
      linesA_ws i hi)).trans (congrArg (catArrays · 50) parse_mapA)

theorem image_textA : intfmtImage.extract 0 800 = decImageA := by
  have hle : 50 ≤ decChunksA.size := by rw [decChunksA_size]; exact Nat.le_refl _
  have hfit : 0 + 16 * 50 ≤ intfmtImage.size := by rw [intfmtImage_size]; decide
  have hch : ∀ i, (hi : i < 50) →
      intfmtImage.extract (0 + 16 * i) (0 + 16 * i + 16) =
        decChunksA[i]'(Nat.lt_of_lt_of_le hi hle) := by
    intro i hi
    have hsz : i < decChunksA.size := by simpa [decChunksA_size] using hi
    have h := image_atA i hi
    -- lineStartA i = 16*i, lineStopA i = 16*i+16
    change intfmtImage.extract (lineStartA i) (lineStopA i) = decChunksA[i]! at h
    exact (get!_eq_getElem decChunksA i hsz ▸ h)
  exact extract_chunks16_from intfmtImage decChunksA 0 50 hle hfit hch

end IntFmt
