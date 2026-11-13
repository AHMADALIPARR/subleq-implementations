/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only
Kernel parse/image identity for lines 100–145 of intfmt.dec.
-/

import IntFmt.DecBindDataC

namespace IntFmt

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem get!_eq_getElem {α : Type _} [Inhabited α] (xs : Array α)
    (i : Nat) (h : i < xs.size) : xs[i]! = xs[i] := by
  exact getElem!_pos xs i h

theorem parse_mapC : decLinesC.map parseDecText = decChunksC := by
  refine map_eq_of_get parseDecText decLinesC decChunksC
    (decLinesC_size.trans decChunksC_size.symm) ?_
  intro i hi
  have hk : i < 46 := by simpa [decLinesC_size] using hi
  have hs : i < decChunksC.size := by simpa [decChunksC_size] using hk
  exact (get!_eq_getElem decLinesC i hi ▸
    get!_eq_getElem decChunksC i hs ▸ parse_atC i hk)

def decTextC : String := catStrings decLinesC 46
def decImageC : Array UInt16 := catArrays decChunksC 46

theorem ws_textC : listEndsWS decTextC.toList :=
  listEndsWS_catStrings decLinesC 46 (by rw [decLinesC_size]; exact Nat.le_refl _) (fun i hi =>
    get!_eq_getElem decLinesC i (by simpa [decLinesC_size] using hi) ▸
      linesC_ws i hi)

theorem parse_textC : parseDecText decTextC = decImageC :=
  (parseDecText_catStrings decLinesC 46 (by rw [decLinesC_size]; exact Nat.le_refl _) (fun i hi =>
    get!_eq_getElem decLinesC i (by simpa [decLinesC_size] using hi) ▸
      linesC_ws i hi)).trans (congrArg (catArrays · 46) parse_mapC)

theorem image_textC_body : intfmtImage.extract 1600 2320 = catArrays decChunksC 45 := by
  have hle : 45 ≤ decChunksC.size := by rw [decChunksC_size]; exact Nat.le_refl _; decide
  have hfit : 1600 + 16 * 45 ≤ intfmtImage.size := by rw [intfmtImage_size]; decide
  have hch : ∀ i, (hi : i < 45) →
      intfmtImage.extract (1600 + 16 * i) (1600 + 16 * i + 16) =
        decChunksC[i]'(Nat.lt_of_lt_of_le hi hle) := by
    intro i hi
    have h46 : i < 46 := Nat.lt_trans hi (by decide)
    have hsz : i < decChunksC.size := by simpa [decChunksC_size] using h46
    have h := image_atC i h46
    have hne : ¬ i = 45 := Nat.ne_of_lt hi
    have hstop : lineStopC i = 1600 + 16 * i + 16 := by simp [lineStopC, hne]
    have hstart : lineStartC i = 1600 + 16 * i := rfl
    change intfmtImage.extract (lineStartC i) (lineStopC i) = decChunksC[i]! at h
    rw [hstart, hstop] at h
    exact (get!_eq_getElem decChunksC i hsz ▸ h)
  exact extract_chunks16_from intfmtImage decChunksC 1600 45 hle hfit hch

theorem image_textC : intfmtImage.extract 1600 2323 = decImageC := by
  have hsz : 2323 ≤ intfmtImage.size := by rw [intfmtImage_size]; decide
  have hsplit := extract_split intfmtImage 1600 2320 2323
    (by decide) (by decide) hsz
  have hlast := image_atC 45 (by decide)
  have hlast' : intfmtImage.extract 2320 2323 = decChunksC[45]! := by
    have : lineStartC 45 = 2320 := rfl
    have : lineStopC 45 = 2323 := by simp [lineStopC]
    simpa [lineStartC, lineStopC] using hlast
  have h45 : 45 < decChunksC.size := by rw [decChunksC_size]; exact Nat.le_refl _; decide
  have hcat : catArrays decChunksC 46 =
      catArrays decChunksC 45 ++ decChunksC[45] :=
    catArrays_succ decChunksC 45 h45
  rw [decImageC, hcat, ← image_textC_body, ← hsplit, hlast',
    get!_eq_getElem decChunksC 45 h45]

end IntFmt
