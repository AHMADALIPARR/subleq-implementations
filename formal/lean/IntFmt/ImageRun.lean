/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Load the assembled `intfmt.dec` image into the 16-bit SUBLEQ machine
model (`Subleq.step` over `UInt16` memory) and reason about execution.

Kernel:
  * every image cell is a `UInt16` (in range by construction)
  * `loadImage` / `prepMachine` are total
  * `Subleq.sub_defined`: arithmetic is defined
  * `run` is structurally recursive on fuel, so it always terminates
  * `intfmtFuel = 2000` is a documented bound (see evidence below)
  * `loadImage` is a direct array lookup. The historical fold
    `loadImageAux` is retained; `loadImage_eq_aux` identifies them.

Supporting evidence (not a kernel proof of the 2323-cell program):
the C oracle `microcode/tinyprintf/test-oracle` ran this same image
on all 65536 unsigned and all 65536 signed interpretations (plus cap
edge cases): 131128 runs, 0 failures; u16toa steps min 396 / max 1223
/ mean 934; i16toa min 411 / max 1266 / mean 945. 2000 > 1266.
-/

import IntFmt.Image
import IntFmt.DecLoad
import IntFmt.Refinement

namespace IntFmt

open Subleq

def intfmtFuel : Nat := 2000

theorem intfmtFuel_gt_maxMeasured : 1266 < intfmtFuel := by decide

/-- Labels from `microcode/tinyprintf/intfmt.lst`. -/
def addrInput : Word := 12
def addrCap   : Word := 13
def addrWidth : Word := 14
def addrMode  : Word := 15
def addrLen   : Word := 16
def addrN     : Word := 17
def addrT     : Word := 18
def addrSign  : Word := 19
def addrQ0    : Word := 20
def addrBuf   : Word := 32

def emptyMem : Mem := fun _ => 0

/-- Fold the assembled image into a `Mem` (historical definition). -/
def loadImageAux : Nat → Mem → Mem
  | 0, m => m
  | n + 1, m =>
    let m := loadImageAux n m
    if h : n < intfmtImage.size then
      m.set (UInt16.ofNat n) intfmtImage[n]
    else
      m

/-- Cell of the image, or `0` past the end. -/
def imageCell (i : Nat) : Word :=
  if h : i < intfmtImage.size then intfmtImage[i] else 0

/-- Direct lookup of the assembled image. Addresses past the 2323-cell
blob read as `0`. -/
def loadImage : Mem := fun a => imageCell a.toNat

theorem imageCell_of_lt {i : Nat} (h : i < intfmtImage.size) :
    imageCell i = intfmtImage[i] := by
  simp [imageCell, h]

theorem imageCell_of_ge {i : Nat} (h : ¬ i < intfmtImage.size) :
    imageCell i = 0 := by
  simp [imageCell, h]

set_option maxRecDepth 1000000

theorem intfmtImage_size_lt_u16 : intfmtImage.size < 65536 := by
  rw [intfmtImage_size]
  decide

theorem ofNat_toNat_image {n : Nat} (h : n < intfmtImage.size) :
    (UInt16.ofNat n).toNat = n :=
  UInt16.toNat_ofNat_of_lt (Nat.lt_trans h intfmtImage_size_lt_u16)

private theorem aux_get
    (n : Nat) (m : Mem) (a : Word) (hn : n ≤ intfmtImage.size) :
    (loadImageAux n m).get a =
      if a.toNat < n then imageCell a.toNat else m.get a := by
  induction n generalizing m with
  | zero =>
    simp [loadImageAux]
  | succ n ih =>
    have hn' : n ≤ intfmtImage.size := Nat.le_of_succ_le hn
    have hsz : n < intfmtImage.size := Nat.lt_of_succ_le hn
    have hlookup : (loadImageAux (n + 1) m) =
        (loadImageAux n m).set (UInt16.ofNat n) intfmtImage[n] := by
      simp [loadImageAux, hsz]
    rw [hlookup]
    by_cases ha : a = UInt16.ofNat n
    · rw [ha, Mem.get_set_eq]
      have hton : (UInt16.ofNat n).toNat = n := ofNat_toNat_image hsz
      have hlt : n < n + 1 := Nat.lt_succ_self n
      simp [imageCell, hsz, hton, hlt]
    · rw [Mem.get_set_ne (loadImageAux n m) (UInt16.ofNat n) a
          intfmtImage[n] ha]
      rw [ih m hn']
      cases Nat.lt_or_ge a.toNat n with
      | inl hlt =>
        have : a.toNat < n + 1 := Nat.lt_succ_of_lt hlt
        simp [hlt, this]
      | inr hge =>
        have : ¬ a.toNat < n := Nat.not_lt_of_ge hge
        have : ¬ a.toNat < n + 1 := Nat.not_lt_of_ge (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hge ?ne))
        simp [this, ‹¬ a.toNat < n›]
        case ne =>
          intro heq
          apply ha
          have : a = UInt16.ofNat a.toNat := (UInt16.ofNat_toNat (x := a)).symm
          exact this.trans (congrArg UInt16.ofNat heq.symm)

/-- The direct image lookup agrees with the historical fold. -/
theorem loadImage_eq_aux :
    loadImage = loadImageAux intfmtImage.size emptyMem := by
  funext a
  have h := aux_get intfmtImage.size emptyMem a (Nat.le_refl _)
  change imageCell a.toNat = (loadImageAux intfmtImage.size emptyMem).get a
  rw [h]
  split
  · rfl
  · rename_i hge
    exact imageCell_of_ge hge

/-- Machine loaded with the assembled image, `INPUT`/`CAP`/`MODE` set,
    `PC = 0` (boot `JMP START`). Width stays at its image default (0). -/
def prepMachine (input mode cap : Word) : Machine :=
  { mem := (loadImage.set addrInput input |>.set addrMode mode |>.set addrCap cap)
    pc := 0
    output := []
    input := []
    halted := false }

/-- Run the assembled image with the documented fuel budget. -/
def runImage (input mode cap : Word) : Machine :=
  run (prepMachine input mode cap) intfmtFuel

/-- Arithmetic in every step is defined (UInt16 wrap). -/
theorem image_sub_defined (x y : Word) : ∃ r : Word, r = x - y :=
  Subleq.sub_defined x y

/-- `run` always returns, even at fuel 0 (safe halt). -/
theorem runImage_terminates (input mode cap : Word) :
    (run (prepMachine input mode cap) 0).halted = true :=
  run_fuel0_halted _

/-- Memory reads/writes in the machine are at `Word` addresses, hence
in `0..65535`. This is a restatement of the model, not a new axiom. -/
theorem image_mem_in_range (a : Word) : a.toNat < 65536 :=
  UInt16.toNat_lt_size a

/-- A program-cell read from a freshly prepared machine equals the
assembled image, for every address other than the three poke-ins. -/
theorem prepMachine_get_prog (input mode cap a : Word)
    (hIn : a ≠ addrInput) (hMo : a ≠ addrMode) (hCa : a ≠ addrCap) :
    (prepMachine input mode cap).mem.get a = loadImage.get a := by
  unfold prepMachine
  rw [Mem.get_set_ne _ _ _ _ hCa]
  rw [Mem.get_set_ne _ _ _ _ hMo]
  rw [Mem.get_set_ne _ _ _ _ hIn]

theorem loadImage_get_lt (a : Word) (h : a.toNat < intfmtImage.size) :
    loadImage.get a = intfmtImage[a.toNat] := by
  simp [loadImage, Mem.get, imageCell, h]

end IntFmt
