/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Boot, START, mode dispatch, and signed `I_PATH` through to `DIGITS`
(pc 174), with the image constants needed by the place loops.
The default prepared machine has `WIDTH = 0`. Block lemmas, not
end-to-end correctness.
-/

import IntFmt.IPathSign
import IntFmt.PlaceDigits
import IntFmt.RefinementDec

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

theorem image_cell_WIDTH : intfmtImage[14]! = 0 := rfl

theorem prepMachine_get_cap (input mode cap : Word) :
    (prepMachine input mode cap).mem.get 13 = cap := by
  have hmem :
      (prepMachine input mode cap).mem =
        ((loadImage.set addrInput input).set addrMode mode).set addrCap cap := rfl
  rw [hmem, addrInput, addrMode, addrCap]
  exact Mem.get_set_eq _ 13 cap

/-- Nine steps from a prepared machine reach the post-`start_mov` state. -/
theorem prep_runN_9 (input mode cap : Word) :
    runN (prepMachine input mode cap) 9 = afterStartMov input mode cap := by
  have hh : (prepMachine input mode cap).halted = false := rfl
  have hpc : (prepMachine input mode cap).pc.toNat < 32768 := by
    have : (prepMachine input mode cap).pc = 0 := rfl
    simp [this]
  have h1 : runN (prepMachine input mode cap) 1 =
      step (prepMachine input mode cap) :=
    runN_one _ hh hpc
  have h5 : runN (prepMachine input mode cap) 5 =
      runN (step (prepMachine input mode cap)) 4 :=
    (runN_add_eq (prepMachine input mode cap) 1 4 5 rfl).trans (by rw [h1])
  have h9 : runN (prepMachine input mode cap) 9 =
      runN (runN (step (prepMachine input mode cap)) 4) 4 :=
    (runN_add_eq (prepMachine input mode cap) 5 4 9 rfl).trans (by rw [h5])
  exact h9.trans (afterStartMov_eq input mode cap).symm

theorem unsigned_prep_to_digits (input cap : Word) :
    runN (prepMachine input 0 cap) 15 =
      runN (afterStartMov input 0 cap) 6 :=
  (runN_add_eq (prepMachine input 0 cap) 9 6 15 rfl).trans (by rw [prep_runN_9])

theorem signed_prep_to_after_dispatch (input cap : Word) :
    runN (prepMachine input 1 cap) 15 = afterSignedDispatch input cap :=
  ((runN_add_eq (prepMachine input 1 cap) 9 6 15 rfl).trans (by rw [prep_runN_9])).trans
    (afterSignedDispatch_eq input cap).symm

theorem afterStartMov_get_cap (input mode cap : Word) :
    (afterStartMov input mode cap).mem.get 13 = cap := by
  have hsm := start_mov_INPUT_N input mode cap
  have hz := start_zero_regs input mode cap
  have hboot : (step (prepMachine input mode cap)).mem.get 13 = cap := by
    rw [(boot_jmp input mode cap).2.2.1]
    exact prepMachine_get_cap input mode cap
  have h4 : (runN (step (prepMachine input mode cap)) 4).mem.get 13 = cap :=
    ((hz.2.2.2.2.2.2.2.2) 13 (by decide) (by decide) (by decide) (by decide)).trans hboot
  rw [afterStartMov_eq]
  exact (hsm.2.2.2.2.2.2 13 (by decide) (by decide)).trans h4

theorem afterStartMov_get_SIGN (input mode cap : Word) :
    (afterStartMov input mode cap).mem.get 19 = 0 := by
  have hsm := start_mov_INPUT_N input mode cap
  have hz := start_zero_regs input mode cap
  have h4 : (runN (step (prepMachine input mode cap)) 4).mem.get 19 = 0 :=
    hz.2.2.2.1
  rw [afterStartMov_eq]
  exact (hsm.2.2.2.2.2.2 19 (by decide) (by decide)).trans h4

theorem afterStartMov_get_image (input mode cap : Word) (k : Nat)
    (hk : k < 2323)
    (hIn : k ≠ 12) (hMo : k ≠ 15) (hCa : k ≠ 13)
    (hSIGN : k ≠ 19) (hLEN : k ≠ 16) (hPAD : k ≠ 27) (hNDIG : k ≠ 25)
    (hN : k ≠ 17) (hZ : k ≠ 0) :
    (afterStartMov input mode cap).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
  rw [afterStartMov_eq]
  exact start_mov_get input mode cap k hk hIn hMo hCa hSIGN hLEN hPAD hNDIG hN hZ

private theorem const_of_image (input mode cap : Word) (k : Nat) (v : Word)
    (hk : k < 2323)
    (hIn : k ≠ 12) (hMo : k ≠ 15) (hCa : k ≠ 13)
    (hSIGN : k ≠ 19) (hLEN : k ≠ 16) (hPAD : k ≠ 27) (hNDIG : k ≠ 25)
    (hN : k ≠ 17) (hZ : k ≠ 0)
    (himg : intfmtImage[k]! = v) :
    (afterStartMov input mode cap).mem.get (UInt16.ofNat k) = v :=
  (afterStartMov_get_image input mode cap k hk hIn hMo hCa hSIGN hLEN hPAD hNDIG hN hZ).trans himg

/-- After 15 unsigned steps the machine is at `DIGITS` with `N = input`,
`SIGN = 0`, `WIDTH = 0`, and the place-loop constants intact. -/
theorem unsigned_at_digits (input cap : Word) :
    let s := runN (prepMachine input 0 cap) 15
    s.pc = 174 ∧
    s.halted = false ∧
    s.mem.get 0 = 0 ∧
    s.mem.get 17 = input ∧
    s.mem.get 19 = 0 ∧
    s.mem.get 14 = 0 ∧
    s.mem.get 13 = cap ∧
    s.mem.get 3 = 1 ∧
    s.mem.get 4 = 10 ∧
    s.mem.get 5 = 100 ∧
    s.mem.get 6 = 1000 ∧
    s.mem.get 7 = 10000 ∧
    s.mem.get 8 = 48 ∧
    s.mem.get 9 = 45 ∧
    s.mem.get 2322 = 5 ∧
    (∀ k : Nat, 174 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) := by
  intro s
  have hd := mode_dispatch_unsigned input cap
  have hs : s = runN (afterStartMov input 0 cap) 6 := unsigned_prep_to_digits input cap
  have hpresD := hd.2.2.2.2.2.2.2
  have hsDpc : s.pc = 174 := by rw [hs]; exact hd.2.1
  have hsDh : s.halted = false := by rw [hs]; exact hd.2.2.1
  have hsDZ : s.mem.get 0 = 0 := by rw [hs]; exact hd.2.2.2.2.1
  have hsDN : s.mem.get 17 = input := by rw [hs]; exact hd.2.2.2.1
  have hsDS : s.mem.get 19 = 0 := by
    rw [hs]
    exact (hpresD 19 (by decide) (by decide)).trans (afterStartMov_get_SIGN input 0 cap)
  have hsDC : s.mem.get 13 = cap := by
    rw [hs]
    exact (hpresD 13 (by decide) (by decide)).trans (afterStartMov_get_cap input 0 cap)
  have lift (k : Nat) (v : Word)
      (hk : k < 2323)
      (hne12 : k ≠ 12) (hne15 : k ≠ 15) (hne13 : k ≠ 13)
      (hne19 : k ≠ 19) (hne16 : k ≠ 16) (hne27 : k ≠ 27) (hne25 : k ≠ 25)
      (hne17 : k ≠ 17) (hne0 : k ≠ 0)
      (himg : intfmtImage[k]! = v)
      (hne18 : k ≠ 18) :
      s.mem.get (UInt16.ofNat k) = v := by
    rw [hs]
    have h8 := const_of_image input 0 cap k v hk hne12 hne15 hne13 hne19 hne16 hne27 hne25 hne17 hne0 himg
    have hkW : (UInt16.ofNat k) ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have hk0 : (UInt16.ofNat k) ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresD (UInt16.ofNat k) hkW hk0).trans h8
  have hsDW : s.mem.get 14 = 0 := by
    have hk : (14 : Word) = UInt16.ofNat 14 := rfl
    rw [hk]
    exact lift 14 0 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      image_cell_WIDTH (by decide)
  have hsDONE : s.mem.get 3 = 1 := by
    have hk : (3 : Word) = UInt16.ofNat 3 := rfl
    rw [hk]
    exact lift 3 1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      image_cell_ONE (by decide)
  have hsDTEN : s.mem.get 4 = 10 := by
    have hk : (4 : Word) = UInt16.ofNat 4 := rfl
    rw [hk]
    exact lift 4 10 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      image_cell_TEN (by decide)
  have hsDC100 : s.mem.get 5 = 100 := by
    have hk : (5 : Word) = UInt16.ofNat 5 := rfl
    rw [hk]
    exact lift 5 100 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      image_cell_C100 (by decide)
  have hsDC1000 : s.mem.get 6 = 1000 := by
    have hk : (6 : Word) = UInt16.ofNat 6 := rfl
    rw [hk]
    exact lift 6 1000 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      image_cell_C1000 (by decide)
  have hsDC10000 : s.mem.get 7 = 10000 := by
    have hk : (7 : Word) = UInt16.ofNat 7 := rfl
    rw [hk]
    exact lift 7 10000 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      image_cell_C10000 (by decide)
  have hsDK48 : s.mem.get 8 = 48 := by
    have hk : (8 : Word) = UInt16.ofNat 8 := rfl
    rw [hk]
    exact lift 8 48 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      image_cell_K48 (by decide)
  have hsDK45 : s.mem.get 9 = 45 := by
    have hk : (9 : Word) = UInt16.ofNat 9 := rfl
    rw [hk]
    exact lift 9 45 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      image_cell_K45 (by decide)
  have hsDK5 : s.mem.get 2322 = 5 := by
    have hk : (2322 : Word) = UInt16.ofNat 2322 := rfl
    rw [hk]
    exact lift 2322 5 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      image_cell_last (by decide)
  have hcode : ∀ k : Nat, 174 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    rw [hs]
    have h8 := afterStartMov_get_image input 0 cap k (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresD (UInt16.ofNat k) n18 n0).trans h8
  exact ⟨hsDpc, hsDh, hsDZ, hsDN, hsDS, hsDW, hsDC, hsDONE, hsDTEN, hsDC100,
    hsDC1000, hsDC10000, hsDK48, hsDK45, hsDK5, hcode⟩

theorem signed_pos_prep_to_digits (input cap : Word)
    (hpos : 0 < input.toNat) (hhi : input.toNat < 32768) :
    runN (prepMachine input 1 cap) 26 =
      runN (afterSignedDispatch input cap) 11 :=
  (runN_add_eq (prepMachine input 1 cap) 15 11 26 rfl).trans
    (by rw [signed_prep_to_after_dispatch])

theorem signed_zero_prep_to_digits (cap : Word) :
    runN (prepMachine 0 1 cap) 30 =
      runN (afterSignedDispatch 0 cap) 15 :=
  (runN_add_eq (prepMachine 0 1 cap) 15 15 30 rfl).trans
    (by rw [signed_prep_to_after_dispatch])

theorem signed_neg_prep_to_digits (input cap : Word)
    (hneg : 32768 ≤ input.toNat) :
    runN (prepMachine input 1 cap) 40 =
      runN (afterSignedDispatch input cap) 25 :=
  (runN_add_eq (prepMachine input 1 cap) 15 25 40 rfl).trans
    (by rw [signed_prep_to_after_dispatch])

/-- After signed dispatch and the positive `I_PATH` arm, the machine is
at `DIGITS` with `N = input`, `SIGN = 0`, `WIDTH = 0`. -/
theorem signed_pos_at_digits (input cap : Word)
    (hpos : 0 < input.toNat) (hhi : input.toNat < 32768) :
    let s := runN (prepMachine input 1 cap) 26
    s.pc = 174 ∧
    s.halted = false ∧
    s.mem.get 0 = 0 ∧
    s.mem.get 17 = input ∧
    s.mem.get 19 = 0 ∧
    s.mem.get 14 = 0 ∧
    s.mem.get 13 = cap ∧
    s.mem.get 3 = 1 ∧
    s.mem.get 4 = 10 ∧
    s.mem.get 5 = 100 ∧
    s.mem.get 6 = 1000 ∧
    s.mem.get 7 = 10000 ∧
    s.mem.get 8 = 48 ∧
    s.mem.get 9 = 45 ∧
    s.mem.get 2322 = 5 ∧
    (∀ k : Nat, 174 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) := by
  intro s
  have hp := i_path_pos input cap hpos hhi
  have hs : s = runN (afterSignedDispatch input cap) 11 :=
    signed_pos_prep_to_digits input cap hpos hhi
  have hpres := hp.2.2.2.2.2.2
  have hsDpc : s.pc = 174 := by rw [hs]; exact hp.1
  have hsDh : s.halted = false := by rw [hs]; exact hp.2.1
  have hsDZ : s.mem.get 0 = 0 := by rw [hs]; exact hp.2.2.2.2.1
  have hsDN : s.mem.get 17 = input := by rw [hs]; exact hp.2.2.1
  have hsDS : s.mem.get 19 = 0 := by rw [hs]; exact hp.2.2.2.2.2.1
  have hentry := afterSignedDispatch_entry input cap
  have hpresE := hentry.2.2.2.2.2.2
  have hsDC : s.mem.get 13 = cap := by
    rw [hs]
    have hD : (afterSignedDispatch input cap).mem.get 13 =
        (afterStartMov input 1 cap).mem.get 13 :=
      hpresE 13 (by decide) (by decide)
    exact (hpres 13 (by decide) (by decide)).trans
      (hD.trans (afterStartMov_get_cap input 1 cap))
  have lift (k : Nat) (v : Word)
      (hk : k < 2323)
      (hne12 : k ≠ 12) (hne15 : k ≠ 15) (hne13 : k ≠ 13)
      (hne19 : k ≠ 19) (hne16 : k ≠ 16) (hne27 : k ≠ 27) (hne25 : k ≠ 25)
      (hne17 : k ≠ 17) (hne0 : k ≠ 0) (hne18 : k ≠ 18)
      (himg : intfmtImage[k]! = v) :
      s.mem.get (UInt16.ofNat k) = v := by
    rw [hs]
    have hD := afterSignedDispatch_get input cap k hk hne12 hne15 hne13
      hne19 hne16 hne27 hne25 hne17 hne0 hne18
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres (UInt16.ofNat k) n18 n0).trans (hD.trans himg)
  have hsDW : s.mem.get 14 = 0 := by
    have hk : (14 : Word) = UInt16.ofNat 14 := rfl
    rw [hk]
    exact lift 14 0 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_WIDTH
  have hsDONE : s.mem.get 3 = 1 := by
    have hk : (3 : Word) = UInt16.ofNat 3 := rfl
    rw [hk]
    exact lift 3 1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_ONE
  have hsDTEN : s.mem.get 4 = 10 := by
    have hk : (4 : Word) = UInt16.ofNat 4 := rfl
    rw [hk]
    exact lift 4 10 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_TEN
  have hsDC100 : s.mem.get 5 = 100 := by
    have hk : (5 : Word) = UInt16.ofNat 5 := rfl
    rw [hk]
    exact lift 5 100 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_C100
  have hsDC1000 : s.mem.get 6 = 1000 := by
    have hk : (6 : Word) = UInt16.ofNat 6 := rfl
    rw [hk]
    exact lift 6 1000 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_C1000
  have hsDC10000 : s.mem.get 7 = 10000 := by
    have hk : (7 : Word) = UInt16.ofNat 7 := rfl
    rw [hk]
    exact lift 7 10000 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_C10000
  have hsDK48 : s.mem.get 8 = 48 := by
    have hk : (8 : Word) = UInt16.ofNat 8 := rfl
    rw [hk]
    exact lift 8 48 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_K48
  have hsDK45 : s.mem.get 9 = 45 := by
    have hk : (9 : Word) = UInt16.ofNat 9 := rfl
    rw [hk]
    exact lift 9 45 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_K45
  have hsDK5 : s.mem.get 2322 = 5 := by
    have hk : (2322 : Word) = UInt16.ofNat 2322 := rfl
    rw [hk]
    exact lift 2322 5 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_last
  have hcode : ∀ k : Nat, 174 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    rw [hs]
    have hD := afterSignedDispatch_get input cap k (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres (UInt16.ofNat k) n18 n0).trans hD
  exact ⟨hsDpc, hsDh, hsDZ, hsDN, hsDS, hsDW, hsDC, hsDONE, hsDTEN, hsDC100,
    hsDC1000, hsDC10000, hsDK48, hsDK45, hsDK5, hcode⟩

/-- Signed `I_PATH` on input `0` reaches `DIGITS` with `N = 0`, `SIGN = 0`. -/
theorem signed_zero_at_digits (cap : Word) :
    let s := runN (prepMachine 0 1 cap) 30
    s.pc = 174 ∧
    s.halted = false ∧
    s.mem.get 0 = 0 ∧
    s.mem.get 17 = 0 ∧
    s.mem.get 19 = 0 ∧
    s.mem.get 14 = 0 ∧
    s.mem.get 13 = cap ∧
    s.mem.get 3 = 1 ∧
    s.mem.get 4 = 10 ∧
    s.mem.get 5 = 100 ∧
    s.mem.get 6 = 1000 ∧
    s.mem.get 7 = 10000 ∧
    s.mem.get 8 = 48 ∧
    s.mem.get 9 = 45 ∧
    s.mem.get 2322 = 5 ∧
    (∀ k : Nat, 174 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) := by
  intro s
  have hp := i_path_zero cap
  have hs : s = runN (afterSignedDispatch 0 cap) 15 :=
    signed_zero_prep_to_digits cap
  have hpres := hp.2.2.2.2.2.2
  have hsDpc : s.pc = 174 := by rw [hs]; exact hp.1
  have hsDh : s.halted = false := by rw [hs]; exact hp.2.1
  have hsDZ : s.mem.get 0 = 0 := by rw [hs]; exact hp.2.2.2.2.1
  have hsDN : s.mem.get 17 = 0 := by rw [hs]; exact hp.2.2.1
  have hsDS : s.mem.get 19 = 0 := by rw [hs]; exact hp.2.2.2.2.2.1
  have hentry := afterSignedDispatch_entry 0 cap
  have hpresE := hentry.2.2.2.2.2.2
  have hsDC : s.mem.get 13 = cap := by
    rw [hs]
    have hD : (afterSignedDispatch 0 cap).mem.get 13 =
        (afterStartMov 0 1 cap).mem.get 13 :=
      hpresE 13 (by decide) (by decide)
    exact (hpres 13 (by decide) (by decide)).trans
      (hD.trans (afterStartMov_get_cap 0 1 cap))
  have lift (k : Nat) (v : Word)
      (hk : k < 2323)
      (hne12 : k ≠ 12) (hne15 : k ≠ 15) (hne13 : k ≠ 13)
      (hne19 : k ≠ 19) (hne16 : k ≠ 16) (hne27 : k ≠ 27) (hne25 : k ≠ 25)
      (hne17 : k ≠ 17) (hne0 : k ≠ 0) (hne18 : k ≠ 18)
      (himg : intfmtImage[k]! = v) :
      s.mem.get (UInt16.ofNat k) = v := by
    rw [hs]
    have hD := afterSignedDispatch_get 0 cap k hk hne12 hne15 hne13
      hne19 hne16 hne27 hne25 hne17 hne0 hne18
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres (UInt16.ofNat k) n18 n0).trans (hD.trans himg)
  have hsDW : s.mem.get 14 = 0 := by
    have hk : (14 : Word) = UInt16.ofNat 14 := rfl
    rw [hk]
    exact lift 14 0 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_WIDTH
  have hsDONE : s.mem.get 3 = 1 := by
    have hk : (3 : Word) = UInt16.ofNat 3 := rfl
    rw [hk]
    exact lift 3 1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_ONE
  have hsDTEN : s.mem.get 4 = 10 := by
    have hk : (4 : Word) = UInt16.ofNat 4 := rfl
    rw [hk]
    exact lift 4 10 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_TEN
  have hsDC100 : s.mem.get 5 = 100 := by
    have hk : (5 : Word) = UInt16.ofNat 5 := rfl
    rw [hk]
    exact lift 5 100 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_C100
  have hsDC1000 : s.mem.get 6 = 1000 := by
    have hk : (6 : Word) = UInt16.ofNat 6 := rfl
    rw [hk]
    exact lift 6 1000 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_C1000
  have hsDC10000 : s.mem.get 7 = 10000 := by
    have hk : (7 : Word) = UInt16.ofNat 7 := rfl
    rw [hk]
    exact lift 7 10000 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_C10000
  have hsDK48 : s.mem.get 8 = 48 := by
    have hk : (8 : Word) = UInt16.ofNat 8 := rfl
    rw [hk]
    exact lift 8 48 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_K48
  have hsDK45 : s.mem.get 9 = 45 := by
    have hk : (9 : Word) = UInt16.ofNat 9 := rfl
    rw [hk]
    exact lift 9 45 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_K45
  have hsDK5 : s.mem.get 2322 = 5 := by
    have hk : (2322 : Word) = UInt16.ofNat 2322 := rfl
    rw [hk]
    exact lift 2322 5 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_last
  have hcode : ∀ k : Nat, 174 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    rw [hs]
    have hD := afterSignedDispatch_get 0 cap k (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres (UInt16.ofNat k) n18 n0).trans hD
  exact ⟨hsDpc, hsDh, hsDZ, hsDN, hsDS, hsDW, hsDC, hsDONE, hsDTEN, hsDC100,
    hsDC1000, hsDC10000, hsDK48, hsDK45, hsDK5, hcode⟩

/-- After the negative `I_PATH` arm, the machine is at `DIGITS` with
`N = 0 - input`, `SIGN = 1`, `WIDTH = 0`. -/
theorem signed_neg_at_digits (input cap : Word)
    (hneg : 32768 ≤ input.toNat) :
    let s := runN (prepMachine input 1 cap) 40
    s.pc = 174 ∧
    s.halted = false ∧
    s.mem.get 0 = 0 ∧
    s.mem.get 17 = 0 - input ∧
    s.mem.get 19 = 1 ∧
    s.mem.get 14 = 0 ∧
    s.mem.get 13 = cap ∧
    s.mem.get 3 = 1 ∧
    s.mem.get 4 = 10 ∧
    s.mem.get 5 = 100 ∧
    s.mem.get 6 = 1000 ∧
    s.mem.get 7 = 10000 ∧
    s.mem.get 8 = 48 ∧
    s.mem.get 9 = 45 ∧
    s.mem.get 2322 = 5 ∧
    (∀ k : Nat, 174 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) := by
  intro s
  have hp := i_path_neg input cap hneg
  have hs : s = runN (afterSignedDispatch input cap) 25 :=
    signed_neg_prep_to_digits input cap hneg
  -- i_path_neg: pc,h,N,T,Z,SIGN,pres ≠18,0,19,17  (7 conjuncts? )
  -- s25.pc=174 ∧ h ∧ N=0-input ∧ T=0-input ∧ Z=0 ∧ SIGN=1 ∧ pres ≠18,0,19,17
  have hpres := hp.2.2.2.2.2.2
  have hsDpc : s.pc = 174 := by rw [hs]; exact hp.1
  have hsDh : s.halted = false := by rw [hs]; exact hp.2.1
  have hsDN : s.mem.get 17 = 0 - input := by rw [hs]; exact hp.2.2.1
  have hsDZ : s.mem.get 0 = 0 := by rw [hs]; exact hp.2.2.2.2.1
  have hsDS : s.mem.get 19 = 1 := by rw [hs]; exact hp.2.2.2.2.2.1
  have hentry := afterSignedDispatch_entry input cap
  have hpresE := hentry.2.2.2.2.2.2
  have hsDC : s.mem.get 13 = cap := by
    rw [hs]
    have hD : (afterSignedDispatch input cap).mem.get 13 =
        (afterStartMov input 1 cap).mem.get 13 :=
      hpresE 13 (by decide) (by decide)
    exact (hpres 13 (by decide) (by decide) (by decide) (by decide)).trans
      (hD.trans (afterStartMov_get_cap input 1 cap))
  have lift (k : Nat) (v : Word)
      (hk : k < 2323)
      (hne12 : k ≠ 12) (hne15 : k ≠ 15) (hne13 : k ≠ 13)
      (hne19 : k ≠ 19) (hne16 : k ≠ 16) (hne27 : k ≠ 27) (hne25 : k ≠ 25)
      (hne17 : k ≠ 17) (hne0 : k ≠ 0) (hne18 : k ≠ 18)
      (himg : intfmtImage[k]! = v) :
      s.mem.get (UInt16.ofNat k) = v := by
    rw [hs]
    have hD := afterSignedDispatch_get input cap k hk hne12 hne15 hne13
      hne19 hne16 hne27 hne25 hne17 hne0 hne18
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    have n19 : UInt16.ofNat k ≠ (19 : Word) := by
      have : (19 : Word) = UInt16.ofNat 19 := rfl
      rw [this]; exact ofNat_ne k 19 (by omega) (by decide) (by omega)
    have n17 : UInt16.ofNat k ≠ (17 : Word) := by
      have : (17 : Word) = UInt16.ofNat 17 := rfl
      rw [this]; exact ofNat_ne k 17 (by omega) (by decide) (by omega)
    exact (hpres (UInt16.ofNat k) n18 n0 n19 n17).trans (hD.trans himg)
  have hsDW : s.mem.get 14 = 0 := by
    have hk : (14 : Word) = UInt16.ofNat 14 := rfl
    rw [hk]
    exact lift 14 0 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_WIDTH
  have hsDONE : s.mem.get 3 = 1 := by
    have hk : (3 : Word) = UInt16.ofNat 3 := rfl
    rw [hk]
    exact lift 3 1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_ONE
  have hsDTEN : s.mem.get 4 = 10 := by
    have hk : (4 : Word) = UInt16.ofNat 4 := rfl
    rw [hk]
    exact lift 4 10 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_TEN
  have hsDC100 : s.mem.get 5 = 100 := by
    have hk : (5 : Word) = UInt16.ofNat 5 := rfl
    rw [hk]
    exact lift 5 100 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_C100
  have hsDC1000 : s.mem.get 6 = 1000 := by
    have hk : (6 : Word) = UInt16.ofNat 6 := rfl
    rw [hk]
    exact lift 6 1000 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_C1000
  have hsDC10000 : s.mem.get 7 = 10000 := by
    have hk : (7 : Word) = UInt16.ofNat 7 := rfl
    rw [hk]
    exact lift 7 10000 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_C10000
  have hsDK48 : s.mem.get 8 = 48 := by
    have hk : (8 : Word) = UInt16.ofNat 8 := rfl
    rw [hk]
    exact lift 8 48 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_K48
  have hsDK45 : s.mem.get 9 = 45 := by
    have hk : (9 : Word) = UInt16.ofNat 9 := rfl
    rw [hk]
    exact lift 9 45 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_K45
  have hsDK5 : s.mem.get 2322 = 5 := by
    have hk : (2322 : Word) = UInt16.ofNat 2322 := rfl
    rw [hk]
    exact lift 2322 5 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) image_cell_last
  have hcode : ∀ k : Nat, 174 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    rw [hs]
    have hD := afterSignedDispatch_get input cap k (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    have n19 : UInt16.ofNat k ≠ (19 : Word) := by
      have : (19 : Word) = UInt16.ofNat 19 := rfl
      rw [this]; exact ofNat_ne k 19 (by omega) (by decide) (by omega)
    have n17 : UInt16.ofNat k ≠ (17 : Word) := by
      have : (17 : Word) = UInt16.ofNat 17 := rfl
      rw [this]; exact ofNat_ne k 17 (by omega) (by decide) (by omega)
    exact (hpres (UInt16.ofNat k) n18 n0 n19 n17).trans hD
  exact ⟨hsDpc, hsDh, hsDZ, hsDN, hsDS, hsDW, hsDC, hsDONE, hsDTEN, hsDC100,
    hsDC1000, hsDC10000, hsDK48, hsDK45, hsDK5, hcode⟩

end IntFmt
