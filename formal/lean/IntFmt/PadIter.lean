/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

`SP_LOOP` padding iterations at `IDX = 1..7`. Block lemmas, not
end-to-end correctness.
-/

import IntFmt.PadLoop

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000


/-- From `WRITE_SPACE` with `IDX = 1` and `RETID = 1`: write a space at
`BUF+1` and return to `SP_LOOP` with `IDX = 2` and `PAD -= 1`. 28 steps. -/
theorem write_space_pad_idx1 {s : Machine}
    (hpc : s.pc = 1155)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 1)
    (hR : s.mem.get 2319 = 1)
    (hcode : ∀ k : Nat, 1155 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sW := runN s 28
    sW.pc = 1011 ∧
    sW.halted = false ∧
    sW.mem.get 0 = 0 ∧
    sW.mem.get 33 = 32 ∧
    sW.mem.get 29 = 2 ∧
    sW.mem.get 27 = s.mem.get 27 - 1 ∧
    (∀ a, a ≠ 33 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      sW.mem.get a = s.mem.get a) := by
  intro sW
  have hw := write_space (s := s) hpc hh hZ hK32
    (fun k h1 h2 => hcode k h1 (by omega))
  let s5 := runN s 5
  have hs5pc : s5.pc = 1185 := hw.1
  have hs5h : s5.halted = false := hw.2.1
  have hs5Z : s5.mem.get 0 = 0 := hw.2.2.1
  have hs5CH : s5.mem.get 30 = 32 := hw.2.2.2.1
  have hpres5 := hw.2.2.2.2
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hI5 : s5.mem.get 29 = 1 := (hpres5 29 (by decide) (by decide)).trans hI
  have hR5 : s5.mem.get 2319 = 1 := (hpres5 2319 (by decide) (by decide)).trans hR
  have hP5 : s5.mem.get 27 = s.mem.get 27 := hpres5 27 (by decide) (by decide)
  have g5 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have hs := store_ch_idx1 (s := s5) hs5pc hs5h hs5Z hONE5 hI5 g5
  have hrunM : runN s 17 = runN s5 12 := runN_add_eq s 5 12 17 (by decide)
  let sM := runN s 17
  have hsMpc : sM.pc = 1527 := by
    have : sM = runN s5 12 := hrunM; rw [this]; exact hs.1
  have hsMh : sM.halted = false := by
    have : sM = runN s5 12 := hrunM; rw [this]; exact hs.2.1
  have hsMZ : sM.mem.get 0 = 0 := by
    have : sM = runN s5 12 := hrunM; rw [this]; exact hs.2.2.1
  have hsMB : sM.mem.get 33 = 32 := by
    have : sM = runN s5 12 := hrunM
    rw [this]; exact hs.2.2.2.1.trans hs5CH
  have hsMI : sM.mem.get 29 = 1 := by
    have : sM = runN s5 12 := hrunM; rw [this]; exact hs.2.2.2.2.1
  have hONEM : sM.mem.get 3 = 1 := by
    have : sM = runN s5 12 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 3 (by decide) (by decide) (by decide)).trans hONE5
  have hRM : sM.mem.get 2319 = 1 := by
    have : sM = runN s5 12 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hR5
  have hPM : sM.mem.get 27 = s.mem.get 27 := by
    have : sM = runN s5 12 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 27 (by decide) (by decide) (by decide)).trans hP5
  have hpresM : ∀ a, a ≠ 33 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sM.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    have : sM = runN s5 12 := hrunM
    rw [this]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres5 a ha30 ha0)
  have gM : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      sM.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresM (UInt16.ofNat k) n33 n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hr := stored_ret_pad (s := sM) hsMpc hsMh hsMZ hONEM hRM gM
  have hrun : sW = runN sM 11 := runN_add_eq s 17 11 28 (by decide)
  have hsWpc : sW.pc = 1011 := by rw [hrun]; exact hr.1
  have hsWh : sW.halted = false := by rw [hrun]; exact hr.2.1
  have hsWZ : sW.mem.get 0 = 0 := by rw [hrun]; exact hr.2.2.1
  have hsWI : sW.mem.get 29 = 2 := by
    rw [hrun]
    have : sM.mem.get 29 + 1 = (1 : Word) + 1 := by rw [hsMI]
    exact hr.2.2.2.1.trans (this.trans (rfl : (1 : Word) + 1 = 2))
  have hsWP : sW.mem.get 27 = s.mem.get 27 - 1 := by
    rw [hrun]
    exact hr.2.2.2.2.1.trans (by rw [hPM])
  have hsWB : sW.mem.get 33 = 32 := by
    rw [hrun]
    exact (hr.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide)).trans hsMB
  have hpres : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      sW.mem.get a = s.mem.get a := by
    intro a haB ha29 ha27 ha18 ha30 ha0
    rw [hrun]
    exact (hr.2.2.2.2.2 a ha29 ha27 ha18 ha0).trans (hpresM a haB ha18 ha30 ha0)
  exact ⟨hsWpc, hsWh, hsWZ, hsWB, hsWI, hsWP, hpres⟩

/-- From `SP_LOOP` with `PAD > 0`, `IDX = 1 < ROOM`: write a space at
`BUF+1` and return to `SP_LOOP` with `IDX = 2` and `PAD -= 1`. 48 steps. -/
theorem pad_one_iter_idx1 {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 1)
    (hPlo : 0 < (s.mem.get 27).toNat)
    (hPhi : (s.mem.get 27).toNat < 32768)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sI := runN s 48
    sI.pc = 1011 ∧
    sI.halted = false ∧
    sI.mem.get 0 = 0 ∧
    sI.mem.get 33 = 32 ∧
    sI.mem.get 29 = 2 ∧
    sI.mem.get 27 = s.mem.get 27 - 1 ∧
    (∀ a, a ≠ 33 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      sI.mem.get a = s.mem.get a) := by
  intro sI
  have hIlt : (s.mem.get 29).toNat < (s.mem.get 28).toNat := by
    rw [hI]; simp; exact hRlo
  have hw := sp_loop_to_write_space (s := s) hpc hh hZ hONE hPlo hPhi hIlt hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s20 := runN s 20
  have hs20pc : s20.pc = 1155 := hw.1
  have hs20h : s20.halted = false := hw.2.1
  have hs20Z : s20.mem.get 0 = 0 := hw.2.2.1
  have hs20R : s20.mem.get 2319 = 1 := hw.2.2.2.1
  have hs20P : s20.mem.get 27 = s.mem.get 27 := hw.2.2.2.2.1
  have hs20I : s20.mem.get 29 = 1 := hw.2.2.2.2.2.1.trans hI
  have hpres20 := hw.2.2.2.2.2.2.2
  have hONE20 : s20.mem.get 3 = 1 := (hpres20 3 (by decide) (by decide) (by decide)).trans hONE
  have hK20 : s20.mem.get 10 = 32 := (hpres20 10 (by decide) (by decide) (by decide)).trans hK32
  have g20 : ∀ k : Nat, 1155 ≤ k → k < 1575 →
      s20.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres20 (UInt16.ofNat k) n18 n2319 n0).trans (hcode k (by omega) (by omega))
  have hw2 := write_space_pad_idx1 (s := s20) hs20pc hs20h hs20Z hONE20 hK20 hs20I hs20R g20
  have hrun : sI = runN s20 28 := runN_add_eq s 20 28 48 (by decide)
  have hsIpc : sI.pc = 1011 := by rw [hrun]; exact hw2.1
  have hsIh : sI.halted = false := by rw [hrun]; exact hw2.2.1
  have hsIZ : sI.mem.get 0 = 0 := by rw [hrun]; exact hw2.2.2.1
  have hsIB : sI.mem.get 33 = 32 := by rw [hrun]; exact hw2.2.2.2.1
  have hsII : sI.mem.get 29 = 2 := by rw [hrun]; exact hw2.2.2.2.2.1
  have hsIP : sI.mem.get 27 = s.mem.get 27 - 1 := by
    rw [hrun, hw2.2.2.2.2.2.1, hs20P]
  have hpres : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      sI.mem.get a = s.mem.get a := by
    intro a haB ha29 ha27 ha18 ha30 haR ha0
    rw [hrun]
    exact (hw2.2.2.2.2.2.2 a haB ha29 ha27 ha18 ha30 ha0).trans
      (hpres20 a ha18 haR ha0)
  exact ⟨hsIpc, hsIh, hsIZ, hsIB, hsII, hsIP, hpres⟩

/-- From `WRITE_SPACE` with `IDX = 2` and `RETID = 1`: write a space at
`BUF+2` and return to `SP_LOOP` with `IDX = 3` and `PAD -= 1`. 30 steps. -/
theorem write_space_pad_idx2 {s : Machine}
    (hpc : s.pc = 1155)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 2)
    (hR : s.mem.get 2319 = 1)
    (hcode : ∀ k : Nat, 1155 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sW := runN s 30
    sW.pc = 1011 ∧
    sW.halted = false ∧
    sW.mem.get 0 = 0 ∧
    sW.mem.get 34 = 32 ∧
    sW.mem.get 29 = 3 ∧
    sW.mem.get 27 = s.mem.get 27 - 1 ∧
    (∀ a, a ≠ 34 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      sW.mem.get a = s.mem.get a) := by
  intro sW
  have hw := write_space (s := s) hpc hh hZ hK32
    (fun k h1 h2 => hcode k h1 (by omega))
  let s5 := runN s 5
  have hs5pc : s5.pc = 1185 := hw.1
  have hs5h : s5.halted = false := hw.2.1
  have hs5Z : s5.mem.get 0 = 0 := hw.2.2.1
  have hs5CH : s5.mem.get 30 = 32 := hw.2.2.2.1
  have hpres5 := hw.2.2.2.2
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hI5 : s5.mem.get 29 = 2 := (hpres5 29 (by decide) (by decide)).trans hI
  have hR5 : s5.mem.get 2319 = 1 := (hpres5 2319 (by decide) (by decide)).trans hR
  have hP5 : s5.mem.get 27 = s.mem.get 27 := hpres5 27 (by decide) (by decide)
  have g5 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have hs := store_ch_idx2 (s := s5) hs5pc hs5h hs5Z hONE5 hI5 g5
  have hrunM : runN s 19 = runN s5 14 := runN_add_eq s 5 14 19 (by decide)
  let sM := runN s 19
  have hsMpc : sM.pc = 1527 := by
    have : sM = runN s5 14 := hrunM; rw [this]; exact hs.1
  have hsMh : sM.halted = false := by
    have : sM = runN s5 14 := hrunM; rw [this]; exact hs.2.1
  have hsMZ : sM.mem.get 0 = 0 := by
    have : sM = runN s5 14 := hrunM; rw [this]; exact hs.2.2.1
  have hsMB : sM.mem.get 34 = 32 := by
    have : sM = runN s5 14 := hrunM
    rw [this]; exact hs.2.2.2.1.trans hs5CH
  have hsMI : sM.mem.get 29 = 2 := by
    have : sM = runN s5 14 := hrunM; rw [this]; exact hs.2.2.2.2.1
  have hONEM : sM.mem.get 3 = 1 := by
    have : sM = runN s5 14 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 3 (by decide) (by decide) (by decide)).trans hONE5
  have hRM : sM.mem.get 2319 = 1 := by
    have : sM = runN s5 14 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hR5
  have hPM : sM.mem.get 27 = s.mem.get 27 := by
    have : sM = runN s5 14 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 27 (by decide) (by decide) (by decide)).trans hP5
  have hpresM : ∀ a, a ≠ 34 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sM.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    have : sM = runN s5 14 := hrunM
    rw [this]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres5 a ha30 ha0)
  have gM : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      sM.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresM (UInt16.ofNat k) n34 n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hr := stored_ret_pad (s := sM) hsMpc hsMh hsMZ hONEM hRM gM
  have hrun : sW = runN sM 11 := runN_add_eq s 19 11 30 (by decide)
  have hsWpc : sW.pc = 1011 := by rw [hrun]; exact hr.1
  have hsWh : sW.halted = false := by rw [hrun]; exact hr.2.1
  have hsWZ : sW.mem.get 0 = 0 := by rw [hrun]; exact hr.2.2.1
  have hsWI : sW.mem.get 29 = 3 := by
    rw [hrun]
    have : sM.mem.get 29 + 1 = (2 : Word) + 1 := by rw [hsMI]
    exact hr.2.2.2.1.trans (this.trans (rfl : (2 : Word) + 1 = 3))
  have hsWP : sW.mem.get 27 = s.mem.get 27 - 1 := by
    rw [hrun]
    exact hr.2.2.2.2.1.trans (by rw [hPM])
  have hsWB : sW.mem.get 34 = 32 := by
    rw [hrun]
    exact (hr.2.2.2.2.2 34 (by decide) (by decide) (by decide) (by decide)).trans hsMB
  have hpres : ∀ a, a ≠ 34 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      sW.mem.get a = s.mem.get a := by
    intro a haB ha29 ha27 ha18 ha30 ha0
    rw [hrun]
    exact (hr.2.2.2.2.2 a ha29 ha27 ha18 ha0).trans (hpresM a haB ha18 ha30 ha0)
  exact ⟨hsWpc, hsWh, hsWZ, hsWB, hsWI, hsWP, hpres⟩

/-- From `SP_LOOP` with `PAD > 0`, `IDX = 2 < ROOM`: write a space at
`BUF+2` and return to `SP_LOOP` with `IDX = 3` and `PAD -= 1`. 50 steps. -/
theorem pad_one_iter_idx2 {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 2)
    (hPlo : 0 < (s.mem.get 27).toNat)
    (hPhi : (s.mem.get 27).toNat < 32768)
    (hRlo : 2 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sI := runN s 50
    sI.pc = 1011 ∧
    sI.halted = false ∧
    sI.mem.get 0 = 0 ∧
    sI.mem.get 34 = 32 ∧
    sI.mem.get 29 = 3 ∧
    sI.mem.get 27 = s.mem.get 27 - 1 ∧
    (∀ a, a ≠ 34 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      sI.mem.get a = s.mem.get a) := by
  intro sI
  have hIlt : (s.mem.get 29).toNat < (s.mem.get 28).toNat := by
    rw [hI]; simp; exact hRlo
  have hw := sp_loop_to_write_space (s := s) hpc hh hZ hONE hPlo hPhi hIlt hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s20 := runN s 20
  have hs20pc : s20.pc = 1155 := hw.1
  have hs20h : s20.halted = false := hw.2.1
  have hs20Z : s20.mem.get 0 = 0 := hw.2.2.1
  have hs20R : s20.mem.get 2319 = 1 := hw.2.2.2.1
  have hs20P : s20.mem.get 27 = s.mem.get 27 := hw.2.2.2.2.1
  have hs20I : s20.mem.get 29 = 2 := hw.2.2.2.2.2.1.trans hI
  have hpres20 := hw.2.2.2.2.2.2.2
  have hONE20 : s20.mem.get 3 = 1 := (hpres20 3 (by decide) (by decide) (by decide)).trans hONE
  have hK20 : s20.mem.get 10 = 32 := (hpres20 10 (by decide) (by decide) (by decide)).trans hK32
  have g20 : ∀ k : Nat, 1155 ≤ k → k < 1575 →
      s20.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres20 (UInt16.ofNat k) n18 n2319 n0).trans (hcode k (by omega) (by omega))
  have hw2 := write_space_pad_idx2 (s := s20) hs20pc hs20h hs20Z hONE20 hK20 hs20I hs20R g20
  have hrun : sI = runN s20 30 := runN_add_eq s 20 30 50 (by decide)
  have hsIpc : sI.pc = 1011 := by rw [hrun]; exact hw2.1
  have hsIh : sI.halted = false := by rw [hrun]; exact hw2.2.1
  have hsIZ : sI.mem.get 0 = 0 := by rw [hrun]; exact hw2.2.2.1
  have hsIB : sI.mem.get 34 = 32 := by rw [hrun]; exact hw2.2.2.2.1
  have hsII : sI.mem.get 29 = 3 := by rw [hrun]; exact hw2.2.2.2.2.1
  have hsIP : sI.mem.get 27 = s.mem.get 27 - 1 := by
    rw [hrun, hw2.2.2.2.2.2.1, hs20P]
  have hpres : ∀ a, a ≠ 34 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      sI.mem.get a = s.mem.get a := by
    intro a haB ha29 ha27 ha18 ha30 haR ha0
    rw [hrun]
    exact (hw2.2.2.2.2.2.2 a haB ha29 ha27 ha18 ha30 ha0).trans
      (hpres20 a ha18 haR ha0)
  exact ⟨hsIpc, hsIh, hsIZ, hsIB, hsII, hsIP, hpres⟩

/-- From `WRITE_SPACE` with `IDX = 3` and `RETID = 1`: write a space at
`BUF+3` and return to `SP_LOOP` with `IDX = 4` and `PAD -= 1`. 32 steps. -/
theorem write_space_pad_idx3 {s : Machine}
    (hpc : s.pc = 1155)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 3)
    (hR : s.mem.get 2319 = 1)
    (hcode : ∀ k : Nat, 1155 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sW := runN s 32
    sW.pc = 1011 ∧
    sW.halted = false ∧
    sW.mem.get 0 = 0 ∧
    sW.mem.get 35 = 32 ∧
    sW.mem.get 29 = 4 ∧
    sW.mem.get 27 = s.mem.get 27 - 1 ∧
    (∀ a, a ≠ 35 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      sW.mem.get a = s.mem.get a) := by
  intro sW
  have hw := write_space (s := s) hpc hh hZ hK32
    (fun k h1 h2 => hcode k h1 (by omega))
  let s5 := runN s 5
  have hs5pc : s5.pc = 1185 := hw.1
  have hs5h : s5.halted = false := hw.2.1
  have hs5Z : s5.mem.get 0 = 0 := hw.2.2.1
  have hs5CH : s5.mem.get 30 = 32 := hw.2.2.2.1
  have hpres5 := hw.2.2.2.2
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hI5 : s5.mem.get 29 = 3 := (hpres5 29 (by decide) (by decide)).trans hI
  have hR5 : s5.mem.get 2319 = 1 := (hpres5 2319 (by decide) (by decide)).trans hR
  have hP5 : s5.mem.get 27 = s.mem.get 27 := hpres5 27 (by decide) (by decide)
  have g5 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have hs := store_ch_idx3 (s := s5) hs5pc hs5h hs5Z hONE5 hI5 g5
  have hrunM : runN s 21 = runN s5 16 := runN_add_eq s 5 16 21 (by decide)
  let sM := runN s 21
  have hsMpc : sM.pc = 1527 := by
    have : sM = runN s5 16 := hrunM; rw [this]; exact hs.1
  have hsMh : sM.halted = false := by
    have : sM = runN s5 16 := hrunM; rw [this]; exact hs.2.1
  have hsMZ : sM.mem.get 0 = 0 := by
    have : sM = runN s5 16 := hrunM; rw [this]; exact hs.2.2.1
  have hsMB : sM.mem.get 35 = 32 := by
    have : sM = runN s5 16 := hrunM
    rw [this]; exact hs.2.2.2.1.trans hs5CH
  have hsMI : sM.mem.get 29 = 3 := by
    have : sM = runN s5 16 := hrunM; rw [this]; exact hs.2.2.2.2.1
  have hONEM : sM.mem.get 3 = 1 := by
    have : sM = runN s5 16 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 3 (by decide) (by decide) (by decide)).trans hONE5
  have hRM : sM.mem.get 2319 = 1 := by
    have : sM = runN s5 16 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hR5
  have hPM : sM.mem.get 27 = s.mem.get 27 := by
    have : sM = runN s5 16 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 27 (by decide) (by decide) (by decide)).trans hP5
  have hpresM : ∀ a, a ≠ 35 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sM.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    have : sM = runN s5 16 := hrunM
    rw [this]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres5 a ha30 ha0)
  have gM : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      sM.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresM (UInt16.ofNat k) n35 n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hr := stored_ret_pad (s := sM) hsMpc hsMh hsMZ hONEM hRM gM
  have hrun : sW = runN sM 11 := runN_add_eq s 21 11 32 (by decide)
  have hsWpc : sW.pc = 1011 := by rw [hrun]; exact hr.1
  have hsWh : sW.halted = false := by rw [hrun]; exact hr.2.1
  have hsWZ : sW.mem.get 0 = 0 := by rw [hrun]; exact hr.2.2.1
  have hsWI : sW.mem.get 29 = 4 := by
    rw [hrun]
    have : sM.mem.get 29 + 1 = (3 : Word) + 1 := by rw [hsMI]
    exact hr.2.2.2.1.trans (this.trans (rfl : (3 : Word) + 1 = 4))
  have hsWP : sW.mem.get 27 = s.mem.get 27 - 1 := by
    rw [hrun]
    exact hr.2.2.2.2.1.trans (by rw [hPM])
  have hsWB : sW.mem.get 35 = 32 := by
    rw [hrun]
    exact (hr.2.2.2.2.2 35 (by decide) (by decide) (by decide) (by decide)).trans hsMB
  have hpres : ∀ a, a ≠ 35 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      sW.mem.get a = s.mem.get a := by
    intro a haB ha29 ha27 ha18 ha30 ha0
    rw [hrun]
    exact (hr.2.2.2.2.2 a ha29 ha27 ha18 ha0).trans (hpresM a haB ha18 ha30 ha0)
  exact ⟨hsWpc, hsWh, hsWZ, hsWB, hsWI, hsWP, hpres⟩

/-- From `SP_LOOP` with `PAD > 0`, `IDX = 3 < ROOM`: write a space at
`BUF+3` and return to `SP_LOOP` with `IDX = 4` and `PAD -= 1`. 52 steps. -/
theorem pad_one_iter_idx3 {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 3)
    (hPlo : 0 < (s.mem.get 27).toNat)
    (hPhi : (s.mem.get 27).toNat < 32768)
    (hRlo : 3 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sI := runN s 52
    sI.pc = 1011 ∧
    sI.halted = false ∧
    sI.mem.get 0 = 0 ∧
    sI.mem.get 35 = 32 ∧
    sI.mem.get 29 = 4 ∧
    sI.mem.get 27 = s.mem.get 27 - 1 ∧
    (∀ a, a ≠ 35 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      sI.mem.get a = s.mem.get a) := by
  intro sI
  have hIlt : (s.mem.get 29).toNat < (s.mem.get 28).toNat := by
    rw [hI]; simp; exact hRlo
  have hw := sp_loop_to_write_space (s := s) hpc hh hZ hONE hPlo hPhi hIlt hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s20 := runN s 20
  have hs20pc : s20.pc = 1155 := hw.1
  have hs20h : s20.halted = false := hw.2.1
  have hs20Z : s20.mem.get 0 = 0 := hw.2.2.1
  have hs20R : s20.mem.get 2319 = 1 := hw.2.2.2.1
  have hs20P : s20.mem.get 27 = s.mem.get 27 := hw.2.2.2.2.1
  have hs20I : s20.mem.get 29 = 3 := hw.2.2.2.2.2.1.trans hI
  have hpres20 := hw.2.2.2.2.2.2.2
  have hONE20 : s20.mem.get 3 = 1 := (hpres20 3 (by decide) (by decide) (by decide)).trans hONE
  have hK20 : s20.mem.get 10 = 32 := (hpres20 10 (by decide) (by decide) (by decide)).trans hK32
  have g20 : ∀ k : Nat, 1155 ≤ k → k < 1575 →
      s20.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres20 (UInt16.ofNat k) n18 n2319 n0).trans (hcode k (by omega) (by omega))
  have hw2 := write_space_pad_idx3 (s := s20) hs20pc hs20h hs20Z hONE20 hK20 hs20I hs20R g20
  have hrun : sI = runN s20 32 := runN_add_eq s 20 32 52 (by decide)
  have hsIpc : sI.pc = 1011 := by rw [hrun]; exact hw2.1
  have hsIh : sI.halted = false := by rw [hrun]; exact hw2.2.1
  have hsIZ : sI.mem.get 0 = 0 := by rw [hrun]; exact hw2.2.2.1
  have hsIB : sI.mem.get 35 = 32 := by rw [hrun]; exact hw2.2.2.2.1
  have hsII : sI.mem.get 29 = 4 := by rw [hrun]; exact hw2.2.2.2.2.1
  have hsIP : sI.mem.get 27 = s.mem.get 27 - 1 := by
    rw [hrun, hw2.2.2.2.2.2.1, hs20P]
  have hpres : ∀ a, a ≠ 35 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      sI.mem.get a = s.mem.get a := by
    intro a haB ha29 ha27 ha18 ha30 haR ha0
    rw [hrun]
    exact (hw2.2.2.2.2.2.2 a haB ha29 ha27 ha18 ha30 ha0).trans
      (hpres20 a ha18 haR ha0)
  exact ⟨hsIpc, hsIh, hsIZ, hsIB, hsII, hsIP, hpres⟩

/-- From `WRITE_SPACE` with `IDX = 4` and `RETID = 1`: write a space at
`BUF+4` and return to `SP_LOOP` with `IDX = 5` and `PAD -= 1`. 34 steps. -/
theorem write_space_pad_idx4 {s : Machine}
    (hpc : s.pc = 1155)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 4)
    (hR : s.mem.get 2319 = 1)
    (hcode : ∀ k : Nat, 1155 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sW := runN s 34
    sW.pc = 1011 ∧
    sW.halted = false ∧
    sW.mem.get 0 = 0 ∧
    sW.mem.get 36 = 32 ∧
    sW.mem.get 29 = 5 ∧
    sW.mem.get 27 = s.mem.get 27 - 1 ∧
    (∀ a, a ≠ 36 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      sW.mem.get a = s.mem.get a) := by
  intro sW
  have hw := write_space (s := s) hpc hh hZ hK32
    (fun k h1 h2 => hcode k h1 (by omega))
  let s5 := runN s 5
  have hs5pc : s5.pc = 1185 := hw.1
  have hs5h : s5.halted = false := hw.2.1
  have hs5Z : s5.mem.get 0 = 0 := hw.2.2.1
  have hs5CH : s5.mem.get 30 = 32 := hw.2.2.2.1
  have hpres5 := hw.2.2.2.2
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hI5 : s5.mem.get 29 = 4 := (hpres5 29 (by decide) (by decide)).trans hI
  have hR5 : s5.mem.get 2319 = 1 := (hpres5 2319 (by decide) (by decide)).trans hR
  have hP5 : s5.mem.get 27 = s.mem.get 27 := hpres5 27 (by decide) (by decide)
  have g5 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have hs := store_ch_idx4 (s := s5) hs5pc hs5h hs5Z hONE5 hI5 g5
  have hrunM : runN s 23 = runN s5 18 := runN_add_eq s 5 18 23 (by decide)
  let sM := runN s 23
  have hsMpc : sM.pc = 1527 := by
    have : sM = runN s5 18 := hrunM; rw [this]; exact hs.1
  have hsMh : sM.halted = false := by
    have : sM = runN s5 18 := hrunM; rw [this]; exact hs.2.1
  have hsMZ : sM.mem.get 0 = 0 := by
    have : sM = runN s5 18 := hrunM; rw [this]; exact hs.2.2.1
  have hsMB : sM.mem.get 36 = 32 := by
    have : sM = runN s5 18 := hrunM
    rw [this]; exact hs.2.2.2.1.trans hs5CH
  have hsMI : sM.mem.get 29 = 4 := by
    have : sM = runN s5 18 := hrunM; rw [this]; exact hs.2.2.2.2.1
  have hONEM : sM.mem.get 3 = 1 := by
    have : sM = runN s5 18 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 3 (by decide) (by decide) (by decide)).trans hONE5
  have hRM : sM.mem.get 2319 = 1 := by
    have : sM = runN s5 18 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hR5
  have hPM : sM.mem.get 27 = s.mem.get 27 := by
    have : sM = runN s5 18 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 27 (by decide) (by decide) (by decide)).trans hP5
  have hpresM : ∀ a, a ≠ 36 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sM.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    have : sM = runN s5 18 := hrunM
    rw [this]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres5 a ha30 ha0)
  have gM : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      sM.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresM (UInt16.ofNat k) n36 n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hr := stored_ret_pad (s := sM) hsMpc hsMh hsMZ hONEM hRM gM
  have hrun : sW = runN sM 11 := runN_add_eq s 23 11 34 (by decide)
  have hsWpc : sW.pc = 1011 := by rw [hrun]; exact hr.1
  have hsWh : sW.halted = false := by rw [hrun]; exact hr.2.1
  have hsWZ : sW.mem.get 0 = 0 := by rw [hrun]; exact hr.2.2.1
  have hsWI : sW.mem.get 29 = 5 := by
    rw [hrun]
    have : sM.mem.get 29 + 1 = (4 : Word) + 1 := by rw [hsMI]
    exact hr.2.2.2.1.trans (this.trans (rfl : (4 : Word) + 1 = 5))
  have hsWP : sW.mem.get 27 = s.mem.get 27 - 1 := by
    rw [hrun]
    exact hr.2.2.2.2.1.trans (by rw [hPM])
  have hsWB : sW.mem.get 36 = 32 := by
    rw [hrun]
    exact (hr.2.2.2.2.2 36 (by decide) (by decide) (by decide) (by decide)).trans hsMB
  have hpres : ∀ a, a ≠ 36 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      sW.mem.get a = s.mem.get a := by
    intro a haB ha29 ha27 ha18 ha30 ha0
    rw [hrun]
    exact (hr.2.2.2.2.2 a ha29 ha27 ha18 ha0).trans (hpresM a haB ha18 ha30 ha0)
  exact ⟨hsWpc, hsWh, hsWZ, hsWB, hsWI, hsWP, hpres⟩

/-- From `SP_LOOP` with `PAD > 0`, `IDX = 4 < ROOM`: write a space at
`BUF+4` and return to `SP_LOOP` with `IDX = 5` and `PAD -= 1`. 54 steps. -/
theorem pad_one_iter_idx4 {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 4)
    (hPlo : 0 < (s.mem.get 27).toNat)
    (hPhi : (s.mem.get 27).toNat < 32768)
    (hRlo : 4 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sI := runN s 54
    sI.pc = 1011 ∧
    sI.halted = false ∧
    sI.mem.get 0 = 0 ∧
    sI.mem.get 36 = 32 ∧
    sI.mem.get 29 = 5 ∧
    sI.mem.get 27 = s.mem.get 27 - 1 ∧
    (∀ a, a ≠ 36 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      sI.mem.get a = s.mem.get a) := by
  intro sI
  have hIlt : (s.mem.get 29).toNat < (s.mem.get 28).toNat := by
    rw [hI]; simp; exact hRlo
  have hw := sp_loop_to_write_space (s := s) hpc hh hZ hONE hPlo hPhi hIlt hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s20 := runN s 20
  have hs20pc : s20.pc = 1155 := hw.1
  have hs20h : s20.halted = false := hw.2.1
  have hs20Z : s20.mem.get 0 = 0 := hw.2.2.1
  have hs20R : s20.mem.get 2319 = 1 := hw.2.2.2.1
  have hs20P : s20.mem.get 27 = s.mem.get 27 := hw.2.2.2.2.1
  have hs20I : s20.mem.get 29 = 4 := hw.2.2.2.2.2.1.trans hI
  have hpres20 := hw.2.2.2.2.2.2.2
  have hONE20 : s20.mem.get 3 = 1 := (hpres20 3 (by decide) (by decide) (by decide)).trans hONE
  have hK20 : s20.mem.get 10 = 32 := (hpres20 10 (by decide) (by decide) (by decide)).trans hK32
  have g20 : ∀ k : Nat, 1155 ≤ k → k < 1575 →
      s20.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres20 (UInt16.ofNat k) n18 n2319 n0).trans (hcode k (by omega) (by omega))
  have hw2 := write_space_pad_idx4 (s := s20) hs20pc hs20h hs20Z hONE20 hK20 hs20I hs20R g20
  have hrun : sI = runN s20 34 := runN_add_eq s 20 34 54 (by decide)
  have hsIpc : sI.pc = 1011 := by rw [hrun]; exact hw2.1
  have hsIh : sI.halted = false := by rw [hrun]; exact hw2.2.1
  have hsIZ : sI.mem.get 0 = 0 := by rw [hrun]; exact hw2.2.2.1
  have hsIB : sI.mem.get 36 = 32 := by rw [hrun]; exact hw2.2.2.2.1
  have hsII : sI.mem.get 29 = 5 := by rw [hrun]; exact hw2.2.2.2.2.1
  have hsIP : sI.mem.get 27 = s.mem.get 27 - 1 := by
    rw [hrun, hw2.2.2.2.2.2.1, hs20P]
  have hpres : ∀ a, a ≠ 36 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      sI.mem.get a = s.mem.get a := by
    intro a haB ha29 ha27 ha18 ha30 haR ha0
    rw [hrun]
    exact (hw2.2.2.2.2.2.2 a haB ha29 ha27 ha18 ha30 ha0).trans
      (hpres20 a ha18 haR ha0)
  exact ⟨hsIpc, hsIh, hsIZ, hsIB, hsII, hsIP, hpres⟩

/-- From `WRITE_SPACE` with `IDX = 5` and `RETID = 1`: write a space at
`BUF+5` and return to `SP_LOOP` with `IDX = 6` and `PAD -= 1`. 36 steps. -/
theorem write_space_pad_idx5 {s : Machine}
    (hpc : s.pc = 1155)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 5)
    (hR : s.mem.get 2319 = 1)
    (hcode : ∀ k : Nat, 1155 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sW := runN s 36
    sW.pc = 1011 ∧
    sW.halted = false ∧
    sW.mem.get 0 = 0 ∧
    sW.mem.get 37 = 32 ∧
    sW.mem.get 29 = 6 ∧
    sW.mem.get 27 = s.mem.get 27 - 1 ∧
    (∀ a, a ≠ 37 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      sW.mem.get a = s.mem.get a) := by
  intro sW
  have hw := write_space (s := s) hpc hh hZ hK32
    (fun k h1 h2 => hcode k h1 (by omega))
  let s5 := runN s 5
  have hs5pc : s5.pc = 1185 := hw.1
  have hs5h : s5.halted = false := hw.2.1
  have hs5Z : s5.mem.get 0 = 0 := hw.2.2.1
  have hs5CH : s5.mem.get 30 = 32 := hw.2.2.2.1
  have hpres5 := hw.2.2.2.2
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hI5 : s5.mem.get 29 = 5 := (hpres5 29 (by decide) (by decide)).trans hI
  have hR5 : s5.mem.get 2319 = 1 := (hpres5 2319 (by decide) (by decide)).trans hR
  have hP5 : s5.mem.get 27 = s.mem.get 27 := hpres5 27 (by decide) (by decide)
  have g5 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have hs := store_ch_idx5 (s := s5) hs5pc hs5h hs5Z hONE5 hI5 g5
  have hrunM : runN s 25 = runN s5 20 := runN_add_eq s 5 20 25 (by decide)
  let sM := runN s 25
  have hsMpc : sM.pc = 1527 := by
    have : sM = runN s5 20 := hrunM; rw [this]; exact hs.1
  have hsMh : sM.halted = false := by
    have : sM = runN s5 20 := hrunM; rw [this]; exact hs.2.1
  have hsMZ : sM.mem.get 0 = 0 := by
    have : sM = runN s5 20 := hrunM; rw [this]; exact hs.2.2.1
  have hsMB : sM.mem.get 37 = 32 := by
    have : sM = runN s5 20 := hrunM
    rw [this]; exact hs.2.2.2.1.trans hs5CH
  have hsMI : sM.mem.get 29 = 5 := by
    have : sM = runN s5 20 := hrunM; rw [this]; exact hs.2.2.2.2.1
  have hONEM : sM.mem.get 3 = 1 := by
    have : sM = runN s5 20 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 3 (by decide) (by decide) (by decide)).trans hONE5
  have hRM : sM.mem.get 2319 = 1 := by
    have : sM = runN s5 20 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hR5
  have hPM : sM.mem.get 27 = s.mem.get 27 := by
    have : sM = runN s5 20 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 27 (by decide) (by decide) (by decide)).trans hP5
  have hpresM : ∀ a, a ≠ 37 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sM.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    have : sM = runN s5 20 := hrunM
    rw [this]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres5 a ha30 ha0)
  have gM : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      sM.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n37 : UInt16.ofNat k ≠ (37 : Word) := by
      have : (37 : Word) = UInt16.ofNat 37 := rfl
      rw [this]; exact ofNat_ne k 37 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresM (UInt16.ofNat k) n37 n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hr := stored_ret_pad (s := sM) hsMpc hsMh hsMZ hONEM hRM gM
  have hrun : sW = runN sM 11 := runN_add_eq s 25 11 36 (by decide)
  have hsWpc : sW.pc = 1011 := by rw [hrun]; exact hr.1
  have hsWh : sW.halted = false := by rw [hrun]; exact hr.2.1
  have hsWZ : sW.mem.get 0 = 0 := by rw [hrun]; exact hr.2.2.1
  have hsWI : sW.mem.get 29 = 6 := by
    rw [hrun]
    have : sM.mem.get 29 + 1 = (5 : Word) + 1 := by rw [hsMI]
    exact hr.2.2.2.1.trans (this.trans (rfl : (5 : Word) + 1 = 6))
  have hsWP : sW.mem.get 27 = s.mem.get 27 - 1 := by
    rw [hrun]
    exact hr.2.2.2.2.1.trans (by rw [hPM])
  have hsWB : sW.mem.get 37 = 32 := by
    rw [hrun]
    exact (hr.2.2.2.2.2 37 (by decide) (by decide) (by decide) (by decide)).trans hsMB
  have hpres : ∀ a, a ≠ 37 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      sW.mem.get a = s.mem.get a := by
    intro a haB ha29 ha27 ha18 ha30 ha0
    rw [hrun]
    exact (hr.2.2.2.2.2 a ha29 ha27 ha18 ha0).trans (hpresM a haB ha18 ha30 ha0)
  exact ⟨hsWpc, hsWh, hsWZ, hsWB, hsWI, hsWP, hpres⟩

/-- From `SP_LOOP` with `PAD > 0`, `IDX = 5 < ROOM`: write a space at
`BUF+5` and return to `SP_LOOP` with `IDX = 6` and `PAD -= 1`. 56 steps. -/
theorem pad_one_iter_idx5 {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 5)
    (hPlo : 0 < (s.mem.get 27).toNat)
    (hPhi : (s.mem.get 27).toNat < 32768)
    (hRlo : 5 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sI := runN s 56
    sI.pc = 1011 ∧
    sI.halted = false ∧
    sI.mem.get 0 = 0 ∧
    sI.mem.get 37 = 32 ∧
    sI.mem.get 29 = 6 ∧
    sI.mem.get 27 = s.mem.get 27 - 1 ∧
    (∀ a, a ≠ 37 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      sI.mem.get a = s.mem.get a) := by
  intro sI
  have hIlt : (s.mem.get 29).toNat < (s.mem.get 28).toNat := by
    rw [hI]; simp; exact hRlo
  have hw := sp_loop_to_write_space (s := s) hpc hh hZ hONE hPlo hPhi hIlt hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s20 := runN s 20
  have hs20pc : s20.pc = 1155 := hw.1
  have hs20h : s20.halted = false := hw.2.1
  have hs20Z : s20.mem.get 0 = 0 := hw.2.2.1
  have hs20R : s20.mem.get 2319 = 1 := hw.2.2.2.1
  have hs20P : s20.mem.get 27 = s.mem.get 27 := hw.2.2.2.2.1
  have hs20I : s20.mem.get 29 = 5 := hw.2.2.2.2.2.1.trans hI
  have hpres20 := hw.2.2.2.2.2.2.2
  have hONE20 : s20.mem.get 3 = 1 := (hpres20 3 (by decide) (by decide) (by decide)).trans hONE
  have hK20 : s20.mem.get 10 = 32 := (hpres20 10 (by decide) (by decide) (by decide)).trans hK32
  have g20 : ∀ k : Nat, 1155 ≤ k → k < 1575 →
      s20.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres20 (UInt16.ofNat k) n18 n2319 n0).trans (hcode k (by omega) (by omega))
  have hw2 := write_space_pad_idx5 (s := s20) hs20pc hs20h hs20Z hONE20 hK20 hs20I hs20R g20
  have hrun : sI = runN s20 36 := runN_add_eq s 20 36 56 (by decide)
  have hsIpc : sI.pc = 1011 := by rw [hrun]; exact hw2.1
  have hsIh : sI.halted = false := by rw [hrun]; exact hw2.2.1
  have hsIZ : sI.mem.get 0 = 0 := by rw [hrun]; exact hw2.2.2.1
  have hsIB : sI.mem.get 37 = 32 := by rw [hrun]; exact hw2.2.2.2.1
  have hsII : sI.mem.get 29 = 6 := by rw [hrun]; exact hw2.2.2.2.2.1
  have hsIP : sI.mem.get 27 = s.mem.get 27 - 1 := by
    rw [hrun, hw2.2.2.2.2.2.1, hs20P]
  have hpres : ∀ a, a ≠ 37 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      sI.mem.get a = s.mem.get a := by
    intro a haB ha29 ha27 ha18 ha30 haR ha0
    rw [hrun]
    exact (hw2.2.2.2.2.2.2 a haB ha29 ha27 ha18 ha30 ha0).trans
      (hpres20 a ha18 haR ha0)
  exact ⟨hsIpc, hsIh, hsIZ, hsIB, hsII, hsIP, hpres⟩

/-- From `WRITE_SPACE` with `IDX = 6` and `RETID = 1`: write a space at
`BUF+6` and return to `SP_LOOP` with `IDX = 7` and `PAD -= 1`. 38 steps. -/
theorem write_space_pad_idx6 {s : Machine}
    (hpc : s.pc = 1155)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 6)
    (hR : s.mem.get 2319 = 1)
    (hcode : ∀ k : Nat, 1155 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sW := runN s 38
    sW.pc = 1011 ∧
    sW.halted = false ∧
    sW.mem.get 0 = 0 ∧
    sW.mem.get 38 = 32 ∧
    sW.mem.get 29 = 7 ∧
    sW.mem.get 27 = s.mem.get 27 - 1 ∧
    (∀ a, a ≠ 38 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      sW.mem.get a = s.mem.get a) := by
  intro sW
  have hw := write_space (s := s) hpc hh hZ hK32
    (fun k h1 h2 => hcode k h1 (by omega))
  let s5 := runN s 5
  have hs5pc : s5.pc = 1185 := hw.1
  have hs5h : s5.halted = false := hw.2.1
  have hs5Z : s5.mem.get 0 = 0 := hw.2.2.1
  have hs5CH : s5.mem.get 30 = 32 := hw.2.2.2.1
  have hpres5 := hw.2.2.2.2
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hI5 : s5.mem.get 29 = 6 := (hpres5 29 (by decide) (by decide)).trans hI
  have hR5 : s5.mem.get 2319 = 1 := (hpres5 2319 (by decide) (by decide)).trans hR
  have hP5 : s5.mem.get 27 = s.mem.get 27 := hpres5 27 (by decide) (by decide)
  have g5 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have hs := store_ch_idx6 (s := s5) hs5pc hs5h hs5Z hONE5 hI5 g5
  have hrunM : runN s 27 = runN s5 22 := runN_add_eq s 5 22 27 (by decide)
  let sM := runN s 27
  have hsMpc : sM.pc = 1527 := by
    have : sM = runN s5 22 := hrunM; rw [this]; exact hs.1
  have hsMh : sM.halted = false := by
    have : sM = runN s5 22 := hrunM; rw [this]; exact hs.2.1
  have hsMZ : sM.mem.get 0 = 0 := by
    have : sM = runN s5 22 := hrunM; rw [this]; exact hs.2.2.1
  have hsMB : sM.mem.get 38 = 32 := by
    have : sM = runN s5 22 := hrunM
    rw [this]; exact hs.2.2.2.1.trans hs5CH
  have hsMI : sM.mem.get 29 = 6 := by
    have : sM = runN s5 22 := hrunM; rw [this]; exact hs.2.2.2.2.1
  have hONEM : sM.mem.get 3 = 1 := by
    have : sM = runN s5 22 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 3 (by decide) (by decide) (by decide)).trans hONE5
  have hRM : sM.mem.get 2319 = 1 := by
    have : sM = runN s5 22 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hR5
  have hPM : sM.mem.get 27 = s.mem.get 27 := by
    have : sM = runN s5 22 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 27 (by decide) (by decide) (by decide)).trans hP5
  have hpresM : ∀ a, a ≠ 38 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sM.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    have : sM = runN s5 22 := hrunM
    rw [this]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres5 a ha30 ha0)
  have gM : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      sM.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n38 : UInt16.ofNat k ≠ (38 : Word) := by
      have : (38 : Word) = UInt16.ofNat 38 := rfl
      rw [this]; exact ofNat_ne k 38 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresM (UInt16.ofNat k) n38 n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hr := stored_ret_pad (s := sM) hsMpc hsMh hsMZ hONEM hRM gM
  have hrun : sW = runN sM 11 := runN_add_eq s 27 11 38 (by decide)
  have hsWpc : sW.pc = 1011 := by rw [hrun]; exact hr.1
  have hsWh : sW.halted = false := by rw [hrun]; exact hr.2.1
  have hsWZ : sW.mem.get 0 = 0 := by rw [hrun]; exact hr.2.2.1
  have hsWI : sW.mem.get 29 = 7 := by
    rw [hrun]
    have : sM.mem.get 29 + 1 = (6 : Word) + 1 := by rw [hsMI]
    exact hr.2.2.2.1.trans (this.trans (rfl : (6 : Word) + 1 = 7))
  have hsWP : sW.mem.get 27 = s.mem.get 27 - 1 := by
    rw [hrun]
    exact hr.2.2.2.2.1.trans (by rw [hPM])
  have hsWB : sW.mem.get 38 = 32 := by
    rw [hrun]
    exact (hr.2.2.2.2.2 38 (by decide) (by decide) (by decide) (by decide)).trans hsMB
  have hpres : ∀ a, a ≠ 38 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      sW.mem.get a = s.mem.get a := by
    intro a haB ha29 ha27 ha18 ha30 ha0
    rw [hrun]
    exact (hr.2.2.2.2.2 a ha29 ha27 ha18 ha0).trans (hpresM a haB ha18 ha30 ha0)
  exact ⟨hsWpc, hsWh, hsWZ, hsWB, hsWI, hsWP, hpres⟩

/-- From `SP_LOOP` with `PAD > 0`, `IDX = 6 < ROOM`: write a space at
`BUF+6` and return to `SP_LOOP` with `IDX = 7` and `PAD -= 1`. 58 steps. -/
theorem pad_one_iter_idx6 {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 6)
    (hPlo : 0 < (s.mem.get 27).toNat)
    (hPhi : (s.mem.get 27).toNat < 32768)
    (hRlo : 6 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sI := runN s 58
    sI.pc = 1011 ∧
    sI.halted = false ∧
    sI.mem.get 0 = 0 ∧
    sI.mem.get 38 = 32 ∧
    sI.mem.get 29 = 7 ∧
    sI.mem.get 27 = s.mem.get 27 - 1 ∧
    (∀ a, a ≠ 38 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      sI.mem.get a = s.mem.get a) := by
  intro sI
  have hIlt : (s.mem.get 29).toNat < (s.mem.get 28).toNat := by
    rw [hI]; simp; exact hRlo
  have hw := sp_loop_to_write_space (s := s) hpc hh hZ hONE hPlo hPhi hIlt hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s20 := runN s 20
  have hs20pc : s20.pc = 1155 := hw.1
  have hs20h : s20.halted = false := hw.2.1
  have hs20Z : s20.mem.get 0 = 0 := hw.2.2.1
  have hs20R : s20.mem.get 2319 = 1 := hw.2.2.2.1
  have hs20P : s20.mem.get 27 = s.mem.get 27 := hw.2.2.2.2.1
  have hs20I : s20.mem.get 29 = 6 := hw.2.2.2.2.2.1.trans hI
  have hpres20 := hw.2.2.2.2.2.2.2
  have hONE20 : s20.mem.get 3 = 1 := (hpres20 3 (by decide) (by decide) (by decide)).trans hONE
  have hK20 : s20.mem.get 10 = 32 := (hpres20 10 (by decide) (by decide) (by decide)).trans hK32
  have g20 : ∀ k : Nat, 1155 ≤ k → k < 1575 →
      s20.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres20 (UInt16.ofNat k) n18 n2319 n0).trans (hcode k (by omega) (by omega))
  have hw2 := write_space_pad_idx6 (s := s20) hs20pc hs20h hs20Z hONE20 hK20 hs20I hs20R g20
  have hrun : sI = runN s20 38 := runN_add_eq s 20 38 58 (by decide)
  have hsIpc : sI.pc = 1011 := by rw [hrun]; exact hw2.1
  have hsIh : sI.halted = false := by rw [hrun]; exact hw2.2.1
  have hsIZ : sI.mem.get 0 = 0 := by rw [hrun]; exact hw2.2.2.1
  have hsIB : sI.mem.get 38 = 32 := by rw [hrun]; exact hw2.2.2.2.1
  have hsII : sI.mem.get 29 = 7 := by rw [hrun]; exact hw2.2.2.2.2.1
  have hsIP : sI.mem.get 27 = s.mem.get 27 - 1 := by
    rw [hrun, hw2.2.2.2.2.2.1, hs20P]
  have hpres : ∀ a, a ≠ 38 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      sI.mem.get a = s.mem.get a := by
    intro a haB ha29 ha27 ha18 ha30 haR ha0
    rw [hrun]
    exact (hw2.2.2.2.2.2.2 a haB ha29 ha27 ha18 ha30 ha0).trans
      (hpres20 a ha18 haR ha0)
  exact ⟨hsIpc, hsIh, hsIZ, hsIB, hsII, hsIP, hpres⟩

/-- From `WRITE_SPACE` with `IDX = 7` and `RETID = 1`: write a space at
`BUF+7` and return to `SP_LOOP` with `IDX = 8` and `PAD -= 1`. 40 steps. -/
theorem write_space_pad_idx7 {s : Machine}
    (hpc : s.pc = 1155)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 7)
    (hR : s.mem.get 2319 = 1)
    (hcode : ∀ k : Nat, 1155 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sW := runN s 40
    sW.pc = 1011 ∧
    sW.halted = false ∧
    sW.mem.get 0 = 0 ∧
    sW.mem.get 39 = 32 ∧
    sW.mem.get 29 = 8 ∧
    sW.mem.get 27 = s.mem.get 27 - 1 ∧
    (∀ a, a ≠ 39 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      sW.mem.get a = s.mem.get a) := by
  intro sW
  have hw := write_space (s := s) hpc hh hZ hK32
    (fun k h1 h2 => hcode k h1 (by omega))
  let s5 := runN s 5
  have hs5pc : s5.pc = 1185 := hw.1
  have hs5h : s5.halted = false := hw.2.1
  have hs5Z : s5.mem.get 0 = 0 := hw.2.2.1
  have hs5CH : s5.mem.get 30 = 32 := hw.2.2.2.1
  have hpres5 := hw.2.2.2.2
  have hONE5 : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide)).trans hONE
  have hI5 : s5.mem.get 29 = 7 := (hpres5 29 (by decide) (by decide)).trans hI
  have hR5 : s5.mem.get 2319 = 1 := (hpres5 2319 (by decide) (by decide)).trans hR
  have hP5 : s5.mem.get 27 = s.mem.get 27 := hpres5 27 (by decide) (by decide)
  have g5 : ∀ k : Nat, 1185 ≤ k → k < 1527 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n30 n0).trans (hcode k (by omega) (by omega))
  have hs := store_ch_idx7 (s := s5) hs5pc hs5h hs5Z hONE5 hI5 g5
  have hrunM : runN s 29 = runN s5 24 := runN_add_eq s 5 24 29 (by decide)
  let sM := runN s 29
  have hsMpc : sM.pc = 1527 := by
    have : sM = runN s5 24 := hrunM; rw [this]; exact hs.1
  have hsMh : sM.halted = false := by
    have : sM = runN s5 24 := hrunM; rw [this]; exact hs.2.1
  have hsMZ : sM.mem.get 0 = 0 := by
    have : sM = runN s5 24 := hrunM; rw [this]; exact hs.2.2.1
  have hsMB : sM.mem.get 39 = 32 := by
    have : sM = runN s5 24 := hrunM
    rw [this]; exact hs.2.2.2.1.trans hs5CH
  have hsMI : sM.mem.get 29 = 7 := by
    have : sM = runN s5 24 := hrunM; rw [this]; exact hs.2.2.2.2.1
  have hONEM : sM.mem.get 3 = 1 := by
    have : sM = runN s5 24 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 3 (by decide) (by decide) (by decide)).trans hONE5
  have hRM : sM.mem.get 2319 = 1 := by
    have : sM = runN s5 24 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 2319 (by decide) (by decide) (by decide)).trans hR5
  have hPM : sM.mem.get 27 = s.mem.get 27 := by
    have : sM = runN s5 24 := hrunM
    rw [this]; exact (hs.2.2.2.2.2 27 (by decide) (by decide) (by decide)).trans hP5
  have hpresM : ∀ a, a ≠ 39 → a ≠ 18 → a ≠ 30 → a ≠ 0 → sM.mem.get a = s.mem.get a := by
    intro a haB ha18 ha30 ha0
    have : sM = runN s5 24 := hrunM
    rw [this]
    exact (hs.2.2.2.2.2 a haB ha18 ha0).trans (hpres5 a ha30 ha0)
  have gM : ∀ k : Nat, 1527 ≤ k → k < 1575 →
      sM.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n39 : UInt16.ofNat k ≠ (39 : Word) := by
      have : (39 : Word) = UInt16.ofNat 39 := rfl
      rw [this]; exact ofNat_ne k 39 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresM (UInt16.ofNat k) n39 n18 n30 n0).trans (hcode k (by omega) (by omega))
  have hr := stored_ret_pad (s := sM) hsMpc hsMh hsMZ hONEM hRM gM
  have hrun : sW = runN sM 11 := runN_add_eq s 29 11 40 (by decide)
  have hsWpc : sW.pc = 1011 := by rw [hrun]; exact hr.1
  have hsWh : sW.halted = false := by rw [hrun]; exact hr.2.1
  have hsWZ : sW.mem.get 0 = 0 := by rw [hrun]; exact hr.2.2.1
  have hsWI : sW.mem.get 29 = 8 := by
    rw [hrun]
    have : sM.mem.get 29 + 1 = (7 : Word) + 1 := by rw [hsMI]
    exact hr.2.2.2.1.trans (this.trans (rfl : (7 : Word) + 1 = 8))
  have hsWP : sW.mem.get 27 = s.mem.get 27 - 1 := by
    rw [hrun]
    exact hr.2.2.2.2.1.trans (by rw [hPM])
  have hsWB : sW.mem.get 39 = 32 := by
    rw [hrun]
    exact (hr.2.2.2.2.2 39 (by decide) (by decide) (by decide) (by decide)).trans hsMB
  have hpres : ∀ a, a ≠ 39 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 0 →
      sW.mem.get a = s.mem.get a := by
    intro a haB ha29 ha27 ha18 ha30 ha0
    rw [hrun]
    exact (hr.2.2.2.2.2 a ha29 ha27 ha18 ha0).trans (hpresM a haB ha18 ha30 ha0)
  exact ⟨hsWpc, hsWh, hsWZ, hsWB, hsWI, hsWP, hpres⟩

/-- From `SP_LOOP` with `PAD > 0`, `IDX = 7 < ROOM`: write a space at
`BUF+7` and return to `SP_LOOP` with `IDX = 8` and `PAD -= 1`. 60 steps. -/
theorem pad_one_iter_idx7 {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 7)
    (hPlo : 0 < (s.mem.get 27).toNat)
    (hPhi : (s.mem.get 27).toNat < 32768)
    (hRlo : 7 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sI := runN s 60
    sI.pc = 1011 ∧
    sI.halted = false ∧
    sI.mem.get 0 = 0 ∧
    sI.mem.get 39 = 32 ∧
    sI.mem.get 29 = 8 ∧
    sI.mem.get 27 = s.mem.get 27 - 1 ∧
    (∀ a, a ≠ 39 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      sI.mem.get a = s.mem.get a) := by
  intro sI
  have hIlt : (s.mem.get 29).toNat < (s.mem.get 28).toNat := by
    rw [hI]; simp; exact hRlo
  have hw := sp_loop_to_write_space (s := s) hpc hh hZ hONE hPlo hPhi hIlt hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s20 := runN s 20
  have hs20pc : s20.pc = 1155 := hw.1
  have hs20h : s20.halted = false := hw.2.1
  have hs20Z : s20.mem.get 0 = 0 := hw.2.2.1
  have hs20R : s20.mem.get 2319 = 1 := hw.2.2.2.1
  have hs20P : s20.mem.get 27 = s.mem.get 27 := hw.2.2.2.2.1
  have hs20I : s20.mem.get 29 = 7 := hw.2.2.2.2.2.1.trans hI
  have hpres20 := hw.2.2.2.2.2.2.2
  have hONE20 : s20.mem.get 3 = 1 := (hpres20 3 (by decide) (by decide) (by decide)).trans hONE
  have hK20 : s20.mem.get 10 = 32 := (hpres20 10 (by decide) (by decide) (by decide)).trans hK32
  have g20 : ∀ k : Nat, 1155 ≤ k → k < 1575 →
      s20.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres20 (UInt16.ofNat k) n18 n2319 n0).trans (hcode k (by omega) (by omega))
  have hw2 := write_space_pad_idx7 (s := s20) hs20pc hs20h hs20Z hONE20 hK20 hs20I hs20R g20
  have hrun : sI = runN s20 40 := runN_add_eq s 20 40 60 (by decide)
  have hsIpc : sI.pc = 1011 := by rw [hrun]; exact hw2.1
  have hsIh : sI.halted = false := by rw [hrun]; exact hw2.2.1
  have hsIZ : sI.mem.get 0 = 0 := by rw [hrun]; exact hw2.2.2.1
  have hsIB : sI.mem.get 39 = 32 := by rw [hrun]; exact hw2.2.2.2.1
  have hsII : sI.mem.get 29 = 8 := by rw [hrun]; exact hw2.2.2.2.2.1
  have hsIP : sI.mem.get 27 = s.mem.get 27 - 1 := by
    rw [hrun, hw2.2.2.2.2.2.1, hs20P]
  have hpres : ∀ a, a ≠ 39 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      sI.mem.get a = s.mem.get a := by
    intro a haB ha29 ha27 ha18 ha30 haR ha0
    rw [hrun]
    exact (hw2.2.2.2.2.2.2 a haB ha29 ha27 ha18 ha30 ha0).trans
      (hpres20 a ha18 haR ha0)
  exact ⟨hsIpc, hsIh, hsIZ, hsIB, hsII, hsIP, hpres⟩


/-- From `SP_LOOP` with `PAD = 2` and `IDX = 0`, and `2 ≤ ROOM`: write 2
spaces at `BUF+0..BUF+1` and return to `SP_LOOP` with `IDX = 2` and
`PAD = 0`. 94 steps. -/
theorem pad_2_spaces_idx0 {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 0)
    (hP : s.mem.get 27 = 2)
    (hRlo : 2 ≤ (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sP := runN s 94
    sP.pc = 1011 ∧
    sP.halted = false ∧
    sP.mem.get 0 = 0 ∧
    sP.mem.get 32 = 32 ∧
    sP.mem.get 33 = 32 ∧
    sP.mem.get 29 = 2 ∧
    sP.mem.get 27 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sP.mem.get a = s.mem.get a) := by
  intro sP
  have hPlo0 : 0 < (s.mem.get 27).toNat := by simp [hP]
  have hPhi0 : (s.mem.get 27).toNat < 32768 := by simp [hP]
  have hRlo0 : 0 < (s.mem.get 28).toNat := by omega
  have hi0 := pad_one_iter_idx0 (s := s) hpc hh hZ hONE hK32 hI hPlo0 hPhi0 hRlo0 hRhi
    (fun k h1 h2 => hcode k h1 h2)
  let s46 := runN s 46
  have hs46pc : s46.pc = 1011 := hi0.1
  have hs46h : s46.halted = false := hi0.2.1
  have hs46Z : s46.mem.get 0 = 0 := hi0.2.2.1
  have hs46B0 : s46.mem.get 32 = 32 := hi0.2.2.2.1
  have hs46I : s46.mem.get 29 = 1 := hi0.2.2.2.2.1
  have hs46P : s46.mem.get 27 = (1 : Word) := by
    have h := hi0.2.2.2.2.2.1
    rw [h, hP]
    exact (rfl : (2 : Word) - 1 = 1)
  have hpres46 := hi0.2.2.2.2.2.2
  have hONE46 : s46.mem.get 3 = 1 := (hpres46 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK46 : s46.mem.get 10 = 32 := (hpres46 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo46 : 0 < (s46.mem.get 27).toNat := by
    have : s46.mem.get 27 = (1 : Word) := hs46P
    simp [this]
  have hPhi46 : (s46.mem.get 27).toNat < 32768 := by
    have : s46.mem.get 27 = (1 : Word) := hs46P
    simp [this]
  have hRlo46 : 1 < (s46.mem.get 28).toNat := by
    have : s46.mem.get 28 = s.mem.get 28 := hpres46 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi46 : (s46.mem.get 28).toNat < 32768 := by
    have : s46.mem.get 28 = s.mem.get 28 := hpres46 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g46 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s46.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres46 (UInt16.ofNat k) n32 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi1 := pad_one_iter_idx1 (s := s46) hs46pc hs46h hs46Z hONE46 hK46 hs46I
    hPlo46 hPhi46 hRlo46 hRhi46 g46
  have hrun94 : runN s 94 = runN s46 48 := runN_add_eq s 46 48 94 (by decide)
  let s94 := runN s 94
  have hs94pc : s94.pc = 1011 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.1
  have hs94h : s94.halted = false := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.1
  have hs94Z : s94.mem.get 0 = 0 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.1
  have hs94B1 : s94.mem.get 33 = 32 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.2.1
  have hs94I : s94.mem.get 29 = 2 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.2.2.1
  have hs94P : s94.mem.get 27 = (0 : Word) := by
    have : s94 = runN s46 48 := hrun94
    rw [this, hi1.2.2.2.2.2.1, hs46P]
    exact (rfl : (1 : Word) - 1 = 0)
  have hpresL1 := hi1.2.2.2.2.2.2
  have hpres94 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s94.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s94 = runN s46 48 := hrun94
    rw [this]
    exact (hpresL1 a ha33 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres46 a ha32 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs94B0 : s94.mem.get 32 = 32 := by
    have : s94 = runN s46 48 := hrun94
    rw [this]
    exact (hpresL1 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs46B0
  have hsPeq : sP = s94 := rfl
  have hsPpc : sP.pc = 1011 := by rw [hsPeq]; exact hs94pc
  have hsPh : sP.halted = false := by rw [hsPeq]; exact hs94h
  have hsPZ : sP.mem.get 0 = 0 := by rw [hsPeq]; exact hs94Z
  have hsPB0 : sP.mem.get 32 = 32 := by rw [hsPeq]; exact hs94B0
  have hsPB1 : sP.mem.get 33 = 32 := by rw [hsPeq]; exact hs94B1
  have hsPI : sP.mem.get 29 = 2 := by rw [hsPeq]; exact hs94I
  have hsPP : sP.mem.get 27 = 0 := by rw [hsPeq]; exact hs94P
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sP.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha29 ha27 ha18 ha30 ha2319 ha0
    rw [hsPeq]
    exact hpres94 a ha32 ha33 ha29 ha27 ha18 ha30 ha2319 ha0
  exact ⟨hsPpc, hsPh, hsPZ, hsPB0, hsPB1, hsPI, hsPP, hpres⟩

/-- From `SP_LOOP` with `PAD = 3` and `IDX = 0`, and `3 ≤ ROOM`: write 3
spaces at `BUF+0..BUF+2` and return to `SP_LOOP` with `IDX = 3` and
`PAD = 0`. 144 steps. -/
theorem pad_3_spaces_idx0 {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 0)
    (hP : s.mem.get 27 = 3)
    (hRlo : 3 ≤ (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sP := runN s 144
    sP.pc = 1011 ∧
    sP.halted = false ∧
    sP.mem.get 0 = 0 ∧
    sP.mem.get 32 = 32 ∧
    sP.mem.get 33 = 32 ∧
    sP.mem.get 34 = 32 ∧
    sP.mem.get 29 = 3 ∧
    sP.mem.get 27 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sP.mem.get a = s.mem.get a) := by
  intro sP
  have hPlo0 : 0 < (s.mem.get 27).toNat := by simp [hP]
  have hPhi0 : (s.mem.get 27).toNat < 32768 := by simp [hP]
  have hRlo0 : 0 < (s.mem.get 28).toNat := by omega
  have hi0 := pad_one_iter_idx0 (s := s) hpc hh hZ hONE hK32 hI hPlo0 hPhi0 hRlo0 hRhi
    (fun k h1 h2 => hcode k h1 h2)
  let s46 := runN s 46
  have hs46pc : s46.pc = 1011 := hi0.1
  have hs46h : s46.halted = false := hi0.2.1
  have hs46Z : s46.mem.get 0 = 0 := hi0.2.2.1
  have hs46B0 : s46.mem.get 32 = 32 := hi0.2.2.2.1
  have hs46I : s46.mem.get 29 = 1 := hi0.2.2.2.2.1
  have hs46P : s46.mem.get 27 = (2 : Word) := by
    have h := hi0.2.2.2.2.2.1
    rw [h, hP]
    exact (rfl : (3 : Word) - 1 = 2)
  have hpres46 := hi0.2.2.2.2.2.2
  have hONE46 : s46.mem.get 3 = 1 := (hpres46 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK46 : s46.mem.get 10 = 32 := (hpres46 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo46 : 0 < (s46.mem.get 27).toNat := by
    have : s46.mem.get 27 = (2 : Word) := hs46P
    simp [this]
  have hPhi46 : (s46.mem.get 27).toNat < 32768 := by
    have : s46.mem.get 27 = (2 : Word) := hs46P
    simp [this]
  have hRlo46 : 1 < (s46.mem.get 28).toNat := by
    have : s46.mem.get 28 = s.mem.get 28 := hpres46 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi46 : (s46.mem.get 28).toNat < 32768 := by
    have : s46.mem.get 28 = s.mem.get 28 := hpres46 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g46 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s46.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres46 (UInt16.ofNat k) n32 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi1 := pad_one_iter_idx1 (s := s46) hs46pc hs46h hs46Z hONE46 hK46 hs46I
    hPlo46 hPhi46 hRlo46 hRhi46 g46
  have hrun94 : runN s 94 = runN s46 48 := runN_add_eq s 46 48 94 (by decide)
  let s94 := runN s 94
  have hs94pc : s94.pc = 1011 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.1
  have hs94h : s94.halted = false := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.1
  have hs94Z : s94.mem.get 0 = 0 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.1
  have hs94B1 : s94.mem.get 33 = 32 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.2.1
  have hs94I : s94.mem.get 29 = 2 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.2.2.1
  have hs94P : s94.mem.get 27 = (1 : Word) := by
    have : s94 = runN s46 48 := hrun94
    rw [this, hi1.2.2.2.2.2.1, hs46P]
    exact (rfl : (2 : Word) - 1 = 1)
  have hpresL1 := hi1.2.2.2.2.2.2
  have hpres94 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s94.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s94 = runN s46 48 := hrun94
    rw [this]
    exact (hpresL1 a ha33 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres46 a ha32 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs94B0 : s94.mem.get 32 = 32 := by
    have : s94 = runN s46 48 := hrun94
    rw [this]
    exact (hpresL1 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs46B0
  have hONE94 : s94.mem.get 3 = 1 := (hpres94 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK94 : s94.mem.get 10 = 32 := (hpres94 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo94 : 0 < (s94.mem.get 27).toNat := by
    have : s94.mem.get 27 = (1 : Word) := hs94P
    simp [this]
  have hPhi94 : (s94.mem.get 27).toNat < 32768 := by
    have : s94.mem.get 27 = (1 : Word) := hs94P
    simp [this]
  have hRlo94 : 2 < (s94.mem.get 28).toNat := by
    have : s94.mem.get 28 = s.mem.get 28 := hpres94 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi94 : (s94.mem.get 28).toNat < 32768 := by
    have : s94.mem.get 28 = s.mem.get 28 := hpres94 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g94 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s94.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres94 (UInt16.ofNat k) n32 n33 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi2 := pad_one_iter_idx2 (s := s94) hs94pc hs94h hs94Z hONE94 hK94 hs94I
    hPlo94 hPhi94 hRlo94 hRhi94 g94
  have hrun144 : runN s 144 = runN s94 50 := runN_add_eq s 94 50 144 (by decide)
  let s144 := runN s 144
  have hs144pc : s144.pc = 1011 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.1
  have hs144h : s144.halted = false := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.1
  have hs144Z : s144.mem.get 0 = 0 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.2.1
  have hs144B2 : s144.mem.get 34 = 32 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.2.2.1
  have hs144I : s144.mem.get 29 = 3 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.2.2.2.1
  have hs144P : s144.mem.get 27 = (0 : Word) := by
    have : s144 = runN s94 50 := hrun144
    rw [this, hi2.2.2.2.2.2.1, hs94P]
    exact (rfl : (1 : Word) - 1 = 0)
  have hpresL2 := hi2.2.2.2.2.2.2
  have hpres144 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s144.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s144 = runN s94 50 := hrun144
    rw [this]
    exact (hpresL2 a ha34 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres94 a ha32 ha33 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs144B0 : s144.mem.get 32 = 32 := by
    have : s144 = runN s94 50 := hrun144
    rw [this]
    exact (hpresL2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs94B0
  have hs144B1 : s144.mem.get 33 = 32 := by
    have : s144 = runN s94 50 := hrun144
    rw [this]
    exact (hpresL2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs94B1
  have hsPeq : sP = s144 := rfl
  have hsPpc : sP.pc = 1011 := by rw [hsPeq]; exact hs144pc
  have hsPh : sP.halted = false := by rw [hsPeq]; exact hs144h
  have hsPZ : sP.mem.get 0 = 0 := by rw [hsPeq]; exact hs144Z
  have hsPB0 : sP.mem.get 32 = 32 := by rw [hsPeq]; exact hs144B0
  have hsPB1 : sP.mem.get 33 = 32 := by rw [hsPeq]; exact hs144B1
  have hsPB2 : sP.mem.get 34 = 32 := by rw [hsPeq]; exact hs144B2
  have hsPI : sP.mem.get 29 = 3 := by rw [hsPeq]; exact hs144I
  have hsPP : sP.mem.get 27 = 0 := by rw [hsPeq]; exact hs144P
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sP.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha29 ha27 ha18 ha30 ha2319 ha0
    rw [hsPeq]
    exact hpres144 a ha32 ha33 ha34 ha29 ha27 ha18 ha30 ha2319 ha0
  exact ⟨hsPpc, hsPh, hsPZ, hsPB0, hsPB1, hsPB2, hsPI, hsPP, hpres⟩

/-- From `SP_LOOP` with `PAD = 4` and `IDX = 0`, and `4 ≤ ROOM`: write 4
spaces at `BUF+0..BUF+3` and return to `SP_LOOP` with `IDX = 4` and
`PAD = 0`. 196 steps. -/
theorem pad_4_spaces_idx0 {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 0)
    (hP : s.mem.get 27 = 4)
    (hRlo : 4 ≤ (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sP := runN s 196
    sP.pc = 1011 ∧
    sP.halted = false ∧
    sP.mem.get 0 = 0 ∧
    sP.mem.get 32 = 32 ∧
    sP.mem.get 33 = 32 ∧
    sP.mem.get 34 = 32 ∧
    sP.mem.get 35 = 32 ∧
    sP.mem.get 29 = 4 ∧
    sP.mem.get 27 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sP.mem.get a = s.mem.get a) := by
  intro sP
  have hPlo0 : 0 < (s.mem.get 27).toNat := by simp [hP]
  have hPhi0 : (s.mem.get 27).toNat < 32768 := by simp [hP]
  have hRlo0 : 0 < (s.mem.get 28).toNat := by omega
  have hi0 := pad_one_iter_idx0 (s := s) hpc hh hZ hONE hK32 hI hPlo0 hPhi0 hRlo0 hRhi
    (fun k h1 h2 => hcode k h1 h2)
  let s46 := runN s 46
  have hs46pc : s46.pc = 1011 := hi0.1
  have hs46h : s46.halted = false := hi0.2.1
  have hs46Z : s46.mem.get 0 = 0 := hi0.2.2.1
  have hs46B0 : s46.mem.get 32 = 32 := hi0.2.2.2.1
  have hs46I : s46.mem.get 29 = 1 := hi0.2.2.2.2.1
  have hs46P : s46.mem.get 27 = (3 : Word) := by
    have h := hi0.2.2.2.2.2.1
    rw [h, hP]
    exact (rfl : (4 : Word) - 1 = 3)
  have hpres46 := hi0.2.2.2.2.2.2
  have hONE46 : s46.mem.get 3 = 1 := (hpres46 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK46 : s46.mem.get 10 = 32 := (hpres46 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo46 : 0 < (s46.mem.get 27).toNat := by
    have : s46.mem.get 27 = (3 : Word) := hs46P
    simp [this]
  have hPhi46 : (s46.mem.get 27).toNat < 32768 := by
    have : s46.mem.get 27 = (3 : Word) := hs46P
    simp [this]
  have hRlo46 : 1 < (s46.mem.get 28).toNat := by
    have : s46.mem.get 28 = s.mem.get 28 := hpres46 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi46 : (s46.mem.get 28).toNat < 32768 := by
    have : s46.mem.get 28 = s.mem.get 28 := hpres46 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g46 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s46.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres46 (UInt16.ofNat k) n32 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi1 := pad_one_iter_idx1 (s := s46) hs46pc hs46h hs46Z hONE46 hK46 hs46I
    hPlo46 hPhi46 hRlo46 hRhi46 g46
  have hrun94 : runN s 94 = runN s46 48 := runN_add_eq s 46 48 94 (by decide)
  let s94 := runN s 94
  have hs94pc : s94.pc = 1011 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.1
  have hs94h : s94.halted = false := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.1
  have hs94Z : s94.mem.get 0 = 0 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.1
  have hs94B1 : s94.mem.get 33 = 32 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.2.1
  have hs94I : s94.mem.get 29 = 2 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.2.2.1
  have hs94P : s94.mem.get 27 = (2 : Word) := by
    have : s94 = runN s46 48 := hrun94
    rw [this, hi1.2.2.2.2.2.1, hs46P]
    exact (rfl : (3 : Word) - 1 = 2)
  have hpresL1 := hi1.2.2.2.2.2.2
  have hpres94 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s94.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s94 = runN s46 48 := hrun94
    rw [this]
    exact (hpresL1 a ha33 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres46 a ha32 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs94B0 : s94.mem.get 32 = 32 := by
    have : s94 = runN s46 48 := hrun94
    rw [this]
    exact (hpresL1 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs46B0
  have hONE94 : s94.mem.get 3 = 1 := (hpres94 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK94 : s94.mem.get 10 = 32 := (hpres94 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo94 : 0 < (s94.mem.get 27).toNat := by
    have : s94.mem.get 27 = (2 : Word) := hs94P
    simp [this]
  have hPhi94 : (s94.mem.get 27).toNat < 32768 := by
    have : s94.mem.get 27 = (2 : Word) := hs94P
    simp [this]
  have hRlo94 : 2 < (s94.mem.get 28).toNat := by
    have : s94.mem.get 28 = s.mem.get 28 := hpres94 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi94 : (s94.mem.get 28).toNat < 32768 := by
    have : s94.mem.get 28 = s.mem.get 28 := hpres94 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g94 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s94.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres94 (UInt16.ofNat k) n32 n33 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi2 := pad_one_iter_idx2 (s := s94) hs94pc hs94h hs94Z hONE94 hK94 hs94I
    hPlo94 hPhi94 hRlo94 hRhi94 g94
  have hrun144 : runN s 144 = runN s94 50 := runN_add_eq s 94 50 144 (by decide)
  let s144 := runN s 144
  have hs144pc : s144.pc = 1011 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.1
  have hs144h : s144.halted = false := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.1
  have hs144Z : s144.mem.get 0 = 0 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.2.1
  have hs144B2 : s144.mem.get 34 = 32 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.2.2.1
  have hs144I : s144.mem.get 29 = 3 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.2.2.2.1
  have hs144P : s144.mem.get 27 = (1 : Word) := by
    have : s144 = runN s94 50 := hrun144
    rw [this, hi2.2.2.2.2.2.1, hs94P]
    exact (rfl : (2 : Word) - 1 = 1)
  have hpresL2 := hi2.2.2.2.2.2.2
  have hpres144 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s144.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s144 = runN s94 50 := hrun144
    rw [this]
    exact (hpresL2 a ha34 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres94 a ha32 ha33 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs144B0 : s144.mem.get 32 = 32 := by
    have : s144 = runN s94 50 := hrun144
    rw [this]
    exact (hpresL2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs94B0
  have hs144B1 : s144.mem.get 33 = 32 := by
    have : s144 = runN s94 50 := hrun144
    rw [this]
    exact (hpresL2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs94B1
  have hONE144 : s144.mem.get 3 = 1 := (hpres144 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK144 : s144.mem.get 10 = 32 := (hpres144 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo144 : 0 < (s144.mem.get 27).toNat := by
    have : s144.mem.get 27 = (1 : Word) := hs144P
    simp [this]
  have hPhi144 : (s144.mem.get 27).toNat < 32768 := by
    have : s144.mem.get 27 = (1 : Word) := hs144P
    simp [this]
  have hRlo144 : 3 < (s144.mem.get 28).toNat := by
    have : s144.mem.get 28 = s.mem.get 28 := hpres144 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi144 : (s144.mem.get 28).toNat < 32768 := by
    have : s144.mem.get 28 = s.mem.get 28 := hpres144 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g144 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s144.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres144 (UInt16.ofNat k) n32 n33 n34 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi3 := pad_one_iter_idx3 (s := s144) hs144pc hs144h hs144Z hONE144 hK144 hs144I
    hPlo144 hPhi144 hRlo144 hRhi144 g144
  have hrun196 : runN s 196 = runN s144 52 := runN_add_eq s 144 52 196 (by decide)
  let s196 := runN s 196
  have hs196pc : s196.pc = 1011 := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.1
  have hs196h : s196.halted = false := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.2.1
  have hs196Z : s196.mem.get 0 = 0 := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.2.2.1
  have hs196B3 : s196.mem.get 35 = 32 := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.2.2.2.1
  have hs196I : s196.mem.get 29 = 4 := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.2.2.2.2.1
  have hs196P : s196.mem.get 27 = (0 : Word) := by
    have : s196 = runN s144 52 := hrun196
    rw [this, hi3.2.2.2.2.2.1, hs144P]
    exact (rfl : (1 : Word) - 1 = 0)
  have hpresL3 := hi3.2.2.2.2.2.2
  have hpres196 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s196.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s196 = runN s144 52 := hrun196
    rw [this]
    exact (hpresL3 a ha35 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres144 a ha32 ha33 ha34 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs196B0 : s196.mem.get 32 = 32 := by
    have : s196 = runN s144 52 := hrun196
    rw [this]
    exact (hpresL3 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs144B0
  have hs196B1 : s196.mem.get 33 = 32 := by
    have : s196 = runN s144 52 := hrun196
    rw [this]
    exact (hpresL3 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs144B1
  have hs196B2 : s196.mem.get 34 = 32 := by
    have : s196 = runN s144 52 := hrun196
    rw [this]
    exact (hpresL3 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs144B2
  have hsPeq : sP = s196 := rfl
  have hsPpc : sP.pc = 1011 := by rw [hsPeq]; exact hs196pc
  have hsPh : sP.halted = false := by rw [hsPeq]; exact hs196h
  have hsPZ : sP.mem.get 0 = 0 := by rw [hsPeq]; exact hs196Z
  have hsPB0 : sP.mem.get 32 = 32 := by rw [hsPeq]; exact hs196B0
  have hsPB1 : sP.mem.get 33 = 32 := by rw [hsPeq]; exact hs196B1
  have hsPB2 : sP.mem.get 34 = 32 := by rw [hsPeq]; exact hs196B2
  have hsPB3 : sP.mem.get 35 = 32 := by rw [hsPeq]; exact hs196B3
  have hsPI : sP.mem.get 29 = 4 := by rw [hsPeq]; exact hs196I
  have hsPP : sP.mem.get 27 = 0 := by rw [hsPeq]; exact hs196P
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sP.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha29 ha27 ha18 ha30 ha2319 ha0
    rw [hsPeq]
    exact hpres196 a ha32 ha33 ha34 ha35 ha29 ha27 ha18 ha30 ha2319 ha0
  exact ⟨hsPpc, hsPh, hsPZ, hsPB0, hsPB1, hsPB2, hsPB3, hsPI, hsPP, hpres⟩

/-- From `SP_LOOP` with `PAD = 5` and `IDX = 0`, and `5 ≤ ROOM`: write 5
spaces at `BUF+0..BUF+4` and return to `SP_LOOP` with `IDX = 5` and
`PAD = 0`. 250 steps. -/
theorem pad_5_spaces_idx0 {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 0)
    (hP : s.mem.get 27 = 5)
    (hRlo : 5 ≤ (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sP := runN s 250
    sP.pc = 1011 ∧
    sP.halted = false ∧
    sP.mem.get 0 = 0 ∧
    sP.mem.get 32 = 32 ∧
    sP.mem.get 33 = 32 ∧
    sP.mem.get 34 = 32 ∧
    sP.mem.get 35 = 32 ∧
    sP.mem.get 36 = 32 ∧
    sP.mem.get 29 = 5 ∧
    sP.mem.get 27 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sP.mem.get a = s.mem.get a) := by
  intro sP
  have hPlo0 : 0 < (s.mem.get 27).toNat := by simp [hP]
  have hPhi0 : (s.mem.get 27).toNat < 32768 := by simp [hP]
  have hRlo0 : 0 < (s.mem.get 28).toNat := by omega
  have hi0 := pad_one_iter_idx0 (s := s) hpc hh hZ hONE hK32 hI hPlo0 hPhi0 hRlo0 hRhi
    (fun k h1 h2 => hcode k h1 h2)
  let s46 := runN s 46
  have hs46pc : s46.pc = 1011 := hi0.1
  have hs46h : s46.halted = false := hi0.2.1
  have hs46Z : s46.mem.get 0 = 0 := hi0.2.2.1
  have hs46B0 : s46.mem.get 32 = 32 := hi0.2.2.2.1
  have hs46I : s46.mem.get 29 = 1 := hi0.2.2.2.2.1
  have hs46P : s46.mem.get 27 = (4 : Word) := by
    have h := hi0.2.2.2.2.2.1
    rw [h, hP]
    exact (rfl : (5 : Word) - 1 = 4)
  have hpres46 := hi0.2.2.2.2.2.2
  have hONE46 : s46.mem.get 3 = 1 := (hpres46 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK46 : s46.mem.get 10 = 32 := (hpres46 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo46 : 0 < (s46.mem.get 27).toNat := by
    have : s46.mem.get 27 = (4 : Word) := hs46P
    simp [this]
  have hPhi46 : (s46.mem.get 27).toNat < 32768 := by
    have : s46.mem.get 27 = (4 : Word) := hs46P
    simp [this]
  have hRlo46 : 1 < (s46.mem.get 28).toNat := by
    have : s46.mem.get 28 = s.mem.get 28 := hpres46 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi46 : (s46.mem.get 28).toNat < 32768 := by
    have : s46.mem.get 28 = s.mem.get 28 := hpres46 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g46 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s46.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres46 (UInt16.ofNat k) n32 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi1 := pad_one_iter_idx1 (s := s46) hs46pc hs46h hs46Z hONE46 hK46 hs46I
    hPlo46 hPhi46 hRlo46 hRhi46 g46
  have hrun94 : runN s 94 = runN s46 48 := runN_add_eq s 46 48 94 (by decide)
  let s94 := runN s 94
  have hs94pc : s94.pc = 1011 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.1
  have hs94h : s94.halted = false := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.1
  have hs94Z : s94.mem.get 0 = 0 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.1
  have hs94B1 : s94.mem.get 33 = 32 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.2.1
  have hs94I : s94.mem.get 29 = 2 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.2.2.1
  have hs94P : s94.mem.get 27 = (3 : Word) := by
    have : s94 = runN s46 48 := hrun94
    rw [this, hi1.2.2.2.2.2.1, hs46P]
    exact (rfl : (4 : Word) - 1 = 3)
  have hpresL1 := hi1.2.2.2.2.2.2
  have hpres94 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s94.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s94 = runN s46 48 := hrun94
    rw [this]
    exact (hpresL1 a ha33 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres46 a ha32 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs94B0 : s94.mem.get 32 = 32 := by
    have : s94 = runN s46 48 := hrun94
    rw [this]
    exact (hpresL1 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs46B0
  have hONE94 : s94.mem.get 3 = 1 := (hpres94 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK94 : s94.mem.get 10 = 32 := (hpres94 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo94 : 0 < (s94.mem.get 27).toNat := by
    have : s94.mem.get 27 = (3 : Word) := hs94P
    simp [this]
  have hPhi94 : (s94.mem.get 27).toNat < 32768 := by
    have : s94.mem.get 27 = (3 : Word) := hs94P
    simp [this]
  have hRlo94 : 2 < (s94.mem.get 28).toNat := by
    have : s94.mem.get 28 = s.mem.get 28 := hpres94 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi94 : (s94.mem.get 28).toNat < 32768 := by
    have : s94.mem.get 28 = s.mem.get 28 := hpres94 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g94 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s94.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres94 (UInt16.ofNat k) n32 n33 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi2 := pad_one_iter_idx2 (s := s94) hs94pc hs94h hs94Z hONE94 hK94 hs94I
    hPlo94 hPhi94 hRlo94 hRhi94 g94
  have hrun144 : runN s 144 = runN s94 50 := runN_add_eq s 94 50 144 (by decide)
  let s144 := runN s 144
  have hs144pc : s144.pc = 1011 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.1
  have hs144h : s144.halted = false := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.1
  have hs144Z : s144.mem.get 0 = 0 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.2.1
  have hs144B2 : s144.mem.get 34 = 32 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.2.2.1
  have hs144I : s144.mem.get 29 = 3 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.2.2.2.1
  have hs144P : s144.mem.get 27 = (2 : Word) := by
    have : s144 = runN s94 50 := hrun144
    rw [this, hi2.2.2.2.2.2.1, hs94P]
    exact (rfl : (3 : Word) - 1 = 2)
  have hpresL2 := hi2.2.2.2.2.2.2
  have hpres144 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s144.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s144 = runN s94 50 := hrun144
    rw [this]
    exact (hpresL2 a ha34 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres94 a ha32 ha33 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs144B0 : s144.mem.get 32 = 32 := by
    have : s144 = runN s94 50 := hrun144
    rw [this]
    exact (hpresL2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs94B0
  have hs144B1 : s144.mem.get 33 = 32 := by
    have : s144 = runN s94 50 := hrun144
    rw [this]
    exact (hpresL2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs94B1
  have hONE144 : s144.mem.get 3 = 1 := (hpres144 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK144 : s144.mem.get 10 = 32 := (hpres144 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo144 : 0 < (s144.mem.get 27).toNat := by
    have : s144.mem.get 27 = (2 : Word) := hs144P
    simp [this]
  have hPhi144 : (s144.mem.get 27).toNat < 32768 := by
    have : s144.mem.get 27 = (2 : Word) := hs144P
    simp [this]
  have hRlo144 : 3 < (s144.mem.get 28).toNat := by
    have : s144.mem.get 28 = s.mem.get 28 := hpres144 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi144 : (s144.mem.get 28).toNat < 32768 := by
    have : s144.mem.get 28 = s.mem.get 28 := hpres144 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g144 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s144.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres144 (UInt16.ofNat k) n32 n33 n34 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi3 := pad_one_iter_idx3 (s := s144) hs144pc hs144h hs144Z hONE144 hK144 hs144I
    hPlo144 hPhi144 hRlo144 hRhi144 g144
  have hrun196 : runN s 196 = runN s144 52 := runN_add_eq s 144 52 196 (by decide)
  let s196 := runN s 196
  have hs196pc : s196.pc = 1011 := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.1
  have hs196h : s196.halted = false := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.2.1
  have hs196Z : s196.mem.get 0 = 0 := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.2.2.1
  have hs196B3 : s196.mem.get 35 = 32 := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.2.2.2.1
  have hs196I : s196.mem.get 29 = 4 := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.2.2.2.2.1
  have hs196P : s196.mem.get 27 = (1 : Word) := by
    have : s196 = runN s144 52 := hrun196
    rw [this, hi3.2.2.2.2.2.1, hs144P]
    exact (rfl : (2 : Word) - 1 = 1)
  have hpresL3 := hi3.2.2.2.2.2.2
  have hpres196 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s196.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s196 = runN s144 52 := hrun196
    rw [this]
    exact (hpresL3 a ha35 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres144 a ha32 ha33 ha34 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs196B0 : s196.mem.get 32 = 32 := by
    have : s196 = runN s144 52 := hrun196
    rw [this]
    exact (hpresL3 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs144B0
  have hs196B1 : s196.mem.get 33 = 32 := by
    have : s196 = runN s144 52 := hrun196
    rw [this]
    exact (hpresL3 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs144B1
  have hs196B2 : s196.mem.get 34 = 32 := by
    have : s196 = runN s144 52 := hrun196
    rw [this]
    exact (hpresL3 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs144B2
  have hONE196 : s196.mem.get 3 = 1 := (hpres196 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK196 : s196.mem.get 10 = 32 := (hpres196 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo196 : 0 < (s196.mem.get 27).toNat := by
    have : s196.mem.get 27 = (1 : Word) := hs196P
    simp [this]
  have hPhi196 : (s196.mem.get 27).toNat < 32768 := by
    have : s196.mem.get 27 = (1 : Word) := hs196P
    simp [this]
  have hRlo196 : 4 < (s196.mem.get 28).toNat := by
    have : s196.mem.get 28 = s.mem.get 28 := hpres196 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi196 : (s196.mem.get 28).toNat < 32768 := by
    have : s196.mem.get 28 = s.mem.get 28 := hpres196 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g196 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s196.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres196 (UInt16.ofNat k) n32 n33 n34 n35 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi4 := pad_one_iter_idx4 (s := s196) hs196pc hs196h hs196Z hONE196 hK196 hs196I
    hPlo196 hPhi196 hRlo196 hRhi196 g196
  have hrun250 : runN s 250 = runN s196 54 := runN_add_eq s 196 54 250 (by decide)
  let s250 := runN s 250
  have hs250pc : s250.pc = 1011 := by
    have : s250 = runN s196 54 := hrun250; rw [this]; exact hi4.1
  have hs250h : s250.halted = false := by
    have : s250 = runN s196 54 := hrun250; rw [this]; exact hi4.2.1
  have hs250Z : s250.mem.get 0 = 0 := by
    have : s250 = runN s196 54 := hrun250; rw [this]; exact hi4.2.2.1
  have hs250B4 : s250.mem.get 36 = 32 := by
    have : s250 = runN s196 54 := hrun250; rw [this]; exact hi4.2.2.2.1
  have hs250I : s250.mem.get 29 = 5 := by
    have : s250 = runN s196 54 := hrun250; rw [this]; exact hi4.2.2.2.2.1
  have hs250P : s250.mem.get 27 = (0 : Word) := by
    have : s250 = runN s196 54 := hrun250
    rw [this, hi4.2.2.2.2.2.1, hs196P]
    exact (rfl : (1 : Word) - 1 = 0)
  have hpresL4 := hi4.2.2.2.2.2.2
  have hpres250 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s250.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s250 = runN s196 54 := hrun250
    rw [this]
    exact (hpresL4 a ha36 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres196 a ha32 ha33 ha34 ha35 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs250B0 : s250.mem.get 32 = 32 := by
    have : s250 = runN s196 54 := hrun250
    rw [this]
    exact (hpresL4 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs196B0
  have hs250B1 : s250.mem.get 33 = 32 := by
    have : s250 = runN s196 54 := hrun250
    rw [this]
    exact (hpresL4 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs196B1
  have hs250B2 : s250.mem.get 34 = 32 := by
    have : s250 = runN s196 54 := hrun250
    rw [this]
    exact (hpresL4 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs196B2
  have hs250B3 : s250.mem.get 35 = 32 := by
    have : s250 = runN s196 54 := hrun250
    rw [this]
    exact (hpresL4 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs196B3
  have hsPeq : sP = s250 := rfl
  have hsPpc : sP.pc = 1011 := by rw [hsPeq]; exact hs250pc
  have hsPh : sP.halted = false := by rw [hsPeq]; exact hs250h
  have hsPZ : sP.mem.get 0 = 0 := by rw [hsPeq]; exact hs250Z
  have hsPB0 : sP.mem.get 32 = 32 := by rw [hsPeq]; exact hs250B0
  have hsPB1 : sP.mem.get 33 = 32 := by rw [hsPeq]; exact hs250B1
  have hsPB2 : sP.mem.get 34 = 32 := by rw [hsPeq]; exact hs250B2
  have hsPB3 : sP.mem.get 35 = 32 := by rw [hsPeq]; exact hs250B3
  have hsPB4 : sP.mem.get 36 = 32 := by rw [hsPeq]; exact hs250B4
  have hsPI : sP.mem.get 29 = 5 := by rw [hsPeq]; exact hs250I
  have hsPP : sP.mem.get 27 = 0 := by rw [hsPeq]; exact hs250P
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sP.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha29 ha27 ha18 ha30 ha2319 ha0
    rw [hsPeq]
    exact hpres250 a ha32 ha33 ha34 ha35 ha36 ha29 ha27 ha18 ha30 ha2319 ha0
  exact ⟨hsPpc, hsPh, hsPZ, hsPB0, hsPB1, hsPB2, hsPB3, hsPB4, hsPI, hsPP, hpres⟩

/-- From `SP_LOOP` with `PAD = 6` and `IDX = 0`, and `6 ≤ ROOM`: write 6
spaces at `BUF+0..BUF+5` and return to `SP_LOOP` with `IDX = 6` and
`PAD = 0`. 306 steps. -/
theorem pad_6_spaces_idx0 {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 0)
    (hP : s.mem.get 27 = 6)
    (hRlo : 6 ≤ (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sP := runN s 306
    sP.pc = 1011 ∧
    sP.halted = false ∧
    sP.mem.get 0 = 0 ∧
    sP.mem.get 32 = 32 ∧
    sP.mem.get 33 = 32 ∧
    sP.mem.get 34 = 32 ∧
    sP.mem.get 35 = 32 ∧
    sP.mem.get 36 = 32 ∧
    sP.mem.get 37 = 32 ∧
    sP.mem.get 29 = 6 ∧
    sP.mem.get 27 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sP.mem.get a = s.mem.get a) := by
  intro sP
  have hPlo0 : 0 < (s.mem.get 27).toNat := by simp [hP]
  have hPhi0 : (s.mem.get 27).toNat < 32768 := by simp [hP]
  have hRlo0 : 0 < (s.mem.get 28).toNat := by omega
  have hi0 := pad_one_iter_idx0 (s := s) hpc hh hZ hONE hK32 hI hPlo0 hPhi0 hRlo0 hRhi
    (fun k h1 h2 => hcode k h1 h2)
  let s46 := runN s 46
  have hs46pc : s46.pc = 1011 := hi0.1
  have hs46h : s46.halted = false := hi0.2.1
  have hs46Z : s46.mem.get 0 = 0 := hi0.2.2.1
  have hs46B0 : s46.mem.get 32 = 32 := hi0.2.2.2.1
  have hs46I : s46.mem.get 29 = 1 := hi0.2.2.2.2.1
  have hs46P : s46.mem.get 27 = (5 : Word) := by
    have h := hi0.2.2.2.2.2.1
    rw [h, hP]
    exact (rfl : (6 : Word) - 1 = 5)
  have hpres46 := hi0.2.2.2.2.2.2
  have hONE46 : s46.mem.get 3 = 1 := (hpres46 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK46 : s46.mem.get 10 = 32 := (hpres46 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo46 : 0 < (s46.mem.get 27).toNat := by
    have : s46.mem.get 27 = (5 : Word) := hs46P
    simp [this]
  have hPhi46 : (s46.mem.get 27).toNat < 32768 := by
    have : s46.mem.get 27 = (5 : Word) := hs46P
    simp [this]
  have hRlo46 : 1 < (s46.mem.get 28).toNat := by
    have : s46.mem.get 28 = s.mem.get 28 := hpres46 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi46 : (s46.mem.get 28).toNat < 32768 := by
    have : s46.mem.get 28 = s.mem.get 28 := hpres46 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g46 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s46.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres46 (UInt16.ofNat k) n32 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi1 := pad_one_iter_idx1 (s := s46) hs46pc hs46h hs46Z hONE46 hK46 hs46I
    hPlo46 hPhi46 hRlo46 hRhi46 g46
  have hrun94 : runN s 94 = runN s46 48 := runN_add_eq s 46 48 94 (by decide)
  let s94 := runN s 94
  have hs94pc : s94.pc = 1011 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.1
  have hs94h : s94.halted = false := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.1
  have hs94Z : s94.mem.get 0 = 0 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.1
  have hs94B1 : s94.mem.get 33 = 32 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.2.1
  have hs94I : s94.mem.get 29 = 2 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.2.2.1
  have hs94P : s94.mem.get 27 = (4 : Word) := by
    have : s94 = runN s46 48 := hrun94
    rw [this, hi1.2.2.2.2.2.1, hs46P]
    exact (rfl : (5 : Word) - 1 = 4)
  have hpresL1 := hi1.2.2.2.2.2.2
  have hpres94 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s94.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s94 = runN s46 48 := hrun94
    rw [this]
    exact (hpresL1 a ha33 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres46 a ha32 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs94B0 : s94.mem.get 32 = 32 := by
    have : s94 = runN s46 48 := hrun94
    rw [this]
    exact (hpresL1 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs46B0
  have hONE94 : s94.mem.get 3 = 1 := (hpres94 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK94 : s94.mem.get 10 = 32 := (hpres94 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo94 : 0 < (s94.mem.get 27).toNat := by
    have : s94.mem.get 27 = (4 : Word) := hs94P
    simp [this]
  have hPhi94 : (s94.mem.get 27).toNat < 32768 := by
    have : s94.mem.get 27 = (4 : Word) := hs94P
    simp [this]
  have hRlo94 : 2 < (s94.mem.get 28).toNat := by
    have : s94.mem.get 28 = s.mem.get 28 := hpres94 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi94 : (s94.mem.get 28).toNat < 32768 := by
    have : s94.mem.get 28 = s.mem.get 28 := hpres94 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g94 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s94.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres94 (UInt16.ofNat k) n32 n33 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi2 := pad_one_iter_idx2 (s := s94) hs94pc hs94h hs94Z hONE94 hK94 hs94I
    hPlo94 hPhi94 hRlo94 hRhi94 g94
  have hrun144 : runN s 144 = runN s94 50 := runN_add_eq s 94 50 144 (by decide)
  let s144 := runN s 144
  have hs144pc : s144.pc = 1011 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.1
  have hs144h : s144.halted = false := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.1
  have hs144Z : s144.mem.get 0 = 0 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.2.1
  have hs144B2 : s144.mem.get 34 = 32 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.2.2.1
  have hs144I : s144.mem.get 29 = 3 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.2.2.2.1
  have hs144P : s144.mem.get 27 = (3 : Word) := by
    have : s144 = runN s94 50 := hrun144
    rw [this, hi2.2.2.2.2.2.1, hs94P]
    exact (rfl : (4 : Word) - 1 = 3)
  have hpresL2 := hi2.2.2.2.2.2.2
  have hpres144 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s144.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s144 = runN s94 50 := hrun144
    rw [this]
    exact (hpresL2 a ha34 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres94 a ha32 ha33 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs144B0 : s144.mem.get 32 = 32 := by
    have : s144 = runN s94 50 := hrun144
    rw [this]
    exact (hpresL2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs94B0
  have hs144B1 : s144.mem.get 33 = 32 := by
    have : s144 = runN s94 50 := hrun144
    rw [this]
    exact (hpresL2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs94B1
  have hONE144 : s144.mem.get 3 = 1 := (hpres144 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK144 : s144.mem.get 10 = 32 := (hpres144 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo144 : 0 < (s144.mem.get 27).toNat := by
    have : s144.mem.get 27 = (3 : Word) := hs144P
    simp [this]
  have hPhi144 : (s144.mem.get 27).toNat < 32768 := by
    have : s144.mem.get 27 = (3 : Word) := hs144P
    simp [this]
  have hRlo144 : 3 < (s144.mem.get 28).toNat := by
    have : s144.mem.get 28 = s.mem.get 28 := hpres144 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi144 : (s144.mem.get 28).toNat < 32768 := by
    have : s144.mem.get 28 = s.mem.get 28 := hpres144 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g144 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s144.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres144 (UInt16.ofNat k) n32 n33 n34 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi3 := pad_one_iter_idx3 (s := s144) hs144pc hs144h hs144Z hONE144 hK144 hs144I
    hPlo144 hPhi144 hRlo144 hRhi144 g144
  have hrun196 : runN s 196 = runN s144 52 := runN_add_eq s 144 52 196 (by decide)
  let s196 := runN s 196
  have hs196pc : s196.pc = 1011 := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.1
  have hs196h : s196.halted = false := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.2.1
  have hs196Z : s196.mem.get 0 = 0 := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.2.2.1
  have hs196B3 : s196.mem.get 35 = 32 := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.2.2.2.1
  have hs196I : s196.mem.get 29 = 4 := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.2.2.2.2.1
  have hs196P : s196.mem.get 27 = (2 : Word) := by
    have : s196 = runN s144 52 := hrun196
    rw [this, hi3.2.2.2.2.2.1, hs144P]
    exact (rfl : (3 : Word) - 1 = 2)
  have hpresL3 := hi3.2.2.2.2.2.2
  have hpres196 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s196.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s196 = runN s144 52 := hrun196
    rw [this]
    exact (hpresL3 a ha35 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres144 a ha32 ha33 ha34 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs196B0 : s196.mem.get 32 = 32 := by
    have : s196 = runN s144 52 := hrun196
    rw [this]
    exact (hpresL3 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs144B0
  have hs196B1 : s196.mem.get 33 = 32 := by
    have : s196 = runN s144 52 := hrun196
    rw [this]
    exact (hpresL3 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs144B1
  have hs196B2 : s196.mem.get 34 = 32 := by
    have : s196 = runN s144 52 := hrun196
    rw [this]
    exact (hpresL3 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs144B2
  have hONE196 : s196.mem.get 3 = 1 := (hpres196 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK196 : s196.mem.get 10 = 32 := (hpres196 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo196 : 0 < (s196.mem.get 27).toNat := by
    have : s196.mem.get 27 = (2 : Word) := hs196P
    simp [this]
  have hPhi196 : (s196.mem.get 27).toNat < 32768 := by
    have : s196.mem.get 27 = (2 : Word) := hs196P
    simp [this]
  have hRlo196 : 4 < (s196.mem.get 28).toNat := by
    have : s196.mem.get 28 = s.mem.get 28 := hpres196 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi196 : (s196.mem.get 28).toNat < 32768 := by
    have : s196.mem.get 28 = s.mem.get 28 := hpres196 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g196 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s196.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres196 (UInt16.ofNat k) n32 n33 n34 n35 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi4 := pad_one_iter_idx4 (s := s196) hs196pc hs196h hs196Z hONE196 hK196 hs196I
    hPlo196 hPhi196 hRlo196 hRhi196 g196
  have hrun250 : runN s 250 = runN s196 54 := runN_add_eq s 196 54 250 (by decide)
  let s250 := runN s 250
  have hs250pc : s250.pc = 1011 := by
    have : s250 = runN s196 54 := hrun250; rw [this]; exact hi4.1
  have hs250h : s250.halted = false := by
    have : s250 = runN s196 54 := hrun250; rw [this]; exact hi4.2.1
  have hs250Z : s250.mem.get 0 = 0 := by
    have : s250 = runN s196 54 := hrun250; rw [this]; exact hi4.2.2.1
  have hs250B4 : s250.mem.get 36 = 32 := by
    have : s250 = runN s196 54 := hrun250; rw [this]; exact hi4.2.2.2.1
  have hs250I : s250.mem.get 29 = 5 := by
    have : s250 = runN s196 54 := hrun250; rw [this]; exact hi4.2.2.2.2.1
  have hs250P : s250.mem.get 27 = (1 : Word) := by
    have : s250 = runN s196 54 := hrun250
    rw [this, hi4.2.2.2.2.2.1, hs196P]
    exact (rfl : (2 : Word) - 1 = 1)
  have hpresL4 := hi4.2.2.2.2.2.2
  have hpres250 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s250.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s250 = runN s196 54 := hrun250
    rw [this]
    exact (hpresL4 a ha36 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres196 a ha32 ha33 ha34 ha35 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs250B0 : s250.mem.get 32 = 32 := by
    have : s250 = runN s196 54 := hrun250
    rw [this]
    exact (hpresL4 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs196B0
  have hs250B1 : s250.mem.get 33 = 32 := by
    have : s250 = runN s196 54 := hrun250
    rw [this]
    exact (hpresL4 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs196B1
  have hs250B2 : s250.mem.get 34 = 32 := by
    have : s250 = runN s196 54 := hrun250
    rw [this]
    exact (hpresL4 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs196B2
  have hs250B3 : s250.mem.get 35 = 32 := by
    have : s250 = runN s196 54 := hrun250
    rw [this]
    exact (hpresL4 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs196B3
  have hONE250 : s250.mem.get 3 = 1 := (hpres250 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK250 : s250.mem.get 10 = 32 := (hpres250 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo250 : 0 < (s250.mem.get 27).toNat := by
    have : s250.mem.get 27 = (1 : Word) := hs250P
    simp [this]
  have hPhi250 : (s250.mem.get 27).toNat < 32768 := by
    have : s250.mem.get 27 = (1 : Word) := hs250P
    simp [this]
  have hRlo250 : 5 < (s250.mem.get 28).toNat := by
    have : s250.mem.get 28 = s.mem.get 28 := hpres250 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi250 : (s250.mem.get 28).toNat < 32768 := by
    have : s250.mem.get 28 = s.mem.get 28 := hpres250 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g250 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s250.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres250 (UInt16.ofNat k) n32 n33 n34 n35 n36 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi5 := pad_one_iter_idx5 (s := s250) hs250pc hs250h hs250Z hONE250 hK250 hs250I
    hPlo250 hPhi250 hRlo250 hRhi250 g250
  have hrun306 : runN s 306 = runN s250 56 := runN_add_eq s 250 56 306 (by decide)
  let s306 := runN s 306
  have hs306pc : s306.pc = 1011 := by
    have : s306 = runN s250 56 := hrun306; rw [this]; exact hi5.1
  have hs306h : s306.halted = false := by
    have : s306 = runN s250 56 := hrun306; rw [this]; exact hi5.2.1
  have hs306Z : s306.mem.get 0 = 0 := by
    have : s306 = runN s250 56 := hrun306; rw [this]; exact hi5.2.2.1
  have hs306B5 : s306.mem.get 37 = 32 := by
    have : s306 = runN s250 56 := hrun306; rw [this]; exact hi5.2.2.2.1
  have hs306I : s306.mem.get 29 = 6 := by
    have : s306 = runN s250 56 := hrun306; rw [this]; exact hi5.2.2.2.2.1
  have hs306P : s306.mem.get 27 = (0 : Word) := by
    have : s306 = runN s250 56 := hrun306
    rw [this, hi5.2.2.2.2.2.1, hs250P]
    exact (rfl : (1 : Word) - 1 = 0)
  have hpresL5 := hi5.2.2.2.2.2.2
  have hpres306 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s306.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s306 = runN s250 56 := hrun306
    rw [this]
    exact (hpresL5 a ha37 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres250 a ha32 ha33 ha34 ha35 ha36 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs306B0 : s306.mem.get 32 = 32 := by
    have : s306 = runN s250 56 := hrun306
    rw [this]
    exact (hpresL5 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs250B0
  have hs306B1 : s306.mem.get 33 = 32 := by
    have : s306 = runN s250 56 := hrun306
    rw [this]
    exact (hpresL5 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs250B1
  have hs306B2 : s306.mem.get 34 = 32 := by
    have : s306 = runN s250 56 := hrun306
    rw [this]
    exact (hpresL5 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs250B2
  have hs306B3 : s306.mem.get 35 = 32 := by
    have : s306 = runN s250 56 := hrun306
    rw [this]
    exact (hpresL5 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs250B3
  have hs306B4 : s306.mem.get 36 = 32 := by
    have : s306 = runN s250 56 := hrun306
    rw [this]
    exact (hpresL5 36 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs250B4
  have hsPeq : sP = s306 := rfl
  have hsPpc : sP.pc = 1011 := by rw [hsPeq]; exact hs306pc
  have hsPh : sP.halted = false := by rw [hsPeq]; exact hs306h
  have hsPZ : sP.mem.get 0 = 0 := by rw [hsPeq]; exact hs306Z
  have hsPB0 : sP.mem.get 32 = 32 := by rw [hsPeq]; exact hs306B0
  have hsPB1 : sP.mem.get 33 = 32 := by rw [hsPeq]; exact hs306B1
  have hsPB2 : sP.mem.get 34 = 32 := by rw [hsPeq]; exact hs306B2
  have hsPB3 : sP.mem.get 35 = 32 := by rw [hsPeq]; exact hs306B3
  have hsPB4 : sP.mem.get 36 = 32 := by rw [hsPeq]; exact hs306B4
  have hsPB5 : sP.mem.get 37 = 32 := by rw [hsPeq]; exact hs306B5
  have hsPI : sP.mem.get 29 = 6 := by rw [hsPeq]; exact hs306I
  have hsPP : sP.mem.get 27 = 0 := by rw [hsPeq]; exact hs306P
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sP.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha29 ha27 ha18 ha30 ha2319 ha0
    rw [hsPeq]
    exact hpres306 a ha32 ha33 ha34 ha35 ha36 ha37 ha29 ha27 ha18 ha30 ha2319 ha0
  exact ⟨hsPpc, hsPh, hsPZ, hsPB0, hsPB1, hsPB2, hsPB3, hsPB4, hsPB5, hsPI, hsPP, hpres⟩

/-- From `SP_LOOP` with `PAD = 7` and `IDX = 0`, and `7 ≤ ROOM`: write 7
spaces at `BUF+0..BUF+6` and return to `SP_LOOP` with `IDX = 7` and
`PAD = 0`. 364 steps. -/
theorem pad_7_spaces_idx0 {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 0)
    (hP : s.mem.get 27 = 7)
    (hRlo : 7 ≤ (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sP := runN s 364
    sP.pc = 1011 ∧
    sP.halted = false ∧
    sP.mem.get 0 = 0 ∧
    sP.mem.get 32 = 32 ∧
    sP.mem.get 33 = 32 ∧
    sP.mem.get 34 = 32 ∧
    sP.mem.get 35 = 32 ∧
    sP.mem.get 36 = 32 ∧
    sP.mem.get 37 = 32 ∧
    sP.mem.get 38 = 32 ∧
    sP.mem.get 29 = 7 ∧
    sP.mem.get 27 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 38 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sP.mem.get a = s.mem.get a) := by
  intro sP
  have hPlo0 : 0 < (s.mem.get 27).toNat := by simp [hP]
  have hPhi0 : (s.mem.get 27).toNat < 32768 := by simp [hP]
  have hRlo0 : 0 < (s.mem.get 28).toNat := by omega
  have hi0 := pad_one_iter_idx0 (s := s) hpc hh hZ hONE hK32 hI hPlo0 hPhi0 hRlo0 hRhi
    (fun k h1 h2 => hcode k h1 h2)
  let s46 := runN s 46
  have hs46pc : s46.pc = 1011 := hi0.1
  have hs46h : s46.halted = false := hi0.2.1
  have hs46Z : s46.mem.get 0 = 0 := hi0.2.2.1
  have hs46B0 : s46.mem.get 32 = 32 := hi0.2.2.2.1
  have hs46I : s46.mem.get 29 = 1 := hi0.2.2.2.2.1
  have hs46P : s46.mem.get 27 = (6 : Word) := by
    have h := hi0.2.2.2.2.2.1
    rw [h, hP]
    exact (rfl : (7 : Word) - 1 = 6)
  have hpres46 := hi0.2.2.2.2.2.2
  have hONE46 : s46.mem.get 3 = 1 := (hpres46 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK46 : s46.mem.get 10 = 32 := (hpres46 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo46 : 0 < (s46.mem.get 27).toNat := by
    have : s46.mem.get 27 = (6 : Word) := hs46P
    simp [this]
  have hPhi46 : (s46.mem.get 27).toNat < 32768 := by
    have : s46.mem.get 27 = (6 : Word) := hs46P
    simp [this]
  have hRlo46 : 1 < (s46.mem.get 28).toNat := by
    have : s46.mem.get 28 = s.mem.get 28 := hpres46 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi46 : (s46.mem.get 28).toNat < 32768 := by
    have : s46.mem.get 28 = s.mem.get 28 := hpres46 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g46 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s46.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres46 (UInt16.ofNat k) n32 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi1 := pad_one_iter_idx1 (s := s46) hs46pc hs46h hs46Z hONE46 hK46 hs46I
    hPlo46 hPhi46 hRlo46 hRhi46 g46
  have hrun94 : runN s 94 = runN s46 48 := runN_add_eq s 46 48 94 (by decide)
  let s94 := runN s 94
  have hs94pc : s94.pc = 1011 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.1
  have hs94h : s94.halted = false := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.1
  have hs94Z : s94.mem.get 0 = 0 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.1
  have hs94B1 : s94.mem.get 33 = 32 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.2.1
  have hs94I : s94.mem.get 29 = 2 := by
    have : s94 = runN s46 48 := hrun94; rw [this]; exact hi1.2.2.2.2.1
  have hs94P : s94.mem.get 27 = (5 : Word) := by
    have : s94 = runN s46 48 := hrun94
    rw [this, hi1.2.2.2.2.2.1, hs46P]
    exact (rfl : (6 : Word) - 1 = 5)
  have hpresL1 := hi1.2.2.2.2.2.2
  have hpres94 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s94.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s94 = runN s46 48 := hrun94
    rw [this]
    exact (hpresL1 a ha33 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres46 a ha32 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs94B0 : s94.mem.get 32 = 32 := by
    have : s94 = runN s46 48 := hrun94
    rw [this]
    exact (hpresL1 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs46B0
  have hONE94 : s94.mem.get 3 = 1 := (hpres94 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK94 : s94.mem.get 10 = 32 := (hpres94 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo94 : 0 < (s94.mem.get 27).toNat := by
    have : s94.mem.get 27 = (5 : Word) := hs94P
    simp [this]
  have hPhi94 : (s94.mem.get 27).toNat < 32768 := by
    have : s94.mem.get 27 = (5 : Word) := hs94P
    simp [this]
  have hRlo94 : 2 < (s94.mem.get 28).toNat := by
    have : s94.mem.get 28 = s.mem.get 28 := hpres94 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi94 : (s94.mem.get 28).toNat < 32768 := by
    have : s94.mem.get 28 = s.mem.get 28 := hpres94 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g94 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s94.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres94 (UInt16.ofNat k) n32 n33 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi2 := pad_one_iter_idx2 (s := s94) hs94pc hs94h hs94Z hONE94 hK94 hs94I
    hPlo94 hPhi94 hRlo94 hRhi94 g94
  have hrun144 : runN s 144 = runN s94 50 := runN_add_eq s 94 50 144 (by decide)
  let s144 := runN s 144
  have hs144pc : s144.pc = 1011 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.1
  have hs144h : s144.halted = false := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.1
  have hs144Z : s144.mem.get 0 = 0 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.2.1
  have hs144B2 : s144.mem.get 34 = 32 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.2.2.1
  have hs144I : s144.mem.get 29 = 3 := by
    have : s144 = runN s94 50 := hrun144; rw [this]; exact hi2.2.2.2.2.1
  have hs144P : s144.mem.get 27 = (4 : Word) := by
    have : s144 = runN s94 50 := hrun144
    rw [this, hi2.2.2.2.2.2.1, hs94P]
    exact (rfl : (5 : Word) - 1 = 4)
  have hpresL2 := hi2.2.2.2.2.2.2
  have hpres144 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s144.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s144 = runN s94 50 := hrun144
    rw [this]
    exact (hpresL2 a ha34 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres94 a ha32 ha33 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs144B0 : s144.mem.get 32 = 32 := by
    have : s144 = runN s94 50 := hrun144
    rw [this]
    exact (hpresL2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs94B0
  have hs144B1 : s144.mem.get 33 = 32 := by
    have : s144 = runN s94 50 := hrun144
    rw [this]
    exact (hpresL2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs94B1
  have hONE144 : s144.mem.get 3 = 1 := (hpres144 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK144 : s144.mem.get 10 = 32 := (hpres144 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo144 : 0 < (s144.mem.get 27).toNat := by
    have : s144.mem.get 27 = (4 : Word) := hs144P
    simp [this]
  have hPhi144 : (s144.mem.get 27).toNat < 32768 := by
    have : s144.mem.get 27 = (4 : Word) := hs144P
    simp [this]
  have hRlo144 : 3 < (s144.mem.get 28).toNat := by
    have : s144.mem.get 28 = s.mem.get 28 := hpres144 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi144 : (s144.mem.get 28).toNat < 32768 := by
    have : s144.mem.get 28 = s.mem.get 28 := hpres144 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g144 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s144.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres144 (UInt16.ofNat k) n32 n33 n34 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi3 := pad_one_iter_idx3 (s := s144) hs144pc hs144h hs144Z hONE144 hK144 hs144I
    hPlo144 hPhi144 hRlo144 hRhi144 g144
  have hrun196 : runN s 196 = runN s144 52 := runN_add_eq s 144 52 196 (by decide)
  let s196 := runN s 196
  have hs196pc : s196.pc = 1011 := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.1
  have hs196h : s196.halted = false := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.2.1
  have hs196Z : s196.mem.get 0 = 0 := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.2.2.1
  have hs196B3 : s196.mem.get 35 = 32 := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.2.2.2.1
  have hs196I : s196.mem.get 29 = 4 := by
    have : s196 = runN s144 52 := hrun196; rw [this]; exact hi3.2.2.2.2.1
  have hs196P : s196.mem.get 27 = (3 : Word) := by
    have : s196 = runN s144 52 := hrun196
    rw [this, hi3.2.2.2.2.2.1, hs144P]
    exact (rfl : (4 : Word) - 1 = 3)
  have hpresL3 := hi3.2.2.2.2.2.2
  have hpres196 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s196.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s196 = runN s144 52 := hrun196
    rw [this]
    exact (hpresL3 a ha35 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres144 a ha32 ha33 ha34 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs196B0 : s196.mem.get 32 = 32 := by
    have : s196 = runN s144 52 := hrun196
    rw [this]
    exact (hpresL3 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs144B0
  have hs196B1 : s196.mem.get 33 = 32 := by
    have : s196 = runN s144 52 := hrun196
    rw [this]
    exact (hpresL3 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs144B1
  have hs196B2 : s196.mem.get 34 = 32 := by
    have : s196 = runN s144 52 := hrun196
    rw [this]
    exact (hpresL3 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs144B2
  have hONE196 : s196.mem.get 3 = 1 := (hpres196 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK196 : s196.mem.get 10 = 32 := (hpres196 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo196 : 0 < (s196.mem.get 27).toNat := by
    have : s196.mem.get 27 = (3 : Word) := hs196P
    simp [this]
  have hPhi196 : (s196.mem.get 27).toNat < 32768 := by
    have : s196.mem.get 27 = (3 : Word) := hs196P
    simp [this]
  have hRlo196 : 4 < (s196.mem.get 28).toNat := by
    have : s196.mem.get 28 = s.mem.get 28 := hpres196 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi196 : (s196.mem.get 28).toNat < 32768 := by
    have : s196.mem.get 28 = s.mem.get 28 := hpres196 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g196 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s196.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres196 (UInt16.ofNat k) n32 n33 n34 n35 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi4 := pad_one_iter_idx4 (s := s196) hs196pc hs196h hs196Z hONE196 hK196 hs196I
    hPlo196 hPhi196 hRlo196 hRhi196 g196
  have hrun250 : runN s 250 = runN s196 54 := runN_add_eq s 196 54 250 (by decide)
  let s250 := runN s 250
  have hs250pc : s250.pc = 1011 := by
    have : s250 = runN s196 54 := hrun250; rw [this]; exact hi4.1
  have hs250h : s250.halted = false := by
    have : s250 = runN s196 54 := hrun250; rw [this]; exact hi4.2.1
  have hs250Z : s250.mem.get 0 = 0 := by
    have : s250 = runN s196 54 := hrun250; rw [this]; exact hi4.2.2.1
  have hs250B4 : s250.mem.get 36 = 32 := by
    have : s250 = runN s196 54 := hrun250; rw [this]; exact hi4.2.2.2.1
  have hs250I : s250.mem.get 29 = 5 := by
    have : s250 = runN s196 54 := hrun250; rw [this]; exact hi4.2.2.2.2.1
  have hs250P : s250.mem.get 27 = (2 : Word) := by
    have : s250 = runN s196 54 := hrun250
    rw [this, hi4.2.2.2.2.2.1, hs196P]
    exact (rfl : (3 : Word) - 1 = 2)
  have hpresL4 := hi4.2.2.2.2.2.2
  have hpres250 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s250.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s250 = runN s196 54 := hrun250
    rw [this]
    exact (hpresL4 a ha36 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres196 a ha32 ha33 ha34 ha35 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs250B0 : s250.mem.get 32 = 32 := by
    have : s250 = runN s196 54 := hrun250
    rw [this]
    exact (hpresL4 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs196B0
  have hs250B1 : s250.mem.get 33 = 32 := by
    have : s250 = runN s196 54 := hrun250
    rw [this]
    exact (hpresL4 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs196B1
  have hs250B2 : s250.mem.get 34 = 32 := by
    have : s250 = runN s196 54 := hrun250
    rw [this]
    exact (hpresL4 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs196B2
  have hs250B3 : s250.mem.get 35 = 32 := by
    have : s250 = runN s196 54 := hrun250
    rw [this]
    exact (hpresL4 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs196B3
  have hONE250 : s250.mem.get 3 = 1 := (hpres250 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK250 : s250.mem.get 10 = 32 := (hpres250 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo250 : 0 < (s250.mem.get 27).toNat := by
    have : s250.mem.get 27 = (2 : Word) := hs250P
    simp [this]
  have hPhi250 : (s250.mem.get 27).toNat < 32768 := by
    have : s250.mem.get 27 = (2 : Word) := hs250P
    simp [this]
  have hRlo250 : 5 < (s250.mem.get 28).toNat := by
    have : s250.mem.get 28 = s.mem.get 28 := hpres250 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi250 : (s250.mem.get 28).toNat < 32768 := by
    have : s250.mem.get 28 = s.mem.get 28 := hpres250 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g250 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s250.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres250 (UInt16.ofNat k) n32 n33 n34 n35 n36 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi5 := pad_one_iter_idx5 (s := s250) hs250pc hs250h hs250Z hONE250 hK250 hs250I
    hPlo250 hPhi250 hRlo250 hRhi250 g250
  have hrun306 : runN s 306 = runN s250 56 := runN_add_eq s 250 56 306 (by decide)
  let s306 := runN s 306
  have hs306pc : s306.pc = 1011 := by
    have : s306 = runN s250 56 := hrun306; rw [this]; exact hi5.1
  have hs306h : s306.halted = false := by
    have : s306 = runN s250 56 := hrun306; rw [this]; exact hi5.2.1
  have hs306Z : s306.mem.get 0 = 0 := by
    have : s306 = runN s250 56 := hrun306; rw [this]; exact hi5.2.2.1
  have hs306B5 : s306.mem.get 37 = 32 := by
    have : s306 = runN s250 56 := hrun306; rw [this]; exact hi5.2.2.2.1
  have hs306I : s306.mem.get 29 = 6 := by
    have : s306 = runN s250 56 := hrun306; rw [this]; exact hi5.2.2.2.2.1
  have hs306P : s306.mem.get 27 = (1 : Word) := by
    have : s306 = runN s250 56 := hrun306
    rw [this, hi5.2.2.2.2.2.1, hs250P]
    exact (rfl : (2 : Word) - 1 = 1)
  have hpresL5 := hi5.2.2.2.2.2.2
  have hpres306 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s306.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s306 = runN s250 56 := hrun306
    rw [this]
    exact (hpresL5 a ha37 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres250 a ha32 ha33 ha34 ha35 ha36 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs306B0 : s306.mem.get 32 = 32 := by
    have : s306 = runN s250 56 := hrun306
    rw [this]
    exact (hpresL5 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs250B0
  have hs306B1 : s306.mem.get 33 = 32 := by
    have : s306 = runN s250 56 := hrun306
    rw [this]
    exact (hpresL5 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs250B1
  have hs306B2 : s306.mem.get 34 = 32 := by
    have : s306 = runN s250 56 := hrun306
    rw [this]
    exact (hpresL5 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs250B2
  have hs306B3 : s306.mem.get 35 = 32 := by
    have : s306 = runN s250 56 := hrun306
    rw [this]
    exact (hpresL5 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs250B3
  have hs306B4 : s306.mem.get 36 = 32 := by
    have : s306 = runN s250 56 := hrun306
    rw [this]
    exact (hpresL5 36 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs250B4
  have hONE306 : s306.mem.get 3 = 1 := (hpres306 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK306 : s306.mem.get 10 = 32 := (hpres306 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK32
  have hPlo306 : 0 < (s306.mem.get 27).toNat := by
    have : s306.mem.get 27 = (1 : Word) := hs306P
    simp [this]
  have hPhi306 : (s306.mem.get 27).toNat < 32768 := by
    have : s306.mem.get 27 = (1 : Word) := hs306P
    simp [this]
  have hRlo306 : 6 < (s306.mem.get 28).toNat := by
    have : s306.mem.get 28 = s.mem.get 28 := hpres306 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; omega
  have hRhi306 : (s306.mem.get 28).toNat < 32768 := by
    have : s306.mem.get 28 = s.mem.get 28 := hpres306 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g306 : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s306.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n37 : UInt16.ofNat k ≠ (37 : Word) := by
      have : (37 : Word) = UInt16.ofNat 37 := rfl
      rw [this]; exact ofNat_ne k 37 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres306 (UInt16.ofNat k) n32 n33 n34 n35 n36 n37 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hi6 := pad_one_iter_idx6 (s := s306) hs306pc hs306h hs306Z hONE306 hK306 hs306I
    hPlo306 hPhi306 hRlo306 hRhi306 g306
  have hrun364 : runN s 364 = runN s306 58 := runN_add_eq s 306 58 364 (by decide)
  let s364 := runN s 364
  have hs364pc : s364.pc = 1011 := by
    have : s364 = runN s306 58 := hrun364; rw [this]; exact hi6.1
  have hs364h : s364.halted = false := by
    have : s364 = runN s306 58 := hrun364; rw [this]; exact hi6.2.1
  have hs364Z : s364.mem.get 0 = 0 := by
    have : s364 = runN s306 58 := hrun364; rw [this]; exact hi6.2.2.1
  have hs364B6 : s364.mem.get 38 = 32 := by
    have : s364 = runN s306 58 := hrun364; rw [this]; exact hi6.2.2.2.1
  have hs364I : s364.mem.get 29 = 7 := by
    have : s364 = runN s306 58 := hrun364; rw [this]; exact hi6.2.2.2.2.1
  have hs364P : s364.mem.get 27 = (0 : Word) := by
    have : s364 = runN s306 58 := hrun364
    rw [this, hi6.2.2.2.2.2.1, hs306P]
    exact (rfl : (1 : Word) - 1 = 0)
  have hpresL6 := hi6.2.2.2.2.2.2
  have hpres364 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 38 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      s364.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha38 ha29 ha27 ha18 ha30 ha2319 ha0
    have : s364 = runN s306 58 := hrun364
    rw [this]
    exact (hpresL6 a ha38 ha29 ha27 ha18 ha30 ha2319 ha0).trans
      (hpres306 a ha32 ha33 ha34 ha35 ha36 ha37 ha29 ha27 ha18 ha30 ha2319 ha0)
  have hs364B0 : s364.mem.get 32 = 32 := by
    have : s364 = runN s306 58 := hrun364
    rw [this]
    exact (hpresL6 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs306B0
  have hs364B1 : s364.mem.get 33 = 32 := by
    have : s364 = runN s306 58 := hrun364
    rw [this]
    exact (hpresL6 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs306B1
  have hs364B2 : s364.mem.get 34 = 32 := by
    have : s364 = runN s306 58 := hrun364
    rw [this]
    exact (hpresL6 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs306B2
  have hs364B3 : s364.mem.get 35 = 32 := by
    have : s364 = runN s306 58 := hrun364
    rw [this]
    exact (hpresL6 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs306B3
  have hs364B4 : s364.mem.get 36 = 32 := by
    have : s364 = runN s306 58 := hrun364
    rw [this]
    exact (hpresL6 36 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs306B4
  have hs364B5 : s364.mem.get 37 = 32 := by
    have : s364 = runN s306 58 := hrun364
    rw [this]
    exact (hpresL6 37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs306B5
  have hsPeq : sP = s364 := rfl
  have hsPpc : sP.pc = 1011 := by rw [hsPeq]; exact hs364pc
  have hsPh : sP.halted = false := by rw [hsPeq]; exact hs364h
  have hsPZ : sP.mem.get 0 = 0 := by rw [hsPeq]; exact hs364Z
  have hsPB0 : sP.mem.get 32 = 32 := by rw [hsPeq]; exact hs364B0
  have hsPB1 : sP.mem.get 33 = 32 := by rw [hsPeq]; exact hs364B1
  have hsPB2 : sP.mem.get 34 = 32 := by rw [hsPeq]; exact hs364B2
  have hsPB3 : sP.mem.get 35 = 32 := by rw [hsPeq]; exact hs364B3
  have hsPB4 : sP.mem.get 36 = 32 := by rw [hsPeq]; exact hs364B4
  have hsPB5 : sP.mem.get 37 = 32 := by rw [hsPeq]; exact hs364B5
  have hsPB6 : sP.mem.get 38 = 32 := by rw [hsPeq]; exact hs364B6
  have hsPI : sP.mem.get 29 = 7 := by rw [hsPeq]; exact hs364I
  have hsPP : sP.mem.get 27 = 0 := by rw [hsPeq]; exact hs364P
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 38 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sP.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha38 ha29 ha27 ha18 ha30 ha2319 ha0
    rw [hsPeq]
    exact hpres364 a ha32 ha33 ha34 ha35 ha36 ha37 ha38 ha29 ha27 ha18 ha30 ha2319 ha0
  exact ⟨hsPpc, hsPh, hsPZ, hsPB0, hsPB1, hsPB2, hsPB3, hsPB4, hsPB5, hsPB6, hsPI, hsPP, hpres⟩


/-- From `SP_LOOP` with `PAD = 1` and `IDX = 0`, and `1 ≤ ROOM`: write one
space at `BUF+0` and return to `SP_LOOP` with `IDX = 1` and `PAD = 0`. 46 steps. -/
theorem pad_1_spaces_idx0 {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 0)
    (hP : s.mem.get 27 = 1)
    (hRlo : 1 ≤ (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sP := runN s 46
    sP.pc = 1011 ∧
    sP.halted = false ∧
    sP.mem.get 0 = 0 ∧
    sP.mem.get 32 = 32 ∧
    sP.mem.get 29 = 1 ∧
    sP.mem.get 27 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 →
      sP.mem.get a = s.mem.get a) := by
  intro sP
  have hPlo : 0 < (s.mem.get 27).toNat := by simp [hP]
  have hPhi : (s.mem.get 27).toNat < 32768 := by simp [hP]
  have hRlo0 : 0 < (s.mem.get 28).toNat := by omega
  have hw := pad_one_iter_idx0 (s := s) hpc hh hZ hONE hK32 hI hPlo hPhi hRlo0 hRhi hcode
  have hsPpc : sP.pc = 1011 := hw.1
  have hsPh : sP.halted = false := hw.2.1
  have hsPZ : sP.mem.get 0 = 0 := hw.2.2.1
  have hsPB : sP.mem.get 32 = 32 := hw.2.2.2.1
  have hsPI : sP.mem.get 29 = 1 := hw.2.2.2.2.1
  have hsPP : sP.mem.get 27 = 0 := by
    have h := hw.2.2.2.2.2.1
    rw [h, hP]
    exact (rfl : (1 : Word) - 1 = 0)
  have hpres := hw.2.2.2.2.2.2
  exact ⟨hsPpc, hsPh, hsPZ, hsPB, hsPI, hsPP, hpres⟩

/-- `PAD = 1` from `SP_LOOP` at `IDX = 0` writes 1 spaces and exits to
`AFTER_PAD`. 51 steps. -/
theorem pad_1_to_after_pad {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 0)
    (hP : s.mem.get 27 = 1)
    (hRlo : 1 ≤ (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sA := runN s 51
    sA.pc = 1077 ∧
    sA.halted = false ∧
    sA.mem.get 0 = 0 ∧
    sA.mem.get 32 = 32 ∧
    sA.mem.get 29 = 1 ∧
    sA.mem.get 27 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sA.mem.get a = s.mem.get a) := by
  intro sA
  have hp := pad_1_spaces_idx0 (s := s) hpc hh hZ hONE hK32 hI hP hRlo hRhi hcode
  let sP := runN s 46
  have hsPpc : sP.pc = 1011 := hp.1
  have hsPh : sP.halted = false := hp.2.1
  have hsPZ : sP.mem.get 0 = 0 := hp.2.2.1
  have hsPP : sP.mem.get 27 = 0 := hp.2.2.2.2.2.1
  have hpresP := hp.2.2.2.2.2.2
  have gP : ∀ k : Nat, 1011 ≤ k → k < 1026 →
      sP.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresP (UInt16.ofNat k) n32 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hx := sp_loop_pad0 (s := sP) hsPpc hsPh hsPZ hsPP gP
  have hrun : sA = runN sP 5 := runN_add_eq s 46 5 51 (by decide)
  have hprese := hx.2.2.2.2
  have hsAB0 : sA.mem.get 32 = 32 := by
    rw [hrun]; exact (hprese 32 (by decide) (by decide)).trans (hp.2.2.2.1)
  have hsApc : sA.pc = 1077 := by rw [hrun]; exact hx.1
  have hsAh : sA.halted = false := by rw [hrun]; exact hx.2.1
  have hsAZ : sA.mem.get 0 = 0 := by rw [hrun]; exact hx.2.2.1
  have hsAI : sA.mem.get 29 = 1 := by
    rw [hrun]; exact (hprese 29 (by decide) (by decide)).trans (hp.2.2.2.2.1)
  have hsAP : sA.mem.get 27 = 0 := by
    rw [hrun]; exact (hprese 27 (by decide) (by decide)).trans hsPP
  have hpres : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sA.mem.get a = s.mem.get a := by
    intro a ha32 ha29 ha27 ha18 ha30 ha2319 ha0
    rw [hrun]
    exact (hprese a ha18 ha0).trans (hpresP a ha32 ha29 ha27 ha18 ha30 ha2319 ha0)
  exact ⟨hsApc, hsAh, hsAZ, hsAB0, hsAI, hsAP, hpres⟩

/-- `PAD = 2` from `SP_LOOP` at `IDX = 0` writes 2 spaces and exits to
`AFTER_PAD`. 99 steps. -/
theorem pad_2_to_after_pad {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 0)
    (hP : s.mem.get 27 = 2)
    (hRlo : 2 ≤ (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sA := runN s 99
    sA.pc = 1077 ∧
    sA.halted = false ∧
    sA.mem.get 0 = 0 ∧
    sA.mem.get 32 = 32 ∧
    sA.mem.get 33 = 32 ∧
    sA.mem.get 29 = 2 ∧
    sA.mem.get 27 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sA.mem.get a = s.mem.get a) := by
  intro sA
  have hp := pad_2_spaces_idx0 (s := s) hpc hh hZ hONE hK32 hI hP hRlo hRhi hcode
  let sP := runN s 94
  have hsPpc : sP.pc = 1011 := hp.1
  have hsPh : sP.halted = false := hp.2.1
  have hsPZ : sP.mem.get 0 = 0 := hp.2.2.1
  have hsPP : sP.mem.get 27 = 0 := hp.2.2.2.2.2.2.1
  have hpresP := hp.2.2.2.2.2.2.2
  have gP : ∀ k : Nat, 1011 ≤ k → k < 1026 →
      sP.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresP (UInt16.ofNat k) n32 n33 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hx := sp_loop_pad0 (s := sP) hsPpc hsPh hsPZ hsPP gP
  have hrun : sA = runN sP 5 := runN_add_eq s 94 5 99 (by decide)
  have hprese := hx.2.2.2.2
  have hsAB0 : sA.mem.get 32 = 32 := by
    rw [hrun]; exact (hprese 32 (by decide) (by decide)).trans (hp.2.2.2.1)
  have hsAB1 : sA.mem.get 33 = 32 := by
    rw [hrun]; exact (hprese 33 (by decide) (by decide)).trans (hp.2.2.2.2.1)
  have hsApc : sA.pc = 1077 := by rw [hrun]; exact hx.1
  have hsAh : sA.halted = false := by rw [hrun]; exact hx.2.1
  have hsAZ : sA.mem.get 0 = 0 := by rw [hrun]; exact hx.2.2.1
  have hsAI : sA.mem.get 29 = 2 := by
    rw [hrun]; exact (hprese 29 (by decide) (by decide)).trans (hp.2.2.2.2.2.1)
  have hsAP : sA.mem.get 27 = 0 := by
    rw [hrun]; exact (hprese 27 (by decide) (by decide)).trans hsPP
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sA.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha29 ha27 ha18 ha30 ha2319 ha0
    rw [hrun]
    exact (hprese a ha18 ha0).trans (hpresP a ha32 ha33 ha29 ha27 ha18 ha30 ha2319 ha0)
  exact ⟨hsApc, hsAh, hsAZ, hsAB0, hsAB1, hsAI, hsAP, hpres⟩

/-- `PAD = 3` from `SP_LOOP` at `IDX = 0` writes 3 spaces and exits to
`AFTER_PAD`. 149 steps. -/
theorem pad_3_to_after_pad {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 0)
    (hP : s.mem.get 27 = 3)
    (hRlo : 3 ≤ (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sA := runN s 149
    sA.pc = 1077 ∧
    sA.halted = false ∧
    sA.mem.get 0 = 0 ∧
    sA.mem.get 32 = 32 ∧
    sA.mem.get 33 = 32 ∧
    sA.mem.get 34 = 32 ∧
    sA.mem.get 29 = 3 ∧
    sA.mem.get 27 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sA.mem.get a = s.mem.get a) := by
  intro sA
  have hp := pad_3_spaces_idx0 (s := s) hpc hh hZ hONE hK32 hI hP hRlo hRhi hcode
  let sP := runN s 144
  have hsPpc : sP.pc = 1011 := hp.1
  have hsPh : sP.halted = false := hp.2.1
  have hsPZ : sP.mem.get 0 = 0 := hp.2.2.1
  have hsPP : sP.mem.get 27 = 0 := hp.2.2.2.2.2.2.2.1
  have hpresP := hp.2.2.2.2.2.2.2.2
  have gP : ∀ k : Nat, 1011 ≤ k → k < 1026 →
      sP.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresP (UInt16.ofNat k) n32 n33 n34 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hx := sp_loop_pad0 (s := sP) hsPpc hsPh hsPZ hsPP gP
  have hrun : sA = runN sP 5 := runN_add_eq s 144 5 149 (by decide)
  have hprese := hx.2.2.2.2
  have hsAB0 : sA.mem.get 32 = 32 := by
    rw [hrun]; exact (hprese 32 (by decide) (by decide)).trans (hp.2.2.2.1)
  have hsAB1 : sA.mem.get 33 = 32 := by
    rw [hrun]; exact (hprese 33 (by decide) (by decide)).trans (hp.2.2.2.2.1)
  have hsAB2 : sA.mem.get 34 = 32 := by
    rw [hrun]; exact (hprese 34 (by decide) (by decide)).trans (hp.2.2.2.2.2.1)
  have hsApc : sA.pc = 1077 := by rw [hrun]; exact hx.1
  have hsAh : sA.halted = false := by rw [hrun]; exact hx.2.1
  have hsAZ : sA.mem.get 0 = 0 := by rw [hrun]; exact hx.2.2.1
  have hsAI : sA.mem.get 29 = 3 := by
    rw [hrun]; exact (hprese 29 (by decide) (by decide)).trans (hp.2.2.2.2.2.2.1)
  have hsAP : sA.mem.get 27 = 0 := by
    rw [hrun]; exact (hprese 27 (by decide) (by decide)).trans hsPP
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sA.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha29 ha27 ha18 ha30 ha2319 ha0
    rw [hrun]
    exact (hprese a ha18 ha0).trans (hpresP a ha32 ha33 ha34 ha29 ha27 ha18 ha30 ha2319 ha0)
  exact ⟨hsApc, hsAh, hsAZ, hsAB0, hsAB1, hsAB2, hsAI, hsAP, hpres⟩

/-- `PAD = 4` from `SP_LOOP` at `IDX = 0` writes 4 spaces and exits to
`AFTER_PAD`. 201 steps. -/
theorem pad_4_to_after_pad {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 0)
    (hP : s.mem.get 27 = 4)
    (hRlo : 4 ≤ (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sA := runN s 201
    sA.pc = 1077 ∧
    sA.halted = false ∧
    sA.mem.get 0 = 0 ∧
    sA.mem.get 32 = 32 ∧
    sA.mem.get 33 = 32 ∧
    sA.mem.get 34 = 32 ∧
    sA.mem.get 35 = 32 ∧
    sA.mem.get 29 = 4 ∧
    sA.mem.get 27 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sA.mem.get a = s.mem.get a) := by
  intro sA
  have hp := pad_4_spaces_idx0 (s := s) hpc hh hZ hONE hK32 hI hP hRlo hRhi hcode
  let sP := runN s 196
  have hsPpc : sP.pc = 1011 := hp.1
  have hsPh : sP.halted = false := hp.2.1
  have hsPZ : sP.mem.get 0 = 0 := hp.2.2.1
  have hsPP : sP.mem.get 27 = 0 := hp.2.2.2.2.2.2.2.2.1
  have hpresP := hp.2.2.2.2.2.2.2.2.2
  have gP : ∀ k : Nat, 1011 ≤ k → k < 1026 →
      sP.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresP (UInt16.ofNat k) n32 n33 n34 n35 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hx := sp_loop_pad0 (s := sP) hsPpc hsPh hsPZ hsPP gP
  have hrun : sA = runN sP 5 := runN_add_eq s 196 5 201 (by decide)
  have hprese := hx.2.2.2.2
  have hsAB0 : sA.mem.get 32 = 32 := by
    rw [hrun]; exact (hprese 32 (by decide) (by decide)).trans (hp.2.2.2.1)
  have hsAB1 : sA.mem.get 33 = 32 := by
    rw [hrun]; exact (hprese 33 (by decide) (by decide)).trans (hp.2.2.2.2.1)
  have hsAB2 : sA.mem.get 34 = 32 := by
    rw [hrun]; exact (hprese 34 (by decide) (by decide)).trans (hp.2.2.2.2.2.1)
  have hsAB3 : sA.mem.get 35 = 32 := by
    rw [hrun]; exact (hprese 35 (by decide) (by decide)).trans (hp.2.2.2.2.2.2.1)
  have hsApc : sA.pc = 1077 := by rw [hrun]; exact hx.1
  have hsAh : sA.halted = false := by rw [hrun]; exact hx.2.1
  have hsAZ : sA.mem.get 0 = 0 := by rw [hrun]; exact hx.2.2.1
  have hsAI : sA.mem.get 29 = 4 := by
    rw [hrun]; exact (hprese 29 (by decide) (by decide)).trans (hp.2.2.2.2.2.2.2.1)
  have hsAP : sA.mem.get 27 = 0 := by
    rw [hrun]; exact (hprese 27 (by decide) (by decide)).trans hsPP
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sA.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha29 ha27 ha18 ha30 ha2319 ha0
    rw [hrun]
    exact (hprese a ha18 ha0).trans (hpresP a ha32 ha33 ha34 ha35 ha29 ha27 ha18 ha30 ha2319 ha0)
  exact ⟨hsApc, hsAh, hsAZ, hsAB0, hsAB1, hsAB2, hsAB3, hsAI, hsAP, hpres⟩

/-- `PAD = 5` from `SP_LOOP` at `IDX = 0` writes 5 spaces and exits to
`AFTER_PAD`. 255 steps. -/
theorem pad_5_to_after_pad {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 0)
    (hP : s.mem.get 27 = 5)
    (hRlo : 5 ≤ (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sA := runN s 255
    sA.pc = 1077 ∧
    sA.halted = false ∧
    sA.mem.get 0 = 0 ∧
    sA.mem.get 32 = 32 ∧
    sA.mem.get 33 = 32 ∧
    sA.mem.get 34 = 32 ∧
    sA.mem.get 35 = 32 ∧
    sA.mem.get 36 = 32 ∧
    sA.mem.get 29 = 5 ∧
    sA.mem.get 27 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sA.mem.get a = s.mem.get a) := by
  intro sA
  have hp := pad_5_spaces_idx0 (s := s) hpc hh hZ hONE hK32 hI hP hRlo hRhi hcode
  let sP := runN s 250
  have hsPpc : sP.pc = 1011 := hp.1
  have hsPh : sP.halted = false := hp.2.1
  have hsPZ : sP.mem.get 0 = 0 := hp.2.2.1
  have hsPP : sP.mem.get 27 = 0 := hp.2.2.2.2.2.2.2.2.2.1
  have hpresP := hp.2.2.2.2.2.2.2.2.2.2
  have gP : ∀ k : Nat, 1011 ≤ k → k < 1026 →
      sP.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresP (UInt16.ofNat k) n32 n33 n34 n35 n36 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hx := sp_loop_pad0 (s := sP) hsPpc hsPh hsPZ hsPP gP
  have hrun : sA = runN sP 5 := runN_add_eq s 250 5 255 (by decide)
  have hprese := hx.2.2.2.2
  have hsAB0 : sA.mem.get 32 = 32 := by
    rw [hrun]; exact (hprese 32 (by decide) (by decide)).trans (hp.2.2.2.1)
  have hsAB1 : sA.mem.get 33 = 32 := by
    rw [hrun]; exact (hprese 33 (by decide) (by decide)).trans (hp.2.2.2.2.1)
  have hsAB2 : sA.mem.get 34 = 32 := by
    rw [hrun]; exact (hprese 34 (by decide) (by decide)).trans (hp.2.2.2.2.2.1)
  have hsAB3 : sA.mem.get 35 = 32 := by
    rw [hrun]; exact (hprese 35 (by decide) (by decide)).trans (hp.2.2.2.2.2.2.1)
  have hsAB4 : sA.mem.get 36 = 32 := by
    rw [hrun]; exact (hprese 36 (by decide) (by decide)).trans (hp.2.2.2.2.2.2.2.1)
  have hsApc : sA.pc = 1077 := by rw [hrun]; exact hx.1
  have hsAh : sA.halted = false := by rw [hrun]; exact hx.2.1
  have hsAZ : sA.mem.get 0 = 0 := by rw [hrun]; exact hx.2.2.1
  have hsAI : sA.mem.get 29 = 5 := by
    rw [hrun]; exact (hprese 29 (by decide) (by decide)).trans (hp.2.2.2.2.2.2.2.2.1)
  have hsAP : sA.mem.get 27 = 0 := by
    rw [hrun]; exact (hprese 27 (by decide) (by decide)).trans hsPP
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sA.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha29 ha27 ha18 ha30 ha2319 ha0
    rw [hrun]
    exact (hprese a ha18 ha0).trans (hpresP a ha32 ha33 ha34 ha35 ha36 ha29 ha27 ha18 ha30 ha2319 ha0)
  exact ⟨hsApc, hsAh, hsAZ, hsAB0, hsAB1, hsAB2, hsAB3, hsAB4, hsAI, hsAP, hpres⟩

/-- `PAD = 6` from `SP_LOOP` at `IDX = 0` writes 6 spaces and exits to
`AFTER_PAD`. 311 steps. -/
theorem pad_6_to_after_pad {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 0)
    (hP : s.mem.get 27 = 6)
    (hRlo : 6 ≤ (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sA := runN s 311
    sA.pc = 1077 ∧
    sA.halted = false ∧
    sA.mem.get 0 = 0 ∧
    sA.mem.get 32 = 32 ∧
    sA.mem.get 33 = 32 ∧
    sA.mem.get 34 = 32 ∧
    sA.mem.get 35 = 32 ∧
    sA.mem.get 36 = 32 ∧
    sA.mem.get 37 = 32 ∧
    sA.mem.get 29 = 6 ∧
    sA.mem.get 27 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sA.mem.get a = s.mem.get a) := by
  intro sA
  have hp := pad_6_spaces_idx0 (s := s) hpc hh hZ hONE hK32 hI hP hRlo hRhi hcode
  let sP := runN s 306
  have hsPpc : sP.pc = 1011 := hp.1
  have hsPh : sP.halted = false := hp.2.1
  have hsPZ : sP.mem.get 0 = 0 := hp.2.2.1
  have hsPP : sP.mem.get 27 = 0 := hp.2.2.2.2.2.2.2.2.2.2.1
  have hpresP := hp.2.2.2.2.2.2.2.2.2.2.2
  have gP : ∀ k : Nat, 1011 ≤ k → k < 1026 →
      sP.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n37 : UInt16.ofNat k ≠ (37 : Word) := by
      have : (37 : Word) = UInt16.ofNat 37 := rfl
      rw [this]; exact ofNat_ne k 37 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresP (UInt16.ofNat k) n32 n33 n34 n35 n36 n37 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hx := sp_loop_pad0 (s := sP) hsPpc hsPh hsPZ hsPP gP
  have hrun : sA = runN sP 5 := runN_add_eq s 306 5 311 (by decide)
  have hprese := hx.2.2.2.2
  have hsAB0 : sA.mem.get 32 = 32 := by
    rw [hrun]; exact (hprese 32 (by decide) (by decide)).trans (hp.2.2.2.1)
  have hsAB1 : sA.mem.get 33 = 32 := by
    rw [hrun]; exact (hprese 33 (by decide) (by decide)).trans (hp.2.2.2.2.1)
  have hsAB2 : sA.mem.get 34 = 32 := by
    rw [hrun]; exact (hprese 34 (by decide) (by decide)).trans (hp.2.2.2.2.2.1)
  have hsAB3 : sA.mem.get 35 = 32 := by
    rw [hrun]; exact (hprese 35 (by decide) (by decide)).trans (hp.2.2.2.2.2.2.1)
  have hsAB4 : sA.mem.get 36 = 32 := by
    rw [hrun]; exact (hprese 36 (by decide) (by decide)).trans (hp.2.2.2.2.2.2.2.1)
  have hsAB5 : sA.mem.get 37 = 32 := by
    rw [hrun]; exact (hprese 37 (by decide) (by decide)).trans (hp.2.2.2.2.2.2.2.2.1)
  have hsApc : sA.pc = 1077 := by rw [hrun]; exact hx.1
  have hsAh : sA.halted = false := by rw [hrun]; exact hx.2.1
  have hsAZ : sA.mem.get 0 = 0 := by rw [hrun]; exact hx.2.2.1
  have hsAI : sA.mem.get 29 = 6 := by
    rw [hrun]; exact (hprese 29 (by decide) (by decide)).trans (hp.2.2.2.2.2.2.2.2.2.1)
  have hsAP : sA.mem.get 27 = 0 := by
    rw [hrun]; exact (hprese 27 (by decide) (by decide)).trans hsPP
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sA.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha29 ha27 ha18 ha30 ha2319 ha0
    rw [hrun]
    exact (hprese a ha18 ha0).trans (hpresP a ha32 ha33 ha34 ha35 ha36 ha37 ha29 ha27 ha18 ha30 ha2319 ha0)
  exact ⟨hsApc, hsAh, hsAZ, hsAB0, hsAB1, hsAB2, hsAB3, hsAB4, hsAB5, hsAI, hsAP, hpres⟩

/-- `PAD = 7` from `SP_LOOP` at `IDX = 0` writes 7 spaces and exits to
`AFTER_PAD`. 369 steps. -/
theorem pad_7_to_after_pad {s : Machine}
    (hpc : s.pc = 1011)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK32 : s.mem.get 10 = 32)
    (hI : s.mem.get 29 = 0)
    (hP : s.mem.get 27 = 7)
    (hRlo : 7 ≤ (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1011 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sA := runN s 369
    sA.pc = 1077 ∧
    sA.halted = false ∧
    sA.mem.get 0 = 0 ∧
    sA.mem.get 32 = 32 ∧
    sA.mem.get 33 = 32 ∧
    sA.mem.get 34 = 32 ∧
    sA.mem.get 35 = 32 ∧
    sA.mem.get 36 = 32 ∧
    sA.mem.get 37 = 32 ∧
    sA.mem.get 38 = 32 ∧
    sA.mem.get 29 = 7 ∧
    sA.mem.get 27 = 0 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 38 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sA.mem.get a = s.mem.get a) := by
  intro sA
  have hp := pad_7_spaces_idx0 (s := s) hpc hh hZ hONE hK32 hI hP hRlo hRhi hcode
  let sP := runN s 364
  have hsPpc : sP.pc = 1011 := hp.1
  have hsPh : sP.halted = false := hp.2.1
  have hsPZ : sP.mem.get 0 = 0 := hp.2.2.1
  have hsPP : sP.mem.get 27 = 0 := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hpresP := hp.2.2.2.2.2.2.2.2.2.2.2.2
  have gP : ∀ k : Nat, 1011 ≤ k → k < 1026 →
      sP.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
    have n35 : UInt16.ofNat k ≠ (35 : Word) := by
      have : (35 : Word) = UInt16.ofNat 35 := rfl
      rw [this]; exact ofNat_ne k 35 (by omega) (by decide) (by omega)
    have n36 : UInt16.ofNat k ≠ (36 : Word) := by
      have : (36 : Word) = UInt16.ofNat 36 := rfl
      rw [this]; exact ofNat_ne k 36 (by omega) (by decide) (by omega)
    have n37 : UInt16.ofNat k ≠ (37 : Word) := by
      have : (37 : Word) = UInt16.ofNat 37 := rfl
      rw [this]; exact ofNat_ne k 37 (by omega) (by decide) (by omega)
    have n38 : UInt16.ofNat k ≠ (38 : Word) := by
      have : (38 : Word) = UInt16.ofNat 38 := rfl
      rw [this]; exact ofNat_ne k 38 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresP (UInt16.ofNat k) n32 n33 n34 n35 n36 n37 n38 n29 n27 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hx := sp_loop_pad0 (s := sP) hsPpc hsPh hsPZ hsPP gP
  have hrun : sA = runN sP 5 := runN_add_eq s 364 5 369 (by decide)
  have hprese := hx.2.2.2.2
  have hsAB0 : sA.mem.get 32 = 32 := by
    rw [hrun]; exact (hprese 32 (by decide) (by decide)).trans (hp.2.2.2.1)
  have hsAB1 : sA.mem.get 33 = 32 := by
    rw [hrun]; exact (hprese 33 (by decide) (by decide)).trans (hp.2.2.2.2.1)
  have hsAB2 : sA.mem.get 34 = 32 := by
    rw [hrun]; exact (hprese 34 (by decide) (by decide)).trans (hp.2.2.2.2.2.1)
  have hsAB3 : sA.mem.get 35 = 32 := by
    rw [hrun]; exact (hprese 35 (by decide) (by decide)).trans (hp.2.2.2.2.2.2.1)
  have hsAB4 : sA.mem.get 36 = 32 := by
    rw [hrun]; exact (hprese 36 (by decide) (by decide)).trans (hp.2.2.2.2.2.2.2.1)
  have hsAB5 : sA.mem.get 37 = 32 := by
    rw [hrun]; exact (hprese 37 (by decide) (by decide)).trans (hp.2.2.2.2.2.2.2.2.1)
  have hsAB6 : sA.mem.get 38 = 32 := by
    rw [hrun]; exact (hprese 38 (by decide) (by decide)).trans (hp.2.2.2.2.2.2.2.2.2.1)
  have hsApc : sA.pc = 1077 := by rw [hrun]; exact hx.1
  have hsAh : sA.halted = false := by rw [hrun]; exact hx.2.1
  have hsAZ : sA.mem.get 0 = 0 := by rw [hrun]; exact hx.2.2.1
  have hsAI : sA.mem.get 29 = 7 := by
    rw [hrun]; exact (hprese 29 (by decide) (by decide)).trans (hp.2.2.2.2.2.2.2.2.2.2.1)
  have hsAP : sA.mem.get 27 = 0 := by
    rw [hrun]; exact (hprese 27 (by decide) (by decide)).trans hsPP
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 38 → a ≠ 29 → a ≠ 27 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 0 → sA.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha38 ha29 ha27 ha18 ha30 ha2319 ha0
    rw [hrun]
    exact (hprese a ha18 ha0).trans (hpresP a ha32 ha33 ha34 ha35 ha36 ha37 ha38 ha29 ha27 ha18 ha30 ha2319 ha0)
  exact ⟨hsApc, hsAh, hsAZ, hsAB0, hsAB1, hsAB2, hsAB3, hsAB4, hsAB5, hsAB6, hsAI, hsAP, hpres⟩

end IntFmt
