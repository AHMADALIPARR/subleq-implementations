/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Signed `HAVE_DIG` (`SIGN ≠ 0`, `WIDTH = 0`) through the minus path and
halt, plus the matching `P3_DONE` compositions for `NDIG ∈ {1..4}`.
Block lemmas, not end-to-end correctness.
-/

import IntFmt.HaveDigHalt
import IntFmt.Ascii
import IntFmt.Ndig

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000


/-- From `HAVE_DIG` with `SIGN ≠ 0`, `WIDTH = 0`, and `CAP > 0`: set
`RAW = LEN = NDIG + 1`, `PAD = 0`, `ROOM = CAP - 1`, `IDX = 0`, and
reach `AFTER_PAD` in 38 steps. -/
theorem have_dig_to_after_pad_signed {s : Machine}
    (hpc : s.pc = 867)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hW : s.mem.get 14 = 0)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 867 ≤ k → k < 1026 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s38 := runN s 38
    s38.pc = 1077 ∧
    s38.halted = false ∧
    s38.mem.get 0 = 0 ∧
    s38.mem.get 26 = s.mem.get 25 + 1 ∧
    s38.mem.get 16 = s.mem.get 25 + 1 ∧
    s38.mem.get 27 = 0 ∧
    s38.mem.get 28 = s.mem.get 13 - 1 ∧
    s38.mem.get 29 = 0 ∧
    (∀ a, a ≠ 26 → a ≠ 18 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 0 →
      s38.mem.get a = s.mem.get a) := by
  intro s38
  have hd := have_dig_sign_nz (s := s) hpc hh hZ hONE hSlo hShi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s12 := runN s 12
  have hs12pc : s12.pc = 903 := hd.1
  have hs12h : s12.halted = false := hd.2.1
  have hs12Z : s12.mem.get 0 = 0 := hd.2.2.1
  have hs12R : s12.mem.get 26 = s.mem.get 25 + 1 := hd.2.2.2.1
  have hpres12 := hd.2.2.2.2
  have hW12 : s12.mem.get 14 = 0 := (hpres12 14 (by decide) (by decide) (by decide)).trans hW
  have hONE12 : s12.mem.get 3 = 1 := (hpres12 3 (by decide) (by decide) (by decide)).trans hONE
  have hC12 : s12.mem.get 13 = s.mem.get 13 := hpres12 13 (by decide) (by decide) (by decide)
  have g12 : ∀ k : Nat, 903 ≤ k → k < 978 →
      s12.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n26 : UInt16.ofNat k ≠ (26 : Word) := by
      have : (26 : Word) = UInt16.ofNat 26 := rfl
      rw [this]; exact ofNat_ne k 26 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres12 (UInt16.ofNat k) n26 n18 n0).trans (hcode k (by omega) (by omega))
  have hp := pad_len_width0 (s := s12) hs12pc hs12h hs12Z hW12 g12
  have hrun22 : runN s 22 = runN s12 10 := runN_add_eq s 12 10 22 (by decide)
  let s22 := runN s 22
  have hs22pc : s22.pc = 978 := by have : s22 = runN s12 10 := hrun22; rw [this]; exact hp.1
  have hs22h : s22.halted = false := by have : s22 = runN s12 10 := hrun22; rw [this]; exact hp.2.1
  have hs22Z : s22.mem.get 0 = 0 := by have : s22 = runN s12 10 := hrun22; rw [this]; exact hp.2.2.1
  have hs22P : s22.mem.get 27 = 0 := by have : s22 = runN s12 10 := hrun22; rw [this]; exact hp.2.2.2.1
  have hs22L : s22.mem.get 16 = s.mem.get 25 + 1 := by
    have : s22 = runN s12 10 := hrun22
    rw [this]; exact hp.2.2.2.2.1.trans hs12R
  have hs22R : s22.mem.get 26 = s.mem.get 25 + 1 := by
    have : s22 = runN s12 10 := hrun22
    rw [this]; exact (hp.2.2.2.2.2 26 (by decide) (by decide) (by decide) (by decide)).trans hs12R
  have hONE22 : s22.mem.get 3 = 1 := by
    have : s22 = runN s12 10 := hrun22
    rw [this]
    exact (hp.2.2.2.2.2 3 (by decide) (by decide) (by decide) (by decide)).trans hONE12
  have hC22 : s22.mem.get 13 = s.mem.get 13 := by
    have : s22 = runN s12 10 := hrun22
    rw [this]
    exact (hp.2.2.2.2.2 13 (by decide) (by decide) (by decide) (by decide)).trans hC12
  have hClo22 : 0 < (s22.mem.get 13).toNat := by
    have : s22.mem.get 13 = s.mem.get 13 := hC22
    rw [this]; exact hClo
  have hChi22 : (s22.mem.get 13).toNat < 32768 := by
    have : s22.mem.get 13 = s.mem.get 13 := hC22
    rw [this]; exact hChi
  have hpres22 : ∀ a, a ≠ 26 → a ≠ 18 → a ≠ 16 → a ≠ 27 → a ≠ 0 →
      s22.mem.get a = s.mem.get a := by
    intro a ha26 ha18 ha16 ha27 ha0
    have : s22 = runN s12 10 := hrun22
    rw [this]
    exact (hp.2.2.2.2.2 a ha27 ha18 ha16 ha0).trans (hpres12 a ha26 ha18 ha0)
  have g22 : ∀ k : Nat, 978 ≤ k → k < 1011 →
      s22.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n26 : UInt16.ofNat k ≠ (26 : Word) := by
      have : (26 : Word) = UInt16.ofNat 26 := rfl
      rw [this]; exact ofNat_ne k 26 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n16 : UInt16.ofNat k ≠ (16 : Word) := by
      have : (16 : Word) = UInt16.ofNat 16 := rfl
      rw [this]; exact ofNat_ne k 16 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres22 (UInt16.ofNat k) n26 n18 n16 n27 n0).trans (hcode k (by omega) (by omega))
  have hc := cap_nz_to_sploop (s := s22) hs22pc hs22h hs22Z hONE22 hClo22 hChi22 g22
  have hrun33 : runN s 33 = runN s22 11 := runN_add_eq s 22 11 33 (by decide)
  let s33 := runN s 33
  have hs33pc : s33.pc = 1011 := by have : s33 = runN s22 11 := hrun33; rw [this]; exact hc.1
  have hs33h : s33.halted = false := by have : s33 = runN s22 11 := hrun33; rw [this]; exact hc.2.1
  have hs33Z : s33.mem.get 0 = 0 := by have : s33 = runN s22 11 := hrun33; rw [this]; exact hc.2.2.1
  have hs33Room : s33.mem.get 28 = s.mem.get 13 - 1 := by
    have : s33 = runN s22 11 := hrun33
    have h1 : (runN s22 11).mem.get 28 = s22.mem.get 13 - 1 := hc.2.2.2.1
    have h2 : s22.mem.get 13 = s.mem.get 13 := hC22
    rw [this, h1, h2]
  have hs33I : s33.mem.get 29 = 0 := by have : s33 = runN s22 11 := hrun33; rw [this]; exact hc.2.2.2.2.1
  have hs33P : s33.mem.get 27 = 0 := by
    have : s33 = runN s22 11 := hrun33
    rw [this]; exact (hc.2.2.2.2.2 27 (by decide) (by decide) (by decide) (by decide)).trans hs22P
  have hs33L : s33.mem.get 16 = s.mem.get 25 + 1 := by
    have : s33 = runN s22 11 := hrun33
    rw [this]; exact (hc.2.2.2.2.2 16 (by decide) (by decide) (by decide) (by decide)).trans hs22L
  have hs33Raw : s33.mem.get 26 = s.mem.get 25 + 1 := by
    have : s33 = runN s22 11 := hrun33
    rw [this]; exact (hc.2.2.2.2.2 26 (by decide) (by decide) (by decide) (by decide)).trans hs22R
  have hpres33 : ∀ a, a ≠ 26 → a ≠ 18 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 0 →
      s33.mem.get a = s.mem.get a := by
    intro a ha26 ha18 ha16 ha27 ha28 ha29 ha0
    have : s33 = runN s22 11 := hrun33
    rw [this]
    exact (hc.2.2.2.2.2 a ha18 ha28 ha29 ha0).trans (hpres22 a ha26 ha18 ha16 ha27 ha0)
  have g33 : ∀ k : Nat, 1011 ≤ k → k < 1026 →
      s33.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n26 : UInt16.ofNat k ≠ (26 : Word) := by
      have : (26 : Word) = UInt16.ofNat 26 := rfl
      rw [this]; exact ofNat_ne k 26 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n16 : UInt16.ofNat k ≠ (16 : Word) := by
      have : (16 : Word) = UInt16.ofNat 16 := rfl
      rw [this]; exact ofNat_ne k 16 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n28 : UInt16.ofNat k ≠ (28 : Word) := by
      have : (28 : Word) = UInt16.ofNat 28 := rfl
      rw [this]; exact ofNat_ne k 28 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres33 (UInt16.ofNat k) n26 n18 n16 n27 n28 n29 n0).trans
      (hcode k (by omega) (by omega))
  have hs := sp_loop_pad0 (s := s33) hs33pc hs33h hs33Z hs33P g33
  have hrun : s38 = runN s33 5 := runN_add_eq s 33 5 38 (by decide)
  have hs38pc : s38.pc = 1077 := by rw [hrun]; exact hs.1
  have hs38h : s38.halted = false := by rw [hrun]; exact hs.2.1
  have hs38Z : s38.mem.get 0 = 0 := by rw [hrun]; exact hs.2.2.1
  have hs38Raw : s38.mem.get 26 = s.mem.get 25 + 1 := by
    rw [hrun]; exact (hs.2.2.2.2 26 (by decide) (by decide)).trans hs33Raw
  have hs38L : s38.mem.get 16 = s.mem.get 25 + 1 := by
    rw [hrun]; exact (hs.2.2.2.2 16 (by decide) (by decide)).trans hs33L
  have hs38P : s38.mem.get 27 = 0 := by
    rw [hrun]; exact (hs.2.2.2.2 27 (by decide) (by decide)).trans hs33P
  have hs38Room : s38.mem.get 28 = s.mem.get 13 - 1 := by
    rw [hrun]; exact (hs.2.2.2.2 28 (by decide) (by decide)).trans hs33Room
  have hs38I : s38.mem.get 29 = 0 := by
    rw [hrun]; exact (hs.2.2.2.2 29 (by decide) (by decide)).trans hs33I
  have hpres : ∀ a, a ≠ 26 → a ≠ 18 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 0 →
      s38.mem.get a = s.mem.get a := by
    intro a ha26 ha18 ha16 ha27 ha28 ha29 ha0
    rw [hrun]
    exact (hs.2.2.2.2 a ha18 ha0).trans (hpres33 a ha26 ha18 ha16 ha27 ha28 ha29 ha0)
  exact ⟨hs38pc, hs38h, hs38Z, hs38Raw, hs38L, hs38P, hs38Room, hs38I, hpres⟩

/-- From `HAVE_DIG` with `SIGN ≠ 0`, `WIDTH = 0`, `NDIG = 1`, and
`2 < CAP`: write a leading minus, emit the digits, NUL-terminate,
and halt. 341 steps. -/
theorem have_dig_signed_ndig1_done {s : Machine}
    (hpc : s.pc = 867)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hK45 : s.mem.get 9 = 45)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hW : s.mem.get 14 = 0)
    (hN : s.mem.get 25 = 1)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (2 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 867 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 341
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
        sD.mem.get 32 = 45 ∧
    sD.mem.get 33 = s.mem.get 24 ∧
    sD.mem.get 34 = 0 ∧
    sD.mem.get 29 = 2 ∧
    sD.mem.get 16 = 2 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hp := have_dig_to_after_pad_signed (s := s) hpc hh hZ hONE hSlo hShi hW hClo hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let sP := runN s 38
  have hsPpc : sP.pc = 1077 := hp.1
  have hsPh : sP.halted = false := hp.2.1
  have hsPZ : sP.mem.get 0 = 0 := hp.2.2.1
  have hpresP := hp.2.2.2.2.2.2.2.2
  have hONE_P : sP.mem.get 3 = 1 := (hpresP 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5_P : sP.mem.get 2322 = 5 := (hpresP 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hK45_P : sP.mem.get 9 = 45 := (hpresP 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK45
  have hN_P : sP.mem.get 25 = 1 := (hpresP 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN
  have hI_P : sP.mem.get 29 = 0 := hp.2.2.2.2.2.2.2.1
  have hL_P : sP.mem.get 16 = 2 := by
    have : sP.mem.get 16 = s.mem.get 25 + 1 := hp.2.2.2.2.1
    rw [this, hN]
    exact (rfl : (1 : Word) + 1 = 2)
  have hSlo_P : 0 < (sP.mem.get 19).toNat := by
    have : sP.mem.get 19 = s.mem.get 19 := hpresP 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hSlo
  have hShi_P : (sP.mem.get 19).toNat < 32768 := by
    have : sP.mem.get 19 = s.mem.get 19 := hpresP 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hShi
  have hC_P : sP.mem.get 13 = s.mem.get 13 := hpresP 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h1le : (1 : Word).toNat ≤ (s.mem.get 13).toNat := by
    have : (1 : Word).toNat = 1 := rfl
    omega
  have hroom : (sP.mem.get 28).toNat = (s.mem.get 13).toNat - 1 := by
    have hR : sP.mem.get 28 = s.mem.get 13 - 1 := hp.2.2.2.2.2.2.1
    have hs := word_sub_ge (s.mem.get 13) 1 h1le
    exact hR ▸ hs
  have hRlo0 : 0 < (sP.mem.get 28).toNat := by rw [hroom]; omega
  have hRlo : 1 < (sP.mem.get 28).toNat := by rw [hroom]; omega
  have hRhi : (sP.mem.get 28).toNat < 32768 := by rw [hroom]; omega
  have hLlt_P : (2 : Nat) < (sP.mem.get 13).toNat := by rw [hC_P]; exact hLlt
  have hChi_P : (sP.mem.get 13).toNat < 32768 := by rw [hC_P]; exact hChi
  have gP : ∀ k : Nat, 1077 ≤ k → k < 2319 →
      sP.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n26 : UInt16.ofNat k ≠ (26 : Word) := by
      have : (26 : Word) = UInt16.ofNat 26 := rfl
      rw [this]; exact ofNat_ne k 26 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n16 : UInt16.ofNat k ≠ (16 : Word) := by
      have : (16 : Word) = UInt16.ofNat 16 := rfl
      rw [this]; exact ofNat_ne k 16 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n28 : UInt16.ofNat k ≠ (28 : Word) := by
      have : (28 : Word) = UInt16.ofNat 28 := rfl
      rw [this]; exact ofNat_ne k 28 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresP (UInt16.ofNat k) n26 n18 n16 n27 n28 n29 n0).trans
      (hcode k (by omega) (by omega))
  have hm := after_pad_minus_ndig1_done (s := sP) hsPpc hsPh hsPZ hONE_P hK5_P hK45_P
    hN_P hI_P hL_P hSlo_P hShi_P hRlo0 hRlo hRhi hLlt_P hChi_P gP
  have hrun : sD = runN sP 303 := runN_add_eq s 38 303 341 (by decide)
  have hsD32 : sD.mem.get 32 = 45 := by rw [hrun]; exact hm.2.2.2.1
  have hsD33 : sD.mem.get 33 = s.mem.get 24 := by
    rw [hrun]
    have h1 : sP.mem.get 24 = s.mem.get 24 := hpresP 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact (hm.2.2.2.2.1).trans h1
  have hsDNUL : sD.mem.get 34 = 0 := by rw [hrun]; exact hm.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 2 := by rw [hrun]; exact hm.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 2 := by rw [hrun]; exact hm.2.2.2.2.2.2.2.1
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hm.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hm.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hm.2.2.1
  have hpresw := hm.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha26 ha16 ha27 ha28
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpresP a ha26 ha18 ha16 ha27 ha28 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsDNUL, hsDI, hsDL, hpres⟩

/-- From `HAVE_DIG` with `SIGN ≠ 0`, `WIDTH = 0`, `NDIG = 2`, and
`3 < CAP`: write a leading minus, emit the digits, NUL-terminate,
and halt. 403 steps. -/
theorem have_dig_signed_ndig2_done {s : Machine}
    (hpc : s.pc = 867)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hK45 : s.mem.get 9 = 45)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hW : s.mem.get 14 = 0)
    (hN : s.mem.get 25 = 2)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (3 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 867 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 403
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
        sD.mem.get 32 = 45 ∧
    sD.mem.get 33 = s.mem.get 23 ∧
    sD.mem.get 34 = s.mem.get 24 ∧
    sD.mem.get 35 = 0 ∧
    sD.mem.get 29 = 3 ∧
    sD.mem.get 16 = 3 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hp := have_dig_to_after_pad_signed (s := s) hpc hh hZ hONE hSlo hShi hW hClo hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let sP := runN s 38
  have hsPpc : sP.pc = 1077 := hp.1
  have hsPh : sP.halted = false := hp.2.1
  have hsPZ : sP.mem.get 0 = 0 := hp.2.2.1
  have hpresP := hp.2.2.2.2.2.2.2.2
  have hONE_P : sP.mem.get 3 = 1 := (hpresP 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5_P : sP.mem.get 2322 = 5 := (hpresP 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hK45_P : sP.mem.get 9 = 45 := (hpresP 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK45
  have hN_P : sP.mem.get 25 = 2 := (hpresP 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN
  have hI_P : sP.mem.get 29 = 0 := hp.2.2.2.2.2.2.2.1
  have hL_P : sP.mem.get 16 = 3 := by
    have : sP.mem.get 16 = s.mem.get 25 + 1 := hp.2.2.2.2.1
    rw [this, hN]
    exact (rfl : (2 : Word) + 1 = 3)
  have hSlo_P : 0 < (sP.mem.get 19).toNat := by
    have : sP.mem.get 19 = s.mem.get 19 := hpresP 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hSlo
  have hShi_P : (sP.mem.get 19).toNat < 32768 := by
    have : sP.mem.get 19 = s.mem.get 19 := hpresP 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hShi
  have hC_P : sP.mem.get 13 = s.mem.get 13 := hpresP 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h1le : (1 : Word).toNat ≤ (s.mem.get 13).toNat := by
    have : (1 : Word).toNat = 1 := rfl
    omega
  have hroom : (sP.mem.get 28).toNat = (s.mem.get 13).toNat - 1 := by
    have hR : sP.mem.get 28 = s.mem.get 13 - 1 := hp.2.2.2.2.2.2.1
    have hs := word_sub_ge (s.mem.get 13) 1 h1le
    exact hR ▸ hs
  have hRlo0 : 0 < (sP.mem.get 28).toNat := by rw [hroom]; omega
  have hRlo : 2 < (sP.mem.get 28).toNat := by rw [hroom]; omega
  have hRhi : (sP.mem.get 28).toNat < 32768 := by rw [hroom]; omega
  have hLlt_P : (3 : Nat) < (sP.mem.get 13).toNat := by rw [hC_P]; exact hLlt
  have hChi_P : (sP.mem.get 13).toNat < 32768 := by rw [hC_P]; exact hChi
  have gP : ∀ k : Nat, 1077 ≤ k → k < 2319 →
      sP.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n26 : UInt16.ofNat k ≠ (26 : Word) := by
      have : (26 : Word) = UInt16.ofNat 26 := rfl
      rw [this]; exact ofNat_ne k 26 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n16 : UInt16.ofNat k ≠ (16 : Word) := by
      have : (16 : Word) = UInt16.ofNat 16 := rfl
      rw [this]; exact ofNat_ne k 16 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n28 : UInt16.ofNat k ≠ (28 : Word) := by
      have : (28 : Word) = UInt16.ofNat 28 := rfl
      rw [this]; exact ofNat_ne k 28 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresP (UInt16.ofNat k) n26 n18 n16 n27 n28 n29 n0).trans
      (hcode k (by omega) (by omega))
  have hm := after_pad_minus_ndig2_done (s := sP) hsPpc hsPh hsPZ hONE_P hK5_P hK45_P
    hN_P hI_P hL_P hSlo_P hShi_P hRlo0 hRlo hRhi hLlt_P hChi_P gP
  have hrun : sD = runN sP 365 := runN_add_eq s 38 365 403 (by decide)
  have hsD32 : sD.mem.get 32 = 45 := by rw [hrun]; exact hm.2.2.2.1
  have hsD33 : sD.mem.get 33 = s.mem.get 23 := by
    rw [hrun]
    have h1 : sP.mem.get 23 = s.mem.get 23 := hpresP 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact (hm.2.2.2.2.1).trans h1
  have hsD34 : sD.mem.get 34 = s.mem.get 24 := by
    rw [hrun]
    have h1 : sP.mem.get 24 = s.mem.get 24 := hpresP 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact (hm.2.2.2.2.2.1).trans h1
  have hsDNUL : sD.mem.get 35 = 0 := by rw [hrun]; exact hm.2.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 3 := by rw [hrun]; exact hm.2.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 3 := by rw [hrun]; exact hm.2.2.2.2.2.2.2.2.1
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hm.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hm.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hm.2.2.1
  have hpresw := hm.2.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha26 ha16 ha27 ha28
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha35 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpresP a ha26 ha18 ha16 ha27 ha28 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsDNUL, hsDI, hsDL, hpres⟩

/-- From `HAVE_DIG` with `SIGN ≠ 0`, `WIDTH = 0`, `NDIG = 3`, and
`4 < CAP`: write a leading minus, emit the digits, NUL-terminate,
and halt. 465 steps. -/
theorem have_dig_signed_ndig3_done {s : Machine}
    (hpc : s.pc = 867)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hK45 : s.mem.get 9 = 45)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hW : s.mem.get 14 = 0)
    (hN : s.mem.get 25 = 3)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (4 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 867 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 465
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
        sD.mem.get 32 = 45 ∧
    sD.mem.get 33 = s.mem.get 22 ∧
    sD.mem.get 34 = s.mem.get 23 ∧
    sD.mem.get 35 = s.mem.get 24 ∧
    sD.mem.get 36 = 0 ∧
    sD.mem.get 29 = 4 ∧
    sD.mem.get 16 = 4 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hp := have_dig_to_after_pad_signed (s := s) hpc hh hZ hONE hSlo hShi hW hClo hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let sP := runN s 38
  have hsPpc : sP.pc = 1077 := hp.1
  have hsPh : sP.halted = false := hp.2.1
  have hsPZ : sP.mem.get 0 = 0 := hp.2.2.1
  have hpresP := hp.2.2.2.2.2.2.2.2
  have hONE_P : sP.mem.get 3 = 1 := (hpresP 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5_P : sP.mem.get 2322 = 5 := (hpresP 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hK45_P : sP.mem.get 9 = 45 := (hpresP 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK45
  have hN_P : sP.mem.get 25 = 3 := (hpresP 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN
  have hI_P : sP.mem.get 29 = 0 := hp.2.2.2.2.2.2.2.1
  have hL_P : sP.mem.get 16 = 4 := by
    have : sP.mem.get 16 = s.mem.get 25 + 1 := hp.2.2.2.2.1
    rw [this, hN]
    exact (rfl : (3 : Word) + 1 = 4)
  have hSlo_P : 0 < (sP.mem.get 19).toNat := by
    have : sP.mem.get 19 = s.mem.get 19 := hpresP 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hSlo
  have hShi_P : (sP.mem.get 19).toNat < 32768 := by
    have : sP.mem.get 19 = s.mem.get 19 := hpresP 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hShi
  have hC_P : sP.mem.get 13 = s.mem.get 13 := hpresP 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h1le : (1 : Word).toNat ≤ (s.mem.get 13).toNat := by
    have : (1 : Word).toNat = 1 := rfl
    omega
  have hroom : (sP.mem.get 28).toNat = (s.mem.get 13).toNat - 1 := by
    have hR : sP.mem.get 28 = s.mem.get 13 - 1 := hp.2.2.2.2.2.2.1
    have hs := word_sub_ge (s.mem.get 13) 1 h1le
    exact hR ▸ hs
  have hRlo0 : 0 < (sP.mem.get 28).toNat := by rw [hroom]; omega
  have hRlo : 3 < (sP.mem.get 28).toNat := by rw [hroom]; omega
  have hRhi : (sP.mem.get 28).toNat < 32768 := by rw [hroom]; omega
  have hLlt_P : (4 : Nat) < (sP.mem.get 13).toNat := by rw [hC_P]; exact hLlt
  have hChi_P : (sP.mem.get 13).toNat < 32768 := by rw [hC_P]; exact hChi
  have gP : ∀ k : Nat, 1077 ≤ k → k < 2319 →
      sP.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n26 : UInt16.ofNat k ≠ (26 : Word) := by
      have : (26 : Word) = UInt16.ofNat 26 := rfl
      rw [this]; exact ofNat_ne k 26 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n16 : UInt16.ofNat k ≠ (16 : Word) := by
      have : (16 : Word) = UInt16.ofNat 16 := rfl
      rw [this]; exact ofNat_ne k 16 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n28 : UInt16.ofNat k ≠ (28 : Word) := by
      have : (28 : Word) = UInt16.ofNat 28 := rfl
      rw [this]; exact ofNat_ne k 28 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresP (UInt16.ofNat k) n26 n18 n16 n27 n28 n29 n0).trans
      (hcode k (by omega) (by omega))
  have hm := after_pad_minus_ndig3_done (s := sP) hsPpc hsPh hsPZ hONE_P hK5_P hK45_P
    hN_P hI_P hL_P hSlo_P hShi_P hRlo0 hRlo hRhi hLlt_P hChi_P gP
  have hrun : sD = runN sP 427 := runN_add_eq s 38 427 465 (by decide)
  have hsD32 : sD.mem.get 32 = 45 := by rw [hrun]; exact hm.2.2.2.1
  have hsD33 : sD.mem.get 33 = s.mem.get 22 := by
    rw [hrun]
    have h1 : sP.mem.get 22 = s.mem.get 22 := hpresP 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact (hm.2.2.2.2.1).trans h1
  have hsD34 : sD.mem.get 34 = s.mem.get 23 := by
    rw [hrun]
    have h1 : sP.mem.get 23 = s.mem.get 23 := hpresP 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact (hm.2.2.2.2.2.1).trans h1
  have hsD35 : sD.mem.get 35 = s.mem.get 24 := by
    rw [hrun]
    have h1 : sP.mem.get 24 = s.mem.get 24 := hpresP 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact (hm.2.2.2.2.2.2.1).trans h1
  have hsDNUL : sD.mem.get 36 = 0 := by rw [hrun]; exact hm.2.2.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 4 := by rw [hrun]; exact hm.2.2.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 4 := by rw [hrun]; exact hm.2.2.2.2.2.2.2.2.2.1
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hm.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hm.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hm.2.2.1
  have hpresw := hm.2.2.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha26 ha16 ha27 ha28
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha35 ha36 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpresP a ha26 ha18 ha16 ha27 ha28 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsD35, hsDNUL, hsDI, hsDL, hpres⟩

/-- From `HAVE_DIG` with `SIGN ≠ 0`, `WIDTH = 0`, `NDIG = 4`, and
`5 < CAP`: write a leading minus, emit the digits, NUL-terminate,
and halt. 527 steps. -/
theorem have_dig_signed_ndig4_done {s : Machine}
    (hpc : s.pc = 867)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hK45 : s.mem.get 9 = 45)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hW : s.mem.get 14 = 0)
    (hN : s.mem.get 25 = 4)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (5 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 867 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 527
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
        sD.mem.get 32 = 45 ∧
    sD.mem.get 33 = s.mem.get 21 ∧
    sD.mem.get 34 = s.mem.get 22 ∧
    sD.mem.get 35 = s.mem.get 23 ∧
    sD.mem.get 36 = s.mem.get 24 ∧
    sD.mem.get 37 = 0 ∧
    sD.mem.get 29 = 5 ∧
    sD.mem.get 16 = 5 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hp := have_dig_to_after_pad_signed (s := s) hpc hh hZ hONE hSlo hShi hW hClo hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let sP := runN s 38
  have hsPpc : sP.pc = 1077 := hp.1
  have hsPh : sP.halted = false := hp.2.1
  have hsPZ : sP.mem.get 0 = 0 := hp.2.2.1
  have hpresP := hp.2.2.2.2.2.2.2.2
  have hONE_P : sP.mem.get 3 = 1 := (hpresP 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5_P : sP.mem.get 2322 = 5 := (hpresP 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hK45_P : sP.mem.get 9 = 45 := (hpresP 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK45
  have hN_P : sP.mem.get 25 = 4 := (hpresP 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN
  have hI_P : sP.mem.get 29 = 0 := hp.2.2.2.2.2.2.2.1
  have hL_P : sP.mem.get 16 = 5 := by
    have : sP.mem.get 16 = s.mem.get 25 + 1 := hp.2.2.2.2.1
    rw [this, hN]
    exact (rfl : (4 : Word) + 1 = 5)
  have hSlo_P : 0 < (sP.mem.get 19).toNat := by
    have : sP.mem.get 19 = s.mem.get 19 := hpresP 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hSlo
  have hShi_P : (sP.mem.get 19).toNat < 32768 := by
    have : sP.mem.get 19 = s.mem.get 19 := hpresP 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hShi
  have hC_P : sP.mem.get 13 = s.mem.get 13 := hpresP 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h1le : (1 : Word).toNat ≤ (s.mem.get 13).toNat := by
    have : (1 : Word).toNat = 1 := rfl
    omega
  have hroom : (sP.mem.get 28).toNat = (s.mem.get 13).toNat - 1 := by
    have hR : sP.mem.get 28 = s.mem.get 13 - 1 := hp.2.2.2.2.2.2.1
    have hs := word_sub_ge (s.mem.get 13) 1 h1le
    exact hR ▸ hs
  have hRlo0 : 0 < (sP.mem.get 28).toNat := by rw [hroom]; omega
  have hRlo : 4 < (sP.mem.get 28).toNat := by rw [hroom]; omega
  have hRhi : (sP.mem.get 28).toNat < 32768 := by rw [hroom]; omega
  have hLlt_P : (5 : Nat) < (sP.mem.get 13).toNat := by rw [hC_P]; exact hLlt
  have hChi_P : (sP.mem.get 13).toNat < 32768 := by rw [hC_P]; exact hChi
  have gP : ∀ k : Nat, 1077 ≤ k → k < 2319 →
      sP.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n26 : UInt16.ofNat k ≠ (26 : Word) := by
      have : (26 : Word) = UInt16.ofNat 26 := rfl
      rw [this]; exact ofNat_ne k 26 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n16 : UInt16.ofNat k ≠ (16 : Word) := by
      have : (16 : Word) = UInt16.ofNat 16 := rfl
      rw [this]; exact ofNat_ne k 16 (by omega) (by decide) (by omega)
    have n27 : UInt16.ofNat k ≠ (27 : Word) := by
      have : (27 : Word) = UInt16.ofNat 27 := rfl
      rw [this]; exact ofNat_ne k 27 (by omega) (by decide) (by omega)
    have n28 : UInt16.ofNat k ≠ (28 : Word) := by
      have : (28 : Word) = UInt16.ofNat 28 := rfl
      rw [this]; exact ofNat_ne k 28 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresP (UInt16.ofNat k) n26 n18 n16 n27 n28 n29 n0).trans
      (hcode k (by omega) (by omega))
  have hm := after_pad_minus_ndig4_done (s := sP) hsPpc hsPh hsPZ hONE_P hK5_P hK45_P
    hN_P hI_P hL_P hSlo_P hShi_P hRlo0 hRlo hRhi hLlt_P hChi_P gP
  have hrun : sD = runN sP 489 := runN_add_eq s 38 489 527 (by decide)
  have hsD32 : sD.mem.get 32 = 45 := by rw [hrun]; exact hm.2.2.2.1
  have hsD33 : sD.mem.get 33 = s.mem.get 21 := by
    rw [hrun]
    have h1 : sP.mem.get 21 = s.mem.get 21 := hpresP 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact (hm.2.2.2.2.1).trans h1
  have hsD34 : sD.mem.get 34 = s.mem.get 22 := by
    rw [hrun]
    have h1 : sP.mem.get 22 = s.mem.get 22 := hpresP 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact (hm.2.2.2.2.2.1).trans h1
  have hsD35 : sD.mem.get 35 = s.mem.get 23 := by
    rw [hrun]
    have h1 : sP.mem.get 23 = s.mem.get 23 := hpresP 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact (hm.2.2.2.2.2.2.1).trans h1
  have hsD36 : sD.mem.get 36 = s.mem.get 24 := by
    rw [hrun]
    have h1 : sP.mem.get 24 = s.mem.get 24 := hpresP 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact (hm.2.2.2.2.2.2.2.1).trans h1
  have hsDNUL : sD.mem.get 37 = 0 := by rw [hrun]; exact hm.2.2.2.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 5 := by rw [hrun]; exact hm.2.2.2.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 5 := by rw [hrun]; exact hm.2.2.2.2.2.2.2.2.2.2.1
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hm.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hm.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hm.2.2.1
  have hpresw := hm.2.2.2.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha26 ha16 ha27 ha28
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha35 ha36 ha37 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpresP a ha26 ha18 ha16 ha27 ha28 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsD35, hsD36, hsDNUL, hsDI, hsDL, hpres⟩

/-- From `P3_DONE` with leading-zero pattern for `NDIG = 1`, `SIGN ≠ 0`,
`WIDTH = 0`, and `2 < CAP`: ASCII-convert, write a leading minus,
emit, NUL-terminate, and halt. 389 steps. -/
theorem p3_done_signed_ndig1_done {s : Machine}
    (hpc : s.pc = 513)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK48 : s.mem.get 8 = 48)
    (hK45 : s.mem.get 9 = 45)
    (hK5 : s.mem.get 2322 = 5)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hW : s.mem.get 14 = 0)
    (hZ20 : s.mem.get 20 = 0)
    (hZ21 : s.mem.get 21 = 0)
    (hZ22 : s.mem.get 22 = 0)
    (hZ23 : s.mem.get 23 = 0)

    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (2 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 513 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 389
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
        sD.mem.get 32 = 45 ∧
    sD.mem.get 33 = s.mem.get 17 + 48 ∧
    sD.mem.get 34 = 0 ∧
    sD.mem.get 29 = 2 ∧
    sD.mem.get 16 = 2 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have ha := ascii_convert (s := s) hpc hh hZ hK48
    (fun k h1 h2 => hcode k h1 (by omega))
  let s19 := runN s 19
  have hs19pc : s19.pc = 570 := ha.1
  have hs19h : s19.halted = false := ha.2.1
  have hs19Z : s19.mem.get 0 = 0 := ha.2.2.1
  have hpresA := ha.2.2.2.2.2.2.2.2.2
  have hONE19 : s19.mem.get 3 = 1 := (hpresA 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK48_19 : s19.mem.get 8 = 48 := (hpresA 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK48
  have hQ20A : s19.mem.get 20 = 48 := by
    have : s19.mem.get 20 = s.mem.get 20 + 48 := ha.2.2.2.2.1
    rw [this, hZ20]
    exact (rfl : (0 : Word) + 48 = 48)
  have hQ21A : s19.mem.get 21 = 48 := by
    have : s19.mem.get 21 = s.mem.get 21 + 48 := ha.2.2.2.2.2.1
    rw [this, hZ21]
    exact (rfl : (0 : Word) + 48 = 48)
  have hQ22A : s19.mem.get 22 = 48 := by
    have : s19.mem.get 22 = s.mem.get 22 + 48 := ha.2.2.2.2.2.2.1
    rw [this, hZ22]
    exact (rfl : (0 : Word) + 48 = 48)
  have hQ23A : s19.mem.get 23 = 48 := by
    have : s19.mem.get 23 = s.mem.get 23 + 48 := ha.2.2.2.2.2.2.2.1
    rw [this, hZ23]
    exact (rfl : (0 : Word) + 48 = 48)

  have g19 : ∀ k : Nat, 570 ≤ k → k < 867 →
      s19.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n24 : UInt16.ofNat k ≠ (24 : Word) := by
      have : (24 : Word) = UInt16.ofNat 24 := rfl
      rw [this]; exact ofNat_ne k 24 (by omega) (by decide) (by omega)
    have n20 : UInt16.ofNat k ≠ (20 : Word) := by
      have : (20 : Word) = UInt16.ofNat 20 := rfl
      rw [this]; exact ofNat_ne k 20 (by omega) (by decide) (by omega)
    have n21 : UInt16.ofNat k ≠ (21 : Word) := by
      have : (21 : Word) = UInt16.ofNat 21 := rfl
      rw [this]; exact ofNat_ne k 21 (by omega) (by decide) (by omega)
    have n22 : UInt16.ofNat k ≠ (22 : Word) := by
      have : (22 : Word) = UInt16.ofNat 22 := rfl
      rw [this]; exact ofNat_ne k 22 (by omega) (by decide) (by omega)
    have n23 : UInt16.ofNat k ≠ (23 : Word) := by
      have : (23 : Word) = UInt16.ofNat 23 := rfl
      rw [this]; exact ofNat_ne k 23 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresA (UInt16.ofNat k) n24 n20 n21 n22 n23 n0).trans
      (hcode k (by omega) (by omega))
  have hn := ndig_one (s := s19) hs19pc hs19h hs19Z hONE19 hK48_19
    hQ20A hQ21A hQ22A hQ23A g19
  have hrunN : runN s 48 = runN s19 29 := runN_add_eq s 19 29 48 (by decide)
  let sN := runN s 48
  have hsNpc : sN.pc = 867 := by
    have : sN = runN s19 29 := hrunN; rw [this]; exact hn.1
  have hsNh : sN.halted = false := by
    have : sN = runN s19 29 := hrunN; rw [this]; exact hn.2.1
  have hsNZ : sN.mem.get 0 = 0 := by
    have : sN = runN s19 29 := hrunN; rw [this]; exact hn.2.2.1
  have hsNN : sN.mem.get 25 = 1 := by
    have : sN = runN s19 29 := hrunN; rw [this]; exact hn.2.2.2.1
  have hpresNraw := hn.2.2.2.2
  have hpresN : ∀ a, a ≠ 18 → a ≠ 25 → a ≠ 0 → sN.mem.get a = s19.mem.get a := by
    intro a ha18 ha25 ha0
    have : sN = runN s19 29 := hrunN
    rw [this]; exact hpresNraw a ha18 ha25 ha0
  have hONE_N : sN.mem.get 3 = 1 := (hpresN 3 (by decide) (by decide) (by decide)).trans hONE19
  have hK5_N : sN.mem.get 2322 = 5 :=
    (hpresN 2322 (by decide) (by decide) (by decide)).trans ((hpresA 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5)
  have hK45_N : sN.mem.get 9 = 45 :=
    (hpresN 9 (by decide) (by decide) (by decide)).trans ((hpresA 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK45)
  have hSlo_N : 0 < (sN.mem.get 19).toNat := by
    have : sN.mem.get 19 = s.mem.get 19 :=
      (hpresN 19 (by decide) (by decide) (by decide)).trans (hpresA 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hSlo
  have hShi_N : (sN.mem.get 19).toNat < 32768 := by
    have : sN.mem.get 19 = s.mem.get 19 :=
      (hpresN 19 (by decide) (by decide) (by decide)).trans (hpresA 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hShi
  have hW_N : sN.mem.get 14 = 0 :=
    (hpresN 14 (by decide) (by decide) (by decide)).trans ((hpresA 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hW)
  have hClo_N : 0 < (sN.mem.get 13).toNat := by
    have : sN.mem.get 13 = s.mem.get 13 :=
      (hpresN 13 (by decide) (by decide) (by decide)).trans (hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hClo
  have hChi_N : (sN.mem.get 13).toNat < 32768 := by
    have : sN.mem.get 13 = s.mem.get 13 :=
      (hpresN 13 (by decide) (by decide) (by decide)).trans (hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hChi
  have hLlt_N : (2 : Nat) < (sN.mem.get 13).toNat := by
    have : sN.mem.get 13 = s.mem.get 13 :=
      (hpresN 13 (by decide) (by decide) (by decide)).trans (hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hLlt
  have gN : ∀ k : Nat, 867 ≤ k → k < 2319 →
      sN.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n25 : UInt16.ofNat k ≠ (25 : Word) := by
      have : (25 : Word) = UInt16.ofNat 25 := rfl
      rw [this]; exact ofNat_ne k 25 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    have n24 : UInt16.ofNat k ≠ (24 : Word) := by
      have : (24 : Word) = UInt16.ofNat 24 := rfl
      rw [this]; exact ofNat_ne k 24 (by omega) (by decide) (by omega)
    have n20 : UInt16.ofNat k ≠ (20 : Word) := by
      have : (20 : Word) = UInt16.ofNat 20 := rfl
      rw [this]; exact ofNat_ne k 20 (by omega) (by decide) (by omega)
    have n21 : UInt16.ofNat k ≠ (21 : Word) := by
      have : (21 : Word) = UInt16.ofNat 21 := rfl
      rw [this]; exact ofNat_ne k 21 (by omega) (by decide) (by omega)
    have n22 : UInt16.ofNat k ≠ (22 : Word) := by
      have : (22 : Word) = UInt16.ofNat 22 := rfl
      rw [this]; exact ofNat_ne k 22 (by omega) (by decide) (by omega)
    have n23 : UInt16.ofNat k ≠ (23 : Word) := by
      have : (23 : Word) = UInt16.ofNat 23 := rfl
      rw [this]; exact ofNat_ne k 23 (by omega) (by decide) (by omega)
    exact (hpresN (UInt16.ofNat k)
        n18 n25 n0).trans
      ((hpresA (UInt16.ofNat k)
        n24 n20 n21 n22 n23 n0).trans
      (hcode k (by omega) (by omega)))
  have hd := have_dig_signed_ndig1_done (s := sN) hsNpc hsNh hsNZ hONE_N hK5_N hK45_N
    hSlo_N hShi_N hW_N hsNN hClo_N hChi_N hLlt_N gN
  have hrun : sD = runN sN 341 := runN_add_eq s 48 341 389 (by decide)
  have hsD32 : sD.mem.get 32 = 45 := by rw [hrun]; exact hd.2.2.2.1
  have hsD33 : sD.mem.get 33 = s.mem.get 17 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 24 = s19.mem.get 24 := hpresN 24 (by decide) (by decide) (by decide)
    exact (hd.2.2.2.2.1).trans (h1.trans ha.2.2.2.1)
  have hsDNUL : sD.mem.get 34 = 0 := by rw [hrun]; exact hd.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 2 := by rw [hrun]; exact hd.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 2 := by rw [hrun]; exact hd.2.2.2.2.2.2.2.1
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hd.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hd.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hd.2.2.1
  have hpresw := hd.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha26 ha16 ha27 ha28 ha24 ha20 ha21 ha22 ha23 ha25
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha26 ha16 ha27 ha28).trans
      ((hpresN a ha18 ha25 ha0).trans
        (hpresA a ha24 ha20 ha21 ha22 ha23 ha0))
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsDNUL, hsDI, hsDL, hpres⟩

/-- From `P3_DONE` with leading-zero pattern for `NDIG = 2`, `SIGN ≠ 0`,
`WIDTH = 0`, and `3 < CAP`: ASCII-convert, write a leading minus,
emit, NUL-terminate, and halt. 459 steps. -/
theorem p3_done_signed_ndig2_done {s : Machine}
    (hpc : s.pc = 513)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK48 : s.mem.get 8 = 48)
    (hK45 : s.mem.get 9 = 45)
    (hK5 : s.mem.get 2322 = 5)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hW : s.mem.get 14 = 0)
    (hZ20 : s.mem.get 20 = 0)
    (hZ21 : s.mem.get 21 = 0)
    (hZ22 : s.mem.get 22 = 0)
    (hLlo : 0 < (s.mem.get 23).toNat)
    (hLhi : (s.mem.get 23).toNat ≤ 9)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (3 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 513 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 459
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
        sD.mem.get 32 = 45 ∧
    sD.mem.get 33 = s.mem.get 23 + 48 ∧
    sD.mem.get 34 = s.mem.get 17 + 48 ∧
    sD.mem.get 35 = 0 ∧
    sD.mem.get 29 = 3 ∧
    sD.mem.get 16 = 3 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have ha := ascii_convert (s := s) hpc hh hZ hK48
    (fun k h1 h2 => hcode k h1 (by omega))
  let s19 := runN s 19
  have hs19pc : s19.pc = 570 := ha.1
  have hs19h : s19.halted = false := ha.2.1
  have hs19Z : s19.mem.get 0 = 0 := ha.2.2.1
  have hpresA := ha.2.2.2.2.2.2.2.2.2
  have hONE19 : s19.mem.get 3 = 1 := (hpresA 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK48_19 : s19.mem.get 8 = 48 := (hpresA 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK48
  have hQ20A : s19.mem.get 20 = 48 := by
    have : s19.mem.get 20 = s.mem.get 20 + 48 := ha.2.2.2.2.1
    rw [this, hZ20]
    exact (rfl : (0 : Word) + 48 = 48)
  have hQ21A : s19.mem.get 21 = 48 := by
    have : s19.mem.get 21 = s.mem.get 21 + 48 := ha.2.2.2.2.2.1
    rw [this, hZ21]
    exact (rfl : (0 : Word) + 48 = 48)
  have hQ22A : s19.mem.get 22 = 48 := by
    have : s19.mem.get 22 = s.mem.get 22 + 48 := ha.2.2.2.2.2.2.1
    rw [this, hZ22]
    exact (rfl : (0 : Word) + 48 = 48)

  have hloA : 48 ≤ (s19.mem.get 23).toNat := by
    have hq : s19.mem.get 23 = s.mem.get 23 + 48 := ha.2.2.2.2.2.2.2.1
    have hsum : (s.mem.get 23).toNat + 48 < 65536 := by
      have : (s.mem.get 23).toNat ≤ 9 := hLhi
      omega
    have hadd := word_add_toNat (s.mem.get 23) 48 hsum
    have ht : (s19.mem.get 23).toNat = (s.mem.get 23).toNat + 48 := hq ▸ hadd
    omega
  have hhiA : (s19.mem.get 23).toNat ≤ 57 := by
    have hq : s19.mem.get 23 = s.mem.get 23 + 48 := ha.2.2.2.2.2.2.2.1
    have hsum : (s.mem.get 23).toNat + 48 < 65536 := by
      have : (s.mem.get 23).toNat ≤ 9 := hLhi
      omega
    have hadd := word_add_toNat (s.mem.get 23) 48 hsum
    have ht : (s19.mem.get 23).toNat = (s.mem.get 23).toNat + 48 := hq ▸ hadd
    omega
  have hneA : s19.mem.get 23 ≠ 48 := by
    have hq : s19.mem.get 23 = s.mem.get 23 + 48 := ha.2.2.2.2.2.2.2.1
    have hsum : (s.mem.get 23).toNat + 48 < 65536 := by
      have : (s.mem.get 23).toNat ≤ 9 := hLhi
      omega
    have hadd := word_add_toNat (s.mem.get 23) 48 hsum
    have ht : (s19.mem.get 23).toNat = (s.mem.get 23).toNat + 48 := hq ▸ hadd
    intro heq
    have : (s19.mem.get 23).toNat = 48 := by simp [heq]
    omega

  have g19 : ∀ k : Nat, 570 ≤ k → k < 867 →
      s19.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n24 : UInt16.ofNat k ≠ (24 : Word) := by
      have : (24 : Word) = UInt16.ofNat 24 := rfl
      rw [this]; exact ofNat_ne k 24 (by omega) (by decide) (by omega)
    have n20 : UInt16.ofNat k ≠ (20 : Word) := by
      have : (20 : Word) = UInt16.ofNat 20 := rfl
      rw [this]; exact ofNat_ne k 20 (by omega) (by decide) (by omega)
    have n21 : UInt16.ofNat k ≠ (21 : Word) := by
      have : (21 : Word) = UInt16.ofNat 21 := rfl
      rw [this]; exact ofNat_ne k 21 (by omega) (by decide) (by omega)
    have n22 : UInt16.ofNat k ≠ (22 : Word) := by
      have : (22 : Word) = UInt16.ofNat 22 := rfl
      rw [this]; exact ofNat_ne k 22 (by omega) (by decide) (by omega)
    have n23 : UInt16.ofNat k ≠ (23 : Word) := by
      have : (23 : Word) = UInt16.ofNat 23 := rfl
      rw [this]; exact ofNat_ne k 23 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresA (UInt16.ofNat k) n24 n20 n21 n22 n23 n0).trans
      (hcode k (by omega) (by omega))
  have hn := ndig_two (s := s19) hs19pc hs19h hs19Z hONE19 hK48_19
    hQ20A hQ21A hQ22A hloA hhiA hneA g19
  have hrunN : runN s 56 = runN s19 37 := runN_add_eq s 19 37 56 (by decide)
  let sN := runN s 56
  have hsNpc : sN.pc = 867 := by
    have : sN = runN s19 37 := hrunN; rw [this]; exact hn.1
  have hsNh : sN.halted = false := by
    have : sN = runN s19 37 := hrunN; rw [this]; exact hn.2.1
  have hsNZ : sN.mem.get 0 = 0 := by
    have : sN = runN s19 37 := hrunN; rw [this]; exact hn.2.2.1
  have hsNN : sN.mem.get 25 = 2 := by
    have : sN = runN s19 37 := hrunN; rw [this]; exact hn.2.2.2.1
  have hpresNraw := hn.2.2.2.2
  have hpresN : ∀ a, a ≠ 18 → a ≠ 25 → a ≠ 31 → a ≠ 0 → sN.mem.get a = s19.mem.get a := by
    intro a ha18 ha25 ha31 ha0
    have : sN = runN s19 37 := hrunN
    rw [this]; exact hpresNraw a ha18 ha25 ha31 ha0
  have hONE_N : sN.mem.get 3 = 1 := (hpresN 3 (by decide) (by decide) (by decide) (by decide)).trans hONE19
  have hK5_N : sN.mem.get 2322 = 5 :=
    (hpresN 2322 (by decide) (by decide) (by decide) (by decide)).trans ((hpresA 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5)
  have hK45_N : sN.mem.get 9 = 45 :=
    (hpresN 9 (by decide) (by decide) (by decide) (by decide)).trans ((hpresA 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK45)
  have hSlo_N : 0 < (sN.mem.get 19).toNat := by
    have : sN.mem.get 19 = s.mem.get 19 :=
      (hpresN 19 (by decide) (by decide) (by decide) (by decide)).trans (hpresA 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hSlo
  have hShi_N : (sN.mem.get 19).toNat < 32768 := by
    have : sN.mem.get 19 = s.mem.get 19 :=
      (hpresN 19 (by decide) (by decide) (by decide) (by decide)).trans (hpresA 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hShi
  have hW_N : sN.mem.get 14 = 0 :=
    (hpresN 14 (by decide) (by decide) (by decide) (by decide)).trans ((hpresA 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hW)
  have hClo_N : 0 < (sN.mem.get 13).toNat := by
    have : sN.mem.get 13 = s.mem.get 13 :=
      (hpresN 13 (by decide) (by decide) (by decide) (by decide)).trans (hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hClo
  have hChi_N : (sN.mem.get 13).toNat < 32768 := by
    have : sN.mem.get 13 = s.mem.get 13 :=
      (hpresN 13 (by decide) (by decide) (by decide) (by decide)).trans (hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hChi
  have hLlt_N : (3 : Nat) < (sN.mem.get 13).toNat := by
    have : sN.mem.get 13 = s.mem.get 13 :=
      (hpresN 13 (by decide) (by decide) (by decide) (by decide)).trans (hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hLlt
  have gN : ∀ k : Nat, 867 ≤ k → k < 2319 →
      sN.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n25 : UInt16.ofNat k ≠ (25 : Word) := by
      have : (25 : Word) = UInt16.ofNat 25 := rfl
      rw [this]; exact ofNat_ne k 25 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    have n24 : UInt16.ofNat k ≠ (24 : Word) := by
      have : (24 : Word) = UInt16.ofNat 24 := rfl
      rw [this]; exact ofNat_ne k 24 (by omega) (by decide) (by omega)
    have n20 : UInt16.ofNat k ≠ (20 : Word) := by
      have : (20 : Word) = UInt16.ofNat 20 := rfl
      rw [this]; exact ofNat_ne k 20 (by omega) (by decide) (by omega)
    have n21 : UInt16.ofNat k ≠ (21 : Word) := by
      have : (21 : Word) = UInt16.ofNat 21 := rfl
      rw [this]; exact ofNat_ne k 21 (by omega) (by decide) (by omega)
    have n22 : UInt16.ofNat k ≠ (22 : Word) := by
      have : (22 : Word) = UInt16.ofNat 22 := rfl
      rw [this]; exact ofNat_ne k 22 (by omega) (by decide) (by omega)
    have n23 : UInt16.ofNat k ≠ (23 : Word) := by
      have : (23 : Word) = UInt16.ofNat 23 := rfl
      rw [this]; exact ofNat_ne k 23 (by omega) (by decide) (by omega)
    exact (hpresN (UInt16.ofNat k)
        n18 n25 n31 n0).trans
      ((hpresA (UInt16.ofNat k)
        n24 n20 n21 n22 n23 n0).trans
      (hcode k (by omega) (by omega)))
  have hd := have_dig_signed_ndig2_done (s := sN) hsNpc hsNh hsNZ hONE_N hK5_N hK45_N
    hSlo_N hShi_N hW_N hsNN hClo_N hChi_N hLlt_N gN
  have hrun : sD = runN sN 403 := runN_add_eq s 56 403 459 (by decide)
  have hsD32 : sD.mem.get 32 = 45 := by rw [hrun]; exact hd.2.2.2.1
  have hsD33 : sD.mem.get 33 = s.mem.get 23 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 23 = s19.mem.get 23 := hpresN 23 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.2.1).trans (h1.trans ha.2.2.2.2.2.2.2.1)
  have hsD34 : sD.mem.get 34 = s.mem.get 17 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 24 = s19.mem.get 24 := hpresN 24 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.2.2.1).trans (h1.trans ha.2.2.2.1)
  have hsDNUL : sD.mem.get 35 = 0 := by rw [hrun]; exact hd.2.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 3 := by rw [hrun]; exact hd.2.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 3 := by rw [hrun]; exact hd.2.2.2.2.2.2.2.2.1
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hd.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hd.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hd.2.2.1
  have hpresw := hd.2.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha26 ha16 ha27 ha28 ha24 ha20 ha21 ha22 ha23 ha25
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha35 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha26 ha16 ha27 ha28).trans
      ((hpresN a ha18 ha25 ha31 ha0).trans
        (hpresA a ha24 ha20 ha21 ha22 ha23 ha0))
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsDNUL, hsDI, hsDL, hpres⟩

/-- From `P3_DONE` with leading-zero pattern for `NDIG = 3`, `SIGN ≠ 0`,
`WIDTH = 0`, and `4 < CAP`: ASCII-convert, write a leading minus,
emit, NUL-terminate, and halt. 518 steps. -/
theorem p3_done_signed_ndig3_done {s : Machine}
    (hpc : s.pc = 513)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK48 : s.mem.get 8 = 48)
    (hK45 : s.mem.get 9 = 45)
    (hK5 : s.mem.get 2322 = 5)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hW : s.mem.get 14 = 0)
    (hZ20 : s.mem.get 20 = 0)
    (hZ21 : s.mem.get 21 = 0)
    (hLlo : 0 < (s.mem.get 22).toNat)
    (hLhi : (s.mem.get 22).toNat ≤ 9)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (4 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 513 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 518
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
        sD.mem.get 32 = 45 ∧
    sD.mem.get 33 = s.mem.get 22 + 48 ∧
    sD.mem.get 34 = s.mem.get 23 + 48 ∧
    sD.mem.get 35 = s.mem.get 17 + 48 ∧
    sD.mem.get 36 = 0 ∧
    sD.mem.get 29 = 4 ∧
    sD.mem.get 16 = 4 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have ha := ascii_convert (s := s) hpc hh hZ hK48
    (fun k h1 h2 => hcode k h1 (by omega))
  let s19 := runN s 19
  have hs19pc : s19.pc = 570 := ha.1
  have hs19h : s19.halted = false := ha.2.1
  have hs19Z : s19.mem.get 0 = 0 := ha.2.2.1
  have hpresA := ha.2.2.2.2.2.2.2.2.2
  have hONE19 : s19.mem.get 3 = 1 := (hpresA 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK48_19 : s19.mem.get 8 = 48 := (hpresA 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK48
  have hQ20A : s19.mem.get 20 = 48 := by
    have : s19.mem.get 20 = s.mem.get 20 + 48 := ha.2.2.2.2.1
    rw [this, hZ20]
    exact (rfl : (0 : Word) + 48 = 48)
  have hQ21A : s19.mem.get 21 = 48 := by
    have : s19.mem.get 21 = s.mem.get 21 + 48 := ha.2.2.2.2.2.1
    rw [this, hZ21]
    exact (rfl : (0 : Word) + 48 = 48)

  have hloA : 48 ≤ (s19.mem.get 22).toNat := by
    have hq : s19.mem.get 22 = s.mem.get 22 + 48 := ha.2.2.2.2.2.2.1
    have hsum : (s.mem.get 22).toNat + 48 < 65536 := by
      have : (s.mem.get 22).toNat ≤ 9 := hLhi
      omega
    have hadd := word_add_toNat (s.mem.get 22) 48 hsum
    have ht : (s19.mem.get 22).toNat = (s.mem.get 22).toNat + 48 := hq ▸ hadd
    omega
  have hhiA : (s19.mem.get 22).toNat ≤ 57 := by
    have hq : s19.mem.get 22 = s.mem.get 22 + 48 := ha.2.2.2.2.2.2.1
    have hsum : (s.mem.get 22).toNat + 48 < 65536 := by
      have : (s.mem.get 22).toNat ≤ 9 := hLhi
      omega
    have hadd := word_add_toNat (s.mem.get 22) 48 hsum
    have ht : (s19.mem.get 22).toNat = (s.mem.get 22).toNat + 48 := hq ▸ hadd
    omega
  have hneA : s19.mem.get 22 ≠ 48 := by
    have hq : s19.mem.get 22 = s.mem.get 22 + 48 := ha.2.2.2.2.2.2.1
    have hsum : (s.mem.get 22).toNat + 48 < 65536 := by
      have : (s.mem.get 22).toNat ≤ 9 := hLhi
      omega
    have hadd := word_add_toNat (s.mem.get 22) 48 hsum
    have ht : (s19.mem.get 22).toNat = (s.mem.get 22).toNat + 48 := hq ▸ hadd
    intro heq
    have : (s19.mem.get 22).toNat = 48 := by simp [heq]
    omega

  have g19 : ∀ k : Nat, 570 ≤ k → k < 867 →
      s19.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n24 : UInt16.ofNat k ≠ (24 : Word) := by
      have : (24 : Word) = UInt16.ofNat 24 := rfl
      rw [this]; exact ofNat_ne k 24 (by omega) (by decide) (by omega)
    have n20 : UInt16.ofNat k ≠ (20 : Word) := by
      have : (20 : Word) = UInt16.ofNat 20 := rfl
      rw [this]; exact ofNat_ne k 20 (by omega) (by decide) (by omega)
    have n21 : UInt16.ofNat k ≠ (21 : Word) := by
      have : (21 : Word) = UInt16.ofNat 21 := rfl
      rw [this]; exact ofNat_ne k 21 (by omega) (by decide) (by omega)
    have n22 : UInt16.ofNat k ≠ (22 : Word) := by
      have : (22 : Word) = UInt16.ofNat 22 := rfl
      rw [this]; exact ofNat_ne k 22 (by omega) (by decide) (by omega)
    have n23 : UInt16.ofNat k ≠ (23 : Word) := by
      have : (23 : Word) = UInt16.ofNat 23 := rfl
      rw [this]; exact ofNat_ne k 23 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresA (UInt16.ofNat k) n24 n20 n21 n22 n23 n0).trans
      (hcode k (by omega) (by omega))
  have hn := ndig_three (s := s19) hs19pc hs19h hs19Z hONE19 hK48_19
    hQ20A hQ21A hloA hhiA hneA g19
  have hrunN : runN s 53 = runN s19 34 := runN_add_eq s 19 34 53 (by decide)
  let sN := runN s 53
  have hsNpc : sN.pc = 867 := by
    have : sN = runN s19 34 := hrunN; rw [this]; exact hn.1
  have hsNh : sN.halted = false := by
    have : sN = runN s19 34 := hrunN; rw [this]; exact hn.2.1
  have hsNZ : sN.mem.get 0 = 0 := by
    have : sN = runN s19 34 := hrunN; rw [this]; exact hn.2.2.1
  have hsNN : sN.mem.get 25 = 3 := by
    have : sN = runN s19 34 := hrunN; rw [this]; exact hn.2.2.2.1
  have hpresNraw := hn.2.2.2.2
  have hpresN : ∀ a, a ≠ 18 → a ≠ 25 → a ≠ 31 → a ≠ 0 → sN.mem.get a = s19.mem.get a := by
    intro a ha18 ha25 ha31 ha0
    have : sN = runN s19 34 := hrunN
    rw [this]; exact hpresNraw a ha18 ha25 ha31 ha0
  have hONE_N : sN.mem.get 3 = 1 := (hpresN 3 (by decide) (by decide) (by decide) (by decide)).trans hONE19
  have hK5_N : sN.mem.get 2322 = 5 :=
    (hpresN 2322 (by decide) (by decide) (by decide) (by decide)).trans ((hpresA 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5)
  have hK45_N : sN.mem.get 9 = 45 :=
    (hpresN 9 (by decide) (by decide) (by decide) (by decide)).trans ((hpresA 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK45)
  have hSlo_N : 0 < (sN.mem.get 19).toNat := by
    have : sN.mem.get 19 = s.mem.get 19 :=
      (hpresN 19 (by decide) (by decide) (by decide) (by decide)).trans (hpresA 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hSlo
  have hShi_N : (sN.mem.get 19).toNat < 32768 := by
    have : sN.mem.get 19 = s.mem.get 19 :=
      (hpresN 19 (by decide) (by decide) (by decide) (by decide)).trans (hpresA 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hShi
  have hW_N : sN.mem.get 14 = 0 :=
    (hpresN 14 (by decide) (by decide) (by decide) (by decide)).trans ((hpresA 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hW)
  have hClo_N : 0 < (sN.mem.get 13).toNat := by
    have : sN.mem.get 13 = s.mem.get 13 :=
      (hpresN 13 (by decide) (by decide) (by decide) (by decide)).trans (hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hClo
  have hChi_N : (sN.mem.get 13).toNat < 32768 := by
    have : sN.mem.get 13 = s.mem.get 13 :=
      (hpresN 13 (by decide) (by decide) (by decide) (by decide)).trans (hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hChi
  have hLlt_N : (4 : Nat) < (sN.mem.get 13).toNat := by
    have : sN.mem.get 13 = s.mem.get 13 :=
      (hpresN 13 (by decide) (by decide) (by decide) (by decide)).trans (hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hLlt
  have gN : ∀ k : Nat, 867 ≤ k → k < 2319 →
      sN.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n25 : UInt16.ofNat k ≠ (25 : Word) := by
      have : (25 : Word) = UInt16.ofNat 25 := rfl
      rw [this]; exact ofNat_ne k 25 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    have n24 : UInt16.ofNat k ≠ (24 : Word) := by
      have : (24 : Word) = UInt16.ofNat 24 := rfl
      rw [this]; exact ofNat_ne k 24 (by omega) (by decide) (by omega)
    have n20 : UInt16.ofNat k ≠ (20 : Word) := by
      have : (20 : Word) = UInt16.ofNat 20 := rfl
      rw [this]; exact ofNat_ne k 20 (by omega) (by decide) (by omega)
    have n21 : UInt16.ofNat k ≠ (21 : Word) := by
      have : (21 : Word) = UInt16.ofNat 21 := rfl
      rw [this]; exact ofNat_ne k 21 (by omega) (by decide) (by omega)
    have n22 : UInt16.ofNat k ≠ (22 : Word) := by
      have : (22 : Word) = UInt16.ofNat 22 := rfl
      rw [this]; exact ofNat_ne k 22 (by omega) (by decide) (by omega)
    have n23 : UInt16.ofNat k ≠ (23 : Word) := by
      have : (23 : Word) = UInt16.ofNat 23 := rfl
      rw [this]; exact ofNat_ne k 23 (by omega) (by decide) (by omega)
    exact (hpresN (UInt16.ofNat k)
        n18 n25 n31 n0).trans
      ((hpresA (UInt16.ofNat k)
        n24 n20 n21 n22 n23 n0).trans
      (hcode k (by omega) (by omega)))
  have hd := have_dig_signed_ndig3_done (s := sN) hsNpc hsNh hsNZ hONE_N hK5_N hK45_N
    hSlo_N hShi_N hW_N hsNN hClo_N hChi_N hLlt_N gN
  have hrun : sD = runN sN 465 := runN_add_eq s 53 465 518 (by decide)
  have hsD32 : sD.mem.get 32 = 45 := by rw [hrun]; exact hd.2.2.2.1
  have hsD33 : sD.mem.get 33 = s.mem.get 22 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 22 = s19.mem.get 22 := hpresN 22 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.2.1).trans (h1.trans ha.2.2.2.2.2.2.1)
  have hsD34 : sD.mem.get 34 = s.mem.get 23 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 23 = s19.mem.get 23 := hpresN 23 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.2.2.1).trans (h1.trans ha.2.2.2.2.2.2.2.1)
  have hsD35 : sD.mem.get 35 = s.mem.get 17 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 24 = s19.mem.get 24 := hpresN 24 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.2.2.2.1).trans (h1.trans ha.2.2.2.1)
  have hsDNUL : sD.mem.get 36 = 0 := by rw [hrun]; exact hd.2.2.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 4 := by rw [hrun]; exact hd.2.2.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 4 := by rw [hrun]; exact hd.2.2.2.2.2.2.2.2.2.1
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hd.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hd.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hd.2.2.1
  have hpresw := hd.2.2.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha26 ha16 ha27 ha28 ha24 ha20 ha21 ha22 ha23 ha25
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha35 ha36 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha26 ha16 ha27 ha28).trans
      ((hpresN a ha18 ha25 ha31 ha0).trans
        (hpresA a ha24 ha20 ha21 ha22 ha23 ha0))
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsD35, hsDNUL, hsDI, hsDL, hpres⟩

/-- From `P3_DONE` with leading-zero pattern for `NDIG = 4`, `SIGN ≠ 0`,
`WIDTH = 0`, and `5 < CAP`: ASCII-convert, write a leading minus,
emit, NUL-terminate, and halt. 577 steps. -/
theorem p3_done_signed_ndig4_done {s : Machine}
    (hpc : s.pc = 513)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK48 : s.mem.get 8 = 48)
    (hK45 : s.mem.get 9 = 45)
    (hK5 : s.mem.get 2322 = 5)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hW : s.mem.get 14 = 0)
    (hZ20 : s.mem.get 20 = 0)
    (hLlo : 0 < (s.mem.get 21).toNat)
    (hLhi : (s.mem.get 21).toNat ≤ 9)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (5 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 513 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 577
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
        sD.mem.get 32 = 45 ∧
    sD.mem.get 33 = s.mem.get 21 + 48 ∧
    sD.mem.get 34 = s.mem.get 22 + 48 ∧
    sD.mem.get 35 = s.mem.get 23 + 48 ∧
    sD.mem.get 36 = s.mem.get 17 + 48 ∧
    sD.mem.get 37 = 0 ∧
    sD.mem.get 29 = 5 ∧
    sD.mem.get 16 = 5 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have ha := ascii_convert (s := s) hpc hh hZ hK48
    (fun k h1 h2 => hcode k h1 (by omega))
  let s19 := runN s 19
  have hs19pc : s19.pc = 570 := ha.1
  have hs19h : s19.halted = false := ha.2.1
  have hs19Z : s19.mem.get 0 = 0 := ha.2.2.1
  have hpresA := ha.2.2.2.2.2.2.2.2.2
  have hONE19 : s19.mem.get 3 = 1 := (hpresA 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK48_19 : s19.mem.get 8 = 48 := (hpresA 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK48
  have hQ20A : s19.mem.get 20 = 48 := by
    have : s19.mem.get 20 = s.mem.get 20 + 48 := ha.2.2.2.2.1
    rw [this, hZ20]
    exact (rfl : (0 : Word) + 48 = 48)

  have hloA : 48 ≤ (s19.mem.get 21).toNat := by
    have hq : s19.mem.get 21 = s.mem.get 21 + 48 := ha.2.2.2.2.2.1
    have hsum : (s.mem.get 21).toNat + 48 < 65536 := by
      have : (s.mem.get 21).toNat ≤ 9 := hLhi
      omega
    have hadd := word_add_toNat (s.mem.get 21) 48 hsum
    have ht : (s19.mem.get 21).toNat = (s.mem.get 21).toNat + 48 := hq ▸ hadd
    omega
  have hhiA : (s19.mem.get 21).toNat ≤ 57 := by
    have hq : s19.mem.get 21 = s.mem.get 21 + 48 := ha.2.2.2.2.2.1
    have hsum : (s.mem.get 21).toNat + 48 < 65536 := by
      have : (s.mem.get 21).toNat ≤ 9 := hLhi
      omega
    have hadd := word_add_toNat (s.mem.get 21) 48 hsum
    have ht : (s19.mem.get 21).toNat = (s.mem.get 21).toNat + 48 := hq ▸ hadd
    omega
  have hneA : s19.mem.get 21 ≠ 48 := by
    have hq : s19.mem.get 21 = s.mem.get 21 + 48 := ha.2.2.2.2.2.1
    have hsum : (s.mem.get 21).toNat + 48 < 65536 := by
      have : (s.mem.get 21).toNat ≤ 9 := hLhi
      omega
    have hadd := word_add_toNat (s.mem.get 21) 48 hsum
    have ht : (s19.mem.get 21).toNat = (s.mem.get 21).toNat + 48 := hq ▸ hadd
    intro heq
    have : (s19.mem.get 21).toNat = 48 := by simp [heq]
    omega

  have g19 : ∀ k : Nat, 570 ≤ k → k < 867 →
      s19.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n24 : UInt16.ofNat k ≠ (24 : Word) := by
      have : (24 : Word) = UInt16.ofNat 24 := rfl
      rw [this]; exact ofNat_ne k 24 (by omega) (by decide) (by omega)
    have n20 : UInt16.ofNat k ≠ (20 : Word) := by
      have : (20 : Word) = UInt16.ofNat 20 := rfl
      rw [this]; exact ofNat_ne k 20 (by omega) (by decide) (by omega)
    have n21 : UInt16.ofNat k ≠ (21 : Word) := by
      have : (21 : Word) = UInt16.ofNat 21 := rfl
      rw [this]; exact ofNat_ne k 21 (by omega) (by decide) (by omega)
    have n22 : UInt16.ofNat k ≠ (22 : Word) := by
      have : (22 : Word) = UInt16.ofNat 22 := rfl
      rw [this]; exact ofNat_ne k 22 (by omega) (by decide) (by omega)
    have n23 : UInt16.ofNat k ≠ (23 : Word) := by
      have : (23 : Word) = UInt16.ofNat 23 := rfl
      rw [this]; exact ofNat_ne k 23 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresA (UInt16.ofNat k) n24 n20 n21 n22 n23 n0).trans
      (hcode k (by omega) (by omega))
  have hn := ndig_four (s := s19) hs19pc hs19h hs19Z hONE19 hK48_19
    hQ20A hloA hhiA hneA g19
  have hrunN : runN s 50 = runN s19 31 := runN_add_eq s 19 31 50 (by decide)
  let sN := runN s 50
  have hsNpc : sN.pc = 867 := by
    have : sN = runN s19 31 := hrunN; rw [this]; exact hn.1
  have hsNh : sN.halted = false := by
    have : sN = runN s19 31 := hrunN; rw [this]; exact hn.2.1
  have hsNZ : sN.mem.get 0 = 0 := by
    have : sN = runN s19 31 := hrunN; rw [this]; exact hn.2.2.1
  have hsNN : sN.mem.get 25 = 4 := by
    have : sN = runN s19 31 := hrunN; rw [this]; exact hn.2.2.2.1
  have hpresNraw := hn.2.2.2.2
  have hpresN : ∀ a, a ≠ 18 → a ≠ 25 → a ≠ 31 → a ≠ 0 → sN.mem.get a = s19.mem.get a := by
    intro a ha18 ha25 ha31 ha0
    have : sN = runN s19 31 := hrunN
    rw [this]; exact hpresNraw a ha18 ha25 ha31 ha0
  have hONE_N : sN.mem.get 3 = 1 := (hpresN 3 (by decide) (by decide) (by decide) (by decide)).trans hONE19
  have hK5_N : sN.mem.get 2322 = 5 :=
    (hpresN 2322 (by decide) (by decide) (by decide) (by decide)).trans ((hpresA 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5)
  have hK45_N : sN.mem.get 9 = 45 :=
    (hpresN 9 (by decide) (by decide) (by decide) (by decide)).trans ((hpresA 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK45)
  have hSlo_N : 0 < (sN.mem.get 19).toNat := by
    have : sN.mem.get 19 = s.mem.get 19 :=
      (hpresN 19 (by decide) (by decide) (by decide) (by decide)).trans (hpresA 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hSlo
  have hShi_N : (sN.mem.get 19).toNat < 32768 := by
    have : sN.mem.get 19 = s.mem.get 19 :=
      (hpresN 19 (by decide) (by decide) (by decide) (by decide)).trans (hpresA 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hShi
  have hW_N : sN.mem.get 14 = 0 :=
    (hpresN 14 (by decide) (by decide) (by decide) (by decide)).trans ((hpresA 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hW)
  have hClo_N : 0 < (sN.mem.get 13).toNat := by
    have : sN.mem.get 13 = s.mem.get 13 :=
      (hpresN 13 (by decide) (by decide) (by decide) (by decide)).trans (hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hClo
  have hChi_N : (sN.mem.get 13).toNat < 32768 := by
    have : sN.mem.get 13 = s.mem.get 13 :=
      (hpresN 13 (by decide) (by decide) (by decide) (by decide)).trans (hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hChi
  have hLlt_N : (5 : Nat) < (sN.mem.get 13).toNat := by
    have : sN.mem.get 13 = s.mem.get 13 :=
      (hpresN 13 (by decide) (by decide) (by decide) (by decide)).trans (hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hLlt
  have gN : ∀ k : Nat, 867 ≤ k → k < 2319 →
      sN.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n25 : UInt16.ofNat k ≠ (25 : Word) := by
      have : (25 : Word) = UInt16.ofNat 25 := rfl
      rw [this]; exact ofNat_ne k 25 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    have n24 : UInt16.ofNat k ≠ (24 : Word) := by
      have : (24 : Word) = UInt16.ofNat 24 := rfl
      rw [this]; exact ofNat_ne k 24 (by omega) (by decide) (by omega)
    have n20 : UInt16.ofNat k ≠ (20 : Word) := by
      have : (20 : Word) = UInt16.ofNat 20 := rfl
      rw [this]; exact ofNat_ne k 20 (by omega) (by decide) (by omega)
    have n21 : UInt16.ofNat k ≠ (21 : Word) := by
      have : (21 : Word) = UInt16.ofNat 21 := rfl
      rw [this]; exact ofNat_ne k 21 (by omega) (by decide) (by omega)
    have n22 : UInt16.ofNat k ≠ (22 : Word) := by
      have : (22 : Word) = UInt16.ofNat 22 := rfl
      rw [this]; exact ofNat_ne k 22 (by omega) (by decide) (by omega)
    have n23 : UInt16.ofNat k ≠ (23 : Word) := by
      have : (23 : Word) = UInt16.ofNat 23 := rfl
      rw [this]; exact ofNat_ne k 23 (by omega) (by decide) (by omega)
    exact (hpresN (UInt16.ofNat k)
        n18 n25 n31 n0).trans
      ((hpresA (UInt16.ofNat k)
        n24 n20 n21 n22 n23 n0).trans
      (hcode k (by omega) (by omega)))
  have hd := have_dig_signed_ndig4_done (s := sN) hsNpc hsNh hsNZ hONE_N hK5_N hK45_N
    hSlo_N hShi_N hW_N hsNN hClo_N hChi_N hLlt_N gN
  have hrun : sD = runN sN 527 := runN_add_eq s 50 527 577 (by decide)
  have hsD32 : sD.mem.get 32 = 45 := by rw [hrun]; exact hd.2.2.2.1
  have hsD33 : sD.mem.get 33 = s.mem.get 21 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 21 = s19.mem.get 21 := hpresN 21 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.2.1).trans (h1.trans ha.2.2.2.2.2.1)
  have hsD34 : sD.mem.get 34 = s.mem.get 22 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 22 = s19.mem.get 22 := hpresN 22 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.2.2.1).trans (h1.trans ha.2.2.2.2.2.2.1)
  have hsD35 : sD.mem.get 35 = s.mem.get 23 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 23 = s19.mem.get 23 := hpresN 23 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.2.2.2.1).trans (h1.trans ha.2.2.2.2.2.2.2.1)
  have hsD36 : sD.mem.get 36 = s.mem.get 17 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 24 = s19.mem.get 24 := hpresN 24 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.2.2.2.2.1).trans (h1.trans ha.2.2.2.1)
  have hsDNUL : sD.mem.get 37 = 0 := by rw [hrun]; exact hd.2.2.2.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 5 := by rw [hrun]; exact hd.2.2.2.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 5 := by rw [hrun]; exact hd.2.2.2.2.2.2.2.2.2.2.1
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hd.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hd.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hd.2.2.1
  have hpresw := hd.2.2.2.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha26 ha16 ha27 ha28 ha24 ha20 ha21 ha22 ha23 ha25
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha35 ha36 ha37 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha26 ha16 ha27 ha28).trans
      ((hpresN a ha18 ha25 ha31 ha0).trans
        (hpresA a ha24 ha20 ha21 ha22 ha23 ha0))
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsD35, hsD36, hsDNUL, hsDI, hsDL, hpres⟩

end IntFmt
