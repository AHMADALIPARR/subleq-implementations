/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

NDIG = 5 compositions, split into small intermediate lemmas so the
elaborator does not have to apply the packaged
`emit_ndig5_*_write_nul_done` theorems from `AFTER_PAD`.
Block lemmas, not an end-to-end theorem.
-/

import IntFmt.HaveDigHalt
import IntFmt.SignHalt

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

/-- `AFTER_PAD` / `SIGN = 0` / `NDIG = 5` / `IDX = 0` through `EMIT_DIGS`
to `AFTER_DIGS`. 456 steps. -/
theorem after_pad_sign0_ndig5_to_after_digs {s : Machine}
    (hpc : s.pc = 1077)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hS : s.mem.get 19 = 0)
    (hN : s.mem.get 25 = 5)
    (hI : s.mem.get 29 = 0)
    (hRlo : 4 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1077 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sA := runN s 456
    sA.pc = 1905 ∧
    sA.halted = false ∧
    sA.mem.get 0 = 0 ∧
    sA.mem.get 32 = s.mem.get 20 ∧
    sA.mem.get 33 = s.mem.get 21 ∧
    sA.mem.get 34 = s.mem.get 22 ∧
    sA.mem.get 35 = s.mem.get 23 ∧
    sA.mem.get 36 = s.mem.get 24 ∧
    sA.mem.get 29 = 5 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      sA.mem.get a = s.mem.get a) := by
  intro sA
  have ha := after_pad_sign0 (s := s) hpc hh hZ hS
    (fun k h1 h2 => hcode k (by omega) (by omega))
    (fun k h1 h2 => hcode k (by omega) (by omega))
  let s6 := runN s 6
  have hs6pc : s6.pc = 1575 := ha.1
  have hs6h : s6.halted = false := ha.2.1
  have hs6Z : s6.mem.get 0 = 0 := ha.2.2.1
  have hpres6 := ha.2.2.2.2
  have hONE6 : s6.mem.get 3 = 1 := (hpres6 3 (by decide) (by decide)).trans hONE
  have hK56 : s6.mem.get 2322 = 5 := (hpres6 2322 (by decide) (by decide)).trans hK5
  have hN6 : s6.mem.get 25 = 5 := (hpres6 25 (by decide) (by decide)).trans hN
  have hI6 : s6.mem.get 29 = 0 := (hpres6 29 (by decide) (by decide)).trans hI
  have hRlo6 : 4 < (s6.mem.get 28).toNat := by
    have : s6.mem.get 28 = s.mem.get 28 := hpres6 28 (by decide) (by decide)
    rw [this]; exact hRlo
  have hRhi6 : (s6.mem.get 28).toNat < 32768 := by
    have : s6.mem.get 28 = s.mem.get 28 := hpres6 28 (by decide) (by decide)
    rw [this]; exact hRhi
  have g6 : ∀ k : Nat, 1185 ≤ k → k < 1905 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have he := emit_ndig5_idx0 (s := s6) hs6pc hs6h hs6Z hONE6 hK56 hN6 hI6 hRlo6 hRhi6 g6
  have hrun : sA = runN s6 450 := runN_add_eq s 6 450 456 (by decide)
  have hsApc : sA.pc = 1905 := by rw [hrun]; exact he.1
  have hsAh : sA.halted = false := by rw [hrun]; exact he.2.1
  have hsAZ : sA.mem.get 0 = 0 := by rw [hrun]; exact he.2.2.1
  have hsA32 : sA.mem.get 32 = s.mem.get 20 := by
    rw [hrun]; exact (he.2.2.2.1).trans (hpres6 20 (by decide) (by decide))
  have hsA33 : sA.mem.get 33 = s.mem.get 21 := by
    rw [hrun]; exact (he.2.2.2.2.1).trans (hpres6 21 (by decide) (by decide))
  have hsA34 : sA.mem.get 34 = s.mem.get 22 := by
    rw [hrun]; exact (he.2.2.2.2.2.1).trans (hpres6 22 (by decide) (by decide))
  have hsA35 : sA.mem.get 35 = s.mem.get 23 := by
    rw [hrun]; exact (he.2.2.2.2.2.2.1).trans (hpres6 23 (by decide) (by decide))
  have hsA36 : sA.mem.get 36 = s.mem.get 24 := by
    rw [hrun]; exact (he.2.2.2.2.2.2.2.1).trans (hpres6 24 (by decide) (by decide))
  have hsAI : sA.mem.get 29 = 5 := by rw [hrun]; exact he.2.2.2.2.2.2.2.2.1
  have hprese := he.2.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      sA.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hprese a ha32 ha33 ha34 ha35 ha36 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpres6 a ha18 ha0)
  exact ⟨hsApc, hsAh, hsAZ, hsA32, hsA33, hsA34, hsA35, hsA36, hsAI, hpres⟩

/-- `AFTER_PAD` / `SIGN = 0` / `NDIG = 5` through `WRITE_NUL` / `DONE`.
494 steps. -/
theorem after_pad_sign0_ndig5_done {s : Machine}
    (hpc : s.pc = 1077)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hS : s.mem.get 19 = 0)
    (hN : s.mem.get 25 = 5)
    (hI : s.mem.get 29 = 0)
    (hL : s.mem.get 16 = 5)
    (hRlo : 4 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (5 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1077 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 494
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = s.mem.get 20 ∧
    sD.mem.get 33 = s.mem.get 21 ∧
    sD.mem.get 34 = s.mem.get 22 ∧
    sD.mem.get 35 = s.mem.get 23 ∧
    sD.mem.get 36 = s.mem.get 24 ∧
    sD.mem.get 37 = 0 ∧
    sD.mem.get 29 = 5 ∧
    sD.mem.get 16 = 5 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      sD.mem.get a = s.mem.get a) := by
  intro sD
  have ha := after_pad_sign0_ndig5_to_after_digs (s := s) hpc hh hZ hONE hK5 hS hN hI hRlo hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let sA := runN s 456
  have hsApc : sA.pc = 1905 := ha.1
  have hsAh : sA.halted = false := ha.2.1
  have hsAZ : sA.mem.get 0 = 0 := ha.2.2.1
  have hpresA := ha.2.2.2.2.2.2.2.2.2
  have hONEA : sA.mem.get 3 = 1 := (hpresA 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hLA : sA.mem.get 16 = 5 := (hpresA 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL
  have hLltA : (5 : Nat) < (sA.mem.get 13).toNat := by
    have : sA.mem.get 13 = s.mem.get 13 := hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hLlt
  have hChiA : (sA.mem.get 13).toNat < 32768 := by
    have : sA.mem.get 13 = s.mem.get 13 := hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hChi
  have gA : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      sA.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresA (UInt16.ofNat k) n32 n33 n34 n35 n36 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans
      (hcode k (by omega) (by omega))
  have hw := after_digs_write_nul_done_len5 (s := sA) hsApc hsAh hsAZ hONEA hLA hLltA hChiA gA
  have hrun : sD = runN sA 38 := runN_add_eq s 456 38 494 (by decide)
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsD32 : sD.mem.get 32 = s.mem.get 20 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha.2.2.2.1
  have hsD33 : sD.mem.get 33 = s.mem.get 21 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha.2.2.2.2.1
  have hsD34 : sD.mem.get 34 = s.mem.get 22 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2 34 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha.2.2.2.2.2.1
  have hsD35 : sD.mem.get 35 = s.mem.get 23 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2 35 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha.2.2.2.2.2.2.1
  have hsD36 : sD.mem.get 36 = s.mem.get 24 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2 36 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha.2.2.2.2.2.2.2.1
  have hsDNUL : sD.mem.get 37 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 5 := by rw [hrun]; exact hw.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 5 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha37 ha18 ha30 ha29 ha0).trans
      (hpresA a ha32 ha33 ha34 ha35 ha36 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsD35, hsD36, hsDNUL, hsDI, hsDL, hpres⟩

/-- `AFTER_PAD` / `SIGN ≠ 0` / `NDIG = 5` / `IDX = 0` through the minus
path and `EMIT_DIGS` to `AFTER_DIGS`. 511 steps. -/
theorem after_pad_minus_ndig5_to_after_digs {s : Machine}
    (hpc : s.pc = 1077)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hK45 : s.mem.get 9 = 45)
    (hN : s.mem.get 25 = 5)
    (hI : s.mem.get 29 = 0)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hRlo0 : 0 < (s.mem.get 28).toNat)
    (hRlo : 5 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1077 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sA := runN s 511
    sA.pc = 1905 ∧
    sA.halted = false ∧
    sA.mem.get 0 = 0 ∧
    sA.mem.get 32 = 45 ∧
    sA.mem.get 33 = s.mem.get 20 ∧
    sA.mem.get 34 = s.mem.get 21 ∧
    sA.mem.get 35 = s.mem.get 22 ∧
    sA.mem.get 36 = s.mem.get 23 ∧
    sA.mem.get 37 = s.mem.get 24 ∧
    sA.mem.get 29 = 6 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      sA.mem.get a = s.mem.get a) := by
  intro sA
  have hm := after_pad_minus_to_emit_idx0 (s := s) hpc hh hZ hONE hK45 hI hSlo hShi hRlo0 hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s51 := runN s 51
  have hs51pc : s51.pc = 1575 := hm.1
  have hs51h : s51.halted = false := hm.2.1
  have hs51Z : s51.mem.get 0 = 0 := hm.2.2.1
  have hpres51 := hm.2.2.2.2.2
  have hONE51 : s51.mem.get 3 = 1 := (hpres51 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK551 : s51.mem.get 2322 = 5 := (hpres51 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hN51 : s51.mem.get 25 = 5 := (hpres51 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN
  have hI51 : s51.mem.get 29 = 1 := hm.2.2.2.2.1
  have hRlo51 : 5 < (s51.mem.get 28).toNat := by
    have : s51.mem.get 28 = s.mem.get 28 := hpres51 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRlo
  have hRhi51 : (s51.mem.get 28).toNat < 32768 := by
    have : s51.mem.get 28 = s.mem.get 28 := hpres51 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have g51 : ∀ k : Nat, 1185 ≤ k → k < 1905 →
      s51.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n32 : UInt16.ofNat k ≠ (32 : Word) := by
      have : (32 : Word) = UInt16.ofNat 32 := rfl
      rw [this]; exact ofNat_ne k 32 (by omega) (by decide) (by omega)
    have n29 : UInt16.ofNat k ≠ (29 : Word) := by
      have : (29 : Word) = UInt16.ofNat 29 := rfl
      rw [this]; exact ofNat_ne k 29 (by omega) (by decide) (by omega)
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
    exact (hpres51 (UInt16.ofNat k) n32 n29 n18 n30 n2319 n0).trans
      (hcode k (by omega) (by omega))
  have he := emit_ndig5_idx1 (s := s51) hs51pc hs51h hs51Z hONE51 hK551 hN51 hI51 hRlo51 hRhi51 g51
  have hrun : sA = runN s51 460 := runN_add_eq s 51 460 511 (by decide)
  have hsApc : sA.pc = 1905 := by rw [hrun]; exact he.1
  have hsAh : sA.halted = false := by rw [hrun]; exact he.2.1
  have hsAZ : sA.mem.get 0 = 0 := by rw [hrun]; exact he.2.2.1
  have hsA32 : sA.mem.get 32 = 45 := by
    rw [hrun]
    have h1 : s51.mem.get 32 = 45 := hm.2.2.2.1
    exact (he.2.2.2.2.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1
  have hsA33 : sA.mem.get 33 = s.mem.get 20 := by
    rw [hrun]; exact (he.2.2.2.1).trans (hpres51 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsA34 : sA.mem.get 34 = s.mem.get 21 := by
    rw [hrun]; exact (he.2.2.2.2.1).trans (hpres51 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsA35 : sA.mem.get 35 = s.mem.get 22 := by
    rw [hrun]; exact (he.2.2.2.2.2.1).trans (hpres51 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsA36 : sA.mem.get 36 = s.mem.get 23 := by
    rw [hrun]; exact (he.2.2.2.2.2.2.1).trans (hpres51 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsA37 : sA.mem.get 37 = s.mem.get 24 := by
    rw [hrun]; exact (he.2.2.2.2.2.2.2.1).trans (hpres51 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsAI : sA.mem.get 29 = 6 := by rw [hrun]; exact he.2.2.2.2.2.2.2.2.1
  have hprese := he.2.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      sA.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hprese a ha33 ha34 ha35 ha36 ha37 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpres51 a ha32 ha29 ha18 ha30 ha2319 ha0)
  exact ⟨hsApc, hsAh, hsAZ, hsA32, hsA33, hsA34, hsA35, hsA36, hsA37, hsAI, hpres⟩

/-- `AFTER_PAD` / `SIGN ≠ 0` / `NDIG = 5` through `WRITE_NUL` / `DONE`.
551 steps. -/
theorem after_pad_minus_ndig5_done {s : Machine}
    (hpc : s.pc = 1077)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hK45 : s.mem.get 9 = 45)
    (hN : s.mem.get 25 = 5)
    (hI : s.mem.get 29 = 0)
    (hL : s.mem.get 16 = 6)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hRlo0 : 0 < (s.mem.get 28).toNat)
    (hRlo : 5 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (6 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1077 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 551
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = 45 ∧
    sD.mem.get 33 = s.mem.get 20 ∧
    sD.mem.get 34 = s.mem.get 21 ∧
    sD.mem.get 35 = s.mem.get 22 ∧
    sD.mem.get 36 = s.mem.get 23 ∧
    sD.mem.get 37 = s.mem.get 24 ∧
    sD.mem.get 38 = 0 ∧
    sD.mem.get 29 = 6 ∧
    sD.mem.get 16 = 6 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 38 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      sD.mem.get a = s.mem.get a) := by
  intro sD
  have ha := after_pad_minus_ndig5_to_after_digs (s := s) hpc hh hZ hONE hK5 hK45 hN hI
    hSlo hShi hRlo0 hRlo hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let sA := runN s 511
  have hsApc : sA.pc = 1905 := ha.1
  have hsAh : sA.halted = false := ha.2.1
  have hsAZ : sA.mem.get 0 = 0 := ha.2.2.1
  have hpresA := ha.2.2.2.2.2.2.2.2.2.2
  have hONEA : sA.mem.get 3 = 1 := (hpresA 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hLA : sA.mem.get 16 = 6 := (hpresA 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL
  have hLltA : (6 : Nat) < (sA.mem.get 13).toNat := by
    have : sA.mem.get 13 = s.mem.get 13 := hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hLlt
  have hChiA : (sA.mem.get 13).toNat < 32768 := by
    have : sA.mem.get 13 = s.mem.get 13 := hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hChi
  have gA : ∀ k : Nat, 1905 ≤ k → k < 2319 →
      sA.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n30 : UInt16.ofNat k ≠ (30 : Word) := by
      have : (30 : Word) = UInt16.ofNat 30 := rfl
      rw [this]; exact ofNat_ne k 30 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2319 : UInt16.ofNat k ≠ (2319 : Word) := by
      have : (2319 : Word) = UInt16.ofNat 2319 := rfl
      rw [this]; exact ofNat_ne k 2319 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpresA (UInt16.ofNat k) n32 n33 n34 n35 n36 n37 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans
      (hcode k (by omega) (by omega))
  have hw := after_digs_write_nul_done_len6 (s := sA) hsApc hsAh hsAZ hONEA hLA hLltA hChiA gA
  have hrun : sD = runN sA 40 := runN_add_eq s 511 40 551 (by decide)
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsD32 : sD.mem.get 32 = 45 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha.2.2.2.1
  have hsD33 : sD.mem.get 33 = s.mem.get 20 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha.2.2.2.2.1
  have hsD34 : sD.mem.get 34 = s.mem.get 21 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2 34 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha.2.2.2.2.2.1
  have hsD35 : sD.mem.get 35 = s.mem.get 22 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2 35 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha.2.2.2.2.2.2.1
  have hsD36 : sD.mem.get 36 = s.mem.get 23 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2 36 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha.2.2.2.2.2.2.2.1
  have hsD37 : sD.mem.get 37 = s.mem.get 24 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2 37 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha.2.2.2.2.2.2.2.2.1
  have hsDNUL : sD.mem.get 38 = 0 := by rw [hrun]; exact hw.2.2.2.1
  have hsDI : sD.mem.get 29 = 6 := by rw [hrun]; exact hw.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 6 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 38 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha38 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha38 ha18 ha30 ha29 ha0).trans
      (hpresA a ha32 ha33 ha34 ha35 ha36 ha37 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsD35, hsD36, hsD37, hsDNUL, hsDI, hsDL, hpres⟩

/-- From `HAVE_DIG` with `SIGN = 0`, `WIDTH = 0`, `NDIG = 5`, and
`5 < CAP`. 529 steps. -/
theorem have_dig_unsigned_ndig5_done {s : Machine}
    (hpc : s.pc = 867)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hS : s.mem.get 19 = 0)
    (hW : s.mem.get 14 = 0)
    (hN : s.mem.get 25 = 5)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (5 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 867 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 529
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = s.mem.get 20 ∧
    sD.mem.get 33 = s.mem.get 21 ∧
    sD.mem.get 34 = s.mem.get 22 ∧
    sD.mem.get 35 = s.mem.get 23 ∧
    sD.mem.get 36 = s.mem.get 24 ∧
    sD.mem.get 37 = 0 ∧
    sD.mem.get 29 = 5 ∧
    sD.mem.get 16 = 5 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      sD.mem.get a = s.mem.get a) := by
  intro sD
  have hd := have_dig_to_after_pad_unsigned (s := s) hpc hh hZ hONE hS hW hClo hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s35 := runN s 35
  have hs35pc : s35.pc = 1077 := hd.1
  have hs35h : s35.halted = false := hd.2.1
  have hs35Z : s35.mem.get 0 = 0 := hd.2.2.1
  have hpres35 := hd.2.2.2.2.2.2.2.2
  have hL35 : s35.mem.get 16 = 5 := hd.2.2.2.2.1.trans hN
  have hI35 : s35.mem.get 29 = 0 := hd.2.2.2.2.2.2.2.1
  have hR35 : s35.mem.get 28 = s.mem.get 13 - 1 := hd.2.2.2.2.2.2.1
  have hONE35 : s35.mem.get 3 = 1 := (hpres35 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK535 : s35.mem.get 2322 = 5 := (hpres35 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hS35 : s35.mem.get 19 = 0 := (hpres35 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hS
  have hN35 : s35.mem.get 25 = 5 := (hpres35 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN
  have h1le : (1 : Nat) ≤ (s.mem.get 13).toNat := Nat.succ_le_of_lt hClo
  have hRtn : (s.mem.get 13 - 1).toNat = (s.mem.get 13).toNat - 1 :=
    word_sub_ge (s.mem.get 13) 1 (by
      have : (1 : Word).toNat = 1 := rfl
      exact this.symm ▸ h1le)
  have hRlo35 : 4 < (s35.mem.get 28).toNat := by
    rw [hR35, hRtn]; omega
  have hRhi35 : (s35.mem.get 28).toNat < 32768 := by
    rw [hR35, hRtn]; omega
  have hLlt35 : (5 : Nat) < (s35.mem.get 13).toNat := by
    have : s35.mem.get 13 = s.mem.get 13 := hpres35 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hLlt
  have hChi35 : (s35.mem.get 13).toNat < 32768 := by
    have : s35.mem.get 13 = s.mem.get 13 := hpres35 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hChi
  have g35 : ∀ k : Nat, 1077 ≤ k → k < 2319 →
      s35.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres35 (UInt16.ofNat k) n26 n18 n16 n27 n28 n29 n0).trans
      (hcode k (by omega) (by omega))
  have hw := after_pad_sign0_ndig5_done (s := s35) hs35pc hs35h hs35Z hONE35 hK535 hS35 hN35
    hI35 hL35 hRlo35 hRhi35 hLlt35 hChi35 g35
  have hrun : sD = runN s35 494 := runN_add_eq s 35 494 529 (by decide)
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsD32 : sD.mem.get 32 = s.mem.get 20 := by
    rw [hrun]; exact (hw.2.2.2.1).trans (hpres35 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD33 : sD.mem.get 33 = s.mem.get 21 := by
    rw [hrun]; exact (hw.2.2.2.2.1).trans (hpres35 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD34 : sD.mem.get 34 = s.mem.get 22 := by
    rw [hrun]; exact (hw.2.2.2.2.2.1).trans (hpres35 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD35 : sD.mem.get 35 = s.mem.get 23 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2.1).trans (hpres35 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD36 : sD.mem.get 36 = s.mem.get 24 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2.2.1).trans (hpres35 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsDNUL : sD.mem.get 37 = 0 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 5 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 5 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha35 ha36 ha37 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpres35 a ha26 ha18 ha16 ha27 ha28 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsD35, hsD36, hsDNUL, hsDI, hsDL, hpres⟩

/-- From `HAVE_DIG` with `SIGN ≠ 0`, `WIDTH = 0`, `NDIG = 5`, and
`6 < CAP`. 589 steps. -/
theorem have_dig_signed_ndig5_done {s : Machine}
    (hpc : s.pc = 867)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hK45 : s.mem.get 9 = 45)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hW : s.mem.get 14 = 0)
    (hN : s.mem.get 25 = 5)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (6 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 867 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 589
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = 45 ∧
    sD.mem.get 33 = s.mem.get 20 ∧
    sD.mem.get 34 = s.mem.get 21 ∧
    sD.mem.get 35 = s.mem.get 22 ∧
    sD.mem.get 36 = s.mem.get 23 ∧
    sD.mem.get 37 = s.mem.get 24 ∧
    sD.mem.get 38 = 0 ∧
    sD.mem.get 29 = 6 ∧
    sD.mem.get 16 = 6 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 38 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      sD.mem.get a = s.mem.get a) := by
  intro sD
  have hd := have_dig_to_after_pad_signed (s := s) hpc hh hZ hONE hSlo hShi hW hClo hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s38 := runN s 38
  have hs38pc : s38.pc = 1077 := hd.1
  have hs38h : s38.halted = false := hd.2.1
  have hs38Z : s38.mem.get 0 = 0 := hd.2.2.1
  have hpres38 := hd.2.2.2.2.2.2.2.2
  have hL38 : s38.mem.get 16 = 6 := by
    have : s38.mem.get 16 = s.mem.get 25 + 1 := hd.2.2.2.2.1
    rw [this, hN]
    exact (rfl : (5 : Word) + 1 = 6)
  have hI38 : s38.mem.get 29 = 0 := hd.2.2.2.2.2.2.2.1
  have hR38 : s38.mem.get 28 = s.mem.get 13 - 1 := hd.2.2.2.2.2.2.1
  have hONE38 : s38.mem.get 3 = 1 := (hpres38 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK538 : s38.mem.get 2322 = 5 := (hpres38 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hK4538 : s38.mem.get 9 = 45 := (hpres38 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK45
  have hN38 : s38.mem.get 25 = 5 := (hpres38 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN
  have hSlo38 : 0 < (s38.mem.get 19).toNat := by
    have : s38.mem.get 19 = s.mem.get 19 := hpres38 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hSlo
  have hShi38 : (s38.mem.get 19).toNat < 32768 := by
    have : s38.mem.get 19 = s.mem.get 19 := hpres38 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hShi
  have h1le : (1 : Word).toNat ≤ (s.mem.get 13).toNat := by
    have : (1 : Word).toNat = 1 := rfl
    omega
  have hRtn : (s.mem.get 13 - 1).toNat = (s.mem.get 13).toNat - 1 :=
    word_sub_ge (s.mem.get 13) 1 h1le
  have hRlo0 : 0 < (s38.mem.get 28).toNat := by rw [hR38, hRtn]; omega
  have hRlo38 : 5 < (s38.mem.get 28).toNat := by rw [hR38, hRtn]; omega
  have hRhi38 : (s38.mem.get 28).toNat < 32768 := by rw [hR38, hRtn]; omega
  have hLlt38 : (6 : Nat) < (s38.mem.get 13).toNat := by
    have : s38.mem.get 13 = s.mem.get 13 := hpres38 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hLlt
  have hChi38 : (s38.mem.get 13).toNat < 32768 := by
    have : s38.mem.get 13 = s.mem.get 13 := hpres38 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hChi
  have g38 : ∀ k : Nat, 1077 ≤ k → k < 2319 →
      s38.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres38 (UInt16.ofNat k) n26 n18 n16 n27 n28 n29 n0).trans
      (hcode k (by omega) (by omega))
  have hw := after_pad_minus_ndig5_done (s := s38) hs38pc hs38h hs38Z hONE38 hK538 hK4538
    hN38 hI38 hL38 hSlo38 hShi38 hRlo0 hRlo38 hRhi38 hLlt38 hChi38 g38
  have hrun : sD = runN s38 551 := runN_add_eq s 38 551 589 (by decide)
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsD32 : sD.mem.get 32 = 45 := by rw [hrun]; exact hw.2.2.2.1
  have hsD33 : sD.mem.get 33 = s.mem.get 20 := by
    rw [hrun]; exact (hw.2.2.2.2.1).trans (hpres38 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD34 : sD.mem.get 34 = s.mem.get 21 := by
    rw [hrun]; exact (hw.2.2.2.2.2.1).trans (hpres38 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD35 : sD.mem.get 35 = s.mem.get 22 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2.1).trans (hpres38 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD36 : sD.mem.get 36 = s.mem.get 23 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2.2.1).trans (hpres38 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD37 : sD.mem.get 37 = s.mem.get 24 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2.2.2.1).trans (hpres38 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsDNUL : sD.mem.get 38 = 0 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 6 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 6 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 38 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha38 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha35 ha36 ha37 ha38 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpres38 a ha26 ha18 ha16 ha27 ha28 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsD35, hsD36, hsD37, hsDNUL, hsDI, hsDL, hpres⟩

/-- From `P3_DONE` with `Q0` a nonzero digit, `SIGN = 0`, `WIDTH = 0`,
and `5 < CAP`: ASCII-convert, `NDIG = 5`, emit, NUL-terminate, and
halt. 576 steps. -/
theorem p3_done_unsigned_ndig5_done {s : Machine}
    (hpc : s.pc = 513)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK48 : s.mem.get 8 = 48)
    (hK5 : s.mem.get 2322 = 5)
    (hS : s.mem.get 19 = 0)
    (hW : s.mem.get 14 = 0)
    (hLlo : 0 < (s.mem.get 20).toNat)
    (hLhi : (s.mem.get 20).toNat ≤ 9)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (5 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 513 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 576
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = s.mem.get 20 + 48 ∧
    sD.mem.get 33 = s.mem.get 21 + 48 ∧
    sD.mem.get 34 = s.mem.get 22 + 48 ∧
    sD.mem.get 35 = s.mem.get 23 + 48 ∧
    sD.mem.get 36 = s.mem.get 17 + 48 ∧
    sD.mem.get 37 = 0 ∧
    sD.mem.get 29 = 5 ∧
    sD.mem.get 16 = 5 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a) := by
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

  have hloA : 48 ≤ (s19.mem.get 20).toNat := by
    have hq : s19.mem.get 20 = s.mem.get 20 + 48 := ha.2.2.2.2.1
    have hsum : (s.mem.get 20).toNat + 48 < 65536 := by
      have : (s.mem.get 20).toNat ≤ 9 := hLhi
      omega
    have hadd := word_add_toNat (s.mem.get 20) 48 hsum
    have ht : (s19.mem.get 20).toNat = (s.mem.get 20).toNat + 48 := hq ▸ hadd
    omega
  have hhiA : (s19.mem.get 20).toNat ≤ 57 := by
    have hq : s19.mem.get 20 = s.mem.get 20 + 48 := ha.2.2.2.2.1
    have hsum : (s.mem.get 20).toNat + 48 < 65536 := by
      have : (s.mem.get 20).toNat ≤ 9 := hLhi
      omega
    have hadd := word_add_toNat (s.mem.get 20) 48 hsum
    have ht : (s19.mem.get 20).toNat = (s.mem.get 20).toNat + 48 := hq ▸ hadd
    omega
  have hneA : s19.mem.get 20 ≠ 48 := by
    have hq : s19.mem.get 20 = s.mem.get 20 + 48 := ha.2.2.2.2.1
    have hsum : (s.mem.get 20).toNat + 48 < 65536 := by
      have : (s.mem.get 20).toNat ≤ 9 := hLhi
      omega
    have hadd := word_add_toNat (s.mem.get 20) 48 hsum
    have ht : (s19.mem.get 20).toNat = (s.mem.get 20).toNat + 48 := hq ▸ hadd
    intro heq
    have : (s19.mem.get 20).toNat = 48 := by simp [heq]
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
  have hn := ndig_five (s := s19) hs19pc hs19h hs19Z hONE19 hK48_19 hloA hhiA hneA g19
  have hrunN : runN s 47 = runN s19 28 := runN_add_eq s 19 28 47 (by decide)
  let sN := runN s 47
  have hsNpc : sN.pc = 867 := by
    have : sN = runN s19 28 := hrunN; rw [this]; exact hn.1
  have hsNh : sN.halted = false := by
    have : sN = runN s19 28 := hrunN; rw [this]; exact hn.2.1
  have hsNZ : sN.mem.get 0 = 0 := by
    have : sN = runN s19 28 := hrunN; rw [this]; exact hn.2.2.1
  have hsNN : sN.mem.get 25 = 5 := by
    have : sN = runN s19 28 := hrunN; rw [this]; exact hn.2.2.2.1
  have hpresNraw := hn.2.2.2.2
  have hpresN : ∀ a, a ≠ 18 → a ≠ 25 → a ≠ 31 → a ≠ 0 → sN.mem.get a = s19.mem.get a := by
    intro a ha18 ha25 ha31 ha0
    have : sN = runN s19 28 := hrunN
    rw [this]; exact hpresNraw a ha18 ha25 ha31 ha0
  have hONE_N : sN.mem.get 3 = 1 := (hpresN 3 (by decide) (by decide) (by decide) (by decide)).trans hONE19
  have hK5_N : sN.mem.get 2322 = 5 :=
    (hpresN 2322 (by decide) (by decide) (by decide) (by decide)).trans ((hpresA 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5)
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
    exact (hpresN (UInt16.ofNat k) n18 n25 n31 n0).trans
      ((hpresA (UInt16.ofNat k) n24 n20 n21 n22 n23 n0).trans
      (hcode k (by omega) (by omega)))

  have hS_N : sN.mem.get 19 = 0 :=
    (hpresN 19 (by decide) (by decide) (by decide) (by decide)).trans ((hpresA 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hS)
  have hLlt_N : (5 : Nat) < (sN.mem.get 13).toNat := by
    have : sN.mem.get 13 = s.mem.get 13 :=
      (hpresN 13 (by decide) (by decide) (by decide) (by decide)).trans (hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hLlt
  have hd := have_dig_unsigned_ndig5_done (s := sN) hsNpc hsNh hsNZ hONE_N hK5_N hS_N hW_N hsNN
    hClo_N hChi_N hLlt_N gN
  have hrun : sD = runN sN 529 := runN_add_eq s 47 529 576 (by decide)
  have hsD32 : sD.mem.get 32 = s.mem.get 20 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 20 = s19.mem.get 20 := hpresN 20 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.1).trans (h1.trans ha.2.2.2.2.1)
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
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha24 ha20 ha21 ha22 ha23 ha25
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha35 ha36 ha37 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      ((hpresN a ha18 ha25 ha31 ha0).trans
        (hpresA a ha24 ha20 ha21 ha22 ha23 ha0))
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsD35, hsD36, hsDNUL, hsDI, hsDL, hpres⟩


/-- From `P3_DONE` with `Q0` a nonzero digit, `SIGN ≠ 0`, `WIDTH = 0`,
and `6 < CAP`: ASCII-convert, write a leading minus, emit, NUL-terminate,
and halt. 636 steps. -/
theorem p3_done_signed_ndig5_done {s : Machine}
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
    (hLlo : 0 < (s.mem.get 20).toNat)
    (hLhi : (s.mem.get 20).toNat ≤ 9)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (6 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 513 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 636
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = 45 ∧
    sD.mem.get 33 = s.mem.get 20 + 48 ∧
    sD.mem.get 34 = s.mem.get 21 + 48 ∧
    sD.mem.get 35 = s.mem.get 22 + 48 ∧
    sD.mem.get 36 = s.mem.get 23 + 48 ∧
    sD.mem.get 37 = s.mem.get 17 + 48 ∧
    sD.mem.get 38 = 0 ∧
    sD.mem.get 29 = 6 ∧
    sD.mem.get 16 = 6 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 38 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a) := by
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

  have hloA : 48 ≤ (s19.mem.get 20).toNat := by
    have hq : s19.mem.get 20 = s.mem.get 20 + 48 := ha.2.2.2.2.1
    have hsum : (s.mem.get 20).toNat + 48 < 65536 := by
      have : (s.mem.get 20).toNat ≤ 9 := hLhi
      omega
    have hadd := word_add_toNat (s.mem.get 20) 48 hsum
    have ht : (s19.mem.get 20).toNat = (s.mem.get 20).toNat + 48 := hq ▸ hadd
    omega
  have hhiA : (s19.mem.get 20).toNat ≤ 57 := by
    have hq : s19.mem.get 20 = s.mem.get 20 + 48 := ha.2.2.2.2.1
    have hsum : (s.mem.get 20).toNat + 48 < 65536 := by
      have : (s.mem.get 20).toNat ≤ 9 := hLhi
      omega
    have hadd := word_add_toNat (s.mem.get 20) 48 hsum
    have ht : (s19.mem.get 20).toNat = (s.mem.get 20).toNat + 48 := hq ▸ hadd
    omega
  have hneA : s19.mem.get 20 ≠ 48 := by
    have hq : s19.mem.get 20 = s.mem.get 20 + 48 := ha.2.2.2.2.1
    have hsum : (s.mem.get 20).toNat + 48 < 65536 := by
      have : (s.mem.get 20).toNat ≤ 9 := hLhi
      omega
    have hadd := word_add_toNat (s.mem.get 20) 48 hsum
    have ht : (s19.mem.get 20).toNat = (s.mem.get 20).toNat + 48 := hq ▸ hadd
    intro heq
    have : (s19.mem.get 20).toNat = 48 := by simp [heq]
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
  have hn := ndig_five (s := s19) hs19pc hs19h hs19Z hONE19 hK48_19 hloA hhiA hneA g19
  have hrunN : runN s 47 = runN s19 28 := runN_add_eq s 19 28 47 (by decide)
  let sN := runN s 47
  have hsNpc : sN.pc = 867 := by
    have : sN = runN s19 28 := hrunN; rw [this]; exact hn.1
  have hsNh : sN.halted = false := by
    have : sN = runN s19 28 := hrunN; rw [this]; exact hn.2.1
  have hsNZ : sN.mem.get 0 = 0 := by
    have : sN = runN s19 28 := hrunN; rw [this]; exact hn.2.2.1
  have hsNN : sN.mem.get 25 = 5 := by
    have : sN = runN s19 28 := hrunN; rw [this]; exact hn.2.2.2.1
  have hpresNraw := hn.2.2.2.2
  have hpresN : ∀ a, a ≠ 18 → a ≠ 25 → a ≠ 31 → a ≠ 0 → sN.mem.get a = s19.mem.get a := by
    intro a ha18 ha25 ha31 ha0
    have : sN = runN s19 28 := hrunN
    rw [this]; exact hpresNraw a ha18 ha25 ha31 ha0
  have hONE_N : sN.mem.get 3 = 1 := (hpresN 3 (by decide) (by decide) (by decide) (by decide)).trans hONE19
  have hK5_N : sN.mem.get 2322 = 5 :=
    (hpresN 2322 (by decide) (by decide) (by decide) (by decide)).trans ((hpresA 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5)
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
    exact (hpresN (UInt16.ofNat k) n18 n25 n31 n0).trans
      ((hpresA (UInt16.ofNat k) n24 n20 n21 n22 n23 n0).trans
      (hcode k (by omega) (by omega)))

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
  have hLlt_N : (6 : Nat) < (sN.mem.get 13).toNat := by
    have : sN.mem.get 13 = s.mem.get 13 :=
      (hpresN 13 (by decide) (by decide) (by decide) (by decide)).trans (hpresA 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    rw [this]; exact hLlt
  have hd := have_dig_signed_ndig5_done (s := sN) hsNpc hsNh hsNZ hONE_N hK5_N hK45_N
    hSlo_N hShi_N hW_N hsNN hClo_N hChi_N hLlt_N gN
  have hrun : sD = runN sN 589 := runN_add_eq s 47 589 636 (by decide)
  have hsD32 : sD.mem.get 32 = 45 := by rw [hrun]; exact hd.2.2.2.1
  have hsD33 : sD.mem.get 33 = s.mem.get 20 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 20 = s19.mem.get 20 := hpresN 20 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.2.1).trans (h1.trans ha.2.2.2.2.1)
  have hsD34 : sD.mem.get 34 = s.mem.get 21 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 21 = s19.mem.get 21 := hpresN 21 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.2.2.1).trans (h1.trans ha.2.2.2.2.2.1)
  have hsD35 : sD.mem.get 35 = s.mem.get 22 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 22 = s19.mem.get 22 := hpresN 22 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.2.2.2.1).trans (h1.trans ha.2.2.2.2.2.2.1)
  have hsD36 : sD.mem.get 36 = s.mem.get 23 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 23 = s19.mem.get 23 := hpresN 23 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.2.2.2.2.1).trans (h1.trans ha.2.2.2.2.2.2.2.1)
  have hsD37 : sD.mem.get 37 = s.mem.get 17 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 24 = s19.mem.get 24 := hpresN 24 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.2.2.2.2.2.1).trans (h1.trans ha.2.2.2.1)
  have hsDNUL : sD.mem.get 38 = 0 := by rw [hrun]; exact hd.2.2.2.2.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 6 := by rw [hrun]; exact hd.2.2.2.2.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 6 := by rw [hrun]; exact hd.2.2.2.2.2.2.2.2.2.2.2.1
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hd.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hd.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hd.2.2.1
  have hpresw := hd.2.2.2.2.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 38 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha38 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha24 ha20 ha21 ha22 ha23 ha25
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha35 ha36 ha37 ha38 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      ((hpresN a ha18 ha25 ha31 ha0).trans
        (hpresA a ha24 ha20 ha21 ha22 ha23 ha0))
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsD35, hsD36, hsD37, hsDNUL, hsDI, hsDL, hpres⟩

end IntFmt
