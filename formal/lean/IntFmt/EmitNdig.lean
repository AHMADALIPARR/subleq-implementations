/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Per-`NDIG` `EMIT_DIGS`/`DIG_LOOP` compositions. Block lemmas, not
end-to-end correctness.
-/

import IntFmt.EmitDigs

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-- `DIG_LOOP` with `DI = SK = 0` and `IDX = 0 < ROOM`: take `Q0`,
store it, and return to `DIG_LOOP` with `DI = 1` and `IDX = 1`. 79 steps. -/
theorem loop_take_eq_di0_idx0 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 0)
    (hSK : s.mem.get 2320 = 0)
    (hI : s.mem.get 29 = 0)
    (hRlo : 0 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s79 := runN s 79
    s79.pc = 1641 ∧
    s79.halted = false ∧
    s79.mem.get 0 = 0 ∧
    s79.mem.get 32 = s.mem.get 20 ∧
    s79.mem.get 29 = 1 ∧
    s79.mem.get 2321 = 1 ∧
    (∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s79.mem.get a = s.mem.get a) := by
  intro s79
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 0 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = 0 := (hpres10 2320 (by decide) (by decide)).trans hSK
  have hI10 : s10.mem.get 29 = 0 := (hpres10 29 (by decide) (by decide)).trans hI
  have hR10 : s10.mem.get 28 = s.mem.get 28 := hpres10 28 (by decide) (by decide)
  have hQ10 : s10.mem.get 20 = s.mem.get 20 := hpres10 20 (by decide) (by decide)
  have hDI_eq : s10.mem.get 2321 = s10.mem.get 2320 := hs10DI.trans hSK10.symm
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1716 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_eq (s := s10) hs10pc hs10h hs10Z hONE10 hDI_eq g10
  have hrun21 : runN s 21 = runN s10 11 := runN_add_eq s 10 11 21 (by decide)
  let s21 := runN s 21
  have hs21eq : s21 = runN s10 11 := hrun21
  have hs21pc : s21.pc = 1716 := by rw [hs21eq]; exact htk.1
  have hs21h : s21.halted = false := by rw [hs21eq]; exact htk.2.1
  have hs21Z : s21.mem.get 0 = 0 := by rw [hs21eq]; exact htk.2.2.1
  have hs21DI : s21.mem.get 2321 = 0 := by rw [hs21eq, htk.2.2.2.1, hs10DI]
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs21eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE21 : s21.mem.get 3 = 1 := (hpres21 3 (by decide) (by decide)).trans hONE
  have hI21 : s21.mem.get 29 = 0 := (hpres21 29 (by decide) (by decide)).trans hI
  have hR21 : s21.mem.get 28 = s.mem.get 28 := hpres21 28 (by decide) (by decide)
  have hQ21 : s21.mem.get 20 = s.mem.get 20 := hpres21 20 (by decide) (by decide)
  have g21S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g21E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo21 : 0 < (s21.mem.get 28).toNat := by rw [hR21]; exact hRlo
  have hRhi21 : (s21.mem.get 28).toNat < 32768 := by rw [hR21]; exact hRhi
  have hts := take_store_next_di0_idx0 (s := s21) hs21pc hs21h hs21Z hONE21 hs21DI hI21 hRlo21 hRhi21 g21S g21E
  have hrun : s79 = runN s21 58 := runN_add_eq s 21 58 79 (by decide)
  have hsTpc : s79.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s79.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s79.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s79.mem.get 32 = s.mem.get 20 := by
    rw [hrun, hts.2.2.2.1, hQ21]
  have hsTI : s79.mem.get 29 = 1 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s79.mem.get 2321 = 1 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s79.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres21 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `DI = SK = 0` and `IDX = 1 < ROOM`: take `Q0`,
store it, and return to `DIG_LOOP` with `DI = 1` and `IDX = 2`. 81 steps. -/
theorem loop_take_eq_di0_idx1 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 0)
    (hSK : s.mem.get 2320 = 0)
    (hI : s.mem.get 29 = 1)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s81 := runN s 81
    s81.pc = 1641 ∧
    s81.halted = false ∧
    s81.mem.get 0 = 0 ∧
    s81.mem.get 33 = s.mem.get 20 ∧
    s81.mem.get 29 = 2 ∧
    s81.mem.get 2321 = 1 ∧
    (∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s81.mem.get a = s.mem.get a) := by
  intro s81
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 0 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = 0 := (hpres10 2320 (by decide) (by decide)).trans hSK
  have hI10 : s10.mem.get 29 = 1 := (hpres10 29 (by decide) (by decide)).trans hI
  have hR10 : s10.mem.get 28 = s.mem.get 28 := hpres10 28 (by decide) (by decide)
  have hQ10 : s10.mem.get 20 = s.mem.get 20 := hpres10 20 (by decide) (by decide)
  have hDI_eq : s10.mem.get 2321 = s10.mem.get 2320 := hs10DI.trans hSK10.symm
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1716 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_eq (s := s10) hs10pc hs10h hs10Z hONE10 hDI_eq g10
  have hrun21 : runN s 21 = runN s10 11 := runN_add_eq s 10 11 21 (by decide)
  let s21 := runN s 21
  have hs21eq : s21 = runN s10 11 := hrun21
  have hs21pc : s21.pc = 1716 := by rw [hs21eq]; exact htk.1
  have hs21h : s21.halted = false := by rw [hs21eq]; exact htk.2.1
  have hs21Z : s21.mem.get 0 = 0 := by rw [hs21eq]; exact htk.2.2.1
  have hs21DI : s21.mem.get 2321 = 0 := by rw [hs21eq, htk.2.2.2.1, hs10DI]
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs21eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE21 : s21.mem.get 3 = 1 := (hpres21 3 (by decide) (by decide)).trans hONE
  have hI21 : s21.mem.get 29 = 1 := (hpres21 29 (by decide) (by decide)).trans hI
  have hR21 : s21.mem.get 28 = s.mem.get 28 := hpres21 28 (by decide) (by decide)
  have hQ21 : s21.mem.get 20 = s.mem.get 20 := hpres21 20 (by decide) (by decide)
  have g21S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g21E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo21 : 1 < (s21.mem.get 28).toNat := by rw [hR21]; exact hRlo
  have hRhi21 : (s21.mem.get 28).toNat < 32768 := by rw [hR21]; exact hRhi
  have hts := take_store_next_di0_idx1 (s := s21) hs21pc hs21h hs21Z hONE21 hs21DI hI21 hRlo21 hRhi21 g21S g21E
  have hrun : s81 = runN s21 60 := runN_add_eq s 21 60 81 (by decide)
  have hsTpc : s81.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s81.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s81.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s81.mem.get 33 = s.mem.get 20 := by
    rw [hrun, hts.2.2.2.1, hQ21]
  have hsTI : s81.mem.get 29 = 2 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s81.mem.get 2321 = 1 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s81.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres21 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `DI = SK = 1` and `IDX = 0 < ROOM`: take `Q1`,
store it, and return to `DIG_LOOP` with `DI = 2` and `IDX = 1`. 81 steps. -/
theorem loop_take_eq_di1_idx0 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 1)
    (hSK : s.mem.get 2320 = 1)
    (hI : s.mem.get 29 = 0)
    (hRlo : 0 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s81 := runN s 81
    s81.pc = 1641 ∧
    s81.halted = false ∧
    s81.mem.get 0 = 0 ∧
    s81.mem.get 32 = s.mem.get 21 ∧
    s81.mem.get 29 = 1 ∧
    s81.mem.get 2321 = 2 ∧
    (∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s81.mem.get a = s.mem.get a) := by
  intro s81
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 1 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = 1 := (hpres10 2320 (by decide) (by decide)).trans hSK
  have hI10 : s10.mem.get 29 = 0 := (hpres10 29 (by decide) (by decide)).trans hI
  have hR10 : s10.mem.get 28 = s.mem.get 28 := hpres10 28 (by decide) (by decide)
  have hQ10 : s10.mem.get 21 = s.mem.get 21 := hpres10 21 (by decide) (by decide)
  have hDI_eq : s10.mem.get 2321 = s10.mem.get 2320 := hs10DI.trans hSK10.symm
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1716 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_eq (s := s10) hs10pc hs10h hs10Z hONE10 hDI_eq g10
  have hrun21 : runN s 21 = runN s10 11 := runN_add_eq s 10 11 21 (by decide)
  let s21 := runN s 21
  have hs21eq : s21 = runN s10 11 := hrun21
  have hs21pc : s21.pc = 1716 := by rw [hs21eq]; exact htk.1
  have hs21h : s21.halted = false := by rw [hs21eq]; exact htk.2.1
  have hs21Z : s21.mem.get 0 = 0 := by rw [hs21eq]; exact htk.2.2.1
  have hs21DI : s21.mem.get 2321 = 1 := by rw [hs21eq, htk.2.2.2.1, hs10DI]
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs21eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE21 : s21.mem.get 3 = 1 := (hpres21 3 (by decide) (by decide)).trans hONE
  have hI21 : s21.mem.get 29 = 0 := (hpres21 29 (by decide) (by decide)).trans hI
  have hR21 : s21.mem.get 28 = s.mem.get 28 := hpres21 28 (by decide) (by decide)
  have hQ21 : s21.mem.get 21 = s.mem.get 21 := hpres21 21 (by decide) (by decide)
  have g21S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g21E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo21 : 0 < (s21.mem.get 28).toNat := by rw [hR21]; exact hRlo
  have hRhi21 : (s21.mem.get 28).toNat < 32768 := by rw [hR21]; exact hRhi
  have hts := take_store_next_di1_idx0 (s := s21) hs21pc hs21h hs21Z hONE21 hs21DI hI21 hRlo21 hRhi21 g21S g21E
  have hrun : s81 = runN s21 60 := runN_add_eq s 21 60 81 (by decide)
  have hsTpc : s81.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s81.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s81.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s81.mem.get 32 = s.mem.get 21 := by
    rw [hrun, hts.2.2.2.1, hQ21]
  have hsTI : s81.mem.get 29 = 1 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s81.mem.get 2321 = 2 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s81.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres21 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `DI = SK = 1` and `IDX = 1 < ROOM`: take `Q1`,
store it, and return to `DIG_LOOP` with `DI = 2` and `IDX = 2`. 83 steps. -/
theorem loop_take_eq_di1_idx1 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 1)
    (hSK : s.mem.get 2320 = 1)
    (hI : s.mem.get 29 = 1)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s83 := runN s 83
    s83.pc = 1641 ∧
    s83.halted = false ∧
    s83.mem.get 0 = 0 ∧
    s83.mem.get 33 = s.mem.get 21 ∧
    s83.mem.get 29 = 2 ∧
    s83.mem.get 2321 = 2 ∧
    (∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s83.mem.get a = s.mem.get a) := by
  intro s83
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 1 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = 1 := (hpres10 2320 (by decide) (by decide)).trans hSK
  have hI10 : s10.mem.get 29 = 1 := (hpres10 29 (by decide) (by decide)).trans hI
  have hR10 : s10.mem.get 28 = s.mem.get 28 := hpres10 28 (by decide) (by decide)
  have hQ10 : s10.mem.get 21 = s.mem.get 21 := hpres10 21 (by decide) (by decide)
  have hDI_eq : s10.mem.get 2321 = s10.mem.get 2320 := hs10DI.trans hSK10.symm
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1716 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_eq (s := s10) hs10pc hs10h hs10Z hONE10 hDI_eq g10
  have hrun21 : runN s 21 = runN s10 11 := runN_add_eq s 10 11 21 (by decide)
  let s21 := runN s 21
  have hs21eq : s21 = runN s10 11 := hrun21
  have hs21pc : s21.pc = 1716 := by rw [hs21eq]; exact htk.1
  have hs21h : s21.halted = false := by rw [hs21eq]; exact htk.2.1
  have hs21Z : s21.mem.get 0 = 0 := by rw [hs21eq]; exact htk.2.2.1
  have hs21DI : s21.mem.get 2321 = 1 := by rw [hs21eq, htk.2.2.2.1, hs10DI]
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs21eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE21 : s21.mem.get 3 = 1 := (hpres21 3 (by decide) (by decide)).trans hONE
  have hI21 : s21.mem.get 29 = 1 := (hpres21 29 (by decide) (by decide)).trans hI
  have hR21 : s21.mem.get 28 = s.mem.get 28 := hpres21 28 (by decide) (by decide)
  have hQ21 : s21.mem.get 21 = s.mem.get 21 := hpres21 21 (by decide) (by decide)
  have g21S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g21E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo21 : 1 < (s21.mem.get 28).toNat := by rw [hR21]; exact hRlo
  have hRhi21 : (s21.mem.get 28).toNat < 32768 := by rw [hR21]; exact hRhi
  have hts := take_store_next_di1_idx1 (s := s21) hs21pc hs21h hs21Z hONE21 hs21DI hI21 hRlo21 hRhi21 g21S g21E
  have hrun : s83 = runN s21 62 := runN_add_eq s 21 62 83 (by decide)
  have hsTpc : s83.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s83.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s83.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s83.mem.get 33 = s.mem.get 21 := by
    rw [hrun, hts.2.2.2.1, hQ21]
  have hsTI : s83.mem.get 29 = 2 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s83.mem.get 2321 = 2 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s83.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres21 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `DI = SK = 2` and `IDX = 0 < ROOM`: take `Q2`,
store it, and return to `DIG_LOOP` with `DI = 3` and `IDX = 1`. 83 steps. -/
theorem loop_take_eq_di2_idx0 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 2)
    (hSK : s.mem.get 2320 = 2)
    (hI : s.mem.get 29 = 0)
    (hRlo : 0 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s83 := runN s 83
    s83.pc = 1641 ∧
    s83.halted = false ∧
    s83.mem.get 0 = 0 ∧
    s83.mem.get 32 = s.mem.get 22 ∧
    s83.mem.get 29 = 1 ∧
    s83.mem.get 2321 = 3 ∧
    (∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s83.mem.get a = s.mem.get a) := by
  intro s83
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 2 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = 2 := (hpres10 2320 (by decide) (by decide)).trans hSK
  have hI10 : s10.mem.get 29 = 0 := (hpres10 29 (by decide) (by decide)).trans hI
  have hR10 : s10.mem.get 28 = s.mem.get 28 := hpres10 28 (by decide) (by decide)
  have hQ10 : s10.mem.get 22 = s.mem.get 22 := hpres10 22 (by decide) (by decide)
  have hDI_eq : s10.mem.get 2321 = s10.mem.get 2320 := hs10DI.trans hSK10.symm
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1716 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_eq (s := s10) hs10pc hs10h hs10Z hONE10 hDI_eq g10
  have hrun21 : runN s 21 = runN s10 11 := runN_add_eq s 10 11 21 (by decide)
  let s21 := runN s 21
  have hs21eq : s21 = runN s10 11 := hrun21
  have hs21pc : s21.pc = 1716 := by rw [hs21eq]; exact htk.1
  have hs21h : s21.halted = false := by rw [hs21eq]; exact htk.2.1
  have hs21Z : s21.mem.get 0 = 0 := by rw [hs21eq]; exact htk.2.2.1
  have hs21DI : s21.mem.get 2321 = 2 := by rw [hs21eq, htk.2.2.2.1, hs10DI]
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs21eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE21 : s21.mem.get 3 = 1 := (hpres21 3 (by decide) (by decide)).trans hONE
  have hI21 : s21.mem.get 29 = 0 := (hpres21 29 (by decide) (by decide)).trans hI
  have hR21 : s21.mem.get 28 = s.mem.get 28 := hpres21 28 (by decide) (by decide)
  have hQ21 : s21.mem.get 22 = s.mem.get 22 := hpres21 22 (by decide) (by decide)
  have g21S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g21E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo21 : 0 < (s21.mem.get 28).toNat := by rw [hR21]; exact hRlo
  have hRhi21 : (s21.mem.get 28).toNat < 32768 := by rw [hR21]; exact hRhi
  have hts := take_store_next_di2_idx0 (s := s21) hs21pc hs21h hs21Z hONE21 hs21DI hI21 hRlo21 hRhi21 g21S g21E
  have hrun : s83 = runN s21 62 := runN_add_eq s 21 62 83 (by decide)
  have hsTpc : s83.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s83.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s83.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s83.mem.get 32 = s.mem.get 22 := by
    rw [hrun, hts.2.2.2.1, hQ21]
  have hsTI : s83.mem.get 29 = 1 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s83.mem.get 2321 = 3 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s83.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres21 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `DI = SK = 2` and `IDX = 1 < ROOM`: take `Q2`,
store it, and return to `DIG_LOOP` with `DI = 3` and `IDX = 2`. 85 steps. -/
theorem loop_take_eq_di2_idx1 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 2)
    (hSK : s.mem.get 2320 = 2)
    (hI : s.mem.get 29 = 1)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s85 := runN s 85
    s85.pc = 1641 ∧
    s85.halted = false ∧
    s85.mem.get 0 = 0 ∧
    s85.mem.get 33 = s.mem.get 22 ∧
    s85.mem.get 29 = 2 ∧
    s85.mem.get 2321 = 3 ∧
    (∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s85.mem.get a = s.mem.get a) := by
  intro s85
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 2 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = 2 := (hpres10 2320 (by decide) (by decide)).trans hSK
  have hI10 : s10.mem.get 29 = 1 := (hpres10 29 (by decide) (by decide)).trans hI
  have hR10 : s10.mem.get 28 = s.mem.get 28 := hpres10 28 (by decide) (by decide)
  have hQ10 : s10.mem.get 22 = s.mem.get 22 := hpres10 22 (by decide) (by decide)
  have hDI_eq : s10.mem.get 2321 = s10.mem.get 2320 := hs10DI.trans hSK10.symm
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1716 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_eq (s := s10) hs10pc hs10h hs10Z hONE10 hDI_eq g10
  have hrun21 : runN s 21 = runN s10 11 := runN_add_eq s 10 11 21 (by decide)
  let s21 := runN s 21
  have hs21eq : s21 = runN s10 11 := hrun21
  have hs21pc : s21.pc = 1716 := by rw [hs21eq]; exact htk.1
  have hs21h : s21.halted = false := by rw [hs21eq]; exact htk.2.1
  have hs21Z : s21.mem.get 0 = 0 := by rw [hs21eq]; exact htk.2.2.1
  have hs21DI : s21.mem.get 2321 = 2 := by rw [hs21eq, htk.2.2.2.1, hs10DI]
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs21eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE21 : s21.mem.get 3 = 1 := (hpres21 3 (by decide) (by decide)).trans hONE
  have hI21 : s21.mem.get 29 = 1 := (hpres21 29 (by decide) (by decide)).trans hI
  have hR21 : s21.mem.get 28 = s.mem.get 28 := hpres21 28 (by decide) (by decide)
  have hQ21 : s21.mem.get 22 = s.mem.get 22 := hpres21 22 (by decide) (by decide)
  have g21S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g21E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo21 : 1 < (s21.mem.get 28).toNat := by rw [hR21]; exact hRlo
  have hRhi21 : (s21.mem.get 28).toNat < 32768 := by rw [hR21]; exact hRhi
  have hts := take_store_next_di2_idx1 (s := s21) hs21pc hs21h hs21Z hONE21 hs21DI hI21 hRlo21 hRhi21 g21S g21E
  have hrun : s85 = runN s21 64 := runN_add_eq s 21 64 85 (by decide)
  have hsTpc : s85.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s85.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s85.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s85.mem.get 33 = s.mem.get 22 := by
    rw [hrun, hts.2.2.2.1, hQ21]
  have hsTI : s85.mem.get 29 = 2 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s85.mem.get 2321 = 3 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s85.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres21 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `DI = SK = 3` and `IDX = 0 < ROOM`: take `Q3`,
store it, and return to `DIG_LOOP` with `DI = 4` and `IDX = 1`. 85 steps. -/
theorem loop_take_eq_di3_idx0 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 3)
    (hSK : s.mem.get 2320 = 3)
    (hI : s.mem.get 29 = 0)
    (hRlo : 0 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s85 := runN s 85
    s85.pc = 1641 ∧
    s85.halted = false ∧
    s85.mem.get 0 = 0 ∧
    s85.mem.get 32 = s.mem.get 23 ∧
    s85.mem.get 29 = 1 ∧
    s85.mem.get 2321 = 4 ∧
    (∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s85.mem.get a = s.mem.get a) := by
  intro s85
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 3 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = 3 := (hpres10 2320 (by decide) (by decide)).trans hSK
  have hI10 : s10.mem.get 29 = 0 := (hpres10 29 (by decide) (by decide)).trans hI
  have hR10 : s10.mem.get 28 = s.mem.get 28 := hpres10 28 (by decide) (by decide)
  have hQ10 : s10.mem.get 23 = s.mem.get 23 := hpres10 23 (by decide) (by decide)
  have hDI_eq : s10.mem.get 2321 = s10.mem.get 2320 := hs10DI.trans hSK10.symm
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1716 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_eq (s := s10) hs10pc hs10h hs10Z hONE10 hDI_eq g10
  have hrun21 : runN s 21 = runN s10 11 := runN_add_eq s 10 11 21 (by decide)
  let s21 := runN s 21
  have hs21eq : s21 = runN s10 11 := hrun21
  have hs21pc : s21.pc = 1716 := by rw [hs21eq]; exact htk.1
  have hs21h : s21.halted = false := by rw [hs21eq]; exact htk.2.1
  have hs21Z : s21.mem.get 0 = 0 := by rw [hs21eq]; exact htk.2.2.1
  have hs21DI : s21.mem.get 2321 = 3 := by rw [hs21eq, htk.2.2.2.1, hs10DI]
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs21eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE21 : s21.mem.get 3 = 1 := (hpres21 3 (by decide) (by decide)).trans hONE
  have hI21 : s21.mem.get 29 = 0 := (hpres21 29 (by decide) (by decide)).trans hI
  have hR21 : s21.mem.get 28 = s.mem.get 28 := hpres21 28 (by decide) (by decide)
  have hQ21 : s21.mem.get 23 = s.mem.get 23 := hpres21 23 (by decide) (by decide)
  have g21S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g21E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo21 : 0 < (s21.mem.get 28).toNat := by rw [hR21]; exact hRlo
  have hRhi21 : (s21.mem.get 28).toNat < 32768 := by rw [hR21]; exact hRhi
  have hts := take_store_next_di3_idx0 (s := s21) hs21pc hs21h hs21Z hONE21 hs21DI hI21 hRlo21 hRhi21 g21S g21E
  have hrun : s85 = runN s21 64 := runN_add_eq s 21 64 85 (by decide)
  have hsTpc : s85.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s85.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s85.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s85.mem.get 32 = s.mem.get 23 := by
    rw [hrun, hts.2.2.2.1, hQ21]
  have hsTI : s85.mem.get 29 = 1 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s85.mem.get 2321 = 4 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s85.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres21 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `DI = SK = 3` and `IDX = 1 < ROOM`: take `Q3`,
store it, and return to `DIG_LOOP` with `DI = 4` and `IDX = 2`. 87 steps. -/
theorem loop_take_eq_di3_idx1 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 3)
    (hSK : s.mem.get 2320 = 3)
    (hI : s.mem.get 29 = 1)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s87 := runN s 87
    s87.pc = 1641 ∧
    s87.halted = false ∧
    s87.mem.get 0 = 0 ∧
    s87.mem.get 33 = s.mem.get 23 ∧
    s87.mem.get 29 = 2 ∧
    s87.mem.get 2321 = 4 ∧
    (∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s87.mem.get a = s.mem.get a) := by
  intro s87
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 3 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = 3 := (hpres10 2320 (by decide) (by decide)).trans hSK
  have hI10 : s10.mem.get 29 = 1 := (hpres10 29 (by decide) (by decide)).trans hI
  have hR10 : s10.mem.get 28 = s.mem.get 28 := hpres10 28 (by decide) (by decide)
  have hQ10 : s10.mem.get 23 = s.mem.get 23 := hpres10 23 (by decide) (by decide)
  have hDI_eq : s10.mem.get 2321 = s10.mem.get 2320 := hs10DI.trans hSK10.symm
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1716 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_eq (s := s10) hs10pc hs10h hs10Z hONE10 hDI_eq g10
  have hrun21 : runN s 21 = runN s10 11 := runN_add_eq s 10 11 21 (by decide)
  let s21 := runN s 21
  have hs21eq : s21 = runN s10 11 := hrun21
  have hs21pc : s21.pc = 1716 := by rw [hs21eq]; exact htk.1
  have hs21h : s21.halted = false := by rw [hs21eq]; exact htk.2.1
  have hs21Z : s21.mem.get 0 = 0 := by rw [hs21eq]; exact htk.2.2.1
  have hs21DI : s21.mem.get 2321 = 3 := by rw [hs21eq, htk.2.2.2.1, hs10DI]
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs21eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE21 : s21.mem.get 3 = 1 := (hpres21 3 (by decide) (by decide)).trans hONE
  have hI21 : s21.mem.get 29 = 1 := (hpres21 29 (by decide) (by decide)).trans hI
  have hR21 : s21.mem.get 28 = s.mem.get 28 := hpres21 28 (by decide) (by decide)
  have hQ21 : s21.mem.get 23 = s.mem.get 23 := hpres21 23 (by decide) (by decide)
  have g21S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g21E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo21 : 1 < (s21.mem.get 28).toNat := by rw [hR21]; exact hRlo
  have hRhi21 : (s21.mem.get 28).toNat < 32768 := by rw [hR21]; exact hRhi
  have hts := take_store_next_di3_idx1 (s := s21) hs21pc hs21h hs21Z hONE21 hs21DI hI21 hRlo21 hRhi21 g21S g21E
  have hrun : s87 = runN s21 66 := runN_add_eq s 21 66 87 (by decide)
  have hsTpc : s87.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s87.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s87.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s87.mem.get 33 = s.mem.get 23 := by
    rw [hrun, hts.2.2.2.1, hQ21]
  have hsTI : s87.mem.get 29 = 2 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s87.mem.get 2321 = 4 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s87.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres21 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `DI = SK = 4` and `IDX = 0 < ROOM`: take `Q4`,
store it, and return to `DIG_LOOP` with `DI = 5` and `IDX = 1`. 85 steps. -/
theorem loop_take_eq_di4_idx0 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 4)
    (hSK : s.mem.get 2320 = 4)
    (hI : s.mem.get 29 = 0)
    (hRlo : 0 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s85 := runN s 85
    s85.pc = 1641 ∧
    s85.halted = false ∧
    s85.mem.get 0 = 0 ∧
    s85.mem.get 32 = s.mem.get 24 ∧
    s85.mem.get 29 = 1 ∧
    s85.mem.get 2321 = 5 ∧
    (∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s85.mem.get a = s.mem.get a) := by
  intro s85
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 4 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = 4 := (hpres10 2320 (by decide) (by decide)).trans hSK
  have hI10 : s10.mem.get 29 = 0 := (hpres10 29 (by decide) (by decide)).trans hI
  have hR10 : s10.mem.get 28 = s.mem.get 28 := hpres10 28 (by decide) (by decide)
  have hQ10 : s10.mem.get 24 = s.mem.get 24 := hpres10 24 (by decide) (by decide)
  have hDI_eq : s10.mem.get 2321 = s10.mem.get 2320 := hs10DI.trans hSK10.symm
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1716 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_eq (s := s10) hs10pc hs10h hs10Z hONE10 hDI_eq g10
  have hrun21 : runN s 21 = runN s10 11 := runN_add_eq s 10 11 21 (by decide)
  let s21 := runN s 21
  have hs21eq : s21 = runN s10 11 := hrun21
  have hs21pc : s21.pc = 1716 := by rw [hs21eq]; exact htk.1
  have hs21h : s21.halted = false := by rw [hs21eq]; exact htk.2.1
  have hs21Z : s21.mem.get 0 = 0 := by rw [hs21eq]; exact htk.2.2.1
  have hs21DI : s21.mem.get 2321 = 4 := by rw [hs21eq, htk.2.2.2.1, hs10DI]
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs21eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE21 : s21.mem.get 3 = 1 := (hpres21 3 (by decide) (by decide)).trans hONE
  have hI21 : s21.mem.get 29 = 0 := (hpres21 29 (by decide) (by decide)).trans hI
  have hR21 : s21.mem.get 28 = s.mem.get 28 := hpres21 28 (by decide) (by decide)
  have hQ21 : s21.mem.get 24 = s.mem.get 24 := hpres21 24 (by decide) (by decide)
  have g21S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g21E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo21 : 0 < (s21.mem.get 28).toNat := by rw [hR21]; exact hRlo
  have hRhi21 : (s21.mem.get 28).toNat < 32768 := by rw [hR21]; exact hRhi
  have hts := take_store_next_di4_idx0 (s := s21) hs21pc hs21h hs21Z hONE21 hs21DI hI21 hRlo21 hRhi21 g21S g21E
  have hrun : s85 = runN s21 64 := runN_add_eq s 21 64 85 (by decide)
  have hsTpc : s85.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s85.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s85.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s85.mem.get 32 = s.mem.get 24 := by
    rw [hrun, hts.2.2.2.1, hQ21]
  have hsTI : s85.mem.get 29 = 1 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s85.mem.get 2321 = 5 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s85.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres21 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `DI = SK = 4` and `IDX = 1 < ROOM`: take `Q4`,
store it, and return to `DIG_LOOP` with `DI = 5` and `IDX = 2`. 87 steps. -/
theorem loop_take_eq_di4_idx1 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 4)
    (hSK : s.mem.get 2320 = 4)
    (hI : s.mem.get 29 = 1)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s87 := runN s 87
    s87.pc = 1641 ∧
    s87.halted = false ∧
    s87.mem.get 0 = 0 ∧
    s87.mem.get 33 = s.mem.get 24 ∧
    s87.mem.get 29 = 2 ∧
    s87.mem.get 2321 = 5 ∧
    (∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s87.mem.get a = s.mem.get a) := by
  intro s87
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 4 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = 4 := (hpres10 2320 (by decide) (by decide)).trans hSK
  have hI10 : s10.mem.get 29 = 1 := (hpres10 29 (by decide) (by decide)).trans hI
  have hR10 : s10.mem.get 28 = s.mem.get 28 := hpres10 28 (by decide) (by decide)
  have hQ10 : s10.mem.get 24 = s.mem.get 24 := hpres10 24 (by decide) (by decide)
  have hDI_eq : s10.mem.get 2321 = s10.mem.get 2320 := hs10DI.trans hSK10.symm
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1716 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_eq (s := s10) hs10pc hs10h hs10Z hONE10 hDI_eq g10
  have hrun21 : runN s 21 = runN s10 11 := runN_add_eq s 10 11 21 (by decide)
  let s21 := runN s 21
  have hs21eq : s21 = runN s10 11 := hrun21
  have hs21pc : s21.pc = 1716 := by rw [hs21eq]; exact htk.1
  have hs21h : s21.halted = false := by rw [hs21eq]; exact htk.2.1
  have hs21Z : s21.mem.get 0 = 0 := by rw [hs21eq]; exact htk.2.2.1
  have hs21DI : s21.mem.get 2321 = 4 := by rw [hs21eq, htk.2.2.2.1, hs10DI]
  have hpres21 : ∀ a, a ≠ 18 → a ≠ 0 → s21.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs21eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE21 : s21.mem.get 3 = 1 := (hpres21 3 (by decide) (by decide)).trans hONE
  have hI21 : s21.mem.get 29 = 1 := (hpres21 29 (by decide) (by decide)).trans hI
  have hR21 : s21.mem.get 28 = s.mem.get 28 := hpres21 28 (by decide) (by decide)
  have hQ21 : s21.mem.get 24 = s.mem.get 24 := hpres21 24 (by decide) (by decide)
  have g21S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g21E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s21.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres21 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo21 : 1 < (s21.mem.get 28).toNat := by rw [hR21]; exact hRlo
  have hRhi21 : (s21.mem.get 28).toNat < 32768 := by rw [hR21]; exact hRhi
  have hts := take_store_next_di4_idx1 (s := s21) hs21pc hs21h hs21Z hONE21 hs21DI hI21 hRlo21 hRhi21 g21S g21E
  have hrun : s87 = runN s21 66 := runN_add_eq s 21 66 87 (by decide)
  have hsTpc : s87.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s87.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s87.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s87.mem.get 33 = s.mem.get 24 := by
    rw [hrun, hts.2.2.2.1, hQ21]
  have hsTI : s87.mem.get 29 = 2 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s87.mem.get 2321 = 5 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s87.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres21 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `1 = DI > SK` and `IDX = 1 < ROOM`: take `Q1`,
store it, and return to `DIG_LOOP` with `DI = 2` and `IDX = 2`. 79 steps. -/
theorem loop_take_gt_di1_idx1 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 1)
    (hSKlo : (s.mem.get 2320).toNat < 1)
    (hI : s.mem.get 29 = 1)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s79 := runN s 79
    s79.pc = 1641 ∧
    s79.halted = false ∧
    s79.mem.get 0 = 0 ∧
    s79.mem.get 33 = s.mem.get 21 ∧
    s79.mem.get 29 = 2 ∧
    s79.mem.get 2321 = 2 ∧
    (∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s79.mem.get a = s.mem.get a) := by
  intro s79
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 1 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = s.mem.get 2320 := hpres10 2320 (by decide) (by decide)
  have hSKlo10 : (s10.mem.get 2320).toNat < (s10.mem.get 2321).toNat := by
    rw [hSK10, hs10DI]; exact hSKlo
  have hDIhi10 : (s10.mem.get 2321).toNat < 32768 := by rw [hs10DI]; simp
  have hQ10 : s10.mem.get 21 = s.mem.get 21 := hpres10 21 (by decide) (by decide)
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1698 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_gt (s := s10) hs10pc hs10h hs10Z hSKlo10 hDIhi10 g10
  have hrun17 : runN s 17 = runN s10 7 := runN_add_eq s 10 7 17 (by decide)
  let s17 := runN s 17
  have hs17eq : s17 = runN s10 7 := hrun17
  have hs17pc : s17.pc = 1716 := by rw [hs17eq]; exact htk.1
  have hs17h : s17.halted = false := by rw [hs17eq]; exact htk.2.1
  have hs17Z : s17.mem.get 0 = 0 := by rw [hs17eq]; exact htk.2.2.1
  have hs17DI : s17.mem.get 2321 = 1 := by rw [hs17eq, htk.2.2.2.1, hs10DI]
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs17eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE17 : s17.mem.get 3 = 1 := (hpres17 3 (by decide) (by decide)).trans hONE
  have hI17 : s17.mem.get 29 = 1 := (hpres17 29 (by decide) (by decide)).trans hI
  have hR17 : s17.mem.get 28 = s.mem.get 28 := hpres17 28 (by decide) (by decide)
  have hQ17 : s17.mem.get 21 = s.mem.get 21 := hpres17 21 (by decide) (by decide)
  have g17S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g17E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo17 : 1 < (s17.mem.get 28).toNat := by rw [hR17]; exact hRlo
  have hRhi17 : (s17.mem.get 28).toNat < 32768 := by rw [hR17]; exact hRhi
  have hts := take_store_next_di1_idx1 (s := s17) hs17pc hs17h hs17Z hONE17 hs17DI hI17 hRlo17 hRhi17 g17S g17E
  have hrun : s79 = runN s17 62 := runN_add_eq s 17 62 79 (by decide)
  have hsTpc : s79.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s79.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s79.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s79.mem.get 33 = s.mem.get 21 := by
    rw [hrun, hts.2.2.2.1, hQ17]
  have hsTI : s79.mem.get 29 = 2 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s79.mem.get 2321 = 2 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s79.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres17 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `1 = DI > SK` and `IDX = 2 < ROOM`: take `Q1`,
store it, and return to `DIG_LOOP` with `DI = 2` and `IDX = 3`. 81 steps. -/
theorem loop_take_gt_di1_idx2 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 1)
    (hSKlo : (s.mem.get 2320).toNat < 1)
    (hI : s.mem.get 29 = 2)
    (hRlo : 2 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s81 := runN s 81
    s81.pc = 1641 ∧
    s81.halted = false ∧
    s81.mem.get 0 = 0 ∧
    s81.mem.get 34 = s.mem.get 21 ∧
    s81.mem.get 29 = 3 ∧
    s81.mem.get 2321 = 2 ∧
    (∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s81.mem.get a = s.mem.get a) := by
  intro s81
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 1 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = s.mem.get 2320 := hpres10 2320 (by decide) (by decide)
  have hSKlo10 : (s10.mem.get 2320).toNat < (s10.mem.get 2321).toNat := by
    rw [hSK10, hs10DI]; exact hSKlo
  have hDIhi10 : (s10.mem.get 2321).toNat < 32768 := by rw [hs10DI]; simp
  have hQ10 : s10.mem.get 21 = s.mem.get 21 := hpres10 21 (by decide) (by decide)
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1698 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_gt (s := s10) hs10pc hs10h hs10Z hSKlo10 hDIhi10 g10
  have hrun17 : runN s 17 = runN s10 7 := runN_add_eq s 10 7 17 (by decide)
  let s17 := runN s 17
  have hs17eq : s17 = runN s10 7 := hrun17
  have hs17pc : s17.pc = 1716 := by rw [hs17eq]; exact htk.1
  have hs17h : s17.halted = false := by rw [hs17eq]; exact htk.2.1
  have hs17Z : s17.mem.get 0 = 0 := by rw [hs17eq]; exact htk.2.2.1
  have hs17DI : s17.mem.get 2321 = 1 := by rw [hs17eq, htk.2.2.2.1, hs10DI]
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs17eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE17 : s17.mem.get 3 = 1 := (hpres17 3 (by decide) (by decide)).trans hONE
  have hI17 : s17.mem.get 29 = 2 := (hpres17 29 (by decide) (by decide)).trans hI
  have hR17 : s17.mem.get 28 = s.mem.get 28 := hpres17 28 (by decide) (by decide)
  have hQ17 : s17.mem.get 21 = s.mem.get 21 := hpres17 21 (by decide) (by decide)
  have g17S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g17E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo17 : 2 < (s17.mem.get 28).toNat := by rw [hR17]; exact hRlo
  have hRhi17 : (s17.mem.get 28).toNat < 32768 := by rw [hR17]; exact hRhi
  have hts := take_store_next_di1_idx2 (s := s17) hs17pc hs17h hs17Z hONE17 hs17DI hI17 hRlo17 hRhi17 g17S g17E
  have hrun : s81 = runN s17 64 := runN_add_eq s 17 64 81 (by decide)
  have hsTpc : s81.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s81.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s81.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s81.mem.get 34 = s.mem.get 21 := by
    rw [hrun, hts.2.2.2.1, hQ17]
  have hsTI : s81.mem.get 29 = 3 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s81.mem.get 2321 = 2 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s81.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres17 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `2 = DI > SK` and `IDX = 1 < ROOM`: take `Q2`,
store it, and return to `DIG_LOOP` with `DI = 3` and `IDX = 2`. 81 steps. -/
theorem loop_take_gt_di2_idx1 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 2)
    (hSKlo : (s.mem.get 2320).toNat < 2)
    (hI : s.mem.get 29 = 1)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s81 := runN s 81
    s81.pc = 1641 ∧
    s81.halted = false ∧
    s81.mem.get 0 = 0 ∧
    s81.mem.get 33 = s.mem.get 22 ∧
    s81.mem.get 29 = 2 ∧
    s81.mem.get 2321 = 3 ∧
    (∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s81.mem.get a = s.mem.get a) := by
  intro s81
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 2 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = s.mem.get 2320 := hpres10 2320 (by decide) (by decide)
  have hSKlo10 : (s10.mem.get 2320).toNat < (s10.mem.get 2321).toNat := by
    rw [hSK10, hs10DI]; exact hSKlo
  have hDIhi10 : (s10.mem.get 2321).toNat < 32768 := by rw [hs10DI]; simp
  have hQ10 : s10.mem.get 22 = s.mem.get 22 := hpres10 22 (by decide) (by decide)
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1698 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_gt (s := s10) hs10pc hs10h hs10Z hSKlo10 hDIhi10 g10
  have hrun17 : runN s 17 = runN s10 7 := runN_add_eq s 10 7 17 (by decide)
  let s17 := runN s 17
  have hs17eq : s17 = runN s10 7 := hrun17
  have hs17pc : s17.pc = 1716 := by rw [hs17eq]; exact htk.1
  have hs17h : s17.halted = false := by rw [hs17eq]; exact htk.2.1
  have hs17Z : s17.mem.get 0 = 0 := by rw [hs17eq]; exact htk.2.2.1
  have hs17DI : s17.mem.get 2321 = 2 := by rw [hs17eq, htk.2.2.2.1, hs10DI]
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs17eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE17 : s17.mem.get 3 = 1 := (hpres17 3 (by decide) (by decide)).trans hONE
  have hI17 : s17.mem.get 29 = 1 := (hpres17 29 (by decide) (by decide)).trans hI
  have hR17 : s17.mem.get 28 = s.mem.get 28 := hpres17 28 (by decide) (by decide)
  have hQ17 : s17.mem.get 22 = s.mem.get 22 := hpres17 22 (by decide) (by decide)
  have g17S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g17E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo17 : 1 < (s17.mem.get 28).toNat := by rw [hR17]; exact hRlo
  have hRhi17 : (s17.mem.get 28).toNat < 32768 := by rw [hR17]; exact hRhi
  have hts := take_store_next_di2_idx1 (s := s17) hs17pc hs17h hs17Z hONE17 hs17DI hI17 hRlo17 hRhi17 g17S g17E
  have hrun : s81 = runN s17 64 := runN_add_eq s 17 64 81 (by decide)
  have hsTpc : s81.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s81.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s81.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s81.mem.get 33 = s.mem.get 22 := by
    rw [hrun, hts.2.2.2.1, hQ17]
  have hsTI : s81.mem.get 29 = 2 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s81.mem.get 2321 = 3 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s81.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres17 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `2 = DI > SK` and `IDX = 2 < ROOM`: take `Q2`,
store it, and return to `DIG_LOOP` with `DI = 3` and `IDX = 3`. 83 steps. -/
theorem loop_take_gt_di2_idx2 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 2)
    (hSKlo : (s.mem.get 2320).toNat < 2)
    (hI : s.mem.get 29 = 2)
    (hRlo : 2 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s83 := runN s 83
    s83.pc = 1641 ∧
    s83.halted = false ∧
    s83.mem.get 0 = 0 ∧
    s83.mem.get 34 = s.mem.get 22 ∧
    s83.mem.get 29 = 3 ∧
    s83.mem.get 2321 = 3 ∧
    (∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s83.mem.get a = s.mem.get a) := by
  intro s83
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 2 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = s.mem.get 2320 := hpres10 2320 (by decide) (by decide)
  have hSKlo10 : (s10.mem.get 2320).toNat < (s10.mem.get 2321).toNat := by
    rw [hSK10, hs10DI]; exact hSKlo
  have hDIhi10 : (s10.mem.get 2321).toNat < 32768 := by rw [hs10DI]; simp
  have hQ10 : s10.mem.get 22 = s.mem.get 22 := hpres10 22 (by decide) (by decide)
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1698 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_gt (s := s10) hs10pc hs10h hs10Z hSKlo10 hDIhi10 g10
  have hrun17 : runN s 17 = runN s10 7 := runN_add_eq s 10 7 17 (by decide)
  let s17 := runN s 17
  have hs17eq : s17 = runN s10 7 := hrun17
  have hs17pc : s17.pc = 1716 := by rw [hs17eq]; exact htk.1
  have hs17h : s17.halted = false := by rw [hs17eq]; exact htk.2.1
  have hs17Z : s17.mem.get 0 = 0 := by rw [hs17eq]; exact htk.2.2.1
  have hs17DI : s17.mem.get 2321 = 2 := by rw [hs17eq, htk.2.2.2.1, hs10DI]
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs17eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE17 : s17.mem.get 3 = 1 := (hpres17 3 (by decide) (by decide)).trans hONE
  have hI17 : s17.mem.get 29 = 2 := (hpres17 29 (by decide) (by decide)).trans hI
  have hR17 : s17.mem.get 28 = s.mem.get 28 := hpres17 28 (by decide) (by decide)
  have hQ17 : s17.mem.get 22 = s.mem.get 22 := hpres17 22 (by decide) (by decide)
  have g17S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g17E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo17 : 2 < (s17.mem.get 28).toNat := by rw [hR17]; exact hRlo
  have hRhi17 : (s17.mem.get 28).toNat < 32768 := by rw [hR17]; exact hRhi
  have hts := take_store_next_di2_idx2 (s := s17) hs17pc hs17h hs17Z hONE17 hs17DI hI17 hRlo17 hRhi17 g17S g17E
  have hrun : s83 = runN s17 66 := runN_add_eq s 17 66 83 (by decide)
  have hsTpc : s83.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s83.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s83.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s83.mem.get 34 = s.mem.get 22 := by
    rw [hrun, hts.2.2.2.1, hQ17]
  have hsTI : s83.mem.get 29 = 3 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s83.mem.get 2321 = 3 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s83.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres17 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `2 = DI > SK` and `IDX = 3 < ROOM`: take `Q2`,
store it, and return to `DIG_LOOP` with `DI = 3` and `IDX = 4`. 85 steps. -/
theorem loop_take_gt_di2_idx3 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 2)
    (hSKlo : (s.mem.get 2320).toNat < 2)
    (hI : s.mem.get 29 = 3)
    (hRlo : 3 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s85 := runN s 85
    s85.pc = 1641 ∧
    s85.halted = false ∧
    s85.mem.get 0 = 0 ∧
    s85.mem.get 35 = s.mem.get 22 ∧
    s85.mem.get 29 = 4 ∧
    s85.mem.get 2321 = 3 ∧
    (∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s85.mem.get a = s.mem.get a) := by
  intro s85
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 2 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = s.mem.get 2320 := hpres10 2320 (by decide) (by decide)
  have hSKlo10 : (s10.mem.get 2320).toNat < (s10.mem.get 2321).toNat := by
    rw [hSK10, hs10DI]; exact hSKlo
  have hDIhi10 : (s10.mem.get 2321).toNat < 32768 := by rw [hs10DI]; simp
  have hQ10 : s10.mem.get 22 = s.mem.get 22 := hpres10 22 (by decide) (by decide)
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1698 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_gt (s := s10) hs10pc hs10h hs10Z hSKlo10 hDIhi10 g10
  have hrun17 : runN s 17 = runN s10 7 := runN_add_eq s 10 7 17 (by decide)
  let s17 := runN s 17
  have hs17eq : s17 = runN s10 7 := hrun17
  have hs17pc : s17.pc = 1716 := by rw [hs17eq]; exact htk.1
  have hs17h : s17.halted = false := by rw [hs17eq]; exact htk.2.1
  have hs17Z : s17.mem.get 0 = 0 := by rw [hs17eq]; exact htk.2.2.1
  have hs17DI : s17.mem.get 2321 = 2 := by rw [hs17eq, htk.2.2.2.1, hs10DI]
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs17eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE17 : s17.mem.get 3 = 1 := (hpres17 3 (by decide) (by decide)).trans hONE
  have hI17 : s17.mem.get 29 = 3 := (hpres17 29 (by decide) (by decide)).trans hI
  have hR17 : s17.mem.get 28 = s.mem.get 28 := hpres17 28 (by decide) (by decide)
  have hQ17 : s17.mem.get 22 = s.mem.get 22 := hpres17 22 (by decide) (by decide)
  have g17S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g17E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo17 : 3 < (s17.mem.get 28).toNat := by rw [hR17]; exact hRlo
  have hRhi17 : (s17.mem.get 28).toNat < 32768 := by rw [hR17]; exact hRhi
  have hts := take_store_next_di2_idx3 (s := s17) hs17pc hs17h hs17Z hONE17 hs17DI hI17 hRlo17 hRhi17 g17S g17E
  have hrun : s85 = runN s17 68 := runN_add_eq s 17 68 85 (by decide)
  have hsTpc : s85.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s85.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s85.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s85.mem.get 35 = s.mem.get 22 := by
    rw [hrun, hts.2.2.2.1, hQ17]
  have hsTI : s85.mem.get 29 = 4 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s85.mem.get 2321 = 3 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s85.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres17 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `3 = DI > SK` and `IDX = 1 < ROOM`: take `Q3`,
store it, and return to `DIG_LOOP` with `DI = 4` and `IDX = 2`. 83 steps. -/
theorem loop_take_gt_di3_idx1 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 3)
    (hSKlo : (s.mem.get 2320).toNat < 3)
    (hI : s.mem.get 29 = 1)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s83 := runN s 83
    s83.pc = 1641 ∧
    s83.halted = false ∧
    s83.mem.get 0 = 0 ∧
    s83.mem.get 33 = s.mem.get 23 ∧
    s83.mem.get 29 = 2 ∧
    s83.mem.get 2321 = 4 ∧
    (∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s83.mem.get a = s.mem.get a) := by
  intro s83
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 3 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = s.mem.get 2320 := hpres10 2320 (by decide) (by decide)
  have hSKlo10 : (s10.mem.get 2320).toNat < (s10.mem.get 2321).toNat := by
    rw [hSK10, hs10DI]; exact hSKlo
  have hDIhi10 : (s10.mem.get 2321).toNat < 32768 := by rw [hs10DI]; simp
  have hQ10 : s10.mem.get 23 = s.mem.get 23 := hpres10 23 (by decide) (by decide)
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1698 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_gt (s := s10) hs10pc hs10h hs10Z hSKlo10 hDIhi10 g10
  have hrun17 : runN s 17 = runN s10 7 := runN_add_eq s 10 7 17 (by decide)
  let s17 := runN s 17
  have hs17eq : s17 = runN s10 7 := hrun17
  have hs17pc : s17.pc = 1716 := by rw [hs17eq]; exact htk.1
  have hs17h : s17.halted = false := by rw [hs17eq]; exact htk.2.1
  have hs17Z : s17.mem.get 0 = 0 := by rw [hs17eq]; exact htk.2.2.1
  have hs17DI : s17.mem.get 2321 = 3 := by rw [hs17eq, htk.2.2.2.1, hs10DI]
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs17eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE17 : s17.mem.get 3 = 1 := (hpres17 3 (by decide) (by decide)).trans hONE
  have hI17 : s17.mem.get 29 = 1 := (hpres17 29 (by decide) (by decide)).trans hI
  have hR17 : s17.mem.get 28 = s.mem.get 28 := hpres17 28 (by decide) (by decide)
  have hQ17 : s17.mem.get 23 = s.mem.get 23 := hpres17 23 (by decide) (by decide)
  have g17S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g17E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo17 : 1 < (s17.mem.get 28).toNat := by rw [hR17]; exact hRlo
  have hRhi17 : (s17.mem.get 28).toNat < 32768 := by rw [hR17]; exact hRhi
  have hts := take_store_next_di3_idx1 (s := s17) hs17pc hs17h hs17Z hONE17 hs17DI hI17 hRlo17 hRhi17 g17S g17E
  have hrun : s83 = runN s17 66 := runN_add_eq s 17 66 83 (by decide)
  have hsTpc : s83.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s83.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s83.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s83.mem.get 33 = s.mem.get 23 := by
    rw [hrun, hts.2.2.2.1, hQ17]
  have hsTI : s83.mem.get 29 = 2 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s83.mem.get 2321 = 4 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s83.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres17 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `3 = DI > SK` and `IDX = 2 < ROOM`: take `Q3`,
store it, and return to `DIG_LOOP` with `DI = 4` and `IDX = 3`. 85 steps. -/
theorem loop_take_gt_di3_idx2 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 3)
    (hSKlo : (s.mem.get 2320).toNat < 3)
    (hI : s.mem.get 29 = 2)
    (hRlo : 2 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s85 := runN s 85
    s85.pc = 1641 ∧
    s85.halted = false ∧
    s85.mem.get 0 = 0 ∧
    s85.mem.get 34 = s.mem.get 23 ∧
    s85.mem.get 29 = 3 ∧
    s85.mem.get 2321 = 4 ∧
    (∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s85.mem.get a = s.mem.get a) := by
  intro s85
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 3 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = s.mem.get 2320 := hpres10 2320 (by decide) (by decide)
  have hSKlo10 : (s10.mem.get 2320).toNat < (s10.mem.get 2321).toNat := by
    rw [hSK10, hs10DI]; exact hSKlo
  have hDIhi10 : (s10.mem.get 2321).toNat < 32768 := by rw [hs10DI]; simp
  have hQ10 : s10.mem.get 23 = s.mem.get 23 := hpres10 23 (by decide) (by decide)
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1698 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_gt (s := s10) hs10pc hs10h hs10Z hSKlo10 hDIhi10 g10
  have hrun17 : runN s 17 = runN s10 7 := runN_add_eq s 10 7 17 (by decide)
  let s17 := runN s 17
  have hs17eq : s17 = runN s10 7 := hrun17
  have hs17pc : s17.pc = 1716 := by rw [hs17eq]; exact htk.1
  have hs17h : s17.halted = false := by rw [hs17eq]; exact htk.2.1
  have hs17Z : s17.mem.get 0 = 0 := by rw [hs17eq]; exact htk.2.2.1
  have hs17DI : s17.mem.get 2321 = 3 := by rw [hs17eq, htk.2.2.2.1, hs10DI]
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs17eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE17 : s17.mem.get 3 = 1 := (hpres17 3 (by decide) (by decide)).trans hONE
  have hI17 : s17.mem.get 29 = 2 := (hpres17 29 (by decide) (by decide)).trans hI
  have hR17 : s17.mem.get 28 = s.mem.get 28 := hpres17 28 (by decide) (by decide)
  have hQ17 : s17.mem.get 23 = s.mem.get 23 := hpres17 23 (by decide) (by decide)
  have g17S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g17E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo17 : 2 < (s17.mem.get 28).toNat := by rw [hR17]; exact hRlo
  have hRhi17 : (s17.mem.get 28).toNat < 32768 := by rw [hR17]; exact hRhi
  have hts := take_store_next_di3_idx2 (s := s17) hs17pc hs17h hs17Z hONE17 hs17DI hI17 hRlo17 hRhi17 g17S g17E
  have hrun : s85 = runN s17 68 := runN_add_eq s 17 68 85 (by decide)
  have hsTpc : s85.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s85.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s85.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s85.mem.get 34 = s.mem.get 23 := by
    rw [hrun, hts.2.2.2.1, hQ17]
  have hsTI : s85.mem.get 29 = 3 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s85.mem.get 2321 = 4 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s85.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres17 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `3 = DI > SK` and `IDX = 3 < ROOM`: take `Q3`,
store it, and return to `DIG_LOOP` with `DI = 4` and `IDX = 4`. 87 steps. -/
theorem loop_take_gt_di3_idx3 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 3)
    (hSKlo : (s.mem.get 2320).toNat < 3)
    (hI : s.mem.get 29 = 3)
    (hRlo : 3 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s87 := runN s 87
    s87.pc = 1641 ∧
    s87.halted = false ∧
    s87.mem.get 0 = 0 ∧
    s87.mem.get 35 = s.mem.get 23 ∧
    s87.mem.get 29 = 4 ∧
    s87.mem.get 2321 = 4 ∧
    (∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s87.mem.get a = s.mem.get a) := by
  intro s87
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 3 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = s.mem.get 2320 := hpres10 2320 (by decide) (by decide)
  have hSKlo10 : (s10.mem.get 2320).toNat < (s10.mem.get 2321).toNat := by
    rw [hSK10, hs10DI]; exact hSKlo
  have hDIhi10 : (s10.mem.get 2321).toNat < 32768 := by rw [hs10DI]; simp
  have hQ10 : s10.mem.get 23 = s.mem.get 23 := hpres10 23 (by decide) (by decide)
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1698 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_gt (s := s10) hs10pc hs10h hs10Z hSKlo10 hDIhi10 g10
  have hrun17 : runN s 17 = runN s10 7 := runN_add_eq s 10 7 17 (by decide)
  let s17 := runN s 17
  have hs17eq : s17 = runN s10 7 := hrun17
  have hs17pc : s17.pc = 1716 := by rw [hs17eq]; exact htk.1
  have hs17h : s17.halted = false := by rw [hs17eq]; exact htk.2.1
  have hs17Z : s17.mem.get 0 = 0 := by rw [hs17eq]; exact htk.2.2.1
  have hs17DI : s17.mem.get 2321 = 3 := by rw [hs17eq, htk.2.2.2.1, hs10DI]
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs17eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE17 : s17.mem.get 3 = 1 := (hpres17 3 (by decide) (by decide)).trans hONE
  have hI17 : s17.mem.get 29 = 3 := (hpres17 29 (by decide) (by decide)).trans hI
  have hR17 : s17.mem.get 28 = s.mem.get 28 := hpres17 28 (by decide) (by decide)
  have hQ17 : s17.mem.get 23 = s.mem.get 23 := hpres17 23 (by decide) (by decide)
  have g17S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g17E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo17 : 3 < (s17.mem.get 28).toNat := by rw [hR17]; exact hRlo
  have hRhi17 : (s17.mem.get 28).toNat < 32768 := by rw [hR17]; exact hRhi
  have hts := take_store_next_di3_idx3 (s := s17) hs17pc hs17h hs17Z hONE17 hs17DI hI17 hRlo17 hRhi17 g17S g17E
  have hrun : s87 = runN s17 70 := runN_add_eq s 17 70 87 (by decide)
  have hsTpc : s87.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s87.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s87.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s87.mem.get 35 = s.mem.get 23 := by
    rw [hrun, hts.2.2.2.1, hQ17]
  have hsTI : s87.mem.get 29 = 4 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s87.mem.get 2321 = 4 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s87.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres17 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `3 = DI > SK` and `IDX = 4 < ROOM`: take `Q3`,
store it, and return to `DIG_LOOP` with `DI = 4` and `IDX = 5`. 89 steps. -/
theorem loop_take_gt_di3_idx4 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 3)
    (hSKlo : (s.mem.get 2320).toNat < 3)
    (hI : s.mem.get 29 = 4)
    (hRlo : 4 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s89 := runN s 89
    s89.pc = 1641 ∧
    s89.halted = false ∧
    s89.mem.get 0 = 0 ∧
    s89.mem.get 36 = s.mem.get 23 ∧
    s89.mem.get 29 = 5 ∧
    s89.mem.get 2321 = 4 ∧
    (∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s89.mem.get a = s.mem.get a) := by
  intro s89
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 3 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = s.mem.get 2320 := hpres10 2320 (by decide) (by decide)
  have hSKlo10 : (s10.mem.get 2320).toNat < (s10.mem.get 2321).toNat := by
    rw [hSK10, hs10DI]; exact hSKlo
  have hDIhi10 : (s10.mem.get 2321).toNat < 32768 := by rw [hs10DI]; simp
  have hQ10 : s10.mem.get 23 = s.mem.get 23 := hpres10 23 (by decide) (by decide)
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1698 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_gt (s := s10) hs10pc hs10h hs10Z hSKlo10 hDIhi10 g10
  have hrun17 : runN s 17 = runN s10 7 := runN_add_eq s 10 7 17 (by decide)
  let s17 := runN s 17
  have hs17eq : s17 = runN s10 7 := hrun17
  have hs17pc : s17.pc = 1716 := by rw [hs17eq]; exact htk.1
  have hs17h : s17.halted = false := by rw [hs17eq]; exact htk.2.1
  have hs17Z : s17.mem.get 0 = 0 := by rw [hs17eq]; exact htk.2.2.1
  have hs17DI : s17.mem.get 2321 = 3 := by rw [hs17eq, htk.2.2.2.1, hs10DI]
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs17eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE17 : s17.mem.get 3 = 1 := (hpres17 3 (by decide) (by decide)).trans hONE
  have hI17 : s17.mem.get 29 = 4 := (hpres17 29 (by decide) (by decide)).trans hI
  have hR17 : s17.mem.get 28 = s.mem.get 28 := hpres17 28 (by decide) (by decide)
  have hQ17 : s17.mem.get 23 = s.mem.get 23 := hpres17 23 (by decide) (by decide)
  have g17S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g17E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo17 : 4 < (s17.mem.get 28).toNat := by rw [hR17]; exact hRlo
  have hRhi17 : (s17.mem.get 28).toNat < 32768 := by rw [hR17]; exact hRhi
  have hts := take_store_next_di3_idx4 (s := s17) hs17pc hs17h hs17Z hONE17 hs17DI hI17 hRlo17 hRhi17 g17S g17E
  have hrun : s89 = runN s17 72 := runN_add_eq s 17 72 89 (by decide)
  have hsTpc : s89.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s89.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s89.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s89.mem.get 36 = s.mem.get 23 := by
    rw [hrun, hts.2.2.2.1, hQ17]
  have hsTI : s89.mem.get 29 = 5 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s89.mem.get 2321 = 4 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s89.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres17 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `4 = DI > SK` and `IDX = 1 < ROOM`: take `Q4`,
store it, and return to `DIG_LOOP` with `DI = 5` and `IDX = 2`. 83 steps. -/
theorem loop_take_gt_di4_idx1 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 4)
    (hSKlo : (s.mem.get 2320).toNat < 4)
    (hI : s.mem.get 29 = 1)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s83 := runN s 83
    s83.pc = 1641 ∧
    s83.halted = false ∧
    s83.mem.get 0 = 0 ∧
    s83.mem.get 33 = s.mem.get 24 ∧
    s83.mem.get 29 = 2 ∧
    s83.mem.get 2321 = 5 ∧
    (∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s83.mem.get a = s.mem.get a) := by
  intro s83
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 4 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = s.mem.get 2320 := hpres10 2320 (by decide) (by decide)
  have hSKlo10 : (s10.mem.get 2320).toNat < (s10.mem.get 2321).toNat := by
    rw [hSK10, hs10DI]; exact hSKlo
  have hDIhi10 : (s10.mem.get 2321).toNat < 32768 := by rw [hs10DI]; simp
  have hQ10 : s10.mem.get 24 = s.mem.get 24 := hpres10 24 (by decide) (by decide)
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1698 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_gt (s := s10) hs10pc hs10h hs10Z hSKlo10 hDIhi10 g10
  have hrun17 : runN s 17 = runN s10 7 := runN_add_eq s 10 7 17 (by decide)
  let s17 := runN s 17
  have hs17eq : s17 = runN s10 7 := hrun17
  have hs17pc : s17.pc = 1716 := by rw [hs17eq]; exact htk.1
  have hs17h : s17.halted = false := by rw [hs17eq]; exact htk.2.1
  have hs17Z : s17.mem.get 0 = 0 := by rw [hs17eq]; exact htk.2.2.1
  have hs17DI : s17.mem.get 2321 = 4 := by rw [hs17eq, htk.2.2.2.1, hs10DI]
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs17eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE17 : s17.mem.get 3 = 1 := (hpres17 3 (by decide) (by decide)).trans hONE
  have hI17 : s17.mem.get 29 = 1 := (hpres17 29 (by decide) (by decide)).trans hI
  have hR17 : s17.mem.get 28 = s.mem.get 28 := hpres17 28 (by decide) (by decide)
  have hQ17 : s17.mem.get 24 = s.mem.get 24 := hpres17 24 (by decide) (by decide)
  have g17S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g17E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo17 : 1 < (s17.mem.get 28).toNat := by rw [hR17]; exact hRlo
  have hRhi17 : (s17.mem.get 28).toNat < 32768 := by rw [hR17]; exact hRhi
  have hts := take_store_next_di4_idx1 (s := s17) hs17pc hs17h hs17Z hONE17 hs17DI hI17 hRlo17 hRhi17 g17S g17E
  have hrun : s83 = runN s17 66 := runN_add_eq s 17 66 83 (by decide)
  have hsTpc : s83.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s83.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s83.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s83.mem.get 33 = s.mem.get 24 := by
    rw [hrun, hts.2.2.2.1, hQ17]
  have hsTI : s83.mem.get 29 = 2 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s83.mem.get 2321 = 5 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s83.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres17 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `4 = DI > SK` and `IDX = 2 < ROOM`: take `Q4`,
store it, and return to `DIG_LOOP` with `DI = 5` and `IDX = 3`. 85 steps. -/
theorem loop_take_gt_di4_idx2 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 4)
    (hSKlo : (s.mem.get 2320).toNat < 4)
    (hI : s.mem.get 29 = 2)
    (hRlo : 2 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s85 := runN s 85
    s85.pc = 1641 ∧
    s85.halted = false ∧
    s85.mem.get 0 = 0 ∧
    s85.mem.get 34 = s.mem.get 24 ∧
    s85.mem.get 29 = 3 ∧
    s85.mem.get 2321 = 5 ∧
    (∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s85.mem.get a = s.mem.get a) := by
  intro s85
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 4 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = s.mem.get 2320 := hpres10 2320 (by decide) (by decide)
  have hSKlo10 : (s10.mem.get 2320).toNat < (s10.mem.get 2321).toNat := by
    rw [hSK10, hs10DI]; exact hSKlo
  have hDIhi10 : (s10.mem.get 2321).toNat < 32768 := by rw [hs10DI]; simp
  have hQ10 : s10.mem.get 24 = s.mem.get 24 := hpres10 24 (by decide) (by decide)
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1698 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_gt (s := s10) hs10pc hs10h hs10Z hSKlo10 hDIhi10 g10
  have hrun17 : runN s 17 = runN s10 7 := runN_add_eq s 10 7 17 (by decide)
  let s17 := runN s 17
  have hs17eq : s17 = runN s10 7 := hrun17
  have hs17pc : s17.pc = 1716 := by rw [hs17eq]; exact htk.1
  have hs17h : s17.halted = false := by rw [hs17eq]; exact htk.2.1
  have hs17Z : s17.mem.get 0 = 0 := by rw [hs17eq]; exact htk.2.2.1
  have hs17DI : s17.mem.get 2321 = 4 := by rw [hs17eq, htk.2.2.2.1, hs10DI]
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs17eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE17 : s17.mem.get 3 = 1 := (hpres17 3 (by decide) (by decide)).trans hONE
  have hI17 : s17.mem.get 29 = 2 := (hpres17 29 (by decide) (by decide)).trans hI
  have hR17 : s17.mem.get 28 = s.mem.get 28 := hpres17 28 (by decide) (by decide)
  have hQ17 : s17.mem.get 24 = s.mem.get 24 := hpres17 24 (by decide) (by decide)
  have g17S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g17E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo17 : 2 < (s17.mem.get 28).toNat := by rw [hR17]; exact hRlo
  have hRhi17 : (s17.mem.get 28).toNat < 32768 := by rw [hR17]; exact hRhi
  have hts := take_store_next_di4_idx2 (s := s17) hs17pc hs17h hs17Z hONE17 hs17DI hI17 hRlo17 hRhi17 g17S g17E
  have hrun : s85 = runN s17 68 := runN_add_eq s 17 68 85 (by decide)
  have hsTpc : s85.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s85.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s85.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s85.mem.get 34 = s.mem.get 24 := by
    rw [hrun, hts.2.2.2.1, hQ17]
  have hsTI : s85.mem.get 29 = 3 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s85.mem.get 2321 = 5 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s85.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres17 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `4 = DI > SK` and `IDX = 3 < ROOM`: take `Q4`,
store it, and return to `DIG_LOOP` with `DI = 5` and `IDX = 4`. 87 steps. -/
theorem loop_take_gt_di4_idx3 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 4)
    (hSKlo : (s.mem.get 2320).toNat < 4)
    (hI : s.mem.get 29 = 3)
    (hRlo : 3 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s87 := runN s 87
    s87.pc = 1641 ∧
    s87.halted = false ∧
    s87.mem.get 0 = 0 ∧
    s87.mem.get 35 = s.mem.get 24 ∧
    s87.mem.get 29 = 4 ∧
    s87.mem.get 2321 = 5 ∧
    (∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s87.mem.get a = s.mem.get a) := by
  intro s87
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 4 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = s.mem.get 2320 := hpres10 2320 (by decide) (by decide)
  have hSKlo10 : (s10.mem.get 2320).toNat < (s10.mem.get 2321).toNat := by
    rw [hSK10, hs10DI]; exact hSKlo
  have hDIhi10 : (s10.mem.get 2321).toNat < 32768 := by rw [hs10DI]; simp
  have hQ10 : s10.mem.get 24 = s.mem.get 24 := hpres10 24 (by decide) (by decide)
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1698 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_gt (s := s10) hs10pc hs10h hs10Z hSKlo10 hDIhi10 g10
  have hrun17 : runN s 17 = runN s10 7 := runN_add_eq s 10 7 17 (by decide)
  let s17 := runN s 17
  have hs17eq : s17 = runN s10 7 := hrun17
  have hs17pc : s17.pc = 1716 := by rw [hs17eq]; exact htk.1
  have hs17h : s17.halted = false := by rw [hs17eq]; exact htk.2.1
  have hs17Z : s17.mem.get 0 = 0 := by rw [hs17eq]; exact htk.2.2.1
  have hs17DI : s17.mem.get 2321 = 4 := by rw [hs17eq, htk.2.2.2.1, hs10DI]
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs17eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE17 : s17.mem.get 3 = 1 := (hpres17 3 (by decide) (by decide)).trans hONE
  have hI17 : s17.mem.get 29 = 3 := (hpres17 29 (by decide) (by decide)).trans hI
  have hR17 : s17.mem.get 28 = s.mem.get 28 := hpres17 28 (by decide) (by decide)
  have hQ17 : s17.mem.get 24 = s.mem.get 24 := hpres17 24 (by decide) (by decide)
  have g17S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g17E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo17 : 3 < (s17.mem.get 28).toNat := by rw [hR17]; exact hRlo
  have hRhi17 : (s17.mem.get 28).toNat < 32768 := by rw [hR17]; exact hRhi
  have hts := take_store_next_di4_idx3 (s := s17) hs17pc hs17h hs17Z hONE17 hs17DI hI17 hRlo17 hRhi17 g17S g17E
  have hrun : s87 = runN s17 70 := runN_add_eq s 17 70 87 (by decide)
  have hsTpc : s87.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s87.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s87.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s87.mem.get 35 = s.mem.get 24 := by
    rw [hrun, hts.2.2.2.1, hQ17]
  have hsTI : s87.mem.get 29 = 4 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s87.mem.get 2321 = 5 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s87.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres17 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `4 = DI > SK` and `IDX = 4 < ROOM`: take `Q4`,
store it, and return to `DIG_LOOP` with `DI = 5` and `IDX = 5`. 89 steps. -/
theorem loop_take_gt_di4_idx4 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 4)
    (hSKlo : (s.mem.get 2320).toNat < 4)
    (hI : s.mem.get 29 = 4)
    (hRlo : 4 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s89 := runN s 89
    s89.pc = 1641 ∧
    s89.halted = false ∧
    s89.mem.get 0 = 0 ∧
    s89.mem.get 36 = s.mem.get 24 ∧
    s89.mem.get 29 = 5 ∧
    s89.mem.get 2321 = 5 ∧
    (∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s89.mem.get a = s.mem.get a) := by
  intro s89
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 4 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = s.mem.get 2320 := hpres10 2320 (by decide) (by decide)
  have hSKlo10 : (s10.mem.get 2320).toNat < (s10.mem.get 2321).toNat := by
    rw [hSK10, hs10DI]; exact hSKlo
  have hDIhi10 : (s10.mem.get 2321).toNat < 32768 := by rw [hs10DI]; simp
  have hQ10 : s10.mem.get 24 = s.mem.get 24 := hpres10 24 (by decide) (by decide)
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1698 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_gt (s := s10) hs10pc hs10h hs10Z hSKlo10 hDIhi10 g10
  have hrun17 : runN s 17 = runN s10 7 := runN_add_eq s 10 7 17 (by decide)
  let s17 := runN s 17
  have hs17eq : s17 = runN s10 7 := hrun17
  have hs17pc : s17.pc = 1716 := by rw [hs17eq]; exact htk.1
  have hs17h : s17.halted = false := by rw [hs17eq]; exact htk.2.1
  have hs17Z : s17.mem.get 0 = 0 := by rw [hs17eq]; exact htk.2.2.1
  have hs17DI : s17.mem.get 2321 = 4 := by rw [hs17eq, htk.2.2.2.1, hs10DI]
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs17eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE17 : s17.mem.get 3 = 1 := (hpres17 3 (by decide) (by decide)).trans hONE
  have hI17 : s17.mem.get 29 = 4 := (hpres17 29 (by decide) (by decide)).trans hI
  have hR17 : s17.mem.get 28 = s.mem.get 28 := hpres17 28 (by decide) (by decide)
  have hQ17 : s17.mem.get 24 = s.mem.get 24 := hpres17 24 (by decide) (by decide)
  have g17S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g17E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo17 : 4 < (s17.mem.get 28).toNat := by rw [hR17]; exact hRlo
  have hRhi17 : (s17.mem.get 28).toNat < 32768 := by rw [hR17]; exact hRhi
  have hts := take_store_next_di4_idx4 (s := s17) hs17pc hs17h hs17Z hONE17 hs17DI hI17 hRlo17 hRhi17 g17S g17E
  have hrun : s89 = runN s17 72 := runN_add_eq s 17 72 89 (by decide)
  have hsTpc : s89.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s89.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s89.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s89.mem.get 36 = s.mem.get 24 := by
    rw [hrun, hts.2.2.2.1, hQ17]
  have hsTI : s89.mem.get 29 = 5 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s89.mem.get 2321 = 5 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s89.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres17 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- `DIG_LOOP` with `4 = DI > SK` and `IDX = 5 < ROOM`: take `Q4`,
store it, and return to `DIG_LOOP` with `DI = 5` and `IDX = 6`. 91 steps. -/
theorem loop_take_gt_di4_idx5 {s : Machine}
    (hpc : s.pc = 1641)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hDI : s.mem.get 2321 = 4)
    (hSKlo : (s.mem.get 2320).toNat < 4)
    (hI : s.mem.get 29 = 5)
    (hRlo : 5 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcodeS : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!)
    (hcodeE : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s91 := runN s 91
    s91.pc = 1641 ∧
    s91.halted = false ∧
    s91.mem.get 0 = 0 ∧
    s91.mem.get 37 = s.mem.get 24 ∧
    s91.mem.get 29 = 6 ∧
    s91.mem.get 2321 = 5 ∧
    (∀ a, a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s91.mem.get a = s.mem.get a) := by
  intro s91
  have hDIlt5 : (s.mem.get 2321).toNat < 5 := by rw [hDI]; simp
  have hb := dig_loop_to_body (s := s) hpc hh hZ hONE hDIlt5 hK5
    (fun k h1 h2 => hcodeE k h1 (by omega))
  let s10 := runN s 10
  have hs10pc : s10.pc = 1677 := hb.1
  have hs10h : s10.halted = false := hb.2.1
  have hs10Z : s10.mem.get 0 = 0 := hb.2.2.1
  have hs10DI : s10.mem.get 2321 = 4 := hb.2.2.2.1.trans hDI
  have hpres10 := hb.2.2.2.2
  have hONE10 : s10.mem.get 3 = 1 := (hpres10 3 (by decide) (by decide)).trans hONE
  have hSK10 : s10.mem.get 2320 = s.mem.get 2320 := hpres10 2320 (by decide) (by decide)
  have hSKlo10 : (s10.mem.get 2320).toNat < (s10.mem.get 2321).toNat := by
    rw [hSK10, hs10DI]; exact hSKlo
  have hDIhi10 : (s10.mem.get 2321).toNat < 32768 := by rw [hs10DI]; simp
  have hQ10 : s10.mem.get 24 = s.mem.get 24 := hpres10 24 (by decide) (by decide)
  have g10 : ∀ k : Nat, 1677 ≤ k → k < 1698 →
      s10.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres10 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have htk := dig_body_take_gt (s := s10) hs10pc hs10h hs10Z hSKlo10 hDIhi10 g10
  have hrun17 : runN s 17 = runN s10 7 := runN_add_eq s 10 7 17 (by decide)
  let s17 := runN s 17
  have hs17eq : s17 = runN s10 7 := hrun17
  have hs17pc : s17.pc = 1716 := by rw [hs17eq]; exact htk.1
  have hs17h : s17.halted = false := by rw [hs17eq]; exact htk.2.1
  have hs17Z : s17.mem.get 0 = 0 := by rw [hs17eq]; exact htk.2.2.1
  have hs17DI : s17.mem.get 2321 = 4 := by rw [hs17eq, htk.2.2.2.1, hs10DI]
  have hpres17 : ∀ a, a ≠ 18 → a ≠ 0 → s17.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs17eq]; exact (htk.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hONE17 : s17.mem.get 3 = 1 := (hpres17 3 (by decide) (by decide)).trans hONE
  have hI17 : s17.mem.get 29 = 5 := (hpres17 29 (by decide) (by decide)).trans hI
  have hR17 : s17.mem.get 28 = s.mem.get 28 := hpres17 28 (by decide) (by decide)
  have hQ17 : s17.mem.get 24 = s.mem.get 24 := hpres17 24 (by decide) (by decide)
  have g17S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeS k (by omega) (by omega))
  have g17E : ∀ k : Nat, 1716 ≤ k → k < 1905 →
      s17.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres17 (UInt16.ofNat k) n18 n0).trans (hcodeE k (by omega) (by omega))
  have hRlo17 : 5 < (s17.mem.get 28).toNat := by rw [hR17]; exact hRlo
  have hRhi17 : (s17.mem.get 28).toNat < 32768 := by rw [hR17]; exact hRhi
  have hts := take_store_next_di4_idx5 (s := s17) hs17pc hs17h hs17Z hONE17 hs17DI hI17 hRlo17 hRhi17 g17S g17E
  have hrun : s91 = runN s17 74 := runN_add_eq s 17 74 91 (by decide)
  have hsTpc : s91.pc = 1641 := by rw [hrun]; exact hts.1
  have hsTh : s91.halted = false := by rw [hrun]; exact hts.2.1
  have hsTZ : s91.mem.get 0 = 0 := by rw [hrun]; exact hts.2.2.1
  have hsTB : s91.mem.get 37 = s.mem.get 24 := by
    rw [hrun, hts.2.2.2.1, hQ17]
  have hsTI : s91.mem.get 29 = 6 := by rw [hrun]; exact hts.2.2.2.2.1
  have hsTDI : s91.mem.get 2321 = 5 := by rw [hrun]; exact hts.2.2.2.2.2.1
  have hpres : ∀ a, a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 2319 → a ≠ 2321 → a ≠ 0 →
      s91.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 haR haDI ha0
    rw [hrun]
    exact (hts.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres17 a ha18 ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB, hsTI, hsTDI, hpres⟩

/-- From `EMIT_DIGS` with `NDIG = 1` and `IDX = 0 < ROOM`: skip `Q0`..`Q3`,
store `Q4` at `BUF+0`, and reach `AFTER_DIGS` with `IDX = 1`. 218 steps. -/
theorem emit_ndig1_idx0 {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 1)
    (hI : s.mem.get 29 = 0)
    (hRlo : 0 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s218 := runN s 218
    s218.pc = 1905 ∧
    s218.halted = false ∧
    s218.mem.get 0 = 0 ∧
    s218.mem.get 32 = s.mem.get 24 ∧
    s218.mem.get 29 = 1 ∧
    (∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s218.mem.get a = s.mem.get a) := by
  intro s218
  have hNle : (s.mem.get 25).toNat ≤ 5 := by rw [hN]; simp
  have hp := emit_prelude (s := s) hpc hh hZ hONE hNle
    (fun k h1 h2 => hcode k (by omega) (by omega))
  let s22 := runN s 22
  have hs22pc : s22.pc = 1641 := hp.1
  have hs22h : s22.halted = false := hp.2.1
  have hs22Z : s22.mem.get 0 = 0 := hp.2.2.1
  have hs22SK : s22.mem.get 2320 = 4 := by
    rw [hp.2.2.2.1, hN]
    exact (rfl : (5 : Word) - 1 = 4)
  have hs22DI : s22.mem.get 2321 = 0 := hp.2.2.2.2.1
  have hpres22raw := hp.2.2.2.2.2.2
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s22.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    exact hpres22raw a ha31 haSK haDI ha0
  have hONE22 : s22.mem.get 3 = 1 := (hpres22 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK522 : s22.mem.get 2322 = 5 := (hpres22 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hI22 : s22.mem.get 29 = 0 := (hpres22 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR22 : s22.mem.get 28 = s.mem.get 28 := hpres22 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ422 : s22.mem.get 24 = s.mem.get 24 := hpres22 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g22 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s22.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres22 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_22 : (s22.mem.get 2321).toNat < 5 := by rw [hs22DI]; simp
  have hDIltSK_22 : (s22.mem.get 2321).toNat < (s22.mem.get 2320).toNat := by
    rw [hs22DI, hs22SK]; simp
  have hSKhi_22 : (s22.mem.get 2320).toNat < 32768 := by rw [hs22SK]; simp
  have hsk22 := skip_next (s := s22) hs22pc hs22h hs22Z hONE22 hK522
    hDIlt5_22 hDIltSK_22 hSKhi_22 g22
  have hrun47 : runN s 47 = runN s22 25 := runN_add_eq s 22 25 47 (by decide)
  let s47 := runN s 47
  have hs47eq : s47 = runN s22 25 := hrun47
  have hs47pc : s47.pc = 1641 := by rw [hs47eq]; exact hsk22.1
  have hs47h : s47.halted = false := by rw [hs47eq]; exact hsk22.2.1
  have hs47Z : s47.mem.get 0 = 0 := by rw [hs47eq]; exact hsk22.2.2.1
  have hs47DI : s47.mem.get 2321 = 1 := by
    rw [hs47eq, hsk22.2.2.2.1, hs22DI]
    exact (rfl : (0 : Word) + 1 = 1)
  have hpres47 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s47.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs47eq]
    exact (hsk22.2.2.2.2 a ha18 haDI ha0).trans (hpres22 a ha18 ha31 haSK haDI ha0)
  have hONE47 : s47.mem.get 3 = 1 := (hpres47 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK547 : s47.mem.get 2322 = 5 := (hpres47 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs47SK : s47.mem.get 2320 = 4 := by
    rw [hs47eq]; exact (hsk22.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs22SK
  have hI47 : s47.mem.get 29 = 0 := (hpres47 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR47 : s47.mem.get 28 = s.mem.get 28 := hpres47 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ447 : s47.mem.get 24 = s.mem.get 24 := hpres47 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g47 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s47.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres47 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_47 : (s47.mem.get 2321).toNat < 5 := by rw [hs47DI]; simp
  have hDIltSK_47 : (s47.mem.get 2321).toNat < (s47.mem.get 2320).toNat := by
    rw [hs47DI, hs47SK]; simp
  have hSKhi_47 : (s47.mem.get 2320).toNat < 32768 := by rw [hs47SK]; simp
  have hsk47 := skip_next (s := s47) hs47pc hs47h hs47Z hONE47 hK547
    hDIlt5_47 hDIltSK_47 hSKhi_47 g47
  have hrun72 : runN s 72 = runN s47 25 := runN_add_eq s 47 25 72 (by decide)
  let s72 := runN s 72
  have hs72eq : s72 = runN s47 25 := hrun72
  have hs72pc : s72.pc = 1641 := by rw [hs72eq]; exact hsk47.1
  have hs72h : s72.halted = false := by rw [hs72eq]; exact hsk47.2.1
  have hs72Z : s72.mem.get 0 = 0 := by rw [hs72eq]; exact hsk47.2.2.1
  have hs72DI : s72.mem.get 2321 = 2 := by
    rw [hs72eq, hsk47.2.2.2.1, hs47DI]
    exact (rfl : (1 : Word) + 1 = 2)
  have hpres72 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s72.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs72eq]
    exact (hsk47.2.2.2.2 a ha18 haDI ha0).trans (hpres47 a ha18 ha31 haSK haDI ha0)
  have hONE72 : s72.mem.get 3 = 1 := (hpres72 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK572 : s72.mem.get 2322 = 5 := (hpres72 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs72SK : s72.mem.get 2320 = 4 := by
    rw [hs72eq]; exact (hsk47.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs47SK
  have hI72 : s72.mem.get 29 = 0 := (hpres72 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR72 : s72.mem.get 28 = s.mem.get 28 := hpres72 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ472 : s72.mem.get 24 = s.mem.get 24 := hpres72 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g72 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s72.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres72 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_72 : (s72.mem.get 2321).toNat < 5 := by rw [hs72DI]; simp
  have hDIltSK_72 : (s72.mem.get 2321).toNat < (s72.mem.get 2320).toNat := by
    rw [hs72DI, hs72SK]; simp
  have hSKhi_72 : (s72.mem.get 2320).toNat < 32768 := by rw [hs72SK]; simp
  have hsk72 := skip_next (s := s72) hs72pc hs72h hs72Z hONE72 hK572
    hDIlt5_72 hDIltSK_72 hSKhi_72 g72
  have hrun97 : runN s 97 = runN s72 25 := runN_add_eq s 72 25 97 (by decide)
  let s97 := runN s 97
  have hs97eq : s97 = runN s72 25 := hrun97
  have hs97pc : s97.pc = 1641 := by rw [hs97eq]; exact hsk72.1
  have hs97h : s97.halted = false := by rw [hs97eq]; exact hsk72.2.1
  have hs97Z : s97.mem.get 0 = 0 := by rw [hs97eq]; exact hsk72.2.2.1
  have hs97DI : s97.mem.get 2321 = 3 := by
    rw [hs97eq, hsk72.2.2.2.1, hs72DI]
    exact (rfl : (2 : Word) + 1 = 3)
  have hpres97 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s97.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs97eq]
    exact (hsk72.2.2.2.2 a ha18 haDI ha0).trans (hpres72 a ha18 ha31 haSK haDI ha0)
  have hONE97 : s97.mem.get 3 = 1 := (hpres97 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK597 : s97.mem.get 2322 = 5 := (hpres97 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs97SK : s97.mem.get 2320 = 4 := by
    rw [hs97eq]; exact (hsk72.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs72SK
  have hI97 : s97.mem.get 29 = 0 := (hpres97 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR97 : s97.mem.get 28 = s.mem.get 28 := hpres97 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ497 : s97.mem.get 24 = s.mem.get 24 := hpres97 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g97 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s97.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres97 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_97 : (s97.mem.get 2321).toNat < 5 := by rw [hs97DI]; simp
  have hDIltSK_97 : (s97.mem.get 2321).toNat < (s97.mem.get 2320).toNat := by
    rw [hs97DI, hs97SK]; simp
  have hSKhi_97 : (s97.mem.get 2320).toNat < 32768 := by rw [hs97SK]; simp
  have hsk97 := skip_next (s := s97) hs97pc hs97h hs97Z hONE97 hK597
    hDIlt5_97 hDIltSK_97 hSKhi_97 g97
  have hrun122 : runN s 122 = runN s97 25 := runN_add_eq s 97 25 122 (by decide)
  let s122 := runN s 122
  have hs122eq : s122 = runN s97 25 := hrun122
  have hs122pc : s122.pc = 1641 := by rw [hs122eq]; exact hsk97.1
  have hs122h : s122.halted = false := by rw [hs122eq]; exact hsk97.2.1
  have hs122Z : s122.mem.get 0 = 0 := by rw [hs122eq]; exact hsk97.2.2.1
  have hs122DI : s122.mem.get 2321 = 4 := by
    rw [hs122eq, hsk97.2.2.2.1, hs97DI]
    exact (rfl : (3 : Word) + 1 = 4)
  have hpres122 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s122.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs122eq]
    exact (hsk97.2.2.2.2 a ha18 haDI ha0).trans (hpres97 a ha18 ha31 haSK haDI ha0)
  have hONE122 : s122.mem.get 3 = 1 := (hpres122 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5122 : s122.mem.get 2322 = 5 := (hpres122 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs122SK : s122.mem.get 2320 = 4 := by
    rw [hs122eq]; exact (hsk97.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs97SK
  have hI122 : s122.mem.get 29 = 0 := (hpres122 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR122 : s122.mem.get 28 = s.mem.get 28 := hpres122 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ4122 : s122.mem.get 24 = s.mem.get 24 := hpres122 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g122 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s122.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres122 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have g122S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s122.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres122 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo122 : 0 < (s122.mem.get 28).toNat := by rw [hR122]; exact hRlo
  have hRhi122 : (s122.mem.get 28).toNat < 32768 := by rw [hR122]; exact hRhi
  have ht := loop_take_eq_di4_idx0 (s := s122) hs122pc hs122h hs122Z hONE122 hK5122 hs122DI hs122SK hI122 hRlo122 hRhi122 g122S g122
  have hrun207 : runN s 207 = runN s122 85 := runN_add_eq s 122 85 207 (by decide)
  let s207 := runN s 207
  have hs207eq : s207 = runN s122 85 := hrun207
  have hs207pc : s207.pc = 1641 := by rw [hs207eq]; exact ht.1
  have hs207h : s207.halted = false := by rw [hs207eq]; exact ht.2.1
  have hs207Z : s207.mem.get 0 = 0 := by rw [hs207eq]; exact ht.2.2.1
  have hs207B : s207.mem.get 32 = s.mem.get 24 := by
    rw [hs207eq, ht.2.2.2.1, hQ4122]
  have hI207 : s207.mem.get 29 = 1 := by rw [hs207eq]; exact ht.2.2.2.2.1
  have hs207DI : s207.mem.get 2321 = 5 := by rw [hs207eq]; exact ht.2.2.2.2.2.1
  have hpres207 : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s207.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs207eq]
    exact (ht.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans
      (hpres122 a ha18 ha31 haSK haDI ha0)
  have hONE207 : s207.mem.get 3 = 1 := (hpres207 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5207 : s207.mem.get 2322 = 5 := (hpres207 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have g207 : ∀ k : Nat, 1641 ≤ k → k < 1677 →
      s207.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres207 (UInt16.ofNat k) n32 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans
      (hcode k (by omega) (by omega))
  have hx := dig_loop_exit (s := s207) hs207pc hs207h hs207Z hONE207 hs207DI hK5207 g207
  have hrun : s218 = runN s207 11 := runN_add_eq s 207 11 218 (by decide)
  have hs218pc : s218.pc = 1905 := by rw [hrun]; exact hx.1
  have hs218h : s218.halted = false := by rw [hrun]; exact hx.2.1
  have hs218Z : s218.mem.get 0 = 0 := by rw [hrun]; exact hx.2.2.1
  have hs218B : s218.mem.get 32 = s.mem.get 24 := by
    rw [hrun]; exact (hx.2.2.2.2 32 (by decide) (by decide)).trans hs207B
  have hI218 : s218.mem.get 29 = 1 := by
    rw [hrun]; exact (hx.2.2.2.2 29 (by decide) (by decide)).trans hI207
  have hpres : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s218.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hrun]
    exact (hx.2.2.2.2 a ha18 ha0).trans (hpres207 a haB ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  exact ⟨hs218pc, hs218h, hs218Z, hs218B, hI218, hpres⟩

/-- From `EMIT_DIGS` with `NDIG = 1` and `IDX = 1 < ROOM`: write
`Q4`..`Q4` at `BUF+1`..`BUF+1` and reach `AFTER_DIGS`
with `IDX = 2`. 220 steps. -/
theorem emit_ndig1_idx1 {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 1)
    (hI : s.mem.get 29 = 1)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s220 := runN s 220
    s220.pc = 1905 ∧
    s220.halted = false ∧
    s220.mem.get 0 = 0 ∧
    s220.mem.get 33 = s.mem.get 24 ∧
    s220.mem.get 29 = 2 ∧
    (∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s220.mem.get a = s.mem.get a) := by
  intro s220
  have hNle : (s.mem.get 25).toNat ≤ 5 := by rw [hN]; simp
  have hp := emit_prelude (s := s) hpc hh hZ hONE hNle
    (fun k h1 h2 => hcode k (by omega) (by omega))
  let s22 := runN s 22
  have hs22pc : s22.pc = 1641 := hp.1
  have hs22h : s22.halted = false := hp.2.1
  have hs22Z : s22.mem.get 0 = 0 := hp.2.2.1
  have hs22SK : s22.mem.get 2320 = 4 := by
    rw [hp.2.2.2.1, hN]
    exact (rfl : (5 : Word) - 1 = 4)
  have hs22DI : s22.mem.get 2321 = 0 := hp.2.2.2.2.1
  have hpres22raw := hp.2.2.2.2.2.2
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s22.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    exact hpres22raw a ha31 haSK haDI ha0
  have hONE22 : s22.mem.get 3 = 1 := (hpres22 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK522 : s22.mem.get 2322 = 5 := (hpres22 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hI22 : s22.mem.get 29 = 1 := (hpres22 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR22 : s22.mem.get 28 = s.mem.get 28 := hpres22 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2422 : s22.mem.get 24 = s.mem.get 24 := hpres22 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g22 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s22.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres22 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_22 : (s22.mem.get 2321).toNat < 5 := by rw [hs22DI]; simp
  have hDIltSK_22 : (s22.mem.get 2321).toNat < (s22.mem.get 2320).toNat := by
    rw [hs22DI, hs22SK]; simp
  have hSKhi_22 : (s22.mem.get 2320).toNat < 32768 := by rw [hs22SK]; simp
  have hsk22 := skip_next (s := s22) hs22pc hs22h hs22Z hONE22 hK522
    hDIlt5_22 hDIltSK_22 hSKhi_22 g22
  have hrun47 : runN s 47 = runN s22 25 := runN_add_eq s 22 25 47 (by decide)
  let s47 := runN s 47
  have hs47eq : s47 = runN s22 25 := hrun47
  have hs47pc : s47.pc = 1641 := by rw [hs47eq]; exact hsk22.1
  have hs47h : s47.halted = false := by rw [hs47eq]; exact hsk22.2.1
  have hs47Z : s47.mem.get 0 = 0 := by rw [hs47eq]; exact hsk22.2.2.1
  have hs47DI : s47.mem.get 2321 = 1 := by
    rw [hs47eq, hsk22.2.2.2.1, hs22DI]
    exact (rfl : (0 : Word) + 1 = 1)
  have hpres47 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s47.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs47eq]
    exact (hsk22.2.2.2.2 a ha18 haDI ha0).trans (hpres22 a ha18 ha31 haSK haDI ha0)
  have hONE47 : s47.mem.get 3 = 1 := (hpres47 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK547 : s47.mem.get 2322 = 5 := (hpres47 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs47SK : s47.mem.get 2320 = 4 := by
    rw [hs47eq]; exact (hsk22.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs22SK
  have hI47 : s47.mem.get 29 = 1 := (hpres47 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR47 : s47.mem.get 28 = s.mem.get 28 := hpres47 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2447 : s47.mem.get 24 = s.mem.get 24 := hpres47 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g47 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s47.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres47 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_47 : (s47.mem.get 2321).toNat < 5 := by rw [hs47DI]; simp
  have hDIltSK_47 : (s47.mem.get 2321).toNat < (s47.mem.get 2320).toNat := by
    rw [hs47DI, hs47SK]; simp
  have hSKhi_47 : (s47.mem.get 2320).toNat < 32768 := by rw [hs47SK]; simp
  have hsk47 := skip_next (s := s47) hs47pc hs47h hs47Z hONE47 hK547
    hDIlt5_47 hDIltSK_47 hSKhi_47 g47
  have hrun72 : runN s 72 = runN s47 25 := runN_add_eq s 47 25 72 (by decide)
  let s72 := runN s 72
  have hs72eq : s72 = runN s47 25 := hrun72
  have hs72pc : s72.pc = 1641 := by rw [hs72eq]; exact hsk47.1
  have hs72h : s72.halted = false := by rw [hs72eq]; exact hsk47.2.1
  have hs72Z : s72.mem.get 0 = 0 := by rw [hs72eq]; exact hsk47.2.2.1
  have hs72DI : s72.mem.get 2321 = 2 := by
    rw [hs72eq, hsk47.2.2.2.1, hs47DI]
    exact (rfl : (1 : Word) + 1 = 2)
  have hpres72 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s72.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs72eq]
    exact (hsk47.2.2.2.2 a ha18 haDI ha0).trans (hpres47 a ha18 ha31 haSK haDI ha0)
  have hONE72 : s72.mem.get 3 = 1 := (hpres72 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK572 : s72.mem.get 2322 = 5 := (hpres72 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs72SK : s72.mem.get 2320 = 4 := by
    rw [hs72eq]; exact (hsk47.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs47SK
  have hI72 : s72.mem.get 29 = 1 := (hpres72 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR72 : s72.mem.get 28 = s.mem.get 28 := hpres72 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2472 : s72.mem.get 24 = s.mem.get 24 := hpres72 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g72 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s72.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres72 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_72 : (s72.mem.get 2321).toNat < 5 := by rw [hs72DI]; simp
  have hDIltSK_72 : (s72.mem.get 2321).toNat < (s72.mem.get 2320).toNat := by
    rw [hs72DI, hs72SK]; simp
  have hSKhi_72 : (s72.mem.get 2320).toNat < 32768 := by rw [hs72SK]; simp
  have hsk72 := skip_next (s := s72) hs72pc hs72h hs72Z hONE72 hK572
    hDIlt5_72 hDIltSK_72 hSKhi_72 g72
  have hrun97 : runN s 97 = runN s72 25 := runN_add_eq s 72 25 97 (by decide)
  let s97 := runN s 97
  have hs97eq : s97 = runN s72 25 := hrun97
  have hs97pc : s97.pc = 1641 := by rw [hs97eq]; exact hsk72.1
  have hs97h : s97.halted = false := by rw [hs97eq]; exact hsk72.2.1
  have hs97Z : s97.mem.get 0 = 0 := by rw [hs97eq]; exact hsk72.2.2.1
  have hs97DI : s97.mem.get 2321 = 3 := by
    rw [hs97eq, hsk72.2.2.2.1, hs72DI]
    exact (rfl : (2 : Word) + 1 = 3)
  have hpres97 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s97.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs97eq]
    exact (hsk72.2.2.2.2 a ha18 haDI ha0).trans (hpres72 a ha18 ha31 haSK haDI ha0)
  have hONE97 : s97.mem.get 3 = 1 := (hpres97 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK597 : s97.mem.get 2322 = 5 := (hpres97 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs97SK : s97.mem.get 2320 = 4 := by
    rw [hs97eq]; exact (hsk72.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs72SK
  have hI97 : s97.mem.get 29 = 1 := (hpres97 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR97 : s97.mem.get 28 = s.mem.get 28 := hpres97 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2497 : s97.mem.get 24 = s.mem.get 24 := hpres97 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g97 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s97.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres97 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_97 : (s97.mem.get 2321).toNat < 5 := by rw [hs97DI]; simp
  have hDIltSK_97 : (s97.mem.get 2321).toNat < (s97.mem.get 2320).toNat := by
    rw [hs97DI, hs97SK]; simp
  have hSKhi_97 : (s97.mem.get 2320).toNat < 32768 := by rw [hs97SK]; simp
  have hsk97 := skip_next (s := s97) hs97pc hs97h hs97Z hONE97 hK597
    hDIlt5_97 hDIltSK_97 hSKhi_97 g97
  have hrun122 : runN s 122 = runN s97 25 := runN_add_eq s 97 25 122 (by decide)
  let s122 := runN s 122
  have hs122eq : s122 = runN s97 25 := hrun122
  have hs122pc : s122.pc = 1641 := by rw [hs122eq]; exact hsk97.1
  have hs122h : s122.halted = false := by rw [hs122eq]; exact hsk97.2.1
  have hs122Z : s122.mem.get 0 = 0 := by rw [hs122eq]; exact hsk97.2.2.1
  have hs122DI : s122.mem.get 2321 = 4 := by
    rw [hs122eq, hsk97.2.2.2.1, hs97DI]
    exact (rfl : (3 : Word) + 1 = 4)
  have hpres122 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s122.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs122eq]
    exact (hsk97.2.2.2.2 a ha18 haDI ha0).trans (hpres97 a ha18 ha31 haSK haDI ha0)
  have hONE122 : s122.mem.get 3 = 1 := (hpres122 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5122 : s122.mem.get 2322 = 5 := (hpres122 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs122SK : s122.mem.get 2320 = 4 := by
    rw [hs122eq]; exact (hsk97.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs97SK
  have hI122 : s122.mem.get 29 = 1 := (hpres122 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR122 : s122.mem.get 28 = s.mem.get 28 := hpres122 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24122 : s122.mem.get 24 = s.mem.get 24 := hpres122 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g122 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s122.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres122 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have g122S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s122.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres122 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo122 : 1 < (s122.mem.get 28).toNat := by
    rw [hR122]
    have : 1 ≤ 1 := by decide
    omega
  have hRhi122 : (s122.mem.get 28).toNat < 32768 := by rw [hR122]; exact hRhi
  have ht122 := loop_take_eq_di4_idx1 (s := s122) hs122pc hs122h hs122Z hONE122 hK5122 hs122DI hs122SK hI122 hRlo122 hRhi122 g122S g122
  have hrun209 : runN s 209 = runN s122 87 := runN_add_eq s 122 87 209 (by decide)
  let s209 := runN s 209
  have hs209eq : s209 = runN s122 87 := hrun209
  have hs209pc : s209.pc = 1641 := by rw [hs209eq]; exact ht122.1
  have hs209h : s209.halted = false := by rw [hs209eq]; exact ht122.2.1
  have hs209Z : s209.mem.get 0 = 0 := by rw [hs209eq]; exact ht122.2.2.1
  have hs209B33 : s209.mem.get 33 = s.mem.get 24 := by
    rw [hs209eq, ht122.2.2.2.1, hQ24122]
  have hI209 : s209.mem.get 29 = 2 := by rw [hs209eq]; exact ht122.2.2.2.2.1
  have hs209DI : s209.mem.get 2321 = 5 := by rw [hs209eq]; exact ht122.2.2.2.2.2.1
  have hpres209 : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s209.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs209eq]
    exact (ht122.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres122 a ha18 ha31 haSK haDI ha0)
  have hONE209 : s209.mem.get 3 = 1 := (hpres209 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5209 : s209.mem.get 2322 = 5 := (hpres209 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs209SK : s209.mem.get 2320 = 4 := by
    rw [hs209eq]
    exact (ht122.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs122SK
  have hR209 : s209.mem.get 28 = s.mem.get 28 := hpres209 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g209 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s209.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
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
    exact (hpres209 (UInt16.ofNat k) n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hONE209 : s209.mem.get 3 = 1 := (hpres209 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5209x : s209.mem.get 2322 = 5 := (hpres209 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have g209x : ∀ k : Nat, 1641 ≤ k → k < 1677 →
      s209.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
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
    exact (hpres209 (UInt16.ofNat k) n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hx := dig_loop_exit (s := s209) hs209pc hs209h hs209Z hONE209 hs209DI hK5209x g209x
  have hrun : s220 = runN s209 11 := runN_add_eq s 209 11 220 (by decide)
  have hsTpc : s220.pc = 1905 := by rw [hrun]; exact hx.1
  have hsTh : s220.halted = false := by rw [hrun]; exact hx.2.1
  have hsTZ : s220.mem.get 0 = 0 := by rw [hrun]; exact hx.2.2.1
  have hsTB33 : s220.mem.get 33 = s.mem.get 24 := by
    rw [hrun]; exact (hx.2.2.2.2 33 (by decide) (by decide)).trans hs209B33
  have hsTI : s220.mem.get 29 = 2 := by
    rw [hrun]; exact (hx.2.2.2.2 29 (by decide) (by decide)).trans hI209
  have hpres : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s220.mem.get a = s.mem.get a := by
    intro a haB33 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hrun]
    exact (hx.2.2.2.2 a ha18 ha0).trans (hpres209 a haB33 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB33, hsTI, hpres⟩


/-- From `EMIT_DIGS` with `NDIG = 2` and `IDX = 0 < ROOM`: write
`Q3`..`Q4` at `BUF+0`..`BUF+1` and reach `AFTER_DIGS`
with `IDX = 2`. 276 steps. -/
theorem emit_ndig2_idx0 {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 2)
    (hI : s.mem.get 29 = 0)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s276 := runN s 276
    s276.pc = 1905 ∧
    s276.halted = false ∧
    s276.mem.get 0 = 0 ∧
    s276.mem.get 32 = s.mem.get 23 ∧
    s276.mem.get 33 = s.mem.get 24 ∧
    s276.mem.get 29 = 2 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s276.mem.get a = s.mem.get a) := by
  intro s276
  have hNle : (s.mem.get 25).toNat ≤ 5 := by rw [hN]; simp
  have hp := emit_prelude (s := s) hpc hh hZ hONE hNle
    (fun k h1 h2 => hcode k (by omega) (by omega))
  let s22 := runN s 22
  have hs22pc : s22.pc = 1641 := hp.1
  have hs22h : s22.halted = false := hp.2.1
  have hs22Z : s22.mem.get 0 = 0 := hp.2.2.1
  have hs22SK : s22.mem.get 2320 = 3 := by
    rw [hp.2.2.2.1, hN]
    exact (rfl : (5 : Word) - 2 = 3)
  have hs22DI : s22.mem.get 2321 = 0 := hp.2.2.2.2.1
  have hpres22raw := hp.2.2.2.2.2.2
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s22.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    exact hpres22raw a ha31 haSK haDI ha0
  have hONE22 : s22.mem.get 3 = 1 := (hpres22 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK522 : s22.mem.get 2322 = 5 := (hpres22 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hI22 : s22.mem.get 29 = 0 := (hpres22 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR22 : s22.mem.get 28 = s.mem.get 28 := hpres22 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2322 : s22.mem.get 23 = s.mem.get 23 := hpres22 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2422 : s22.mem.get 24 = s.mem.get 24 := hpres22 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g22 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s22.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres22 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_22 : (s22.mem.get 2321).toNat < 5 := by rw [hs22DI]; simp
  have hDIltSK_22 : (s22.mem.get 2321).toNat < (s22.mem.get 2320).toNat := by
    rw [hs22DI, hs22SK]; simp
  have hSKhi_22 : (s22.mem.get 2320).toNat < 32768 := by rw [hs22SK]; simp
  have hsk22 := skip_next (s := s22) hs22pc hs22h hs22Z hONE22 hK522
    hDIlt5_22 hDIltSK_22 hSKhi_22 g22
  have hrun47 : runN s 47 = runN s22 25 := runN_add_eq s 22 25 47 (by decide)
  let s47 := runN s 47
  have hs47eq : s47 = runN s22 25 := hrun47
  have hs47pc : s47.pc = 1641 := by rw [hs47eq]; exact hsk22.1
  have hs47h : s47.halted = false := by rw [hs47eq]; exact hsk22.2.1
  have hs47Z : s47.mem.get 0 = 0 := by rw [hs47eq]; exact hsk22.2.2.1
  have hs47DI : s47.mem.get 2321 = 1 := by
    rw [hs47eq, hsk22.2.2.2.1, hs22DI]
    exact (rfl : (0 : Word) + 1 = 1)
  have hpres47 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s47.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs47eq]
    exact (hsk22.2.2.2.2 a ha18 haDI ha0).trans (hpres22 a ha18 ha31 haSK haDI ha0)
  have hONE47 : s47.mem.get 3 = 1 := (hpres47 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK547 : s47.mem.get 2322 = 5 := (hpres47 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs47SK : s47.mem.get 2320 = 3 := by
    rw [hs47eq]; exact (hsk22.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs22SK
  have hI47 : s47.mem.get 29 = 0 := (hpres47 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR47 : s47.mem.get 28 = s.mem.get 28 := hpres47 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2347 : s47.mem.get 23 = s.mem.get 23 := hpres47 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2447 : s47.mem.get 24 = s.mem.get 24 := hpres47 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g47 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s47.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres47 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_47 : (s47.mem.get 2321).toNat < 5 := by rw [hs47DI]; simp
  have hDIltSK_47 : (s47.mem.get 2321).toNat < (s47.mem.get 2320).toNat := by
    rw [hs47DI, hs47SK]; simp
  have hSKhi_47 : (s47.mem.get 2320).toNat < 32768 := by rw [hs47SK]; simp
  have hsk47 := skip_next (s := s47) hs47pc hs47h hs47Z hONE47 hK547
    hDIlt5_47 hDIltSK_47 hSKhi_47 g47
  have hrun72 : runN s 72 = runN s47 25 := runN_add_eq s 47 25 72 (by decide)
  let s72 := runN s 72
  have hs72eq : s72 = runN s47 25 := hrun72
  have hs72pc : s72.pc = 1641 := by rw [hs72eq]; exact hsk47.1
  have hs72h : s72.halted = false := by rw [hs72eq]; exact hsk47.2.1
  have hs72Z : s72.mem.get 0 = 0 := by rw [hs72eq]; exact hsk47.2.2.1
  have hs72DI : s72.mem.get 2321 = 2 := by
    rw [hs72eq, hsk47.2.2.2.1, hs47DI]
    exact (rfl : (1 : Word) + 1 = 2)
  have hpres72 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s72.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs72eq]
    exact (hsk47.2.2.2.2 a ha18 haDI ha0).trans (hpres47 a ha18 ha31 haSK haDI ha0)
  have hONE72 : s72.mem.get 3 = 1 := (hpres72 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK572 : s72.mem.get 2322 = 5 := (hpres72 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs72SK : s72.mem.get 2320 = 3 := by
    rw [hs72eq]; exact (hsk47.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs47SK
  have hI72 : s72.mem.get 29 = 0 := (hpres72 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR72 : s72.mem.get 28 = s.mem.get 28 := hpres72 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2372 : s72.mem.get 23 = s.mem.get 23 := hpres72 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2472 : s72.mem.get 24 = s.mem.get 24 := hpres72 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g72 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s72.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres72 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_72 : (s72.mem.get 2321).toNat < 5 := by rw [hs72DI]; simp
  have hDIltSK_72 : (s72.mem.get 2321).toNat < (s72.mem.get 2320).toNat := by
    rw [hs72DI, hs72SK]; simp
  have hSKhi_72 : (s72.mem.get 2320).toNat < 32768 := by rw [hs72SK]; simp
  have hsk72 := skip_next (s := s72) hs72pc hs72h hs72Z hONE72 hK572
    hDIlt5_72 hDIltSK_72 hSKhi_72 g72
  have hrun97 : runN s 97 = runN s72 25 := runN_add_eq s 72 25 97 (by decide)
  let s97 := runN s 97
  have hs97eq : s97 = runN s72 25 := hrun97
  have hs97pc : s97.pc = 1641 := by rw [hs97eq]; exact hsk72.1
  have hs97h : s97.halted = false := by rw [hs97eq]; exact hsk72.2.1
  have hs97Z : s97.mem.get 0 = 0 := by rw [hs97eq]; exact hsk72.2.2.1
  have hs97DI : s97.mem.get 2321 = 3 := by
    rw [hs97eq, hsk72.2.2.2.1, hs72DI]
    exact (rfl : (2 : Word) + 1 = 3)
  have hpres97 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s97.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs97eq]
    exact (hsk72.2.2.2.2 a ha18 haDI ha0).trans (hpres72 a ha18 ha31 haSK haDI ha0)
  have hONE97 : s97.mem.get 3 = 1 := (hpres97 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK597 : s97.mem.get 2322 = 5 := (hpres97 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs97SK : s97.mem.get 2320 = 3 := by
    rw [hs97eq]; exact (hsk72.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs72SK
  have hI97 : s97.mem.get 29 = 0 := (hpres97 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR97 : s97.mem.get 28 = s.mem.get 28 := hpres97 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2397 : s97.mem.get 23 = s.mem.get 23 := hpres97 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2497 : s97.mem.get 24 = s.mem.get 24 := hpres97 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g97 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s97.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres97 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have g97S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s97.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres97 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo97 : 0 < (s97.mem.get 28).toNat := by
    rw [hR97]
    have : 0 ≤ 1 := by decide
    omega
  have hRhi97 : (s97.mem.get 28).toNat < 32768 := by rw [hR97]; exact hRhi
  have ht97 := loop_take_eq_di3_idx0 (s := s97) hs97pc hs97h hs97Z hONE97 hK597 hs97DI hs97SK hI97 hRlo97 hRhi97 g97S g97
  have hrun182 : runN s 182 = runN s97 85 := runN_add_eq s 97 85 182 (by decide)
  let s182 := runN s 182
  have hs182eq : s182 = runN s97 85 := hrun182
  have hs182pc : s182.pc = 1641 := by rw [hs182eq]; exact ht97.1
  have hs182h : s182.halted = false := by rw [hs182eq]; exact ht97.2.1
  have hs182Z : s182.mem.get 0 = 0 := by rw [hs182eq]; exact ht97.2.2.1
  have hs182B32 : s182.mem.get 32 = s.mem.get 23 := by
    rw [hs182eq, ht97.2.2.2.1, hQ2397]
  have hI182 : s182.mem.get 29 = 1 := by rw [hs182eq]; exact ht97.2.2.2.2.1
  have hs182DI : s182.mem.get 2321 = 4 := by rw [hs182eq]; exact ht97.2.2.2.2.2.1
  have hpres182 : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s182.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs182eq]
    exact (ht97.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres97 a ha18 ha31 haSK haDI ha0)
  have hONE182 : s182.mem.get 3 = 1 := (hpres182 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5182 : s182.mem.get 2322 = 5 := (hpres182 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs182SK : s182.mem.get 2320 = 3 := by
    rw [hs182eq]
    exact (ht97.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs97SK
  have hR182 : s182.mem.get 28 = s.mem.get 28 := hpres182 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24182 : s182.mem.get 24 = s.mem.get 24 := hpres182 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g182 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s182.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres182 (UInt16.ofNat k) n32 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo182 : (s182.mem.get 2320).toNat < 4 := by rw [hs182SK]; simp
  have g182S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s182.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres182 (UInt16.ofNat k) n32 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo182 : 1 < (s182.mem.get 28).toNat := by
    rw [hR182]
    have : 1 ≤ 1 := by decide
    omega
  have hRhi182 : (s182.mem.get 28).toNat < 32768 := by rw [hR182]; exact hRhi
  have ht182 := loop_take_gt_di4_idx1 (s := s182) hs182pc hs182h hs182Z hONE182 hK5182 hs182DI hSKlo182 hI182 hRlo182 hRhi182 g182S g182
  have hrun265 : runN s 265 = runN s182 83 := runN_add_eq s 182 83 265 (by decide)
  let s265 := runN s 265
  have hs265eq : s265 = runN s182 83 := hrun265
  have hs265pc : s265.pc = 1641 := by rw [hs265eq]; exact ht182.1
  have hs265h : s265.halted = false := by rw [hs265eq]; exact ht182.2.1
  have hs265Z : s265.mem.get 0 = 0 := by rw [hs265eq]; exact ht182.2.2.1
  have hs265B33 : s265.mem.get 33 = s.mem.get 24 := by
    rw [hs265eq, ht182.2.2.2.1, hQ24182]
  have hI265 : s265.mem.get 29 = 2 := by rw [hs265eq]; exact ht182.2.2.2.2.1
  have hs265DI : s265.mem.get 2321 = 5 := by rw [hs265eq]; exact ht182.2.2.2.2.2.1
  have hpres265 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s265.mem.get a = s.mem.get a := by
    intro a haB32 haB33 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs265eq]
    exact (ht182.2.2.2.2.2.2 a haB33 ha29 ha18 ha30 haR haDI ha0).trans (hpres182 a haB32 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs265B32 : s265.mem.get 32 = s.mem.get 23 := by
    rw [hs265eq]
    exact (ht182.2.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs182B32
  have hONE265 : s265.mem.get 3 = 1 := (hpres265 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5265 : s265.mem.get 2322 = 5 := (hpres265 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs265SK : s265.mem.get 2320 = 3 := by
    rw [hs265eq]
    exact (ht182.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs182SK
  have hR265 : s265.mem.get 28 = s.mem.get 28 := hpres265 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g265 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s265.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres265 (UInt16.ofNat k) n32 n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hONE265 : s265.mem.get 3 = 1 := (hpres265 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5265x : s265.mem.get 2322 = 5 := (hpres265 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have g265x : ∀ k : Nat, 1641 ≤ k → k < 1677 →
      s265.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres265 (UInt16.ofNat k) n32 n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hx := dig_loop_exit (s := s265) hs265pc hs265h hs265Z hONE265 hs265DI hK5265x g265x
  have hrun : s276 = runN s265 11 := runN_add_eq s 265 11 276 (by decide)
  have hsTpc : s276.pc = 1905 := by rw [hrun]; exact hx.1
  have hsTh : s276.halted = false := by rw [hrun]; exact hx.2.1
  have hsTZ : s276.mem.get 0 = 0 := by rw [hrun]; exact hx.2.2.1
  have hsTB32 : s276.mem.get 32 = s.mem.get 23 := by
    rw [hrun]; exact (hx.2.2.2.2 32 (by decide) (by decide)).trans hs265B32
  have hsTB33 : s276.mem.get 33 = s.mem.get 24 := by
    rw [hrun]; exact (hx.2.2.2.2 33 (by decide) (by decide)).trans hs265B33
  have hsTI : s276.mem.get 29 = 2 := by
    rw [hrun]; exact (hx.2.2.2.2 29 (by decide) (by decide)).trans hI265
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s276.mem.get a = s.mem.get a := by
    intro a haB32 haB33 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hrun]
    exact (hx.2.2.2.2 a ha18 ha0).trans (hpres265 a haB32 haB33 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB32, hsTB33, hsTI, hpres⟩


/-- From `EMIT_DIGS` with `NDIG = 2` and `IDX = 1 < ROOM`: write
`Q3`..`Q4` at `BUF+1`..`BUF+2` and reach `AFTER_DIGS`
with `IDX = 3`. 280 steps. -/
theorem emit_ndig2_idx1 {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 2)
    (hI : s.mem.get 29 = 1)
    (hRlo : 2 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s280 := runN s 280
    s280.pc = 1905 ∧
    s280.halted = false ∧
    s280.mem.get 0 = 0 ∧
    s280.mem.get 33 = s.mem.get 23 ∧
    s280.mem.get 34 = s.mem.get 24 ∧
    s280.mem.get 29 = 3 ∧
    (∀ a, a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s280.mem.get a = s.mem.get a) := by
  intro s280
  have hNle : (s.mem.get 25).toNat ≤ 5 := by rw [hN]; simp
  have hp := emit_prelude (s := s) hpc hh hZ hONE hNle
    (fun k h1 h2 => hcode k (by omega) (by omega))
  let s22 := runN s 22
  have hs22pc : s22.pc = 1641 := hp.1
  have hs22h : s22.halted = false := hp.2.1
  have hs22Z : s22.mem.get 0 = 0 := hp.2.2.1
  have hs22SK : s22.mem.get 2320 = 3 := by
    rw [hp.2.2.2.1, hN]
    exact (rfl : (5 : Word) - 2 = 3)
  have hs22DI : s22.mem.get 2321 = 0 := hp.2.2.2.2.1
  have hpres22raw := hp.2.2.2.2.2.2
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s22.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    exact hpres22raw a ha31 haSK haDI ha0
  have hONE22 : s22.mem.get 3 = 1 := (hpres22 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK522 : s22.mem.get 2322 = 5 := (hpres22 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hI22 : s22.mem.get 29 = 1 := (hpres22 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR22 : s22.mem.get 28 = s.mem.get 28 := hpres22 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2322 : s22.mem.get 23 = s.mem.get 23 := hpres22 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2422 : s22.mem.get 24 = s.mem.get 24 := hpres22 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g22 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s22.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres22 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_22 : (s22.mem.get 2321).toNat < 5 := by rw [hs22DI]; simp
  have hDIltSK_22 : (s22.mem.get 2321).toNat < (s22.mem.get 2320).toNat := by
    rw [hs22DI, hs22SK]; simp
  have hSKhi_22 : (s22.mem.get 2320).toNat < 32768 := by rw [hs22SK]; simp
  have hsk22 := skip_next (s := s22) hs22pc hs22h hs22Z hONE22 hK522
    hDIlt5_22 hDIltSK_22 hSKhi_22 g22
  have hrun47 : runN s 47 = runN s22 25 := runN_add_eq s 22 25 47 (by decide)
  let s47 := runN s 47
  have hs47eq : s47 = runN s22 25 := hrun47
  have hs47pc : s47.pc = 1641 := by rw [hs47eq]; exact hsk22.1
  have hs47h : s47.halted = false := by rw [hs47eq]; exact hsk22.2.1
  have hs47Z : s47.mem.get 0 = 0 := by rw [hs47eq]; exact hsk22.2.2.1
  have hs47DI : s47.mem.get 2321 = 1 := by
    rw [hs47eq, hsk22.2.2.2.1, hs22DI]
    exact (rfl : (0 : Word) + 1 = 1)
  have hpres47 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s47.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs47eq]
    exact (hsk22.2.2.2.2 a ha18 haDI ha0).trans (hpres22 a ha18 ha31 haSK haDI ha0)
  have hONE47 : s47.mem.get 3 = 1 := (hpres47 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK547 : s47.mem.get 2322 = 5 := (hpres47 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs47SK : s47.mem.get 2320 = 3 := by
    rw [hs47eq]; exact (hsk22.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs22SK
  have hI47 : s47.mem.get 29 = 1 := (hpres47 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR47 : s47.mem.get 28 = s.mem.get 28 := hpres47 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2347 : s47.mem.get 23 = s.mem.get 23 := hpres47 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2447 : s47.mem.get 24 = s.mem.get 24 := hpres47 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g47 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s47.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres47 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_47 : (s47.mem.get 2321).toNat < 5 := by rw [hs47DI]; simp
  have hDIltSK_47 : (s47.mem.get 2321).toNat < (s47.mem.get 2320).toNat := by
    rw [hs47DI, hs47SK]; simp
  have hSKhi_47 : (s47.mem.get 2320).toNat < 32768 := by rw [hs47SK]; simp
  have hsk47 := skip_next (s := s47) hs47pc hs47h hs47Z hONE47 hK547
    hDIlt5_47 hDIltSK_47 hSKhi_47 g47
  have hrun72 : runN s 72 = runN s47 25 := runN_add_eq s 47 25 72 (by decide)
  let s72 := runN s 72
  have hs72eq : s72 = runN s47 25 := hrun72
  have hs72pc : s72.pc = 1641 := by rw [hs72eq]; exact hsk47.1
  have hs72h : s72.halted = false := by rw [hs72eq]; exact hsk47.2.1
  have hs72Z : s72.mem.get 0 = 0 := by rw [hs72eq]; exact hsk47.2.2.1
  have hs72DI : s72.mem.get 2321 = 2 := by
    rw [hs72eq, hsk47.2.2.2.1, hs47DI]
    exact (rfl : (1 : Word) + 1 = 2)
  have hpres72 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s72.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs72eq]
    exact (hsk47.2.2.2.2 a ha18 haDI ha0).trans (hpres47 a ha18 ha31 haSK haDI ha0)
  have hONE72 : s72.mem.get 3 = 1 := (hpres72 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK572 : s72.mem.get 2322 = 5 := (hpres72 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs72SK : s72.mem.get 2320 = 3 := by
    rw [hs72eq]; exact (hsk47.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs47SK
  have hI72 : s72.mem.get 29 = 1 := (hpres72 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR72 : s72.mem.get 28 = s.mem.get 28 := hpres72 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2372 : s72.mem.get 23 = s.mem.get 23 := hpres72 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2472 : s72.mem.get 24 = s.mem.get 24 := hpres72 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g72 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s72.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres72 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_72 : (s72.mem.get 2321).toNat < 5 := by rw [hs72DI]; simp
  have hDIltSK_72 : (s72.mem.get 2321).toNat < (s72.mem.get 2320).toNat := by
    rw [hs72DI, hs72SK]; simp
  have hSKhi_72 : (s72.mem.get 2320).toNat < 32768 := by rw [hs72SK]; simp
  have hsk72 := skip_next (s := s72) hs72pc hs72h hs72Z hONE72 hK572
    hDIlt5_72 hDIltSK_72 hSKhi_72 g72
  have hrun97 : runN s 97 = runN s72 25 := runN_add_eq s 72 25 97 (by decide)
  let s97 := runN s 97
  have hs97eq : s97 = runN s72 25 := hrun97
  have hs97pc : s97.pc = 1641 := by rw [hs97eq]; exact hsk72.1
  have hs97h : s97.halted = false := by rw [hs97eq]; exact hsk72.2.1
  have hs97Z : s97.mem.get 0 = 0 := by rw [hs97eq]; exact hsk72.2.2.1
  have hs97DI : s97.mem.get 2321 = 3 := by
    rw [hs97eq, hsk72.2.2.2.1, hs72DI]
    exact (rfl : (2 : Word) + 1 = 3)
  have hpres97 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s97.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs97eq]
    exact (hsk72.2.2.2.2 a ha18 haDI ha0).trans (hpres72 a ha18 ha31 haSK haDI ha0)
  have hONE97 : s97.mem.get 3 = 1 := (hpres97 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK597 : s97.mem.get 2322 = 5 := (hpres97 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs97SK : s97.mem.get 2320 = 3 := by
    rw [hs97eq]; exact (hsk72.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs72SK
  have hI97 : s97.mem.get 29 = 1 := (hpres97 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR97 : s97.mem.get 28 = s.mem.get 28 := hpres97 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2397 : s97.mem.get 23 = s.mem.get 23 := hpres97 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2497 : s97.mem.get 24 = s.mem.get 24 := hpres97 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g97 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s97.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres97 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have g97S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s97.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres97 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo97 : 1 < (s97.mem.get 28).toNat := by
    rw [hR97]
    have : 1 ≤ 2 := by decide
    omega
  have hRhi97 : (s97.mem.get 28).toNat < 32768 := by rw [hR97]; exact hRhi
  have ht97 := loop_take_eq_di3_idx1 (s := s97) hs97pc hs97h hs97Z hONE97 hK597 hs97DI hs97SK hI97 hRlo97 hRhi97 g97S g97
  have hrun184 : runN s 184 = runN s97 87 := runN_add_eq s 97 87 184 (by decide)
  let s184 := runN s 184
  have hs184eq : s184 = runN s97 87 := hrun184
  have hs184pc : s184.pc = 1641 := by rw [hs184eq]; exact ht97.1
  have hs184h : s184.halted = false := by rw [hs184eq]; exact ht97.2.1
  have hs184Z : s184.mem.get 0 = 0 := by rw [hs184eq]; exact ht97.2.2.1
  have hs184B33 : s184.mem.get 33 = s.mem.get 23 := by
    rw [hs184eq, ht97.2.2.2.1, hQ2397]
  have hI184 : s184.mem.get 29 = 2 := by rw [hs184eq]; exact ht97.2.2.2.2.1
  have hs184DI : s184.mem.get 2321 = 4 := by rw [hs184eq]; exact ht97.2.2.2.2.2.1
  have hpres184 : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s184.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs184eq]
    exact (ht97.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres97 a ha18 ha31 haSK haDI ha0)
  have hONE184 : s184.mem.get 3 = 1 := (hpres184 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5184 : s184.mem.get 2322 = 5 := (hpres184 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs184SK : s184.mem.get 2320 = 3 := by
    rw [hs184eq]
    exact (ht97.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs97SK
  have hR184 : s184.mem.get 28 = s.mem.get 28 := hpres184 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24184 : s184.mem.get 24 = s.mem.get 24 := hpres184 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g184 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s184.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
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
    exact (hpres184 (UInt16.ofNat k) n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo184 : (s184.mem.get 2320).toNat < 4 := by rw [hs184SK]; simp
  have g184S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s184.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
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
    exact (hpres184 (UInt16.ofNat k) n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo184 : 2 < (s184.mem.get 28).toNat := by
    rw [hR184]
    have : 2 ≤ 2 := by decide
    omega
  have hRhi184 : (s184.mem.get 28).toNat < 32768 := by rw [hR184]; exact hRhi
  have ht184 := loop_take_gt_di4_idx2 (s := s184) hs184pc hs184h hs184Z hONE184 hK5184 hs184DI hSKlo184 hI184 hRlo184 hRhi184 g184S g184
  have hrun269 : runN s 269 = runN s184 85 := runN_add_eq s 184 85 269 (by decide)
  let s269 := runN s 269
  have hs269eq : s269 = runN s184 85 := hrun269
  have hs269pc : s269.pc = 1641 := by rw [hs269eq]; exact ht184.1
  have hs269h : s269.halted = false := by rw [hs269eq]; exact ht184.2.1
  have hs269Z : s269.mem.get 0 = 0 := by rw [hs269eq]; exact ht184.2.2.1
  have hs269B34 : s269.mem.get 34 = s.mem.get 24 := by
    rw [hs269eq, ht184.2.2.2.1, hQ24184]
  have hI269 : s269.mem.get 29 = 3 := by rw [hs269eq]; exact ht184.2.2.2.2.1
  have hs269DI : s269.mem.get 2321 = 5 := by rw [hs269eq]; exact ht184.2.2.2.2.2.1
  have hpres269 : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s269.mem.get a = s.mem.get a := by
    intro a haB33 haB34 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs269eq]
    exact (ht184.2.2.2.2.2.2 a haB34 ha29 ha18 ha30 haR haDI ha0).trans (hpres184 a haB33 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs269B33 : s269.mem.get 33 = s.mem.get 23 := by
    rw [hs269eq]
    exact (ht184.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs184B33
  have hONE269 : s269.mem.get 3 = 1 := (hpres269 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5269 : s269.mem.get 2322 = 5 := (hpres269 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs269SK : s269.mem.get 2320 = 3 := by
    rw [hs269eq]
    exact (ht184.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs184SK
  have hR269 : s269.mem.get 28 = s.mem.get 28 := hpres269 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g269 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s269.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
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
    exact (hpres269 (UInt16.ofNat k) n33 n34 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hONE269 : s269.mem.get 3 = 1 := (hpres269 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5269x : s269.mem.get 2322 = 5 := (hpres269 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have g269x : ∀ k : Nat, 1641 ≤ k → k < 1677 →
      s269.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
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
    exact (hpres269 (UInt16.ofNat k) n33 n34 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hx := dig_loop_exit (s := s269) hs269pc hs269h hs269Z hONE269 hs269DI hK5269x g269x
  have hrun : s280 = runN s269 11 := runN_add_eq s 269 11 280 (by decide)
  have hsTpc : s280.pc = 1905 := by rw [hrun]; exact hx.1
  have hsTh : s280.halted = false := by rw [hrun]; exact hx.2.1
  have hsTZ : s280.mem.get 0 = 0 := by rw [hrun]; exact hx.2.2.1
  have hsTB33 : s280.mem.get 33 = s.mem.get 23 := by
    rw [hrun]; exact (hx.2.2.2.2 33 (by decide) (by decide)).trans hs269B33
  have hsTB34 : s280.mem.get 34 = s.mem.get 24 := by
    rw [hrun]; exact (hx.2.2.2.2 34 (by decide) (by decide)).trans hs269B34
  have hsTI : s280.mem.get 29 = 3 := by
    rw [hrun]; exact (hx.2.2.2.2 29 (by decide) (by decide)).trans hI269
  have hpres : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s280.mem.get a = s.mem.get a := by
    intro a haB33 haB34 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hrun]
    exact (hx.2.2.2.2 a ha18 ha0).trans (hpres269 a haB33 haB34 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB33, hsTB34, hsTI, hpres⟩


/-- From `EMIT_DIGS` with `NDIG = 3` and `IDX = 0 < ROOM`: write
`Q2`..`Q4` at `BUF+0`..`BUF+2` and reach `AFTER_DIGS`
with `IDX = 3`. 334 steps. -/
theorem emit_ndig3_idx0 {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 3)
    (hI : s.mem.get 29 = 0)
    (hRlo : 2 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s334 := runN s 334
    s334.pc = 1905 ∧
    s334.halted = false ∧
    s334.mem.get 0 = 0 ∧
    s334.mem.get 32 = s.mem.get 22 ∧
    s334.mem.get 33 = s.mem.get 23 ∧
    s334.mem.get 34 = s.mem.get 24 ∧
    s334.mem.get 29 = 3 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s334.mem.get a = s.mem.get a) := by
  intro s334
  have hNle : (s.mem.get 25).toNat ≤ 5 := by rw [hN]; simp
  have hp := emit_prelude (s := s) hpc hh hZ hONE hNle
    (fun k h1 h2 => hcode k (by omega) (by omega))
  let s22 := runN s 22
  have hs22pc : s22.pc = 1641 := hp.1
  have hs22h : s22.halted = false := hp.2.1
  have hs22Z : s22.mem.get 0 = 0 := hp.2.2.1
  have hs22SK : s22.mem.get 2320 = 2 := by
    rw [hp.2.2.2.1, hN]
    exact (rfl : (5 : Word) - 3 = 2)
  have hs22DI : s22.mem.get 2321 = 0 := hp.2.2.2.2.1
  have hpres22raw := hp.2.2.2.2.2.2
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s22.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    exact hpres22raw a ha31 haSK haDI ha0
  have hONE22 : s22.mem.get 3 = 1 := (hpres22 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK522 : s22.mem.get 2322 = 5 := (hpres22 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hI22 : s22.mem.get 29 = 0 := (hpres22 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR22 : s22.mem.get 28 = s.mem.get 28 := hpres22 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2222 : s22.mem.get 22 = s.mem.get 22 := hpres22 22 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2322 : s22.mem.get 23 = s.mem.get 23 := hpres22 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2422 : s22.mem.get 24 = s.mem.get 24 := hpres22 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g22 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s22.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres22 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_22 : (s22.mem.get 2321).toNat < 5 := by rw [hs22DI]; simp
  have hDIltSK_22 : (s22.mem.get 2321).toNat < (s22.mem.get 2320).toNat := by
    rw [hs22DI, hs22SK]; simp
  have hSKhi_22 : (s22.mem.get 2320).toNat < 32768 := by rw [hs22SK]; simp
  have hsk22 := skip_next (s := s22) hs22pc hs22h hs22Z hONE22 hK522
    hDIlt5_22 hDIltSK_22 hSKhi_22 g22
  have hrun47 : runN s 47 = runN s22 25 := runN_add_eq s 22 25 47 (by decide)
  let s47 := runN s 47
  have hs47eq : s47 = runN s22 25 := hrun47
  have hs47pc : s47.pc = 1641 := by rw [hs47eq]; exact hsk22.1
  have hs47h : s47.halted = false := by rw [hs47eq]; exact hsk22.2.1
  have hs47Z : s47.mem.get 0 = 0 := by rw [hs47eq]; exact hsk22.2.2.1
  have hs47DI : s47.mem.get 2321 = 1 := by
    rw [hs47eq, hsk22.2.2.2.1, hs22DI]
    exact (rfl : (0 : Word) + 1 = 1)
  have hpres47 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s47.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs47eq]
    exact (hsk22.2.2.2.2 a ha18 haDI ha0).trans (hpres22 a ha18 ha31 haSK haDI ha0)
  have hONE47 : s47.mem.get 3 = 1 := (hpres47 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK547 : s47.mem.get 2322 = 5 := (hpres47 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs47SK : s47.mem.get 2320 = 2 := by
    rw [hs47eq]; exact (hsk22.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs22SK
  have hI47 : s47.mem.get 29 = 0 := (hpres47 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR47 : s47.mem.get 28 = s.mem.get 28 := hpres47 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2247 : s47.mem.get 22 = s.mem.get 22 := hpres47 22 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2347 : s47.mem.get 23 = s.mem.get 23 := hpres47 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2447 : s47.mem.get 24 = s.mem.get 24 := hpres47 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g47 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s47.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres47 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_47 : (s47.mem.get 2321).toNat < 5 := by rw [hs47DI]; simp
  have hDIltSK_47 : (s47.mem.get 2321).toNat < (s47.mem.get 2320).toNat := by
    rw [hs47DI, hs47SK]; simp
  have hSKhi_47 : (s47.mem.get 2320).toNat < 32768 := by rw [hs47SK]; simp
  have hsk47 := skip_next (s := s47) hs47pc hs47h hs47Z hONE47 hK547
    hDIlt5_47 hDIltSK_47 hSKhi_47 g47
  have hrun72 : runN s 72 = runN s47 25 := runN_add_eq s 47 25 72 (by decide)
  let s72 := runN s 72
  have hs72eq : s72 = runN s47 25 := hrun72
  have hs72pc : s72.pc = 1641 := by rw [hs72eq]; exact hsk47.1
  have hs72h : s72.halted = false := by rw [hs72eq]; exact hsk47.2.1
  have hs72Z : s72.mem.get 0 = 0 := by rw [hs72eq]; exact hsk47.2.2.1
  have hs72DI : s72.mem.get 2321 = 2 := by
    rw [hs72eq, hsk47.2.2.2.1, hs47DI]
    exact (rfl : (1 : Word) + 1 = 2)
  have hpres72 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s72.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs72eq]
    exact (hsk47.2.2.2.2 a ha18 haDI ha0).trans (hpres47 a ha18 ha31 haSK haDI ha0)
  have hONE72 : s72.mem.get 3 = 1 := (hpres72 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK572 : s72.mem.get 2322 = 5 := (hpres72 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs72SK : s72.mem.get 2320 = 2 := by
    rw [hs72eq]; exact (hsk47.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs47SK
  have hI72 : s72.mem.get 29 = 0 := (hpres72 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR72 : s72.mem.get 28 = s.mem.get 28 := hpres72 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2272 : s72.mem.get 22 = s.mem.get 22 := hpres72 22 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2372 : s72.mem.get 23 = s.mem.get 23 := hpres72 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2472 : s72.mem.get 24 = s.mem.get 24 := hpres72 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g72 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s72.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres72 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have g72S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s72.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres72 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo72 : 0 < (s72.mem.get 28).toNat := by
    rw [hR72]
    have : 0 ≤ 2 := by decide
    omega
  have hRhi72 : (s72.mem.get 28).toNat < 32768 := by rw [hR72]; exact hRhi
  have ht72 := loop_take_eq_di2_idx0 (s := s72) hs72pc hs72h hs72Z hONE72 hK572 hs72DI hs72SK hI72 hRlo72 hRhi72 g72S g72
  have hrun155 : runN s 155 = runN s72 83 := runN_add_eq s 72 83 155 (by decide)
  let s155 := runN s 155
  have hs155eq : s155 = runN s72 83 := hrun155
  have hs155pc : s155.pc = 1641 := by rw [hs155eq]; exact ht72.1
  have hs155h : s155.halted = false := by rw [hs155eq]; exact ht72.2.1
  have hs155Z : s155.mem.get 0 = 0 := by rw [hs155eq]; exact ht72.2.2.1
  have hs155B32 : s155.mem.get 32 = s.mem.get 22 := by
    rw [hs155eq, ht72.2.2.2.1, hQ2272]
  have hI155 : s155.mem.get 29 = 1 := by rw [hs155eq]; exact ht72.2.2.2.2.1
  have hs155DI : s155.mem.get 2321 = 3 := by rw [hs155eq]; exact ht72.2.2.2.2.2.1
  have hpres155 : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s155.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs155eq]
    exact (ht72.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres72 a ha18 ha31 haSK haDI ha0)
  have hONE155 : s155.mem.get 3 = 1 := (hpres155 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5155 : s155.mem.get 2322 = 5 := (hpres155 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs155SK : s155.mem.get 2320 = 2 := by
    rw [hs155eq]
    exact (ht72.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs72SK
  have hR155 : s155.mem.get 28 = s.mem.get 28 := hpres155 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ23155 : s155.mem.get 23 = s.mem.get 23 := hpres155 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24155 : s155.mem.get 24 = s.mem.get 24 := hpres155 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g155 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s155.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres155 (UInt16.ofNat k) n32 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo155 : (s155.mem.get 2320).toNat < 3 := by rw [hs155SK]; simp
  have g155S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s155.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres155 (UInt16.ofNat k) n32 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo155 : 1 < (s155.mem.get 28).toNat := by
    rw [hR155]
    have : 1 ≤ 2 := by decide
    omega
  have hRhi155 : (s155.mem.get 28).toNat < 32768 := by rw [hR155]; exact hRhi
  have ht155 := loop_take_gt_di3_idx1 (s := s155) hs155pc hs155h hs155Z hONE155 hK5155 hs155DI hSKlo155 hI155 hRlo155 hRhi155 g155S g155
  have hrun238 : runN s 238 = runN s155 83 := runN_add_eq s 155 83 238 (by decide)
  let s238 := runN s 238
  have hs238eq : s238 = runN s155 83 := hrun238
  have hs238pc : s238.pc = 1641 := by rw [hs238eq]; exact ht155.1
  have hs238h : s238.halted = false := by rw [hs238eq]; exact ht155.2.1
  have hs238Z : s238.mem.get 0 = 0 := by rw [hs238eq]; exact ht155.2.2.1
  have hs238B33 : s238.mem.get 33 = s.mem.get 23 := by
    rw [hs238eq, ht155.2.2.2.1, hQ23155]
  have hI238 : s238.mem.get 29 = 2 := by rw [hs238eq]; exact ht155.2.2.2.2.1
  have hs238DI : s238.mem.get 2321 = 4 := by rw [hs238eq]; exact ht155.2.2.2.2.2.1
  have hpres238 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s238.mem.get a = s.mem.get a := by
    intro a haB32 haB33 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs238eq]
    exact (ht155.2.2.2.2.2.2 a haB33 ha29 ha18 ha30 haR haDI ha0).trans (hpres155 a haB32 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs238B32 : s238.mem.get 32 = s.mem.get 22 := by
    rw [hs238eq]
    exact (ht155.2.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs155B32
  have hONE238 : s238.mem.get 3 = 1 := (hpres238 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5238 : s238.mem.get 2322 = 5 := (hpres238 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs238SK : s238.mem.get 2320 = 2 := by
    rw [hs238eq]
    exact (ht155.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs155SK
  have hR238 : s238.mem.get 28 = s.mem.get 28 := hpres238 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24238 : s238.mem.get 24 = s.mem.get 24 := hpres238 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g238 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s238.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres238 (UInt16.ofNat k) n32 n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo238 : (s238.mem.get 2320).toNat < 4 := by rw [hs238SK]; simp
  have g238S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s238.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres238 (UInt16.ofNat k) n32 n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo238 : 2 < (s238.mem.get 28).toNat := by
    rw [hR238]
    have : 2 ≤ 2 := by decide
    omega
  have hRhi238 : (s238.mem.get 28).toNat < 32768 := by rw [hR238]; exact hRhi
  have ht238 := loop_take_gt_di4_idx2 (s := s238) hs238pc hs238h hs238Z hONE238 hK5238 hs238DI hSKlo238 hI238 hRlo238 hRhi238 g238S g238
  have hrun323 : runN s 323 = runN s238 85 := runN_add_eq s 238 85 323 (by decide)
  let s323 := runN s 323
  have hs323eq : s323 = runN s238 85 := hrun323
  have hs323pc : s323.pc = 1641 := by rw [hs323eq]; exact ht238.1
  have hs323h : s323.halted = false := by rw [hs323eq]; exact ht238.2.1
  have hs323Z : s323.mem.get 0 = 0 := by rw [hs323eq]; exact ht238.2.2.1
  have hs323B34 : s323.mem.get 34 = s.mem.get 24 := by
    rw [hs323eq, ht238.2.2.2.1, hQ24238]
  have hI323 : s323.mem.get 29 = 3 := by rw [hs323eq]; exact ht238.2.2.2.2.1
  have hs323DI : s323.mem.get 2321 = 5 := by rw [hs323eq]; exact ht238.2.2.2.2.2.1
  have hpres323 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s323.mem.get a = s.mem.get a := by
    intro a haB32 haB33 haB34 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs323eq]
    exact (ht238.2.2.2.2.2.2 a haB34 ha29 ha18 ha30 haR haDI ha0).trans (hpres238 a haB32 haB33 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs323B32 : s323.mem.get 32 = s.mem.get 22 := by
    rw [hs323eq]
    exact (ht238.2.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs238B32
  have hs323B33 : s323.mem.get 33 = s.mem.get 23 := by
    rw [hs323eq]
    exact (ht238.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs238B33
  have hONE323 : s323.mem.get 3 = 1 := (hpres323 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5323 : s323.mem.get 2322 = 5 := (hpres323 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs323SK : s323.mem.get 2320 = 2 := by
    rw [hs323eq]
    exact (ht238.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs238SK
  have hR323 : s323.mem.get 28 = s.mem.get 28 := hpres323 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g323 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s323.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres323 (UInt16.ofNat k) n32 n33 n34 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hONE323 : s323.mem.get 3 = 1 := (hpres323 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5323x : s323.mem.get 2322 = 5 := (hpres323 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have g323x : ∀ k : Nat, 1641 ≤ k → k < 1677 →
      s323.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres323 (UInt16.ofNat k) n32 n33 n34 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hx := dig_loop_exit (s := s323) hs323pc hs323h hs323Z hONE323 hs323DI hK5323x g323x
  have hrun : s334 = runN s323 11 := runN_add_eq s 323 11 334 (by decide)
  have hsTpc : s334.pc = 1905 := by rw [hrun]; exact hx.1
  have hsTh : s334.halted = false := by rw [hrun]; exact hx.2.1
  have hsTZ : s334.mem.get 0 = 0 := by rw [hrun]; exact hx.2.2.1
  have hsTB32 : s334.mem.get 32 = s.mem.get 22 := by
    rw [hrun]; exact (hx.2.2.2.2 32 (by decide) (by decide)).trans hs323B32
  have hsTB33 : s334.mem.get 33 = s.mem.get 23 := by
    rw [hrun]; exact (hx.2.2.2.2 33 (by decide) (by decide)).trans hs323B33
  have hsTB34 : s334.mem.get 34 = s.mem.get 24 := by
    rw [hrun]; exact (hx.2.2.2.2 34 (by decide) (by decide)).trans hs323B34
  have hsTI : s334.mem.get 29 = 3 := by
    rw [hrun]; exact (hx.2.2.2.2 29 (by decide) (by decide)).trans hI323
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s334.mem.get a = s.mem.get a := by
    intro a haB32 haB33 haB34 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hrun]
    exact (hx.2.2.2.2 a ha18 ha0).trans (hpres323 a haB32 haB33 haB34 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB32, hsTB33, hsTB34, hsTI, hpres⟩


/-- From `EMIT_DIGS` with `NDIG = 3` and `IDX = 1 < ROOM`: write
`Q2`..`Q4` at `BUF+1`..`BUF+3` and reach `AFTER_DIGS`
with `IDX = 4`. 340 steps. -/
theorem emit_ndig3_idx1 {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 3)
    (hI : s.mem.get 29 = 1)
    (hRlo : 3 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s340 := runN s 340
    s340.pc = 1905 ∧
    s340.halted = false ∧
    s340.mem.get 0 = 0 ∧
    s340.mem.get 33 = s.mem.get 22 ∧
    s340.mem.get 34 = s.mem.get 23 ∧
    s340.mem.get 35 = s.mem.get 24 ∧
    s340.mem.get 29 = 4 ∧
    (∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s340.mem.get a = s.mem.get a) := by
  intro s340
  have hNle : (s.mem.get 25).toNat ≤ 5 := by rw [hN]; simp
  have hp := emit_prelude (s := s) hpc hh hZ hONE hNle
    (fun k h1 h2 => hcode k (by omega) (by omega))
  let s22 := runN s 22
  have hs22pc : s22.pc = 1641 := hp.1
  have hs22h : s22.halted = false := hp.2.1
  have hs22Z : s22.mem.get 0 = 0 := hp.2.2.1
  have hs22SK : s22.mem.get 2320 = 2 := by
    rw [hp.2.2.2.1, hN]
    exact (rfl : (5 : Word) - 3 = 2)
  have hs22DI : s22.mem.get 2321 = 0 := hp.2.2.2.2.1
  have hpres22raw := hp.2.2.2.2.2.2
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s22.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    exact hpres22raw a ha31 haSK haDI ha0
  have hONE22 : s22.mem.get 3 = 1 := (hpres22 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK522 : s22.mem.get 2322 = 5 := (hpres22 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hI22 : s22.mem.get 29 = 1 := (hpres22 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR22 : s22.mem.get 28 = s.mem.get 28 := hpres22 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2222 : s22.mem.get 22 = s.mem.get 22 := hpres22 22 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2322 : s22.mem.get 23 = s.mem.get 23 := hpres22 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2422 : s22.mem.get 24 = s.mem.get 24 := hpres22 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g22 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s22.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres22 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_22 : (s22.mem.get 2321).toNat < 5 := by rw [hs22DI]; simp
  have hDIltSK_22 : (s22.mem.get 2321).toNat < (s22.mem.get 2320).toNat := by
    rw [hs22DI, hs22SK]; simp
  have hSKhi_22 : (s22.mem.get 2320).toNat < 32768 := by rw [hs22SK]; simp
  have hsk22 := skip_next (s := s22) hs22pc hs22h hs22Z hONE22 hK522
    hDIlt5_22 hDIltSK_22 hSKhi_22 g22
  have hrun47 : runN s 47 = runN s22 25 := runN_add_eq s 22 25 47 (by decide)
  let s47 := runN s 47
  have hs47eq : s47 = runN s22 25 := hrun47
  have hs47pc : s47.pc = 1641 := by rw [hs47eq]; exact hsk22.1
  have hs47h : s47.halted = false := by rw [hs47eq]; exact hsk22.2.1
  have hs47Z : s47.mem.get 0 = 0 := by rw [hs47eq]; exact hsk22.2.2.1
  have hs47DI : s47.mem.get 2321 = 1 := by
    rw [hs47eq, hsk22.2.2.2.1, hs22DI]
    exact (rfl : (0 : Word) + 1 = 1)
  have hpres47 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s47.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs47eq]
    exact (hsk22.2.2.2.2 a ha18 haDI ha0).trans (hpres22 a ha18 ha31 haSK haDI ha0)
  have hONE47 : s47.mem.get 3 = 1 := (hpres47 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK547 : s47.mem.get 2322 = 5 := (hpres47 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs47SK : s47.mem.get 2320 = 2 := by
    rw [hs47eq]; exact (hsk22.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs22SK
  have hI47 : s47.mem.get 29 = 1 := (hpres47 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR47 : s47.mem.get 28 = s.mem.get 28 := hpres47 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2247 : s47.mem.get 22 = s.mem.get 22 := hpres47 22 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2347 : s47.mem.get 23 = s.mem.get 23 := hpres47 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2447 : s47.mem.get 24 = s.mem.get 24 := hpres47 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g47 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s47.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres47 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_47 : (s47.mem.get 2321).toNat < 5 := by rw [hs47DI]; simp
  have hDIltSK_47 : (s47.mem.get 2321).toNat < (s47.mem.get 2320).toNat := by
    rw [hs47DI, hs47SK]; simp
  have hSKhi_47 : (s47.mem.get 2320).toNat < 32768 := by rw [hs47SK]; simp
  have hsk47 := skip_next (s := s47) hs47pc hs47h hs47Z hONE47 hK547
    hDIlt5_47 hDIltSK_47 hSKhi_47 g47
  have hrun72 : runN s 72 = runN s47 25 := runN_add_eq s 47 25 72 (by decide)
  let s72 := runN s 72
  have hs72eq : s72 = runN s47 25 := hrun72
  have hs72pc : s72.pc = 1641 := by rw [hs72eq]; exact hsk47.1
  have hs72h : s72.halted = false := by rw [hs72eq]; exact hsk47.2.1
  have hs72Z : s72.mem.get 0 = 0 := by rw [hs72eq]; exact hsk47.2.2.1
  have hs72DI : s72.mem.get 2321 = 2 := by
    rw [hs72eq, hsk47.2.2.2.1, hs47DI]
    exact (rfl : (1 : Word) + 1 = 2)
  have hpres72 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s72.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs72eq]
    exact (hsk47.2.2.2.2 a ha18 haDI ha0).trans (hpres47 a ha18 ha31 haSK haDI ha0)
  have hONE72 : s72.mem.get 3 = 1 := (hpres72 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK572 : s72.mem.get 2322 = 5 := (hpres72 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs72SK : s72.mem.get 2320 = 2 := by
    rw [hs72eq]; exact (hsk47.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs47SK
  have hI72 : s72.mem.get 29 = 1 := (hpres72 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR72 : s72.mem.get 28 = s.mem.get 28 := hpres72 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2272 : s72.mem.get 22 = s.mem.get 22 := hpres72 22 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2372 : s72.mem.get 23 = s.mem.get 23 := hpres72 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2472 : s72.mem.get 24 = s.mem.get 24 := hpres72 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g72 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s72.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres72 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have g72S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s72.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres72 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo72 : 1 < (s72.mem.get 28).toNat := by
    rw [hR72]
    have : 1 ≤ 3 := by decide
    omega
  have hRhi72 : (s72.mem.get 28).toNat < 32768 := by rw [hR72]; exact hRhi
  have ht72 := loop_take_eq_di2_idx1 (s := s72) hs72pc hs72h hs72Z hONE72 hK572 hs72DI hs72SK hI72 hRlo72 hRhi72 g72S g72
  have hrun157 : runN s 157 = runN s72 85 := runN_add_eq s 72 85 157 (by decide)
  let s157 := runN s 157
  have hs157eq : s157 = runN s72 85 := hrun157
  have hs157pc : s157.pc = 1641 := by rw [hs157eq]; exact ht72.1
  have hs157h : s157.halted = false := by rw [hs157eq]; exact ht72.2.1
  have hs157Z : s157.mem.get 0 = 0 := by rw [hs157eq]; exact ht72.2.2.1
  have hs157B33 : s157.mem.get 33 = s.mem.get 22 := by
    rw [hs157eq, ht72.2.2.2.1, hQ2272]
  have hI157 : s157.mem.get 29 = 2 := by rw [hs157eq]; exact ht72.2.2.2.2.1
  have hs157DI : s157.mem.get 2321 = 3 := by rw [hs157eq]; exact ht72.2.2.2.2.2.1
  have hpres157 : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s157.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs157eq]
    exact (ht72.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres72 a ha18 ha31 haSK haDI ha0)
  have hONE157 : s157.mem.get 3 = 1 := (hpres157 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5157 : s157.mem.get 2322 = 5 := (hpres157 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs157SK : s157.mem.get 2320 = 2 := by
    rw [hs157eq]
    exact (ht72.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs72SK
  have hR157 : s157.mem.get 28 = s.mem.get 28 := hpres157 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ23157 : s157.mem.get 23 = s.mem.get 23 := hpres157 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24157 : s157.mem.get 24 = s.mem.get 24 := hpres157 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g157 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s157.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
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
    exact (hpres157 (UInt16.ofNat k) n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo157 : (s157.mem.get 2320).toNat < 3 := by rw [hs157SK]; simp
  have g157S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s157.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
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
    exact (hpres157 (UInt16.ofNat k) n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo157 : 2 < (s157.mem.get 28).toNat := by
    rw [hR157]
    have : 2 ≤ 3 := by decide
    omega
  have hRhi157 : (s157.mem.get 28).toNat < 32768 := by rw [hR157]; exact hRhi
  have ht157 := loop_take_gt_di3_idx2 (s := s157) hs157pc hs157h hs157Z hONE157 hK5157 hs157DI hSKlo157 hI157 hRlo157 hRhi157 g157S g157
  have hrun242 : runN s 242 = runN s157 85 := runN_add_eq s 157 85 242 (by decide)
  let s242 := runN s 242
  have hs242eq : s242 = runN s157 85 := hrun242
  have hs242pc : s242.pc = 1641 := by rw [hs242eq]; exact ht157.1
  have hs242h : s242.halted = false := by rw [hs242eq]; exact ht157.2.1
  have hs242Z : s242.mem.get 0 = 0 := by rw [hs242eq]; exact ht157.2.2.1
  have hs242B34 : s242.mem.get 34 = s.mem.get 23 := by
    rw [hs242eq, ht157.2.2.2.1, hQ23157]
  have hI242 : s242.mem.get 29 = 3 := by rw [hs242eq]; exact ht157.2.2.2.2.1
  have hs242DI : s242.mem.get 2321 = 4 := by rw [hs242eq]; exact ht157.2.2.2.2.2.1
  have hpres242 : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s242.mem.get a = s.mem.get a := by
    intro a haB33 haB34 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs242eq]
    exact (ht157.2.2.2.2.2.2 a haB34 ha29 ha18 ha30 haR haDI ha0).trans (hpres157 a haB33 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs242B33 : s242.mem.get 33 = s.mem.get 22 := by
    rw [hs242eq]
    exact (ht157.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs157B33
  have hONE242 : s242.mem.get 3 = 1 := (hpres242 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5242 : s242.mem.get 2322 = 5 := (hpres242 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs242SK : s242.mem.get 2320 = 2 := by
    rw [hs242eq]
    exact (ht157.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs157SK
  have hR242 : s242.mem.get 28 = s.mem.get 28 := hpres242 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24242 : s242.mem.get 24 = s.mem.get 24 := hpres242 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g242 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s242.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
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
    exact (hpres242 (UInt16.ofNat k) n33 n34 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo242 : (s242.mem.get 2320).toNat < 4 := by rw [hs242SK]; simp
  have g242S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s242.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
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
    exact (hpres242 (UInt16.ofNat k) n33 n34 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo242 : 3 < (s242.mem.get 28).toNat := by
    rw [hR242]
    have : 3 ≤ 3 := by decide
    omega
  have hRhi242 : (s242.mem.get 28).toNat < 32768 := by rw [hR242]; exact hRhi
  have ht242 := loop_take_gt_di4_idx3 (s := s242) hs242pc hs242h hs242Z hONE242 hK5242 hs242DI hSKlo242 hI242 hRlo242 hRhi242 g242S g242
  have hrun329 : runN s 329 = runN s242 87 := runN_add_eq s 242 87 329 (by decide)
  let s329 := runN s 329
  have hs329eq : s329 = runN s242 87 := hrun329
  have hs329pc : s329.pc = 1641 := by rw [hs329eq]; exact ht242.1
  have hs329h : s329.halted = false := by rw [hs329eq]; exact ht242.2.1
  have hs329Z : s329.mem.get 0 = 0 := by rw [hs329eq]; exact ht242.2.2.1
  have hs329B35 : s329.mem.get 35 = s.mem.get 24 := by
    rw [hs329eq, ht242.2.2.2.1, hQ24242]
  have hI329 : s329.mem.get 29 = 4 := by rw [hs329eq]; exact ht242.2.2.2.2.1
  have hs329DI : s329.mem.get 2321 = 5 := by rw [hs329eq]; exact ht242.2.2.2.2.2.1
  have hpres329 : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s329.mem.get a = s.mem.get a := by
    intro a haB33 haB34 haB35 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs329eq]
    exact (ht242.2.2.2.2.2.2 a haB35 ha29 ha18 ha30 haR haDI ha0).trans (hpres242 a haB33 haB34 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs329B33 : s329.mem.get 33 = s.mem.get 22 := by
    rw [hs329eq]
    exact (ht242.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs242B33
  have hs329B34 : s329.mem.get 34 = s.mem.get 23 := by
    rw [hs329eq]
    exact (ht242.2.2.2.2.2.2 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs242B34
  have hONE329 : s329.mem.get 3 = 1 := (hpres329 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5329 : s329.mem.get 2322 = 5 := (hpres329 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs329SK : s329.mem.get 2320 = 2 := by
    rw [hs329eq]
    exact (ht242.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs242SK
  have hR329 : s329.mem.get 28 = s.mem.get 28 := hpres329 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g329 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s329.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
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
    exact (hpres329 (UInt16.ofNat k) n33 n34 n35 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hONE329 : s329.mem.get 3 = 1 := (hpres329 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5329x : s329.mem.get 2322 = 5 := (hpres329 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have g329x : ∀ k : Nat, 1641 ≤ k → k < 1677 →
      s329.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
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
    exact (hpres329 (UInt16.ofNat k) n33 n34 n35 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hx := dig_loop_exit (s := s329) hs329pc hs329h hs329Z hONE329 hs329DI hK5329x g329x
  have hrun : s340 = runN s329 11 := runN_add_eq s 329 11 340 (by decide)
  have hsTpc : s340.pc = 1905 := by rw [hrun]; exact hx.1
  have hsTh : s340.halted = false := by rw [hrun]; exact hx.2.1
  have hsTZ : s340.mem.get 0 = 0 := by rw [hrun]; exact hx.2.2.1
  have hsTB33 : s340.mem.get 33 = s.mem.get 22 := by
    rw [hrun]; exact (hx.2.2.2.2 33 (by decide) (by decide)).trans hs329B33
  have hsTB34 : s340.mem.get 34 = s.mem.get 23 := by
    rw [hrun]; exact (hx.2.2.2.2 34 (by decide) (by decide)).trans hs329B34
  have hsTB35 : s340.mem.get 35 = s.mem.get 24 := by
    rw [hrun]; exact (hx.2.2.2.2 35 (by decide) (by decide)).trans hs329B35
  have hsTI : s340.mem.get 29 = 4 := by
    rw [hrun]; exact (hx.2.2.2.2 29 (by decide) (by decide)).trans hI329
  have hpres : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s340.mem.get a = s.mem.get a := by
    intro a haB33 haB34 haB35 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hrun]
    exact (hx.2.2.2.2 a ha18 ha0).trans (hpres329 a haB33 haB34 haB35 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB33, hsTB34, hsTB35, hsTI, hpres⟩


/-- From `EMIT_DIGS` with `NDIG = 4` and `IDX = 0 < ROOM`: write
`Q1`..`Q4` at `BUF+0`..`BUF+3` and reach `AFTER_DIGS`
with `IDX = 4`. 392 steps. -/
theorem emit_ndig4_idx0 {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 4)
    (hI : s.mem.get 29 = 0)
    (hRlo : 3 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s392 := runN s 392
    s392.pc = 1905 ∧
    s392.halted = false ∧
    s392.mem.get 0 = 0 ∧
    s392.mem.get 32 = s.mem.get 21 ∧
    s392.mem.get 33 = s.mem.get 22 ∧
    s392.mem.get 34 = s.mem.get 23 ∧
    s392.mem.get 35 = s.mem.get 24 ∧
    s392.mem.get 29 = 4 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s392.mem.get a = s.mem.get a) := by
  intro s392
  have hNle : (s.mem.get 25).toNat ≤ 5 := by rw [hN]; simp
  have hp := emit_prelude (s := s) hpc hh hZ hONE hNle
    (fun k h1 h2 => hcode k (by omega) (by omega))
  let s22 := runN s 22
  have hs22pc : s22.pc = 1641 := hp.1
  have hs22h : s22.halted = false := hp.2.1
  have hs22Z : s22.mem.get 0 = 0 := hp.2.2.1
  have hs22SK : s22.mem.get 2320 = 1 := by
    rw [hp.2.2.2.1, hN]
    exact (rfl : (5 : Word) - 4 = 1)
  have hs22DI : s22.mem.get 2321 = 0 := hp.2.2.2.2.1
  have hpres22raw := hp.2.2.2.2.2.2
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s22.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    exact hpres22raw a ha31 haSK haDI ha0
  have hONE22 : s22.mem.get 3 = 1 := (hpres22 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK522 : s22.mem.get 2322 = 5 := (hpres22 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hI22 : s22.mem.get 29 = 0 := (hpres22 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR22 : s22.mem.get 28 = s.mem.get 28 := hpres22 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2122 : s22.mem.get 21 = s.mem.get 21 := hpres22 21 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2222 : s22.mem.get 22 = s.mem.get 22 := hpres22 22 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2322 : s22.mem.get 23 = s.mem.get 23 := hpres22 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2422 : s22.mem.get 24 = s.mem.get 24 := hpres22 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g22 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s22.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres22 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_22 : (s22.mem.get 2321).toNat < 5 := by rw [hs22DI]; simp
  have hDIltSK_22 : (s22.mem.get 2321).toNat < (s22.mem.get 2320).toNat := by
    rw [hs22DI, hs22SK]; simp
  have hSKhi_22 : (s22.mem.get 2320).toNat < 32768 := by rw [hs22SK]; simp
  have hsk22 := skip_next (s := s22) hs22pc hs22h hs22Z hONE22 hK522
    hDIlt5_22 hDIltSK_22 hSKhi_22 g22
  have hrun47 : runN s 47 = runN s22 25 := runN_add_eq s 22 25 47 (by decide)
  let s47 := runN s 47
  have hs47eq : s47 = runN s22 25 := hrun47
  have hs47pc : s47.pc = 1641 := by rw [hs47eq]; exact hsk22.1
  have hs47h : s47.halted = false := by rw [hs47eq]; exact hsk22.2.1
  have hs47Z : s47.mem.get 0 = 0 := by rw [hs47eq]; exact hsk22.2.2.1
  have hs47DI : s47.mem.get 2321 = 1 := by
    rw [hs47eq, hsk22.2.2.2.1, hs22DI]
    exact (rfl : (0 : Word) + 1 = 1)
  have hpres47 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s47.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs47eq]
    exact (hsk22.2.2.2.2 a ha18 haDI ha0).trans (hpres22 a ha18 ha31 haSK haDI ha0)
  have hONE47 : s47.mem.get 3 = 1 := (hpres47 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK547 : s47.mem.get 2322 = 5 := (hpres47 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs47SK : s47.mem.get 2320 = 1 := by
    rw [hs47eq]; exact (hsk22.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs22SK
  have hI47 : s47.mem.get 29 = 0 := (hpres47 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR47 : s47.mem.get 28 = s.mem.get 28 := hpres47 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2147 : s47.mem.get 21 = s.mem.get 21 := hpres47 21 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2247 : s47.mem.get 22 = s.mem.get 22 := hpres47 22 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2347 : s47.mem.get 23 = s.mem.get 23 := hpres47 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2447 : s47.mem.get 24 = s.mem.get 24 := hpres47 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g47 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s47.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres47 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have g47S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s47.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres47 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo47 : 0 < (s47.mem.get 28).toNat := by
    rw [hR47]
    have : 0 ≤ 3 := by decide
    omega
  have hRhi47 : (s47.mem.get 28).toNat < 32768 := by rw [hR47]; exact hRhi
  have ht47 := loop_take_eq_di1_idx0 (s := s47) hs47pc hs47h hs47Z hONE47 hK547 hs47DI hs47SK hI47 hRlo47 hRhi47 g47S g47
  have hrun128 : runN s 128 = runN s47 81 := runN_add_eq s 47 81 128 (by decide)
  let s128 := runN s 128
  have hs128eq : s128 = runN s47 81 := hrun128
  have hs128pc : s128.pc = 1641 := by rw [hs128eq]; exact ht47.1
  have hs128h : s128.halted = false := by rw [hs128eq]; exact ht47.2.1
  have hs128Z : s128.mem.get 0 = 0 := by rw [hs128eq]; exact ht47.2.2.1
  have hs128B32 : s128.mem.get 32 = s.mem.get 21 := by
    rw [hs128eq, ht47.2.2.2.1, hQ2147]
  have hI128 : s128.mem.get 29 = 1 := by rw [hs128eq]; exact ht47.2.2.2.2.1
  have hs128DI : s128.mem.get 2321 = 2 := by rw [hs128eq]; exact ht47.2.2.2.2.2.1
  have hpres128 : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s128.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs128eq]
    exact (ht47.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres47 a ha18 ha31 haSK haDI ha0)
  have hONE128 : s128.mem.get 3 = 1 := (hpres128 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5128 : s128.mem.get 2322 = 5 := (hpres128 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs128SK : s128.mem.get 2320 = 1 := by
    rw [hs128eq]
    exact (ht47.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs47SK
  have hR128 : s128.mem.get 28 = s.mem.get 28 := hpres128 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ22128 : s128.mem.get 22 = s.mem.get 22 := hpres128 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ23128 : s128.mem.get 23 = s.mem.get 23 := hpres128 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24128 : s128.mem.get 24 = s.mem.get 24 := hpres128 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g128 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s128.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres128 (UInt16.ofNat k) n32 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo128 : (s128.mem.get 2320).toNat < 2 := by rw [hs128SK]; simp
  have g128S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s128.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres128 (UInt16.ofNat k) n32 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo128 : 1 < (s128.mem.get 28).toNat := by
    rw [hR128]
    have : 1 ≤ 3 := by decide
    omega
  have hRhi128 : (s128.mem.get 28).toNat < 32768 := by rw [hR128]; exact hRhi
  have ht128 := loop_take_gt_di2_idx1 (s := s128) hs128pc hs128h hs128Z hONE128 hK5128 hs128DI hSKlo128 hI128 hRlo128 hRhi128 g128S g128
  have hrun209 : runN s 209 = runN s128 81 := runN_add_eq s 128 81 209 (by decide)
  let s209 := runN s 209
  have hs209eq : s209 = runN s128 81 := hrun209
  have hs209pc : s209.pc = 1641 := by rw [hs209eq]; exact ht128.1
  have hs209h : s209.halted = false := by rw [hs209eq]; exact ht128.2.1
  have hs209Z : s209.mem.get 0 = 0 := by rw [hs209eq]; exact ht128.2.2.1
  have hs209B33 : s209.mem.get 33 = s.mem.get 22 := by
    rw [hs209eq, ht128.2.2.2.1, hQ22128]
  have hI209 : s209.mem.get 29 = 2 := by rw [hs209eq]; exact ht128.2.2.2.2.1
  have hs209DI : s209.mem.get 2321 = 3 := by rw [hs209eq]; exact ht128.2.2.2.2.2.1
  have hpres209 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s209.mem.get a = s.mem.get a := by
    intro a haB32 haB33 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs209eq]
    exact (ht128.2.2.2.2.2.2 a haB33 ha29 ha18 ha30 haR haDI ha0).trans (hpres128 a haB32 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs209B32 : s209.mem.get 32 = s.mem.get 21 := by
    rw [hs209eq]
    exact (ht128.2.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs128B32
  have hONE209 : s209.mem.get 3 = 1 := (hpres209 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5209 : s209.mem.get 2322 = 5 := (hpres209 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs209SK : s209.mem.get 2320 = 1 := by
    rw [hs209eq]
    exact (ht128.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs128SK
  have hR209 : s209.mem.get 28 = s.mem.get 28 := hpres209 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ23209 : s209.mem.get 23 = s.mem.get 23 := hpres209 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24209 : s209.mem.get 24 = s.mem.get 24 := hpres209 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g209 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s209.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres209 (UInt16.ofNat k) n32 n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo209 : (s209.mem.get 2320).toNat < 3 := by rw [hs209SK]; simp
  have g209S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s209.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres209 (UInt16.ofNat k) n32 n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo209 : 2 < (s209.mem.get 28).toNat := by
    rw [hR209]
    have : 2 ≤ 3 := by decide
    omega
  have hRhi209 : (s209.mem.get 28).toNat < 32768 := by rw [hR209]; exact hRhi
  have ht209 := loop_take_gt_di3_idx2 (s := s209) hs209pc hs209h hs209Z hONE209 hK5209 hs209DI hSKlo209 hI209 hRlo209 hRhi209 g209S g209
  have hrun294 : runN s 294 = runN s209 85 := runN_add_eq s 209 85 294 (by decide)
  let s294 := runN s 294
  have hs294eq : s294 = runN s209 85 := hrun294
  have hs294pc : s294.pc = 1641 := by rw [hs294eq]; exact ht209.1
  have hs294h : s294.halted = false := by rw [hs294eq]; exact ht209.2.1
  have hs294Z : s294.mem.get 0 = 0 := by rw [hs294eq]; exact ht209.2.2.1
  have hs294B34 : s294.mem.get 34 = s.mem.get 23 := by
    rw [hs294eq, ht209.2.2.2.1, hQ23209]
  have hI294 : s294.mem.get 29 = 3 := by rw [hs294eq]; exact ht209.2.2.2.2.1
  have hs294DI : s294.mem.get 2321 = 4 := by rw [hs294eq]; exact ht209.2.2.2.2.2.1
  have hpres294 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s294.mem.get a = s.mem.get a := by
    intro a haB32 haB33 haB34 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs294eq]
    exact (ht209.2.2.2.2.2.2 a haB34 ha29 ha18 ha30 haR haDI ha0).trans (hpres209 a haB32 haB33 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs294B32 : s294.mem.get 32 = s.mem.get 21 := by
    rw [hs294eq]
    exact (ht209.2.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs209B32
  have hs294B33 : s294.mem.get 33 = s.mem.get 22 := by
    rw [hs294eq]
    exact (ht209.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs209B33
  have hONE294 : s294.mem.get 3 = 1 := (hpres294 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5294 : s294.mem.get 2322 = 5 := (hpres294 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs294SK : s294.mem.get 2320 = 1 := by
    rw [hs294eq]
    exact (ht209.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs209SK
  have hR294 : s294.mem.get 28 = s.mem.get 28 := hpres294 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24294 : s294.mem.get 24 = s.mem.get 24 := hpres294 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g294 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s294.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres294 (UInt16.ofNat k) n32 n33 n34 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo294 : (s294.mem.get 2320).toNat < 4 := by rw [hs294SK]; simp
  have g294S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s294.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres294 (UInt16.ofNat k) n32 n33 n34 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo294 : 3 < (s294.mem.get 28).toNat := by
    rw [hR294]
    have : 3 ≤ 3 := by decide
    omega
  have hRhi294 : (s294.mem.get 28).toNat < 32768 := by rw [hR294]; exact hRhi
  have ht294 := loop_take_gt_di4_idx3 (s := s294) hs294pc hs294h hs294Z hONE294 hK5294 hs294DI hSKlo294 hI294 hRlo294 hRhi294 g294S g294
  have hrun381 : runN s 381 = runN s294 87 := runN_add_eq s 294 87 381 (by decide)
  let s381 := runN s 381
  have hs381eq : s381 = runN s294 87 := hrun381
  have hs381pc : s381.pc = 1641 := by rw [hs381eq]; exact ht294.1
  have hs381h : s381.halted = false := by rw [hs381eq]; exact ht294.2.1
  have hs381Z : s381.mem.get 0 = 0 := by rw [hs381eq]; exact ht294.2.2.1
  have hs381B35 : s381.mem.get 35 = s.mem.get 24 := by
    rw [hs381eq, ht294.2.2.2.1, hQ24294]
  have hI381 : s381.mem.get 29 = 4 := by rw [hs381eq]; exact ht294.2.2.2.2.1
  have hs381DI : s381.mem.get 2321 = 5 := by rw [hs381eq]; exact ht294.2.2.2.2.2.1
  have hpres381 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s381.mem.get a = s.mem.get a := by
    intro a haB32 haB33 haB34 haB35 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs381eq]
    exact (ht294.2.2.2.2.2.2 a haB35 ha29 ha18 ha30 haR haDI ha0).trans (hpres294 a haB32 haB33 haB34 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs381B32 : s381.mem.get 32 = s.mem.get 21 := by
    rw [hs381eq]
    exact (ht294.2.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs294B32
  have hs381B33 : s381.mem.get 33 = s.mem.get 22 := by
    rw [hs381eq]
    exact (ht294.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs294B33
  have hs381B34 : s381.mem.get 34 = s.mem.get 23 := by
    rw [hs381eq]
    exact (ht294.2.2.2.2.2.2 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs294B34
  have hONE381 : s381.mem.get 3 = 1 := (hpres381 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5381 : s381.mem.get 2322 = 5 := (hpres381 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs381SK : s381.mem.get 2320 = 1 := by
    rw [hs381eq]
    exact (ht294.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs294SK
  have hR381 : s381.mem.get 28 = s.mem.get 28 := hpres381 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g381 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s381.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres381 (UInt16.ofNat k) n32 n33 n34 n35 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hONE381 : s381.mem.get 3 = 1 := (hpres381 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5381x : s381.mem.get 2322 = 5 := (hpres381 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have g381x : ∀ k : Nat, 1641 ≤ k → k < 1677 →
      s381.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres381 (UInt16.ofNat k) n32 n33 n34 n35 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hx := dig_loop_exit (s := s381) hs381pc hs381h hs381Z hONE381 hs381DI hK5381x g381x
  have hrun : s392 = runN s381 11 := runN_add_eq s 381 11 392 (by decide)
  have hsTpc : s392.pc = 1905 := by rw [hrun]; exact hx.1
  have hsTh : s392.halted = false := by rw [hrun]; exact hx.2.1
  have hsTZ : s392.mem.get 0 = 0 := by rw [hrun]; exact hx.2.2.1
  have hsTB32 : s392.mem.get 32 = s.mem.get 21 := by
    rw [hrun]; exact (hx.2.2.2.2 32 (by decide) (by decide)).trans hs381B32
  have hsTB33 : s392.mem.get 33 = s.mem.get 22 := by
    rw [hrun]; exact (hx.2.2.2.2 33 (by decide) (by decide)).trans hs381B33
  have hsTB34 : s392.mem.get 34 = s.mem.get 23 := by
    rw [hrun]; exact (hx.2.2.2.2 34 (by decide) (by decide)).trans hs381B34
  have hsTB35 : s392.mem.get 35 = s.mem.get 24 := by
    rw [hrun]; exact (hx.2.2.2.2 35 (by decide) (by decide)).trans hs381B35
  have hsTI : s392.mem.get 29 = 4 := by
    rw [hrun]; exact (hx.2.2.2.2 29 (by decide) (by decide)).trans hI381
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s392.mem.get a = s.mem.get a := by
    intro a haB32 haB33 haB34 haB35 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hrun]
    exact (hx.2.2.2.2 a ha18 ha0).trans (hpres381 a haB32 haB33 haB34 haB35 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB32, hsTB33, hsTB34, hsTB35, hsTI, hpres⟩


/-- From `EMIT_DIGS` with `NDIG = 4` and `IDX = 1 < ROOM`: write
`Q1`..`Q4` at `BUF+1`..`BUF+4` and reach `AFTER_DIGS`
with `IDX = 5`. 400 steps. -/
theorem emit_ndig4_idx1 {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 4)
    (hI : s.mem.get 29 = 1)
    (hRlo : 4 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s400 := runN s 400
    s400.pc = 1905 ∧
    s400.halted = false ∧
    s400.mem.get 0 = 0 ∧
    s400.mem.get 33 = s.mem.get 21 ∧
    s400.mem.get 34 = s.mem.get 22 ∧
    s400.mem.get 35 = s.mem.get 23 ∧
    s400.mem.get 36 = s.mem.get 24 ∧
    s400.mem.get 29 = 5 ∧
    (∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s400.mem.get a = s.mem.get a) := by
  intro s400
  have hNle : (s.mem.get 25).toNat ≤ 5 := by rw [hN]; simp
  have hp := emit_prelude (s := s) hpc hh hZ hONE hNle
    (fun k h1 h2 => hcode k (by omega) (by omega))
  let s22 := runN s 22
  have hs22pc : s22.pc = 1641 := hp.1
  have hs22h : s22.halted = false := hp.2.1
  have hs22Z : s22.mem.get 0 = 0 := hp.2.2.1
  have hs22SK : s22.mem.get 2320 = 1 := by
    rw [hp.2.2.2.1, hN]
    exact (rfl : (5 : Word) - 4 = 1)
  have hs22DI : s22.mem.get 2321 = 0 := hp.2.2.2.2.1
  have hpres22raw := hp.2.2.2.2.2.2
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s22.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    exact hpres22raw a ha31 haSK haDI ha0
  have hONE22 : s22.mem.get 3 = 1 := (hpres22 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK522 : s22.mem.get 2322 = 5 := (hpres22 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hI22 : s22.mem.get 29 = 1 := (hpres22 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR22 : s22.mem.get 28 = s.mem.get 28 := hpres22 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2122 : s22.mem.get 21 = s.mem.get 21 := hpres22 21 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2222 : s22.mem.get 22 = s.mem.get 22 := hpres22 22 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2322 : s22.mem.get 23 = s.mem.get 23 := hpres22 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2422 : s22.mem.get 24 = s.mem.get 24 := hpres22 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g22 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s22.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres22 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hDIlt5_22 : (s22.mem.get 2321).toNat < 5 := by rw [hs22DI]; simp
  have hDIltSK_22 : (s22.mem.get 2321).toNat < (s22.mem.get 2320).toNat := by
    rw [hs22DI, hs22SK]; simp
  have hSKhi_22 : (s22.mem.get 2320).toNat < 32768 := by rw [hs22SK]; simp
  have hsk22 := skip_next (s := s22) hs22pc hs22h hs22Z hONE22 hK522
    hDIlt5_22 hDIltSK_22 hSKhi_22 g22
  have hrun47 : runN s 47 = runN s22 25 := runN_add_eq s 22 25 47 (by decide)
  let s47 := runN s 47
  have hs47eq : s47 = runN s22 25 := hrun47
  have hs47pc : s47.pc = 1641 := by rw [hs47eq]; exact hsk22.1
  have hs47h : s47.halted = false := by rw [hs47eq]; exact hsk22.2.1
  have hs47Z : s47.mem.get 0 = 0 := by rw [hs47eq]; exact hsk22.2.2.1
  have hs47DI : s47.mem.get 2321 = 1 := by
    rw [hs47eq, hsk22.2.2.2.1, hs22DI]
    exact (rfl : (0 : Word) + 1 = 1)
  have hpres47 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s47.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    rw [hs47eq]
    exact (hsk22.2.2.2.2 a ha18 haDI ha0).trans (hpres22 a ha18 ha31 haSK haDI ha0)
  have hONE47 : s47.mem.get 3 = 1 := (hpres47 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK547 : s47.mem.get 2322 = 5 := (hpres47 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs47SK : s47.mem.get 2320 = 1 := by
    rw [hs47eq]; exact (hsk22.2.2.2.2 2320 (by decide) (by decide) (by decide)).trans hs22SK
  have hI47 : s47.mem.get 29 = 1 := (hpres47 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR47 : s47.mem.get 28 = s.mem.get 28 := hpres47 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2147 : s47.mem.get 21 = s.mem.get 21 := hpres47 21 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2247 : s47.mem.get 22 = s.mem.get 22 := hpres47 22 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2347 : s47.mem.get 23 = s.mem.get 23 := hpres47 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2447 : s47.mem.get 24 = s.mem.get 24 := hpres47 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g47 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s47.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres47 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have g47S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s47.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres47 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo47 : 1 < (s47.mem.get 28).toNat := by
    rw [hR47]
    have : 1 ≤ 4 := by decide
    omega
  have hRhi47 : (s47.mem.get 28).toNat < 32768 := by rw [hR47]; exact hRhi
  have ht47 := loop_take_eq_di1_idx1 (s := s47) hs47pc hs47h hs47Z hONE47 hK547 hs47DI hs47SK hI47 hRlo47 hRhi47 g47S g47
  have hrun130 : runN s 130 = runN s47 83 := runN_add_eq s 47 83 130 (by decide)
  let s130 := runN s 130
  have hs130eq : s130 = runN s47 83 := hrun130
  have hs130pc : s130.pc = 1641 := by rw [hs130eq]; exact ht47.1
  have hs130h : s130.halted = false := by rw [hs130eq]; exact ht47.2.1
  have hs130Z : s130.mem.get 0 = 0 := by rw [hs130eq]; exact ht47.2.2.1
  have hs130B33 : s130.mem.get 33 = s.mem.get 21 := by
    rw [hs130eq, ht47.2.2.2.1, hQ2147]
  have hI130 : s130.mem.get 29 = 2 := by rw [hs130eq]; exact ht47.2.2.2.2.1
  have hs130DI : s130.mem.get 2321 = 2 := by rw [hs130eq]; exact ht47.2.2.2.2.2.1
  have hpres130 : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s130.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs130eq]
    exact (ht47.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres47 a ha18 ha31 haSK haDI ha0)
  have hONE130 : s130.mem.get 3 = 1 := (hpres130 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5130 : s130.mem.get 2322 = 5 := (hpres130 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs130SK : s130.mem.get 2320 = 1 := by
    rw [hs130eq]
    exact (ht47.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs47SK
  have hR130 : s130.mem.get 28 = s.mem.get 28 := hpres130 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ22130 : s130.mem.get 22 = s.mem.get 22 := hpres130 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ23130 : s130.mem.get 23 = s.mem.get 23 := hpres130 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24130 : s130.mem.get 24 = s.mem.get 24 := hpres130 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g130 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s130.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
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
    exact (hpres130 (UInt16.ofNat k) n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo130 : (s130.mem.get 2320).toNat < 2 := by rw [hs130SK]; simp
  have g130S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s130.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
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
    exact (hpres130 (UInt16.ofNat k) n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo130 : 2 < (s130.mem.get 28).toNat := by
    rw [hR130]
    have : 2 ≤ 4 := by decide
    omega
  have hRhi130 : (s130.mem.get 28).toNat < 32768 := by rw [hR130]; exact hRhi
  have ht130 := loop_take_gt_di2_idx2 (s := s130) hs130pc hs130h hs130Z hONE130 hK5130 hs130DI hSKlo130 hI130 hRlo130 hRhi130 g130S g130
  have hrun213 : runN s 213 = runN s130 83 := runN_add_eq s 130 83 213 (by decide)
  let s213 := runN s 213
  have hs213eq : s213 = runN s130 83 := hrun213
  have hs213pc : s213.pc = 1641 := by rw [hs213eq]; exact ht130.1
  have hs213h : s213.halted = false := by rw [hs213eq]; exact ht130.2.1
  have hs213Z : s213.mem.get 0 = 0 := by rw [hs213eq]; exact ht130.2.2.1
  have hs213B34 : s213.mem.get 34 = s.mem.get 22 := by
    rw [hs213eq, ht130.2.2.2.1, hQ22130]
  have hI213 : s213.mem.get 29 = 3 := by rw [hs213eq]; exact ht130.2.2.2.2.1
  have hs213DI : s213.mem.get 2321 = 3 := by rw [hs213eq]; exact ht130.2.2.2.2.2.1
  have hpres213 : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s213.mem.get a = s.mem.get a := by
    intro a haB33 haB34 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs213eq]
    exact (ht130.2.2.2.2.2.2 a haB34 ha29 ha18 ha30 haR haDI ha0).trans (hpres130 a haB33 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs213B33 : s213.mem.get 33 = s.mem.get 21 := by
    rw [hs213eq]
    exact (ht130.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs130B33
  have hONE213 : s213.mem.get 3 = 1 := (hpres213 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5213 : s213.mem.get 2322 = 5 := (hpres213 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs213SK : s213.mem.get 2320 = 1 := by
    rw [hs213eq]
    exact (ht130.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs130SK
  have hR213 : s213.mem.get 28 = s.mem.get 28 := hpres213 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ23213 : s213.mem.get 23 = s.mem.get 23 := hpres213 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24213 : s213.mem.get 24 = s.mem.get 24 := hpres213 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g213 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s213.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
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
    exact (hpres213 (UInt16.ofNat k) n33 n34 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo213 : (s213.mem.get 2320).toNat < 3 := by rw [hs213SK]; simp
  have g213S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s213.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
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
    exact (hpres213 (UInt16.ofNat k) n33 n34 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo213 : 3 < (s213.mem.get 28).toNat := by
    rw [hR213]
    have : 3 ≤ 4 := by decide
    omega
  have hRhi213 : (s213.mem.get 28).toNat < 32768 := by rw [hR213]; exact hRhi
  have ht213 := loop_take_gt_di3_idx3 (s := s213) hs213pc hs213h hs213Z hONE213 hK5213 hs213DI hSKlo213 hI213 hRlo213 hRhi213 g213S g213
  have hrun300 : runN s 300 = runN s213 87 := runN_add_eq s 213 87 300 (by decide)
  let s300 := runN s 300
  have hs300eq : s300 = runN s213 87 := hrun300
  have hs300pc : s300.pc = 1641 := by rw [hs300eq]; exact ht213.1
  have hs300h : s300.halted = false := by rw [hs300eq]; exact ht213.2.1
  have hs300Z : s300.mem.get 0 = 0 := by rw [hs300eq]; exact ht213.2.2.1
  have hs300B35 : s300.mem.get 35 = s.mem.get 23 := by
    rw [hs300eq, ht213.2.2.2.1, hQ23213]
  have hI300 : s300.mem.get 29 = 4 := by rw [hs300eq]; exact ht213.2.2.2.2.1
  have hs300DI : s300.mem.get 2321 = 4 := by rw [hs300eq]; exact ht213.2.2.2.2.2.1
  have hpres300 : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s300.mem.get a = s.mem.get a := by
    intro a haB33 haB34 haB35 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs300eq]
    exact (ht213.2.2.2.2.2.2 a haB35 ha29 ha18 ha30 haR haDI ha0).trans (hpres213 a haB33 haB34 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs300B33 : s300.mem.get 33 = s.mem.get 21 := by
    rw [hs300eq]
    exact (ht213.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs213B33
  have hs300B34 : s300.mem.get 34 = s.mem.get 22 := by
    rw [hs300eq]
    exact (ht213.2.2.2.2.2.2 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs213B34
  have hONE300 : s300.mem.get 3 = 1 := (hpres300 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5300 : s300.mem.get 2322 = 5 := (hpres300 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs300SK : s300.mem.get 2320 = 1 := by
    rw [hs300eq]
    exact (ht213.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs213SK
  have hR300 : s300.mem.get 28 = s.mem.get 28 := hpres300 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24300 : s300.mem.get 24 = s.mem.get 24 := hpres300 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g300 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s300.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
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
    exact (hpres300 (UInt16.ofNat k) n33 n34 n35 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo300 : (s300.mem.get 2320).toNat < 4 := by rw [hs300SK]; simp
  have g300S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s300.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
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
    exact (hpres300 (UInt16.ofNat k) n33 n34 n35 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo300 : 4 < (s300.mem.get 28).toNat := by
    rw [hR300]
    have : 4 ≤ 4 := by decide
    omega
  have hRhi300 : (s300.mem.get 28).toNat < 32768 := by rw [hR300]; exact hRhi
  have ht300 := loop_take_gt_di4_idx4 (s := s300) hs300pc hs300h hs300Z hONE300 hK5300 hs300DI hSKlo300 hI300 hRlo300 hRhi300 g300S g300
  have hrun389 : runN s 389 = runN s300 89 := runN_add_eq s 300 89 389 (by decide)
  let s389 := runN s 389
  have hs389eq : s389 = runN s300 89 := hrun389
  have hs389pc : s389.pc = 1641 := by rw [hs389eq]; exact ht300.1
  have hs389h : s389.halted = false := by rw [hs389eq]; exact ht300.2.1
  have hs389Z : s389.mem.get 0 = 0 := by rw [hs389eq]; exact ht300.2.2.1
  have hs389B36 : s389.mem.get 36 = s.mem.get 24 := by
    rw [hs389eq, ht300.2.2.2.1, hQ24300]
  have hI389 : s389.mem.get 29 = 5 := by rw [hs389eq]; exact ht300.2.2.2.2.1
  have hs389DI : s389.mem.get 2321 = 5 := by rw [hs389eq]; exact ht300.2.2.2.2.2.1
  have hpres389 : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s389.mem.get a = s.mem.get a := by
    intro a haB33 haB34 haB35 haB36 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs389eq]
    exact (ht300.2.2.2.2.2.2 a haB36 ha29 ha18 ha30 haR haDI ha0).trans (hpres300 a haB33 haB34 haB35 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs389B33 : s389.mem.get 33 = s.mem.get 21 := by
    rw [hs389eq]
    exact (ht300.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs300B33
  have hs389B34 : s389.mem.get 34 = s.mem.get 22 := by
    rw [hs389eq]
    exact (ht300.2.2.2.2.2.2 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs300B34
  have hs389B35 : s389.mem.get 35 = s.mem.get 23 := by
    rw [hs389eq]
    exact (ht300.2.2.2.2.2.2 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs300B35
  have hONE389 : s389.mem.get 3 = 1 := (hpres389 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5389 : s389.mem.get 2322 = 5 := (hpres389 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs389SK : s389.mem.get 2320 = 1 := by
    rw [hs389eq]
    exact (ht300.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs300SK
  have hR389 : s389.mem.get 28 = s.mem.get 28 := hpres389 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g389 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s389.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
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
    exact (hpres389 (UInt16.ofNat k) n33 n34 n35 n36 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hONE389 : s389.mem.get 3 = 1 := (hpres389 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5389x : s389.mem.get 2322 = 5 := (hpres389 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have g389x : ∀ k : Nat, 1641 ≤ k → k < 1677 →
      s389.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
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
    exact (hpres389 (UInt16.ofNat k) n33 n34 n35 n36 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hx := dig_loop_exit (s := s389) hs389pc hs389h hs389Z hONE389 hs389DI hK5389x g389x
  have hrun : s400 = runN s389 11 := runN_add_eq s 389 11 400 (by decide)
  have hsTpc : s400.pc = 1905 := by rw [hrun]; exact hx.1
  have hsTh : s400.halted = false := by rw [hrun]; exact hx.2.1
  have hsTZ : s400.mem.get 0 = 0 := by rw [hrun]; exact hx.2.2.1
  have hsTB33 : s400.mem.get 33 = s.mem.get 21 := by
    rw [hrun]; exact (hx.2.2.2.2 33 (by decide) (by decide)).trans hs389B33
  have hsTB34 : s400.mem.get 34 = s.mem.get 22 := by
    rw [hrun]; exact (hx.2.2.2.2 34 (by decide) (by decide)).trans hs389B34
  have hsTB35 : s400.mem.get 35 = s.mem.get 23 := by
    rw [hrun]; exact (hx.2.2.2.2 35 (by decide) (by decide)).trans hs389B35
  have hsTB36 : s400.mem.get 36 = s.mem.get 24 := by
    rw [hrun]; exact (hx.2.2.2.2 36 (by decide) (by decide)).trans hs389B36
  have hsTI : s400.mem.get 29 = 5 := by
    rw [hrun]; exact (hx.2.2.2.2 29 (by decide) (by decide)).trans hI389
  have hpres : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s400.mem.get a = s.mem.get a := by
    intro a haB33 haB34 haB35 haB36 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hrun]
    exact (hx.2.2.2.2 a ha18 ha0).trans (hpres389 a haB33 haB34 haB35 haB36 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB33, hsTB34, hsTB35, hsTB36, hsTI, hpres⟩


/-- From `EMIT_DIGS` with `NDIG = 5` and `IDX = 0 < ROOM`: write
`Q0`..`Q4` at `BUF+0`..`BUF+4` and reach `AFTER_DIGS`
with `IDX = 5`. 450 steps. -/
theorem emit_ndig5_idx0 {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 5)
    (hI : s.mem.get 29 = 0)
    (hRlo : 4 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s450 := runN s 450
    s450.pc = 1905 ∧
    s450.halted = false ∧
    s450.mem.get 0 = 0 ∧
    s450.mem.get 32 = s.mem.get 20 ∧
    s450.mem.get 33 = s.mem.get 21 ∧
    s450.mem.get 34 = s.mem.get 22 ∧
    s450.mem.get 35 = s.mem.get 23 ∧
    s450.mem.get 36 = s.mem.get 24 ∧
    s450.mem.get 29 = 5 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s450.mem.get a = s.mem.get a) := by
  intro s450
  have hNle : (s.mem.get 25).toNat ≤ 5 := by rw [hN]; simp
  have hp := emit_prelude (s := s) hpc hh hZ hONE hNle
    (fun k h1 h2 => hcode k (by omega) (by omega))
  let s22 := runN s 22
  have hs22pc : s22.pc = 1641 := hp.1
  have hs22h : s22.halted = false := hp.2.1
  have hs22Z : s22.mem.get 0 = 0 := hp.2.2.1
  have hs22SK : s22.mem.get 2320 = 0 := by
    rw [hp.2.2.2.1, hN]
    exact (rfl : (5 : Word) - 5 = 0)
  have hs22DI : s22.mem.get 2321 = 0 := hp.2.2.2.2.1
  have hpres22raw := hp.2.2.2.2.2.2
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s22.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    exact hpres22raw a ha31 haSK haDI ha0
  have hONE22 : s22.mem.get 3 = 1 := (hpres22 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK522 : s22.mem.get 2322 = 5 := (hpres22 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hI22 : s22.mem.get 29 = 0 := (hpres22 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR22 : s22.mem.get 28 = s.mem.get 28 := hpres22 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2022 : s22.mem.get 20 = s.mem.get 20 := hpres22 20 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2122 : s22.mem.get 21 = s.mem.get 21 := hpres22 21 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2222 : s22.mem.get 22 = s.mem.get 22 := hpres22 22 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2322 : s22.mem.get 23 = s.mem.get 23 := hpres22 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2422 : s22.mem.get 24 = s.mem.get 24 := hpres22 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g22 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s22.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres22 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have g22S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s22.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres22 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo22 : 0 < (s22.mem.get 28).toNat := by
    rw [hR22]
    have : 0 ≤ 4 := by decide
    omega
  have hRhi22 : (s22.mem.get 28).toNat < 32768 := by rw [hR22]; exact hRhi
  have ht22 := loop_take_eq_di0_idx0 (s := s22) hs22pc hs22h hs22Z hONE22 hK522 hs22DI hs22SK hI22 hRlo22 hRhi22 g22S g22
  have hrun101 : runN s 101 = runN s22 79 := runN_add_eq s 22 79 101 (by decide)
  let s101 := runN s 101
  have hs101eq : s101 = runN s22 79 := hrun101
  have hs101pc : s101.pc = 1641 := by rw [hs101eq]; exact ht22.1
  have hs101h : s101.halted = false := by rw [hs101eq]; exact ht22.2.1
  have hs101Z : s101.mem.get 0 = 0 := by rw [hs101eq]; exact ht22.2.2.1
  have hs101B32 : s101.mem.get 32 = s.mem.get 20 := by
    rw [hs101eq, ht22.2.2.2.1, hQ2022]
  have hI101 : s101.mem.get 29 = 1 := by rw [hs101eq]; exact ht22.2.2.2.2.1
  have hs101DI : s101.mem.get 2321 = 1 := by rw [hs101eq]; exact ht22.2.2.2.2.2.1
  have hpres101 : ∀ a, a ≠ 32 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s101.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs101eq]
    exact (ht22.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres22 a ha18 ha31 haSK haDI ha0)
  have hONE101 : s101.mem.get 3 = 1 := (hpres101 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5101 : s101.mem.get 2322 = 5 := (hpres101 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs101SK : s101.mem.get 2320 = 0 := by
    rw [hs101eq]
    exact (ht22.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs22SK
  have hR101 : s101.mem.get 28 = s.mem.get 28 := hpres101 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ21101 : s101.mem.get 21 = s.mem.get 21 := hpres101 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ22101 : s101.mem.get 22 = s.mem.get 22 := hpres101 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ23101 : s101.mem.get 23 = s.mem.get 23 := hpres101 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24101 : s101.mem.get 24 = s.mem.get 24 := hpres101 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g101 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s101.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres101 (UInt16.ofNat k) n32 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo101 : (s101.mem.get 2320).toNat < 1 := by rw [hs101SK]; simp
  have g101S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s101.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres101 (UInt16.ofNat k) n32 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo101 : 1 < (s101.mem.get 28).toNat := by
    rw [hR101]
    have : 1 ≤ 4 := by decide
    omega
  have hRhi101 : (s101.mem.get 28).toNat < 32768 := by rw [hR101]; exact hRhi
  have ht101 := loop_take_gt_di1_idx1 (s := s101) hs101pc hs101h hs101Z hONE101 hK5101 hs101DI hSKlo101 hI101 hRlo101 hRhi101 g101S g101
  have hrun180 : runN s 180 = runN s101 79 := runN_add_eq s 101 79 180 (by decide)
  let s180 := runN s 180
  have hs180eq : s180 = runN s101 79 := hrun180
  have hs180pc : s180.pc = 1641 := by rw [hs180eq]; exact ht101.1
  have hs180h : s180.halted = false := by rw [hs180eq]; exact ht101.2.1
  have hs180Z : s180.mem.get 0 = 0 := by rw [hs180eq]; exact ht101.2.2.1
  have hs180B33 : s180.mem.get 33 = s.mem.get 21 := by
    rw [hs180eq, ht101.2.2.2.1, hQ21101]
  have hI180 : s180.mem.get 29 = 2 := by rw [hs180eq]; exact ht101.2.2.2.2.1
  have hs180DI : s180.mem.get 2321 = 2 := by rw [hs180eq]; exact ht101.2.2.2.2.2.1
  have hpres180 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s180.mem.get a = s.mem.get a := by
    intro a haB32 haB33 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs180eq]
    exact (ht101.2.2.2.2.2.2 a haB33 ha29 ha18 ha30 haR haDI ha0).trans (hpres101 a haB32 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs180B32 : s180.mem.get 32 = s.mem.get 20 := by
    rw [hs180eq]
    exact (ht101.2.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs101B32
  have hONE180 : s180.mem.get 3 = 1 := (hpres180 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5180 : s180.mem.get 2322 = 5 := (hpres180 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs180SK : s180.mem.get 2320 = 0 := by
    rw [hs180eq]
    exact (ht101.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs101SK
  have hR180 : s180.mem.get 28 = s.mem.get 28 := hpres180 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ22180 : s180.mem.get 22 = s.mem.get 22 := hpres180 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ23180 : s180.mem.get 23 = s.mem.get 23 := hpres180 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24180 : s180.mem.get 24 = s.mem.get 24 := hpres180 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g180 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s180.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres180 (UInt16.ofNat k) n32 n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo180 : (s180.mem.get 2320).toNat < 2 := by rw [hs180SK]; simp
  have g180S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s180.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres180 (UInt16.ofNat k) n32 n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo180 : 2 < (s180.mem.get 28).toNat := by
    rw [hR180]
    have : 2 ≤ 4 := by decide
    omega
  have hRhi180 : (s180.mem.get 28).toNat < 32768 := by rw [hR180]; exact hRhi
  have ht180 := loop_take_gt_di2_idx2 (s := s180) hs180pc hs180h hs180Z hONE180 hK5180 hs180DI hSKlo180 hI180 hRlo180 hRhi180 g180S g180
  have hrun263 : runN s 263 = runN s180 83 := runN_add_eq s 180 83 263 (by decide)
  let s263 := runN s 263
  have hs263eq : s263 = runN s180 83 := hrun263
  have hs263pc : s263.pc = 1641 := by rw [hs263eq]; exact ht180.1
  have hs263h : s263.halted = false := by rw [hs263eq]; exact ht180.2.1
  have hs263Z : s263.mem.get 0 = 0 := by rw [hs263eq]; exact ht180.2.2.1
  have hs263B34 : s263.mem.get 34 = s.mem.get 22 := by
    rw [hs263eq, ht180.2.2.2.1, hQ22180]
  have hI263 : s263.mem.get 29 = 3 := by rw [hs263eq]; exact ht180.2.2.2.2.1
  have hs263DI : s263.mem.get 2321 = 3 := by rw [hs263eq]; exact ht180.2.2.2.2.2.1
  have hpres263 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s263.mem.get a = s.mem.get a := by
    intro a haB32 haB33 haB34 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs263eq]
    exact (ht180.2.2.2.2.2.2 a haB34 ha29 ha18 ha30 haR haDI ha0).trans (hpres180 a haB32 haB33 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs263B32 : s263.mem.get 32 = s.mem.get 20 := by
    rw [hs263eq]
    exact (ht180.2.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs180B32
  have hs263B33 : s263.mem.get 33 = s.mem.get 21 := by
    rw [hs263eq]
    exact (ht180.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs180B33
  have hONE263 : s263.mem.get 3 = 1 := (hpres263 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5263 : s263.mem.get 2322 = 5 := (hpres263 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs263SK : s263.mem.get 2320 = 0 := by
    rw [hs263eq]
    exact (ht180.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs180SK
  have hR263 : s263.mem.get 28 = s.mem.get 28 := hpres263 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ23263 : s263.mem.get 23 = s.mem.get 23 := hpres263 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24263 : s263.mem.get 24 = s.mem.get 24 := hpres263 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g263 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s263.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres263 (UInt16.ofNat k) n32 n33 n34 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo263 : (s263.mem.get 2320).toNat < 3 := by rw [hs263SK]; simp
  have g263S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s263.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres263 (UInt16.ofNat k) n32 n33 n34 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo263 : 3 < (s263.mem.get 28).toNat := by
    rw [hR263]
    have : 3 ≤ 4 := by decide
    omega
  have hRhi263 : (s263.mem.get 28).toNat < 32768 := by rw [hR263]; exact hRhi
  have ht263 := loop_take_gt_di3_idx3 (s := s263) hs263pc hs263h hs263Z hONE263 hK5263 hs263DI hSKlo263 hI263 hRlo263 hRhi263 g263S g263
  have hrun350 : runN s 350 = runN s263 87 := runN_add_eq s 263 87 350 (by decide)
  let s350 := runN s 350
  have hs350eq : s350 = runN s263 87 := hrun350
  have hs350pc : s350.pc = 1641 := by rw [hs350eq]; exact ht263.1
  have hs350h : s350.halted = false := by rw [hs350eq]; exact ht263.2.1
  have hs350Z : s350.mem.get 0 = 0 := by rw [hs350eq]; exact ht263.2.2.1
  have hs350B35 : s350.mem.get 35 = s.mem.get 23 := by
    rw [hs350eq, ht263.2.2.2.1, hQ23263]
  have hI350 : s350.mem.get 29 = 4 := by rw [hs350eq]; exact ht263.2.2.2.2.1
  have hs350DI : s350.mem.get 2321 = 4 := by rw [hs350eq]; exact ht263.2.2.2.2.2.1
  have hpres350 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s350.mem.get a = s.mem.get a := by
    intro a haB32 haB33 haB34 haB35 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs350eq]
    exact (ht263.2.2.2.2.2.2 a haB35 ha29 ha18 ha30 haR haDI ha0).trans (hpres263 a haB32 haB33 haB34 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs350B32 : s350.mem.get 32 = s.mem.get 20 := by
    rw [hs350eq]
    exact (ht263.2.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs263B32
  have hs350B33 : s350.mem.get 33 = s.mem.get 21 := by
    rw [hs350eq]
    exact (ht263.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs263B33
  have hs350B34 : s350.mem.get 34 = s.mem.get 22 := by
    rw [hs350eq]
    exact (ht263.2.2.2.2.2.2 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs263B34
  have hONE350 : s350.mem.get 3 = 1 := (hpres350 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5350 : s350.mem.get 2322 = 5 := (hpres350 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs350SK : s350.mem.get 2320 = 0 := by
    rw [hs350eq]
    exact (ht263.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs263SK
  have hR350 : s350.mem.get 28 = s.mem.get 28 := hpres350 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24350 : s350.mem.get 24 = s.mem.get 24 := hpres350 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g350 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s350.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres350 (UInt16.ofNat k) n32 n33 n34 n35 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo350 : (s350.mem.get 2320).toNat < 4 := by rw [hs350SK]; simp
  have g350S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s350.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres350 (UInt16.ofNat k) n32 n33 n34 n35 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo350 : 4 < (s350.mem.get 28).toNat := by
    rw [hR350]
    have : 4 ≤ 4 := by decide
    omega
  have hRhi350 : (s350.mem.get 28).toNat < 32768 := by rw [hR350]; exact hRhi
  have ht350 := loop_take_gt_di4_idx4 (s := s350) hs350pc hs350h hs350Z hONE350 hK5350 hs350DI hSKlo350 hI350 hRlo350 hRhi350 g350S g350
  have hrun439 : runN s 439 = runN s350 89 := runN_add_eq s 350 89 439 (by decide)
  let s439 := runN s 439
  have hs439eq : s439 = runN s350 89 := hrun439
  have hs439pc : s439.pc = 1641 := by rw [hs439eq]; exact ht350.1
  have hs439h : s439.halted = false := by rw [hs439eq]; exact ht350.2.1
  have hs439Z : s439.mem.get 0 = 0 := by rw [hs439eq]; exact ht350.2.2.1
  have hs439B36 : s439.mem.get 36 = s.mem.get 24 := by
    rw [hs439eq, ht350.2.2.2.1, hQ24350]
  have hI439 : s439.mem.get 29 = 5 := by rw [hs439eq]; exact ht350.2.2.2.2.1
  have hs439DI : s439.mem.get 2321 = 5 := by rw [hs439eq]; exact ht350.2.2.2.2.2.1
  have hpres439 : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s439.mem.get a = s.mem.get a := by
    intro a haB32 haB33 haB34 haB35 haB36 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs439eq]
    exact (ht350.2.2.2.2.2.2 a haB36 ha29 ha18 ha30 haR haDI ha0).trans (hpres350 a haB32 haB33 haB34 haB35 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs439B32 : s439.mem.get 32 = s.mem.get 20 := by
    rw [hs439eq]
    exact (ht350.2.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs350B32
  have hs439B33 : s439.mem.get 33 = s.mem.get 21 := by
    rw [hs439eq]
    exact (ht350.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs350B33
  have hs439B34 : s439.mem.get 34 = s.mem.get 22 := by
    rw [hs439eq]
    exact (ht350.2.2.2.2.2.2 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs350B34
  have hs439B35 : s439.mem.get 35 = s.mem.get 23 := by
    rw [hs439eq]
    exact (ht350.2.2.2.2.2.2 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs350B35
  have hONE439 : s439.mem.get 3 = 1 := (hpres439 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5439 : s439.mem.get 2322 = 5 := (hpres439 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs439SK : s439.mem.get 2320 = 0 := by
    rw [hs439eq]
    exact (ht350.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs350SK
  have hR439 : s439.mem.get 28 = s.mem.get 28 := hpres439 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g439 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s439.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres439 (UInt16.ofNat k) n32 n33 n34 n35 n36 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hONE439 : s439.mem.get 3 = 1 := (hpres439 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5439x : s439.mem.get 2322 = 5 := (hpres439 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have g439x : ∀ k : Nat, 1641 ≤ k → k < 1677 →
      s439.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
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
    exact (hpres439 (UInt16.ofNat k) n32 n33 n34 n35 n36 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hx := dig_loop_exit (s := s439) hs439pc hs439h hs439Z hONE439 hs439DI hK5439x g439x
  have hrun : s450 = runN s439 11 := runN_add_eq s 439 11 450 (by decide)
  have hsTpc : s450.pc = 1905 := by rw [hrun]; exact hx.1
  have hsTh : s450.halted = false := by rw [hrun]; exact hx.2.1
  have hsTZ : s450.mem.get 0 = 0 := by rw [hrun]; exact hx.2.2.1
  have hsTB32 : s450.mem.get 32 = s.mem.get 20 := by
    rw [hrun]; exact (hx.2.2.2.2 32 (by decide) (by decide)).trans hs439B32
  have hsTB33 : s450.mem.get 33 = s.mem.get 21 := by
    rw [hrun]; exact (hx.2.2.2.2 33 (by decide) (by decide)).trans hs439B33
  have hsTB34 : s450.mem.get 34 = s.mem.get 22 := by
    rw [hrun]; exact (hx.2.2.2.2 34 (by decide) (by decide)).trans hs439B34
  have hsTB35 : s450.mem.get 35 = s.mem.get 23 := by
    rw [hrun]; exact (hx.2.2.2.2 35 (by decide) (by decide)).trans hs439B35
  have hsTB36 : s450.mem.get 36 = s.mem.get 24 := by
    rw [hrun]; exact (hx.2.2.2.2 36 (by decide) (by decide)).trans hs439B36
  have hsTI : s450.mem.get 29 = 5 := by
    rw [hrun]; exact (hx.2.2.2.2 29 (by decide) (by decide)).trans hI439
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s450.mem.get a = s.mem.get a := by
    intro a haB32 haB33 haB34 haB35 haB36 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hrun]
    exact (hx.2.2.2.2 a ha18 ha0).trans (hpres439 a haB32 haB33 haB34 haB35 haB36 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB32, hsTB33, hsTB34, hsTB35, hsTB36, hsTI, hpres⟩


/-- From `EMIT_DIGS` with `NDIG = 5` and `IDX = 1 < ROOM`: write
`Q0`..`Q4` at `BUF+1`..`BUF+5` and reach `AFTER_DIGS`
with `IDX = 6`. 460 steps. -/
theorem emit_ndig5_idx1 {s : Machine}
    (hpc : s.pc = 1575)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hN : s.mem.get 25 = 5)
    (hI : s.mem.get 29 = 1)
    (hRlo : 5 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hcode : ∀ k : Nat, 1185 ≤ k → k < 1905 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let s460 := runN s 460
    s460.pc = 1905 ∧
    s460.halted = false ∧
    s460.mem.get 0 = 0 ∧
    s460.mem.get 33 = s.mem.get 20 ∧
    s460.mem.get 34 = s.mem.get 21 ∧
    s460.mem.get 35 = s.mem.get 22 ∧
    s460.mem.get 36 = s.mem.get 23 ∧
    s460.mem.get 37 = s.mem.get 24 ∧
    s460.mem.get 29 = 6 ∧
    (∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s460.mem.get a = s.mem.get a) := by
  intro s460
  have hNle : (s.mem.get 25).toNat ≤ 5 := by rw [hN]; simp
  have hp := emit_prelude (s := s) hpc hh hZ hONE hNle
    (fun k h1 h2 => hcode k (by omega) (by omega))
  let s22 := runN s 22
  have hs22pc : s22.pc = 1641 := hp.1
  have hs22h : s22.halted = false := hp.2.1
  have hs22Z : s22.mem.get 0 = 0 := hp.2.2.1
  have hs22SK : s22.mem.get 2320 = 0 := by
    rw [hp.2.2.2.1, hN]
    exact (rfl : (5 : Word) - 5 = 0)
  have hs22DI : s22.mem.get 2321 = 0 := hp.2.2.2.2.1
  have hpres22raw := hp.2.2.2.2.2.2
  have hpres22 : ∀ a, a ≠ 18 → a ≠ 31 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s22.mem.get a = s.mem.get a := by
    intro a ha18 ha31 haSK haDI ha0
    exact hpres22raw a ha31 haSK haDI ha0
  have hONE22 : s22.mem.get 3 = 1 := (hpres22 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK522 : s22.mem.get 2322 = 5 := (hpres22 2322 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hI22 : s22.mem.get 29 = 1 := (hpres22 29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hI
  have hR22 : s22.mem.get 28 = s.mem.get 28 := hpres22 28 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2022 : s22.mem.get 20 = s.mem.get 20 := hpres22 20 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2122 : s22.mem.get 21 = s.mem.get 21 := hpres22 21 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2222 : s22.mem.get 22 = s.mem.get 22 := hpres22 22 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2322 : s22.mem.get 23 = s.mem.get 23 := hpres22 23 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ2422 : s22.mem.get 24 = s.mem.get 24 := hpres22 24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have g22 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s22.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres22 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have g22S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s22.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n31 : UInt16.ofNat k ≠ (31 : Word) := by
      have : (31 : Word) = UInt16.ofNat 31 := rfl
      rw [this]; exact ofNat_ne k 31 (by omega) (by decide) (by omega)
    have n2320 : UInt16.ofNat k ≠ (2320 : Word) := by
      have : (2320 : Word) = UInt16.ofNat 2320 := rfl
      rw [this]; exact ofNat_ne k 2320 (by omega) (by decide) (by omega)
    have n2321 : UInt16.ofNat k ≠ (2321 : Word) := by
      have : (2321 : Word) = UInt16.ofNat 2321 := rfl
      rw [this]; exact ofNat_ne k 2321 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres22 (UInt16.ofNat k) n18 n31 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo22 : 1 < (s22.mem.get 28).toNat := by
    rw [hR22]
    have : 1 ≤ 5 := by decide
    omega
  have hRhi22 : (s22.mem.get 28).toNat < 32768 := by rw [hR22]; exact hRhi
  have ht22 := loop_take_eq_di0_idx1 (s := s22) hs22pc hs22h hs22Z hONE22 hK522 hs22DI hs22SK hI22 hRlo22 hRhi22 g22S g22
  have hrun103 : runN s 103 = runN s22 81 := runN_add_eq s 22 81 103 (by decide)
  let s103 := runN s 103
  have hs103eq : s103 = runN s22 81 := hrun103
  have hs103pc : s103.pc = 1641 := by rw [hs103eq]; exact ht22.1
  have hs103h : s103.halted = false := by rw [hs103eq]; exact ht22.2.1
  have hs103Z : s103.mem.get 0 = 0 := by rw [hs103eq]; exact ht22.2.2.1
  have hs103B33 : s103.mem.get 33 = s.mem.get 20 := by
    rw [hs103eq, ht22.2.2.2.1, hQ2022]
  have hI103 : s103.mem.get 29 = 2 := by rw [hs103eq]; exact ht22.2.2.2.2.1
  have hs103DI : s103.mem.get 2321 = 1 := by rw [hs103eq]; exact ht22.2.2.2.2.2.1
  have hpres103 : ∀ a, a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s103.mem.get a = s.mem.get a := by
    intro a haB ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs103eq]
    exact (ht22.2.2.2.2.2.2 a haB ha29 ha18 ha30 haR haDI ha0).trans (hpres22 a ha18 ha31 haSK haDI ha0)
  have hONE103 : s103.mem.get 3 = 1 := (hpres103 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5103 : s103.mem.get 2322 = 5 := (hpres103 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs103SK : s103.mem.get 2320 = 0 := by
    rw [hs103eq]
    exact (ht22.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs22SK
  have hR103 : s103.mem.get 28 = s.mem.get 28 := hpres103 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ21103 : s103.mem.get 21 = s.mem.get 21 := hpres103 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ22103 : s103.mem.get 22 = s.mem.get 22 := hpres103 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ23103 : s103.mem.get 23 = s.mem.get 23 := hpres103 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24103 : s103.mem.get 24 = s.mem.get 24 := hpres103 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g103 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s103.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
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
    exact (hpres103 (UInt16.ofNat k) n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo103 : (s103.mem.get 2320).toNat < 1 := by rw [hs103SK]; simp
  have g103S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s103.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
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
    exact (hpres103 (UInt16.ofNat k) n33 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo103 : 2 < (s103.mem.get 28).toNat := by
    rw [hR103]
    have : 2 ≤ 5 := by decide
    omega
  have hRhi103 : (s103.mem.get 28).toNat < 32768 := by rw [hR103]; exact hRhi
  have ht103 := loop_take_gt_di1_idx2 (s := s103) hs103pc hs103h hs103Z hONE103 hK5103 hs103DI hSKlo103 hI103 hRlo103 hRhi103 g103S g103
  have hrun184 : runN s 184 = runN s103 81 := runN_add_eq s 103 81 184 (by decide)
  let s184 := runN s 184
  have hs184eq : s184 = runN s103 81 := hrun184
  have hs184pc : s184.pc = 1641 := by rw [hs184eq]; exact ht103.1
  have hs184h : s184.halted = false := by rw [hs184eq]; exact ht103.2.1
  have hs184Z : s184.mem.get 0 = 0 := by rw [hs184eq]; exact ht103.2.2.1
  have hs184B34 : s184.mem.get 34 = s.mem.get 21 := by
    rw [hs184eq, ht103.2.2.2.1, hQ21103]
  have hI184 : s184.mem.get 29 = 3 := by rw [hs184eq]; exact ht103.2.2.2.2.1
  have hs184DI : s184.mem.get 2321 = 2 := by rw [hs184eq]; exact ht103.2.2.2.2.2.1
  have hpres184 : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s184.mem.get a = s.mem.get a := by
    intro a haB33 haB34 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs184eq]
    exact (ht103.2.2.2.2.2.2 a haB34 ha29 ha18 ha30 haR haDI ha0).trans (hpres103 a haB33 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs184B33 : s184.mem.get 33 = s.mem.get 20 := by
    rw [hs184eq]
    exact (ht103.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs103B33
  have hONE184 : s184.mem.get 3 = 1 := (hpres184 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5184 : s184.mem.get 2322 = 5 := (hpres184 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs184SK : s184.mem.get 2320 = 0 := by
    rw [hs184eq]
    exact (ht103.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs103SK
  have hR184 : s184.mem.get 28 = s.mem.get 28 := hpres184 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ22184 : s184.mem.get 22 = s.mem.get 22 := hpres184 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ23184 : s184.mem.get 23 = s.mem.get 23 := hpres184 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24184 : s184.mem.get 24 = s.mem.get 24 := hpres184 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g184 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s184.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
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
    exact (hpres184 (UInt16.ofNat k) n33 n34 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo184 : (s184.mem.get 2320).toNat < 2 := by rw [hs184SK]; simp
  have g184S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s184.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n33 : UInt16.ofNat k ≠ (33 : Word) := by
      have : (33 : Word) = UInt16.ofNat 33 := rfl
      rw [this]; exact ofNat_ne k 33 (by omega) (by decide) (by omega)
    have n34 : UInt16.ofNat k ≠ (34 : Word) := by
      have : (34 : Word) = UInt16.ofNat 34 := rfl
      rw [this]; exact ofNat_ne k 34 (by omega) (by decide) (by omega)
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
    exact (hpres184 (UInt16.ofNat k) n33 n34 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo184 : 3 < (s184.mem.get 28).toNat := by
    rw [hR184]
    have : 3 ≤ 5 := by decide
    omega
  have hRhi184 : (s184.mem.get 28).toNat < 32768 := by rw [hR184]; exact hRhi
  have ht184 := loop_take_gt_di2_idx3 (s := s184) hs184pc hs184h hs184Z hONE184 hK5184 hs184DI hSKlo184 hI184 hRlo184 hRhi184 g184S g184
  have hrun269 : runN s 269 = runN s184 85 := runN_add_eq s 184 85 269 (by decide)
  let s269 := runN s 269
  have hs269eq : s269 = runN s184 85 := hrun269
  have hs269pc : s269.pc = 1641 := by rw [hs269eq]; exact ht184.1
  have hs269h : s269.halted = false := by rw [hs269eq]; exact ht184.2.1
  have hs269Z : s269.mem.get 0 = 0 := by rw [hs269eq]; exact ht184.2.2.1
  have hs269B35 : s269.mem.get 35 = s.mem.get 22 := by
    rw [hs269eq, ht184.2.2.2.1, hQ22184]
  have hI269 : s269.mem.get 29 = 4 := by rw [hs269eq]; exact ht184.2.2.2.2.1
  have hs269DI : s269.mem.get 2321 = 3 := by rw [hs269eq]; exact ht184.2.2.2.2.2.1
  have hpres269 : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s269.mem.get a = s.mem.get a := by
    intro a haB33 haB34 haB35 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs269eq]
    exact (ht184.2.2.2.2.2.2 a haB35 ha29 ha18 ha30 haR haDI ha0).trans (hpres184 a haB33 haB34 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs269B33 : s269.mem.get 33 = s.mem.get 20 := by
    rw [hs269eq]
    exact (ht184.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs184B33
  have hs269B34 : s269.mem.get 34 = s.mem.get 21 := by
    rw [hs269eq]
    exact (ht184.2.2.2.2.2.2 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs184B34
  have hONE269 : s269.mem.get 3 = 1 := (hpres269 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5269 : s269.mem.get 2322 = 5 := (hpres269 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs269SK : s269.mem.get 2320 = 0 := by
    rw [hs269eq]
    exact (ht184.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs184SK
  have hR269 : s269.mem.get 28 = s.mem.get 28 := hpres269 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ23269 : s269.mem.get 23 = s.mem.get 23 := hpres269 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24269 : s269.mem.get 24 = s.mem.get 24 := hpres269 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g269 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s269.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
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
    exact (hpres269 (UInt16.ofNat k) n33 n34 n35 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo269 : (s269.mem.get 2320).toNat < 3 := by rw [hs269SK]; simp
  have g269S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s269.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
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
    exact (hpres269 (UInt16.ofNat k) n33 n34 n35 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo269 : 4 < (s269.mem.get 28).toNat := by
    rw [hR269]
    have : 4 ≤ 5 := by decide
    omega
  have hRhi269 : (s269.mem.get 28).toNat < 32768 := by rw [hR269]; exact hRhi
  have ht269 := loop_take_gt_di3_idx4 (s := s269) hs269pc hs269h hs269Z hONE269 hK5269 hs269DI hSKlo269 hI269 hRlo269 hRhi269 g269S g269
  have hrun358 : runN s 358 = runN s269 89 := runN_add_eq s 269 89 358 (by decide)
  let s358 := runN s 358
  have hs358eq : s358 = runN s269 89 := hrun358
  have hs358pc : s358.pc = 1641 := by rw [hs358eq]; exact ht269.1
  have hs358h : s358.halted = false := by rw [hs358eq]; exact ht269.2.1
  have hs358Z : s358.mem.get 0 = 0 := by rw [hs358eq]; exact ht269.2.2.1
  have hs358B36 : s358.mem.get 36 = s.mem.get 23 := by
    rw [hs358eq, ht269.2.2.2.1, hQ23269]
  have hI358 : s358.mem.get 29 = 5 := by rw [hs358eq]; exact ht269.2.2.2.2.1
  have hs358DI : s358.mem.get 2321 = 4 := by rw [hs358eq]; exact ht269.2.2.2.2.2.1
  have hpres358 : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s358.mem.get a = s.mem.get a := by
    intro a haB33 haB34 haB35 haB36 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs358eq]
    exact (ht269.2.2.2.2.2.2 a haB36 ha29 ha18 ha30 haR haDI ha0).trans (hpres269 a haB33 haB34 haB35 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs358B33 : s358.mem.get 33 = s.mem.get 20 := by
    rw [hs358eq]
    exact (ht269.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs269B33
  have hs358B34 : s358.mem.get 34 = s.mem.get 21 := by
    rw [hs358eq]
    exact (ht269.2.2.2.2.2.2 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs269B34
  have hs358B35 : s358.mem.get 35 = s.mem.get 22 := by
    rw [hs358eq]
    exact (ht269.2.2.2.2.2.2 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs269B35
  have hONE358 : s358.mem.get 3 = 1 := (hpres358 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5358 : s358.mem.get 2322 = 5 := (hpres358 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs358SK : s358.mem.get 2320 = 0 := by
    rw [hs358eq]
    exact (ht269.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs269SK
  have hR358 : s358.mem.get 28 = s.mem.get 28 := hpres358 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hQ24358 : s358.mem.get 24 = s.mem.get 24 := hpres358 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g358 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s358.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
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
    exact (hpres358 (UInt16.ofNat k) n33 n34 n35 n36 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hSKlo358 : (s358.mem.get 2320).toNat < 4 := by rw [hs358SK]; simp
  have g358S : ∀ k : Nat, 1185 ≤ k → k < 1575 →
      s358.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
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
    exact (hpres358 (UInt16.ofNat k) n33 n34 n35 n36 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hRlo358 : 5 < (s358.mem.get 28).toNat := by
    rw [hR358]
    have : 5 ≤ 5 := by decide
    omega
  have hRhi358 : (s358.mem.get 28).toNat < 32768 := by rw [hR358]; exact hRhi
  have ht358 := loop_take_gt_di4_idx5 (s := s358) hs358pc hs358h hs358Z hONE358 hK5358 hs358DI hSKlo358 hI358 hRlo358 hRhi358 g358S g358
  have hrun449 : runN s 449 = runN s358 91 := runN_add_eq s 358 91 449 (by decide)
  let s449 := runN s 449
  have hs449eq : s449 = runN s358 91 := hrun449
  have hs449pc : s449.pc = 1641 := by rw [hs449eq]; exact ht358.1
  have hs449h : s449.halted = false := by rw [hs449eq]; exact ht358.2.1
  have hs449Z : s449.mem.get 0 = 0 := by rw [hs449eq]; exact ht358.2.2.1
  have hs449B37 : s449.mem.get 37 = s.mem.get 24 := by
    rw [hs449eq, ht358.2.2.2.1, hQ24358]
  have hI449 : s449.mem.get 29 = 6 := by rw [hs449eq]; exact ht358.2.2.2.2.1
  have hs449DI : s449.mem.get 2321 = 5 := by rw [hs449eq]; exact ht358.2.2.2.2.2.1
  have hpres449 : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s449.mem.get a = s.mem.get a := by
    intro a haB33 haB34 haB35 haB36 haB37 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hs449eq]
    exact (ht358.2.2.2.2.2.2 a haB37 ha29 ha18 ha30 haR haDI ha0).trans (hpres358 a haB33 haB34 haB35 haB36 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  have hs449B33 : s449.mem.get 33 = s.mem.get 20 := by
    rw [hs449eq]
    exact (ht358.2.2.2.2.2.2 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs358B33
  have hs449B34 : s449.mem.get 34 = s.mem.get 21 := by
    rw [hs449eq]
    exact (ht358.2.2.2.2.2.2 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs358B34
  have hs449B35 : s449.mem.get 35 = s.mem.get 22 := by
    rw [hs449eq]
    exact (ht358.2.2.2.2.2.2 35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs358B35
  have hs449B36 : s449.mem.get 36 = s.mem.get 23 := by
    rw [hs449eq]
    exact (ht358.2.2.2.2.2.2 36 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs358B36
  have hONE449 : s449.mem.get 3 = 1 := (hpres449 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5449 : s449.mem.get 2322 = 5 := (hpres449 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hs449SK : s449.mem.get 2320 = 0 := by
    rw [hs449eq]
    exact (ht358.2.2.2.2.2.2 2320 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs358SK
  have hR449 : s449.mem.get 28 = s.mem.get 28 := hpres449 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g449 : ∀ k : Nat, 1641 ≤ k → k < 1905 →
      s449.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
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
    exact (hpres449 (UInt16.ofNat k) n33 n34 n35 n36 n37 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hONE449 : s449.mem.get 3 = 1 := (hpres449 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK5449x : s449.mem.get 2322 = 5 := (hpres449 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have g449x : ∀ k : Nat, 1641 ≤ k → k < 1677 →
      s449.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
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
    exact (hpres449 (UInt16.ofNat k) n33 n34 n35 n36 n37 n29 n18 n30 n31 n2319 n2320 n2321 n0).trans (hcode k (by omega) (by omega))
  have hx := dig_loop_exit (s := s449) hs449pc hs449h hs449Z hONE449 hs449DI hK5449x g449x
  have hrun : s460 = runN s449 11 := runN_add_eq s 449 11 460 (by decide)
  have hsTpc : s460.pc = 1905 := by rw [hrun]; exact hx.1
  have hsTh : s460.halted = false := by rw [hrun]; exact hx.2.1
  have hsTZ : s460.mem.get 0 = 0 := by rw [hrun]; exact hx.2.2.1
  have hsTB33 : s460.mem.get 33 = s.mem.get 20 := by
    rw [hrun]; exact (hx.2.2.2.2 33 (by decide) (by decide)).trans hs449B33
  have hsTB34 : s460.mem.get 34 = s.mem.get 21 := by
    rw [hrun]; exact (hx.2.2.2.2 34 (by decide) (by decide)).trans hs449B34
  have hsTB35 : s460.mem.get 35 = s.mem.get 22 := by
    rw [hrun]; exact (hx.2.2.2.2 35 (by decide) (by decide)).trans hs449B35
  have hsTB36 : s460.mem.get 36 = s.mem.get 23 := by
    rw [hrun]; exact (hx.2.2.2.2 36 (by decide) (by decide)).trans hs449B36
  have hsTB37 : s460.mem.get 37 = s.mem.get 24 := by
    rw [hrun]; exact (hx.2.2.2.2 37 (by decide) (by decide)).trans hs449B37
  have hsTI : s460.mem.get 29 = 6 := by
    rw [hrun]; exact (hx.2.2.2.2 29 (by decide) (by decide)).trans hI449
  have hpres : ∀ a, a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 →
      s460.mem.get a = s.mem.get a := by
    intro a haB33 haB34 haB35 haB36 haB37 ha29 ha18 ha30 ha31 haR haSK haDI ha0
    rw [hrun]
    exact (hx.2.2.2.2 a ha18 ha0).trans (hpres449 a haB33 haB34 haB35 haB36 haB37 ha29 ha18 ha30 ha31 haR haSK haDI ha0)
  exact ⟨hsTpc, hsTh, hsTZ, hsTB33, hsTB34, hsTB35, hsTB36, hsTB37, hsTI, hpres⟩

end IntFmt
