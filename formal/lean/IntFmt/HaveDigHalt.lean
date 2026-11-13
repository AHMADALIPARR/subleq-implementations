/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Compose `HAVE_DIG` / `AFTER_PAD` with `EMIT_DIGS` / `WRITE_NUL` / `DONE`.
Block lemmas, not an end-to-end theorem.
-/

import IntFmt.WriteNul

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000


/-- `AFTER_PAD` with `SIGN = 0`, `NDIG = 1`, `IDX = 0`, and `LEN = 1 < CAP`,
through `EMIT_DIGS` / `WRITE_NUL` / `DONE`. 254 steps. -/
theorem after_pad_sign0_ndig1_done {s : Machine}
    (hpc : s.pc = 1077)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hS : s.mem.get 19 = 0)
    (hN : s.mem.get 25 = 1)
    (hI : s.mem.get 29 = 0)
    (hL : s.mem.get 16 = 1)
    (hRlo : 0 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (1 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1077 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 254
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = s.mem.get 24 ∧
    sD.mem.get 33 = 0 ∧
    sD.mem.get 29 = 1 ∧
    sD.mem.get 16 = 1 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
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
  have hN6 : s6.mem.get 25 = 1 := (hpres6 25 (by decide) (by decide)).trans hN
  have hI6 : s6.mem.get 29 = 0 := (hpres6 29 (by decide) (by decide)).trans hI
  have hL6 : s6.mem.get 16 = 1 := (hpres6 16 (by decide) (by decide)).trans hL
  have hRlo6 : 0 < (s6.mem.get 28).toNat := by
    have hR6 : s6.mem.get 28 = s.mem.get 28 := hpres6 28 (by decide) (by decide)
    rw [hR6]; exact hRlo
  have hRhi6 : (s6.mem.get 28).toNat < 32768 := by
    have hR6 : s6.mem.get 28 = s.mem.get 28 := hpres6 28 (by decide) (by decide)
    rw [hR6]; exact hRhi
  have hLlt6 : (1 : Nat) < (s6.mem.get 13).toNat := by
    have : s6.mem.get 13 = s.mem.get 13 := hpres6 13 (by decide) (by decide)
    rw [this]; exact hLlt
  have hChi6 : (s6.mem.get 13).toNat < 32768 := by
    have : s6.mem.get 13 = s.mem.get 13 := hpres6 13 (by decide) (by decide)
    rw [this]; exact hChi
  have g6 : ∀ k : Nat, 1185 ≤ k → k < 2319 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hw := emit_ndig1_idx0_write_nul_done (s := s6) hs6pc hs6h hs6Z hONE6 hK56 hN6 hI6 hL6
    hRlo6 hRhi6 hLlt6 hChi6 g6
  have hrun : sD = runN s6 248 := runN_add_eq s 6 248 254 (by decide)
  have hsD32 : sD.mem.get 32 = s.mem.get 24 := by
    rw [hrun]; exact (hw.2.2.2.1).trans (hpres6 24 (by decide) (by decide))
  -- Q cells are preserved by after_pad_sign0 (pres ≠18 ≠0)
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDNUL : sD.mem.get 33 = 0 := by rw [hrun]; exact hw.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 1 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 1 := by rw [hrun]; exact hw.2.2.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha32 ha33 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpres6 a (by exact ha18) (by exact ha0))
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsDNUL, hsDI, hsDL, hpres⟩

/-- `AFTER_PAD` with `SIGN = 0`, `NDIG = 2`, `IDX = 0`, and `LEN = 2 < CAP`,
through `EMIT_DIGS` / `WRITE_NUL` / `DONE`. 314 steps. -/
theorem after_pad_sign0_ndig2_done {s : Machine}
    (hpc : s.pc = 1077)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hS : s.mem.get 19 = 0)
    (hN : s.mem.get 25 = 2)
    (hI : s.mem.get 29 = 0)
    (hL : s.mem.get 16 = 2)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (2 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1077 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 314
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = s.mem.get 23 ∧
    sD.mem.get 33 = s.mem.get 24 ∧
    sD.mem.get 34 = 0 ∧
    sD.mem.get 29 = 2 ∧
    sD.mem.get 16 = 2 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
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
  have hN6 : s6.mem.get 25 = 2 := (hpres6 25 (by decide) (by decide)).trans hN
  have hI6 : s6.mem.get 29 = 0 := (hpres6 29 (by decide) (by decide)).trans hI
  have hL6 : s6.mem.get 16 = 2 := (hpres6 16 (by decide) (by decide)).trans hL
  have hRlo6 : 1 < (s6.mem.get 28).toNat := by
    have hR6 : s6.mem.get 28 = s.mem.get 28 := hpres6 28 (by decide) (by decide)
    rw [hR6]; exact hRlo
  have hRhi6 : (s6.mem.get 28).toNat < 32768 := by
    have hR6 : s6.mem.get 28 = s.mem.get 28 := hpres6 28 (by decide) (by decide)
    rw [hR6]; exact hRhi
  have hLlt6 : (2 : Nat) < (s6.mem.get 13).toNat := by
    have : s6.mem.get 13 = s.mem.get 13 := hpres6 13 (by decide) (by decide)
    rw [this]; exact hLlt
  have hChi6 : (s6.mem.get 13).toNat < 32768 := by
    have : s6.mem.get 13 = s.mem.get 13 := hpres6 13 (by decide) (by decide)
    rw [this]; exact hChi
  have g6 : ∀ k : Nat, 1185 ≤ k → k < 2319 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hw := emit_ndig2_idx0_write_nul_done (s := s6) hs6pc hs6h hs6Z hONE6 hK56 hN6 hI6 hL6
    hRlo6 hRhi6 hLlt6 hChi6 g6
  have hrun : sD = runN s6 308 := runN_add_eq s 6 308 314 (by decide)
  have hsD32 : sD.mem.get 32 = s.mem.get 23 := by
    rw [hrun]; exact (hw.2.2.2.1).trans (hpres6 23 (by decide) (by decide))
  have hsD33 : sD.mem.get 33 = s.mem.get 24 := by
    rw [hrun]; exact (hw.2.2.2.2.1).trans (hpres6 24 (by decide) (by decide))
  -- Q cells are preserved by after_pad_sign0 (pres ≠18 ≠0)
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDNUL : sD.mem.get 34 = 0 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 2 := by rw [hrun]; exact hw.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 2 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpres6 a (by exact ha18) (by exact ha0))
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsDNUL, hsDI, hsDL, hpres⟩

/-- `AFTER_PAD` with `SIGN = 0`, `NDIG = 3`, `IDX = 0`, and `LEN = 3 < CAP`,
through `EMIT_DIGS` / `WRITE_NUL` / `DONE`. 374 steps. -/
theorem after_pad_sign0_ndig3_done {s : Machine}
    (hpc : s.pc = 1077)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hS : s.mem.get 19 = 0)
    (hN : s.mem.get 25 = 3)
    (hI : s.mem.get 29 = 0)
    (hL : s.mem.get 16 = 3)
    (hRlo : 2 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (3 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1077 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 374
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = s.mem.get 22 ∧
    sD.mem.get 33 = s.mem.get 23 ∧
    sD.mem.get 34 = s.mem.get 24 ∧
    sD.mem.get 35 = 0 ∧
    sD.mem.get 29 = 3 ∧
    sD.mem.get 16 = 3 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
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
  have hN6 : s6.mem.get 25 = 3 := (hpres6 25 (by decide) (by decide)).trans hN
  have hI6 : s6.mem.get 29 = 0 := (hpres6 29 (by decide) (by decide)).trans hI
  have hL6 : s6.mem.get 16 = 3 := (hpres6 16 (by decide) (by decide)).trans hL
  have hRlo6 : 2 < (s6.mem.get 28).toNat := by
    have hR6 : s6.mem.get 28 = s.mem.get 28 := hpres6 28 (by decide) (by decide)
    rw [hR6]; exact hRlo
  have hRhi6 : (s6.mem.get 28).toNat < 32768 := by
    have hR6 : s6.mem.get 28 = s.mem.get 28 := hpres6 28 (by decide) (by decide)
    rw [hR6]; exact hRhi
  have hLlt6 : (3 : Nat) < (s6.mem.get 13).toNat := by
    have : s6.mem.get 13 = s.mem.get 13 := hpres6 13 (by decide) (by decide)
    rw [this]; exact hLlt
  have hChi6 : (s6.mem.get 13).toNat < 32768 := by
    have : s6.mem.get 13 = s.mem.get 13 := hpres6 13 (by decide) (by decide)
    rw [this]; exact hChi
  have g6 : ∀ k : Nat, 1185 ≤ k → k < 2319 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hw := emit_ndig3_idx0_write_nul_done (s := s6) hs6pc hs6h hs6Z hONE6 hK56 hN6 hI6 hL6
    hRlo6 hRhi6 hLlt6 hChi6 g6
  have hrun : sD = runN s6 368 := runN_add_eq s 6 368 374 (by decide)
  have hsD32 : sD.mem.get 32 = s.mem.get 22 := by
    rw [hrun]; exact (hw.2.2.2.1).trans (hpres6 22 (by decide) (by decide))
  have hsD33 : sD.mem.get 33 = s.mem.get 23 := by
    rw [hrun]; exact (hw.2.2.2.2.1).trans (hpres6 23 (by decide) (by decide))
  have hsD34 : sD.mem.get 34 = s.mem.get 24 := by
    rw [hrun]; exact (hw.2.2.2.2.2.1).trans (hpres6 24 (by decide) (by decide))
  -- Q cells are preserved by after_pad_sign0 (pres ≠18 ≠0)
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDNUL : sD.mem.get 35 = 0 := by rw [hrun]; exact hw.2.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 3 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 3 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha35 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpres6 a (by exact ha18) (by exact ha0))
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsDNUL, hsDI, hsDL, hpres⟩

/-- `AFTER_PAD` with `SIGN = 0`, `NDIG = 4`, `IDX = 0`, and `LEN = 4 < CAP`,
through `EMIT_DIGS` / `WRITE_NUL` / `DONE`. 434 steps. -/
theorem after_pad_sign0_ndig4_done {s : Machine}
    (hpc : s.pc = 1077)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hS : s.mem.get 19 = 0)
    (hN : s.mem.get 25 = 4)
    (hI : s.mem.get 29 = 0)
    (hL : s.mem.get 16 = 4)
    (hRlo : 3 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (4 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1077 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 434
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = s.mem.get 21 ∧
    sD.mem.get 33 = s.mem.get 22 ∧
    sD.mem.get 34 = s.mem.get 23 ∧
    sD.mem.get 35 = s.mem.get 24 ∧
    sD.mem.get 36 = 0 ∧
    sD.mem.get 29 = 4 ∧
    sD.mem.get 16 = 4 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
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
  have hN6 : s6.mem.get 25 = 4 := (hpres6 25 (by decide) (by decide)).trans hN
  have hI6 : s6.mem.get 29 = 0 := (hpres6 29 (by decide) (by decide)).trans hI
  have hL6 : s6.mem.get 16 = 4 := (hpres6 16 (by decide) (by decide)).trans hL
  have hRlo6 : 3 < (s6.mem.get 28).toNat := by
    have hR6 : s6.mem.get 28 = s.mem.get 28 := hpres6 28 (by decide) (by decide)
    rw [hR6]; exact hRlo
  have hRhi6 : (s6.mem.get 28).toNat < 32768 := by
    have hR6 : s6.mem.get 28 = s.mem.get 28 := hpres6 28 (by decide) (by decide)
    rw [hR6]; exact hRhi
  have hLlt6 : (4 : Nat) < (s6.mem.get 13).toNat := by
    have : s6.mem.get 13 = s.mem.get 13 := hpres6 13 (by decide) (by decide)
    rw [this]; exact hLlt
  have hChi6 : (s6.mem.get 13).toNat < 32768 := by
    have : s6.mem.get 13 = s.mem.get 13 := hpres6 13 (by decide) (by decide)
    rw [this]; exact hChi
  have g6 : ∀ k : Nat, 1185 ≤ k → k < 2319 →
      s6.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    exact (hpres6 (UInt16.ofNat k) n18 n0).trans (hcode k (by omega) (by omega))
  have hw := emit_ndig4_idx0_write_nul_done (s := s6) hs6pc hs6h hs6Z hONE6 hK56 hN6 hI6 hL6
    hRlo6 hRhi6 hLlt6 hChi6 g6
  have hrun : sD = runN s6 428 := runN_add_eq s 6 428 434 (by decide)
  have hsD32 : sD.mem.get 32 = s.mem.get 21 := by
    rw [hrun]; exact (hw.2.2.2.1).trans (hpres6 21 (by decide) (by decide))
  have hsD33 : sD.mem.get 33 = s.mem.get 22 := by
    rw [hrun]; exact (hw.2.2.2.2.1).trans (hpres6 22 (by decide) (by decide))
  have hsD34 : sD.mem.get 34 = s.mem.get 23 := by
    rw [hrun]; exact (hw.2.2.2.2.2.1).trans (hpres6 23 (by decide) (by decide))
  have hsD35 : sD.mem.get 35 = s.mem.get 24 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2.1).trans (hpres6 24 (by decide) (by decide))
  -- Q cells are preserved by after_pad_sign0 (pres ≠18 ≠0)
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDNUL : sD.mem.get 36 = 0 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 4 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 4 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha35 ha36 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpres6 a (by exact ha18) (by exact ha0))
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsD35, hsDNUL, hsDI, hsDL, hpres⟩

/-- `AFTER_PAD` with `SIGN = 0`, `NDIG = 5`, `IDX = 0`, and `LEN = 5 < CAP`,
through `EMIT_DIGS` / `WRITE_NUL` / `DONE`. 496 steps. -/
theorem have_dig_unsigned_ndig1_done {s : Machine}
    (hpc : s.pc = 867)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hS : s.mem.get 19 = 0)
    (hW : s.mem.get 14 = 0)
    (hN : s.mem.get 25 = 1)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (1 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 867 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 289
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = s.mem.get 24 ∧
    sD.mem.get 33 = 0 ∧
    sD.mem.get 29 = 1 ∧
    sD.mem.get 16 = 1 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hd := have_dig_to_after_pad_unsigned (s := s) hpc hh hZ hONE hS hW hClo hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s35 := runN s 35
  have hs35pc : s35.pc = 1077 := hd.1
  have hs35h : s35.halted = false := hd.2.1
  have hs35Z : s35.mem.get 0 = 0 := hd.2.2.1
  have hpres35 := hd.2.2.2.2.2.2.2.2
  have hL35 : s35.mem.get 16 = 1 := hd.2.2.2.2.1.trans hN
  have hI35 : s35.mem.get 29 = 0 := hd.2.2.2.2.2.2.2.1
  have hR35 : s35.mem.get 28 = s.mem.get 13 - 1 := hd.2.2.2.2.2.2.1
  have hONE35 : s35.mem.get 3 = 1 := (hpres35 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK535 : s35.mem.get 2322 = 5 := (hpres35 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hS35 : s35.mem.get 19 = 0 := (hpres35 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hS
  have hN35 : s35.mem.get 25 = 1 := (hpres35 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN
  have h1le : (1 : Nat) ≤ (s.mem.get 13).toNat := Nat.succ_le_of_lt hClo
  have hRtn : (s.mem.get 13 - 1).toNat = (s.mem.get 13).toNat - 1 :=
    word_sub_ge (s.mem.get 13) 1 (by
      have : (1 : Word).toNat = 1 := rfl
      exact this.symm ▸ h1le)
  have hRlo35 : 0 < (s35.mem.get 28).toNat := by
    rw [hR35, hRtn]
    omega
  have hRhi35 : (s35.mem.get 28).toNat < 32768 := by
    rw [hR35, hRtn]; omega
  have hLlt35 : (1 : Nat) < (s35.mem.get 13).toNat := by
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
    exact (hpres35 (UInt16.ofNat k) n26 n18 n16 n27 n28 n29 n0).trans (hcode k (by omega) (by omega))
  have hw := after_pad_sign0_ndig1_done (s := s35) hs35pc hs35h hs35Z hONE35 hK535 hS35 hN35 hI35 hL35
    hRlo35 hRhi35 hLlt35 hChi35 g35
  have hrun : sD = runN s35 254 := runN_add_eq s 35 254 289 (by decide)
  have hsD32 : sD.mem.get 32 = s.mem.get 24 := by
    rw [hrun]; exact (hw.2.2.2.1).trans (hpres35 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDNUL : sD.mem.get 33 = 0 := by rw [hrun]; exact hw.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 1 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 1 := by rw [hrun]; exact hw.2.2.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha32 ha33 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpres35 a ha26 ha18 ha16 ha27 ha28 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsDNUL, hsDI, hsDL, hpres⟩

/-- `HAVE_DIG` with `SIGN = 0`, `WIDTH = 0`, `NDIG = 2`, and `2 < CAP`,
through padding, `EMIT_DIGS`, `WRITE_NUL`, and `DONE`. 349 steps. -/
theorem have_dig_unsigned_ndig2_done {s : Machine}
    (hpc : s.pc = 867)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hS : s.mem.get 19 = 0)
    (hW : s.mem.get 14 = 0)
    (hN : s.mem.get 25 = 2)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (2 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 867 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 349
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = s.mem.get 23 ∧
    sD.mem.get 33 = s.mem.get 24 ∧
    sD.mem.get 34 = 0 ∧
    sD.mem.get 29 = 2 ∧
    sD.mem.get 16 = 2 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hd := have_dig_to_after_pad_unsigned (s := s) hpc hh hZ hONE hS hW hClo hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s35 := runN s 35
  have hs35pc : s35.pc = 1077 := hd.1
  have hs35h : s35.halted = false := hd.2.1
  have hs35Z : s35.mem.get 0 = 0 := hd.2.2.1
  have hpres35 := hd.2.2.2.2.2.2.2.2
  have hL35 : s35.mem.get 16 = 2 := hd.2.2.2.2.1.trans hN
  have hI35 : s35.mem.get 29 = 0 := hd.2.2.2.2.2.2.2.1
  have hR35 : s35.mem.get 28 = s.mem.get 13 - 1 := hd.2.2.2.2.2.2.1
  have hONE35 : s35.mem.get 3 = 1 := (hpres35 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK535 : s35.mem.get 2322 = 5 := (hpres35 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hS35 : s35.mem.get 19 = 0 := (hpres35 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hS
  have hN35 : s35.mem.get 25 = 2 := (hpres35 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN
  have h1le : (1 : Nat) ≤ (s.mem.get 13).toNat := Nat.succ_le_of_lt hClo
  have hRtn : (s.mem.get 13 - 1).toNat = (s.mem.get 13).toNat - 1 :=
    word_sub_ge (s.mem.get 13) 1 (by
      have : (1 : Word).toNat = 1 := rfl
      exact this.symm ▸ h1le)
  have hRlo35 : 1 < (s35.mem.get 28).toNat := by
    rw [hR35, hRtn]
    omega
  have hRhi35 : (s35.mem.get 28).toNat < 32768 := by
    rw [hR35, hRtn]; omega
  have hLlt35 : (2 : Nat) < (s35.mem.get 13).toNat := by
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
    exact (hpres35 (UInt16.ofNat k) n26 n18 n16 n27 n28 n29 n0).trans (hcode k (by omega) (by omega))
  have hw := after_pad_sign0_ndig2_done (s := s35) hs35pc hs35h hs35Z hONE35 hK535 hS35 hN35 hI35 hL35
    hRlo35 hRhi35 hLlt35 hChi35 g35
  have hrun : sD = runN s35 314 := runN_add_eq s 35 314 349 (by decide)
  have hsD32 : sD.mem.get 32 = s.mem.get 23 := by
    rw [hrun]; exact (hw.2.2.2.1).trans (hpres35 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD33 : sD.mem.get 33 = s.mem.get 24 := by
    rw [hrun]; exact (hw.2.2.2.2.1).trans (hpres35 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDNUL : sD.mem.get 34 = 0 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 2 := by rw [hrun]; exact hw.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 2 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpres35 a ha26 ha18 ha16 ha27 ha28 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsDNUL, hsDI, hsDL, hpres⟩

/-- `HAVE_DIG` with `SIGN = 0`, `WIDTH = 0`, `NDIG = 3`, and `3 < CAP`,
through padding, `EMIT_DIGS`, `WRITE_NUL`, and `DONE`. 409 steps. -/
theorem have_dig_unsigned_ndig3_done {s : Machine}
    (hpc : s.pc = 867)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hS : s.mem.get 19 = 0)
    (hW : s.mem.get 14 = 0)
    (hN : s.mem.get 25 = 3)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (3 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 867 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 409
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = s.mem.get 22 ∧
    sD.mem.get 33 = s.mem.get 23 ∧
    sD.mem.get 34 = s.mem.get 24 ∧
    sD.mem.get 35 = 0 ∧
    sD.mem.get 29 = 3 ∧
    sD.mem.get 16 = 3 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hd := have_dig_to_after_pad_unsigned (s := s) hpc hh hZ hONE hS hW hClo hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s35 := runN s 35
  have hs35pc : s35.pc = 1077 := hd.1
  have hs35h : s35.halted = false := hd.2.1
  have hs35Z : s35.mem.get 0 = 0 := hd.2.2.1
  have hpres35 := hd.2.2.2.2.2.2.2.2
  have hL35 : s35.mem.get 16 = 3 := hd.2.2.2.2.1.trans hN
  have hI35 : s35.mem.get 29 = 0 := hd.2.2.2.2.2.2.2.1
  have hR35 : s35.mem.get 28 = s.mem.get 13 - 1 := hd.2.2.2.2.2.2.1
  have hONE35 : s35.mem.get 3 = 1 := (hpres35 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK535 : s35.mem.get 2322 = 5 := (hpres35 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hS35 : s35.mem.get 19 = 0 := (hpres35 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hS
  have hN35 : s35.mem.get 25 = 3 := (hpres35 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN
  have h1le : (1 : Nat) ≤ (s.mem.get 13).toNat := Nat.succ_le_of_lt hClo
  have hRtn : (s.mem.get 13 - 1).toNat = (s.mem.get 13).toNat - 1 :=
    word_sub_ge (s.mem.get 13) 1 (by
      have : (1 : Word).toNat = 1 := rfl
      exact this.symm ▸ h1le)
  have hRlo35 : 2 < (s35.mem.get 28).toNat := by
    rw [hR35, hRtn]
    omega
  have hRhi35 : (s35.mem.get 28).toNat < 32768 := by
    rw [hR35, hRtn]; omega
  have hLlt35 : (3 : Nat) < (s35.mem.get 13).toNat := by
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
    exact (hpres35 (UInt16.ofNat k) n26 n18 n16 n27 n28 n29 n0).trans (hcode k (by omega) (by omega))
  have hw := after_pad_sign0_ndig3_done (s := s35) hs35pc hs35h hs35Z hONE35 hK535 hS35 hN35 hI35 hL35
    hRlo35 hRhi35 hLlt35 hChi35 g35
  have hrun : sD = runN s35 374 := runN_add_eq s 35 374 409 (by decide)
  have hsD32 : sD.mem.get 32 = s.mem.get 22 := by
    rw [hrun]; exact (hw.2.2.2.1).trans (hpres35 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD33 : sD.mem.get 33 = s.mem.get 23 := by
    rw [hrun]; exact (hw.2.2.2.2.1).trans (hpres35 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD34 : sD.mem.get 34 = s.mem.get 24 := by
    rw [hrun]; exact (hw.2.2.2.2.2.1).trans (hpres35 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDNUL : sD.mem.get 35 = 0 := by rw [hrun]; exact hw.2.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 3 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 3 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha35 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpres35 a ha26 ha18 ha16 ha27 ha28 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsDNUL, hsDI, hsDL, hpres⟩

/-- `HAVE_DIG` with `SIGN = 0`, `WIDTH = 0`, `NDIG = 4`, and `4 < CAP`,
through padding, `EMIT_DIGS`, `WRITE_NUL`, and `DONE`. 469 steps. -/
theorem have_dig_unsigned_ndig4_done {s : Machine}
    (hpc : s.pc = 867)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hS : s.mem.get 19 = 0)
    (hW : s.mem.get 14 = 0)
    (hN : s.mem.get 25 = 4)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (4 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 867 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 469
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = s.mem.get 21 ∧
    sD.mem.get 33 = s.mem.get 22 ∧
    sD.mem.get 34 = s.mem.get 23 ∧
    sD.mem.get 35 = s.mem.get 24 ∧
    sD.mem.get 36 = 0 ∧
    sD.mem.get 29 = 4 ∧
    sD.mem.get 16 = 4 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hd := have_dig_to_after_pad_unsigned (s := s) hpc hh hZ hONE hS hW hClo hChi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s35 := runN s 35
  have hs35pc : s35.pc = 1077 := hd.1
  have hs35h : s35.halted = false := hd.2.1
  have hs35Z : s35.mem.get 0 = 0 := hd.2.2.1
  have hpres35 := hd.2.2.2.2.2.2.2.2
  have hL35 : s35.mem.get 16 = 4 := hd.2.2.2.2.1.trans hN
  have hI35 : s35.mem.get 29 = 0 := hd.2.2.2.2.2.2.2.1
  have hR35 : s35.mem.get 28 = s.mem.get 13 - 1 := hd.2.2.2.2.2.2.1
  have hONE35 : s35.mem.get 3 = 1 := (hpres35 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK535 : s35.mem.get 2322 = 5 := (hpres35 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hS35 : s35.mem.get 19 = 0 := (hpres35 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hS
  have hN35 : s35.mem.get 25 = 4 := (hpres35 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN
  have h1le : (1 : Nat) ≤ (s.mem.get 13).toNat := Nat.succ_le_of_lt hClo
  have hRtn : (s.mem.get 13 - 1).toNat = (s.mem.get 13).toNat - 1 :=
    word_sub_ge (s.mem.get 13) 1 (by
      have : (1 : Word).toNat = 1 := rfl
      exact this.symm ▸ h1le)
  have hRlo35 : 3 < (s35.mem.get 28).toNat := by
    rw [hR35, hRtn]
    omega
  have hRhi35 : (s35.mem.get 28).toNat < 32768 := by
    rw [hR35, hRtn]; omega
  have hLlt35 : (4 : Nat) < (s35.mem.get 13).toNat := by
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
    exact (hpres35 (UInt16.ofNat k) n26 n18 n16 n27 n28 n29 n0).trans (hcode k (by omega) (by omega))
  have hw := after_pad_sign0_ndig4_done (s := s35) hs35pc hs35h hs35Z hONE35 hK535 hS35 hN35 hI35 hL35
    hRlo35 hRhi35 hLlt35 hChi35 g35
  have hrun : sD = runN s35 434 := runN_add_eq s 35 434 469 (by decide)
  have hsD32 : sD.mem.get 32 = s.mem.get 21 := by
    rw [hrun]; exact (hw.2.2.2.1).trans (hpres35 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD33 : sD.mem.get 33 = s.mem.get 22 := by
    rw [hrun]; exact (hw.2.2.2.2.1).trans (hpres35 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD34 : sD.mem.get 34 = s.mem.get 23 := by
    rw [hrun]; exact (hw.2.2.2.2.2.1).trans (hpres35 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD35 : sD.mem.get 35 = s.mem.get 24 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2.1).trans (hpres35 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDNUL : sD.mem.get 36 = 0 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 4 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 4 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha35 ha36 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpres35 a ha26 ha18 ha16 ha27 ha28 ha29 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsD35, hsDNUL, hsDI, hsDL, hpres⟩

/-- `HAVE_DIG` with `SIGN = 0`, `WIDTH = 0`, `NDIG = 5`, and `5 < CAP`,
through padding, `EMIT_DIGS`, `WRITE_NUL`, and `DONE`. 531 steps. -/
theorem after_pad_minus_ndig1_done {s : Machine}
    (hpc : s.pc = 1077)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hK45 : s.mem.get 9 = 45)
    (hN : s.mem.get 25 = 1)
    (hI : s.mem.get 29 = 0)
    (hL : s.mem.get 16 = 2)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hRlo0 : 0 < (s.mem.get 28).toNat)
    (hRlo : 1 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (2 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1077 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 303
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = 45 ∧
    sD.mem.get 33 = s.mem.get 24 ∧
    sD.mem.get 34 = 0 ∧
    sD.mem.get 29 = 2 ∧
    sD.mem.get 16 = 2 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hm := after_pad_minus_to_emit_idx0 (s := s) hpc hh hZ hONE hK45 hI hSlo hShi hRlo0 hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s51 := runN s 51
  have hs51pc : s51.pc = 1575 := hm.1
  have hs51h : s51.halted = false := hm.2.1
  have hs51Z : s51.mem.get 0 = 0 := hm.2.2.1
  have hs51B0 : s51.mem.get 32 = 45 := hm.2.2.2.1
  have hs51I : s51.mem.get 29 = 1 := hm.2.2.2.2.1
  have hpres51 := hm.2.2.2.2.2
  have hONE51 : s51.mem.get 3 = 1 := (hpres51 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK551 : s51.mem.get 2322 = 5 := (hpres51 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hN51 : s51.mem.get 25 = 1 := (hpres51 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN
  have hL51 : s51.mem.get 16 = 2 := (hpres51 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL
  have hRlo51 : 1 < (s51.mem.get 28).toNat := by
    have : s51.mem.get 28 = s.mem.get 28 := hpres51 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRlo
  have hRhi51 : (s51.mem.get 28).toNat < 32768 := by
    have : s51.mem.get 28 = s.mem.get 28 := hpres51 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have hLlt51 : (2 : Nat) < (s51.mem.get 13).toNat := by
    have : s51.mem.get 13 = s.mem.get 13 := hpres51 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hLlt
  have hChi51 : (s51.mem.get 13).toNat < 32768 := by
    have : s51.mem.get 13 = s.mem.get 13 := hpres51 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hChi
  have g51 : ∀ k : Nat, 1185 ≤ k → k < 2319 →
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
    exact (hpres51 (UInt16.ofNat k) n32 n29 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hw := emit_ndig1_idx1_write_nul_done (s := s51) hs51pc hs51h hs51Z hONE51 hK551 hN51 hs51I hL51
    hRlo51 hRhi51 hLlt51 hChi51 g51
  have hrun : sD = runN s51 252 := runN_add_eq s 51 252 303 (by decide)
  have hsDB0 : sD.mem.get 32 = 45 := by
    rw [hrun]
    exact (hw.2.2.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs51B0
  have hsD33 : sD.mem.get 33 = s.mem.get 24 := by
    rw [hrun]; exact (hw.2.2.2.1).trans (hpres51 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDNUL : sD.mem.get 34 = 0 := by rw [hrun]; exact hw.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 2 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 2 := by rw [hrun]; exact hw.2.2.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha33 ha34 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpres51 a ha32 ha29 ha18 ha30 ha2319 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsDB0, hsD33, hsDNUL, hsDI, hsDL, hpres⟩

/-- `AFTER_PAD` with `SIGN ≠ 0`, `NDIG = 2`, `IDX = 0 < ROOM`, and `LEN = 3 < CAP`,
writes `'-'` then digits and a NUL, and halts. 365 steps. -/
theorem after_pad_minus_ndig2_done {s : Machine}
    (hpc : s.pc = 1077)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hK45 : s.mem.get 9 = 45)
    (hN : s.mem.get 25 = 2)
    (hI : s.mem.get 29 = 0)
    (hL : s.mem.get 16 = 3)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hRlo0 : 0 < (s.mem.get 28).toNat)
    (hRlo : 2 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (3 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1077 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 365
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
    sD.mem.get 32 = 45 ∧
    sD.mem.get 33 = s.mem.get 23 ∧
    sD.mem.get 34 = s.mem.get 24 ∧
    sD.mem.get 35 = 0 ∧
    sD.mem.get 29 = 3 ∧
    sD.mem.get 16 = 3 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hm := after_pad_minus_to_emit_idx0 (s := s) hpc hh hZ hONE hK45 hI hSlo hShi hRlo0 hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s51 := runN s 51
  have hs51pc : s51.pc = 1575 := hm.1
  have hs51h : s51.halted = false := hm.2.1
  have hs51Z : s51.mem.get 0 = 0 := hm.2.2.1
  have hs51B0 : s51.mem.get 32 = 45 := hm.2.2.2.1
  have hs51I : s51.mem.get 29 = 1 := hm.2.2.2.2.1
  have hpres51 := hm.2.2.2.2.2
  have hONE51 : s51.mem.get 3 = 1 := (hpres51 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK551 : s51.mem.get 2322 = 5 := (hpres51 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hN51 : s51.mem.get 25 = 2 := (hpres51 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN
  have hL51 : s51.mem.get 16 = 3 := (hpres51 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL
  have hRlo51 : 2 < (s51.mem.get 28).toNat := by
    have : s51.mem.get 28 = s.mem.get 28 := hpres51 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRlo
  have hRhi51 : (s51.mem.get 28).toNat < 32768 := by
    have : s51.mem.get 28 = s.mem.get 28 := hpres51 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have hLlt51 : (3 : Nat) < (s51.mem.get 13).toNat := by
    have : s51.mem.get 13 = s.mem.get 13 := hpres51 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hLlt
  have hChi51 : (s51.mem.get 13).toNat < 32768 := by
    have : s51.mem.get 13 = s.mem.get 13 := hpres51 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hChi
  have g51 : ∀ k : Nat, 1185 ≤ k → k < 2319 →
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
    exact (hpres51 (UInt16.ofNat k) n32 n29 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hw := emit_ndig2_idx1_write_nul_done (s := s51) hs51pc hs51h hs51Z hONE51 hK551 hN51 hs51I hL51
    hRlo51 hRhi51 hLlt51 hChi51 g51
  have hrun : sD = runN s51 314 := runN_add_eq s 51 314 365 (by decide)
  have hsDB0 : sD.mem.get 32 = 45 := by
    rw [hrun]
    exact (hw.2.2.2.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs51B0
  have hsD33 : sD.mem.get 33 = s.mem.get 23 := by
    rw [hrun]; exact (hw.2.2.2.1).trans (hpres51 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD34 : sD.mem.get 34 = s.mem.get 24 := by
    rw [hrun]; exact (hw.2.2.2.2.1).trans (hpres51 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDNUL : sD.mem.get 35 = 0 := by rw [hrun]; exact hw.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 3 := by rw [hrun]; exact hw.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 3 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha33 ha34 ha35 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpres51 a ha32 ha29 ha18 ha30 ha2319 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsDB0, hsD33, hsD34, hsDNUL, hsDI, hsDL, hpres⟩

/-- `AFTER_PAD` with `SIGN ≠ 0`, `NDIG = 3`, `IDX = 0 < ROOM`, and `LEN = 4 < CAP`,
writes `'-'` then digits and a NUL, and halts. 427 steps. -/
theorem after_pad_minus_ndig3_done {s : Machine}
    (hpc : s.pc = 1077)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hK45 : s.mem.get 9 = 45)
    (hN : s.mem.get 25 = 3)
    (hI : s.mem.get 29 = 0)
    (hL : s.mem.get 16 = 4)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hRlo0 : 0 < (s.mem.get 28).toNat)
    (hRlo : 3 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (4 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1077 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 427
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
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hm := after_pad_minus_to_emit_idx0 (s := s) hpc hh hZ hONE hK45 hI hSlo hShi hRlo0 hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s51 := runN s 51
  have hs51pc : s51.pc = 1575 := hm.1
  have hs51h : s51.halted = false := hm.2.1
  have hs51Z : s51.mem.get 0 = 0 := hm.2.2.1
  have hs51B0 : s51.mem.get 32 = 45 := hm.2.2.2.1
  have hs51I : s51.mem.get 29 = 1 := hm.2.2.2.2.1
  have hpres51 := hm.2.2.2.2.2
  have hONE51 : s51.mem.get 3 = 1 := (hpres51 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK551 : s51.mem.get 2322 = 5 := (hpres51 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hN51 : s51.mem.get 25 = 3 := (hpres51 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN
  have hL51 : s51.mem.get 16 = 4 := (hpres51 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL
  have hRlo51 : 3 < (s51.mem.get 28).toNat := by
    have : s51.mem.get 28 = s.mem.get 28 := hpres51 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRlo
  have hRhi51 : (s51.mem.get 28).toNat < 32768 := by
    have : s51.mem.get 28 = s.mem.get 28 := hpres51 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have hLlt51 : (4 : Nat) < (s51.mem.get 13).toNat := by
    have : s51.mem.get 13 = s.mem.get 13 := hpres51 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hLlt
  have hChi51 : (s51.mem.get 13).toNat < 32768 := by
    have : s51.mem.get 13 = s.mem.get 13 := hpres51 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hChi
  have g51 : ∀ k : Nat, 1185 ≤ k → k < 2319 →
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
    exact (hpres51 (UInt16.ofNat k) n32 n29 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hw := emit_ndig3_idx1_write_nul_done (s := s51) hs51pc hs51h hs51Z hONE51 hK551 hN51 hs51I hL51
    hRlo51 hRhi51 hLlt51 hChi51 g51
  have hrun : sD = runN s51 376 := runN_add_eq s 51 376 427 (by decide)
  have hsDB0 : sD.mem.get 32 = 45 := by
    rw [hrun]
    exact (hw.2.2.2.2.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs51B0
  have hsD33 : sD.mem.get 33 = s.mem.get 22 := by
    rw [hrun]; exact (hw.2.2.2.1).trans (hpres51 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD34 : sD.mem.get 34 = s.mem.get 23 := by
    rw [hrun]; exact (hw.2.2.2.2.1).trans (hpres51 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD35 : sD.mem.get 35 = s.mem.get 24 := by
    rw [hrun]; exact (hw.2.2.2.2.2.1).trans (hpres51 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDNUL : sD.mem.get 36 = 0 := by rw [hrun]; exact hw.2.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 4 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 4 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha33 ha34 ha35 ha36 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpres51 a ha32 ha29 ha18 ha30 ha2319 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsDB0, hsD33, hsD34, hsD35, hsDNUL, hsDI, hsDL, hpres⟩

/-- `AFTER_PAD` with `SIGN ≠ 0`, `NDIG = 4`, `IDX = 0 < ROOM`, and `LEN = 5 < CAP`,
writes `'-'` then digits and a NUL, and halts. 489 steps. -/
theorem after_pad_minus_ndig4_done {s : Machine}
    (hpc : s.pc = 1077)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK5 : s.mem.get 2322 = 5)
    (hK45 : s.mem.get 9 = 45)
    (hN : s.mem.get 25 = 4)
    (hI : s.mem.get 29 = 0)
    (hL : s.mem.get 16 = 5)
    (hSlo : 0 < (s.mem.get 19).toNat)
    (hShi : (s.mem.get 19).toNat < 32768)
    (hRlo0 : 0 < (s.mem.get 28).toNat)
    (hRlo : 4 < (s.mem.get 28).toNat)
    (hRhi : (s.mem.get 28).toNat < 32768)
    (hLlt : (5 : Nat) < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hcode : ∀ k : Nat, 1077 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 489
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
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a) := by
  intro sD
  have hm := after_pad_minus_to_emit_idx0 (s := s) hpc hh hZ hONE hK45 hI hSlo hShi hRlo0 hRhi
    (fun k h1 h2 => hcode k h1 (by omega))
  let s51 := runN s 51
  have hs51pc : s51.pc = 1575 := hm.1
  have hs51h : s51.halted = false := hm.2.1
  have hs51Z : s51.mem.get 0 = 0 := hm.2.2.1
  have hs51B0 : s51.mem.get 32 = 45 := hm.2.2.2.1
  have hs51I : s51.mem.get 29 = 1 := hm.2.2.2.2.1
  have hpres51 := hm.2.2.2.2.2
  have hONE51 : s51.mem.get 3 = 1 := (hpres51 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hK551 : s51.mem.get 2322 = 5 := (hpres51 2322 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hK5
  have hN51 : s51.mem.get 25 = 4 := (hpres51 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hN
  have hL51 : s51.mem.get 16 = 5 := (hpres51 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL
  have hRlo51 : 4 < (s51.mem.get 28).toNat := by
    have : s51.mem.get 28 = s.mem.get 28 := hpres51 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRlo
  have hRhi51 : (s51.mem.get 28).toNat < 32768 := by
    have : s51.mem.get 28 = s.mem.get 28 := hpres51 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hRhi
  have hLlt51 : (5 : Nat) < (s51.mem.get 13).toNat := by
    have : s51.mem.get 13 = s.mem.get 13 := hpres51 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hLlt
  have hChi51 : (s51.mem.get 13).toNat < 32768 := by
    have : s51.mem.get 13 = s.mem.get 13 := hpres51 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hChi
  have g51 : ∀ k : Nat, 1185 ≤ k → k < 2319 →
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
    exact (hpres51 (UInt16.ofNat k) n32 n29 n18 n30 n2319 n0).trans (hcode k (by omega) (by omega))
  have hw := emit_ndig4_idx1_write_nul_done (s := s51) hs51pc hs51h hs51Z hONE51 hK551 hN51 hs51I hL51
    hRlo51 hRhi51 hLlt51 hChi51 g51
  have hrun : sD = runN s51 438 := runN_add_eq s 51 438 489 (by decide)
  have hsDB0 : sD.mem.get 32 = 45 := by
    rw [hrun]
    exact (hw.2.2.2.2.2.2.2.2.2.2 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs51B0
  have hsD33 : sD.mem.get 33 = s.mem.get 21 := by
    rw [hrun]; exact (hw.2.2.2.1).trans (hpres51 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD34 : sD.mem.get 34 = s.mem.get 22 := by
    rw [hrun]; exact (hw.2.2.2.2.1).trans (hpres51 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD35 : sD.mem.get 35 = s.mem.get 23 := by
    rw [hrun]; exact (hw.2.2.2.2.2.1).trans (hpres51 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsD36 : sD.mem.get 36 = s.mem.get 24 := by
    rw [hrun]; exact (hw.2.2.2.2.2.2.1).trans (hpres51 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hw.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hw.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hw.2.2.1
  have hsDNUL : sD.mem.get 37 = 0 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 5 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 5 := by rw [hrun]; exact hw.2.2.2.2.2.2.2.2.2.1
  have hpresw := hw.2.2.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha37 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0
    rw [hrun]
    exact (hpresw a ha33 ha34 ha35 ha36 ha37 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      (hpres51 a ha32 ha29 ha18 ha30 ha2319 ha0)
  exact ⟨hsDpc, hsDh, hsDZ, hsDB0, hsD33, hsD34, hsD35, hsD36, hsDNUL, hsDI, hsDL, hpres⟩

end IntFmt
