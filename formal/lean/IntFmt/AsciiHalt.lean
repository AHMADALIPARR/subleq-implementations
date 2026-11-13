/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

From `P3_DONE` through ASCII, leading-zero `NDIG`, and the default
unsigned `HAVE_DIG` path to a halted machine. Block lemmas, not
end-to-end correctness.
-/

import IntFmt.HaveDigHalt

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000


/-- From `P3_DONE` with leading-zero pattern for `NDIG = 1`, `SIGN = 0`,
`WIDTH = 0`, and `1 < CAP`: ASCII-convert, emit, NUL-terminate, and
halt. 337 steps. -/
theorem p3_done_unsigned_ndig1_done {s : Machine}
    (hpc : s.pc = 513)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK48 : s.mem.get 8 = 48)
    (hK5 : s.mem.get 2322 = 5)
    (hS : s.mem.get 19 = 0)
    (hW : s.mem.get 14 = 0)
    (hZ20 : s.mem.get 20 = 0)
    (hZ21 : s.mem.get 21 = 0)
    (hZ22 : s.mem.get 22 = 0)
    (hZ23 : s.mem.get 23 = 0)

    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (1 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 513 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 337
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
        sD.mem.get 32 = s.mem.get 17 + 48 ∧
    sD.mem.get 33 = 0 ∧
    sD.mem.get 29 = 1 ∧
    sD.mem.get 16 = 1 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a) := by
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
  have hS_N : sN.mem.get 19 = 0 :=
    (hpresN 19 (by decide) (by decide) (by decide)).trans ((hpresA 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hS)
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
  have hLlt_N : (1 : Nat) < (sN.mem.get 13).toNat := by
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
    -- transfer through ndig then ascii pres; addresses in 867..2318 aren't 18,25,31,0,24,20..23
    exact (hpresN (UInt16.ofNat k)
        n18 n25 n0).trans
      ((hpresA (UInt16.ofNat k)
        n24 n20 n21 n22 n23 n0).trans
      (hcode k (by omega) (by omega)))
  have hd := have_dig_unsigned_ndig1_done (s := sN) hsNpc hsNh hsNZ hONE_N hK5_N hS_N hW_N hsNN
    hClo_N hChi_N hLlt_N gN
  have hrun : sD = runN sN 289 := runN_add_eq s 48 289 337 (by decide)
  have hsD32 : sD.mem.get 32 = s.mem.get 17 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 24 = s19.mem.get 24 := hpresN 24 (by decide) (by decide) (by decide)
    exact (hd.2.2.2.1).trans (h1.trans ha.2.2.2.1)
  have hsDNUL : sD.mem.get 33 = 0 := by rw [hrun]; exact hd.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 1 := by rw [hrun]; exact hd.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 1 := by rw [hrun]; exact hd.2.2.2.2.2.2.1
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hd.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hd.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hd.2.2.1
  have hpresw := hd.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha24 ha20 ha21 ha22 ha23 ha25
    rw [hrun]
    exact (hpresw a ha32 ha33 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      ((hpresN a ha18 ha25 ha0).trans
        (hpresA a ha24 ha20 ha21 ha22 ha23 ha0))
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsDNUL, hsDI, hsDL, hpres⟩

/-- From `P3_DONE` with leading-zero pattern for `NDIG = 2`, `SIGN = 0`,
`WIDTH = 0`, and `2 < CAP`: ASCII-convert, emit, NUL-terminate, and
halt. 405 steps. -/
theorem p3_done_unsigned_ndig2_done {s : Machine}
    (hpc : s.pc = 513)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK48 : s.mem.get 8 = 48)
    (hK5 : s.mem.get 2322 = 5)
    (hS : s.mem.get 19 = 0)
    (hW : s.mem.get 14 = 0)
    (hZ20 : s.mem.get 20 = 0)
    (hZ21 : s.mem.get 21 = 0)
    (hZ22 : s.mem.get 22 = 0)
    (hLlo : 0 < (s.mem.get 23).toNat)
    (hLhi : (s.mem.get 23).toNat ≤ 9)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (2 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 513 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 405
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
        sD.mem.get 32 = s.mem.get 23 + 48 ∧
    sD.mem.get 33 = s.mem.get 17 + 48 ∧
    sD.mem.get 34 = 0 ∧
    sD.mem.get 29 = 2 ∧
    sD.mem.get 16 = 2 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a) := by
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
    intro heq
    have ht : (s19.mem.get 23).toNat = (s.mem.get 23).toNat + 48 := hq ▸ hadd
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
  have hS_N : sN.mem.get 19 = 0 :=
    (hpresN 19 (by decide) (by decide) (by decide) (by decide)).trans ((hpresA 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hS)
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
  have hLlt_N : (2 : Nat) < (sN.mem.get 13).toNat := by
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
    -- transfer through ndig then ascii pres; addresses in 867..2318 aren't 18,25,31,0,24,20..23
    exact (hpresN (UInt16.ofNat k)
        n18 n25 n31 n0).trans
      ((hpresA (UInt16.ofNat k)
        n24 n20 n21 n22 n23 n0).trans
      (hcode k (by omega) (by omega)))
  have hd := have_dig_unsigned_ndig2_done (s := sN) hsNpc hsNh hsNZ hONE_N hK5_N hS_N hW_N hsNN
    hClo_N hChi_N hLlt_N gN
  have hrun : sD = runN sN 349 := runN_add_eq s 56 349 405 (by decide)
  have hsD32 : sD.mem.get 32 = s.mem.get 23 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 23 = s19.mem.get 23 := hpresN 23 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.1).trans (h1.trans ha.2.2.2.2.2.2.2.1)
  have hsD33 : sD.mem.get 33 = s.mem.get 17 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 24 = s19.mem.get 24 := hpresN 24 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.2.1).trans (h1.trans ha.2.2.2.1)
  have hsDNUL : sD.mem.get 34 = 0 := by rw [hrun]; exact hd.2.2.2.2.2.1
  have hsDI : sD.mem.get 29 = 2 := by rw [hrun]; exact hd.2.2.2.2.2.2.1
  have hsDL : sD.mem.get 16 = 2 := by rw [hrun]; exact hd.2.2.2.2.2.2.2.1
  have hsDpc : sD.pc = 32768 := by rw [hrun]; exact hd.1
  have hsDh : sD.halted = true := by rw [hrun]; exact hd.2.1
  have hsDZ : sD.mem.get 0 = 0 := by rw [hrun]; exact hd.2.2.1
  have hpresw := hd.2.2.2.2.2.2.2.2
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha24 ha20 ha21 ha22 ha23 ha25
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      ((hpresN a ha18 ha25 ha31 ha0).trans
        (hpresA a ha24 ha20 ha21 ha22 ha23 ha0))
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsDNUL, hsDI, hsDL, hpres⟩

/-- From `P3_DONE` with leading-zero pattern for `NDIG = 3`, `SIGN = 0`,
`WIDTH = 0`, and `3 < CAP`: ASCII-convert, emit, NUL-terminate, and
halt. 462 steps. -/
theorem p3_done_unsigned_ndig3_done {s : Machine}
    (hpc : s.pc = 513)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK48 : s.mem.get 8 = 48)
    (hK5 : s.mem.get 2322 = 5)
    (hS : s.mem.get 19 = 0)
    (hW : s.mem.get 14 = 0)
    (hZ20 : s.mem.get 20 = 0)
    (hZ21 : s.mem.get 21 = 0)
    (hLlo : 0 < (s.mem.get 22).toNat)
    (hLhi : (s.mem.get 22).toNat ≤ 9)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (3 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 513 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 462
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
        sD.mem.get 32 = s.mem.get 22 + 48 ∧
    sD.mem.get 33 = s.mem.get 23 + 48 ∧
    sD.mem.get 34 = s.mem.get 17 + 48 ∧
    sD.mem.get 35 = 0 ∧
    sD.mem.get 29 = 3 ∧
    sD.mem.get 16 = 3 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a) := by
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
    intro heq
    have ht : (s19.mem.get 22).toNat = (s.mem.get 22).toNat + 48 := hq ▸ hadd
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
  have hS_N : sN.mem.get 19 = 0 :=
    (hpresN 19 (by decide) (by decide) (by decide) (by decide)).trans ((hpresA 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hS)
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
    -- transfer through ndig then ascii pres; addresses in 867..2318 aren't 18,25,31,0,24,20..23
    exact (hpresN (UInt16.ofNat k)
        n18 n25 n31 n0).trans
      ((hpresA (UInt16.ofNat k)
        n24 n20 n21 n22 n23 n0).trans
      (hcode k (by omega) (by omega)))
  have hd := have_dig_unsigned_ndig3_done (s := sN) hsNpc hsNh hsNZ hONE_N hK5_N hS_N hW_N hsNN
    hClo_N hChi_N hLlt_N gN
  have hrun : sD = runN sN 409 := runN_add_eq s 53 409 462 (by decide)
  have hsD32 : sD.mem.get 32 = s.mem.get 22 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 22 = s19.mem.get 22 := hpresN 22 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.1).trans (h1.trans ha.2.2.2.2.2.2.1)
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
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha24 ha20 ha21 ha22 ha23 ha25
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha35 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      ((hpresN a ha18 ha25 ha31 ha0).trans
        (hpresA a ha24 ha20 ha21 ha22 ha23 ha0))
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsDNUL, hsDI, hsDL, hpres⟩

/-- From `P3_DONE` with leading-zero pattern for `NDIG = 4`, `SIGN = 0`,
`WIDTH = 0`, and `4 < CAP`: ASCII-convert, emit, NUL-terminate, and
halt. 519 steps. -/
theorem p3_done_unsigned_ndig4_done {s : Machine}
    (hpc : s.pc = 513)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hK48 : s.mem.get 8 = 48)
    (hK5 : s.mem.get 2322 = 5)
    (hS : s.mem.get 19 = 0)
    (hW : s.mem.get 14 = 0)
    (hZ20 : s.mem.get 20 = 0)
    (hLlo : 0 < (s.mem.get 21).toNat)
    (hLhi : (s.mem.get 21).toNat ≤ 9)
    (hClo : 0 < (s.mem.get 13).toNat)
    (hChi : (s.mem.get 13).toNat < 32768)
    (hLlt : (4 : Nat) < (s.mem.get 13).toNat)
    (hcode : ∀ k : Nat, 513 ≤ k → k < 2319 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let sD := runN s 519
    sD.pc = 32768 ∧
    sD.halted = true ∧
    sD.mem.get 0 = 0 ∧
        sD.mem.get 32 = s.mem.get 21 + 48 ∧
    sD.mem.get 33 = s.mem.get 22 + 48 ∧
    sD.mem.get 34 = s.mem.get 23 + 48 ∧
    sD.mem.get 35 = s.mem.get 17 + 48 ∧
    sD.mem.get 36 = 0 ∧
    sD.mem.get 29 = 4 ∧
    sD.mem.get 16 = 4 ∧
    (∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a) := by
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
    intro heq
    have ht : (s19.mem.get 21).toNat = (s.mem.get 21).toNat + 48 := hq ▸ hadd
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
  have hS_N : sN.mem.get 19 = 0 :=
    (hpresN 19 (by decide) (by decide) (by decide) (by decide)).trans ((hpresA 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hS)
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
    -- transfer through ndig then ascii pres; addresses in 867..2318 aren't 18,25,31,0,24,20..23
    exact (hpresN (UInt16.ofNat k)
        n18 n25 n31 n0).trans
      ((hpresA (UInt16.ofNat k)
        n24 n20 n21 n22 n23 n0).trans
      (hcode k (by omega) (by omega)))
  have hd := have_dig_unsigned_ndig4_done (s := sN) hsNpc hsNh hsNZ hONE_N hK5_N hS_N hW_N hsNN
    hClo_N hChi_N hLlt_N gN
  have hrun : sD = runN sN 469 := runN_add_eq s 50 469 519 (by decide)
  have hsD32 : sD.mem.get 32 = s.mem.get 21 + 48 := by
    rw [hrun]
    have h1 : sN.mem.get 21 = s19.mem.get 21 := hpresN 21 (by decide) (by decide) (by decide) (by decide)
    exact (hd.2.2.2.1).trans (h1.trans ha.2.2.2.2.2.1)
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
  have hpres : ∀ a, a ≠ 32 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 26 → a ≠ 16 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 18 → a ≠ 30 → a ≠ 31 → a ≠ 2319 → a ≠ 2320 → a ≠ 2321 → a ≠ 0 → a ≠ 24 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 25 → sD.mem.get a = s.mem.get a := by
    intro a ha32 ha33 ha34 ha35 ha36 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0 ha24 ha20 ha21 ha22 ha23 ha25
    rw [hrun]
    exact (hpresw a ha32 ha33 ha34 ha35 ha36 ha26 ha16 ha27 ha28 ha29 ha18 ha30 ha31 ha2319 ha2320 ha2321 ha0).trans
      ((hpresN a ha18 ha25 ha31 ha0).trans
        (hpresA a ha24 ha20 ha21 ha22 ha23 ha0))
  exact ⟨hsDpc, hsDh, hsDZ, hsD32, hsD33, hsD34, hsD35, hsDNUL, hsDI, hsDL, hpres⟩

end IntFmt
