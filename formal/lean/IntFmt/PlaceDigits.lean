/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

From `DIGITS` (pc 174) through the four place loops to `P3_DONE`
(pc 513), with the reconstruction of `N` as decimal place digits
`Q0..Q3` and ones remainder. Block lemma, not end-to-end correctness.
-/

import IntFmt.Place0
import IntFmt.PlaceLoop

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-- Unique quotient and remainder for `n = q * b + r` with `r < b`. -/
theorem unique_divmod {n q r b : Nat} (hb : 0 < b) (hr : r < b)
    (heq : n = q * b + r) :
    q = n / b ∧ r = n % b := by
  have heq' : n = b * q + r := by rw [Nat.mul_comm q b] at heq; exact heq
  have hdiv : (b * q + r) / b = q := by
    rw [Nat.mul_add_div hb, Nat.div_eq_of_lt hr, Nat.add_zero]
  have hmod : (b * q + r) % b = r := by
    rw [Nat.mul_add_mod b q r, Nat.mod_eq_of_lt hr]
  constructor
  · exact (heq' ▸ hdiv).symm
  · exact (heq' ▸ hmod).symm

theorem div1000_mod10 (n : Nat) :
    n / 1000 % 10 = n % 10000 / 1000 := by
  have hmul : 10000 * (n / 10000) = 1000 * (10 * (n / 10000)) := by omega
  have hdiv : n / 1000 = 10 * (n / 10000) + n % 10000 / 1000 := by
    have hL : n / 1000 = (10000 * (n / 10000) + n % 10000) / 1000 :=
      (congrArg (fun x => x / 1000) (Nat.div_add_mod n 10000)).symm
    rw [hL, hmul]
    exact Nat.mul_add_div (by decide : 0 < 1000) _ _
  have hr : n % 10000 / 1000 < 10 := by
    have : n % 10000 < 10000 := Nat.mod_lt n (by decide)
    omega
  have hmod : (10 * (n / 10000) + n % 10000 / 1000) % 10 =
      n % 10000 / 1000 := by
    rw [Nat.mul_add_mod 10 (n / 10000) (n % 10000 / 1000), Nat.mod_eq_of_lt hr]
  rw [hdiv, hmod]

theorem div100_mod10 (n : Nat) :
    n / 100 % 10 = n % 1000 / 100 := by
  have hmul : 1000 * (n / 1000) = 100 * (10 * (n / 1000)) := by omega
  have hdiv : n / 100 = 10 * (n / 1000) + n % 1000 / 100 := by
    have hL : n / 100 = (1000 * (n / 1000) + n % 1000) / 100 :=
      (congrArg (fun x => x / 100) (Nat.div_add_mod n 1000)).symm
    rw [hL, hmul]
    exact Nat.mul_add_div (by decide : 0 < 100) _ _
  have hr : n % 1000 / 100 < 10 := by
    have : n % 1000 < 1000 := Nat.mod_lt n (by decide)
    omega
  have hmod : (10 * (n / 1000) + n % 1000 / 100) % 10 = n % 1000 / 100 := by
    rw [Nat.mul_add_mod 10 (n / 1000) (n % 1000 / 100), Nat.mod_eq_of_lt hr]
  rw [hdiv, hmod]

theorem div10_mod10 (n : Nat) :
    n / 10 % 10 = n % 100 / 10 := by
  have hmul : 100 * (n / 100) = 10 * (10 * (n / 100)) := by omega
  have hdiv : n / 10 = 10 * (n / 100) + n % 100 / 10 := by
    have hL : n / 10 = (100 * (n / 100) + n % 100) / 10 :=
      (congrArg (fun x => x / 10) (Nat.div_add_mod n 100)).symm
    rw [hL, hmul]
    exact Nat.mul_add_div (by decide : 0 < 10) _ _
  have hr : n % 100 / 10 < 10 := by
    have : n % 100 < 100 := Nat.mod_lt n (by decide)
    omega
  have hmod : (10 * (n / 100) + n % 100 / 10) % 10 = n % 100 / 10 := by
    rw [Nat.mul_add_mod 10 (n / 100) (n % 100 / 10), Nat.mod_eq_of_lt hr]
  rw [hdiv, hmod]

/-- Steps from `DIGITS` through `P0`..`P3` to `P3_DONE`. -/
def placeAllSteps (n : Nat) : Nat :=
  5 + p0PlaceSteps n + placeSteps 1000 (n % 10000)
    + placeSteps 100 (n % 1000) + placeSteps 10 (n % 100)

theorem placeAllSteps_le (n : Nat) :
    placeAllSteps n ≤ 5 + (16 + 21 * (n / 10000))
      + (16 + 21 * (n % 10000 / 1000))
      + (16 + 21 * (n % 1000 / 100))
      + (16 + 21 * (n % 100 / 10)) := by
  have h0 := p0PlaceSteps_le n
  have h1 := placeSteps_le 1000 (n % 10000) (by decide)
  have h2 := placeSteps_le 100 (n % 1000) (by decide)
  have h3 := placeSteps_le 10 (n % 100) (by decide)
  unfold placeAllSteps
  omega

theorem placeAllSteps_le_of_word (n : Nat) (hn : n < 65536) :
    placeAllSteps n ≤ 757 := by
  have := placeAllSteps_le n
  have h0 : n / 10000 ≤ 6 := by omega
  have h1 : n % 10000 / 1000 ≤ 9 := by
    have : n % 10000 < 10000 := Nat.mod_lt n (by decide)
    omega
  have h2 : n % 1000 / 100 ≤ 9 := by
    have : n % 1000 < 1000 := Nat.mod_lt n (by decide)
    omega
  have h3 : n % 100 / 10 ≤ 9 := by
    have : n % 100 < 100 := Nat.mod_lt n (by decide)
    omega
  omega

/-- From `DIGITS` (pc 174) through the four place loops to `P3_DONE`
(pc 513). The entry value of `N` is recovered as decimal place digits
`Q0..Q3` and the ones remainder still in `N`. -/
theorem digits_to_p3_done {s : Machine}
    (hpc : s.pc = 174)
    (hh : s.halted = false)
    (hZ : s.mem.get 0 = 0)
    (hONE : s.mem.get 3 = 1)
    (hTEN : s.mem.get 4 = 10)
    (hC100 : s.mem.get 5 = 100)
    (hC1000 : s.mem.get 6 = 1000)
    (hC10000 : s.mem.get 7 = 10000)
    (hcode : ∀ k : Nat, 174 ≤ k → k < 513 →
      s.mem.get (UInt16.ofNat k) = intfmtImage[k]!) :
    let n := (s.mem.get 17).toNat
    let sP := runN s (placeAllSteps n)
    sP.pc = 513 ∧
    sP.halted = false ∧
    sP.mem.get 0 = 0 ∧
    (sP.mem.get 20).toNat = n / 10000 ∧
    (sP.mem.get 21).toNat = n / 1000 % 10 ∧
    (sP.mem.get 22).toNat = n / 100 % 10 ∧
    (sP.mem.get 23).toNat = n / 10 % 10 ∧
    (sP.mem.get 17).toNat = n % 10 ∧
    sP.mem.get 24 = 0 ∧
    (∀ a, a ≠ 17 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 24 → a ≠ 18 → a ≠ 0 →
      sP.mem.get a = s.mem.get a) := by
  intro n sP
  have hz := digits_zero_Qs (s := s) hpc hh
    (fun k h1 h2 => hcode k h1 (by omega))
  let s5 := runN s 5
  have hs5pc : s5.pc = 189 := hz.1
  have hs5h : s5.halted = false := hz.2.1
  have hpres5 := hz.2.2.2.2.2.2.2
  have hs5Z : s5.mem.get 0 = 0 := (hpres5 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hZ
  have hs5ONE : s5.mem.get 3 = 1 := (hpres5 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hONE
  have hs5TEN : s5.mem.get 4 = 10 := (hpres5 4 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hTEN
  have hs5C100 : s5.mem.get 5 = 100 := (hpres5 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hC100
  have hs5C1000 : s5.mem.get 6 = 1000 := (hpres5 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hC1000
  have hs5C10000 : s5.mem.get 7 = 10000 := (hpres5 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hC10000
  have hs5N : s5.mem.get 17 = s.mem.get 17 := hpres5 17 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs5Q0 : s5.mem.get 20 = 0 := hz.2.2.1
  have hs5Q1 : s5.mem.get 21 = 0 := hz.2.2.2.1
  have hs5Q2 : s5.mem.get 22 = 0 := hz.2.2.2.2.1
  have hs5Q3 : s5.mem.get 23 = 0 := hz.2.2.2.2.2.1
  have hs5Q4 : s5.mem.get 24 = 0 := hz.2.2.2.2.2.2.1
  have hn5 : (s5.mem.get 17).toNat = n := by rw [hs5N]
  have hnlt : n < 65536 := by
    simpa [show UInt16.size = 65536 from rfl] using UInt16.toNat_lt_size (s.mem.get 17)
  have hQ0p : (s5.mem.get 20).toNat + (s5.mem.get 17).toNat / 10000 < 65536 := by
    have h0 : (s5.mem.get 20).toNat = 0 := by simp [hs5Q0]
    rw [h0, hn5]; omega
  have g5 : ∀ k : Nat, 189 ≤ k → k < 270 →
      s5.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
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
    have n24 : UInt16.ofNat k ≠ (24 : Word) := by
      have : (24 : Word) = UInt16.ofNat 24 := rfl
      rw [this]; exact ofNat_ne k 24 (by omega) (by decide) (by omega)
    exact (hpres5 (UInt16.ofNat k) n20 n21 n22 n23 n24).trans
      (hcode k (by omega) (by omega))
  have hp0 := p0_loop (s := s5) hs5pc hs5h hs5Z hs5ONE hs5C10000 hQ0p g5
  have hrun0 : runN s (5 + p0PlaceSteps n) = runN s5 (p0PlaceSteps (s5.mem.get 17).toNat) := by
    have hsteps : p0PlaceSteps (s5.mem.get 17).toNat = p0PlaceSteps n := by rw [hn5]
    have h := runN_add_eq s 5 (p0PlaceSteps n) (5 + p0PlaceSteps n) (by omega)
    rw [h, hsteps]
  let s0 := runN s (5 + p0PlaceSteps n)
  have hs0eq : s0 = runN s5 (p0PlaceSteps (s5.mem.get 17).toNat) := hrun0
  have hs0pc : s0.pc = 270 := by rw [hs0eq]; exact hp0.1
  have hs0h : s0.halted = false := by rw [hs0eq]; exact hp0.2.1
  have hs0Z : s0.mem.get 0 = 0 := by rw [hs0eq]; exact hp0.2.2.1
  have hs0rem_lt : (s0.mem.get 17).toNat < 10000 := by rw [hs0eq]; exact hp0.2.2.2.1
  have hrec0 : (s5.mem.get 20).toNat * 10000 + (s5.mem.get 17).toNat =
      (s0.mem.get 20).toNat * 10000 + (s0.mem.get 17).toNat := by
    rw [hs0eq]; exact hp0.2.2.2.2.1
  have hpres0raw := hp0.2.2.2.2.2
  have hpres0 : ∀ a, a ≠ 17 → a ≠ 20 → a ≠ 18 → a ≠ 0 →
      s0.mem.get a = s5.mem.get a := by
    intro a ha17 ha20 ha18 ha0
    rw [hs0eq]; exact hpres0raw a ha17 ha20 ha18 ha0
  have hzeroQ : (s5.mem.get 20).toNat = 0 := by simp [hs5Q0]
  have heq0 : n = (s0.mem.get 20).toNat * 10000 + (s0.mem.get 17).toNat := by
    have : n = (s5.mem.get 20).toNat * 10000 + (s5.mem.get 17).toNat := by
      rw [hzeroQ, hn5, Nat.zero_mul, Nat.zero_add]
    exact this.trans hrec0
  have hdiv0 := unique_divmod (n := n) (q := (s0.mem.get 20).toNat)
    (r := (s0.mem.get 17).toNat) (b := 10000) (by decide) hs0rem_lt heq0
  have hs0Q0 : (s0.mem.get 20).toNat = n / 10000 := hdiv0.1
  have hs0N : (s0.mem.get 17).toNat = n % 10000 := hdiv0.2
  have hs0ONE : s0.mem.get 3 = 1 := (hpres0 3 (by decide) (by decide) (by decide) (by decide)).trans hs5ONE
  have hs0C1000 : s0.mem.get 6 = 1000 := (hpres0 6 (by decide) (by decide) (by decide) (by decide)).trans hs5C1000
  have hs0C100 : s0.mem.get 5 = 100 := (hpres0 5 (by decide) (by decide) (by decide) (by decide)).trans hs5C100
  have hs0TEN : s0.mem.get 4 = 10 := (hpres0 4 (by decide) (by decide) (by decide) (by decide)).trans hs5TEN
  have hs0Q1 : s0.mem.get 21 = 0 := (hpres0 21 (by decide) (by decide) (by decide) (by decide)).trans hs5Q1
  have hs0Q2 : s0.mem.get 22 = 0 := (hpres0 22 (by decide) (by decide) (by decide) (by decide)).trans hs5Q2
  have hs0Q3 : s0.mem.get 23 = 0 := (hpres0 23 (by decide) (by decide) (by decide) (by decide)).trans hs5Q3
  have hs0Q4 : s0.mem.get 24 = 0 := (hpres0 24 (by decide) (by decide) (by decide) (by decide)).trans hs5Q4
  have hQ1p : (s0.mem.get 21).toNat + (s0.mem.get 17).toNat / 1000 < 65536 := by
    have h0 : (s0.mem.get 21).toNat = 0 := by simp [hs0Q1]
    rw [h0]; omega
  have g0 : ∀ k : Nat, 270 ≤ k → k < 351 →
      s0.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n17 : UInt16.ofNat k ≠ (17 : Word) := by
      have : (17 : Word) = UInt16.ofNat 17 := rfl
      rw [this]; exact ofNat_ne k 17 (by omega) (by decide) (by omega)
    have n20 : UInt16.ofNat k ≠ (20 : Word) := by
      have : (20 : Word) = UInt16.ofNat 20 := rfl
      rw [this]; exact ofNat_ne k 20 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    have n21 : UInt16.ofNat k ≠ (21 : Word) := by
      have : (21 : Word) = UInt16.ofNat 21 := rfl
      rw [this]; exact ofNat_ne k 21 (by omega) (by decide) (by omega)
    have n22 : UInt16.ofNat k ≠ (22 : Word) := by
      have : (22 : Word) = UInt16.ofNat 22 := rfl
      rw [this]; exact ofNat_ne k 22 (by omega) (by decide) (by omega)
    have n23 : UInt16.ofNat k ≠ (23 : Word) := by
      have : (23 : Word) = UInt16.ofNat 23 := rfl
      rw [this]; exact ofNat_ne k 23 (by omega) (by decide) (by omega)
    have n24 : UInt16.ofNat k ≠ (24 : Word) := by
      have : (24 : Word) = UInt16.ofNat 24 := rfl
      rw [this]; exact ofNat_ne k 24 (by omega) (by decide) (by omega)
    exact (hpres0 (UInt16.ofNat k) n17 n20 n18 n0).trans
      ((hpres5 (UInt16.ofNat k) n20 n21 n22 n23 n24).trans
      (hcode k (by omega) (by omega)))
  have hp1 := p1_loop (s := s0) hs0pc hs0h hs0Z hs0ONE hs0C1000 hQ1p g0
  have hst1 : placeSteps 1000 (s0.mem.get 17).toNat = placeSteps 1000 (n % 10000) := by
    rw [hs0N]
  have hsum1 : 5 + p0PlaceSteps n + placeSteps 1000 (n % 10000) =
      (5 + p0PlaceSteps n) + placeSteps 1000 (n % 10000) := by omega
  have hrun1 : runN s (5 + p0PlaceSteps n + placeSteps 1000 (n % 10000)) =
      runN s0 (placeSteps 1000 (s0.mem.get 17).toNat) := by
    have h := runN_add_eq s (5 + p0PlaceSteps n) (placeSteps 1000 (n % 10000))
      (5 + p0PlaceSteps n + placeSteps 1000 (n % 10000)) (by omega)
    rw [h, hst1]
  let s1 := runN s (5 + p0PlaceSteps n + placeSteps 1000 (n % 10000))
  have hs1eq : s1 = runN s0 (placeSteps 1000 (s0.mem.get 17).toNat) := hrun1
  have hs1pc : s1.pc = 351 := by rw [hs1eq]; exact hp1.1
  have hs1h : s1.halted = false := by rw [hs1eq]; exact hp1.2.1
  have hs1Z : s1.mem.get 0 = 0 := by rw [hs1eq]; exact hp1.2.2.1
  have hs1rem_lt : (s1.mem.get 17).toNat < 1000 := by rw [hs1eq]; exact hp1.2.2.2.1
  have hrec1 : (s0.mem.get 21).toNat * 1000 + (s0.mem.get 17).toNat =
      (s1.mem.get 21).toNat * 1000 + (s1.mem.get 17).toNat := by
    rw [hs1eq]; exact hp1.2.2.2.2.1
  have hpres1raw := hp1.2.2.2.2.2
  have hpres1 : ∀ a, a ≠ 17 → a ≠ 21 → a ≠ 18 → a ≠ 0 →
      s1.mem.get a = s0.mem.get a := by
    intro a ha17 ha21 ha18 ha0
    rw [hs1eq]; exact hpres1raw a ha17 ha21 ha18 ha0
  have hzeroQ1 : (s0.mem.get 21).toNat = 0 := by simp [hs0Q1]
  have heq1 : n % 10000 = (s1.mem.get 21).toNat * 1000 + (s1.mem.get 17).toNat := by
    have : n % 10000 = (s0.mem.get 21).toNat * 1000 + (s0.mem.get 17).toNat := by
      rw [hzeroQ1, hs0N, Nat.zero_mul, Nat.zero_add]
    exact this.trans hrec1
  have hdiv1 := unique_divmod (n := n % 10000) (q := (s1.mem.get 21).toNat)
    (r := (s1.mem.get 17).toNat) (b := 1000) (by decide) hs1rem_lt heq1
  have hs1Q1 : (s1.mem.get 21).toNat = n / 1000 % 10 := by
    have : (s1.mem.get 21).toNat = n % 10000 / 1000 := hdiv1.1
    exact this.trans (div1000_mod10 n).symm
  have hs1N : (s1.mem.get 17).toNat = n % 1000 := by
    have : (s1.mem.get 17).toNat = n % 10000 % 1000 := hdiv1.2
    have hmod : n % 10000 % 1000 = n % 1000 := Nat.mod_mod_of_dvd n (by decide : 1000 ∣ 10000)
    exact this.trans hmod
  have hs1ONE : s1.mem.get 3 = 1 := (hpres1 3 (by decide) (by decide) (by decide) (by decide)).trans hs0ONE
  have hs1C100 : s1.mem.get 5 = 100 := (hpres1 5 (by decide) (by decide) (by decide) (by decide)).trans hs0C100
  have hs1TEN : s1.mem.get 4 = 10 := (hpres1 4 (by decide) (by decide) (by decide) (by decide)).trans hs0TEN
  have hs1Q0 : s1.mem.get 20 = s0.mem.get 20 := hpres1 20 (by decide) (by decide) (by decide) (by decide)
  have hs1Q2 : s1.mem.get 22 = 0 := (hpres1 22 (by decide) (by decide) (by decide) (by decide)).trans hs0Q2
  have hs1Q3 : s1.mem.get 23 = 0 := (hpres1 23 (by decide) (by decide) (by decide) (by decide)).trans hs0Q3
  have hs1Q4 : s1.mem.get 24 = 0 := (hpres1 24 (by decide) (by decide) (by decide) (by decide)).trans hs0Q4
  have hQ2p : (s1.mem.get 22).toNat + (s1.mem.get 17).toNat / 100 < 65536 := by
    have h0 : (s1.mem.get 22).toNat = 0 := by simp [hs1Q2]
    rw [h0]; omega
  have g1 : ∀ k : Nat, 351 ≤ k → k < 432 →
      s1.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n17 : UInt16.ofNat k ≠ (17 : Word) := by
      have : (17 : Word) = UInt16.ofNat 17 := rfl
      rw [this]; exact ofNat_ne k 17 (by omega) (by decide) (by omega)
    have n21 : UInt16.ofNat k ≠ (21 : Word) := by
      have : (21 : Word) = UInt16.ofNat 21 := rfl
      rw [this]; exact ofNat_ne k 21 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    have n20 : UInt16.ofNat k ≠ (20 : Word) := by
      have : (20 : Word) = UInt16.ofNat 20 := rfl
      rw [this]; exact ofNat_ne k 20 (by omega) (by decide) (by omega)
    have n22 : UInt16.ofNat k ≠ (22 : Word) := by
      have : (22 : Word) = UInt16.ofNat 22 := rfl
      rw [this]; exact ofNat_ne k 22 (by omega) (by decide) (by omega)
    have n23 : UInt16.ofNat k ≠ (23 : Word) := by
      have : (23 : Word) = UInt16.ofNat 23 := rfl
      rw [this]; exact ofNat_ne k 23 (by omega) (by decide) (by omega)
    have n24 : UInt16.ofNat k ≠ (24 : Word) := by
      have : (24 : Word) = UInt16.ofNat 24 := rfl
      rw [this]; exact ofNat_ne k 24 (by omega) (by decide) (by omega)
    exact (hpres1 (UInt16.ofNat k) n17 n21 n18 n0).trans
      ((hpres0 (UInt16.ofNat k) n17 n20 n18 n0).trans
      ((hpres5 (UInt16.ofNat k) n20 n21 n22 n23 n24).trans
      (hcode k (by omega) (by omega))))
  have hp2 := p2_loop (s := s1) hs1pc hs1h hs1Z hs1ONE hs1C100 hQ2p g1
  have hst2 : placeSteps 100 (s1.mem.get 17).toNat = placeSteps 100 (n % 1000) := by
    rw [hs1N]
  have hrun2 : runN s (5 + p0PlaceSteps n + placeSteps 1000 (n % 10000)
        + placeSteps 100 (n % 1000)) =
      runN s1 (placeSteps 100 (s1.mem.get 17).toNat) := by
    have h := runN_add_eq s
      (5 + p0PlaceSteps n + placeSteps 1000 (n % 10000))
      (placeSteps 100 (n % 1000))
      (5 + p0PlaceSteps n + placeSteps 1000 (n % 10000) + placeSteps 100 (n % 1000))
      (by omega)
    rw [h, hst2]
  let s2 := runN s (5 + p0PlaceSteps n + placeSteps 1000 (n % 10000)
    + placeSteps 100 (n % 1000))
  have hs2eq : s2 = runN s1 (placeSteps 100 (s1.mem.get 17).toNat) := hrun2
  have hs2pc : s2.pc = 432 := by rw [hs2eq]; exact hp2.1
  have hs2h : s2.halted = false := by rw [hs2eq]; exact hp2.2.1
  have hs2Z : s2.mem.get 0 = 0 := by rw [hs2eq]; exact hp2.2.2.1
  have hs2rem_lt : (s2.mem.get 17).toNat < 100 := by rw [hs2eq]; exact hp2.2.2.2.1
  have hrec2 : (s1.mem.get 22).toNat * 100 + (s1.mem.get 17).toNat =
      (s2.mem.get 22).toNat * 100 + (s2.mem.get 17).toNat := by
    rw [hs2eq]; exact hp2.2.2.2.2.1
  have hpres2raw := hp2.2.2.2.2.2
  have hpres2 : ∀ a, a ≠ 17 → a ≠ 22 → a ≠ 18 → a ≠ 0 →
      s2.mem.get a = s1.mem.get a := by
    intro a ha17 ha22 ha18 ha0
    rw [hs2eq]; exact hpres2raw a ha17 ha22 ha18 ha0
  have hzeroQ2 : (s1.mem.get 22).toNat = 0 := by simp [hs1Q2]
  have heq2 : n % 1000 = (s2.mem.get 22).toNat * 100 + (s2.mem.get 17).toNat := by
    have : n % 1000 = (s1.mem.get 22).toNat * 100 + (s1.mem.get 17).toNat := by
      rw [hzeroQ2, hs1N, Nat.zero_mul, Nat.zero_add]
    exact this.trans hrec2
  have hdiv2 := unique_divmod (n := n % 1000) (q := (s2.mem.get 22).toNat)
    (r := (s2.mem.get 17).toNat) (b := 100) (by decide) hs2rem_lt heq2
  have hs2Q2 : (s2.mem.get 22).toNat = n / 100 % 10 := by
    have : (s2.mem.get 22).toNat = n % 1000 / 100 := hdiv2.1
    exact this.trans (div100_mod10 n).symm
  have hs2N : (s2.mem.get 17).toNat = n % 100 := by
    have : (s2.mem.get 17).toNat = n % 1000 % 100 := hdiv2.2
    have hmod : n % 1000 % 100 = n % 100 := Nat.mod_mod_of_dvd n (by decide : 100 ∣ 1000)
    exact this.trans hmod
  have hs2ONE : s2.mem.get 3 = 1 := (hpres2 3 (by decide) (by decide) (by decide) (by decide)).trans hs1ONE
  have hs2TEN : s2.mem.get 4 = 10 := (hpres2 4 (by decide) (by decide) (by decide) (by decide)).trans hs1TEN
  have hs2Q0 : s2.mem.get 20 = s1.mem.get 20 := hpres2 20 (by decide) (by decide) (by decide) (by decide)
  have hs2Q1 : s2.mem.get 21 = s1.mem.get 21 := hpres2 21 (by decide) (by decide) (by decide) (by decide)
  have hs2Q3 : s2.mem.get 23 = 0 := (hpres2 23 (by decide) (by decide) (by decide) (by decide)).trans hs1Q3
  have hs2Q4 : s2.mem.get 24 = 0 := (hpres2 24 (by decide) (by decide) (by decide) (by decide)).trans hs1Q4
  have hQ3p : (s2.mem.get 23).toNat + (s2.mem.get 17).toNat / 10 < 65536 := by
    have h0 : (s2.mem.get 23).toNat = 0 := by simp [hs2Q3]
    rw [h0]; omega
  have g2 : ∀ k : Nat, 432 ≤ k → k < 513 →
      s2.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    intro k h1 h2
    have n17 : UInt16.ofNat k ≠ (17 : Word) := by
      have : (17 : Word) = UInt16.ofNat 17 := rfl
      rw [this]; exact ofNat_ne k 17 (by omega) (by decide) (by omega)
    have n22 : UInt16.ofNat k ≠ (22 : Word) := by
      have : (22 : Word) = UInt16.ofNat 22 := rfl
      rw [this]; exact ofNat_ne k 22 (by omega) (by decide) (by omega)
    have n18 : UInt16.ofNat k ≠ (18 : Word) := by
      have : (18 : Word) = UInt16.ofNat 18 := rfl
      rw [this]; exact ofNat_ne k 18 (by omega) (by decide) (by omega)
    have n0 : UInt16.ofNat k ≠ (0 : Word) := by
      have : (0 : Word) = UInt16.ofNat 0 := rfl
      rw [this]; exact ofNat_ne k 0 (by omega) (by decide) (by omega)
    have n20 : UInt16.ofNat k ≠ (20 : Word) := by
      have : (20 : Word) = UInt16.ofNat 20 := rfl
      rw [this]; exact ofNat_ne k 20 (by omega) (by decide) (by omega)
    have n21 : UInt16.ofNat k ≠ (21 : Word) := by
      have : (21 : Word) = UInt16.ofNat 21 := rfl
      rw [this]; exact ofNat_ne k 21 (by omega) (by decide) (by omega)
    have n23 : UInt16.ofNat k ≠ (23 : Word) := by
      have : (23 : Word) = UInt16.ofNat 23 := rfl
      rw [this]; exact ofNat_ne k 23 (by omega) (by decide) (by omega)
    have n24 : UInt16.ofNat k ≠ (24 : Word) := by
      have : (24 : Word) = UInt16.ofNat 24 := rfl
      rw [this]; exact ofNat_ne k 24 (by omega) (by decide) (by omega)
    exact (hpres2 (UInt16.ofNat k) n17 n22 n18 n0).trans
      ((hpres1 (UInt16.ofNat k) n17 n21 n18 n0).trans
      ((hpres0 (UInt16.ofNat k) n17 n20 n18 n0).trans
      ((hpres5 (UInt16.ofNat k) n20 n21 n22 n23 n24).trans
      (hcode k (by omega) (by omega)))))
  have hp3 := p3_loop (s := s2) hs2pc hs2h hs2Z hs2ONE hs2TEN hQ3p g2
  have hst3 : placeSteps 10 (s2.mem.get 17).toNat = placeSteps 10 (n % 100) := by
    rw [hs2N]
  have hrun3 : sP = runN s2 (placeSteps 10 (s2.mem.get 17).toNat) := by
    have h := runN_add_eq s
      (5 + p0PlaceSteps n + placeSteps 1000 (n % 10000) + placeSteps 100 (n % 1000))
      (placeSteps 10 (n % 100))
      (placeAllSteps n) rfl
    rw [← hst3] at h
    exact h
  have hsPpc : sP.pc = 513 := by rw [hrun3]; exact hp3.1
  have hsPh : sP.halted = false := by rw [hrun3]; exact hp3.2.1
  have hsPZ : sP.mem.get 0 = 0 := by rw [hrun3]; exact hp3.2.2.1
  have hsPrem_lt : (sP.mem.get 17).toNat < 10 := by rw [hrun3]; exact hp3.2.2.2.1
  have hrec3 : (s2.mem.get 23).toNat * 10 + (s2.mem.get 17).toNat =
      (sP.mem.get 23).toNat * 10 + (sP.mem.get 17).toNat := by
    rw [hrun3]; exact hp3.2.2.2.2.1
  have hpres3raw := hp3.2.2.2.2.2
  have hpres3 : ∀ a, a ≠ 17 → a ≠ 23 → a ≠ 18 → a ≠ 0 →
      sP.mem.get a = s2.mem.get a := by
    intro a ha17 ha23 ha18 ha0
    rw [hrun3]; exact hpres3raw a ha17 ha23 ha18 ha0
  have hzeroQ3 : (s2.mem.get 23).toNat = 0 := by simp [hs2Q3]
  have heq3 : n % 100 = (sP.mem.get 23).toNat * 10 + (sP.mem.get 17).toNat := by
    have : n % 100 = (s2.mem.get 23).toNat * 10 + (s2.mem.get 17).toNat := by
      rw [hzeroQ3, hs2N, Nat.zero_mul, Nat.zero_add]
    exact this.trans hrec3
  have hdiv3 := unique_divmod (n := n % 100) (q := (sP.mem.get 23).toNat)
    (r := (sP.mem.get 17).toNat) (b := 10) (by decide) hsPrem_lt heq3
  have hsPQ3 : (sP.mem.get 23).toNat = n / 10 % 10 := by
    have : (sP.mem.get 23).toNat = n % 100 / 10 := hdiv3.1
    exact this.trans (div10_mod10 n).symm
  have hsPN : (sP.mem.get 17).toNat = n % 10 := by
    have : (sP.mem.get 17).toNat = n % 100 % 10 := hdiv3.2
    have hmod : n % 100 % 10 = n % 10 := Nat.mod_mod_of_dvd n (by decide : 10 ∣ 100)
    exact this.trans hmod
  have hsPQ0 : (sP.mem.get 20).toNat = n / 10000 := by
    have : sP.mem.get 20 = s0.mem.get 20 :=
      (hpres3 20 (by decide) (by decide) (by decide) (by decide)).trans
        ((hpres2 20 (by decide) (by decide) (by decide) (by decide)).trans hs1Q0)
    rw [this]; exact hs0Q0
  have hsPQ1 : (sP.mem.get 21).toNat = n / 1000 % 10 := by
    have : sP.mem.get 21 = s1.mem.get 21 :=
      (hpres3 21 (by decide) (by decide) (by decide) (by decide)).trans hs2Q1
    rw [this]; exact hs1Q1
  have hsPQ2 : (sP.mem.get 22).toNat = n / 100 % 10 := by
    have : sP.mem.get 22 = s2.mem.get 22 := hpres3 22 (by decide) (by decide) (by decide) (by decide)
    rw [this]; exact hs2Q2
  have hsPQ4 : sP.mem.get 24 = 0 :=
    (hpres3 24 (by decide) (by decide) (by decide) (by decide)).trans hs2Q4
  have hpres : ∀ a, a ≠ 17 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 24 → a ≠ 18 → a ≠ 0 →
      sP.mem.get a = s.mem.get a := by
    intro a ha17 ha20 ha21 ha22 ha23 ha24 ha18 ha0
    exact (hpres3 a ha17 ha23 ha18 ha0).trans
      ((hpres2 a ha17 ha22 ha18 ha0).trans
      ((hpres1 a ha17 ha21 ha18 ha0).trans
      ((hpres0 a ha17 ha20 ha18 ha0).trans
      (hpres5 a ha20 ha21 ha22 ha23 ha24))))
  exact ⟨hsPpc, hsPh, hsPZ, hsPQ0, hsPQ1, hsPQ2, hsPQ3, hsPN, hsPQ4, hpres⟩

end IntFmt
