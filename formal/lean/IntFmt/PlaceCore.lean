/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Shared helpers for the place-value loops at `DIGITS` / `P0_LOOP`..`P3_DONE`.
These are block-lemma utilities, not end-to-end correctness.
-/

import IntFmt.IPathSign

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-- `runN s (m + n) = runN (runN s m) n` with a concrete sum. -/
theorem runN_add_eq (s : Machine) (m n k : Nat) (h : m + n = k) :
    runN s k = runN (runN s m) n := by
  have hmn := runN_add s m n
  rw [h] at hmn
  exact hmn

theorem runN_2_steps (s : Machine)
    (hh : s.halted = false) (hpc : s.pc.toNat < 32768)
    (h5h : (step s).halted = false) (h5pc : (step s).pc.toNat < 32768) :
    runN s 2 = step (step s) := by
  have h := runN_succ_go s 1 hh hpc
  have h2 := runN_one (step s) h5h h5pc
  exact h.trans h2

theorem runN_3_steps (s : Machine)
    (h0h : s.halted = false) (h0pc : s.pc.toNat < 32768)
    (h1h : (step s).halted = false) (h1pc : (step s).pc.toNat < 32768)
    (h2h : (step (step s)).halted = false) (h2pc : (step (step s)).pc.toNat < 32768) :
    runN s 3 = step (step (step s)) := by
  have h3 : runN s 3 = runN (step s) 2 := runN_succ_go s 2 h0h h0pc
  have h2 := runN_2_steps (step s) h1h h1pc h2h h2pc
  exact h3.trans h2

theorem extract_chunk (base : Nat) (chunk : Array UInt16)
    (hch : intfmtImage.extract base (base + 16) = chunk)
    (off : Nat) (hoff : off < 16) (hbase : base + 16 ≤ 2323) :
    intfmtImage[base + off]! = chunk[off]! := by
  have he : base + 16 ≤ intfmtImage.size := by
    rw [intfmtImage_size]
    exact hbase
  have hse : base ≤ base + 16 := Nat.le_add_right base 16
  have hi : off < (base + 16) - base := by
    have : (base + 16) - base = 16 := Nat.add_sub_cancel_left base 16
    omega
  have hex := image_cell_of_extract base (base + 16) off he hse hi
  rw [hex, hch]

theorem word_pc_off {s : Machine} (base off : Nat)
    (hspc : s.pc = UInt16.ofNat base) (hsum : base + off < 65536) :
    s.pc + UInt16.ofNat off = UInt16.ofNat (base + off) := by
  have hton : s.pc.toNat = base := by
    have : (UInt16.ofNat base).toNat = base :=
      UInt16.toNat_ofNat_of_lt (by have hsz : UInt16.size = 65536 := rfl; rw [hsz]; omega)
    simpa [hspc] using this
  apply UInt16.toNat.inj
  have hsz : UInt16.size = 65536 := rfl
  have hbound : s.pc.toNat + off < 65536 := by rw [hton]; omega
  have hL : (s.pc + UInt16.ofNat off).toNat = base + off := by
    have hw := word_add_toNat s.pc off hbound
    omega
  have hR : (UInt16.ofNat (base + off)).toNat = base + off :=
    UInt16.toNat_ofNat_of_lt (by rw [hsz]; omega)
  exact hL.trans hR.symm

theorem ofNat_ne (a b : Nat)
    (ha : a < 65536) (hb : b < 65536) (hne : a ≠ b) :
    UInt16.ofNat a ≠ UInt16.ofNat b := by
  intro h
  have hsz : UInt16.size = 65536 := rfl
  have hL : (UInt16.ofNat a).toNat = a :=
    UInt16.toNat_ofNat_of_lt (by rw [hsz]; exact ha)
  have hR : (UInt16.ofNat b).toNat = b :=
    UInt16.toNat_ofNat_of_lt (by rw [hsz]; exact hb)
  have : a = b := by
    have hx := congrArg UInt16.toNat h
    rw [hL, hR] at hx
    exact hx
  exact hne this

theorem pc_off_ne {s : Machine} (base i target : Nat)
    (hspc : s.pc = UInt16.ofNat base)
    (hsum : base + i < 65536) (ht : target < 65536)
    (hne : base + i ≠ target) :
    s.pc + UInt16.ofNat i ≠ UInt16.ofNat target := by
  intro h
  have heq := (word_pc_off base i hspc hsum).symm.trans h
  exact ofNat_ne (base + i) target hsum ht hne heq

/-- Subtracting a value that does not exceed `a` does not wrap. -/
theorem word_sub_ge (a b : Word) (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  have ha : a.toNat < 65536 := by
    simpa [show UInt16.size = 65536 from rfl] using UInt16.toNat_lt_size a
  have hb : b.toNat < 65536 := by
    simpa [show UInt16.size = 65536 from rfl] using UInt16.toNat_lt_size b
  have hpow : (2 : Nat) ^ 16 = 65536 := rfl
  have hk : a.toNat - b.toNat < 65536 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) ha
  have hkmod : (a.toNat - b.toNat) % 65536 = a.toNat - b.toNat :=
    Nat.mod_eq_of_lt hk
  have hx : (2 ^ 16 - b.toNat + a.toNat) % 2 ^ 16 = a.toNat - b.toNat := by
    rw [hpow]
    have : 65536 - b.toNat + a.toNat = (a.toNat - b.toNat) + 65536 := by omega
    rw [this, Nat.add_mod]
    have : 65536 % 65536 = 0 := Nat.mod_self 65536
    rw [this, Nat.add_zero, hkmod]
    exact hkmod
  rw [UInt16.toNat_sub]
  exact hx

theorem word_add_one_toNat (w : Word) (h : w.toNat + 1 < 65536) :
    (w + 1).toNat = w.toNat + 1 := by
  have hone : (1 : Word).toNat = 1 := rfl
  have hadd : (w + 1).toNat = (w.toNat + (1 : Word).toNat) % 65536 :=
    UInt16.toNat_add w 1
  rw [hadd, hone, Nat.mod_eq_of_lt h]

/-- Compare-diamond steps for one visit to a P0-style place loop,
given the current `N.toNat`. -/
def p0CmpSteps (n : Nat) : Nat :=
  if n < 10000 then
    if n = 0 then 10 else 16
  else if 32768 ≤ n then 9
  else if n = 10000 then 16
  else 13

theorem p0CmpSteps_zero : p0CmpSteps 0 = 10 := rfl

theorem p0CmpSteps_small {n : Nat} (h0 : 0 < n) (h : n < 10000) :
    p0CmpSteps n = 16 := by
  have : n ≠ 0 := Nat.pos_iff_ne_zero.mp h0
  simp [p0CmpSteps, h, this]

theorem p0CmpSteps_hi {n : Nat} (h : 32768 ≤ n) :
    p0CmpSteps n = 9 := by
  have : ¬ n < 10000 :=
    Nat.not_lt_of_le (Nat.le_trans (by decide : 10000 ≤ 32768) h)
  simp [p0CmpSteps, this, h]

theorem p0CmpSteps_eq : p0CmpSteps 10000 = 16 := rfl

theorem p0CmpSteps_mid {n : Nat} (h1 : 10000 < n) (h2 : n < 32768) :
    p0CmpSteps n = 13 := by
  have hge : ¬ n < 10000 := Nat.not_lt_of_le (Nat.le_of_lt h1)
  have hne : n ≠ 10000 := Nat.ne_of_gt h1
  have hhi : ¬ 32768 ≤ n := Nat.not_le_of_gt h2
  simp [p0CmpSteps, hge, hhi, hne]

theorem p0CmpSteps_le (n : Nat) : p0CmpSteps n + 5 ≤ 21 := by
  unfold p0CmpSteps
  by_cases h1 : n < 10000
  · by_cases h0 : n = 0
    · simp [h1, h0]
    · simp [h1, h0]
  · by_cases h2 : 32768 ≤ n
    · simp [h1, h2]
    · by_cases h3 : n = 10000
      · simp [h1, h2, h3]
      · simp [h1, h2, h3]

/-- Exact step count of the `P0` loop from `P0_LOOP` to `P0_DONE`. -/
def p0PlaceSteps (n : Nat) : Nat :=
  (List.range (n / 10000)).foldl
    (fun acc i => acc + p0CmpSteps (n - i * 10000) + 5) 0
    + p0CmpSteps (n % 10000)

theorem p0PlaceSteps_zero : p0PlaceSteps 0 = 10 := by
  simp [p0PlaceSteps, p0CmpSteps]

theorem p0PlaceSteps_small {n : Nat} (h0 : 0 < n) (h : n < 10000) :
    p0PlaceSteps n = 16 := by
  have hdiv : n / 10000 = 0 := Nat.div_eq_of_lt h
  have hmod : n % 10000 = n := Nat.mod_eq_of_lt h
  rw [p0PlaceSteps, hdiv, hmod, p0CmpSteps_small h0 h]
  rfl

private theorem foldl_p0_le (xs : List Nat) (n acc : Nat) :
    xs.foldl (fun acc i => acc + p0CmpSteps (n - i * 10000) + 5) acc ≤
      acc + 21 * xs.length := by
  induction xs generalizing acc with
  | nil =>
    simp
  | cons i rest ih =>
    simp [List.foldl]
    have hstep := p0CmpSteps_le (n - i * 10000)
    have := ih (acc + p0CmpSteps (n - i * 10000) + 5)
    omega

private theorem length_range (n : Nat) : (List.range n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.length_append, ih]
    rfl

theorem p0PlaceSteps_le (n : Nat) :
    p0PlaceSteps n ≤ 16 + 21 * (n / 10000) := by
  have hfold := foldl_p0_le (List.range (n / 10000)) n 0
  have hlen := length_range (n / 10000)
  have hcmp : p0CmpSteps (n % 10000) ≤ 16 := by
    have := p0CmpSteps_le (n % 10000)
    omega
  have hbound :
      (List.range (n / 10000)).foldl
        (fun acc i => acc + p0CmpSteps (n - i * 10000) + 5) 0 ≤
        21 * (n / 10000) := by
    rw [Nat.zero_add] at hfold
    rw [hlen] at hfold
    exact hfold
  rw [p0PlaceSteps]
  omega

end IntFmt
