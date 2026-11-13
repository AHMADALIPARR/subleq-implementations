/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Milestone 1: decimal correctness for every signed 16-bit integer.
Milestone 2: min-int safety via unsigned magnitude (no signed 16-bit negation).

Kernel proofs only (induction, omega, simp). Exhaustive executable
sweep is supporting evidence in `IntFmt.Evidence`, not `native_decide`.
-/

namespace IntFmt

def inInt16 (n : Int) : Prop := -32768 ≤ n ∧ n ≤ 32767

/-- Repeated-subtraction divmod (the SUBLEQ microcode algorithm). -/
def divmodSub (n base : Nat) : Nat × Nat :=
  if h : 2 ≤ base ∧ base ≤ n then
    let p := divmodSub (n - base) base
    (p.1 + 1, p.2)
  else
    (0, n)
termination_by n
decreasing_by
  exact Nat.sub_lt (by omega) (by omega)

theorem divmodSub_eq (n base : Nat) (hb : 2 ≤ base) :
    divmodSub n base = (n / base, n % base) := by
  refine Nat.strongRecOn n fun n ih => ?_
  unfold divmodSub
  by_cases h : 2 ≤ base ∧ base ≤ n
  · have hlt : n - base < n := Nat.sub_lt (by omega) (by omega)
    simp [h]
    have ih' := ih (n - base) hlt
    rw [ih']
    have hb0 : 0 < base := by omega
    have hle : base ≤ n := h.2
    constructor
    · have : n / base = (n - base) / base + 1 := by
        rw [Nat.div_eq_ite]
        simp [hb0, hle]
      exact this.symm
    · exact (Nat.mod_eq_sub_mod hle).symm
  · have hlt : n < base := by
      have : ¬ base ≤ n := fun hle => h ⟨hb, hle⟩
      exact Nat.lt_of_not_ge this
    simp [h]
    constructor
    · exact (Nat.div_eq_of_lt hlt).symm
    · exact (Nat.mod_eq_of_lt hlt).symm

def valueFrom (acc : Nat) (ds : List Nat) (base : Nat) : Nat :=
  ds.foldl (fun a d => a * base + d) acc

def value (ds : List Nat) (base : Nat) : Nat :=
  valueFrom 0 ds base

theorem valueFrom_append_singleton (acc d base : Nat) (xs : List Nat) :
    valueFrom acc (xs ++ [d]) base = valueFrom acc xs base * base + d := by
  induction xs generalizing acc with
  | nil =>
    simp [valueFrom, List.foldl]
  | cons x xs ih =>
    simpa [valueFrom, List.foldl] using ih (acc * base + x)

def digitsLSD (n base : Nat) : List Nat :=
  if h : 2 ≤ base ∧ base ≤ n then
    (divmodSub n base).2 :: digitsLSD (divmodSub n base).1 base
  else
    [n]
termination_by n
decreasing_by
  have eq := divmodSub_eq n base h.1
  have hlt : n / base < n := Nat.div_lt_self (by omega) (by omega)
  exact lt_of_eq_of_lt (by rw [eq]) hlt

def uToDigits (n base : Nat) : List Nat :=
  (digitsLSD n base).reverse

theorem value_uToDigits (n base : Nat) (hb : 2 ≤ base) :
    value (uToDigits n base) base = n := by
  suffices h : value ((digitsLSD n base).reverse) base = n by
    simpa [uToDigits] using h
  refine Nat.strongRecOn n fun n ih => ?_
  unfold digitsLSD
  by_cases h : 2 ≤ base ∧ base ≤ n
  · have eq := divmodSub_eq n base hb
    have hlt : n / base < n := Nat.div_lt_self (by omega) (by omega)
    simp [h, eq]
    have ih' : value ((digitsLSD (n / base) base).reverse) base = n / base :=
      ih (n / base) hlt
    have app := valueFrom_append_singleton 0 (n % base) base
      ((digitsLSD (n / base) base).reverse)
    simp [value] at app ih' ⊢
    rw [app, ih']
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n base
  · have : ¬ base ≤ n := fun hle => h ⟨hb, hle⟩
    have hlt : n < base := Nat.lt_of_not_ge this
    simp [h, value, valueFrom, List.foldl]

def digitChar (d : Nat) : Char :=
  Char.ofNat ('0'.toNat + d)

def uToDec (n : Nat) : String :=
  String.ofList ((uToDigits n 10).map digitChar)

/-- Canonical decimal (spec). `Int.natAbs` is defined on unbounded Lean ints. -/
def intToDec (n : Int) : String :=
  if n < 0 then "-" ++ uToDec n.natAbs else uToDec n.toNat

/-- Two's-complement 16-bit bit pattern as a `Nat`. -/
def int16Bits (n : Int) (_h : inInt16 n) : Nat :=
  if n ≥ 0 then n.toNat else (n + 65536).toNat

/-- Unsigned 16-bit magnitude: `0 - bits` modulo 65536 (defined at -32768). -/
def unsignedMag (n : Int) (h : inInt16 n) : Nat :=
  if n ≥ 0 then n.toNat
  else (65536 - int16Bits n h) % 65536

theorem eq_neg_natAbs_of_neg {n : Int} (hn : n < 0) :
    n = - (n.natAbs : Int) := by
  cases Int.natAbs_eq n with
  | inl hp =>
    have : 0 ≤ n := by
      rw [hp]
      exact Int.natCast_nonneg _
    exact (Int.not_le.mpr hn this).elim
  | inr hn' =>
    exact hn'

theorem toNat_nat_sub {a b : Nat} (h : b ≤ a) :
    ((a : Int) - (b : Int)).toNat = a - b := by
  have : (a : Int) - (b : Int) = Int.ofNat (a - b) := by
    exact (Int.ofNat_sub h).symm
  rw [this]
  exact Int.toNat_natCast (a - b)

theorem unsignedMag_eq_natAbs {n : Int} (h : inInt16 n) :
    unsignedMag n h = n.natAbs := by
  unfold unsignedMag
  by_cases hn : 0 ≤ n
  · simp [hn]
    -- n.toNat = n.natAbs
    have e : (n.natAbs : Int) = n := Int.natAbs_of_nonneg hn
    calc
      n.toNat = (n.natAbs : Int).toNat := by rw [e]
      _ = n.natAbs := Int.toNat_natCast _
  · have hn' : n < 0 := Int.lt_of_not_ge hn
    unfold int16Bits
    have : ¬ n ≥ 0 := fun hge => (Int.not_le.mpr hn') hge
    simp [this]
    have hneg : n = - (n.natAbs : Int) := eq_neg_natAbs_of_neg hn'
    have hkU : n.natAbs ≤ 32768 := by
      have hlo : -32768 ≤ n := h.1
      have : (n.natAbs : Int) ≤ 32768 := by
        rw [hneg] at hlo
        omega
      exact Int.ofNat_le.mp this
    have hsum : (n + 65536 : Int) = (65536 : Int) - (n.natAbs : Int) := by
      omega
    have hbits : (n + 65536).toNat = 65536 - n.natAbs := by
      rw [hsum]
      exact toNat_nat_sub (by omega : n.natAbs ≤ 65536)
    rw [hbits]
    have hdiff : 65536 - (65536 - n.natAbs) = n.natAbs :=
      Nat.sub_sub_self (by omega : n.natAbs ≤ 65536)
    rw [hdiff]
    exact Nat.mod_eq_of_lt (by omega : n.natAbs < 65536)

def i16toa (n : Int) (h : inInt16 n) : String :=
  if n < 0 then "-" ++ uToDec (unsignedMag n h) else uToDec n.toNat

/-- Milestone 1 & 2: implementation matches the canonical decimal spec. -/
theorem i16toa_eq_intToDec (n : Int) (h : inInt16 n) :
    i16toa n h = intToDec n := by
  unfold i16toa intToDec
  by_cases hn : n < 0
  · simp [hn, unsignedMag_eq_natAbs h]
  · have hge : 0 ≤ n := Int.not_lt.mp hn
    have e : n.toNat = n.natAbs := by
      have e' : (n.natAbs : Int) = n := Int.natAbs_of_nonneg hge
      calc
        n.toNat = (n.natAbs : Int).toNat := by rw [e']
        _ = n.natAbs := Int.toNat_natCast _
    simp [hn, e]

/-- Milestone 2 at the overflowing edge: defined and equal to the spec. -/
theorem i16toa_minInt :
    i16toa (-32768) ⟨by omega, by omega⟩ = intToDec (-32768) :=
  i16toa_eq_intToDec _ _

end IntFmt
