/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Fuel-bounded execution without the “fuel 0 forces halt” behaviour, plus
the single-instruction `step` characterisation used by the macro lemmas.
-/

import IntFmt.Subleq

namespace IntFmt.Subleq

/-- Like `run`, but `runN s 0 = s` (does not force a halt). -/
def runN : Machine → Nat → Machine
  | s, 0 => s
  | s, n + 1 =>
    if s.halted || 32768 ≤ s.pc.toNat then
      { s with halted := true }
    else
      runN (step s) n

@[simp] theorem runN_zero (s : Machine) : runN s 0 = s := rfl

theorem runN_succ (s : Machine) (n : Nat) :
    runN s (n + 1) =
      if s.halted || 32768 ≤ s.pc.toNat then
        { s with halted := true }
      else
        runN (step s) n := rfl

theorem runN_succ_go (s : Machine) (n : Nat)
    (hh : s.halted = false) (hpc : s.pc.toNat < 32768) :
    runN s (n + 1) = runN (step s) n := by
  have : ¬ (s.halted || 32768 ≤ s.pc.toNat) := by
    simp [hh, Nat.not_le_of_gt hpc]
  simp [runN_succ, this]

theorem runN_succ_halt (s : Machine) (n : Nat)
    (h : s.halted = true ∨ 32768 ≤ s.pc.toNat) :
    runN s (n + 1) = { s with halted := true } := by
  have : s.halted || 32768 ≤ s.pc.toNat := by
    cases h with
    | inl hh => simp [hh]
    | inr hp => simp [hp]
  simp [runN_succ, this]

/-- If the machine has already halted by program HALT (or the flag),
further `run` fuel only sets `halted`. -/
theorem run_of_done (s : Machine) (fuel : Nat)
    (h : s.halted = true ∨ 32768 ≤ s.pc.toNat) :
    run s fuel = { s with halted := true } := by
  cases fuel with
  | zero =>
    simp [run]
  | succ k =>
    have : s.halted || 32768 ≤ s.pc.toNat := by
      cases h with
      | inl hh => simp [hh]
      | inr hp => simp [hp]
    simp [run, this]

/-- Characterisation of a non-I/O SUBLEQ step. -/
theorem step_sub {s : Machine} {a b c : Word}
    (hh : s.halted = false)
    (hpc : s.pc.toNat < 32768)
    (ha : s.mem.get s.pc = a)
    (hb : s.mem.get (s.pc + 1) = b)
    (hc : s.mem.get (s.pc + 2) = c)
    (hna : a ≠ 0xFFFF)
    (hnb : b ≠ 0xFFFF) :
    step s =
      let r := s.mem.get b - s.mem.get a
      { s with
        mem := s.mem.set b r
        pc := if r = 0 || 0x8000 ≤ r then c else s.pc + 3 } := by
  unfold step
  have hhalt : (s.halted || decide (32768 ≤ s.pc.toNat)) = false := by
    simp [hh, Nat.not_le_of_gt hpc]
  simp [hhalt, ha, hb, hc, hna, hnb]

/-- Operand `-1` (0xFFFF) never appears in the intfmt instruction stream
as an I/O operand; this helper just records the two disequalities. -/
theorem not_io {a b : Word} (ha : a ≠ 0xFFFF) (hb : b ≠ 0xFFFF) :
    a ≠ 0xFFFF ∧ b ≠ 0xFFFF := ⟨ha, hb⟩

theorem runN_one (s : Machine)
    (hh : s.halted = false) (hpc : s.pc.toNat < 32768) :
    runN s 1 = step s := by
  rw [runN_succ_go s 0 hh hpc, runN_zero]

theorem runN_succ_eq (s : Machine) (n : Nat)
    (hh : s.halted = false) (hpc : s.pc.toNat < 32768) :
    runN s (n + 1) = runN (step s) n :=
  runN_succ_go s n hh hpc

end IntFmt.Subleq
