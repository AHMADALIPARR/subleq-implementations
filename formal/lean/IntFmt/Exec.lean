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

theorem runN_add (s : Machine) (m n : Nat) :
    runN s (m + n) = runN (runN s m) n := by
  induction m generalizing s with
  | zero => simp [runN_zero]
  | succ m ih =>
    rw [Nat.succ_add, runN_succ, runN_succ]
    split
    · cases n with
      | zero => simp [runN_zero]
      | succ _ => simp [runN_succ]
    · exact ih (step s)

/-- How a fuel-bounded run ended. -/
inductive HaltKind where
  | programHalt    -- `halted` is already set, or `pc ≥ 32768` (program HALT)
  | fuelExhausted  -- fuel ran out while the machine was still running
  deriving DecidableEq, Repr

/-- Result of a counted run: final state, exact steps taken, and why it stopped.
`steps` is the number of `step` applications performed. Fuel exhaustion
is distinguished from a program HALT (including jumping to `pc ≥ 32768`). -/
structure RunResult where
  state : Machine
  steps : Nat
  kind : HaltKind

/-- Counted execution: `fuel = 0` on a still-running machine is
`fuelExhausted` and does **not** force `halted = true`. If the machine
has already taken a program HALT (or the flag is set), the kind is
`programHalt` and `halted` is set. -/
def runCounted (s : Machine) : Nat → RunResult
  | 0 =>
    if s.halted || 32768 ≤ s.pc.toNat then
      { state := { s with halted := true }, steps := 0, kind := .programHalt }
    else
      { state := s, steps := 0, kind := .fuelExhausted }
  | n + 1 =>
    if s.halted || 32768 ≤ s.pc.toNat then
      { state := { s with halted := true }, steps := 0, kind := .programHalt }
    else
      let r := runCounted (step s) n
      { r with steps := r.steps + 1 }

theorem runCounted_zero_go (s : Machine)
    (hh : s.halted = false) (hpc : s.pc.toNat < 32768) :
    runCounted s 0 = { state := s, steps := 0, kind := .fuelExhausted } := by
  have : ¬ (s.halted || 32768 ≤ s.pc.toNat) := by
    simp [hh, Nat.not_le_of_gt hpc]
  simp [runCounted, this]

theorem runCounted_zero_halt (s : Machine)
    (h : s.halted = true ∨ 32768 ≤ s.pc.toNat) :
    runCounted s 0 =
      { state := { s with halted := true }, steps := 0, kind := .programHalt } := by
  have : s.halted || 32768 ≤ s.pc.toNat := by
    cases h with
    | inl hh => simp [hh]
    | inr hp => simp [hp]
  simp [runCounted, this]

theorem runCounted_succ_go (s : Machine) (n : Nat)
    (hh : s.halted = false) (hpc : s.pc.toNat < 32768) :
    runCounted s (n + 1) =
      let r := runCounted (step s) n
      { r with steps := r.steps + 1 } := by
  have : ¬ (s.halted || 32768 ≤ s.pc.toNat) := by
    simp [hh, Nat.not_le_of_gt hpc]
  simp [runCounted, this]

theorem runCounted_succ_halt (s : Machine) (n : Nat)
    (h : s.halted = true ∨ 32768 ≤ s.pc.toNat) :
    runCounted s (n + 1) =
      { state := { s with halted := true }, steps := 0, kind := .programHalt } := by
  have : s.halted || 32768 ≤ s.pc.toNat := by
    cases h with
    | inl hh => simp [hh]
    | inr hp => simp [hp]
  simp [runCounted, this]

/-- A program-HALT result never claims fuel exhaustion. -/
theorem runCounted_programHalt_not_exhaust (s : Machine) (fuel : Nat)
    (h : (runCounted s fuel).kind = HaltKind.programHalt) :
    (runCounted s fuel).kind ≠ HaltKind.fuelExhausted := by
  intro hf
  cases h.symm.trans hf

/-- If counted execution reports a program HALT, the final state is halted
and we took at most `fuel` steps. -/
theorem runCounted_programHalt_le (s : Machine) (fuel : Nat)
    (h : (runCounted s fuel).kind = HaltKind.programHalt) :
    (runCounted s fuel).state.halted = true ∧
    (runCounted s fuel).steps ≤ fuel := by
  induction fuel generalizing s with
  | zero =>
    cases hb : (s.halted || 32768 ≤ s.pc.toNat) with
    | false =>
      have : (runCounted s 0).kind = HaltKind.fuelExhausted := by
        simp [runCounted, hb]
      exact absurd (this.symm.trans h) (by decide)
    | true =>
      simp [runCounted, hb]
  | succ n ih =>
    cases hb : (s.halted || 32768 ≤ s.pc.toNat) with
    | true =>
      simp [runCounted, hb]
    | false =>
      have hs := ih (step s)
      have hr : runCounted s (n + 1) =
          let r := runCounted (step s) n
          { r with steps := r.steps + 1 } := by
        simp [runCounted, hb]
      have hk : (runCounted (step s) n).kind = HaltKind.programHalt := by
        simpa [hr] using h
      have ⟨hh, hle⟩ := hs hk
      refine ⟨?_, ?_⟩
      · simpa [hr] using hh
      · have : (runCounted s (n + 1)).steps = (runCounted (step s) n).steps + 1 := by
          simp [hr]
        omega

end IntFmt.Subleq
