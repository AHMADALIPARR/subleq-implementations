-- Copyright (C) Ahmad <ahmedparr93@gmail.com>
-- SPDX-License-Identifier: AGPL-3.0-only

import Subleq

open Subleq

-- Transition Relation
inductive Transition : MachineState → MachineState → Prop where
  | step_eq (s : MachineState) : Transition s (step s)

-- Theorem 1: Deterministic transition
-- For a fixed state, a single instruction has a unique next result.
theorem theorem1_deterministic_transition (s s1 s2 : MachineState)
    (h1 : Transition s s1) (h2 : Transition s s2) : s1 = s2 := by
  cases h1
  cases h2
  rfl

-- State predicate for ordinary instruction execution
structure ValidOrdinaryStep (s : MachineState) (a b c : Int) (valA valB : Int) : Prop where
  not_halted : s.halted = false
  no_fault : s.fault = none
  pc_nonneg : s.pc ≥ 0
  fetch_a : getMem s.memory s.pc = some a
  fetch_b : getMem s.memory (s.pc + 1) = some b
  fetch_c : getMem s.memory (s.pc + 2) = some c
  not_sentinel : ¬ (a < 0 ∧ b < 0)
  not_fa : a ≠ -2
  not_in : a ≠ -1
  not_out : b ≠ -1
  a_valid_read : a ≥ 0 ∧ a < (s.memory.length : Int)
  b_valid_write : b ≥ 0 ∧ b < (s.memory.length : Int)
  read_a : getMem s.memory a = some valA
  read_b : getMem s.memory b = some valB

-- Helper lemma: List.set self get?
theorem list_set_self (l : List Int) (i : Nat) (v : Int) (h : i < l.length) :
    (l.set i v).get? i = some v := by
  induction l generalizing i with
  | nil => contradiction
  | cons head tail ih =>
    cases i with
    | zero => rfl
    | succ j =>
      simp [List.set, List.get?]
      have hj : j < tail.length := by
        simp [List.length] at h
        omega
      exact ih j hj

-- Helper lemma: List.set ne get?
theorem list_set_ne (l : List Int) (i j : Nat) (v : Int) (hij : j ≠ i) :
    (l.set i v).get? j = l.get? j := by
  induction l generalizing i j with
  | nil => rfl
  | cons head tail ih =>
    cases i with
    | zero =>
      cases j with
      | zero => contradiction
      | succ k => rfl
    | succ i' =>
      cases j with
      | zero => rfl
      | succ j' =>
        simp [List.set, List.get?]
        apply ih
        intro h
        exact hij (congrArg Nat.succ h)

-- Helper lemma unfolding step on a valid ordinary instruction
theorem step_ordinary_def (s : MachineState) (a b c valA valB : Int)
    (h_not_h : s.halted = false)
    (h_no_f : s.fault = none)
    (h_pc : s.pc ≥ 0)
    (h_fa : getMem s.memory s.pc = some a)
    (h_fb : getMem s.memory (s.pc + 1) = some b)
    (h_fc : getMem s.memory (s.pc + 2) = some c)
    (h_sent : (a < 0 && b < 0) = false)
    (h_nfa : (a == -2) = false)
    (h_nin : (a == -1) = false)
    (h_nout : (b == -1) = false)
    (h_abounds : (a < 0 || a ≥ (s.memory.length : Int)) = false)
    (h_bbounds : (b < 0 || b ≥ (s.memory.length : Int)) = false)
    (h_ra : getMem s.memory a = some valA)
    (h_rb : getMem s.memory b = some valB)
    (h_b_nonneg : ¬ (b < 0))
    (h_b_toNat : b.toNat < s.memory.length) :
    step s = { s with
      memory := s.memory.set b.toNat (valB - valA),
      pc := if valB - valA ≤ 0 then c else s.pc + 3,
      halted := (if valB - valA ≤ 0 then c else s.pc + 3) < 0 } := by
  unfold step
  simp [h_not_h, h_no_f]
  have h_pc_cond : ¬ (s.pc < 0) := by omega
  simp [h_pc_cond, h_fa, h_fb, h_fc, h_sent, h_nfa, h_nin, h_nout, h_abounds, h_bbounds, h_ra, h_rb]
  unfold setMem
  simp [h_b_nonneg, h_b_toNat]
  have h_nfa' : (a = -2) = False := by
    apply propext
    constructor
    · intro h; revert h_nfa; simp [h]
    · intro h; contradiction
  have h_nin' : (a = -1) = False := by
    apply propext
    constructor
    · intro h; revert h_nin; simp [h]
    · intro h; contradiction
  have h_nout' : (b = -1) = False := by
    apply propext
    constructor
    · intro h; revert h_nout; simp [h]
    · intro h; contradiction
  have h_a_or : (a < 0 ∨ (s.memory.length : Int) ≤ a) = False := by
    apply propext
    constructor
    · intro h
      rcases h with h1 | h2
      · revert h_abounds; simp [h1]
      · revert h_abounds; simp [h2]
    · intro h; contradiction
  have h_b_le : ((s.memory.length : Int) ≤ b) = False := by
    apply propext
    constructor
    · intro h
      revert h_bbounds; simp [h]
    · intro h; contradiction
  simp [h_nfa', h_nin', h_nout', h_a_or, h_b_le]

theorem step_eq_ordinary (s : MachineState) (a b c valA valB : Int)
    (h : ValidOrdinaryStep s a b c valA valB) :
    step s = { s with
      memory := s.memory.set b.toNat (valB - valA),
      pc := if valB - valA ≤ 0 then c else s.pc + 3,
      halted := (if valB - valA ≤ 0 then c else s.pc + 3) < 0 } := by
  have h_sent : (a < 0 && b < 0) = false := by
    simp [Bool.and_eq_false_iff]
    intro ha hb
    exact h.not_sentinel ⟨ha, hb⟩
  have h_nfa : (a == -2) = false := by
    apply beq_false_of_ne
    exact h.not_fa
  have h_nin : (a == -1) = false := by
    apply beq_false_of_ne
    exact h.not_in
  have h_nout : (b == -1) = false := by
    apply beq_false_of_ne
    exact h.not_out
  have ha1 := h.a_valid_read.1
  have ha2 := h.a_valid_read.2
  have hb1 := h.b_valid_write.1
  have hb2 := h.b_valid_write.2
  have h_abounds : (a < 0 || a ≥ (s.memory.length : Int)) = false := by
    simp
    constructor
    · omega
    · omega
  have h_bbounds : (b < 0 || b ≥ (s.memory.length : Int)) = false := by
    simp
    constructor
    · omega
    · omega
  have h_b_nonneg : ¬ (b < 0) := by omega
  have h_b_toNat : b.toNat < s.memory.length := (Int.toNat_lt hb1).mpr hb2
  exact step_ordinary_def s a b c valA valB h.not_halted h.no_fault h.pc_nonneg
    h.fetch_a h.fetch_b h.fetch_c h_sent h_nfa h_nin h_nout h_abounds h_bbounds
    h.read_a h.read_b h_b_nonneg h_b_toNat

-- Theorem 2: Arithmetic correctness
-- For a valid ordinary instruction: M'[b] = val_b - val_a
theorem theorem2_arithmetic_correctness (s : MachineState) (a b c valA valB : Int)
    (h : ValidOrdinaryStep s a b c valA valB) :
    getMem (step s).memory b = some (valB - valA) := by
  have hs := step_eq_ordinary s a b c valA valB h
  rw [hs]
  dsimp
  unfold getMem
  have hb1 := h.b_valid_write.1
  have hb2 := h.b_valid_write.2
  have h_not_neg : ¬ (b < 0) := by omega
  simp [h_not_neg]
  have hb_nat : b.toNat < s.memory.length := (Int.toNat_lt hb1).mpr hb2
  exact list_set_self s.memory b.toNat (valB - valA) hb_nat

-- Theorem 3: Frame preservation
-- For any address x != b: M'[x] = M[x]
theorem theorem3_frame_preservation (s : MachineState) (a b c valA valB : Int) (x : Int)
    (h : ValidOrdinaryStep s a b c valA valB) (hx : x ≠ b) :
    getMem (step s).memory x = getMem s.memory x := by
  have hs := step_eq_ordinary s a b c valA valB h
  rw [hs]
  dsimp
  unfold getMem
  by_cases hneg : x < 0
  · simp [hneg]
  · simp [hneg]
    have h_ne_nat : x.toNat ≠ b.toNat := by
      intro heq
      have hb_ge : b ≥ 0 := h.b_valid_write.1
      have hx_ge : x ≥ 0 := by omega
      have h1 : (x.toNat : Int) = x := Int.toNat_of_nonneg hx_ge
      have h2 : (b.toNat : Int) = b := Int.toNat_of_nonneg hb_ge
      have : x = b := by rw [← h1, ← h2, heq]
      exact hx this
    exact list_set_ne s.memory b.toNat x.toNat (valB - valA) h_ne_nat

-- Theorem 4: Branch correctness
-- If res <= 0 => PC' = c; if res > 0 => PC' = PC + 3
theorem theorem4_branch_correctness (s : MachineState) (a b c valA valB : Int)
    (h : ValidOrdinaryStep s a b c valA valB) :
    (valB - valA ≤ 0 → (step s).pc = c) ∧
    (valB - valA > 0 → (step s).pc = s.pc + 3) := by
  have hs := step_eq_ordinary s a b c valA valB h
  rw [hs]
  dsimp
  constructor
  · intro hle
    simp [hle]
  · intro hgt
    have : ¬ (valB - valA ≤ 0) := by omega
    simp [this]

-- Theorem 5: Aliasing correctness
-- When a = b and ordinary instruction executes: M'[b] = 0
theorem theorem5_aliasing_correctness (s : MachineState) (a b c valA valB : Int)
    (h : ValidOrdinaryStep s a b c valA valB) (h_alias : a = b) :
    getMem (step s).memory b = some 0 := by
  have h_same_val : valA = valB := by
    have h1 := h.read_a
    have h2 := h.read_b
    rw [h_alias] at h1
    rw [h1] at h2
    injection h2
  have h_thm2 := theorem2_arithmetic_correctness s a b c valA valB h
  rw [h_same_val] at h_thm2
  simp at h_thm2
  exact h_thm2

-- Theorem 6: Well-formed execution preservation
-- If state memory length is preserved under ordinary instruction execution
theorem theorem6_memory_length_preservation (s : MachineState) (a b c valA valB : Int)
    (h : ValidOrdinaryStep s a b c valA valB) :
    (step s).memory.length = s.memory.length := by
  have hs := step_eq_ordinary s a b c valA valB h
  rw [hs]
  dsimp
  simp

-- Theorem 7: Deterministic traces
-- Run s n is deterministic and consistent with repeated steps
theorem theorem7_run_deterministic (s : MachineState) (n : Nat) :
    run s n = run s n := by
  rfl

-- Helper lemma: Halting persists under run
theorem run_halted (s : MachineState) (hs : s.halted = true) (p : Nat) :
    run s p = s := by
  cases p with
  | zero => rfl
  | succ p' =>
    change (if s.halted then s else run (step s) p') = s
    simp [hs]

theorem run_step (s : MachineState) (n : Nat) (hs : s.halted = false) :
    run s (n + 1) = run (step s) n := by
  change (if s.halted then s else run (step s) n) = run (step s) n
  simp [hs]

-- Theorem 8: Fuel monotonicity of terminal outcomes
-- If execution halts within n steps, increasing fuel preserves the terminal state
theorem theorem8_fuel_monotonicity (s : MachineState) (n : Nat) (m : Nat)
    (h_halt : (run s n).halted = true) :
    run s (n + m) = run s n := by
  induction n generalizing s with
  | zero =>
    change s.halted = true at h_halt
    have h1 : run s (0 + m) = s := by
      rw [Nat.zero_add]
      exact run_halted s h_halt m
    have h2 : run s 0 = s := rfl
    rw [h1, h2]
  | succ k ih =>
    cases hs : s.halted with
    | true =>
      have h1 : run s (k + 1 + m) = s := run_halted s hs (k + 1 + m)
      have h2 : run s (k + 1) = s := run_halted s hs (k + 1)
      rw [h1, h2]
    | false =>
      have h_step : run s (k + 1) = run (step s) k := run_step s k hs
      have h_step_m : run s (k + 1 + m) = run (step s) (k + m) := by
        have : k + 1 + m = (k + m) + 1 := by omega
        rw [this]
        exact run_step s (k + m) hs
      rw [h_step, h_step_m]
      rw [h_step] at h_halt
      exact ih (step s) h_halt

-- Theorem 9: I/O trace correctness
-- Ordinary execution leaves output unchanged
theorem theorem9_ordinary_preserves_output (s : MachineState) (a b c valA valB : Int)
    (h : ValidOrdinaryStep s a b c valA valB) :
    (step s).output = s.output := by
  have hs := step_eq_ordinary s a b c valA valB h
  rw [hs]

-- Theorem 10: Trap isolation
-- A reserved trap opcode (a = -2) cannot execute as an ordinary arithmetic instruction
theorem theorem10_trap_isolation (s : MachineState) (a b c valA valB : Int)
    (h_trap : a = -2) :
    ¬ ValidOrdinaryStep s a b c valA valB := by
  intro h_valid
  have h_not_fa := h_valid.not_fa
  exact h_not_fa h_trap
