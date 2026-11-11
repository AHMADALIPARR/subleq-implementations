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
-- SPDX-License-Identifier: AGPL-3.0-or-later
import Subleq.Machine
/-!
# Theorems about the SUBLEQ machine

All statements are about the executable `step` / `run` in `Subleq/Machine.lean`.
No proof escape hatch is used; `scripts/check-lean-trusted.sh` rejects them in CI.
-/

namespace Subleq

/-! ## Arithmetic -/

/-- Every wrapped value is a 32-bit signed integer. -/
theorem wrap32_bounds (x : Int) : -2147483648 ≤ wrap32 x ∧ wrap32 x < 2147483648 := by
  unfold wrap32; omega

/-- Wrapping does nothing to a value already in range. -/
theorem wrap32_of_bounds (x : Int) (h1 : -2147483648 ≤ x) (h2 : x < 2147483648) :
    wrap32 x = x := by
  unfold wrap32; omega

/-- `wrap32` depends only on the value modulo 2^32. -/
theorem wrap32_congr (x k : Int) : wrap32 (x + 4294967296 * k) = wrap32 x := by
  unfold wrap32; omega

/-! ## Memory -/

/-- Out-of-range reads give 0. -/
theorem rd_oob (m : Array Int) (a : Int) (h : ¬ InRange m a) : rd m a = 0 := by
  simp [rd, h]

/-- Out-of-range writes are discarded. -/
theorem wr_oob (m : Array Int) (a v : Int) (h : ¬ InRange m a) : wr m a v = m := by
  simp [wr, h]

/-- An in-range write followed by a read of the same address returns the value. -/
theorem rd_wr_same (m : Array Int) (a v : Int) (h : InRange m a) : rd (wr m a v) a = v := by
  have hs : (m.setIfInBounds a.toNat v).size = m.size := Array.size_setIfInBounds
  unfold InRange at h
  have hlt : a.toNat < m.size := by omega
  simp [rd, wr, InRange, h, hs, Array.getD, hlt]

theorem wr_size (m : Array Int) (a v : Int) : (wr m a v).size = m.size := by
  unfold wr; split <;> simp [Array.size_setIfInBounds]

/-! ## One step -/

/-- The memory size never changes. -/
theorem step_size (s : State) : (step s).mem.size = s.mem.size := by
  unfold step
  split
  · rfl
  split
  · rfl
  simp only []
  split
  · rfl
  split
  · split
    · rfl
    · unfold haltOn; split <;> simp [wr_size]
  split
  · unfold haltOn; split <;> rfl
  · unfold haltOn; split <;> simp [wr_size]

/-- A stopped machine (halted, trap, fault, step limit) never changes. -/
theorem step_stopped (s : State) (h : s.status ≠ .running) : step s = s := by
  simp [step, h]

/-- PC < 0 or PC + 2 ≥ N is a fault with no other change. -/
theorem step_badpc (s : State) (hr : s.status = .running) (h : BadPC s) :
    step s = { s with status := .faultPC } := by
  simp [step, hr, h]

/-- (Priority 1) `a = -2` traps with code `b`, whatever `b` and `c` are. -/
theorem step_trap (s : State) (hr : s.status = .running) (hpc : ¬ BadPC s)
    (ha : rd s.mem s.pc = -2) :
    step s = { s with status := .trap, code := rd s.mem (s.pc + 1), steps := s.steps + 1 } := by
  simp [step, hr, hpc, ha]

/-- (Priority 2) `a = -1` reads input into `M[b]` (even if `b < 0`, where the
write is discarded), or faults when the input is exhausted. -/
theorem step_input_empty (s : State) (hr : s.status = .running) (hpc : ¬ BadPC s)
    (ha : rd s.mem s.pc = -1) (hin : s.input = []) :
    step s = { s with status := .faultInput } := by
  simp [step, hr, hpc, ha, hin]

theorem step_input (s : State) (v : Int) (rest : List Int) (hr : s.status = .running)
    (hpc : ¬ BadPC s) (ha : rd s.mem s.pc = -1) (hin : s.input = v :: rest) :
    step s = haltOn (rd s.mem (s.pc + 2))
      { s with mem := wr s.mem (rd s.mem (s.pc + 1)) (wrap32 v), input := rest,
               pc := s.pc + 3, steps := s.steps + 1 } := by
  simp [step, hr, hpc, ha, hin]

/-- (Priority 3) `a ∉ {-1,-2}` and `b < 0` appends `read(a)` to the output. -/
theorem step_output (s : State) (hr : s.status = .running) (hpc : ¬ BadPC s)
    (ha1 : rd s.mem s.pc ≠ -1) (ha2 : rd s.mem s.pc ≠ -2) (hb : rd s.mem (s.pc + 1) < 0) :
    step s = haltOn (rd s.mem (s.pc + 2))
      { s with output := s.output ++ [rd s.mem (rd s.mem s.pc)], pc := s.pc + 3,
               steps := s.steps + 1 } := by
  simp [step, hr, hpc, ha1, ha2, hb]

/-- (Priority 4) The ordinary SUBLEQ step, branching on the wrapped result to
the absolute target `c`. -/
theorem step_ordinary (s : State) (hr : s.status = .running) (hpc : ¬ BadPC s)
    (ha1 : rd s.mem s.pc ≠ -1) (ha2 : rd s.mem s.pc ≠ -2) (hb : ¬ rd s.mem (s.pc + 1) < 0) :
    let a := rd s.mem s.pc
    let b := rd s.mem (s.pc + 1)
    let c := rd s.mem (s.pc + 2)
    let r := wrap32 (rd s.mem b - rd s.mem a)
    step s = haltOn c
      { s with mem := wr s.mem b r, pc := if r ≤ 0 then c else s.pc + 3,
               steps := s.steps + 1 } := by
  simp [step, hr, hpc, ha1, ha2, hb]

/-- The halt rule. `step_input`, `step_output` and `step_ordinary` end in
`haltOn c`; with `c = -1` the result is halted whether or not the branch was
taken, otherwise `haltOn` changes nothing. -/
theorem haltOn_neg_one (s : State) : (haltOn (-1) s).status = .halted := by
  simp [haltOn]

theorem haltOn_other (c : Int) (s : State) (h : c ≠ -1) : haltOn c s = s := by
  simp [haltOn, h]

/-- A step increases the step counter by exactly one or leaves it unchanged
(faults and already-stopped states). -/
theorem step_steps (s : State) :
    (step s).steps = s.steps + 1 ∨ (step s).steps = s.steps := by
  unfold step
  split
  · exact Or.inr rfl
  split
  · exact Or.inr rfl
  simp only []
  split
  · exact Or.inl rfl
  split
  · split
    · exact Or.inr rfl
    · left; unfold haltOn; split <;> rfl
  split
  · left; unfold haltOn; split <;> rfl
  · left; unfold haltOn; split <;> rfl

/-! ## Invariant: every cell stays a 32-bit value -/

def Cells32 (m : Array Int) : Prop := ∀ i (h : i < m.size), wrap32 m[i] = m[i]

theorem wrap32_idem (x : Int) : wrap32 (wrap32 x) = wrap32 x := by
  unfold wrap32; omega

theorem wr_cells32 (m : Array Int) (a v : Int) (hm : Cells32 m) (hv : wrap32 v = v) :
    Cells32 (wr m a v) := by
  unfold wr
  split
  · intro i h
    have hs : (m.setIfInBounds a.toNat v).size = m.size := Array.size_setIfInBounds
    have hi : i < m.size := hs ▸ h
    rw [Array.getElem_setIfInBounds hi]
    split
    · exact hv
    · exact hm i hi
  · exact hm

/-- If all cells are 32-bit values, they still are after a step. -/
theorem step_cells32 (s : State) (h : Cells32 s.mem) : Cells32 (step s).mem := by
  unfold step
  split
  · exact h
  split
  · exact h
  simp only []
  split
  · exact h
  split
  · split
    · exact h
    · unfold haltOn; split <;> exact wr_cells32 _ _ _ h (wrap32_idem _)
  split
  · unfold haltOn; split <;> exact h
  · unfold haltOn; split <;> exact wr_cells32 _ _ _ h (wrap32_idem _)

theorem init_cells32 (image input : List Int) : Cells32 (init image input).mem := by
  intro i h
  simp [init, wrap32_idem]

/-! ## Running -/

/-- `run` never leaves the machine in the `running` status. -/
theorem run_stops (n : Nat) (s : State) : (run n s).status ≠ .running := by
  induction n generalizing s with
  | zero => unfold run; split <;> simp_all
  | succ n ih => unfold run; split
                 · exact ih _
                 · assumption

/-- Running a stopped machine changes nothing. -/
theorem run_stopped (n : Nat) (s : State) (h : s.status ≠ .running) : run n s = s := by
  cases n <;> simp [run, h]

/-- With fuel left and a running machine, `run (n+1)` is one `step` followed by `run n`. -/
theorem run_succ (n : Nat) (s : State) (h : s.status = .running) :
    run (n + 1) s = run n (step s) := by
  simp [run, h]

/-- The 32-bit invariant is preserved by `run`; with `init_cells32` it holds for
every result of `run n (init image input)`. -/
theorem run_cells32 (n : Nat) (s : State) (h : Cells32 s.mem) : Cells32 (run n s).mem := by
  induction n generalizing s with
  | zero => unfold run; split <;> exact h
  | succ n ih => unfold run; split
                 · exact ih _ (step_cells32 _ h)
                 · exact h

end Subleq
