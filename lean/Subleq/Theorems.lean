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
