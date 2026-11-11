-- SPDX-License-Identifier: AGPL-3.0-or-later
/-!
# SUBLEQ machine (directive semantics)

Executable definitions of the machine in `semantics/subleq-spec.md`.
The same `step` and `run` are used by the theorems in `Subleq/Theorems.lean`
and by the `subleq-lean` executable (`Main.lean`), so the tested binary runs
exactly the definitions the theorems are about.
-/

namespace Subleq

/-- Reduce an integer to the 32-bit signed two's-complement range. -/
def wrap32 (x : Int) : Int := (x + 2147483648) % 4294967296 - 2147483648

inductive Status where
  | running
  | halted
  | trap
  | faultPC
  | faultInput
  | stepLimit
  deriving DecidableEq, Repr

structure State where
  mem : Array Int
  pc : Int
  input : List Int
  output : List Int
  status : Status
  code : Int
  steps : Nat
  deriving Repr

/-- `0 ≤ a < N`. -/
def InRange (m : Array Int) (a : Int) : Prop := 0 ≤ a ∧ a < (m.size : Int)

instance (m : Array Int) (a : Int) : Decidable (InRange m a) := by
  unfold InRange; infer_instance

/-- Out-of-range reads give 0. -/
def rd (m : Array Int) (a : Int) : Int :=
  if InRange m a then m.getD a.toNat 0 else 0

/-- Out-of-range writes are discarded. -/
def wr (m : Array Int) (a : Int) (v : Int) : Array Int :=
  if InRange m a then m.setIfInBounds a.toNat v else m

/-- The halt rule: after a completed non-trap step, `c = -1` halts. -/
def haltOn (c : Int) (s : State) : State :=
  if c = -1 then { s with status := .halted } else s

/-- PC cannot fetch three cells. -/
def BadPC (s : State) : Prop := s.pc < 0 ∨ (s.mem.size : Int) ≤ s.pc + 2

instance (s : State) : Decidable (BadPC s) := by
  unfold BadPC; infer_instance

/-- One step. Priority: a = -2 trap > a = -1 input > b < 0 output > ordinary. -/
def step (s : State) : State :=
  if s.status ≠ .running then s
  else if BadPC s then { s with status := .faultPC }
  else
    let a := rd s.mem s.pc
    let b := rd s.mem (s.pc + 1)
    let c := rd s.mem (s.pc + 2)
    if a = -2 then
      { s with status := .trap, code := b, steps := s.steps + 1 }
    else if a = -1 then
      match s.input with
      | [] => { s with status := .faultInput }
      | v :: rest =>
        haltOn c { s with mem := wr s.mem b (wrap32 v), input := rest,
                          pc := s.pc + 3, steps := s.steps + 1 }
    else if b < 0 then
      haltOn c { s with output := s.output ++ [rd s.mem a], pc := s.pc + 3,
                        steps := s.steps + 1 }
    else
      let r := wrap32 (rd s.mem b - rd s.mem a)
      haltOn c { s with mem := wr s.mem b r,
                        pc := if r ≤ 0 then c else s.pc + 3,
                        steps := s.steps + 1 }

/-- Run with at most `fuel` attempted steps; if the machine is still running
when the fuel is gone, the status becomes `stepLimit`. -/
def run : Nat → State → State
  | 0, s => if s.status = .running then { s with status := .stepLimit } else s
  | n + 1, s => if s.status = .running then run n (step s) else s

def init (image : List Int) (input : List Int) : State :=
  { mem := (image.map wrap32).toArray, pc := 0, input := input, output := [],
    status := .running, code := 0, steps := 0 }

def Status.render : Status → String
  | .running => "running"
  | .halted => "halted"
  | .trap => "trap"
  | .faultPC => "fault:pc-out-of-range"
  | .faultInput => "fault:input-exhausted"
  | .stepLimit => "step-limit"

private def renderList (label : String) (xs : List Int) : String :=
  String.intercalate " " (label :: xs.map toString)

/-- Canonical six-line result (semantics/subleq-spec.md §5). -/
def render (s : State) : String :=
  s!"STATUS {s.status.render}\nPC {s.pc}\nSTEPS {s.steps}\nCODE {s.code}\n" ++
  renderList "OUTPUT" s.output ++ "\n" ++ renderList "MEM" s.mem.toList ++ "\n"

end Subleq
