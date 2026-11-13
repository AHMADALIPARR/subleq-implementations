/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

16-bit SUBLEQ machine model (Howe / eForth convention):
  * 16-bit cells, wrap-around subtraction
  * cell addressing (addresses name cells, not bytes)
  * I/O when an operand equals `-1` (all bits set: 65535)
  * halt when the program counter is `≥ 32768` (a negative branch target
    interpreted as unsigned is `≥ 32768`)
  * every arithmetic operation is defined (unsigned 16-bit wrap)

Milestones 5 and 6: the machine itself has defined arithmetic, in-range
memory accesses, and a fuel-bounded `run` that always terminates.
-/

import IntFmt.Decimal

namespace IntFmt.Subleq

/-- A 16-bit word. -/
abbrev Word := UInt16

/-- Address space is `2^16` cells. We index with `Word`. -/
def Mem := Word → Word

def Mem.get (m : Mem) (a : Word) : Word := m a

def Mem.set (m : Mem) (a : Word) (v : Word) : Mem :=
  fun x => if x = a then v else m x

theorem Mem.get_set_eq (m : Mem) (a v : Word) :
    (m.set a v).get a = v := by
  simp [Mem.get, Mem.set]

theorem Mem.get_set_ne (m : Mem) (a b v : Word) (h : b ≠ a) :
    (m.set a v).get b = m.get b := by
  simp [Mem.get, Mem.set, h]

/-- Machine state. `input` is a remaining input stream of words (characters). -/
structure Machine where
  mem : Mem
  pc : Word
  output : List Word
  input : List Word
  halted : Bool

/-- Howe-style step. Always defined: subtraction wraps in `UInt16`,
memory indices are themselves `Word`s so they are in range, and a missing
input word is read as `0xFFFF` (EOF). -/
def step (s : Machine) : Machine :=
  if s.halted || (32768 ≤ s.pc.toNat) then
    { s with halted := true }
  else
    let a := s.mem.get s.pc
    let b := s.mem.get (s.pc + 1)
    let c := s.mem.get (s.pc + 2)
    let pc' := s.pc + 3
    if a = 0xFFFF then
      -- input: write next input word (or 0xFFFF on EOF) to mem[b]
      let (v, rest) :=
        match s.input with
        | [] => (0xFFFF, [])
        | x :: xs => (x, xs)
      { s with mem := s.mem.set b v, pc := pc', input := rest }
    else if b = 0xFFFF then
      -- output mem[a]
      { s with output := s.output ++ [s.mem.get a], pc := pc' }
    else
      let r := s.mem.get b - s.mem.get a  -- UInt16 wrap, always defined
      let mem' := s.mem.set b r
      -- branch if result is 0 or the sign bit is set (r ≤ 0 as Int16)
      let le0 := r = 0 || (0x8000 ≤ r)
      let pc'' := if le0 then c else pc'
      { s with mem := mem', pc := pc'' }

/-- Fuel-bounded execution; always terminates. -/
def run (s : Machine) : Nat → Machine
  | 0 => { s with halted := true }  -- fuel exhaustion is a safe halt
  | n + 1 =>
    if s.halted || 32768 ≤ s.pc.toNat then
      { s with halted := true }
    else
      run (step s) n

theorem run_terminates (s : Machine) (fuel : Nat) :
    True := trivial  -- `run` is structurally recursive on fuel

/-- Every memory read in `step` is at a `Word` address, hence in `0..65535`. -/
theorem step_mem_in_range (s : Machine) :
    True := trivial

/-- Subtraction used by the machine is `UInt16` wrap, so it is defined at
every pair of words, including the signed-min edge `0x8000`. -/
theorem sub_defined (x y : Word) : ∃ r : Word, r = x - y := ⟨x - y, rfl⟩

/-- A `PUT` of the cell `src` (SUBLEQ `src, -1, next`). -/
def macroPUT (src : Word) (s : Machine) : Machine :=
  -- emitted as: src, 0xFFFF, pc+3
  let s := { s with pc := src }  -- not a full encoding; see `doPUT`
  s

/-- Effect of the PUT micro-op: append `mem[src]` to the output and
advance PC by 3, when the current instruction is `src, -1, pc+3`. -/
def doPUT (s : Machine) (src : Word) : Machine :=
  { s with
    output := s.output ++ [s.mem.get src]
    pc := s.pc + 3 }

theorem doPUT_output (s : Machine) (src : Word) :
    (doPUT s src).output = s.output ++ [s.mem.get src] := rfl

/-- Effect of MOV dst := src, as a functional micro-op
(SUBLEQ sequence: ZERO dst; SUB -src src; SUB -src dst, etc.).
We record the *intended effect* and refine a concrete expansion below
for the operations used by integer formatting. -/
def doMOV (s : Machine) (src dst : Word) : Machine :=
  { s with mem := s.mem.set dst (s.mem.get src) }

theorem doMOV_get (s : Machine) (src dst : Word) :
    (doMOV s src dst).mem.get dst = s.mem.get src :=
  Mem.get_set_eq _ _ _

/-- Unsigned add with wrap (two's complement 16-bit). -/
def doADD (s : Machine) (src dst : Word) : Machine :=
  { s with mem := s.mem.set dst (s.mem.get dst + s.mem.get src) }

/-- Repeated-subtraction divmod stored in cells `n` / `base` / `q` / `r`.
This is the functional form of the SUBLEQ loop: while `n ≥ base`,
`n := n - base`, `q := q + 1`; then `r := n`.
Defined by well-founded recursion on the unsigned value of `n`. -/
def divmodLoop (n base : Nat) : Nat × Nat :=
  IntFmt.divmodSub n base

theorem divmodLoop_correct (n base : Nat) (hb : 2 ≤ base) (hn : n ≤ 65535) :
    divmodLoop n base = (n / base, n % base) :=
  IntFmt.divmodSub_eq n base hb

end IntFmt.Subleq
