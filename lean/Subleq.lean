-- Copyright (C) Ahmad <ahmedparr93@gmail.com>
-- SPDX-License-Identifier: AGPL-3.0-only

namespace Subleq

abbrev Address := Nat

inductive MachineFault where
  | invalidFetch
  | invalidRead
  | invalidWrite
  | inputExhausted
  | flashAttentionTrap
  deriving Repr, DecidableEq, BEq

structure MachineState where
  memory : List Int
  pc : Int
  input : List Int
  output : List Int
  halted : Bool
  fault : Option MachineFault
  deriving Repr, DecidableEq, BEq

def getMem (mem : List Int) (idx : Int) : Option Int :=
  if idx < 0 then none
  else mem.get? idx.toNat

def setMem (mem : List Int) (idx : Int) (val : Int) : Option (List Int) :=
  if idx < 0 then none
  else
    let n := idx.toNat
    if n < mem.length then
      some (mem.set n val)
    else none

def step (s : MachineState) : MachineState :=
  if s.halted then s
  else match s.fault with
    | some _ => { s with halted := true }
    | none =>
      if s.pc < 0 then { s with halted := true }
      else
        match getMem s.memory s.pc, getMem s.memory (s.pc + 1), getMem s.memory (s.pc + 2) with
        | some a, some b, some c =>
          if a < 0 && b < 0 then
            { s with halted := true }
          else if a == -2 then
            if c < 0 then
              { s with halted := true, fault := some MachineFault.flashAttentionTrap }
            else
              { s with pc := c, fault := some MachineFault.flashAttentionTrap }
          else if a == -1 then
            if b < 0 || b >= (s.memory.length : Int) then
              { s with halted := true, fault := some MachineFault.invalidWrite }
            else match s.input with
              | [] => { s with halted := true, fault := some MachineFault.inputExhausted }
              | inVal :: restInput =>
                match setMem s.memory b inVal with
                | some newMem =>
                  let nextPc := if inVal <= 0 then c else s.pc + 3
                  { s with memory := newMem, pc := nextPc, input := restInput, halted := nextPc < 0 }
                | none => { s with halted := true, fault := some MachineFault.invalidWrite }
          else if b == -1 then
            if a < 0 || a >= (s.memory.length : Int) then
              { s with halted := true, fault := some MachineFault.invalidRead }
            else match getMem s.memory a with
              | some outVal =>
                let nextPc := s.pc + 3
                { s with pc := nextPc, output := s.output ++ [outVal], halted := nextPc < 0 }
              | none => { s with halted := true, fault := some MachineFault.invalidRead }
          else
            if a < 0 || a >= (s.memory.length : Int) then
              { s with halted := true, fault := some MachineFault.invalidRead }
            else if b < 0 || b >= (s.memory.length : Int) then
              { s with halted := true, fault := some MachineFault.invalidWrite }
            else match getMem s.memory a, getMem s.memory b with
              | some valA, some valB =>
                let res := valB - valA
                match setMem s.memory b res with
                | some newMem =>
                  let nextPc := if res <= 0 then c else s.pc + 3
                  { s with memory := newMem, pc := nextPc, halted := nextPc < 0 }
                | none => { s with halted := true, fault := some MachineFault.invalidWrite }
              | _, _ => { s with halted := true, fault := some MachineFault.invalidRead }
        | _, _, _ =>
          { s with halted := true, fault := some MachineFault.invalidFetch }

def run (s : MachineState) : Nat → MachineState
  | 0 => s
  | n + 1 =>
    if s.halted then s
    else run (step s) n

end Subleq
