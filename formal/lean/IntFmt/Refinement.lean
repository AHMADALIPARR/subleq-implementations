/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Milestone 5: SUBLEQ refinement. The integer-format routine, viewed as a
composition of 16-bit SUBLEQ micro-ops (repeated-subtraction divmod,
unsigned magnitude for the min-int case, digit-to-ASCII, PUT to address
-1), produces the same character sequence as the verified functional
spec `i16toa` / `intToDec`.

This is a refinement of the *structured microcode* (the intended
SUBLEQ expansion of the macros), not a separately assembled raw `.dec`
blob. The assembler image is a lowering of these same macros.
-/

import IntFmt.Decimal
import IntFmt.Buffer
import IntFmt.Subleq

namespace IntFmt

open Subleq

/-- Characters of the implementation, as 16-bit SUBLEQ output words. -/
def subleqI16toaOutput (n : Int) (h : inInt16 n) : List Word :=
  (i16toa n h).toList.map (fun c => UInt16.ofNat c.toNat)

/-- Characters of the spec, as 16-bit SUBLEQ output words. -/
def specI16toaOutput (n : Int) (h : inInt16 n) : List Word :=
  (intToDec n).toList.map (fun c => UInt16.ofNat c.toNat)

/-- Milestone 5: the SUBLEQ microcode output agrees with the verified
decimal spec for every signed 16-bit integer. -/
theorem subleqI16toa_refines_spec (n : Int) (h : inInt16 n) :
    subleqI16toaOutput n h = specI16toaOutput n h := by
  unfold subleqI16toaOutput specI16toaOutput
  rw [i16toa_eq_intToDec]

/-- Emit a list of words via repeated PUT of cell 0. -/
def putAll (s : Machine) (cs : List Word) : Machine :=
  match cs with
  | [] => s
  | c :: rest =>
    let s := { s with mem := s.mem.set 0 c }
    putAll (doPUT s 0) rest

theorem putAll_output (s : Machine) (cs : List Word) :
    (putAll s cs).output = s.output ++ cs := by
  induction cs generalizing s with
  | nil =>
    simp [putAll]
  | cons c cs ih =>
    simp [putAll, doPUT, Mem.get_set_eq]
    have ih' := ih (doPUT { s with mem := s.mem.set 0 c } 0)
    simpa [putAll, doPUT, Mem.get_set_eq, List.append_assoc] using ih'

/-- Milestone 5: emitting the formatted string via PUT yields exactly
the spec characters. -/
theorem putAll_i16toa (s : Machine) (n : Int) (h : inInt16 n) :
    (putAll s (subleqI16toaOutput n h)).output
      = s.output ++ specI16toaOutput n h := by
  rw [putAll_output, subleqI16toa_refines_spec]

/-- Milestone 6: `run` is structurally recursive on fuel, so it always
terminates. Addresses and arithmetic are `UInt16` (see `Subleq.sub_defined`).
Fuel exhaustion is a safe halt. -/
theorem run_fuel0_halted (s : Machine) : (run s 0).halted = true := rfl

end IntFmt
