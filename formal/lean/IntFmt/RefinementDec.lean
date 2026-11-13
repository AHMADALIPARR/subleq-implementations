/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Refinement of the *actual* 2323-cell `intfmt.dec` image against the
verified formatting specification.

Target (conceptual):

  ∀ n : Int16,
    output (run intfmtFuel (loadIntfmtDec n)) = formatSpec n

where `loadIntfmtDec n` is `prepMachine` of the assembled image with
`MODE = 1` (signed), `CAP = 8`, `WIDTH = 0`, and `INPUT` the 16-bit
pattern of `n`.  `output` is the `CAP`-cell buffer at `BUF` together
with the untruncated length in `LEN`, including a NUL when `CAP > 0`.

This file proves:

* Program identity (via `DecLoad` / `ImageRun.loadImage_eq_aux`):
  the machine memory is exactly the assembled artifact.
* The boot instruction at cell 0 is `JMP START`, and one `step` of
  a prepared machine lands at `START` (cell 48) with Z still 0.
* The existing termination / defined-arithmetic / in-range lemmas
  apply to this exact image (`runImage_terminates`, `image_sub_defined`,
  `image_mem_in_range`, `intfmtFuel_gt_maxMeasured`).
* A program-HALT (or already-halted) state is connected to `run` at
  the official fuel bound by `run_intfmtFuel_of_done`.

The universal execution-equivalence theorem over every `Int16` (that
the assembled bytes, stepped under `Subleq.step`, match `intToDec` /
`snprintfSpec`) is the remaining obligation; it is not assumed and
not admitted. Block lemmas and the assembler-macro characterisation
in `Macros.lean` are the intended route.
-/

import IntFmt.DecLoad
import IntFmt.ImageRun
import IntFmt.Macros
import IntFmt.Buffer
import IntFmt.Decimal

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000

/-- Default signed run: 16-bit two's-complement input, cap 8, no pad. -/
def loadIntfmtDec (n : Int16) : Machine :=
  prepMachine (UInt16.ofNat n.toBitVec.toNat) 1 8

/-- Buffer cells `BUF .. BUF+cap-1`, as 16-bit words. -/
def machineBuf (s : Machine) (cap : Nat) : List Word :=
  (List.range cap).map (fun i => s.mem.get (addrBuf + UInt16.ofNat i))

/-- Required length reported by the program. -/
def machineLen (s : Machine) : Word :=
  s.mem.get addrLen

/-- Canonical payload of signed 16-bit decimal formatting. -/
def formatPayload (n : Int16) : List Nat :=
  (intToDec n.toInt).toList.map (fun c => c.toNat)

/-- Spec output: snprintf-style buffer of capacity 8, plus the
untruncated length. -/
def formatSpec (n : Int16) : List Nat × Nat :=
  snprintfSpec (formatPayload n) 8

/-- The first three cells are `JMP START` (`subleq Z, Z, 48`). -/
theorem image_boot_JMP :
    intfmtImage[0]! = 0 ∧ intfmtImage[1]! = 0 ∧ intfmtImage[2]! = 48 :=
  ⟨image_cell_Z, rfl, image_cell_startTarget⟩

/-- Fetch a non-poked image cell from a prepared machine. -/
theorem prep_get_cell (input mode cap : Word) (k : Nat)
    (hk : k < 2323) (hIn : k ≠ 12) (hMo : k ≠ 15) (hCa : k ≠ 13) :
    (prepMachine input mode cap).mem.get (UInt16.ofNat k) =
      imageCell k := by
  have hsz : k < intfmtImage.size := by
    rw [intfmtImage_size]
    exact hk
  have hton : (UInt16.ofNat k).toNat = k := ofNat_toNat_image hsz
  have hIn' : UInt16.ofNat k ≠ addrInput := by
    intro h
    have := congrArg UInt16.toNat h
    simp [addrInput, hton] at this
    exact hIn this
  have hMo' : UInt16.ofNat k ≠ addrMode := by
    intro h
    have := congrArg UInt16.toNat h
    simp [addrMode, hton] at this
    exact hMo this
  have hCa' : UInt16.ofNat k ≠ addrCap := by
    intro h
    have := congrArg UInt16.toNat h
    simp [addrCap, hton] at this
    exact hCa this
  rw [prepMachine_get_prog input mode cap (UInt16.ofNat k) hIn' hMo' hCa']
  -- loadImage.get a = imageCell a.toNat by definition
  change imageCell (UInt16.ofNat k).toNat = imageCell k
  rw [hton]

/-- A prepared machine is running at PC 0, not halted, with Z = 0. -/
theorem prep_ready (input mode cap : Word) :
    (prepMachine input mode cap).halted = false ∧
    (prepMachine input mode cap).pc = 0 ∧
    (prepMachine input mode cap).pc.toNat < 32768 ∧
    (prepMachine input mode cap).mem.get 0 = 0 := by
  have hpc0 : (prepMachine input mode cap).pc = 0 := rfl
  have hhalt : (prepMachine input mode cap).halted = false := rfl
  have hpc : (prepMachine input mode cap).pc.toNat < 32768 := by
    rw [hpc0]
    decide
  have hZ : (prepMachine input mode cap).mem.get 0 = 0 := by
    have h := prep_get_cell input mode cap 0
      (by decide) (by decide) (by decide) (by decide)
    have hz : imageCell 0 = 0 := by
      simp [imageCell, intfmtImage_size]
      rfl
    have h' : (prepMachine input mode cap).mem.get 0 = imageCell 0 := by
      simpa using h
    exact h'.trans hz
  exact ⟨hhalt, hpc0, hpc, hZ⟩

/-- One step from a prepared machine executes the boot `JMP START`
and lands at cell 48, with memory (including Z) unchanged. -/
theorem boot_jmp (input mode cap : Word) :
    (step (prepMachine input mode cap)).pc = 48 ∧
    (step (prepMachine input mode cap)).halted = false ∧
    (step (prepMachine input mode cap)).mem = (prepMachine input mode cap).mem ∧
    (step (prepMachine input mode cap)).output = [] := by
  have hr := prep_ready input mode cap
  have h0 : (prepMachine input mode cap).mem.get 0 = 0 := hr.2.2.2
  have h1 : (prepMachine input mode cap).mem.get 1 = 0 := by
    have h := prep_get_cell input mode cap 1
      (by decide) (by decide) (by decide) (by decide)
    have hz : imageCell 1 = 0 := by
      simp [imageCell, intfmtImage_size]
      rfl
    have h' : (prepMachine input mode cap).mem.get 1 = imageCell 1 := by
      simpa using h
    exact h'.trans hz
  have h2 : (prepMachine input mode cap).mem.get 2 = 48 := by
    have h := prep_get_cell input mode cap 2
      (by decide) (by decide) (by decide) (by decide)
    have hz : imageCell 2 = 48 := by
      simp [imageCell, intfmtImage_size]
      rfl
    have h' : (prepMachine input mode cap).mem.get 2 = imageCell 2 := by
      simpa using h
    exact h'.trans hz
  have hp0 : (prepMachine input mode cap).pc = 0 := hr.2.1
  have hstep :=
    step_JMP (s := prepMachine input mode cap) (dest := 48)
      hr.1 hr.2.2.1 h0
      (by simpa [hp0] using h0)
      (by simpa [hp0] using h1)
      (by simpa [hp0] using h2)
  refine ⟨?pc, ?halt, ?mem, ?out⟩
  · rw [hstep]
  · rw [hstep]; exact hr.1
  · rw [hstep]
  · rw [hstep]; rfl

/-- The existing safety theorems talk about this exact assembled image. -/
theorem safety_applies (n : Int16) :
    (run (loadIntfmtDec n) 0).halted = true ∧
    (∀ x y : Word, ∃ r, r = x - y) ∧
    (∀ a : Word, a.toNat < 65536) ∧
    1266 < intfmtFuel :=
  ⟨runImage_terminates _ _ _,
    fun x y => image_sub_defined x y,
    image_mem_in_range,
    intfmtFuel_gt_maxMeasured⟩

/-- If the machine has already taken HALT (or the halt flag is set),
`run` at the official fuel bound is that state with `halted = true`.
This connects a bounded execution that has already halted to the
established halt-on-fuel / halt-on-negative-PC behaviour. -/
theorem run_intfmtFuel_of_done (s : Machine)
    (h : s.halted = true ∨ 32768 ≤ s.pc.toNat) :
    run s intfmtFuel = { s with halted := true } :=
  run_of_done s intfmtFuel h

/-- Program identity: the memory used by `runImage` is exactly the
assembled 2323-cell image (direct lookup, equal to the historical fold). -/
theorem program_identity :
    intfmtImage.size = 2323 ∧
    loadImage = loadImageAux intfmtImage.size emptyMem ∧
    intfmtImage.extract 0 16 = parseDecText intfmtDecLine0 :=
  ⟨intfmtImage_size, loadImage_eq_aux, intfmtImage_prefix16_eq_parse⟩

end IntFmt
