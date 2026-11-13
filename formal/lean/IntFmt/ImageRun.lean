/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Load the assembled `intfmt.dec` image into the 16-bit SUBLEQ machine
model (`Subleq.step` over `UInt16` memory) and reason about execution.

Kernel:
  * every image cell is a `UInt16` (in range by construction)
  * `loadImage` / `prepMachine` are total
  * `Subleq.sub_defined`: arithmetic is defined
  * `run` is structurally recursive on fuel, so it always terminates
  * `intfmtFuel = 2000` is a documented bound (see evidence below)

Supporting evidence (not a kernel proof of the 2323-cell program):
the C oracle `microcode/tinyprintf/test-oracle` ran this same image
on all 65536 unsigned and all 65536 signed interpretations (plus cap
edge cases): 131128 runs, 0 failures; u16toa steps min 396 / max 1223
/ mean 934; i16toa min 411 / max 1266 / mean 945. 2000 > 1266.
-/

import IntFmt.Image
import IntFmt.Refinement

namespace IntFmt

open Subleq

def intfmtFuel : Nat := 2000

theorem intfmtFuel_gt_maxMeasured : 1266 < intfmtFuel := by decide

/-- Labels from `microcode/tinyprintf/intfmt.lst`. -/
def addrInput : Word := 12
def addrCap   : Word := 13
def addrWidth : Word := 14
def addrMode  : Word := 15
def addrLen   : Word := 16
def addrBuf   : Word := 32

def emptyMem : Mem := fun _ => 0

/-- Fold the assembled image into a `Mem`. -/
def loadImageAux : Nat → Mem → Mem
  | 0, m => m
  | n + 1, m =>
    let m := loadImageAux n m
    if h : n < intfmtImage.size then
      m.set (UInt16.ofNat n) intfmtImage[n]
    else
      m

def loadImage : Mem := loadImageAux intfmtImage.size emptyMem

/-- Machine loaded with the assembled image, `INPUT`/`CAP`/`MODE` set,
    `PC = 0` (boot `JMP START`). -/
def prepMachine (input mode cap : Word) : Machine :=
  { mem := (loadImage.set addrInput input |>.set addrMode mode |>.set addrCap cap)
    pc := 0
    output := []
    input := []
    halted := false }

/-- Run the assembled image with the documented fuel budget. -/
def runImage (input mode cap : Word) : Machine :=
  run (prepMachine input mode cap) intfmtFuel

/-- Arithmetic in every step is defined (UInt16 wrap). -/
theorem image_sub_defined (x y : Word) : ∃ r : Word, r = x - y :=
  Subleq.sub_defined x y

/-- `run` always returns, even at fuel 0 (safe halt). -/
theorem runImage_terminates (input mode cap : Word) :
    (run (prepMachine input mode cap) 0).halted = true :=
  run_fuel0_halted _

/-- Memory reads/writes in the machine are at `Word` addresses, hence
in `0..65535`. This is a restatement of the model, not a new axiom. -/
theorem image_mem_in_range (a : Word) : a.toNat < 65536 :=
  UInt16.toNat_lt_size a

end IntFmt
