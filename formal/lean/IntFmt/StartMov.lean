/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Concrete `MOV INPUT N` at pc 60 on the assembled `intfmt.dec` image.
This is a block lemma, not end-to-end correctness.

The encoding is read from the 16-cell extracts inside the proof; there
is no public hard-coded `intfmtImage[62]! = 63` identity lemma. A
mutation of that fall-through that keeps a matching SHA-256 and
regenerated chunks still breaks `start_mov_INPUT_N`.
-/

import IntFmt.StartBlock
import IntFmt.Macros

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem extract60_63 (off : Nat) (h : off < 4) :
    intfmtImage[60 + off]! = decChunk003[12 + off]! := by
  have he : 64 ≤ intfmtImage.size := by rw [intfmtImage_size]; decide
  have hex := image_cell_of_extract 48 64 (12 + off) he (by decide) (by omega)
  have hadd : 48 + (12 + off) = 60 + off := by omega
  rw [← hadd, hex, image_chunk003]

private theorem extract64_71 (off : Nat) (h : off < 8) :
    intfmtImage[64 + off]! = decChunk004[off]! := by
  have he : 80 ≤ intfmtImage.size := by rw [intfmtImage_size]; decide
  have hex := image_cell_of_extract 64 80 off he (by decide) (by omega)
  rw [hex, image_chunk004]

/-- `prepMachine` writes `input` at `INPUT` (cell 12). -/
theorem prepMachine_get_input (input mode cap : Word) :
    (prepMachine input mode cap).mem.get 12 = input := by
  have hmem :
      (prepMachine input mode cap).mem =
        ((loadImage.set addrInput input).set addrMode mode).set addrCap cap := rfl
  rw [hmem, addrInput, addrMode, addrCap]
  have h13 : (12 : Word) ≠ 13 := by decide
  have h15 : (12 : Word) ≠ 15 := by decide
  rw [Mem.get_set_ne _ 13 12 cap h13]
  rw [Mem.get_set_ne _ 15 12 mode h15]
  exact Mem.get_set_eq _ 12 input

/-- After the four START `ZERO`s, a non-poked, non-cleared cell still
equals the assembled image. -/
theorem start_zero_regs_get (input mode cap : Word) (k : Nat)
    (hk : k < 2323)
    (hIn : k ≠ 12) (hMo : k ≠ 15) (hCa : k ≠ 13)
    (hSIGN : k ≠ 19) (hLEN : k ≠ 16) (hPAD : k ≠ 27) (hNDIG : k ≠ 25) :
    (runN (step (prepMachine input mode cap)) 4).mem.get (UInt16.ofNat k) =
      intfmtImage[k]! := by
  have hpres := (start_zero_regs input mode cap).2.2.2.2.2.2.2.2
  have hsz : k < intfmtImage.size := by rw [intfmtImage_size]; exact hk
  have hton : (UInt16.ofNat k).toNat = k := ofNat_toNat_image hsz
  have h19 : UInt16.ofNat k ≠ 19 := by
    intro h
    have hx := congrArg UInt16.toNat h
    have : k = 19 := by
      simpa [hton] using hx
    exact hSIGN this
  have h16 : UInt16.ofNat k ≠ 16 := by
    intro h
    have hx := congrArg UInt16.toNat h
    have : k = 16 := by
      simpa [hton] using hx
    exact hLEN this
  have h27 : UInt16.ofNat k ≠ 27 := by
    intro h
    have hx := congrArg UInt16.toNat h
    have : k = 27 := by
      simpa [hton] using hx
    exact hPAD this
  have h25 : UInt16.ofNat k ≠ 25 := by
    intro h
    have hx := congrArg UInt16.toNat h
    have : k = 25 := by
      simpa [hton] using hx
    exact hNDIG this
  exact (hpres (UInt16.ofNat k) h19 h16 h27 h25).trans
    (afterBoot_get input mode cap k hk hIn hMo hCa)

/-- After the four START `ZERO`s, `INPUT` still holds the poked value. -/
theorem start_zero_regs_get_INPUT (input mode cap : Word) :
    (runN (step (prepMachine input mode cap)) 4).mem.get 12 = input := by
  have hpres := (start_zero_regs input mode cap).2.2.2.2.2.2.2.2
  have hboot : (step (prepMachine input mode cap)).mem.get 12 = input := by
    rw [(boot_jmp input mode cap).2.2.1]
    exact prepMachine_get_input input mode cap
  exact (hpres 12 (by decide) (by decide) (by decide) (by decide)).trans hboot

/-- After the four START `ZERO`s, `MOV INPUT, N` at pc 60 leaves
`N = input`, `Z = 0`, and `pc = 72`. Encoding cells (including the
fall-through at cell 62) are read from the 16-cell extracts inside
this proof, not from a public identity lemma. -/
theorem start_mov_INPUT_N (input mode cap : Word) :
    let s0 := step (prepMachine input mode cap)
    let s4 := runN s0 4
    let s8 := runN s4 4
    s4.pc = 60 ∧
    s8.pc = 72 ∧
    s8.halted = false ∧
    s8.mem.get 17 = input ∧
    s8.mem.get 0 = 0 ∧
    s8.mem.get 12 = input ∧
    (∀ a, a ≠ 17 → a ≠ 0 → s8.mem.get a = s4.mem.get a) := by
  intro s0 s4 s8
  have hz := start_zero_regs input mode cap
  have hs4pc : s4.pc = 60 := hz.2.1
  have hs4h : s4.halted = false := hz.2.2.1
  have hZ : s4.mem.get 0 = 0 := hz.2.2.2.2.2.2.2.1
  have poff (off : Nat) (hoff : off ≤ 12) :
      s4.pc + UInt16.ofNat off = UInt16.ofNat (60 + off) := by
    have hton : s4.pc.toNat = 60 := by simp [hs4pc]
    apply UInt16.toNat.inj
    have hsz : UInt16.size = 65536 := rfl
    have hbound : s4.pc.toNat + off < 65536 := by
      rw [hton]
      omega
    have hL : (s4.pc + UInt16.ofNat off).toNat = 60 + off := by
      have hw := word_add_toNat s4.pc off hbound
      rw [hw, hton]
    have hR : (UInt16.ofNat (60 + off)).toNat = 60 + off := by
      have hlt : 60 + off < UInt16.size := by
        rw [hsz]
        omega
      exact UInt16.toNat_ofNat_of_lt hlt
    exact hL.trans hR.symm
  have gimg (off : Nat) (hoff : off < 12) :
      s4.mem.get (UInt16.ofNat (60 + off)) = intfmtImage[60 + off]! :=
    start_zero_regs_get input mode cap (60 + off)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  have h0 : s4.mem.get s4.pc = 17 := by
    have hp : s4.pc = UInt16.ofNat 60 := by
      simpa [hs4pc] using (rfl : (60 : Word) = UInt16.ofNat 60)
    rw [hp]
    have hval : decChunk003[12]! = 17 := rfl
    exact (gimg 0 (by decide)).trans ((extract60_63 0 (by decide)).trans hval)
  have h1 : s4.mem.get (s4.pc + UInt16.ofNat 1) = 17 := by
    rw [poff 1 (by decide)]
    have hval : decChunk003[13]! = 17 := rfl
    exact (gimg 1 (by decide)).trans ((extract60_63 1 (by decide)).trans hval)
  have h2 : s4.mem.get (s4.pc + UInt16.ofNat 2) = s4.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk003[14]! = 63 := rfl
    have h63 : (63 : Word) = UInt16.ofNat 63 := rfl
    exact (gimg 2 (by decide)).trans
      ((extract60_63 2 (by decide)).trans (hval.trans h63))
  have h3 : s4.mem.get (s4.pc + UInt16.ofNat 3) = 12 := by
    rw [poff 3 (by decide)]
    have hval : decChunk003[15]! = 12 := rfl
    exact (gimg 3 (by decide)).trans ((extract60_63 3 (by decide)).trans hval)
  have h4 : s4.mem.get (s4.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk004[0]! = 0 := rfl
    exact (gimg 4 (by decide)).trans ((extract64_71 0 (by decide)).trans hval)
  have h5 : s4.mem.get (s4.pc + UInt16.ofNat 5) = s4.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk004[1]! = 66 := rfl
    have h66 : (66 : Word) = UInt16.ofNat 66 := rfl
    exact (gimg 5 (by decide)).trans
      ((extract64_71 1 (by decide)).trans (hval.trans h66))
  have h6 : s4.mem.get (s4.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk004[2]! = 0 := rfl
    exact (gimg 6 (by decide)).trans ((extract64_71 2 (by decide)).trans hval)
  have h7 : s4.mem.get (s4.pc + UInt16.ofNat 7) = 17 := by
    rw [poff 7 (by decide)]
    have hval : decChunk004[3]! = 17 := rfl
    exact (gimg 7 (by decide)).trans ((extract64_71 3 (by decide)).trans hval)
  have h8 : s4.mem.get (s4.pc + UInt16.ofNat 8) = s4.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk004[4]! = 69 := rfl
    have h69 : (69 : Word) = UInt16.ofNat 69 := rfl
    exact (gimg 8 (by decide)).trans
      ((extract64_71 4 (by decide)).trans (hval.trans h69))
  have h9 : s4.mem.get (s4.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk004[5]! = 0 := rfl
    exact (gimg 9 (by decide)).trans ((extract64_71 5 (by decide)).trans hval)
  have h10 : s4.mem.get (s4.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk004[6]! = 0 := rfl
    exact (gimg 10 (by decide)).trans ((extract64_71 6 (by decide)).trans hval)
  have h11 : s4.mem.get (s4.pc + UInt16.ofNat 11) = s4.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk004[7]! = 72 := rfl
    have h72 : (72 : Word) = UInt16.ofNat 72 := rfl
    exact (gimg 11 (by decide)).trans
      ((extract64_71 7 (by decide)).trans (hval.trans h72))
  have hcodeD : ∀ i : Nat, i < 12 → s4.pc + UInt16.ofNat i ≠ (17 : Word) := by
    intro i hi h
    have heq := poff i (Nat.le_of_lt hi)
    have hx := congrArg UInt16.toNat (heq.symm.trans h)
    have hsz : UInt16.size = 65536 := rfl
    have hL : (UInt16.ofNat (60 + i)).toNat = 60 + i := by
      have hlt : 60 + i < UInt16.size := by rw [hsz]; omega
      exact UInt16.toNat_ofNat_of_lt hlt
    have h17 : (17 : Word).toNat = 17 := rfl
    have : 60 + i = 17 := by
      rw [hL, h17] at hx
      exact hx
    omega
  have hcodeZ : ∀ i : Nat, i < 12 → s4.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi h
    have heq := poff i (Nat.le_of_lt hi)
    have hx := congrArg UInt16.toNat (heq.symm.trans h)
    have hsz : UInt16.size = 65536 := rfl
    have hL : (UInt16.ofNat (60 + i)).toNat = 60 + i := by
      have hlt : 60 + i < UInt16.size := by rw [hsz]; omega
      exact UInt16.toNat_ofNat_of_lt hlt
    have h0t : (0 : Word).toNat = 0 := rfl
    have : 60 + i = 0 := by
      rw [hL, h0t] at hx
      exact hx
    omega
  have hpc : s4.pc.toNat + 12 ≤ 32768 := by simp [hs4pc]
  have hpc0 : 0 < s4.pc.toNat := by simp [hs4pc]
  have hmov :=
    runN_MOV (s := s4) (src := 12) (dst := 17)
      hs4h hpc hpc0 hZ (by decide) (by decide) (by decide) (by decide)
      h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hcodeD hcodeZ
  have hpc8 : s8.pc = 72 := by
    have hp := hmov.1
    have hadd : s4.pc + UInt16.ofNat 12 = (72 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 72 = (72 : Word))
    exact hp.trans hadd
  have hN : s8.mem.get 17 = input :=
    hmov.2.2.1.trans (start_zero_regs_get_INPUT input mode cap)
  have hZ8 : s8.mem.get 0 = 0 := hmov.2.2.2.1
  have hIn : s8.mem.get 12 = input :=
    hmov.2.2.2.2.1.trans (start_zero_regs_get_INPUT input mode cap)
  have hpres := hmov.2.2.2.2.2
  exact ⟨hs4pc, hpc8, hmov.2.1, hN, hZ8, hIn, hpres⟩

/-- After `MOV INPUT N`, a non-poked, non-cleared, non-destination cell
still equals the assembled image. -/
theorem start_mov_get (input mode cap : Word) (k : Nat)
    (hk : k < 2323)
    (hIn : k ≠ 12) (hMo : k ≠ 15) (hCa : k ≠ 13)
    (hSIGN : k ≠ 19) (hLEN : k ≠ 16) (hPAD : k ≠ 27) (hNDIG : k ≠ 25)
    (hN : k ≠ 17) (hZ : k ≠ 0) :
    (runN (runN (step (prepMachine input mode cap)) 4) 4).mem.get
      (UInt16.ofNat k) = intfmtImage[k]! := by
  have hpres := (start_mov_INPUT_N input mode cap).2.2.2.2.2.2
  have hsz : k < intfmtImage.size := by rw [intfmtImage_size]; exact hk
  have hton : (UInt16.ofNat k).toNat = k := ofNat_toNat_image hsz
  have h17 : UInt16.ofNat k ≠ 17 := by
    intro h
    have hx := congrArg UInt16.toNat h
    have : k = 17 := by simpa [hton] using hx
    exact hN this
  have h0 : UInt16.ofNat k ≠ 0 := by
    intro h
    have hx := congrArg UInt16.toNat h
    have : k = 0 := by simpa [hton] using hx
    exact hZ this
  exact (hpres (UInt16.ofNat k) h17 h0).trans
    (start_zero_regs_get input mode cap k hk hIn hMo hCa hSIGN hLEN hPAD hNDIG)

/-- `prepMachine` writes `mode` at `MODE` (cell 15). -/
theorem prepMachine_get_mode (input mode cap : Word) :
    (prepMachine input mode cap).mem.get 15 = mode := by
  have hmem :
      (prepMachine input mode cap).mem =
        ((loadImage.set addrInput input).set addrMode mode).set addrCap cap := rfl
  rw [hmem, addrInput, addrMode, addrCap]
  have h13 : (15 : Word) ≠ 13 := by decide
  rw [Mem.get_set_ne _ 13 15 cap h13]
  exact Mem.get_set_eq _ 15 mode

/-- After `MOV INPUT N`, `MODE` still holds the poked value. -/
theorem start_mov_get_MODE (input mode cap : Word) :
    (runN (runN (step (prepMachine input mode cap)) 4) 4).mem.get 15 = mode := by
  have hpres := (start_mov_INPUT_N input mode cap).2.2.2.2.2.2
  have h4 : (runN (step (prepMachine input mode cap)) 4).mem.get 15 = mode := by
    have hz := (start_zero_regs input mode cap).2.2.2.2.2.2.2.2
    have hboot : (step (prepMachine input mode cap)).mem.get 15 = mode := by
      rw [(boot_jmp input mode cap).2.2.1]
      exact prepMachine_get_mode input mode cap
    exact (hz 15 (by decide) (by decide) (by decide) (by decide)).trans hboot
  exact (hpres 15 (by decide) (by decide)).trans h4

end IntFmt
