/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Mode dispatch on the assembled `intfmt.dec` image, composed with
`start_mov_INPUT_N`. These are block lemmas, not end-to-end correctness.

After `MOV INPUT N` (pc 72): `MOV MODE T; JLEZ T U_PATH; JMP I_PATH`.
Signed mode (1) enters `I_PATH` at pc 93; unsigned mode (0) jumps to
`DIGITS` at pc 174.
-/

import IntFmt.StartMov

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-- Machine after boot, the four START `ZERO`s, and `MOV INPUT N`.
Marked irreducible so later `runN` lemmas do not unfold the loaded image. -/
@[irreducible] def afterStartMov (input mode cap : Word) : Machine :=
  runN (runN (step (prepMachine input mode cap)) 4) 4

theorem afterStartMov_eq (input mode cap : Word) :
    afterStartMov input mode cap =
      runN (runN (step (prepMachine input mode cap)) 4) 4 := by
  unfold afterStartMov
  rfl

/-- `runN s 6` is two steps past `runN s 4`, when those steps are taken. -/
private theorem runN_6_of_4_2 (s : Machine)
    (h4h : (runN s 4).halted = false)
    (h4pc : (runN s 4).pc.toNat < 32768)
    (h5h : (step (runN s 4)).halted = false)
    (h5pc : (step (runN s 4)).pc.toNat < 32768) :
    runN s 6 = step (step (runN s 4)) := by
  have h6 : runN s 6 = runN (runN s 4) 2 := by
    have h := runN_add s 4 2
    rw [show (4 + 2 = 6) from rfl] at h
    exact h
  have hgo1 := runN_succ_go (runN s 4) 1 h4h h4pc
  have hgo2 := runN_one (step (runN s 4)) h5h h5pc
  exact h6.trans (hgo1.trans hgo2)

private theorem extract_chunk (base : Nat) (chunk : Array UInt16)
    (hch : intfmtImage.extract base (base + 16) = chunk)
    (off : Nat) (hoff : off < 16) (hbase : base + 16 ≤ 2323) :
    intfmtImage[base + off]! = chunk[off]! := by
  have he : base + 16 ≤ intfmtImage.size := by
    rw [intfmtImage_size]
    exact hbase
  have hse : base ≤ base + 16 := Nat.le_add_right base 16
  have hi : off < (base + 16) - base := by
    have : (base + 16) - base = 16 := Nat.add_sub_cancel_left base 16
    omega
  have hex := image_cell_of_extract base (base + 16) off he hse hi
  rw [hex, hch]

private theorem cell64 (off : Nat) (h : off < 16) :
    intfmtImage[64 + off]! = decChunk004[off]! :=
  extract_chunk 64 decChunk004 image_chunk004 off h (by decide)

private theorem cell80 (off : Nat) (h : off < 16) :
    intfmtImage[80 + off]! = decChunk005[off]! :=
  extract_chunk 80 decChunk005 image_chunk005 off h (by decide)

/-- After `start_mov`, program cells used by the mode dispatch still
match the image. -/
private theorem start_mov_code (input mode cap : Word) (k : Nat)
    (hk : 72 ≤ k) (hk2 : k < 93) :
    (afterStartMov input mode cap).mem.get (UInt16.ofNat k) =
      intfmtImage[k]! := by
  have hlt : k < 2323 := by omega
  have h := start_mov_get input mode cap k hlt
    (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  rw [afterStartMov_eq]
  exact h

private theorem image_ONE : intfmtImage[3]! = 1 := by
  have hex := image_cell_of_extract 0 16 3
    (by rw [intfmtImage_size]; decide) (by decide) (by decide)
  have hval : decChunk000[3]! = 1 := rfl
  exact hex.trans (by rw [image_chunk000]; exact hval)

/-- After `start_mov`, `ONE` (cell 3) still holds `1`. -/
theorem start_mov_get_ONE (input mode cap : Word) :
    (afterStartMov input mode cap).mem.get 3 = 1 := by
  have h := start_mov_get input mode cap 3 (by decide)
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hk : (3 : Word) = UInt16.ofNat 3 := rfl
  rw [hk, afterStartMov_eq]
  exact h.trans image_ONE

private theorem pc72_off {s : Machine} (hspc : s.pc = 72)
    (off : Nat) (hoff : off ≤ 21) :
    s.pc + UInt16.ofNat off = UInt16.ofNat (72 + off) := by
  have hton : s.pc.toNat = 72 := by simp [hspc]
  apply UInt16.toNat.inj
  have hsz : UInt16.size = 65536 := rfl
  have hbound : s.pc.toNat + off < 65536 := by rw [hton]; omega
  have hL : (s.pc + UInt16.ofNat off).toNat = 72 + off := by
    have hw := word_add_toNat s.pc off hbound
    omega
  have hR : (UInt16.ofNat (72 + off)).toNat = 72 + off := by
    have hlt : 72 + off < UInt16.size := by rw [hsz]; omega
    exact UInt16.toNat_ofNat_of_lt hlt
  exact hL.trans hR.symm

/-- After `MOV INPUT N`, `MOV MODE T` finishes at pc 84 with `T = mode`. -/
theorem mode_mov_MODE_T (input mode cap : Word) :
    let s := afterStartMov input mode cap
    let s4 := runN s 4
    s.pc = 72 ∧
    s4.pc = 84 ∧
    s4.halted = false ∧
    s4.mem.get 18 = mode ∧
    s4.mem.get 0 = 0 ∧
    s4.mem.get 15 = mode ∧
    s4.mem.get 17 = input ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s4.mem.get a = s.mem.get a) := by
  intro s s4
  have heq := afterStartMov_eq input mode cap
  have hsm := start_mov_INPUT_N input mode cap
  have hsdef : s = afterStartMov input mode cap := rfl
  have hspc : s.pc = 72 := by
    rw [hsdef, heq]
    exact hsm.2.1
  have hsh : s.halted = false := by
    rw [hsdef, heq]
    exact hsm.2.2.1
  have hZ : s.mem.get 0 = 0 := by
    rw [hsdef, heq]
    exact hsm.2.2.2.2.1
  have hN0 : s.mem.get 17 = input := by
    rw [hsdef, heq]
    exact hsm.2.2.2.1
  have hMODE : s.mem.get 15 = mode := by
    rw [hsdef, heq]
    exact start_mov_get_MODE input mode cap
  have poff (off : Nat) (hoff : off ≤ 21) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (72 + off) :=
    pc72_off hspc off hoff
  have gimg (off : Nat) (hoff : off < 21) :
      s.mem.get (UInt16.ofNat (72 + off)) = intfmtImage[72 + off]! :=
    start_mov_code input mode cap (72 + off) (by omega) (by omega)
  have hp : s.pc = UInt16.ofNat 72 :=
    hspc.trans (rfl : (72 : Word) = UInt16.ofNat 72)
  have h0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk004[8]! = 18 := rfl
    exact (gimg 0 (by decide)).trans ((cell64 8 (by decide)).trans hval)
  have h1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk004[9]! = 18 := rfl
    exact (gimg 1 (by decide)).trans ((cell64 9 (by decide)).trans hval)
  have h2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk004[10]! = 75 := rfl
    have hv : (75 : Word) = UInt16.ofNat 75 := rfl
    exact (gimg 2 (by decide)).trans ((cell64 10 (by decide)).trans (hval.trans hv))
  have h3 : s.mem.get (s.pc + UInt16.ofNat 3) = 15 := by
    rw [poff 3 (by decide)]
    have hval : decChunk004[11]! = 15 := rfl
    exact (gimg 3 (by decide)).trans ((cell64 11 (by decide)).trans hval)
  have h4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk004[12]! = 0 := rfl
    exact (gimg 4 (by decide)).trans ((cell64 12 (by decide)).trans hval)
  have h5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk004[13]! = 78 := rfl
    have hv : (78 : Word) = UInt16.ofNat 78 := rfl
    exact (gimg 5 (by decide)).trans ((cell64 13 (by decide)).trans (hval.trans hv))
  have h6c : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk004[14]! = 0 := rfl
    exact (gimg 6 (by decide)).trans ((cell64 14 (by decide)).trans hval)
  have h7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk004[15]! = 18 := rfl
    exact (gimg 7 (by decide)).trans ((cell64 15 (by decide)).trans hval)
  have h8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk005[0]! = 81 := rfl
    have hv : (81 : Word) = UInt16.ofNat 81 := rfl
    exact (gimg 8 (by decide)).trans ((cell80 0 (by decide)).trans (hval.trans hv))
  have h9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk005[1]! = 0 := rfl
    exact (gimg 9 (by decide)).trans ((cell80 1 (by decide)).trans hval)
  have h10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk005[2]! = 0 := rfl
    exact (gimg 10 (by decide)).trans ((cell80 2 (by decide)).trans hval)
  have h11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk005[3]! = 84 := rfl
    have hv : (84 : Word) = UInt16.ofNat 84 := rfl
    exact (gimg 11 (by decide)).trans ((cell80 3 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi h
    have heq := poff i (by omega)
    have hx := congrArg UInt16.toNat (heq.symm.trans h)
    have hsz : UInt16.size = 65536 := rfl
    have hL : (UInt16.ofNat (72 + i)).toNat = 72 + i := by
      have hlt : 72 + i < UInt16.size := by rw [hsz]; omega
      exact UInt16.toNat_ofNat_of_lt hlt
    have : 72 + i = 18 := by
      have h18 : (18 : Word).toNat = 18 := rfl
      rw [hL, h18] at hx
      exact hx
    omega
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi h
    have heq := poff i (by omega)
    have hx := congrArg UInt16.toNat (heq.symm.trans h)
    have hsz : UInt16.size = 65536 := rfl
    have hL : (UInt16.ofNat (72 + i)).toNat = 72 + i := by
      have hlt : 72 + i < UInt16.size := by rw [hsz]; omega
      exact UInt16.toNat_ofNat_of_lt hlt
    have : 72 + i = 0 := by
      have h0t : (0 : Word).toNat = 0 := rfl
      rw [hL, h0t] at hx
      exact hx
    omega
  have hpc : s.pc.toNat + 12 ≤ 32768 := by simp [hspc]
  have hpc0 : 0 < s.pc.toNat := by simp [hspc]
  have hmov :=
    runN_MOV (s := s) (src := 15) (dst := 18)
      hsh hpc hpc0 hZ (by decide) (by decide) (by decide) (by decide)
      h0 h1 h2 h3 h4 h5 h6c h7 h8 h9 h10 h11 hcodeD hcodeZ
  have hs4pc : s4.pc = 84 := by
    have hadd : s.pc + UInt16.ofNat 12 = (84 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 84 = (84 : Word))
    exact hmov.1.trans hadd
  have hs4h : s4.halted = false := hmov.2.1
  have hT : s4.mem.get 18 = mode := hmov.2.2.1.trans hMODE
  have hZ4 : s4.mem.get 0 = 0 := hmov.2.2.2.1
  have hpres4 := hmov.2.2.2.2.2
  have hM4 : s4.mem.get 15 = mode := (hpres4 15 (by decide) (by decide)).trans hMODE
  have hN4 : s4.mem.get 17 = input := (hpres4 17 (by decide) (by decide)).trans hN0
  exact ⟨hspc, hs4pc, hs4h, hT, hZ4, hM4, hN4, hpres4⟩

/-- After `MOV MODE T`, signed mode falls through `JLEZ` to the `JMP I_PATH`
at pc 87, then enters `I_PATH` at pc 93 with `T = 1`. -/
theorem mode_dispatch_signed (input cap : Word) :
    let s := afterStartMov input 1 cap
    let s6 := runN s 6
    s.pc = 72 ∧
    s6.pc = 93 ∧
    s6.halted = false ∧
    s6.mem.get 17 = input ∧
    s6.mem.get 0 = 0 ∧
    s6.mem.get 15 = 1 ∧
    s6.mem.get 18 = 1 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a) := by
  intro s s6
  have hm := mode_mov_MODE_T input 1 cap
  have hspc : s.pc = 72 := hm.1
  let s4 := runN s 4
  have hs4pc : s4.pc = 84 := hm.2.1
  have hs4h : s4.halted = false := hm.2.2.1
  have hT : s4.mem.get 18 = 1 := hm.2.2.2.1
  have hZ4 : s4.mem.get 0 = 0 := hm.2.2.2.2.1
  have hM4 : s4.mem.get 15 = 1 := hm.2.2.2.2.2.1
  have hN4 : s4.mem.get 17 = input := hm.2.2.2.2.2.2.1
  have hpres4 := hm.2.2.2.2.2.2.2
  have gimg (off : Nat) (hoff : off < 21) :
      s.mem.get (UInt16.ofNat (72 + off)) = intfmtImage[72 + off]! :=
    start_mov_code input 1 cap (72 + off) (by omega) (by omega)
  have j0 : s4.mem.get s4.pc = 0 := by
    have hp : s4.pc = UInt16.ofNat 84 :=
      hs4pc.trans (rfl : (84 : Word) = UInt16.ofNat 84)
    rw [hp]
    have hget : s4.mem.get (UInt16.ofNat 84) = s.mem.get (UInt16.ofNat 84) :=
      hpres4 (UInt16.ofNat 84) (by decide) (by decide)
    have hval : decChunk005[4]! = 0 := rfl
    exact hget.trans ((gimg 12 (by decide)).trans ((cell80 4 (by decide)).trans hval))
  have j1 : s4.mem.get (s4.pc + 1) = 18 := by
    have : s4.pc + 1 = (85 : Word) := by simp [hs4pc]
    rw [this, (rfl : (85 : Word) = UInt16.ofNat 85)]
    have hget : s4.mem.get (UInt16.ofNat 85) = s.mem.get (UInt16.ofNat 85) :=
      hpres4 (UInt16.ofNat 85) (by decide) (by decide)
    have hval : decChunk005[5]! = 18 := rfl
    exact hget.trans ((gimg 13 (by decide)).trans ((cell80 5 (by decide)).trans hval))
  have j2 : s4.mem.get (s4.pc + 2) = 90 := by
    have : s4.pc + 2 = (86 : Word) := by simp [hs4pc]
    rw [this, (rfl : (86 : Word) = UInt16.ofNat 86)]
    have hget : s4.mem.get (UInt16.ofNat 86) = s.mem.get (UInt16.ofNat 86) :=
      hpres4 (UInt16.ofNat 86) (by decide) (by decide)
    have hval : decChunk005[6]! = 90 := rfl
    exact hget.trans ((gimg 14 (by decide)).trans ((cell80 6 (by decide)).trans hval))
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez :=
    step_JLEZ (s := s4) (x := 18) (dest := 90)
      hs4h hpc4 hZ4 j0 j1 j2 (by decide)
  have hle : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = false := by
    have : le0 (s4.mem.get 18) = false := by
      rw [hT]
      exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := s4.pc + 3 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18 then (90 : Word)
          else s4.pc + 3) = s4.pc + 3 := by
      simp [hle]
    rw [hjlez, hif]
  have hs5pc : (step s4).pc = 87 := by
    have : s4.pc + 3 = (87 : Word) := by simp [hs4pc]
    rw [hs5eq]
    exact this
  have hs5h : (step s4).halted = false := by
    rw [hs5eq]
    exact hs4h
  have hs5Z : (step s4).mem.get 0 = 0 := by
    rw [hs5eq]
    exact hZ4
  have jmp0 : (step s4).mem.get (step s4).pc = 0 := by
    have hp : (step s4).pc = UInt16.ofNat 87 :=
      hs5pc.trans (rfl : (87 : Word) = UInt16.ofNat 87)
    rw [hp]
    have hmem : (step s4).mem.get (UInt16.ofNat 87) = s4.mem.get (UInt16.ofNat 87) := by
      rw [hs5eq]
    have hget : s4.mem.get (UInt16.ofNat 87) = s.mem.get (UInt16.ofNat 87) :=
      hpres4 (UInt16.ofNat 87) (by decide) (by decide)
    have hval : decChunk005[7]! = 0 := rfl
    exact hmem.trans (hget.trans ((gimg 15 (by decide)).trans ((cell80 7 (by decide)).trans hval)))
  have jmp1 : (step s4).mem.get ((step s4).pc + 1) = 0 := by
    have : (step s4).pc + 1 = (88 : Word) := by simp [hs5pc]
    rw [this, (rfl : (88 : Word) = UInt16.ofNat 88)]
    have hmem : (step s4).mem.get (UInt16.ofNat 88) = s4.mem.get (UInt16.ofNat 88) := by
      rw [hs5eq]
    have hget : s4.mem.get (UInt16.ofNat 88) = s.mem.get (UInt16.ofNat 88) :=
      hpres4 (UInt16.ofNat 88) (by decide) (by decide)
    have hval : decChunk005[8]! = 0 := rfl
    exact hmem.trans (hget.trans ((gimg 16 (by decide)).trans ((cell80 8 (by decide)).trans hval)))
  have jmp2 : (step s4).mem.get ((step s4).pc + 2) = 93 := by
    have : (step s4).pc + 2 = (89 : Word) := by simp [hs5pc]
    rw [this, (rfl : (89 : Word) = UInt16.ofNat 89)]
    have hmem : (step s4).mem.get (UInt16.ofNat 89) = s4.mem.get (UInt16.ofNat 89) := by
      rw [hs5eq]
    have hget : s4.mem.get (UInt16.ofNat 89) = s.mem.get (UInt16.ofNat 89) :=
      hpres4 (UInt16.ofNat 89) (by decide) (by decide)
    have hval : decChunk005[9]! = 93 := rfl
    exact hmem.trans (hget.trans ((gimg 17 (by decide)).trans ((cell80 9 (by decide)).trans hval)))
  have hpc5 : (step s4).pc.toNat < 32768 := by simp [hs5pc]
  have hjmp :=
    step_JMP (s := step s4) (dest := 93)
      hs5h hpc5 hs5Z jmp0 jmp1 jmp2
  have hrun : s6 = step (step s4) :=
    runN_6_of_4_2 s hs4h hpc4 hs5h hpc5
  have hmem6 : (step (step s4)).mem = s4.mem := by
    have h1 : (step s4).mem = s4.mem := by rw [hs5eq]
    have h2 : (step (step s4)).mem = (step s4).mem := by rw [hjmp]
    exact h2.trans h1
  have hs6pc : s6.pc = 93 := by
    rw [hrun, hjmp]
  have hs6h : s6.halted = false := by
    rw [hrun, hjmp]
    exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    rw [hrun, hmem6]
    exact hZ4
  have hs6N : s6.mem.get 17 = input := by
    rw [hrun, hmem6]
    exact hN4
  have hs6M : s6.mem.get 15 = 1 := by
    rw [hrun, hmem6]
    exact hM4
  have hs6T : s6.mem.get 18 = 1 := by
    rw [hrun, hmem6]
    exact hT
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hmem6]
    exact hpres4 a ha18 ha0
  exact ⟨hspc, hs6pc, hs6h, hs6N, hs6Z, hs6M, hs6T, hpres6⟩

/-- After `MOV MODE T`, unsigned mode takes `JLEZ` to `U_PATH` (pc 90) and
the `JMP DIGITS` there, arriving at pc 174 with `T = 0`. -/
theorem mode_dispatch_unsigned (input cap : Word) :
    let s := afterStartMov input 0 cap
    let s6 := runN s 6
    s.pc = 72 ∧
    s6.pc = 174 ∧
    s6.halted = false ∧
    s6.mem.get 17 = input ∧
    s6.mem.get 0 = 0 ∧
    s6.mem.get 15 = 0 ∧
    s6.mem.get 18 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a) := by
  intro s s6
  have hm := mode_mov_MODE_T input 0 cap
  have hspc : s.pc = 72 := hm.1
  let s4 := runN s 4
  have hs4pc : s4.pc = 84 := hm.2.1
  have hs4h : s4.halted = false := hm.2.2.1
  have hT : s4.mem.get 18 = 0 := hm.2.2.2.1
  have hZ4 : s4.mem.get 0 = 0 := hm.2.2.2.2.1
  have hM4 : s4.mem.get 15 = 0 := hm.2.2.2.2.2.1
  have hN4 : s4.mem.get 17 = input := hm.2.2.2.2.2.2.1
  have hpres4 := hm.2.2.2.2.2.2.2
  have gimg (off : Nat) (hoff : off < 21) :
      s.mem.get (UInt16.ofNat (72 + off)) = intfmtImage[72 + off]! :=
    start_mov_code input 0 cap (72 + off) (by omega) (by omega)
  have j0 : s4.mem.get s4.pc = 0 := by
    have hp : s4.pc = UInt16.ofNat 84 :=
      hs4pc.trans (rfl : (84 : Word) = UInt16.ofNat 84)
    rw [hp]
    have hget : s4.mem.get (UInt16.ofNat 84) = s.mem.get (UInt16.ofNat 84) :=
      hpres4 (UInt16.ofNat 84) (by decide) (by decide)
    have hval : decChunk005[4]! = 0 := rfl
    exact hget.trans ((gimg 12 (by decide)).trans ((cell80 4 (by decide)).trans hval))
  have j1 : s4.mem.get (s4.pc + 1) = 18 := by
    have : s4.pc + 1 = (85 : Word) := by simp [hs4pc]
    rw [this, (rfl : (85 : Word) = UInt16.ofNat 85)]
    have hget : s4.mem.get (UInt16.ofNat 85) = s.mem.get (UInt16.ofNat 85) :=
      hpres4 (UInt16.ofNat 85) (by decide) (by decide)
    have hval : decChunk005[5]! = 18 := rfl
    exact hget.trans ((gimg 13 (by decide)).trans ((cell80 5 (by decide)).trans hval))
  have j2 : s4.mem.get (s4.pc + 2) = 90 := by
    have : s4.pc + 2 = (86 : Word) := by simp [hs4pc]
    rw [this, (rfl : (86 : Word) = UInt16.ofNat 86)]
    have hget : s4.mem.get (UInt16.ofNat 86) = s.mem.get (UInt16.ofNat 86) :=
      hpres4 (UInt16.ofNat 86) (by decide) (by decide)
    have hval : decChunk005[6]! = 90 := rfl
    exact hget.trans ((gimg 14 (by decide)).trans ((cell80 6 (by decide)).trans hval))
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hjlez :=
    step_JLEZ (s := s4) (x := 18) (dest := 90)
      hs4h hpc4 hZ4 j0 j1 j2 (by decide)
  have hle : (s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18) = true := by
    have : le0 (s4.mem.get 18) = true := by
      rw [hT]
      exact le0_zero
    simpa [le0] using this
  have hs5eq : step s4 = { s4 with pc := 90 } := by
    have hif :
        (if s4.mem.get 18 = 0 || 0x8000 ≤ s4.mem.get 18 then (90 : Word)
          else s4.pc + 3) = (90 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hs5pc : (step s4).pc = 90 := by
    rw [hs5eq]
  have hs5h : (step s4).halted = false := by
    rw [hs5eq]
    exact hs4h
  have hs5Z : (step s4).mem.get 0 = 0 := by
    rw [hs5eq]
    exact hZ4
  have jmp0 : (step s4).mem.get (step s4).pc = 0 := by
    have hp : (step s4).pc = UInt16.ofNat 90 :=
      hs5pc.trans (rfl : (90 : Word) = UInt16.ofNat 90)
    rw [hp]
    have hmem : (step s4).mem.get (UInt16.ofNat 90) = s4.mem.get (UInt16.ofNat 90) := by
      rw [hs5eq]
    have hget : s4.mem.get (UInt16.ofNat 90) = s.mem.get (UInt16.ofNat 90) :=
      hpres4 (UInt16.ofNat 90) (by decide) (by decide)
    have hval : decChunk005[10]! = 0 := rfl
    exact hmem.trans (hget.trans ((gimg 18 (by decide)).trans ((cell80 10 (by decide)).trans hval)))
  have jmp1 : (step s4).mem.get ((step s4).pc + 1) = 0 := by
    have : (step s4).pc + 1 = (91 : Word) := by simp [hs5pc]
    rw [this, (rfl : (91 : Word) = UInt16.ofNat 91)]
    have hmem : (step s4).mem.get (UInt16.ofNat 91) = s4.mem.get (UInt16.ofNat 91) := by
      rw [hs5eq]
    have hget : s4.mem.get (UInt16.ofNat 91) = s.mem.get (UInt16.ofNat 91) :=
      hpres4 (UInt16.ofNat 91) (by decide) (by decide)
    have hval : decChunk005[11]! = 0 := rfl
    exact hmem.trans (hget.trans ((gimg 19 (by decide)).trans ((cell80 11 (by decide)).trans hval)))
  have jmp2 : (step s4).mem.get ((step s4).pc + 2) = 174 := by
    have : (step s4).pc + 2 = (92 : Word) := by simp [hs5pc]
    rw [this, (rfl : (92 : Word) = UInt16.ofNat 92)]
    have hmem : (step s4).mem.get (UInt16.ofNat 92) = s4.mem.get (UInt16.ofNat 92) := by
      rw [hs5eq]
    have hget : s4.mem.get (UInt16.ofNat 92) = s.mem.get (UInt16.ofNat 92) :=
      hpres4 (UInt16.ofNat 92) (by decide) (by decide)
    have hval : decChunk005[12]! = 174 := rfl
    exact hmem.trans (hget.trans ((gimg 20 (by decide)).trans ((cell80 12 (by decide)).trans hval)))
  have hpc5 : (step s4).pc.toNat < 32768 := by simp [hs5pc]
  have hjmp :=
    step_JMP (s := step s4) (dest := 174)
      hs5h hpc5 hs5Z jmp0 jmp1 jmp2
  have hrun : s6 = step (step s4) :=
    runN_6_of_4_2 s hs4h hpc4 hs5h hpc5
  have hmem6 : (step (step s4)).mem = s4.mem := by
    have h1 : (step s4).mem = s4.mem := by rw [hs5eq]
    have h2 : (step (step s4)).mem = (step s4).mem := by rw [hjmp]
    exact h2.trans h1
  have hs6pc : s6.pc = 174 := by
    rw [hrun, hjmp]
  have hs6h : s6.halted = false := by
    rw [hrun, hjmp]
    exact hs5h
  have hs6Z : s6.mem.get 0 = 0 := by
    rw [hrun, hmem6]
    exact hZ4
  have hs6N : s6.mem.get 17 = input := by
    rw [hrun, hmem6]
    exact hN4
  have hs6M : s6.mem.get 15 = 0 := by
    rw [hrun, hmem6]
    exact hM4
  have hs6T : s6.mem.get 18 = 0 := by
    rw [hrun, hmem6]
    exact hT
  have hpres6 : ∀ a, a ≠ 18 → a ≠ 0 → s6.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hmem6]
    exact hpres4 a ha18 ha0
  exact ⟨hspc, hs6pc, hs6h, hs6N, hs6Z, hs6M, hs6T, hpres6⟩

end IntFmt
