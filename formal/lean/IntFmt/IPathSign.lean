/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Signed `I_PATH` (pc 93) on the assembled `intfmt.dec` image, composed
with `mode_dispatch_signed`. Block lemmas, not end-to-end correctness.

From pc 93 the residual `MOV N T; SUB K32768 T` runs, then the real
sign test `MOV N T; JLEZ T maybe_neg; JMP DIGITS`. Positives take 11
steps to `DIGITS` (pc 174); zero takes 15; negatives take 25 and set
`SIGN = 1` with `N` the two's-complement magnitude.
-/

import IntFmt.IPath

namespace IntFmt

open Subleq

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-- Machine at `I_PATH` after signed mode dispatch. Irreducible so later
`runN` lemmas do not unfold the loaded image. -/
@[irreducible] def afterSignedDispatch (input cap : Word) : Machine :=
  runN (afterStartMov input 1 cap) 6

theorem afterSignedDispatch_eq (input cap : Word) :
    afterSignedDispatch input cap = runN (afterStartMov input 1 cap) 6 := by
  unfold afterSignedDispatch
  rfl

/-- `runN s (m + n) = runN (runN s m) n` with a concrete sum. -/
private theorem runN_add_eq (s : Machine) (m n k : Nat) (h : m + n = k) :
    runN s k = runN (runN s m) n := by
  have hmn := runN_add s m n
  rw [h] at hmn
  exact hmn

private theorem runN_2_steps (s : Machine)
    (hh : s.halted = false) (hpc : s.pc.toNat < 32768)
    (h5h : (step s).halted = false) (h5pc : (step s).pc.toNat < 32768) :
    runN s 2 = step (step s) := by
  have h := runN_succ_go s 1 hh hpc
  have h2 := runN_one (step s) h5h h5pc
  exact h.trans h2

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

private theorem cell80 (off : Nat) (h : off < 16) :
    intfmtImage[80 + off]! = decChunk005[off]! :=
  extract_chunk 80 decChunk005 image_chunk005 off h (by decide)

private theorem cell96 (off : Nat) (h : off < 16) :
    intfmtImage[96 + off]! = decChunk006[off]! :=
  extract_chunk 96 decChunk006 image_chunk006 off h (by decide)

private theorem cell112 (off : Nat) (h : off < 16) :
    intfmtImage[112 + off]! = decChunk007[off]! :=
  extract_chunk 112 decChunk007 image_chunk007 off h (by decide)

private theorem cell128 (off : Nat) (h : off < 16) :
    intfmtImage[128 + off]! = decChunk008[off]! :=
  extract_chunk 128 decChunk008 image_chunk008 off h (by decide)

private theorem cell144 (off : Nat) (h : off < 16) :
    intfmtImage[144 + off]! = decChunk009[off]! :=
  extract_chunk 144 decChunk009 image_chunk009 off h (by decide)

private theorem cell160 (off : Nat) (h : off < 16) :
    intfmtImage[160 + off]! = decChunk010[off]! :=
  extract_chunk 160 decChunk010 image_chunk010 off h (by decide)

private theorem word_pc_off {s : Machine} (base off : Nat)
    (hspc : s.pc = UInt16.ofNat base) (hsum : base + off < 65536) :
    s.pc + UInt16.ofNat off = UInt16.ofNat (base + off) := by
  have hton : s.pc.toNat = base := by
    have : (UInt16.ofNat base).toNat = base :=
      UInt16.toNat_ofNat_of_lt (by have hsz : UInt16.size = 65536 := rfl; rw [hsz]; omega)
    simpa [hspc] using this
  apply UInt16.toNat.inj
  have hsz : UInt16.size = 65536 := rfl
  have hbound : s.pc.toNat + off < 65536 := by rw [hton]; omega
  have hL : (s.pc + UInt16.ofNat off).toNat = base + off := by
    have hw := word_add_toNat s.pc off hbound
    omega
  have hR : (UInt16.ofNat (base + off)).toNat = base + off :=
    UInt16.toNat_ofNat_of_lt (by rw [hsz]; omega)
  exact hL.trans hR.symm

private theorem pc_off_ne {s : Machine} (base i target : Nat)
    (hspc : s.pc = UInt16.ofNat base)
    (hsum : base + i < 65536) (ht : target < 65536)
    (hne : base + i ≠ target) :
    s.pc + UInt16.ofNat i ≠ UInt16.ofNat target := by
  intro h
  have heq := (word_pc_off base i hspc hsum).symm.trans h
  have hx := congrArg UInt16.toNat heq
  have hsz : UInt16.size = 65536 := rfl
  have hL : (UInt16.ofNat (base + i)).toNat = base + i :=
    UInt16.toNat_ofNat_of_lt (by rw [hsz]; omega)
  have hR : (UInt16.ofNat target).toNat = target :=
    UInt16.toNat_ofNat_of_lt (by rw [hsz]; omega)
  have : base + i = target := by
    rw [hL, hR] at hx
    exact hx
  exact hne this

private theorem ofNat_ne (a b : Nat)
    (ha : a < 65536) (hb : b < 65536) (hne : a ≠ b) :
    UInt16.ofNat a ≠ UInt16.ofNat b := by
  intro h
  have hsz : UInt16.size = 65536 := rfl
  have hL : (UInt16.ofNat a).toNat = a :=
    UInt16.toNat_ofNat_of_lt (by rw [hsz]; exact ha)
  have hR : (UInt16.ofNat b).toNat = b :=
    UInt16.toNat_ofNat_of_lt (by rw [hsz]; exact hb)
  have : a = b := by
    have hx := congrArg UInt16.toNat h
    rw [hL, hR] at hx
    exact hx
  exact hne this


private theorem le0_succ_neg {w : Word} (h : 32768 ≤ w.toNat) :
    le0 (w + 1) = true := by
  have hsz : UInt16.size = 65536 := rfl
  have hwlt : w.toNat < 65536 := by
    simpa [hsz] using UInt16.toNat_lt_size w
  by_cases hmax : w.toNat = 65535
  · have hw0 : w + 1 = 0 := by
      apply UInt16.toNat.inj
      have hadd : (w + 1).toNat = (w.toNat + (1 : Word).toNat) % 65536 :=
        UInt16.toNat_add w 1
      have hone : (1 : Word).toNat = 1 := rfl
      have h0 : (0 : Word).toNat = 0 := rfl
      rw [hadd, hone, hmax]
      exact h0.symm
    rw [hw0]
    exact le0_zero
  · have hlt : w.toNat + 1 < 65536 := by omega
    have hton : (w + 1).toNat = w.toNat + 1 := by
      have hadd : (w + 1).toNat = (w.toNat + (1 : Word).toNat) % 65536 :=
        UInt16.toNat_add w 1
      have hone : (1 : Word).toNat = 1 := rfl
      rw [hadd, hone, Nat.mod_eq_of_lt hlt]
    exact le0_hi (by omega)

/-- Entry state at `I_PATH` after signed dispatch. -/
theorem afterSignedDispatch_entry (input cap : Word) :
    let s := afterSignedDispatch input cap
    s.pc = 93 ∧
    s.halted = false ∧
    s.mem.get 17 = input ∧
    s.mem.get 0 = 0 ∧
    s.mem.get 15 = 1 ∧
    s.mem.get 18 = 1 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s.mem.get a = (afterStartMov input 1 cap).mem.get a) := by
  intro s
  have heq := afterSignedDispatch_eq input cap
  have hm := mode_dispatch_signed input cap
  have hsdef : s = afterSignedDispatch input cap := rfl
  refine ⟨?pc, ?hh, ?n, ?z, ?m, ?t, ?pres⟩
  · rw [hsdef, heq]; exact hm.2.1
  · rw [hsdef, heq]; exact hm.2.2.1
  · rw [hsdef, heq]; exact hm.2.2.2.1
  · rw [hsdef, heq]; exact hm.2.2.2.2.1
  · rw [hsdef, heq]; exact hm.2.2.2.2.2.1
  · rw [hsdef, heq]; exact hm.2.2.2.2.2.2.1
  · intro a ha18 ha0
    rw [hsdef, heq]
    exact hm.2.2.2.2.2.2.2 a ha18 ha0

/-- Program / constant cells still match the image (not N, T, Z, or the
poked / START-cleared registers). -/
theorem afterSignedDispatch_get (input cap : Word) (k : Nat)
    (hk : k < 2323)
    (hIn : k ≠ 12) (hMo : k ≠ 15) (hCa : k ≠ 13)
    (hSIGN : k ≠ 19) (hLEN : k ≠ 16) (hPAD : k ≠ 27) (hNDIG : k ≠ 25)
    (hN : k ≠ 17) (hZ : k ≠ 0) (hT : k ≠ 18) :
    (afterSignedDispatch input cap).mem.get (UInt16.ofNat k) =
      intfmtImage[k]! := by
  have hent := afterSignedDispatch_entry input cap
  have hpres := hent.2.2.2.2.2.2
  have hsm := start_mov_get input 1 cap k hk
    hIn hMo hCa hSIGN hLEN hPAD hNDIG hN hZ
  have hton : (UInt16.ofNat k).toNat = k := ofNat_toNat_image (by
    rw [intfmtImage_size]; exact hk)
  have h18 : UInt16.ofNat k ≠ 18 := by
    intro h
    have : k = 18 := by
      have hx := congrArg UInt16.toNat h
      simpa [hton] using hx
    exact hT this
  have h0 : UInt16.ofNat k ≠ 0 := by
    intro h
    have : k = 0 := by
      have hx := congrArg UInt16.toNat h
      simpa [hton] using hx
    exact hZ this
  have hstart : (afterStartMov input 1 cap).mem.get (UInt16.ofNat k) =
      intfmtImage[k]! := by
    rw [afterStartMov_eq]
    exact hsm
  exact (hpres (UInt16.ofNat k) h18 h0).trans hstart

private theorem ipath_code (input cap : Word) (k : Nat)
    (hk : 93 ≤ k) (hk2 : k < 174) :
    (afterSignedDispatch input cap).mem.get (UInt16.ofNat k) =
      intfmtImage[k]! :=
  afterSignedDispatch_get input cap k (by omega)
    (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)

theorem afterSignedDispatch_get_ONE (input cap : Word) :
    (afterSignedDispatch input cap).mem.get 3 = 1 := by
  have hpres := (afterSignedDispatch_entry input cap).2.2.2.2.2.2
  have h := start_mov_get_ONE input 1 cap
  exact (hpres 3 (by decide) (by decide)).trans h

theorem afterSignedDispatch_get_K32768 (input cap : Word) :
    (afterSignedDispatch input cap).mem.get 11 = 32768 := by
  have h := afterSignedDispatch_get input cap 11 (by decide)
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hk : (11 : Word) = UInt16.ofNat 11 := rfl
  rw [hk]
  exact h.trans image_cell_K32768

theorem afterSignedDispatch_get_SIGN (input cap : Word) :
    (afterSignedDispatch input cap).mem.get 19 = 0 := by
  have hpresD := (afterSignedDispatch_entry input cap).2.2.2.2.2.2
  have hsm := start_mov_INPUT_N input 1 cap
  have hz := start_zero_regs input 1 cap
  have h8 : (afterStartMov input 1 cap).mem.get 19 = 0 := by
    rw [afterStartMov_eq]
    have h4 : (runN (step (prepMachine input 1 cap)) 4).mem.get 19 = 0 :=
      hz.2.2.2.1
    exact (hsm.2.2.2.2.2.2 19 (by decide) (by decide)).trans h4
  exact (hpresD 19 (by decide) (by decide)).trans h8

/-- After the residual `MOV N T; SUB K32768 T` and the real `MOV N T`,
the machine is at the sign-test `JLEZ` (pc 120) with `T = N`. -/
theorem i_path_prelude (input cap : Word) :
    let s := afterSignedDispatch input cap
    let s9 := runN s 9
    s.pc = 93 ∧
    s9.pc = 120 ∧
    s9.halted = false ∧
    s9.mem.get 17 = input ∧
    s9.mem.get 18 = input ∧
    s9.mem.get 0 = 0 ∧
    s9.mem.get 19 = 0 ∧
    s9.mem.get 15 = 1 ∧
    s9.mem.get 3 = 1 ∧
    s9.mem.get 11 = 32768 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a) := by
  intro s s9
  have he := afterSignedDispatch_entry input cap
  have hspc : s.pc = 93 := he.1
  have hsh : s.halted = false := he.2.1
  have hN0 : s.mem.get 17 = input := he.2.2.1
  have hZ : s.mem.get 0 = 0 := he.2.2.2.1
  have hMODE : s.mem.get 15 = 1 := he.2.2.2.2.1
  have hSIGN0 := afterSignedDispatch_get_SIGN input cap
  have hONE0 := afterSignedDispatch_get_ONE input cap
  have hK0 := afterSignedDispatch_get_K32768 input cap
  have hp : s.pc = UInt16.ofNat 93 :=
    hspc.trans (rfl : (93 : Word) = UInt16.ofNat 93)
  have poff (off : Nat) (hoff : off ≤ 27) :
      s.pc + UInt16.ofNat off = UInt16.ofNat (93 + off) :=
    word_pc_off 93 off hp (by omega)
  have gimg (off : Nat) (hoff : off < 27) :
      s.mem.get (UInt16.ofNat (93 + off)) = intfmtImage[93 + off]! :=
    ipath_code input cap (93 + off) (by omega) (by omega)
  -- MOV N T at pc 93
  have h0 : s.mem.get s.pc = 18 := by
    rw [hp]
    have hval : decChunk005[13]! = 18 := rfl
    exact (gimg 0 (by decide)).trans ((cell80 13 (by decide)).trans hval)
  have h1 : s.mem.get (s.pc + UInt16.ofNat 1) = 18 := by
    rw [poff 1 (by decide)]
    have hval : decChunk005[14]! = 18 := rfl
    exact (gimg 1 (by decide)).trans ((cell80 14 (by decide)).trans hval)
  have h2 : s.mem.get (s.pc + UInt16.ofNat 2) = s.pc + UInt16.ofNat 3 := by
    rw [poff 2 (by decide), poff 3 (by decide)]
    have hval : decChunk005[15]! = 96 := rfl
    have hv : (96 : Word) = UInt16.ofNat 96 := rfl
    exact (gimg 2 (by decide)).trans ((cell80 15 (by decide)).trans (hval.trans hv))
  have h3 : s.mem.get (s.pc + UInt16.ofNat 3) = 17 := by
    rw [poff 3 (by decide)]
    have hval : decChunk006[0]! = 17 := rfl
    exact (gimg 3 (by decide)).trans ((cell96 0 (by decide)).trans hval)
  have h4 : s.mem.get (s.pc + UInt16.ofNat 4) = 0 := by
    rw [poff 4 (by decide)]
    have hval : decChunk006[1]! = 0 := rfl
    exact (gimg 4 (by decide)).trans ((cell96 1 (by decide)).trans hval)
  have h5 : s.mem.get (s.pc + UInt16.ofNat 5) = s.pc + UInt16.ofNat 6 := by
    rw [poff 5 (by decide), poff 6 (by decide)]
    have hval : decChunk006[2]! = 99 := rfl
    have hv : (99 : Word) = UInt16.ofNat 99 := rfl
    exact (gimg 5 (by decide)).trans ((cell96 2 (by decide)).trans (hval.trans hv))
  have h6c : s.mem.get (s.pc + UInt16.ofNat 6) = 0 := by
    rw [poff 6 (by decide)]
    have hval : decChunk006[3]! = 0 := rfl
    exact (gimg 6 (by decide)).trans ((cell96 3 (by decide)).trans hval)
  have h7 : s.mem.get (s.pc + UInt16.ofNat 7) = 18 := by
    rw [poff 7 (by decide)]
    have hval : decChunk006[4]! = 18 := rfl
    exact (gimg 7 (by decide)).trans ((cell96 4 (by decide)).trans hval)
  have h8 : s.mem.get (s.pc + UInt16.ofNat 8) = s.pc + UInt16.ofNat 9 := by
    rw [poff 8 (by decide), poff 9 (by decide)]
    have hval : decChunk006[5]! = 102 := rfl
    have hv : (102 : Word) = UInt16.ofNat 102 := rfl
    exact (gimg 8 (by decide)).trans ((cell96 5 (by decide)).trans (hval.trans hv))
  have h9 : s.mem.get (s.pc + UInt16.ofNat 9) = 0 := by
    rw [poff 9 (by decide)]
    have hval : decChunk006[6]! = 0 := rfl
    exact (gimg 9 (by decide)).trans ((cell96 6 (by decide)).trans hval)
  have h10 : s.mem.get (s.pc + UInt16.ofNat 10) = 0 := by
    rw [poff 10 (by decide)]
    have hval : decChunk006[7]! = 0 := rfl
    exact (gimg 10 (by decide)).trans ((cell96 7 (by decide)).trans hval)
  have h11 : s.mem.get (s.pc + UInt16.ofNat 11) = s.pc + UInt16.ofNat 12 := by
    rw [poff 11 (by decide), poff 12 (by decide)]
    have hval : decChunk006[8]! = 105 := rfl
    have hv : (105 : Word) = UInt16.ofNat 105 := rfl
    exact (gimg 11 (by decide)).trans ((cell96 8 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 93 i 18 hp (by omega) (by omega) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 93 i 0 hp (by omega) (by omega) (by omega)
  have hpc : s.pc.toNat + 12 ≤ 32768 := by simp [hspc]
  have hpc0 : 0 < s.pc.toNat := by simp [hspc]
  have hmov1 :=
    runN_MOV (s := s) (src := 17) (dst := 18)
      hsh hpc hpc0 hZ (by decide) (by decide) (by decide) (by decide)
      h0 h1 h2 h3 h4 h5 h6c h7 h8 h9 h10 h11 hcodeD hcodeZ
  let s4 := runN s 4
  have hs4pc : s4.pc = 105 := by
    have hadd : s.pc + UInt16.ofNat 12 = (105 : Word) := by
      rw [poff 12 (by decide)]
      exact (rfl : UInt16.ofNat 105 = (105 : Word))
    exact hmov1.1.trans hadd
  have hs4h : s4.halted = false := hmov1.2.1
  have hT4 : s4.mem.get 18 = input := hmov1.2.2.1.trans hN0
  have hZ4 : s4.mem.get 0 = 0 := hmov1.2.2.2.1
  have hpres4 := hmov1.2.2.2.2.2
  have hN4 : s4.mem.get 17 = input := hmov1.2.2.2.2.1.trans hN0
  -- SUB K32768 T at pc 105 (fall-through)
  have sub0 : s4.mem.get s4.pc = 11 := by
    have hp4 : s4.pc = UInt16.ofNat 105 :=
      hs4pc.trans (rfl : (105 : Word) = UInt16.ofNat 105)
    rw [hp4]
    have hget : s4.mem.get (UInt16.ofNat 105) = s.mem.get (UInt16.ofNat 105) :=
      hpres4 (UInt16.ofNat 105) (by decide) (by decide)
    have hval : decChunk006[9]! = 11 := rfl
    exact hget.trans ((gimg 12 (by decide)).trans ((cell96 9 (by decide)).trans hval))
  have sub1 : s4.mem.get (s4.pc + 1) = 18 := by
    have : s4.pc + 1 = (106 : Word) := by simp [hs4pc]
    rw [this, (rfl : (106 : Word) = UInt16.ofNat 106)]
    have hget : s4.mem.get (UInt16.ofNat 106) = s.mem.get (UInt16.ofNat 106) :=
      hpres4 (UInt16.ofNat 106) (by decide) (by decide)
    have hval : decChunk006[10]! = 18 := rfl
    exact hget.trans ((gimg 13 (by decide)).trans ((cell96 10 (by decide)).trans hval))
  have sub2 : s4.mem.get (s4.pc + 2) = s4.pc + 3 := by
    have hp107 : s4.pc + 2 = (107 : Word) := by simp [hs4pc]
    have hp108 : s4.pc + 3 = (108 : Word) := by simp [hs4pc]
    rw [hp107, hp108]
    rw [(rfl : (107 : Word) = UInt16.ofNat 107)]
    have hget : s4.mem.get (UInt16.ofNat 107) = s.mem.get (UInt16.ofNat 107) :=
      hpres4 (UInt16.ofNat 107) (by decide) (by decide)
    have hval : decChunk006[11]! = 108 := rfl
    have hv : (108 : Word) = UInt16.ofNat 108 := rfl
    exact hget.trans ((gimg 14 (by decide)).trans ((cell96 11 (by decide)).trans (hval.trans hv)))
  have hpc4 : s4.pc.toNat < 32768 := by simp [hs4pc]
  have hsub :=
    step_SUB (s := s4) (a := 11) (b := 18)
      hs4h hpc4 sub0 sub1 sub2 (by decide) (by decide)
  have hs5eq := hsub
  have hs5pc : (step s4).pc = 108 := by
    have : s4.pc + 3 = (108 : Word) := by simp [hs4pc]
    rw [hs5eq]
    exact this
  have hs5h : (step s4).halted = false := by
    rw [hs5eq]
    exact hs4h
  have hs5Z : (step s4).mem.get 0 = 0 := by
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 0 (s4.mem.get 18 - s4.mem.get 11) (by decide)).trans hZ4
  have hs5N : (step s4).mem.get 17 = input := by
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 17 (s4.mem.get 18 - s4.mem.get 11) (by decide)).trans hN4
  have hpres5 : ∀ a, a ≠ 18 → a ≠ 0 → (step s4).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs5eq]
    exact (Mem.get_set_ne s4.mem 18 a (s4.mem.get 18 - s4.mem.get 11) ha18).trans
      (hpres4 a ha18 ha0)
  -- second MOV N T at pc 108
  let s5 := step s4
  have hp5 : s5.pc = UInt16.ofNat 108 :=
    hs5pc.trans (rfl : (108 : Word) = UInt16.ofNat 108)
  have poff5 (off : Nat) (hoff : off ≤ 12) :
      s5.pc + UInt16.ofNat off = UInt16.ofNat (108 + off) :=
    word_pc_off 108 off hp5 (by omega)
  have g5 (off : Nat) (hoff : off < 12) :
      s5.mem.get (UInt16.ofNat (108 + off)) = intfmtImage[108 + off]! := by
    have hcell : s.mem.get (UInt16.ofNat (108 + off)) = intfmtImage[108 + off]! :=
      ipath_code input cap (108 + off) (by omega) (by omega)
    have hne18 : UInt16.ofNat (108 + off) ≠ 18 :=
      ofNat_ne (108 + off) 18 (by omega) (by omega) (by omega)
    have hne0 : UInt16.ofNat (108 + off) ≠ 0 :=
      ofNat_ne (108 + off) 0 (by omega) (by omega) (by omega)
    exact (hpres5 (UInt16.ofNat (108 + off)) hne18 hne0).trans hcell
  have m0 : s5.mem.get s5.pc = 18 := by
    rw [hp5]
    have hval : decChunk006[12]! = 18 := rfl
    exact (g5 0 (by decide)).trans ((cell96 12 (by decide)).trans hval)
  have m1 : s5.mem.get (s5.pc + UInt16.ofNat 1) = 18 := by
    rw [poff5 1 (by decide)]
    have hval : decChunk006[13]! = 18 := rfl
    exact (g5 1 (by decide)).trans ((cell96 13 (by decide)).trans hval)
  have m2 : s5.mem.get (s5.pc + UInt16.ofNat 2) = s5.pc + UInt16.ofNat 3 := by
    rw [poff5 2 (by decide), poff5 3 (by decide)]
    have hval : decChunk006[14]! = 111 := rfl
    have hv : (111 : Word) = UInt16.ofNat 111 := rfl
    exact (g5 2 (by decide)).trans ((cell96 14 (by decide)).trans (hval.trans hv))
  have m3 : s5.mem.get (s5.pc + UInt16.ofNat 3) = 17 := by
    rw [poff5 3 (by decide)]
    have hval : decChunk006[15]! = 17 := rfl
    exact (g5 3 (by decide)).trans ((cell96 15 (by decide)).trans hval)
  have m4 : s5.mem.get (s5.pc + UInt16.ofNat 4) = 0 := by
    rw [poff5 4 (by decide)]
    have hval : decChunk007[0]! = 0 := rfl
    exact (g5 4 (by decide)).trans ((cell112 0 (by decide)).trans hval)
  have m5 : s5.mem.get (s5.pc + UInt16.ofNat 5) = s5.pc + UInt16.ofNat 6 := by
    rw [poff5 5 (by decide), poff5 6 (by decide)]
    have hval : decChunk007[1]! = 114 := rfl
    have hv : (114 : Word) = UInt16.ofNat 114 := rfl
    exact (g5 5 (by decide)).trans ((cell112 1 (by decide)).trans (hval.trans hv))
  have m6 : s5.mem.get (s5.pc + UInt16.ofNat 6) = 0 := by
    rw [poff5 6 (by decide)]
    have hval : decChunk007[2]! = 0 := rfl
    exact (g5 6 (by decide)).trans ((cell112 2 (by decide)).trans hval)
  have m7 : s5.mem.get (s5.pc + UInt16.ofNat 7) = 18 := by
    rw [poff5 7 (by decide)]
    have hval : decChunk007[3]! = 18 := rfl
    exact (g5 7 (by decide)).trans ((cell112 3 (by decide)).trans hval)
  have m8 : s5.mem.get (s5.pc + UInt16.ofNat 8) = s5.pc + UInt16.ofNat 9 := by
    rw [poff5 8 (by decide), poff5 9 (by decide)]
    have hval : decChunk007[4]! = 117 := rfl
    have hv : (117 : Word) = UInt16.ofNat 117 := rfl
    exact (g5 8 (by decide)).trans ((cell112 4 (by decide)).trans (hval.trans hv))
  have m9 : s5.mem.get (s5.pc + UInt16.ofNat 9) = 0 := by
    rw [poff5 9 (by decide)]
    have hval : decChunk007[5]! = 0 := rfl
    exact (g5 9 (by decide)).trans ((cell112 5 (by decide)).trans hval)
  have m10 : s5.mem.get (s5.pc + UInt16.ofNat 10) = 0 := by
    rw [poff5 10 (by decide)]
    have hval : decChunk007[6]! = 0 := rfl
    exact (g5 10 (by decide)).trans ((cell112 6 (by decide)).trans hval)
  have m11 : s5.mem.get (s5.pc + UInt16.ofNat 11) = s5.pc + UInt16.ofNat 12 := by
    rw [poff5 11 (by decide), poff5 12 (by decide)]
    have hval : decChunk007[7]! = 120 := rfl
    have hv : (120 : Word) = UInt16.ofNat 120 := rfl
    exact (g5 11 (by decide)).trans ((cell112 7 (by decide)).trans (hval.trans hv))
  have hcodeD5 : ∀ i : Nat, i < 12 → s5.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 108 i 18 hp5 (by omega) (by omega) (by omega)
  have hcodeZ5 : ∀ i : Nat, i < 12 → s5.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 108 i 0 hp5 (by omega) (by omega) (by omega)
  have hpc5 : s5.pc.toNat + 12 ≤ 32768 := by
    have : s5.pc = 108 := hs5pc
    simp [this]
  have hpc50 : 0 < s5.pc.toNat := by
    have : s5.pc = 108 := hs5pc
    simp [this]
  have hmov2 :=
    runN_MOV (s := s5) (src := 17) (dst := 18)
      hs5h hpc5 hpc50 hs5Z (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD5 hcodeZ5
  have hrun : s9 = runN s5 4 := by
    have h95 : runN s 9 = runN (runN s 4) 5 := runN_add_eq s 4 5 9 (by decide)
    have hgo : runN s4 5 = runN (step s4) 4 := runN_succ_go s4 4 hs4h hpc4
    exact h95.trans hgo
  have hs9pc : s9.pc = 120 := by
    have hadd : s5.pc + UInt16.ofNat 12 = (120 : Word) := by
      rw [poff5 12 (by decide)]
      exact (rfl : UInt16.ofNat 120 = (120 : Word))
    rw [hrun]
    exact hmov2.1.trans hadd
  have hs9h : s9.halted = false := by
    rw [hrun]
    exact hmov2.2.1
  have hs9T : s9.mem.get 18 = input := by
    rw [hrun]
    exact hmov2.2.2.1.trans hs5N
  have hs9Z : s9.mem.get 0 = 0 := by
    rw [hrun]
    exact hmov2.2.2.2.1
  have hpres9 : ∀ a, a ≠ 18 → a ≠ 0 → s9.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun]
    exact (hmov2.2.2.2.2.2 a ha18 ha0).trans (hpres5 a ha18 ha0)
  have hs9N : s9.mem.get 17 = input :=
    (hpres9 17 (by decide) (by decide)).trans hN0
  have hs9S : s9.mem.get 19 = 0 := by
    have : s.mem.get 19 = 0 := hSIGN0
    exact (hpres9 19 (by decide) (by decide)).trans this
  have hs9M : s9.mem.get 15 = 1 :=
    (hpres9 15 (by decide) (by decide)).trans hMODE
  have hs9O : s9.mem.get 3 = 1 :=
    (hpres9 3 (by decide) (by decide)).trans hONE0
  have hs9K : s9.mem.get 11 = 32768 :=
    (hpres9 11 (by decide) (by decide)).trans hK0
  exact ⟨hspc, hs9pc, hs9h, hs9N, hs9T, hs9Z, hs9S, hs9M, hs9O, hs9K, hpres9⟩

/-- Positive `N` (1..32767): `JLEZ` falls through and `JMP DIGITS` in 2
further steps (11 from `I_PATH`). `SIGN` stays 0 and `T = N`. -/
theorem i_path_pos (input cap : Word)
    (hpos : 0 < input.toNat) (hhi : input.toNat < 32768) :
    let s := afterSignedDispatch input cap
    let s11 := runN s 11
    s11.pc = 174 ∧
    s11.halted = false ∧
    s11.mem.get 17 = input ∧
    s11.mem.get 18 = input ∧
    s11.mem.get 0 = 0 ∧
    s11.mem.get 19 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a) := by
  intro s s11
  have hp := i_path_prelude input cap
  let s9 := runN s 9
  have hs9pc : s9.pc = 120 := hp.2.1
  have hs9h : s9.halted = false := hp.2.2.1
  have hN9 : s9.mem.get 17 = input := hp.2.2.2.1
  have hT9 : s9.mem.get 18 = input := hp.2.2.2.2.1
  have hZ9 : s9.mem.get 0 = 0 := hp.2.2.2.2.2.1
  have hS9 : s9.mem.get 19 = 0 := hp.2.2.2.2.2.2.1
  have hpres9 := hp.2.2.2.2.2.2.2.2.2.2
  have gimg (off : Nat) (hoff : off < 6) :
      s.mem.get (UInt16.ofNat (120 + off)) = intfmtImage[120 + off]! :=
    ipath_code input cap (120 + off) (by omega) (by omega)
  have j0 : s9.mem.get s9.pc = 0 := by
    have hp9 : s9.pc = UInt16.ofNat 120 :=
      hs9pc.trans (rfl : (120 : Word) = UInt16.ofNat 120)
    rw [hp9]
    have hget : s9.mem.get (UInt16.ofNat 120) = s.mem.get (UInt16.ofNat 120) :=
      hpres9 (UInt16.ofNat 120) (by decide) (by decide)
    have hval : decChunk007[8]! = 0 := rfl
    exact hget.trans ((gimg 0 (by decide)).trans ((cell112 8 (by decide)).trans hval))
  have j1 : s9.mem.get (s9.pc + 1) = 18 := by
    have : s9.pc + 1 = (121 : Word) := by simp [hs9pc]
    rw [this, (rfl : (121 : Word) = UInt16.ofNat 121)]
    have hget : s9.mem.get (UInt16.ofNat 121) = s.mem.get (UInt16.ofNat 121) :=
      hpres9 (UInt16.ofNat 121) (by decide) (by decide)
    have hval : decChunk007[9]! = 18 := rfl
    exact hget.trans ((gimg 1 (by decide)).trans ((cell112 9 (by decide)).trans hval))
  have j2 : s9.mem.get (s9.pc + 2) = 126 := by
    have : s9.pc + 2 = (122 : Word) := by simp [hs9pc]
    rw [this, (rfl : (122 : Word) = UInt16.ofNat 122)]
    have hget : s9.mem.get (UInt16.ofNat 122) = s.mem.get (UInt16.ofNat 122) :=
      hpres9 (UInt16.ofNat 122) (by decide) (by decide)
    have hval : decChunk007[10]! = 126 := rfl
    exact hget.trans ((gimg 2 (by decide)).trans ((cell112 10 (by decide)).trans hval))
  have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
  have hjlez :=
    step_JLEZ (s := s9) (x := 18) (dest := 126)
      hs9h hpc9 hZ9 j0 j1 j2 (by decide)
  have hle : (s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18) = false := by
    have : le0 (s9.mem.get 18) = false := by
      rw [hT9]
      exact le0_pos hpos hhi
    simpa [le0] using this
  have hs10eq : step s9 = { s9 with pc := s9.pc + 3 } := by
    have hif :
        (if s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18 then (126 : Word)
          else s9.pc + 3) = s9.pc + 3 := by
      simp [hle]
    rw [hjlez, hif]
  have hs10pc : (step s9).pc = 123 := by
    have : s9.pc + 3 = (123 : Word) := by simp [hs9pc]
    rw [hs10eq]
    exact this
  have hs10h : (step s9).halted = false := by
    rw [hs10eq]
    exact hs9h
  have hs10Z : (step s9).mem.get 0 = 0 := by
    rw [hs10eq]
    exact hZ9
  have jmp0 : (step s9).mem.get (step s9).pc = 0 := by
    have hp10 : (step s9).pc = UInt16.ofNat 123 :=
      hs10pc.trans (rfl : (123 : Word) = UInt16.ofNat 123)
    rw [hp10]
    have hmem : (step s9).mem.get (UInt16.ofNat 123) = s9.mem.get (UInt16.ofNat 123) := by
      rw [hs10eq]
    have hget : s9.mem.get (UInt16.ofNat 123) = s.mem.get (UInt16.ofNat 123) :=
      hpres9 (UInt16.ofNat 123) (by decide) (by decide)
    have hval : decChunk007[11]! = 0 := rfl
    exact hmem.trans (hget.trans ((gimg 3 (by decide)).trans ((cell112 11 (by decide)).trans hval)))
  have jmp1 : (step s9).mem.get ((step s9).pc + 1) = 0 := by
    have : (step s9).pc + 1 = (124 : Word) := by simp [hs10pc]
    rw [this, (rfl : (124 : Word) = UInt16.ofNat 124)]
    have hmem : (step s9).mem.get (UInt16.ofNat 124) = s9.mem.get (UInt16.ofNat 124) := by
      rw [hs10eq]
    have hget : s9.mem.get (UInt16.ofNat 124) = s.mem.get (UInt16.ofNat 124) :=
      hpres9 (UInt16.ofNat 124) (by decide) (by decide)
    have hval : decChunk007[12]! = 0 := rfl
    exact hmem.trans (hget.trans ((gimg 4 (by decide)).trans ((cell112 12 (by decide)).trans hval)))
  have jmp2 : (step s9).mem.get ((step s9).pc + 2) = 174 := by
    have : (step s9).pc + 2 = (125 : Word) := by simp [hs10pc]
    rw [this, (rfl : (125 : Word) = UInt16.ofNat 125)]
    have hmem : (step s9).mem.get (UInt16.ofNat 125) = s9.mem.get (UInt16.ofNat 125) := by
      rw [hs10eq]
    have hget : s9.mem.get (UInt16.ofNat 125) = s.mem.get (UInt16.ofNat 125) :=
      hpres9 (UInt16.ofNat 125) (by decide) (by decide)
    have hval : decChunk007[13]! = 174 := rfl
    exact hmem.trans (hget.trans ((gimg 5 (by decide)).trans ((cell112 13 (by decide)).trans hval)))
  have hpc10 : (step s9).pc.toNat < 32768 := by simp [hs10pc]
  have hjmp :=
    step_JMP (s := step s9) (dest := 174)
      hs10h hpc10 hs10Z jmp0 jmp1 jmp2
  have hrun : s11 = step (step s9) := by
    have h11 : runN s 11 = runN s9 2 := runN_add_eq s 9 2 11 (by decide)
    have h2 := runN_2_steps s9 hs9h hpc9 hs10h hpc10
    exact h11.trans h2
  have hmem11 : (step (step s9)).mem = s9.mem := by
    have h1 : (step s9).mem = s9.mem := by rw [hs10eq]
    have h2 : (step (step s9)).mem = (step s9).mem := by rw [hjmp]
    exact h2.trans h1
  have hs11pc : s11.pc = 174 := by
    rw [hrun, hjmp]
  have hs11h : s11.halted = false := by
    rw [hrun, hjmp]
    exact hs10h
  have hs11Z : s11.mem.get 0 = 0 := by
    rw [hrun, hmem11]
    exact hZ9
  have hs11N : s11.mem.get 17 = input := by
    rw [hrun, hmem11]
    exact hN9
  have hs11T : s11.mem.get 18 = input := by
    rw [hrun, hmem11]
    exact hT9
  have hs11S : s11.mem.get 19 = 0 := by
    rw [hrun, hmem11]
    exact hS9
  have hpres11 : ∀ a, a ≠ 18 → a ≠ 0 → s11.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hmem11]
    exact hpres9 a ha18 ha0
  exact ⟨hs11pc, hs11h, hs11N, hs11T, hs11Z, hs11S, hpres11⟩


/-- Zero `N`: `JLEZ` enters `maybe_neg`, `INC T` makes `T = 1`, then
`JLEZ` falls through and `JMP DIGITS` (15 steps from `I_PATH`).
`SIGN` stays 0. -/
theorem i_path_zero (cap : Word) :
    let s := afterSignedDispatch 0 cap
    let s15 := runN s 15
    s15.pc = 174 ∧
    s15.halted = false ∧
    s15.mem.get 17 = 0 ∧
    s15.mem.get 18 = 1 ∧
    s15.mem.get 0 = 0 ∧
    s15.mem.get 19 = 0 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a) := by
  intro s s15
  have hp := i_path_prelude 0 cap
  let s9 := runN s 9
  have hs9pc : s9.pc = 120 := hp.2.1
  have hs9h : s9.halted = false := hp.2.2.1
  have hN9 : s9.mem.get 17 = (0 : Word) := hp.2.2.2.1
  have hT9 : s9.mem.get 18 = (0 : Word) := hp.2.2.2.2.1
  have hZ9 : s9.mem.get 0 = 0 := hp.2.2.2.2.2.1
  have hS9 : s9.mem.get 19 = 0 := hp.2.2.2.2.2.2.1
  have hONE9 : s9.mem.get 3 = 1 := hp.2.2.2.2.2.2.2.2.1
  have hpres9 := hp.2.2.2.2.2.2.2.2.2.2
  have gimg (off : Nat) (hoff : off < 21) :
      s.mem.get (UInt16.ofNat (120 + off)) = intfmtImage[120 + off]! :=
    ipath_code 0 cap (120 + off) (by omega) (by omega)
  have j0 : s9.mem.get s9.pc = 0 := by
    have hp9 : s9.pc = UInt16.ofNat 120 :=
      hs9pc.trans (rfl : (120 : Word) = UInt16.ofNat 120)
    rw [hp9]
    have hget : s9.mem.get (UInt16.ofNat 120) = s.mem.get (UInt16.ofNat 120) :=
      hpres9 (UInt16.ofNat 120) (by decide) (by decide)
    have hval : decChunk007[8]! = 0 := rfl
    exact hget.trans ((gimg 0 (by decide)).trans ((cell112 8 (by decide)).trans hval))
  have j1 : s9.mem.get (s9.pc + 1) = 18 := by
    have : s9.pc + 1 = (121 : Word) := by simp [hs9pc]
    rw [this, (rfl : (121 : Word) = UInt16.ofNat 121)]
    have hget : s9.mem.get (UInt16.ofNat 121) = s.mem.get (UInt16.ofNat 121) :=
      hpres9 (UInt16.ofNat 121) (by decide) (by decide)
    have hval : decChunk007[9]! = 18 := rfl
    exact hget.trans ((gimg 1 (by decide)).trans ((cell112 9 (by decide)).trans hval))
  have j2 : s9.mem.get (s9.pc + 2) = 126 := by
    have : s9.pc + 2 = (122 : Word) := by simp [hs9pc]
    rw [this, (rfl : (122 : Word) = UInt16.ofNat 122)]
    have hget : s9.mem.get (UInt16.ofNat 122) = s.mem.get (UInt16.ofNat 122) :=
      hpres9 (UInt16.ofNat 122) (by decide) (by decide)
    have hval : decChunk007[10]! = 126 := rfl
    exact hget.trans ((gimg 2 (by decide)).trans ((cell112 10 (by decide)).trans hval))
  have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
  have hjlez :=
    step_JLEZ (s := s9) (x := 18) (dest := 126)
      hs9h hpc9 hZ9 j0 j1 j2 (by decide)
  have hle : (s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18) = true := by
    have : le0 (s9.mem.get 18) = true := by
      rw [hT9]
      exact le0_zero
    simpa [le0] using this
  have hs10eq : step s9 = { s9 with pc := 126 } := by
    have hif :
        (if s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18 then (126 : Word)
          else s9.pc + 3) = (126 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hs10pc : (step s9).pc = 126 := by
    rw [hs10eq]
  have hs10h : (step s9).halted = false := by
    rw [hs10eq]
    exact hs9h
  have hs10Z : (step s9).mem.get 0 = 0 := by
    rw [hs10eq]
    exact hZ9
  have hs10ONE : (step s9).mem.get 3 = 1 := by
    rw [hs10eq]
    exact hONE9
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → (step s9).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs10eq]
    exact hpres9 a ha18 ha0
  -- INC T at maybe_neg (pc 126)
  let s10 := step s9
  have hp10 : s10.pc = UInt16.ofNat 126 :=
    hs10pc.trans (rfl : (126 : Word) = UInt16.ofNat 126)
  have poff10 (off : Nat) (hoff : off ≤ 9) :
      s10.pc + UInt16.ofNat off = UInt16.ofNat (126 + off) :=
    word_pc_off 126 off hp10 (by omega)
  have g10 (off : Nat) (hoff : off < 15) :
      s10.mem.get (UInt16.ofNat (126 + off)) = intfmtImage[126 + off]! := by
    have hcell : s.mem.get (UInt16.ofNat (126 + off)) = intfmtImage[126 + off]! :=
      ipath_code 0 cap (126 + off) (by omega) (by omega)
    have hne18 : UInt16.ofNat (126 + off) ≠ 18 :=
      ofNat_ne (126 + off) 18 (by omega) (by omega) (by omega)
    have hne0 : UInt16.ofNat (126 + off) ≠ 0 :=
      ofNat_ne (126 + off) 0 (by omega) (by omega) (by omega)
    exact (hpres10 (UInt16.ofNat (126 + off)) hne18 hne0).trans hcell
  have i0 : s10.mem.get s10.pc = 3 := by
    rw [hp10]
    have hval : decChunk007[14]! = 3 := rfl
    exact (g10 0 (by decide)).trans ((cell112 14 (by decide)).trans hval)
  have i1 : s10.mem.get (s10.pc + UInt16.ofNat 1) = 0 := by
    rw [poff10 1 (by decide)]
    have hval : decChunk007[15]! = 0 := rfl
    exact (g10 1 (by decide)).trans ((cell112 15 (by decide)).trans hval)
  have i2 : s10.mem.get (s10.pc + UInt16.ofNat 2) = s10.pc + UInt16.ofNat 3 := by
    rw [poff10 2 (by decide), poff10 3 (by decide)]
    have hval : decChunk008[0]! = 129 := rfl
    have hv : (129 : Word) = UInt16.ofNat 129 := rfl
    exact (g10 2 (by decide)).trans ((cell128 0 (by decide)).trans (hval.trans hv))
  have i3 : s10.mem.get (s10.pc + UInt16.ofNat 3) = 0 := by
    rw [poff10 3 (by decide)]
    have hval : decChunk008[1]! = 0 := rfl
    exact (g10 3 (by decide)).trans ((cell128 1 (by decide)).trans hval)
  have i4 : s10.mem.get (s10.pc + UInt16.ofNat 4) = 18 := by
    rw [poff10 4 (by decide)]
    have hval : decChunk008[2]! = 18 := rfl
    exact (g10 4 (by decide)).trans ((cell128 2 (by decide)).trans hval)
  have i5 : s10.mem.get (s10.pc + UInt16.ofNat 5) = s10.pc + UInt16.ofNat 6 := by
    rw [poff10 5 (by decide), poff10 6 (by decide)]
    have hval : decChunk008[3]! = 132 := rfl
    have hv : (132 : Word) = UInt16.ofNat 132 := rfl
    exact (g10 5 (by decide)).trans ((cell128 3 (by decide)).trans (hval.trans hv))
  have i6 : s10.mem.get (s10.pc + UInt16.ofNat 6) = 0 := by
    rw [poff10 6 (by decide)]
    have hval : decChunk008[4]! = 0 := rfl
    exact (g10 6 (by decide)).trans ((cell128 4 (by decide)).trans hval)
  have i7 : s10.mem.get (s10.pc + UInt16.ofNat 7) = 0 := by
    rw [poff10 7 (by decide)]
    have hval : decChunk008[5]! = 0 := rfl
    exact (g10 7 (by decide)).trans ((cell128 5 (by decide)).trans hval)
  have i8 : s10.mem.get (s10.pc + UInt16.ofNat 8) = s10.pc + UInt16.ofNat 9 := by
    rw [poff10 8 (by decide), poff10 9 (by decide)]
    have hval : decChunk008[6]! = 135 := rfl
    have hv : (135 : Word) = UInt16.ofNat 135 := rfl
    exact (g10 8 (by decide)).trans ((cell128 6 (by decide)).trans (hval.trans hv))
  have hcodeD10 : ∀ i : Nat, i < 9 → s10.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 126 i 18 hp10 (by omega) (by omega) (by omega)
  have hcodeZ10 : ∀ i : Nat, i < 9 → s10.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 126 i 0 hp10 (by omega) (by omega) (by omega)
  have hpc10b : s10.pc.toNat + 9 ≤ 32768 := by
    have : s10.pc = 126 := hs10pc
    simp [this]
  have hpc10_0 : 0 < s10.pc.toNat := by
    have : s10.pc = 126 := hs10pc
    simp [this]
  have hinc :=
    runN_ADD (s := s10) (src := 3) (dst := 18)
      hs10h hpc10b hpc10_0 hs10Z (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD10 hcodeZ10
  let s13 := runN s10 3
  have hs13pc : s13.pc = 135 := by
    have hadd : s10.pc + UInt16.ofNat 9 = (135 : Word) := by
      rw [poff10 9 (by decide)]
      exact (rfl : UInt16.ofNat 135 = (135 : Word))
    exact hinc.1.trans hadd
  have hs13h : s13.halted = false := hinc.2.1
  have hT13 : s13.mem.get 18 = 1 := by
    have : s10.mem.get 18 + s10.mem.get 3 = (0 : Word) + 1 := by
      have hT10 : s10.mem.get 18 = 0 := by
        rw [show s10 = step s9 from rfl, hs10eq]
        exact hT9
      rw [hT10, hs10ONE]
    exact hinc.2.2.1.trans this
  have hZ13 : s13.mem.get 0 = 0 := hinc.2.2.2.1
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have hN13 : s13.mem.get 17 = 0 :=
    (hpres13 17 (by decide) (by decide)).trans (by
      have : s.mem.get 17 = 0 := (afterSignedDispatch_entry 0 cap).2.2.1
      exact this)
  have hS13 : s13.mem.get 19 = 0 :=
    (hpres13 19 (by decide) (by decide)).trans (afterSignedDispatch_get_SIGN 0 cap)
  -- JLEZ T do_neg at pc 135, T = 1 so fall through, then JMP DIGITS
  have k0 : s13.mem.get s13.pc = 0 := by
    have hp13 : s13.pc = UInt16.ofNat 135 :=
      hs13pc.trans (rfl : (135 : Word) = UInt16.ofNat 135)
    rw [hp13]
    have hget : s13.mem.get (UInt16.ofNat 135) = s.mem.get (UInt16.ofNat 135) :=
      hpres13 (UInt16.ofNat 135) (by decide) (by decide)
    have hval : decChunk008[7]! = 0 := rfl
    exact hget.trans ((gimg 15 (by decide)).trans ((cell128 7 (by decide)).trans hval))
  have k1 : s13.mem.get (s13.pc + 1) = 18 := by
    have : s13.pc + 1 = (136 : Word) := by simp [hs13pc]
    rw [this, (rfl : (136 : Word) = UInt16.ofNat 136)]
    have hget : s13.mem.get (UInt16.ofNat 136) = s.mem.get (UInt16.ofNat 136) :=
      hpres13 (UInt16.ofNat 136) (by decide) (by decide)
    have hval : decChunk008[8]! = 18 := rfl
    exact hget.trans ((gimg 16 (by decide)).trans ((cell128 8 (by decide)).trans hval))
  have k2 : s13.mem.get (s13.pc + 2) = 141 := by
    have : s13.pc + 2 = (137 : Word) := by simp [hs13pc]
    rw [this, (rfl : (137 : Word) = UInt16.ofNat 137)]
    have hget : s13.mem.get (UInt16.ofNat 137) = s.mem.get (UInt16.ofNat 137) :=
      hpres13 (UInt16.ofNat 137) (by decide) (by decide)
    have hval : decChunk008[9]! = 141 := rfl
    exact hget.trans ((gimg 17 (by decide)).trans ((cell128 9 (by decide)).trans hval))
  have hpc13 : s13.pc.toNat < 32768 := by simp [hs13pc]
  have hjlez2 :=
    step_JLEZ (s := s13) (x := 18) (dest := 141)
      hs13h hpc13 hZ13 k0 k1 k2 (by decide)
  have hle2 : (s13.mem.get 18 = 0 || 0x8000 ≤ s13.mem.get 18) = false := by
    have : le0 (s13.mem.get 18) = false := by
      rw [hT13]
      exact le0_pos (by decide) (by decide)
    simpa [le0] using this
  have hs14eq : step s13 = { s13 with pc := s13.pc + 3 } := by
    have hif :
        (if s13.mem.get 18 = 0 || 0x8000 ≤ s13.mem.get 18 then (141 : Word)
          else s13.pc + 3) = s13.pc + 3 := by
      simp [hle2]
    rw [hjlez2, hif]
  have hs14pc : (step s13).pc = 138 := by
    have : s13.pc + 3 = (138 : Word) := by simp [hs13pc]
    rw [hs14eq]
    exact this
  have hs14h : (step s13).halted = false := by
    rw [hs14eq]
    exact hs13h
  have hs14Z : (step s13).mem.get 0 = 0 := by
    rw [hs14eq]
    exact hZ13
  have jmp0 : (step s13).mem.get (step s13).pc = 0 := by
    have hp14 : (step s13).pc = UInt16.ofNat 138 :=
      hs14pc.trans (rfl : (138 : Word) = UInt16.ofNat 138)
    rw [hp14]
    have hmem : (step s13).mem.get (UInt16.ofNat 138) = s13.mem.get (UInt16.ofNat 138) := by
      rw [hs14eq]
    have hget : s13.mem.get (UInt16.ofNat 138) = s.mem.get (UInt16.ofNat 138) :=
      hpres13 (UInt16.ofNat 138) (by decide) (by decide)
    have hval : decChunk008[10]! = 0 := rfl
    exact hmem.trans (hget.trans ((gimg 18 (by decide)).trans ((cell128 10 (by decide)).trans hval)))
  have jmp1 : (step s13).mem.get ((step s13).pc + 1) = 0 := by
    have : (step s13).pc + 1 = (139 : Word) := by simp [hs14pc]
    rw [this, (rfl : (139 : Word) = UInt16.ofNat 139)]
    have hmem : (step s13).mem.get (UInt16.ofNat 139) = s13.mem.get (UInt16.ofNat 139) := by
      rw [hs14eq]
    have hget : s13.mem.get (UInt16.ofNat 139) = s.mem.get (UInt16.ofNat 139) :=
      hpres13 (UInt16.ofNat 139) (by decide) (by decide)
    have hval : decChunk008[11]! = 0 := rfl
    exact hmem.trans (hget.trans ((gimg 19 (by decide)).trans ((cell128 11 (by decide)).trans hval)))
  have jmp2 : (step s13).mem.get ((step s13).pc + 2) = 174 := by
    have : (step s13).pc + 2 = (140 : Word) := by simp [hs14pc]
    rw [this, (rfl : (140 : Word) = UInt16.ofNat 140)]
    have hmem : (step s13).mem.get (UInt16.ofNat 140) = s13.mem.get (UInt16.ofNat 140) := by
      rw [hs14eq]
    have hget : s13.mem.get (UInt16.ofNat 140) = s.mem.get (UInt16.ofNat 140) :=
      hpres13 (UInt16.ofNat 140) (by decide) (by decide)
    have hval : decChunk008[12]! = 174 := rfl
    exact hmem.trans (hget.trans ((gimg 20 (by decide)).trans ((cell128 12 (by decide)).trans hval)))
  have hpc14 : (step s13).pc.toNat < 32768 := by simp [hs14pc]
  have hjmp :=
    step_JMP (s := step s13) (dest := 174)
      hs14h hpc14 hs14Z jmp0 jmp1 jmp2
  have hrun : s15 = step (step s13) := by
    have h15 : runN s 15 = runN s9 6 := runN_add_eq s 9 6 15 (by decide)
    have h6 : runN s9 6 = runN s10 5 := runN_succ_go s9 5 hs9h hpc9
    have h5 : runN s10 5 = runN s13 2 := runN_add_eq s10 3 2 5 (by decide)
    have h2 := runN_2_steps s13 hs13h hpc13 hs14h hpc14
    exact h15.trans (h6.trans (h5.trans h2))
  have hmem15 : (step (step s13)).mem = s13.mem := by
    have h1 : (step s13).mem = s13.mem := by rw [hs14eq]
    have h2 : (step (step s13)).mem = (step s13).mem := by rw [hjmp]
    exact h2.trans h1
  have hs15pc : s15.pc = 174 := by
    rw [hrun, hjmp]
  have hs15h : s15.halted = false := by
    rw [hrun, hjmp]
    exact hs14h
  have hs15Z : s15.mem.get 0 = 0 := by
    rw [hrun, hmem15]
    exact hZ13
  have hs15N : s15.mem.get 17 = 0 := by
    rw [hrun, hmem15]
    exact hN13
  have hs15T : s15.mem.get 18 = 1 := by
    rw [hrun, hmem15]
    exact hT13
  have hs15S : s15.mem.get 19 = 0 := by
    rw [hrun, hmem15]
    exact hS13
  have hpres15 : ∀ a, a ≠ 18 → a ≠ 0 → s15.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hmem15]
    exact hpres13 a ha18 ha0
  exact ⟨hs15pc, hs15h, hs15N, hs15T, hs15Z, hs15S, hpres15⟩


/-- Negative `N`: from the sign-test `JLEZ` the machine reaches `do_neg`
(pc 141) in 5 further steps (14 from `I_PATH`) with `T = N + 1`. -/
theorem i_path_neg_to_doneg (input cap : Word)
    (hneg : 32768 ≤ input.toNat) :
    let s := afterSignedDispatch input cap
    let s14 := runN s 14
    s14.pc = 141 ∧
    s14.halted = false ∧
    s14.mem.get 17 = input ∧
    s14.mem.get 18 = input + 1 ∧
    s14.mem.get 0 = 0 ∧
    s14.mem.get 19 = 0 ∧
    s14.mem.get 3 = 1 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → s14.mem.get a = s.mem.get a) := by
  intro s s14
  have hp := i_path_prelude input cap
  let s9 := runN s 9
  have hs9pc : s9.pc = 120 := hp.2.1
  have hs9h : s9.halted = false := hp.2.2.1
  have hN9 : s9.mem.get 17 = input := hp.2.2.2.1
  have hT9 : s9.mem.get 18 = input := hp.2.2.2.2.1
  have hZ9 : s9.mem.get 0 = 0 := hp.2.2.2.2.2.1
  have hS9 : s9.mem.get 19 = 0 := hp.2.2.2.2.2.2.1
  have hONE9 : s9.mem.get 3 = 1 := hp.2.2.2.2.2.2.2.2.1
  have hpres9 := hp.2.2.2.2.2.2.2.2.2.2
  have gimg (off : Nat) (hoff : off < 21) :
      s.mem.get (UInt16.ofNat (120 + off)) = intfmtImage[120 + off]! :=
    ipath_code input cap (120 + off) (by omega) (by omega)
  have j0 : s9.mem.get s9.pc = 0 := by
    have hp9 : s9.pc = UInt16.ofNat 120 :=
      hs9pc.trans (rfl : (120 : Word) = UInt16.ofNat 120)
    rw [hp9]
    have hget : s9.mem.get (UInt16.ofNat 120) = s.mem.get (UInt16.ofNat 120) :=
      hpres9 (UInt16.ofNat 120) (by decide) (by decide)
    have hval : decChunk007[8]! = 0 := rfl
    exact hget.trans ((gimg 0 (by decide)).trans ((cell112 8 (by decide)).trans hval))
  have j1 : s9.mem.get (s9.pc + 1) = 18 := by
    have : s9.pc + 1 = (121 : Word) := by simp [hs9pc]
    rw [this, (rfl : (121 : Word) = UInt16.ofNat 121)]
    have hget : s9.mem.get (UInt16.ofNat 121) = s.mem.get (UInt16.ofNat 121) :=
      hpres9 (UInt16.ofNat 121) (by decide) (by decide)
    have hval : decChunk007[9]! = 18 := rfl
    exact hget.trans ((gimg 1 (by decide)).trans ((cell112 9 (by decide)).trans hval))
  have j2 : s9.mem.get (s9.pc + 2) = 126 := by
    have : s9.pc + 2 = (122 : Word) := by simp [hs9pc]
    rw [this, (rfl : (122 : Word) = UInt16.ofNat 122)]
    have hget : s9.mem.get (UInt16.ofNat 122) = s.mem.get (UInt16.ofNat 122) :=
      hpres9 (UInt16.ofNat 122) (by decide) (by decide)
    have hval : decChunk007[10]! = 126 := rfl
    exact hget.trans ((gimg 2 (by decide)).trans ((cell112 10 (by decide)).trans hval))
  have hpc9 : s9.pc.toNat < 32768 := by simp [hs9pc]
  have hjlez :=
    step_JLEZ (s := s9) (x := 18) (dest := 126)
      hs9h hpc9 hZ9 j0 j1 j2 (by decide)
  have hle : (s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18) = true := by
    have : le0 (s9.mem.get 18) = true := by
      rw [hT9]
      exact le0_hi hneg
    simpa [le0] using this
  have hs10eq : step s9 = { s9 with pc := 126 } := by
    have hif :
        (if s9.mem.get 18 = 0 || 0x8000 ≤ s9.mem.get 18 then (126 : Word)
          else s9.pc + 3) = (126 : Word) := by
      simp [hle]
    rw [hjlez, hif]
  have hs10pc : (step s9).pc = 126 := by
    rw [hs10eq]
  have hs10h : (step s9).halted = false := by
    rw [hs10eq]
    exact hs9h
  have hs10Z : (step s9).mem.get 0 = 0 := by
    rw [hs10eq]
    exact hZ9
  have hs10ONE : (step s9).mem.get 3 = 1 := by
    rw [hs10eq]
    exact hONE9
  have hpres10 : ∀ a, a ≠ 18 → a ≠ 0 → (step s9).mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hs10eq]
    exact hpres9 a ha18 ha0
  let s10 := step s9
  have hp10 : s10.pc = UInt16.ofNat 126 :=
    hs10pc.trans (rfl : (126 : Word) = UInt16.ofNat 126)
  have poff10 (off : Nat) (hoff : off ≤ 9) :
      s10.pc + UInt16.ofNat off = UInt16.ofNat (126 + off) :=
    word_pc_off 126 off hp10 (by omega)
  have g10 (off : Nat) (hoff : off < 15) :
      s10.mem.get (UInt16.ofNat (126 + off)) = intfmtImage[126 + off]! := by
    have hcell : s.mem.get (UInt16.ofNat (126 + off)) = intfmtImage[126 + off]! :=
      ipath_code input cap (126 + off) (by omega) (by omega)
    have hne18 : UInt16.ofNat (126 + off) ≠ 18 :=
      ofNat_ne (126 + off) 18 (by omega) (by omega) (by omega)
    have hne0 : UInt16.ofNat (126 + off) ≠ 0 :=
      ofNat_ne (126 + off) 0 (by omega) (by omega) (by omega)
    exact (hpres10 (UInt16.ofNat (126 + off)) hne18 hne0).trans hcell
  have i0 : s10.mem.get s10.pc = 3 := by
    rw [hp10]
    have hval : decChunk007[14]! = 3 := rfl
    exact (g10 0 (by decide)).trans ((cell112 14 (by decide)).trans hval)
  have i1 : s10.mem.get (s10.pc + UInt16.ofNat 1) = 0 := by
    rw [poff10 1 (by decide)]
    have hval : decChunk007[15]! = 0 := rfl
    exact (g10 1 (by decide)).trans ((cell112 15 (by decide)).trans hval)
  have i2 : s10.mem.get (s10.pc + UInt16.ofNat 2) = s10.pc + UInt16.ofNat 3 := by
    rw [poff10 2 (by decide), poff10 3 (by decide)]
    have hval : decChunk008[0]! = 129 := rfl
    have hv : (129 : Word) = UInt16.ofNat 129 := rfl
    exact (g10 2 (by decide)).trans ((cell128 0 (by decide)).trans (hval.trans hv))
  have i3 : s10.mem.get (s10.pc + UInt16.ofNat 3) = 0 := by
    rw [poff10 3 (by decide)]
    have hval : decChunk008[1]! = 0 := rfl
    exact (g10 3 (by decide)).trans ((cell128 1 (by decide)).trans hval)
  have i4 : s10.mem.get (s10.pc + UInt16.ofNat 4) = 18 := by
    rw [poff10 4 (by decide)]
    have hval : decChunk008[2]! = 18 := rfl
    exact (g10 4 (by decide)).trans ((cell128 2 (by decide)).trans hval)
  have i5 : s10.mem.get (s10.pc + UInt16.ofNat 5) = s10.pc + UInt16.ofNat 6 := by
    rw [poff10 5 (by decide), poff10 6 (by decide)]
    have hval : decChunk008[3]! = 132 := rfl
    have hv : (132 : Word) = UInt16.ofNat 132 := rfl
    exact (g10 5 (by decide)).trans ((cell128 3 (by decide)).trans (hval.trans hv))
  have i6 : s10.mem.get (s10.pc + UInt16.ofNat 6) = 0 := by
    rw [poff10 6 (by decide)]
    have hval : decChunk008[4]! = 0 := rfl
    exact (g10 6 (by decide)).trans ((cell128 4 (by decide)).trans hval)
  have i7 : s10.mem.get (s10.pc + UInt16.ofNat 7) = 0 := by
    rw [poff10 7 (by decide)]
    have hval : decChunk008[5]! = 0 := rfl
    exact (g10 7 (by decide)).trans ((cell128 5 (by decide)).trans hval)
  have i8 : s10.mem.get (s10.pc + UInt16.ofNat 8) = s10.pc + UInt16.ofNat 9 := by
    rw [poff10 8 (by decide), poff10 9 (by decide)]
    have hval : decChunk008[6]! = 135 := rfl
    have hv : (135 : Word) = UInt16.ofNat 135 := rfl
    exact (g10 8 (by decide)).trans ((cell128 6 (by decide)).trans (hval.trans hv))
  have hcodeD10 : ∀ i : Nat, i < 9 → s10.pc + UInt16.ofNat i ≠ (18 : Word) := by
    intro i hi
    have : (18 : Word) = UInt16.ofNat 18 := rfl
    rw [this]
    exact pc_off_ne 126 i 18 hp10 (by omega) (by omega) (by omega)
  have hcodeZ10 : ∀ i : Nat, i < 9 → s10.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 126 i 0 hp10 (by omega) (by omega) (by omega)
  have hpc10b : s10.pc.toNat + 9 ≤ 32768 := by
    have : s10.pc = 126 := hs10pc
    simp [this]
  have hpc10_0 : 0 < s10.pc.toNat := by
    have : s10.pc = 126 := hs10pc
    simp [this]
  have hinc :=
    runN_ADD (s := s10) (src := 3) (dst := 18)
      hs10h hpc10b hpc10_0 hs10Z (by decide) (by decide) (by decide)
      i0 i1 i2 i3 i4 i5 i6 i7 i8 hcodeD10 hcodeZ10
  let s13 := runN s10 3
  have hs13pc : s13.pc = 135 := by
    have hadd : s10.pc + UInt16.ofNat 9 = (135 : Word) := by
      rw [poff10 9 (by decide)]
      exact (rfl : UInt16.ofNat 135 = (135 : Word))
    exact hinc.1.trans hadd
  have hs13h : s13.halted = false := hinc.2.1
  have hT13 : s13.mem.get 18 = input + 1 := by
    have hT10 : s10.mem.get 18 = input := by
      rw [show s10 = step s9 from rfl, hs10eq]
      exact hT9
    have : s10.mem.get 18 + s10.mem.get 3 = input + 1 := by
      rw [hT10, hs10ONE]
    exact hinc.2.2.1.trans this
  have hZ13 : s13.mem.get 0 = 0 := hinc.2.2.2.1
  have hpres13 : ∀ a, a ≠ 18 → a ≠ 0 → s13.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    exact (hinc.2.2.2.2 a ha18 ha0).trans (hpres10 a ha18 ha0)
  have k0 : s13.mem.get s13.pc = 0 := by
    have hp13 : s13.pc = UInt16.ofNat 135 :=
      hs13pc.trans (rfl : (135 : Word) = UInt16.ofNat 135)
    rw [hp13]
    have hget : s13.mem.get (UInt16.ofNat 135) = s.mem.get (UInt16.ofNat 135) :=
      hpres13 (UInt16.ofNat 135) (by decide) (by decide)
    have hval : decChunk008[7]! = 0 := rfl
    exact hget.trans ((gimg 15 (by decide)).trans ((cell128 7 (by decide)).trans hval))
  have k1 : s13.mem.get (s13.pc + 1) = 18 := by
    have : s13.pc + 1 = (136 : Word) := by simp [hs13pc]
    rw [this, (rfl : (136 : Word) = UInt16.ofNat 136)]
    have hget : s13.mem.get (UInt16.ofNat 136) = s.mem.get (UInt16.ofNat 136) :=
      hpres13 (UInt16.ofNat 136) (by decide) (by decide)
    have hval : decChunk008[8]! = 18 := rfl
    exact hget.trans ((gimg 16 (by decide)).trans ((cell128 8 (by decide)).trans hval))
  have k2 : s13.mem.get (s13.pc + 2) = 141 := by
    have : s13.pc + 2 = (137 : Word) := by simp [hs13pc]
    rw [this, (rfl : (137 : Word) = UInt16.ofNat 137)]
    have hget : s13.mem.get (UInt16.ofNat 137) = s.mem.get (UInt16.ofNat 137) :=
      hpres13 (UInt16.ofNat 137) (by decide) (by decide)
    have hval : decChunk008[9]! = 141 := rfl
    exact hget.trans ((gimg 17 (by decide)).trans ((cell128 9 (by decide)).trans hval))
  have hpc13 : s13.pc.toNat < 32768 := by simp [hs13pc]
  have hjlez2 :=
    step_JLEZ (s := s13) (x := 18) (dest := 141)
      hs13h hpc13 hZ13 k0 k1 k2 (by decide)
  have hle2 : (s13.mem.get 18 = 0 || 0x8000 ≤ s13.mem.get 18) = true := by
    have : le0 (s13.mem.get 18) = true := by
      rw [hT13]
      exact le0_succ_neg hneg
    simpa [le0] using this
  have hs14eq : step s13 = { s13 with pc := 141 } := by
    have hif :
        (if s13.mem.get 18 = 0 || 0x8000 ≤ s13.mem.get 18 then (141 : Word)
          else s13.pc + 3) = (141 : Word) := by
      simp [hle2]
    rw [hjlez2, hif]
  have hrun : s14 = step s13 := by
    have h14 : runN s 14 = runN s9 5 := runN_add_eq s 9 5 14 (by decide)
    have h5 : runN s9 5 = runN s10 4 := runN_succ_go s9 4 hs9h hpc9
    have h4 : runN s10 4 = runN s13 1 := runN_add_eq s10 3 1 4 (by decide)
    have h1 := runN_one s13 hs13h hpc13
    exact h14.trans (h5.trans (h4.trans h1))
  have hs14pc : s14.pc = 141 := by
    rw [hrun, hs14eq]
  have hs14h : s14.halted = false := by
    rw [hrun, hs14eq]
    exact hs13h
  have hs14Z : s14.mem.get 0 = 0 := by
    rw [hrun, hs14eq]
    exact hZ13
  have hs14T : s14.mem.get 18 = input + 1 := by
    rw [hrun, hs14eq]
    exact hT13
  have hpres14 : ∀ a, a ≠ 18 → a ≠ 0 → s14.mem.get a = s.mem.get a := by
    intro a ha18 ha0
    rw [hrun, hs14eq]
    exact hpres13 a ha18 ha0
  have hs14N : s14.mem.get 17 = input :=
    (hpres14 17 (by decide) (by decide)).trans (afterSignedDispatch_entry input cap).2.2.1
  have hs14S : s14.mem.get 19 = 0 :=
    (hpres14 19 (by decide) (by decide)).trans (afterSignedDispatch_get_SIGN input cap)
  have hs14O : s14.mem.get 3 = 1 :=
    (hpres14 3 (by decide) (by decide)).trans (afterSignedDispatch_get_ONE input cap)
  exact ⟨hs14pc, hs14h, hs14N, hs14T, hs14Z, hs14S, hs14O, hpres14⟩


/-- Negative `N`: `do_neg` sets `SIGN = 1`, replaces `N` (and `T`) with
the two's-complement magnitude `0 - N`, and jumps to `DIGITS` (25 steps
from `I_PATH`). -/
theorem i_path_neg (input cap : Word)
    (hneg : 32768 ≤ input.toNat) :
    let s := afterSignedDispatch input cap
    let s25 := runN s 25
    s25.pc = 174 ∧
    s25.halted = false ∧
    s25.mem.get 17 = 0 - input ∧
    s25.mem.get 18 = 0 - input ∧
    s25.mem.get 0 = 0 ∧
    s25.mem.get 19 = 1 ∧
    (∀ a, a ≠ 18 → a ≠ 0 → a ≠ 19 → a ≠ 17 → s25.mem.get a = s.mem.get a) := by
  intro s s25
  have hd := i_path_neg_to_doneg input cap hneg
  let s14 := runN s 14
  have hs14pc : s14.pc = 141 := hd.1
  have hs14h : s14.halted = false := hd.2.1
  have hN14 : s14.mem.get 17 = input := hd.2.2.1
  have hT14 : s14.mem.get 18 = input + 1 := hd.2.2.2.1
  have hZ14 : s14.mem.get 0 = 0 := hd.2.2.2.2.1
  have hS14 : s14.mem.get 19 = 0 := hd.2.2.2.2.2.1
  have hONE14 : s14.mem.get 3 = 1 := hd.2.2.2.2.2.2.1
  have hpres14 := hd.2.2.2.2.2.2.2
  have hp14 : s14.pc = UInt16.ofNat 141 :=
    hs14pc.trans (rfl : (141 : Word) = UInt16.ofNat 141)
  have poff14 (off : Nat) (hoff : off ≤ 12) :
      s14.pc + UInt16.ofNat off = UInt16.ofNat (141 + off) :=
    word_pc_off 141 off hp14 (by omega)
  have g14 (off : Nat) (hoff : off < 33) :
      s14.mem.get (UInt16.ofNat (141 + off)) = intfmtImage[141 + off]! := by
    have hcell : s.mem.get (UInt16.ofNat (141 + off)) = intfmtImage[141 + off]! :=
      ipath_code input cap (141 + off) (by omega) (by omega)
    have hne18 : UInt16.ofNat (141 + off) ≠ 18 :=
      ofNat_ne (141 + off) 18 (by omega) (by omega) (by omega)
    have hne0 : UInt16.ofNat (141 + off) ≠ 0 :=
      ofNat_ne (141 + off) 0 (by omega) (by omega) (by omega)
    exact (hpres14 (UInt16.ofNat (141 + off)) hne18 hne0).trans hcell
  -- MOV ONE SIGN at pc 141
  have m0 : s14.mem.get s14.pc = 19 := by
    rw [hp14]
    have hval : decChunk008[13]! = 19 := rfl
    exact (g14 0 (by decide)).trans ((cell128 13 (by decide)).trans hval)
  have m1 : s14.mem.get (s14.pc + UInt16.ofNat 1) = 19 := by
    rw [poff14 1 (by decide)]
    have hval : decChunk008[14]! = 19 := rfl
    exact (g14 1 (by decide)).trans ((cell128 14 (by decide)).trans hval)
  have m2 : s14.mem.get (s14.pc + UInt16.ofNat 2) = s14.pc + UInt16.ofNat 3 := by
    rw [poff14 2 (by decide), poff14 3 (by decide)]
    have hval : decChunk008[15]! = 144 := rfl
    have hv : (144 : Word) = UInt16.ofNat 144 := rfl
    exact (g14 2 (by decide)).trans ((cell128 15 (by decide)).trans (hval.trans hv))
  have m3 : s14.mem.get (s14.pc + UInt16.ofNat 3) = 3 := by
    rw [poff14 3 (by decide)]
    have hval : decChunk009[0]! = 3 := rfl
    exact (g14 3 (by decide)).trans ((cell144 0 (by decide)).trans hval)
  have m4 : s14.mem.get (s14.pc + UInt16.ofNat 4) = 0 := by
    rw [poff14 4 (by decide)]
    have hval : decChunk009[1]! = 0 := rfl
    exact (g14 4 (by decide)).trans ((cell144 1 (by decide)).trans hval)
  have m5 : s14.mem.get (s14.pc + UInt16.ofNat 5) = s14.pc + UInt16.ofNat 6 := by
    rw [poff14 5 (by decide), poff14 6 (by decide)]
    have hval : decChunk009[2]! = 147 := rfl
    have hv : (147 : Word) = UInt16.ofNat 147 := rfl
    exact (g14 5 (by decide)).trans ((cell144 2 (by decide)).trans (hval.trans hv))
  have m6 : s14.mem.get (s14.pc + UInt16.ofNat 6) = 0 := by
    rw [poff14 6 (by decide)]
    have hval : decChunk009[3]! = 0 := rfl
    exact (g14 6 (by decide)).trans ((cell144 3 (by decide)).trans hval)
  have m7 : s14.mem.get (s14.pc + UInt16.ofNat 7) = 19 := by
    rw [poff14 7 (by decide)]
    have hval : decChunk009[4]! = 19 := rfl
    exact (g14 7 (by decide)).trans ((cell144 4 (by decide)).trans hval)
  have m8 : s14.mem.get (s14.pc + UInt16.ofNat 8) = s14.pc + UInt16.ofNat 9 := by
    rw [poff14 8 (by decide), poff14 9 (by decide)]
    have hval : decChunk009[5]! = 150 := rfl
    have hv : (150 : Word) = UInt16.ofNat 150 := rfl
    exact (g14 8 (by decide)).trans ((cell144 5 (by decide)).trans (hval.trans hv))
  have m9 : s14.mem.get (s14.pc + UInt16.ofNat 9) = 0 := by
    rw [poff14 9 (by decide)]
    have hval : decChunk009[6]! = 0 := rfl
    exact (g14 9 (by decide)).trans ((cell144 6 (by decide)).trans hval)
  have m10 : s14.mem.get (s14.pc + UInt16.ofNat 10) = 0 := by
    rw [poff14 10 (by decide)]
    have hval : decChunk009[7]! = 0 := rfl
    exact (g14 10 (by decide)).trans ((cell144 7 (by decide)).trans hval)
  have m11 : s14.mem.get (s14.pc + UInt16.ofNat 11) = s14.pc + UInt16.ofNat 12 := by
    rw [poff14 11 (by decide), poff14 12 (by decide)]
    have hval : decChunk009[8]! = 153 := rfl
    have hv : (153 : Word) = UInt16.ofNat 153 := rfl
    exact (g14 11 (by decide)).trans ((cell144 8 (by decide)).trans (hval.trans hv))
  have hcodeD : ∀ i : Nat, i < 12 → s14.pc + UInt16.ofNat i ≠ (19 : Word) := by
    intro i hi
    have : (19 : Word) = UInt16.ofNat 19 := rfl
    rw [this]
    exact pc_off_ne 141 i 19 hp14 (by omega) (by omega) (by omega)
  have hcodeZ : ∀ i : Nat, i < 12 → s14.pc + UInt16.ofNat i ≠ (0 : Word) := by
    intro i hi
    have : (0 : Word) = UInt16.ofNat 0 := rfl
    rw [this]
    exact pc_off_ne 141 i 0 hp14 (by omega) (by omega) (by omega)
  have hpc14 : s14.pc.toNat + 12 ≤ 32768 := by simp [hs14pc]
  have hpc140 : 0 < s14.pc.toNat := by simp [hs14pc]
  have hmov :=
    runN_MOV (s := s14) (src := 3) (dst := 19)
      hs14h hpc14 hpc140 hZ14 (by decide) (by decide) (by decide) (by decide)
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 hcodeD hcodeZ
  let s18 := runN s14 4
  have hs18pc : s18.pc = 153 := by
    have hadd : s14.pc + UInt16.ofNat 12 = (153 : Word) := by
      rw [poff14 12 (by decide)]
      exact (rfl : UInt16.ofNat 153 = (153 : Word))
    exact hmov.1.trans hadd
  have hs18h : s18.halted = false := hmov.2.1
  have hS18 : s18.mem.get 19 = 1 := hmov.2.2.1.trans hONE14
  have hZ18 : s18.mem.get 0 = 0 := hmov.2.2.2.1
  have hpres18 := hmov.2.2.2.2.2
  have hN18 : s18.mem.get 17 = input :=
    (hpres18 17 (by decide) (by decide)).trans hN14
  have hT18 : s18.mem.get 18 = input + 1 :=
    (hpres18 18 (by decide) (by decide)).trans hT14
  -- helper: code cells after MOV SIGN still match the image
  have g18 (k : Nat) (hk1 : 153 ≤ k) (hk2 : k < 174) :
      s18.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    have hcell : s14.mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
      have heq : k = 141 + (k - 141) := by omega
      have hoff : k - 141 < 33 := by omega
      have hgot := g14 (k - 141) hoff
      rw [← heq] at hgot
      exact hgot
    have hne19 : UInt16.ofNat k ≠ 19 :=
      ofNat_ne k 19 (by omega) (by omega) (by omega)
    have hne0 : UInt16.ofNat k ≠ 0 :=
      ofNat_ne k 0 (by omega) (by omega) (by omega)
    exact (hpres18 (UInt16.ofNat k) hne19 hne0).trans hcell
  -- ZERO T at pc 153
  have z0 : s18.mem.get s18.pc = 18 := by
    have hp18 : s18.pc = UInt16.ofNat 153 :=
      hs18pc.trans (rfl : (153 : Word) = UInt16.ofNat 153)
    rw [hp18]
    have hval : decChunk009[9]! = 18 := rfl
    exact (g18 153 (by decide) (by decide)).trans ((cell144 9 (by decide)).trans hval)
  have z1 : s18.mem.get (s18.pc + 1) = 18 := by
    have : s18.pc + 1 = (154 : Word) := by simp [hs18pc]
    rw [this, (rfl : (154 : Word) = UInt16.ofNat 154)]
    have hval : decChunk009[10]! = 18 := rfl
    exact (g18 154 (by decide) (by decide)).trans ((cell144 10 (by decide)).trans hval)
  have z2 : s18.mem.get (s18.pc + 2) = s18.pc + 3 := by
    have hp155 : s18.pc + 2 = (155 : Word) := by simp [hs18pc]
    have hp156 : s18.pc + 3 = (156 : Word) := by simp [hs18pc]
    rw [hp155, hp156, (rfl : (155 : Word) = UInt16.ofNat 155)]
    have hval : decChunk009[11]! = 156 := rfl
    have hv : (156 : Word) = UInt16.ofNat 156 := rfl
    exact (g18 155 (by decide) (by decide)).trans ((cell144 11 (by decide)).trans (hval.trans hv))
  have hpc18 : s18.pc.toNat < 32768 := by simp [hs18pc]
  have hzeroT :=
    step_ZERO (s := s18) (x := 18) hs18h hpc18 z0 z1 z2 (by decide)
  have hs19pc : (step s18).pc = 156 := by
    have : s18.pc + 3 = (156 : Word) := by simp [hs18pc]
    rw [hzeroT]
    exact this
  have hs19h : (step s18).halted = false := by
    rw [hzeroT]
    exact hs18h
  have hs19T : (step s18).mem.get 18 = 0 := by
    rw [hzeroT]
    exact Mem.get_set_eq s18.mem 18 0
  have hs19Z : (step s18).mem.get 0 = 0 := by
    rw [hzeroT]
    exact (Mem.get_set_ne s18.mem 18 0 0 (by decide)).trans hZ18
  have hs19N : (step s18).mem.get 17 = input := by
    rw [hzeroT]
    exact (Mem.get_set_ne s18.mem 18 17 0 (by decide)).trans hN18
  have hs19S : (step s18).mem.get 19 = 1 := by
    rw [hzeroT]
    exact (Mem.get_set_ne s18.mem 18 19 0 (by decide)).trans hS18
  have g19 (k : Nat) (hk1 : 156 ≤ k) (hk2 : k < 174) :
      (step s18).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    rw [hzeroT]
    have hne18 : UInt16.ofNat k ≠ 18 :=
      ofNat_ne k 18 (by omega) (by omega) (by omega)
    exact (Mem.get_set_ne s18.mem 18 (UInt16.ofNat k) 0 hne18).trans
      (g18 k (by omega) hk2)
  -- SUB N T at pc 156: T := 0 - input
  have s0 : (step s18).mem.get (step s18).pc = 17 := by
    have hp19 : (step s18).pc = UInt16.ofNat 156 :=
      hs19pc.trans (rfl : (156 : Word) = UInt16.ofNat 156)
    rw [hp19]
    have hval : decChunk009[12]! = 17 := rfl
    exact (g19 156 (by decide) (by decide)).trans ((cell144 12 (by decide)).trans hval)
  have s1 : (step s18).mem.get ((step s18).pc + 1) = 18 := by
    have : (step s18).pc + 1 = (157 : Word) := by simp [hs19pc]
    rw [this, (rfl : (157 : Word) = UInt16.ofNat 157)]
    have hval : decChunk009[13]! = 18 := rfl
    exact (g19 157 (by decide) (by decide)).trans ((cell144 13 (by decide)).trans hval)
  have s2 : (step s18).mem.get ((step s18).pc + 2) = (step s18).pc + 3 := by
    have hp158 : (step s18).pc + 2 = (158 : Word) := by simp [hs19pc]
    have hp159 : (step s18).pc + 3 = (159 : Word) := by simp [hs19pc]
    rw [hp158, hp159, (rfl : (158 : Word) = UInt16.ofNat 158)]
    have hval : decChunk009[14]! = 159 := rfl
    have hv : (159 : Word) = UInt16.ofNat 159 := rfl
    exact (g19 158 (by decide) (by decide)).trans ((cell144 14 (by decide)).trans (hval.trans hv))
  have hpc19 : (step s18).pc.toNat < 32768 := by simp [hs19pc]
  have hsubT :=
    step_SUB (s := step s18) (a := 17) (b := 18)
      hs19h hpc19 s0 s1 s2 (by decide) (by decide)
  have hs20pc : (step (step s18)).pc = 159 := by
    have : (step s18).pc + 3 = (159 : Word) := by simp [hs19pc]
    rw [hsubT]
    exact this
  have hs20h : (step (step s18)).halted = false := by
    rw [hsubT]
    exact hs19h
  have hs20T : (step (step s18)).mem.get 18 = 0 - input := by
    rw [hsubT]
    have : (step s18).mem.get 18 - (step s18).mem.get 17 = 0 - input := by
      rw [hs19T, hs19N]
    exact (Mem.get_set_eq (step s18).mem 18 ((step s18).mem.get 18 - (step s18).mem.get 17)).trans this
  have hs20Z : (step (step s18)).mem.get 0 = 0 := by
    rw [hsubT]
    exact (Mem.get_set_ne (step s18).mem 18 0
      ((step s18).mem.get 18 - (step s18).mem.get 17) (by decide)).trans hs19Z
  have hs20N : (step (step s18)).mem.get 17 = input := by
    rw [hsubT]
    exact (Mem.get_set_ne (step s18).mem 18 17
      ((step s18).mem.get 18 - (step s18).mem.get 17) (by decide)).trans hs19N
  have hs20S : (step (step s18)).mem.get 19 = 1 := by
    rw [hsubT]
    exact (Mem.get_set_ne (step s18).mem 18 19
      ((step s18).mem.get 18 - (step s18).mem.get 17) (by decide)).trans hs19S
  have g20 (k : Nat) (hk1 : 159 ≤ k) (hk2 : k < 174) :
      (step (step s18)).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    rw [hsubT]
    have hne18 : UInt16.ofNat k ≠ 18 :=
      ofNat_ne k 18 (by omega) (by omega) (by omega)
    exact (Mem.get_set_ne (step s18).mem 18 (UInt16.ofNat k)
      ((step s18).mem.get 18 - (step s18).mem.get 17) hne18).trans
      (g19 k (by omega) hk2)
  -- ZERO N at pc 159
  have n0 : (step (step s18)).mem.get (step (step s18)).pc = 17 := by
    have hp20 : (step (step s18)).pc = UInt16.ofNat 159 :=
      hs20pc.trans (rfl : (159 : Word) = UInt16.ofNat 159)
    rw [hp20]
    have hval : decChunk009[15]! = 17 := rfl
    exact (g20 159 (by decide) (by decide)).trans ((cell144 15 (by decide)).trans hval)
  have n1 : (step (step s18)).mem.get ((step (step s18)).pc + 1) = 17 := by
    have : (step (step s18)).pc + 1 = (160 : Word) := by simp [hs20pc]
    rw [this, (rfl : (160 : Word) = UInt16.ofNat 160)]
    have hval : decChunk010[0]! = 17 := rfl
    exact (g20 160 (by decide) (by decide)).trans ((cell160 0 (by decide)).trans hval)
  have n2 : (step (step s18)).mem.get ((step (step s18)).pc + 2) =
      (step (step s18)).pc + 3 := by
    have hp161 : (step (step s18)).pc + 2 = (161 : Word) := by simp [hs20pc]
    have hp162 : (step (step s18)).pc + 3 = (162 : Word) := by simp [hs20pc]
    rw [hp161, hp162, (rfl : (161 : Word) = UInt16.ofNat 161)]
    have hval : decChunk010[1]! = 162 := rfl
    have hv : (162 : Word) = UInt16.ofNat 162 := rfl
    exact (g20 161 (by decide) (by decide)).trans ((cell160 1 (by decide)).trans (hval.trans hv))
  have hpc20 : (step (step s18)).pc.toNat < 32768 := by simp [hs20pc]
  have hzeroN :=
    step_ZERO (s := step (step s18)) (x := 17)
      hs20h hpc20 n0 n1 n2 (by decide)
  let s21 := step (step (step s18))
  have hs21eq : s21 = step (step (step s18)) := rfl
  have hs21pc : (step (step (step s18))).pc = 162 := by
    have : (step (step s18)).pc + 3 = (162 : Word) := by simp [hs20pc]
    rw [hzeroN]
    exact this
  have hs21h : (step (step (step s18))).halted = false := by
    rw [hzeroN]
    exact hs20h
  have hs21N : (step (step (step s18))).mem.get 17 = 0 := by
    rw [hzeroN]
    exact Mem.get_set_eq (step (step s18)).mem 17 0
  have hs21T : (step (step (step s18))).mem.get 18 = 0 - input := by
    rw [hzeroN]
    exact (Mem.get_set_ne (step (step s18)).mem 17 18 0 (by decide)).trans hs20T
  have hs21Z : (step (step (step s18))).mem.get 0 = 0 := by
    rw [hzeroN]
    exact (Mem.get_set_ne (step (step s18)).mem 17 0 0 (by decide)).trans hs20Z
  have hs21S : (step (step (step s18))).mem.get 19 = 1 := by
    rw [hzeroN]
    exact (Mem.get_set_ne (step (step s18)).mem 17 19 0 (by decide)).trans hs20S
  have g21 (k : Nat) (hk1 : 162 ≤ k) (hk2 : k < 174) :
      (step (step (step s18))).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    rw [hzeroN]
    have hne17 : UInt16.ofNat k ≠ 17 :=
      ofNat_ne k 17 (by omega) (by omega) (by omega)
    exact (Mem.get_set_ne (step (step s18)).mem 17 (UInt16.ofNat k) 0 hne17).trans
      (g20 k (by omega) hk2)
  -- SUB T Z at pc 162: Z := 0 - T = input
  have u0 : (step (step (step s18))).mem.get (step (step (step s18))).pc = 18 := by
    have hp21 : (step (step (step s18))).pc = UInt16.ofNat 162 :=
      hs21pc.trans (rfl : (162 : Word) = UInt16.ofNat 162)
    rw [hp21]
    have hval : decChunk010[2]! = 18 := rfl
    exact (g21 162 (by decide) (by decide)).trans ((cell160 2 (by decide)).trans hval)
  have u1 : (step (step (step s18))).mem.get ((step (step (step s18))).pc + 1) = 0 := by
    have : (step (step (step s18))).pc + 1 = (163 : Word) := by simp [hs21pc]
    rw [this, (rfl : (163 : Word) = UInt16.ofNat 163)]
    have hval : decChunk010[3]! = 0 := rfl
    exact (g21 163 (by decide) (by decide)).trans ((cell160 3 (by decide)).trans hval)
  have u2 : (step (step (step s18))).mem.get ((step (step (step s18))).pc + 2) =
      (step (step (step s18))).pc + 3 := by
    have hp164 : (step (step (step s18))).pc + 2 = (164 : Word) := by simp [hs21pc]
    have hp165 : (step (step (step s18))).pc + 3 = (165 : Word) := by simp [hs21pc]
    rw [hp164, hp165, (rfl : (164 : Word) = UInt16.ofNat 164)]
    have hval : decChunk010[4]! = 165 := rfl
    have hv : (165 : Word) = UInt16.ofNat 165 := rfl
    exact (g21 164 (by decide) (by decide)).trans ((cell160 4 (by decide)).trans (hval.trans hv))
  have hpc21 : (step (step (step s18))).pc.toNat < 32768 := by simp [hs21pc]
  have hsubZ :=
    step_SUB (s := step (step (step s18))) (a := 18) (b := 0)
      hs21h hpc21 u0 u1 u2 (by decide) (by decide)
  have hs22pc : (step (step (step (step s18)))).pc = 165 := by
    have : (step (step (step s18))).pc + 3 = (165 : Word) := by simp [hs21pc]
    rw [hsubZ]
    exact this
  have hs22h : (step (step (step (step s18)))).halted = false := by
    rw [hsubZ]
    exact hs21h
  have hs22Z : (step (step (step (step s18)))).mem.get 0 = 0 - (0 - input) := by
    rw [hsubZ]
    have : (step (step (step s18))).mem.get 0 - (step (step (step s18))).mem.get 18 =
        0 - (0 - input) := by
      rw [hs21Z, hs21T]
    exact (Mem.get_set_eq (step (step (step s18))).mem 0
      ((step (step (step s18))).mem.get 0 - (step (step (step s18))).mem.get 18)).trans this
  have hs22N : (step (step (step (step s18)))).mem.get 17 = 0 := by
    rw [hsubZ]
    exact (Mem.get_set_ne (step (step (step s18))).mem 0 17
      ((step (step (step s18))).mem.get 0 - (step (step (step s18))).mem.get 18) (by decide)).trans hs21N
  have hs22T : (step (step (step (step s18)))).mem.get 18 = 0 - input := by
    rw [hsubZ]
    exact (Mem.get_set_ne (step (step (step s18))).mem 0 18
      ((step (step (step s18))).mem.get 0 - (step (step (step s18))).mem.get 18) (by decide)).trans hs21T
  have hs22S : (step (step (step (step s18)))).mem.get 19 = 1 := by
    rw [hsubZ]
    exact (Mem.get_set_ne (step (step (step s18))).mem 0 19
      ((step (step (step s18))).mem.get 0 - (step (step (step s18))).mem.get 18) (by decide)).trans hs21S
  have g22 (k : Nat) (hk1 : 165 ≤ k) (hk2 : k < 174) :
      (step (step (step (step s18)))).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    rw [hsubZ]
    have hne0 : UInt16.ofNat k ≠ 0 :=
      ofNat_ne k 0 (by omega) (by omega) (by omega)
    exact (Mem.get_set_ne (step (step (step s18))).mem 0 (UInt16.ofNat k)
      ((step (step (step s18))).mem.get 0 - (step (step (step s18))).mem.get 18) hne0).trans
      (g21 k (by omega) hk2)
  -- SUB Z N at pc 165: N := 0 - Z = 0 - (0 - input) = input wait NO
  -- Z currently is 0 - (0 - input) which equals input (add_sub_neg).
  -- N is 0, so N := 0 - Z = 0 - (0 - (0 - input)) wait
  -- T = 0 - input
  -- Z := 0 - T = 0 - (0 - input)
  -- N := N - Z = 0 - (0 - (0 - input))  ... that's messy
  -- We want N = 0 - input.
  -- 0 - (0 - (0 - input)) = (0 - input) ? Let's see:
  -- add_sub_neg: a - (0 - b) = a + b, so 0 - (0 - b) = b.
  -- Here Z = 0 - (0 - input) = input, thus N = 0 - Z = 0 - input. YES.
  have v0 : (step (step (step (step s18)))).mem.get (step (step (step (step s18)))).pc = 0 := by
    have hp22 : (step (step (step (step s18)))).pc = UInt16.ofNat 165 :=
      hs22pc.trans (rfl : (165 : Word) = UInt16.ofNat 165)
    rw [hp22]
    have hval : decChunk010[5]! = 0 := rfl
    exact (g22 165 (by decide) (by decide)).trans ((cell160 5 (by decide)).trans hval)
  have v1 : (step (step (step (step s18)))).mem.get ((step (step (step (step s18)))).pc + 1) = 17 := by
    have : (step (step (step (step s18)))).pc + 1 = (166 : Word) := by simp [hs22pc]
    rw [this, (rfl : (166 : Word) = UInt16.ofNat 166)]
    have hval : decChunk010[6]! = 17 := rfl
    exact (g22 166 (by decide) (by decide)).trans ((cell160 6 (by decide)).trans hval)
  have v2 : (step (step (step (step s18)))).mem.get ((step (step (step (step s18)))).pc + 2) =
      (step (step (step (step s18)))).pc + 3 := by
    have hp167 : (step (step (step (step s18)))).pc + 2 = (167 : Word) := by simp [hs22pc]
    have hp168 : (step (step (step (step s18)))).pc + 3 = (168 : Word) := by simp [hs22pc]
    rw [hp167, hp168, (rfl : (167 : Word) = UInt16.ofNat 167)]
    have hval : decChunk010[7]! = 168 := rfl
    have hv : (168 : Word) = UInt16.ofNat 168 := rfl
    exact (g22 167 (by decide) (by decide)).trans ((cell160 7 (by decide)).trans (hval.trans hv))
  have hpc22 : (step (step (step (step s18)))).pc.toNat < 32768 := by simp [hs22pc]
  have hsubN :=
    step_SUB (s := step (step (step (step s18)))) (a := 0) (b := 17)
      hs22h hpc22 v0 v1 v2 (by decide) (by decide)
  have hs23pc : (step (step (step (step (step s18))))).pc = 168 := by
    have : (step (step (step (step s18)))).pc + 3 = (168 : Word) := by simp [hs22pc]
    rw [hsubN]
    exact this
  have hs23h : (step (step (step (step (step s18))))).halted = false := by
    rw [hsubN]
    exact hs22h
  have hs23N : (step (step (step (step (step s18))))).mem.get 17 = 0 - input := by
    rw [hsubN]
    have hZeq : (step (step (step (step s18)))).mem.get 0 = input := by
      have : 0 - (0 - input) = input := by
        simpa using add_sub_neg (0 : Word) input
      exact hs22Z.trans this
    have : (step (step (step (step s18)))).mem.get 17 -
        (step (step (step (step s18)))).mem.get 0 = 0 - input := by
      rw [hs22N, hZeq]
    exact (Mem.get_set_eq (step (step (step (step s18)))).mem 17
      ((step (step (step (step s18)))).mem.get 17 -
        (step (step (step (step s18)))).mem.get 0)).trans this
  have hs23Z : (step (step (step (step (step s18))))).mem.get 0 =
      (step (step (step (step s18)))).mem.get 0 := by
    rw [hsubN]
    exact Mem.get_set_ne (step (step (step (step s18)))).mem 17 0
      ((step (step (step (step s18)))).mem.get 17 -
        (step (step (step (step s18)))).mem.get 0) (by decide)
  have hs23T : (step (step (step (step (step s18))))).mem.get 18 = 0 - input := by
    rw [hsubN]
    exact (Mem.get_set_ne (step (step (step (step s18)))).mem 17 18
      ((step (step (step (step s18)))).mem.get 17 -
        (step (step (step (step s18)))).mem.get 0) (by decide)).trans hs22T
  have hs23S : (step (step (step (step (step s18))))).mem.get 19 = 1 := by
    rw [hsubN]
    exact (Mem.get_set_ne (step (step (step (step s18)))).mem 17 19
      ((step (step (step (step s18)))).mem.get 17 -
        (step (step (step (step s18)))).mem.get 0) (by decide)).trans hs22S
  have g23 (k : Nat) (hk1 : 168 ≤ k) (hk2 : k < 174) :
      (step (step (step (step (step s18))))).mem.get (UInt16.ofNat k) = intfmtImage[k]! := by
    rw [hsubN]
    have hne17 : UInt16.ofNat k ≠ 17 :=
      ofNat_ne k 17 (by omega) (by omega) (by omega)
    exact (Mem.get_set_ne (step (step (step (step s18)))).mem 17 (UInt16.ofNat k)
      ((step (step (step (step s18)))).mem.get 17 -
        (step (step (step (step s18)))).mem.get 0) hne17).trans
      (g22 k (by omega) hk2)
  -- ZERO Z at pc 168
  have y0 : (step (step (step (step (step s18))))).mem.get
      (step (step (step (step (step s18))))).pc = 0 := by
    have hp23 : (step (step (step (step (step s18))))).pc = UInt16.ofNat 168 :=
      hs23pc.trans (rfl : (168 : Word) = UInt16.ofNat 168)
    rw [hp23]
    have hval : decChunk010[8]! = 0 := rfl
    exact (g23 168 (by decide) (by decide)).trans ((cell160 8 (by decide)).trans hval)
  have y1 : (step (step (step (step (step s18))))).mem.get
      ((step (step (step (step (step s18))))).pc + 1) = 0 := by
    have : (step (step (step (step (step s18))))).pc + 1 = (169 : Word) := by simp [hs23pc]
    rw [this, (rfl : (169 : Word) = UInt16.ofNat 169)]
    have hval : decChunk010[9]! = 0 := rfl
    exact (g23 169 (by decide) (by decide)).trans ((cell160 9 (by decide)).trans hval)
  have y2 : (step (step (step (step (step s18))))).mem.get
      ((step (step (step (step (step s18))))).pc + 2) =
      (step (step (step (step (step s18))))).pc + 3 := by
    have hp170 : (step (step (step (step (step s18))))).pc + 2 = (170 : Word) := by simp [hs23pc]
    have hp171 : (step (step (step (step (step s18))))).pc + 3 = (171 : Word) := by simp [hs23pc]
    rw [hp170, hp171, (rfl : (170 : Word) = UInt16.ofNat 170)]
    have hval : decChunk010[10]! = 171 := rfl
    have hv : (171 : Word) = UInt16.ofNat 171 := rfl
    exact (g23 170 (by decide) (by decide)).trans ((cell160 10 (by decide)).trans (hval.trans hv))
  have hpc23 : (step (step (step (step (step s18))))).pc.toNat < 32768 := by simp [hs23pc]
  have hzeroZ :=
    step_ZERO (s := step (step (step (step (step s18))))) (x := 0)
      hs23h hpc23 y0 y1 y2 (by decide)
  have hs24pc : (step (step (step (step (step (step s18)))))).pc = 171 := by
    have : (step (step (step (step (step s18))))).pc + 3 = (171 : Word) := by simp [hs23pc]
    rw [hzeroZ]
    exact this
  have hs24h : (step (step (step (step (step (step s18)))))).halted = false := by
    rw [hzeroZ]
    exact hs23h
  have hs24Z : (step (step (step (step (step (step s18)))))).mem.get 0 = 0 := by
    rw [hzeroZ]
    exact Mem.get_set_eq (step (step (step (step (step s18))))).mem 0 0
  have hs24N : (step (step (step (step (step (step s18)))))).mem.get 17 = 0 - input := by
    rw [hzeroZ]
    exact (Mem.get_set_ne (step (step (step (step (step s18))))).mem 0 17 0 (by decide)).trans hs23N
  have hs24T : (step (step (step (step (step (step s18)))))).mem.get 18 = 0 - input := by
    rw [hzeroZ]
    exact (Mem.get_set_ne (step (step (step (step (step s18))))).mem 0 18 0 (by decide)).trans hs23T
  have hs24S : (step (step (step (step (step (step s18)))))).mem.get 19 = 1 := by
    rw [hzeroZ]
    exact (Mem.get_set_ne (step (step (step (step (step s18))))).mem 0 19 0 (by decide)).trans hs23S
  have g24 (k : Nat) (hk1 : 171 ≤ k) (hk2 : k < 174) :
      (step (step (step (step (step (step s18)))))).mem.get (UInt16.ofNat k) =
        intfmtImage[k]! := by
    rw [hzeroZ]
    have hne0 : UInt16.ofNat k ≠ 0 :=
      ofNat_ne k 0 (by omega) (by omega) (by omega)
    exact (Mem.get_set_ne (step (step (step (step (step s18))))).mem 0 (UInt16.ofNat k) 0 hne0).trans
      (g23 k (by omega) hk2)
  -- JMP DIGITS at pc 171
  have j0 : (step (step (step (step (step (step s18)))))).mem.get
      (step (step (step (step (step (step s18)))))).pc = 0 := by
    have hp24 : (step (step (step (step (step (step s18)))))).pc = UInt16.ofNat 171 :=
      hs24pc.trans (rfl : (171 : Word) = UInt16.ofNat 171)
    rw [hp24]
    have hval : decChunk010[11]! = 0 := rfl
    exact (g24 171 (by decide) (by decide)).trans ((cell160 11 (by decide)).trans hval)
  have j1 : (step (step (step (step (step (step s18)))))).mem.get
      ((step (step (step (step (step (step s18)))))).pc + 1) = 0 := by
    have : (step (step (step (step (step (step s18)))))).pc + 1 = (172 : Word) := by simp [hs24pc]
    rw [this, (rfl : (172 : Word) = UInt16.ofNat 172)]
    have hval : decChunk010[12]! = 0 := rfl
    exact (g24 172 (by decide) (by decide)).trans ((cell160 12 (by decide)).trans hval)
  have j2 : (step (step (step (step (step (step s18)))))).mem.get
      ((step (step (step (step (step (step s18)))))).pc + 2) = 174 := by
    have : (step (step (step (step (step (step s18)))))).pc + 2 = (173 : Word) := by simp [hs24pc]
    rw [this, (rfl : (173 : Word) = UInt16.ofNat 173)]
    have hval : decChunk010[13]! = 174 := rfl
    exact (g24 173 (by decide) (by decide)).trans ((cell160 13 (by decide)).trans hval)
  have hpc24 : (step (step (step (step (step (step s18)))))).pc.toNat < 32768 := by simp [hs24pc]
  have hjmp :=
    step_JMP (s := step (step (step (step (step (step s18)))))) (dest := 174)
      hs24h hpc24 hs24Z j0 j1 j2
  -- s25 = runN s 25 = 14 + 4 + 7 steps
  have hrun : s25 = step (step (step (step (step (step (step s18)))))) := by
    have h25 : runN s 25 = runN s14 11 := runN_add_eq s 14 11 25 (by decide)
    have h11 : runN s14 11 = runN s18 7 := runN_add_eq s14 4 7 11 (by decide)
    have go (t : Machine) (n : Nat)
        (hh : t.halted = false) (hpc : t.pc.toNat < 32768) :
        runN t (n + 1) = runN (step t) n := runN_succ_go t n hh hpc
    have h7 : runN s18 7 = runN (step s18) 6 := go s18 6 hs18h hpc18
    have h6 : runN (step s18) 6 = runN (step (step s18)) 5 :=
      go (step s18) 5 hs19h hpc19
    have h5 : runN (step (step s18)) 5 = runN (step (step (step s18))) 4 :=
      go (step (step s18)) 4 hs20h hpc20
    have h4 : runN (step (step (step s18))) 4 = runN (step (step (step (step s18)))) 3 :=
      go (step (step (step s18))) 3 hs21h hpc21
    have h3 : runN (step (step (step (step s18)))) 3 =
        runN (step (step (step (step (step s18))))) 2 :=
      go (step (step (step (step s18)))) 2 hs22h hpc22
    have h2 : runN (step (step (step (step (step s18))))) 2 =
        step (step (step (step (step (step (step s18)))))) :=
      runN_2_steps (step (step (step (step (step s18))))) hs23h hpc23 hs24h hpc24
    exact h25.trans (h11.trans (h7.trans (h6.trans (h5.trans (h4.trans (h3.trans h2))))))
  have hs25pc : s25.pc = 174 := by
    rw [hrun, hjmp]
  have hs25h : s25.halted = false := by
    rw [hrun, hjmp]
    exact hs24h
  have hs25Z : s25.mem.get 0 = 0 := by
    rw [hrun, hjmp]
    exact hs24Z
  have hs25N : s25.mem.get 17 = 0 - input := by
    rw [hrun, hjmp]
    exact hs24N
  have hs25T : s25.mem.get 18 = 0 - input := by
    rw [hrun, hjmp]
    exact hs24T
  have hs25S : s25.mem.get 19 = 1 := by
    rw [hrun, hjmp]
    exact hs24S
  have hpres25 : ∀ a, a ≠ 18 → a ≠ 0 → a ≠ 19 → a ≠ 17 → s25.mem.get a = s.mem.get a := by
    intro a ha18 ha0 ha19 ha17
    have h1 : s25.mem.get a = s18.mem.get a := by
      rw [hrun, hjmp, hzeroZ, hsubN, hsubZ, hzeroN, hsubT, hzeroT]
      -- after unfolding the 7 mem updates, only 18,0,17,19 were written
      refine (
        (Mem.get_set_ne _ 0 a 0 ha0).trans <|
        (Mem.get_set_ne _ 17 a _ ha17).trans <|
        (Mem.get_set_ne _ 0 a _ ha0).trans <|
        (Mem.get_set_ne _ 17 a 0 ha17).trans <|
        (Mem.get_set_ne _ 18 a _ ha18).trans <|
        (Mem.get_set_ne _ 18 a 0 ha18).trans ?_)
      rfl
    exact h1.trans ((hpres18 a ha19 ha0).trans (hpres14 a ha18 ha0))
  exact ⟨hs25pc, hs25h, hs25N, hs25T, hs25Z, hs25S, hpres25⟩

end IntFmt
