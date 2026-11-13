/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Array-extract splitting, used to kernel-check that the concatenation
of per-line image chunks equals `intfmtImage`.
-/

import IntFmt.DecLoad

namespace IntFmt

/-- `xs.extract s mid ++ xs.extract mid e = xs.extract s e`
when `s ≤ mid ≤ e ≤ xs.size`. -/
theorem extract_split {α : Type _} (xs : Array α) (s mid e : Nat)
    (hsm : s ≤ mid) (hme : mid ≤ e) (he : e ≤ xs.size) :
    xs.extract s mid ++ xs.extract mid e = xs.extract s e := by
  have hms : mid ≤ xs.size := Nat.le_trans hme he
  have hss : s ≤ xs.size := Nat.le_trans hsm hms
  apply Array.ext
  · simp [Array.size_append, Array.size_extract,
      Nat.min_eq_left he, Nat.min_eq_left hms, Nat.min_eq_left hss]
    omega
  · intro i hi1 hi2
    have hszL : (xs.extract s mid).size = mid - s := by
      simp [Array.size_extract, Nat.min_eq_left hms]
    have hszR : (xs.extract mid e).size = e - mid := by
      simp [Array.size_extract, Nat.min_eq_left he]
    have hszA : (xs.extract s e).size = e - s := by
      simp [Array.size_extract, Nat.min_eq_left he]
    have hmin : min mid xs.size - s = mid - s := by
      simp [Nat.min_eq_left hms]
    rw [Array.getElem_append]
    by_cases hlt : i < (xs.extract s mid).size
    · have : i < mid - s := by simpa [hszL] using hlt
      simp [hlt, hmin, this, Array.getElem_extract]
    · have hi' : mid - s ≤ i := by
        have : ¬ i < mid - s := by simpa [hszL] using hlt
        exact Nat.le_of_not_gt this
      have : mid + (i - (xs.extract s mid).size) = s + i := by
        simp [hszL]
        omega
      have : ¬ i < min mid xs.size - s := by
        simpa [hmin, hszL] using hlt
      simp [hlt, this, Array.getElem_extract]
      -- goal: xs[mid + (i - (min mid xs.size - s))] = xs[s + i]
      simp [hmin, hszL]
      -- mid + (i - (mid - s)) = s + i
      have heq : mid + (i - (mid - s)) = s + i := by omega
      simp [heq]

/-- `xs.extract 0 e ++ xs.extract e xs.size = xs` when `e ≤ xs.size`. -/
theorem extract_split_all {α : Type _} (xs : Array α) (e : Nat)
    (he : e ≤ xs.size) :
    xs.extract 0 e ++ xs.extract e xs.size = xs := by
  have h := extract_split xs 0 e xs.size (Nat.zero_le _) he (Nat.le_refl _)
  have hx : xs.extract 0 xs.size = xs := by
    simpa using (Array.extract_size (xs := xs))
  rw [h, hx]

/-- The last character of a tokenized `.dec` fragment is whitespace
(or the fragment is empty), so tokens do not straddle a concatenation. -/
def listEndsWS (cs : List Char) : Prop :=
  match cs.getLast? with
  | none => True
  | some c => isDecWS c = true

theorem listEndsWS_nil : listEndsWS [] := trivial

theorem getLast?_append_right {α} (s t : List α) (c : α)
    (ht : t.getLast? = some c) :
    (s ++ t).getLast? = some c := by
  simp [List.getLast?_append, ht]

theorem listEndsWS_append (s t : List Char)
    (hs : listEndsWS s) (ht : listEndsWS t) :
    listEndsWS (s ++ t) := by
  unfold listEndsWS at *
  cases htr : t.getLast? with
  | none =>
    have : t = [] := List.getLast?_eq_none_iff.mp htr
    subst t
    simpa using hs
  | some c =>
    have : (s ++ t).getLast? = some c := getLast?_append_right s t c htr
    simpa [this] using (by simpa [htr] using ht)

theorem parseDecText_empty : parseDecText "" = #[] := rfl

theorem tokensAux_nil (n : Nat) : tokensAux n [] = [] := by
  cases n with
  | zero => rfl
  | succ _ => rfl

theorem mem_of_getLast? {α} {cs : List α} {c : α}
    (h : cs.getLast? = some c) : c ∈ cs := by
  induction cs with
  | nil => simp at h
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp [List.getLast?] at h
      subst h
      simp
    | cons y ys =>
      have : (x :: y :: ys).getLast? = (y :: ys).getLast? := by
        simp [List.getLast?]
      have hy : (y :: ys).getLast? = some c := by
        simpa [this] using h
      exact List.mem_cons_of_mem x (ih hy)

theorem takeWhile_append_hit {α} (p : α → Bool) (s t : List α)
    (hit : ∃ x ∈ s, p x = false) :
    List.takeWhile p (s ++ t) = List.takeWhile p s := by
  induction s with
  | nil =>
    obtain ⟨_, hx, _⟩ := hit
    simp at hx
  | cons c rest ih =>
    cases hc : p c
    · simp [List.takeWhile, hc]
    · have hit' : ∃ x ∈ rest, p x = false := by
        obtain ⟨x, hx, hpx⟩ := hit
        have : x = c ∨ x ∈ rest := List.mem_cons.mp hx
        cases this with
        | inl heq =>
          subst heq
          simp [hc] at hpx
        | inr hr => exact ⟨x, hr, hpx⟩
      simp [List.takeWhile, hc, ih hit']

theorem dropWhile_append_hit {α} (p : α → Bool) (s t : List α)
    (hit : ∃ x ∈ s, p x = false) :
    List.dropWhile p (s ++ t) = List.dropWhile p s ++ t := by
  induction s with
  | nil =>
    obtain ⟨_, hx, _⟩ := hit
    simp at hx
  | cons c rest ih =>
    cases hc : p c
    · simp [List.dropWhile, hc]
    · have hit' : ∃ x ∈ rest, p x = false := by
        obtain ⟨x, hx, hpx⟩ := hit
        have : x = c ∨ x ∈ rest := List.mem_cons.mp hx
        cases this with
        | inl heq =>
          subst heq
          simp [hc] at hpx
        | inr hr => exact ⟨x, hr, hpx⟩
      simp [List.dropWhile, hc, ih hit']

theorem dropWhile_length_le {α} (p : α → Bool) (s : List α) :
    (s.dropWhile p).length ≤ s.length := by
  induction s with
  | nil => simp
  | cons c rest ih =>
    cases hc : p c
    · simp [List.dropWhile, hc]
    · simp [List.dropWhile, hc]
      exact Nat.le_trans ih (Nat.le_succ _)

theorem dropWhile_cons_notWS (c : Char) (rest : List Char)
    (hc : isDecWS c = false) :
    (c :: rest).dropWhile (fun x => !isDecWS x) =
      rest.dropWhile (fun x => !isDecWS x) := by
  have : (!isDecWS c) = true := by simp [hc]
  simp [List.dropWhile, this]

/-- Extra fuel beyond `cs.length` does not change the token list. -/
theorem tokensAux_extra {fuel : Nat} {cs : List Char}
    (h : cs.length ≤ fuel) :
    tokensAux (fuel + 1) cs = tokensAux fuel cs := by
  induction fuel generalizing cs with
  | zero =>
    have : cs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h)
    subst this
    simp [tokensAux_nil]
  | succ fuel ih =>
    cases cs with
    | nil => simp [tokensAux_nil]
    | cons c rest =>
      cases hc : isDecWS c
      · have hrest : rest.length ≤ fuel := by
          simp at h
          omega
        have hdw : (rest.dropWhile (fun x => !isDecWS x)).length ≤ fuel :=
          Nat.le_trans (dropWhile_length_le (fun x => !isDecWS x) rest) hrest
        simp [tokensAux, hc, dropWhile_cons_notWS c rest hc]
        exact ih hdw
      · have hrest : rest.length ≤ fuel := by
          simp at h
          omega
        simp [tokensAux, hc]
        exact ih hrest

theorem tokensAux_ge_add (n k : Nat) (cs : List Char) (hn : cs.length ≤ n) :
    tokensAux (n + k) cs = tokensAux n cs := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.add_succ, tokensAux_extra (by omega), ih]

theorem tokensAux_ge (n fuel : Nat) (cs : List Char)
    (hn : cs.length ≤ n) (hf : n ≤ fuel) :
    tokensAux fuel cs = tokensAux n cs := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hf
  simpa [hk] using tokensAux_ge_add n k cs hn

theorem tokensAux_complete {fuel : Nat} {cs : List Char}
    (h : cs.length ≤ fuel) :
    tokensAux fuel cs = tokensChars cs :=
  tokensAux_ge cs.length fuel cs (Nat.le_refl _) h

theorem listEndsWS_tail_of_ws {c : Char} {rest : List Char}
    (hw : isDecWS c = true) (hs : listEndsWS (c :: rest)) :
    listEndsWS rest := by
  unfold listEndsWS at *
  cases rest with
  | nil => trivial
  | cons x xs =>
    simpa [List.getLast?] using hs

theorem getLast?_dropWhile_hit {α} (p : α → Bool) (s : List α)
    (hit : ∃ x ∈ s, p x = false) :
    (s.dropWhile p).getLast? = s.getLast? := by
  induction s with
  | nil =>
    obtain ⟨_, hx, _⟩ := hit
    simp at hx
  | cons c rest ih =>
    cases hc : p c
    · simp [List.dropWhile, hc]
    · have hit' : ∃ x ∈ rest, p x = false := by
        obtain ⟨x, hx, hpx⟩ := hit
        have : x = c ∨ x ∈ rest := List.mem_cons.mp hx
        cases this with
        | inl heq =>
          subst heq
          simp [hc] at hpx
        | inr hr => exact ⟨x, hr, hpx⟩
      have hne : rest ≠ [] := by
        intro hr
        subst hr
        obtain ⟨_, hx, _⟩ := hit'
        simp at hx
      have hlast : (c :: rest).getLast? = rest.getLast? := by
        cases rest with
        | nil => exact (hne rfl).elim
        | cons _ _ => simp [List.getLast?]
      simp [List.dropWhile, hc, hlast, ih hit']

theorem listEndsWS_dropWhile (s : List Char) (hs : listEndsWS s)
    (hit : ∃ x ∈ s, (fun y => !isDecWS y) x = false) :
    listEndsWS (s.dropWhile (fun x => !isDecWS x)) := by
  unfold listEndsWS at *
  have := getLast?_dropWhile_hit (fun y => !isDecWS y) s hit
  cases h : s.getLast? with
  | none => simpa [this, h]
  | some c => simpa [this, h] using (by simpa [h] using hs)

theorem tokensAux_append (fuel : Nat) (s t : List Char)
    (hf : s.length + t.length ≤ fuel) (hs : listEndsWS s) :
    tokensAux fuel (s ++ t) = tokensAux s.length s ++ tokensAux t.length t := by
  induction fuel generalizing s with
  | zero =>
    have hs0 : s.length = 0 := by omega
    have ht0 : t.length = 0 := by omega
    have hsnil : s = [] := List.eq_nil_of_length_eq_zero hs0
    have htnil : t = [] := List.eq_nil_of_length_eq_zero ht0
    subst hsnil
    subst htnil
    simp [tokensAux_nil]
  | succ fuel ih =>
    cases s with
    | nil =>
      have : t.length ≤ fuel + 1 := by simpa using hf
      simp [tokensAux_nil, tokensChars, tokensAux_complete this]
    | cons c rest =>
      cases hc : isDecWS c
      · have hit : ∃ x ∈ (c :: rest), (fun y => !isDecWS y) x = false := by
          unfold listEndsWS at hs
          cases hgl : (c :: rest).getLast? with
          | none => simp at hgl
          | some x =>
            refine ⟨x, mem_of_getLast? hgl, ?_⟩
            have hx : isDecWS x = true := by simpa [hgl] using hs
            simp [hx]
        have htw := takeWhile_append_hit (fun x => !isDecWS x) (c :: rest) t hit
        have hdw := dropWhile_append_hit (fun x => !isDecWS x) (c :: rest) t hit
        have hafter_ws : listEndsWS ((c :: rest).dropWhile (fun x => !isDecWS x)) :=
          listEndsWS_dropWhile (c :: rest) hs hit
        have hs_len : (c :: rest).length = rest.length + 1 := rfl
        have hafter_len :
            ((c :: rest).dropWhile (fun x => !isDecWS x)).length ≤ rest.length := by
          rw [dropWhile_cons_notWS c rest hc]
          exact dropWhile_length_le (fun x => !isDecWS x) rest
        have hlenAfter :
            ((c :: rest).dropWhile (fun x => !isDecWS x)).length + t.length ≤ fuel := by
          omega
        have ih' :=
          ih ((c :: rest).dropWhile (fun x => !isDecWS x)) hlenAfter hafter_ws
        have lhs :
            tokensAux (fuel + 1) (c :: rest ++ t) =
              (c :: rest ++ t).takeWhile (fun x => !isDecWS x) ::
                tokensAux fuel ((c :: rest ++ t).dropWhile (fun x => !isDecWS x)) := by
          have : isDecWS c = false := hc
          simp [tokensAux, this]
        have rhs :
            tokensAux (rest.length + 1) (c :: rest) =
              (c :: rest).takeWhile (fun x => !isDecWS x) ::
                tokensAux rest.length
                  ((c :: rest).dropWhile (fun x => !isDecWS x)) := by
          simp [tokensAux, hc]
        rw [lhs, htw, show (c :: rest ++ t) = (c :: rest) ++ t from rfl, hdw, ih']
        rw [hs_len, rhs]
        simp
        exact (tokensAux_ge
          ((c :: rest).dropWhile (fun x => !isDecWS x)).length
          rest.length
          ((c :: rest).dropWhile (fun x => !isDecWS x))
          (Nat.le_refl _) hafter_len).symm
      · have hs' : listEndsWS rest := listEndsWS_tail_of_ws hc hs
        have hf' : rest.length + t.length ≤ fuel := by
          have : (c :: rest).length = rest.length + 1 := rfl
          omega
        simp [tokensAux, hc, ih rest hf' hs']

theorem tokensChars_append (s t : List Char) (hs : listEndsWS s) :
    tokensChars (s ++ t) = tokensChars s ++ tokensChars t := by
  have hf : s.length + t.length ≤ (s ++ t).length := by simp [List.length_append]
  have h := tokensAux_append (s ++ t).length s t hf hs
  simpa [tokensChars, List.length_append] using h

theorem toList_append (s t : String) : (s ++ t).toList = s.toList ++ t.toList :=
  String.toList_append

theorem parseDecChars_append (s t : List Char) (hs : listEndsWS s) :
    parseDecChars (s ++ t) = parseDecChars s ++ parseDecChars t := by
  -- List.append_toArray : l₁.toArray ++ l₂.toArray = (l₁ ++ l₂).toArray
  simp [parseDecChars, tokensChars_append s t hs, List.map_append, List.append_toArray]

/-- Parser of a concatenation, when the left side is empty or ends in
whitespace (every generated `.dec` line ends in a newline). -/
theorem parseDecText_append (s t : String) (hs : listEndsWS s.toList) :
    parseDecText (s ++ t) = parseDecText s ++ parseDecText t := by
  rw [parseDecText, toList_append, parseDecChars_append (s := s.toList) (t := t.toList) hs]
  rfl

/-- Left-associated concatenation of the first `n` strings of an array. -/
def catStrings (xs : Array String) : Nat → String
  | 0 => ""
  | n + 1 =>
    if h : n < xs.size then catStrings xs n ++ xs[n] else catStrings xs n

/-- Left-associated concatenation of the first `n` arrays. -/
def catArrays {α} (xs : Array (Array α)) : Nat → Array α
  | 0 => #[]
  | n + 1 =>
    if h : n < xs.size then catArrays xs n ++ xs[n] else catArrays xs n

theorem catStrings_zero (xs : Array String) : catStrings xs 0 = "" := rfl

theorem catStrings_succ (xs : Array String) (n : Nat) (h : n < xs.size) :
    catStrings xs (n + 1) = catStrings xs n ++ xs[n] := by
  simp [catStrings, h]

theorem catArrays_zero {α} (xs : Array (Array α)) : catArrays xs 0 = #[] := rfl

theorem catArrays_succ {α} (xs : Array (Array α)) (n : Nat) (h : n < xs.size) :
    catArrays xs (n + 1) = catArrays xs n ++ xs[n] := by
  simp [catArrays, h]

theorem listEndsWS_catStrings (xs : Array String) (n : Nat) (hn : n ≤ xs.size)
    (hws : ∀ i, (hi : i < n) →
      listEndsWS (xs[i]'(Nat.lt_of_lt_of_le hi hn)).toList) :
    listEndsWS (catStrings xs n).toList := by
  induction n with
  | zero =>
    simp [catStrings]
    exact listEndsWS_nil
  | succ n ih =>
    have hn' : n < xs.size := Nat.lt_of_succ_le hn
    rw [catStrings_succ xs n hn', toList_append]
    refine listEndsWS_append _ _ (ih (Nat.le_of_lt hn') (fun i hi =>
      hws i (Nat.lt_succ_of_lt hi))) ?_
    exact hws n (Nat.lt_succ_self n)

theorem getElem_map_parse (xs : Array String) (n : Nat) (h : n < xs.size) :
    (xs.map parseDecText)[n]'(by simp [Array.size_map, h]) = parseDecText xs[n] := by
  simp [Array.getElem_map]

/-- Parsing the concatenation of `n` newline-terminated lines is the
concatenation of the per-line parses. -/
theorem parseDecText_catStrings (xs : Array String) (n : Nat) (hn : n ≤ xs.size)
    (hws : ∀ i, (hi : i < n) →
      listEndsWS (xs[i]'(Nat.lt_of_lt_of_le hi hn)).toList) :
    parseDecText (catStrings xs n) = catArrays (xs.map parseDecText) n := by
  induction n with
  | zero =>
    simp [catStrings, catArrays, parseDecText_empty]
  | succ n ih =>
    have hn' : n < xs.size := Nat.lt_of_succ_le hn
    have hmap : n < (xs.map parseDecText).size := by simp [Array.size_map, hn']
    rw [catStrings_succ xs n hn', catArrays_succ (xs.map parseDecText) n hmap]
    have hs : listEndsWS (catStrings xs n).toList :=
      listEndsWS_catStrings xs n (Nat.le_of_lt hn')
        (fun i hi => hws i (Nat.lt_succ_of_lt hi))
    rw [parseDecText_append _ _ hs, ih (Nat.le_of_lt hn')
      (fun i hi => hws i (Nat.lt_succ_of_lt hi)), getElem_map_parse xs n hn']

/-- `xs.extract 0 (16 * n)` splits into `n` adjacent 16-cell chunks
when those chunks fit in `xs`. -/
theorem extract_chunks16 {α} (xs : Array α) (chunks : Array (Array α))
    (n : Nat) (hn : n ≤ chunks.size)
    (hfit : 16 * n ≤ xs.size)
    (hch : ∀ i, (hi : i < n) →
      xs.extract (16 * i) (16 * i + 16) = chunks[i]'(Nat.lt_of_lt_of_le hi hn)) :
    xs.extract 0 (16 * n) = catArrays chunks n := by
  induction n with
  | zero =>
    apply Array.ext
    · simp [catArrays, Array.size_extract]
    · intro i hi1 hi2
      simp [catArrays] at hi1
  | succ n ih =>
    have hn' : n < chunks.size := Nat.lt_of_succ_le hn
    have hfitn : 16 * n ≤ xs.size := by omega
    have hend : 16 * (n + 1) ≤ xs.size := hfit
    have hmid : 16 * n ≤ 16 * (n + 1) := Nat.mul_le_mul_left 16 (Nat.le_succ n)
    have hsplit := extract_split xs 0 (16 * n) (16 * (n + 1))
      (Nat.zero_le _) hmid hend
    have hchunk : xs.extract (16 * n) (16 * n + 16) =
        chunks[n]'(hn') := by
      have : 16 * n + 16 = 16 * (n + 1) := by omega
      simpa [this] using hch n (Nat.lt_succ_self n)
    rw [catArrays_succ chunks n hn']
    rw [← ih (Nat.le_of_lt hn') hfitn (fun i hi => hch i (Nat.lt_succ_of_lt hi))]
    rw [← hsplit]
    have hidx : 16 * n + 16 = 16 * (n + 1) := by omega
    rw [← hidx, hchunk]

/-- Pointwise agreement of `f ∘ xs` with `ys` gives `xs.map f = ys`. -/
theorem map_eq_of_get {α β} (f : α → β) (xs : Array α) (ys : Array β)
    (hsize : xs.size = ys.size)
    (hget : ∀ i, (hi : i < xs.size) → f xs[i] = ys[i]'(hsize ▸ hi)) :
    xs.map f = ys := by
  apply Array.ext
  · simp [Array.size_map, hsize]
  · intro i hi1 hi2
    have hi : i < xs.size := by simpa [Array.size_map] using hi1
    have := hget i hi
    simpa [Array.getElem_map] using this

/-- Concatenate three adjacent extracts. -/
theorem extract_split3 {α} (xs : Array α) (a b c : Nat)
    (ha : a ≤ b) (hb : b ≤ c) (hc : c ≤ xs.size) :
    xs.extract 0 a ++ xs.extract a b ++ xs.extract b c = xs.extract 0 c := by
  have h1 := extract_split xs 0 a b (Nat.zero_le _) ha (Nat.le_trans hb hc)
  have h2 := extract_split xs 0 b c (Nat.le_trans (Nat.zero_le a) ha) hb hc
  rw [h1, h2]


/-- `xs.extract base (base + 16 * n)` splits into `n` adjacent 16-cell chunks. -/
theorem extract_chunks16_from {α} (xs : Array α) (chunks : Array (Array α))
    (base n : Nat) (hn : n ≤ chunks.size)
    (hfit : base + 16 * n ≤ xs.size)
    (hch : ∀ i, (hi : i < n) →
      xs.extract (base + 16 * i) (base + 16 * i + 16) =
        chunks[i]'(Nat.lt_of_lt_of_le hi hn)) :
    xs.extract base (base + 16 * n) = catArrays chunks n := by
  induction n with
  | zero =>
    have hbase : base ≤ xs.size := by omega
    have hsz : (xs.extract base (base + 16 * 0)).size = 0 := by
      simp [Array.size_extract, Nat.min_eq_left hbase]
    apply Array.ext
    · simp [catArrays, Array.size_extract, Nat.min_eq_left hbase]
    · intro i hi1 _hi2
      simp [Array.size_extract, Nat.min_eq_left hbase] at hi1
  | succ n ih =>
    have hn' : n < chunks.size := Nat.lt_of_succ_le hn
    have hfitn : base + 16 * n ≤ xs.size := by omega
    have hend : base + 16 * (n + 1) ≤ xs.size := hfit
    have hmid : base + 16 * n ≤ base + 16 * (n + 1) := by omega
    have hsplit := extract_split xs base (base + 16 * n) (base + 16 * (n + 1))
      (by omega) hmid hend
    have hchunk : xs.extract (base + 16 * n) (base + 16 * n + 16) =
        chunks[n]'(hn') := by
      have : base + 16 * n + 16 = base + 16 * (n + 1) := by omega
      simpa [this] using hch n (Nat.lt_succ_self n)
    rw [catArrays_succ chunks n hn']
    rw [← ih (Nat.le_of_lt hn') hfitn (fun i hi => hch i (Nat.lt_succ_of_lt hi))]
    rw [← hsplit]
    have hidx : base + 16 * n + 16 = base + 16 * (n + 1) := by omega
    rw [← hidx, hchunk]

end IntFmt
