import VeriCut.Spec.Stream

namespace VeriCut

variable {α Pic : Type}

theorem picture_eq (c : Codec α Pic) (s : Stream α) (i : Nat) (h : i < s.length) :
    picture c s i =
      c.step s[i].data (s[i].refs.map fun r => if r < i then picture c s r else c.blank) := by
  rw [picture]; simp [h]

theorem length_decode (c : Codec α Pic) (s : Stream α) : (decode c s).length = s.length := by
  simp [decode]

theorem getElem_decode (c : Codec α Pic) (s : Stream α) (i : Nat) (h : i < (decode c s).length) :
    (decode c s)[i] = picture c s i := by
  simp [decode]

theorem length_extract [Inhabited α] (s : Stream α) (ks : List Nat) :
    (extract s ks).length = ks.length := by simp [extract]

/-- **Copy soundness.** Copying a dependency-closed set of packets byte-for-byte
yields exactly the same pictures, for every codec. -/
theorem picture_extract [Inhabited α] (c : Codec α Pic) (s : Stream α) (ks : List Nat)
    (hwf : s.WellFormed) (hks : CopySet s ks) :
    ∀ j (hj : j < ks.length), picture c (extract s ks) j = picture c s ks[j] := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
  intro hj
  have hk : ks[j] < s.length := hks.bound _ (List.getElem_mem hj)
  have hjt : j < (extract s ks).length := by simp [length_extract, hj]
  rw [picture_eq c _ j hjt, picture_eq c s _ hk]
  have hget : (extract s ks)[j] = { s[ks[j]] with refs := s[ks[j]].refs.map (ks.idxOf ·) } := by
    simp [extract, List.getD_eq_getElem?_getD, hk]
  simp only [hget, List.map_map]
  congr 1
  apply List.map_congr_left
  intro r hr
  have hrk : r < ks[j] := hwf _ hk r hr
  have hrmem : r ∈ ks := hks.closed _ (List.getElem_mem hj) hk r hr
  have hm : ks.idxOf r < ks.length := List.idxOf_lt_length_of_mem hrmem
  have hkm : ks[ks.idxOf r] = r := List.getElem_idxOf hm
  have hmj : ks.idxOf r < j := by
    have hp := List.pairwise_iff_getElem.mp hks.sorted
    rcases Nat.lt_trichotomy (ks.idxOf r) j with h | h | h
    · exact h
    · exfalso; subst h; omega
    · exfalso; have := hp j _ hj hm h; omega
  simp only [Function.comp, hmj, hrk, if_true]
  rw [ih _ hmj hm, hkm]

/-- Copy soundness, whole-stream form. -/
theorem decode_extract [Inhabited α] (c : Codec α Pic) (s : Stream α) (ks : List Nat)
    (hwf : s.WellFormed) (hks : CopySet s ks) :
    decode c (extract s ks) = ks.map (picture c s) := by
  apply List.ext_getElem
  · simp [length_decode, length_extract]
  · intro j h1 h2
    rw [getElem_decode, List.getElem_map]
    exact picture_extract c s ks hwf hks j (by simpa [length_decode, length_extract] using h1)

/-! ## Concatenation -/

theorem length_shift (n : Nat) (s : Stream α) : (shift n s).length = s.length := by simp [shift]

theorem picture_append_left (c : Codec α Pic) (e t : Stream α) (he : e.WellFormed) :
    ∀ i, i < e.length → picture c (e ++ t) i = picture c e i := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
  intro hi
  have hi' : i < (e ++ t).length := by simp; omega
  rw [picture_eq c _ i hi', picture_eq c e i hi]
  simp only [List.getElem_append_left hi]
  congr 1
  apply List.map_congr_left
  intro r hr
  have : r < i := he i hi r hr
  simp only [this, if_true]
  exact ih r this (by omega)

theorem picture_append_shift (c : Codec α Pic) (e t : Stream α) (ht : t.WellFormed) :
    ∀ j, j < t.length → picture c (e ++ shift e.length t) (e.length + j) = picture c t j := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
  intro hj
  have hj' : e.length + j < (e ++ shift e.length t).length := by simp [length_shift]; omega
  rw [picture_eq c _ _ hj', picture_eq c t j hj]
  have hget : (e ++ shift e.length t)[e.length + j] =
      { t[j] with refs := t[j].refs.map (· + e.length) } := by
    rw [List.getElem_append_right (by omega)]
    simp [shift]
  simp only [hget, List.map_map]
  congr 1
  apply List.map_congr_left
  intro r hr
  have hrj : r < j := ht j hj r hr
  have h1 : r + e.length < e.length + j := by omega
  simp only [Function.comp, h1, hrj, if_true]
  have := ih r hrj (by omega)
  rw [show r + e.length = e.length + r by omega]
  exact this

theorem wellFormed_append_shift (e t : Stream α) (he : e.WellFormed) (ht : t.WellFormed) :
    (e ++ shift e.length t).WellFormed := by
  intro i hi r hr
  by_cases h : i < e.length
  · rw [List.getElem_append_left h] at hr
    exact he i h r hr
  · rw [List.getElem_append_right (by omega)] at hr
    simp only [shift, List.getElem_map, List.mem_map] at hr
    obtain ⟨r0, hr0, rfl⟩ := hr
    have hlt : i - e.length < t.length := by simp [length_shift] at hi; omega
    have := ht (i - e.length) hlt r0 hr0
    omega

/-- **Splice.** Appending a self-contained stream decodes to the two decodes
appended. Nothing in the second part can see the first. -/
theorem decode_append_shift (c : Codec α Pic) (e t : Stream α)
    (he : e.WellFormed) (ht : t.WellFormed) :
    decode c (e ++ shift e.length t) = decode c e ++ decode c t := by
  apply List.ext_getElem
  · simp [length_decode, length_shift]
  · intro i h1 h2
    rw [getElem_decode]
    simp only [length_decode, length_shift, List.length_append] at h1
    by_cases h : i < e.length
    · rw [List.getElem_append_left (by simpa [length_decode] using h), getElem_decode]
      exact picture_append_left c e _ he i h
    · rw [List.getElem_append_right (by simpa [length_decode] using h), getElem_decode]
      have := picture_append_shift c e t ht (i - e.length) (by omega)
      rw [show e.length + (i - e.length) = i by omega] at this
      simpa [length_decode] using this

theorem length_concatStreams (xs : List (Stream α)) :
    (concatStreams xs).length = (xs.map List.length).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [concatStreams, length_shift, ih]

theorem wellFormed_concatStreams (xs : List (Stream α)) (h : ∀ x ∈ xs, x.WellFormed) :
    (concatStreams xs).WellFormed := by
  induction xs with
  | nil => intro i hi; simp [concatStreams] at hi
  | cons x xs ih =>
    exact wellFormed_append_shift x _ (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

/-- Concatenating self-contained segments decodes segment by segment. -/
theorem decode_concatStreams (c : Codec α Pic) (xs : List (Stream α))
    (h : ∀ x ∈ xs, x.WellFormed) :
    decode c (concatStreams xs) = (xs.map (decode c)).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [concatStreams, List.map_cons, List.flatten_cons]
    rw [decode_append_shift c x _ (h x (by simp))
      (wellFormed_concatStreams xs fun y hy => h y (by simp [hy]))]
    rw [ih fun y hy => h y (by simp [hy])]

end VeriCut
