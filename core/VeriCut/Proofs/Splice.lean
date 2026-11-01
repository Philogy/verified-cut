import VeriCut.Proofs.RoundTrip
import VeriCut.Export

/-! Splicing valid clips gives valid PCM, so the export round-trips. -/

namespace VeriCut

theorem Clip.size_samples (format : Format) (c : Clip) (h : c.Valid format) :
    c.samples.size = (c.stop - c.start) * format.channels := by
  have hsz := Flac.size_eq_length_mul c.src h.src
  have : c.stop * c.src.format.channels ≤ c.src.samples.size := by
    rw [hsz]; exact Nat.mul_le_mul_right _ h.range.2
  simp only [Clip.samples, Array.size_extract, h.format] at *
  rw [Nat.min_eq_left this, Nat.sub_mul]

theorem foldl_append_size (l : List (Array Int)) (acc : Array Int) :
    (l.foldl (· ++ ·) acc).size = acc.size + (l.map Array.size).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem mem_foldl_append (l : List (Array Int)) (acc : Array Int) (v : Int) (h : v ∈ l.foldl (· ++ ·) acc) :
    v ∈ acc ∨ ∃ a ∈ l, v ∈ a := by
  induction l generalizing acc with
  | nil => exact Or.inl h
  | cons a l ih =>
    rcases ih _ h with h | ⟨b, hb, hv⟩
    · rcases Array.mem_append.1 h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨a, by simp, h⟩
    · exact Or.inr ⟨b, by simp [hb], hv⟩

theorem sum_map_mul {α : Type} (l : List α) (f : α → Nat) (k : Nat) :
    (l.map fun x => f x * k).sum = (l.map f).sum * k := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.add_mul]

/-- The splice of valid clips that fits in FLAC is valid PCM. -/
theorem splice_valid (format : Format) (clips : List Clip) (valid : ∀ c ∈ clips, c.Valid format)
    (nonempty : clips ≠ []) (short : (clips.map fun c => c.stop - c.start).sum < 2 ^ 36) :
    (splice format clips).Valid := by
  obtain ⟨c0, hc0⟩ := List.exists_mem_of_ne_nil clips nonempty
  have v0 := valid c0 hc0
  have hf := v0.format
  have hC := hf ▸ v0.src.channels
  have hsize : (splice format clips).samples.size = (clips.map fun c => c.stop - c.start).sum * format.channels := by
    simp only [splice, foldl_append_size, List.map_map]
    simp only [Array.size_empty, Nat.zero_add]
    rw [← sum_map_mul]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact Clip.size_samples format c (valid c hc)
  refine ⟨hC, hf ▸ v0.src.bitsPerSample, hf ▸ v0.src.sampleRate, ?_, ?_, ?_⟩
  · show (splice format clips).samples.size % format.channels = 0
    rw [hsize]; exact Nat.mul_mod_left _ _
  · show (splice format clips).samples.size / format.channels < 2 ^ 36
    rw [hsize, Nat.mul_div_cancel _ (by omega)]; exact short
  · intro v hv
    rcases mem_foldl_append _ _ v hv with h | ⟨a, ha, hv⟩
    · simp at h
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
      have := (valid c hc).src.range v (Flac.mem_extract hv)
      rwa [(valid c hc).format] at this

end VeriCut

namespace VeriCut

theorem Pcm.valid_of_isValid (x : Pcm) (hv : x.isValid = true) : x.Valid := by
  simp only [Pcm.isValid, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true] at hv
  obtain ⟨⟨c1, c2, b1, b2, r1, r2, w, l⟩, hr⟩ := hv
  refine ⟨⟨c1, c2⟩, ⟨b1, b2⟩, ⟨r1, r2⟩, w, l, ?_⟩
  intro v hv
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hv
  simpa using hr i hi

/-- The CLI's check establishes the theorems' hypothesis. -/
theorem Pcm.valid_of_validate (x : Pcm) (h : x.validate = .ok ()) : x.Valid := by
  unfold Pcm.validate at h
  split at h
  · exact x.valid_of_isValid ‹_›
  · cases h

end VeriCut
