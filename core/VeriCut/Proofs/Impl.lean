import VeriCut.Impl.Planner
import VeriCut.Proofs.Planner

namespace VeriCut

variable {α : Type} [Inhabited α]

theorem copyTable_size (s : Stream α) (r : DisplayRange) (k : Nat) :
    (copyTable s r k).size = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [copyTable, ih]

theorem copyTable_getD (s : Stream α) (r : DisplayRange) :
    ∀ k i, i < k → (copyTable s r k).getD i false = copyable s r i := by
  intro k
  induction k with
  | zero => intro i h; omega
  | succ k ih =>
    intro i hi
    have hsz := copyTable_size s r k
    simp only [copyTable]
    by_cases h : i < k
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
      simp only [hsz, show i ≠ k by omega, if_false]
      rw [← Array.getD_eq_getD_getElem?]
      exact ih i h
    · have hik : i = k := by omega
      subst hik
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_push]
      simp only [hsz, if_true, Option.getD_some]
      rw [copyEntry, copyable_eq]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · intro hh x hx; have := hh x hx; exact ⟨this.1, by rw [← ih x this.1]; exact this.2⟩
      · intro hh x hx; have := hh x hx; exact ⟨this.1, by rw [ih x this.1]; exact this.2⟩

/-- The table agrees with the reference definition. -/
theorem table_eq_copyable (s : Stream α) (r : DisplayRange) (i : Nat) (hi : i < s.length) :
    (copyTable s r s.length).getD i false = copyable s r i :=
  copyTable_getD s r _ i hi

theorem runs_flatten (f : Nat → Bool) (l : List Nat) :
    ((runs f l).map Prod.snd).flatten = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [runs]
    split
    · rename_i h; simp [h] at ih; simp [ih]
    · rename_i b run rest h
      rw [h] at ih
      split <;> simp_all

theorem runs_const (f : Nat → Bool) (l : List Nat) :
    ∀ p ∈ runs f l, ∀ x ∈ p.2, f x = p.1 := by
  induction l with
  | nil => simp [runs]
  | cons x xs ih =>
    simp only [runs]
    split
    · simp
    · rename_i b run rest h
      rw [h] at ih
      split
      · rename_i hb
        intro p hp y hy
        simp at hp
        rcases hp with rfl | hp
        · simp at hy; rcases hy with rfl | hy
          · simpa using (beq_iff_eq.mp hb).symm
          · exact ih (b, run) (by simp) y hy
        · exact ih p (by simp [hp]) y hy
      · intro p hp y hy
        simp at hp
        rcases hp with rfl | rfl | hp
        · simp at hy; subst hy; rfl
        · exact ih (b, run) (by simp) y hy
        · exact ih p (by simp [hp]) y hy

theorem checkClosed_sound (s : Stream α) (ks : List Nat) (h : checkClosed s ks = true) :
    DepClosed s ks := by
  intro k hk hlen x hx
  simp only [checkClosed, List.all_eq_true, List.contains_iff_mem] at h
  have := h k hk x (by simpa [List.getD_eq_getElem?_getD, hlen] using hx)
  simpa using this

/-- **Planner soundness**: every copy segment the planner emits is a valid copy
set, so by `export_correct` the export decodes to the requested frames. -/
theorem plan_valid (s : Stream α) (r : DisplayRange) : PlanValid s (plan s r) := by
  intro ks hks
  simp only [plan, List.mem_map] at hks
  obtain ⟨⟨b, run⟩, _, hseg⟩ := hks
  simp only [mkSegment] at hseg
  split at hseg
  · split at hseg
    · rename_i _ hc
      injection hseg with hks; subst hks
      exact ⟨List.Pairwise.filter _ List.pairwise_lt_range,
        by intro k hk; simp at hk; exact hk.1, checkClosed_sound s _ hc⟩
    · cases hseg
  · cases hseg

theorem mkSegment_frames_mem (s : Stream α) (b : Bool) (run : List Nat)
    (hrun : ∀ x ∈ run, x < s.length) (i : Nat) :
    i ∈ (mkSegment s b run).frames ↔ i ∈ run := by
  simp only [mkSegment]
  split
  · split
    · simp only [Segment.frames, List.mem_filter, List.mem_range, List.contains_iff_mem]
      exact ⟨fun h => h.2, fun h => ⟨hrun i h, h⟩⟩
    · rfl
  · rfl

/-- **Coverage**: the plan contains exactly the wanted frames. -/
theorem plan_covers (s : Stream α) (r : DisplayRange) (i : Nat) :
    i ∈ ((plan s r).map Segment.frames).flatten ↔ wanted s r i = true := by
  have hdo : ∀ x, x ∈ displayOrder s r ↔ wanted s r x = true := by
    intro x
    simp only [displayOrder, List.mem_mergeSort, List.mem_filter, List.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨wanted_lt s r x h, h⟩⟩
  rw [← hdo, ← runs_flatten (fun i => (copyTable s r s.length).getD i false) (displayOrder s r)]
  simp only [plan, List.map_map, List.mem_flatten, List.mem_map, Function.comp]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hi⟩
    refine ⟨p.2, ⟨p, hp, rfl⟩, ?_⟩
    have hrun : ∀ x ∈ p.2, x < s.length := by
      intro x hx
      have : x ∈ displayOrder s r := by
        rw [← runs_flatten (fun i => (copyTable s r s.length).getD i false) (displayOrder s r)]
        exact List.mem_flatten.mpr ⟨p.2, List.mem_map.mpr ⟨p, hp, rfl⟩, hx⟩
      exact wanted_lt s r x ((hdo x).mp this)
    exact (mkSegment_frames_mem s p.1 p.2 hrun i).mp hi
  · rintro ⟨_, ⟨p, hp, rfl⟩, hi⟩
    refine ⟨_, ⟨p, hp, rfl⟩, ?_⟩
    have hrun : ∀ x ∈ p.2, x < s.length := by
      intro x hx
      have : x ∈ displayOrder s r := by
        rw [← runs_flatten (fun i => (copyTable s r s.length).getD i false) (displayOrder s r)]
        exact List.mem_flatten.mpr ⟨p.2, List.mem_map.mpr ⟨p, hp, rfl⟩, hx⟩
      exact wanted_lt s r x ((hdo x).mp this)
    exact (mkSegment_frames_mem s p.1 p.2 hrun i).mpr hi

/-- **Copies only copyable frames** (and by `copyable_maximal`, copyable is the
best possible). -/
theorem plan_copy_copyable (s : Stream α) (r : DisplayRange) (ks : List Nat)
    (hks : Segment.copy ks ∈ plan s r) : ∀ i ∈ ks, copyable s r i = true := by
  simp only [plan, List.mem_map] at hks
  obtain ⟨⟨b, run⟩, hp, hseg⟩ := hks
  have hconst := runs_const _ _ _ hp
  simp only [mkSegment] at hseg
  split at hseg
  · rename_i hb
    split at hseg
    · injection hseg with hks; subst hks
      intro i hi
      simp only [List.mem_filter, List.mem_range, List.contains_iff_mem] at hi
      have := hconst i hi.2
      simp only at this
      rw [← table_eq_copyable s r i hi.1, this, hb]
    · cases hseg
  · cases hseg

end VeriCut
