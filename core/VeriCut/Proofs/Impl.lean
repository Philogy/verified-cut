import VeriCut.Impl.Planner
import VeriCut.Proofs.Planner

namespace VeriCut

variable {α : Type}

theorem wantedA_toArray (s : Stream α) (r : DisplayRange) (i : Nat) :
    wantedA s.toArray r i = wanted s r i := by
  simp only [wantedA, wanted, List.size_toArray, List.getElem_toArray]

theorem copyTable_size (a : Array (Packet α)) (r : DisplayRange) (k : Nat) :
    (copyTable a r k).size = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [copyTable, ih]

theorem copyTable_getD (s : Stream α) (r : DisplayRange) :
    ∀ k i, i < k → (copyTable s.toArray r k).getD i false = copyable s r i := by
  intro k
  induction k with
  | zero => intro i h; omega
  | succ k ih =>
    intro i hi
    have hsz := copyTable_size s.toArray r k
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
      simp only [List.size_toArray, List.getElem_toArray, wantedA_toArray]
      split
      · congr 1
        apply Bool.eq_iff_iff.mpr
        simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · intro hh x hx; have := hh x hx; exact ⟨this.1, by rw [← ih x this.1]; exact this.2⟩
        · intro hh x hx; have := hh x hx; exact ⟨this.1, by rw [ih x this.1]; exact this.2⟩
      · rfl

/-- The table agrees with the reference definition. -/
theorem table_eq_copyable (s : Stream α) (r : DisplayRange) (i : Nat) (hi : i < s.length) :
    (copyTable s.toArray r s.toArray.size).getD i false = copyable s r i :=
  copyTable_getD s r _ i (by simpa using hi)

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

theorem memTable_getD_aux (n : Nat) (run : List Nat) (m : Array Bool) (hm : m.size = n) (i : Nat) :
    (run.foldl (fun m i => m.set! i true) m).getD i false =
      (m.getD i false || (decide (i < n) && run.contains i)) := by
  induction run generalizing m with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [hm])]
    simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
      List.contains_cons, hm]
    by_cases hx : x = i
    · subst hx; by_cases h : x < n
      · simp [h]
      · simp [h, Array.getElem?_eq_none (show m.size ≤ x by omega)]
    · have : (i == x) = false := by simp; omega
      simp [hx, this]

theorem memTable_getD (n : Nat) (run : List Nat) (i : Nat) :
    (memTable n run).getD i false = (decide (i < n) && run.contains i) := by
  rw [memTable, memTable_getD_aux n run _ (by simp)]
  by_cases h : i < n <;> simp [Array.getD_eq_getD_getElem?, h]

theorem checkClosed_sound (s : Stream α) (mem : Array Bool) (ks : List Nat)
    (hmem : ∀ x, mem.getD x false = true ↔ x ∈ ks) (h : checkClosed s.toArray mem ks = true) :
    DepClosed s ks := by
  intro k hk hlen x hx
  have := h
  simp only [checkClosed, List.all_eq_true, List.size_toArray, List.getElem_toArray] at this
  have hk' := this k hk
  simp only [hlen, dite_true, List.all_eq_true] at hk'
  exact (hmem x).mp (hk' x hx)

/-- The frames `mkSegment` copies for a run: those of `run` below `n`. -/
theorem mem_filter_memTable (n : Nat) (run : List Nat) (i : Nat) :
    i ∈ (List.range n).filter (fun i => (memTable n run).getD i false) ↔ i < n ∧ i ∈ run := by
  simp only [List.mem_filter, List.mem_range, memTable_getD, Bool.and_eq_true, decide_eq_true_eq,
    List.contains_iff_mem]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

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
      refine ⟨List.Pairwise.filter _ List.pairwise_lt_range,
        by intro k hk; simp at hk; simpa using hk.1, checkClosed_sound s _ _ ?_ hc⟩
      intro x
      rw [mem_filter_memTable, memTable_getD]
      simp
    · cases hseg
  · cases hseg

theorem mkSegment_frames_mem (s : Stream α) (b : Bool) (run : List Nat)
    (hrun : ∀ x ∈ run, x < s.length) (i : Nat) :
    i ∈ (mkSegment s.toArray b run).frames ↔ i ∈ run := by
  simp only [mkSegment]
  split
  · split
    · simp only [Segment.frames, mem_filter_memTable, List.size_toArray]
      exact ⟨fun h => h.2, fun h => ⟨hrun i h, h⟩⟩
    · rfl
  · rfl

/-- **Coverage**: the plan contains exactly the wanted frames. -/
theorem plan_covers (s : Stream α) (r : DisplayRange) (i : Nat) :
    i ∈ ((plan s r).map Segment.frames).flatten ↔ wanted s r i = true := by
  have hdo : ∀ x, x ∈ displayOrder s.toArray r ↔ wanted s r x = true := by
    intro x
    simp only [displayOrder, List.mem_map, List.mem_mergeSort, List.mem_filter,
      List.mem_finRange, true_and, wantedA_toArray]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro h; exact ⟨⟨x, by simpa using wanted_lt s r x h⟩, h, rfl⟩
  rw [← hdo, ← runs_flatten (fun i => (copyTable s.toArray r s.toArray.size).getD i false) (displayOrder s.toArray r)]
  simp only [plan, List.map_map, List.mem_flatten, List.mem_map, Function.comp]
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hi⟩
    refine ⟨p.2, ⟨p, hp, rfl⟩, ?_⟩
    have hrun : ∀ x ∈ p.2, x < s.length := by
      intro x hx
      have : x ∈ displayOrder s.toArray r := by
        rw [← runs_flatten (fun i => (copyTable s.toArray r s.toArray.size).getD i false) (displayOrder s.toArray r)]
        exact List.mem_flatten.mpr ⟨p.2, List.mem_map.mpr ⟨p, hp, rfl⟩, hx⟩
      exact wanted_lt s r x ((hdo x).mp this)
    exact (mkSegment_frames_mem s p.1 p.2 hrun i).mp hi
  · rintro ⟨_, ⟨p, hp, rfl⟩, hi⟩
    refine ⟨_, ⟨p, hp, rfl⟩, ?_⟩
    have hrun : ∀ x ∈ p.2, x < s.length := by
      intro x hx
      have : x ∈ displayOrder s.toArray r := by
        rw [← runs_flatten (fun i => (copyTable s.toArray r s.toArray.size).getD i false) (displayOrder s.toArray r)]
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
      simp only [mem_filter_memTable, List.size_toArray] at hi
      have := hconst i hi.2
      simp only at this
      rw [← table_eq_copyable s r i hi.1, this, hb]
    · cases hseg
  · cases hseg

end VeriCut
