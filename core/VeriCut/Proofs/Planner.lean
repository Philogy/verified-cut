import VeriCut.Spec.Planner
import VeriCut.Proofs.Decode

namespace VeriCut

variable {α : Type}

theorem copyable_eq (s : Stream α) (r : DisplayRange) (i : Nat) :
    copyable s r i = if h : i < s.length then
      (wanted s r i && s[i].refs.all fun x => decide (x < i) && copyable s r x) else false := by
  rw [copyable]
  split
  · congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor
    · intro h x hx
      have := h ⟨x, hx⟩ (List.mem_attach _ _)
      by_cases hxi : x < i <;> simp_all
    · intro h ⟨x, hx⟩ _
      have := h x hx
      by_cases hxi : x < i <;> simp_all
  · rfl

theorem wanted_lt (s : Stream α) (r : DisplayRange) (i : Nat) (h : wanted s r i = true) :
    i < s.length := by
  unfold wanted at h; split at h
  · assumption
  · cases h

theorem copyable_lt (s : Stream α) (r : DisplayRange) (i : Nat) (h : copyable s r i = true) :
    i < s.length := by
  rw [copyable_eq] at h; split at h
  · assumption
  · cases h

theorem copyable_wanted (s : Stream α) (r : DisplayRange) (i : Nat)
    (h : copyable s r i = true) : wanted s r i = true := by
  rw [copyable_eq] at h; split at h
  · simp at h; exact h.1
  · cases h

theorem copyable_ref (s : Stream α) (r : DisplayRange) (i x : Nat) (hi : i < s.length)
    (h : copyable s r i = true) (hx : x ∈ s[i].refs) : copyable s r x = true := by
  rw [copyable_eq] at h; simp [hi] at h; exact (h.2 x hx).2

/-- The frames the reference planner copies. -/
def copySetOf (s : Stream α) (r : DisplayRange) : List Nat :=
  (List.range s.length).filter (copyable s r)

/-- **Soundness**: the copyable frames form a valid copy set. -/
theorem copySet_copyable (s : Stream α) (r : DisplayRange) :
    CopySet s (copySetOf s r) where
  sorted := List.Pairwise.filter _ List.pairwise_lt_range
  bound := by intro k hk; simp [copySetOf] at hk; exact hk.1
  closed := by
    intro k hk hlen x hx
    simp [copySetOf] at hk ⊢
    have hc := copyable_ref s r k x hlen hk.2 hx
    exact ⟨wanted_lt s r x (copyable_wanted s r x hc), hc⟩

/-- **Maximality**: any dependency-closed set of wanted frames is contained in
the copyable frames. So no correct copy plan re-encodes fewer frames. -/
theorem copyable_maximal (s : Stream α) (r : DisplayRange) (hwf : s.WellFormed)
    (T : Nat → Prop)
    (hT : ∀ i, T i → wanted s r i = true ∧ ∀ (h : i < s.length), ∀ x ∈ s[i].refs, T x) :
    ∀ i, T i → copyable s r i = true := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
  intro hi
  obtain ⟨hw, hrefs⟩ := hT i hi
  have hlt := wanted_lt s r i hw
  rw [copyable_eq]
  simp only [hlt, dite_true, hw, Bool.true_and, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  intro x hx
  have hxi : x < i := hwf i hlt x hx
  exact ⟨hxi, ih x hxi (hrefs hlt x hx)⟩

end VeriCut
