import SmartCut.Spec.Planner
import SmartCut.Proofs.Decode

namespace SmartCut

variable {α : Type} [Inhabited α]

theorem copyable_eq (s : Stream α) (r : DisplayRange) (i : Nat) :
    copyable s r i = (wanted s r i &&
      (s.getD i default).refs.all fun x => decide (x < i) && copyable s r x) := by
  rw [copyable]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro h x hx
    have := h ⟨x, hx⟩ (List.mem_attach _ _)
    by_cases hxi : x < i <;> simp_all
  · intro h ⟨x, hx⟩ _
    have := h x hx
    by_cases hxi : x < i <;> simp_all

theorem wanted_lt (s : Stream α) (r : DisplayRange) (i : Nat) (h : wanted s r i = true) :
    i < s.length := by
  simp [wanted] at h; exact h.1.1

theorem copyable_wanted (s : Stream α) (r : DisplayRange) (i : Nat)
    (h : copyable s r i = true) : wanted s r i = true := by
  rw [copyable_eq] at h; simp at h; exact h.1

theorem copyable_ref (s : Stream α) (r : DisplayRange) (i x : Nat)
    (h : copyable s r i = true) (hx : x ∈ (s.getD i default).refs) : copyable s r x = true := by
  rw [copyable_eq] at h; simp at h; exact (h.2 x hx).2

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
    have hx' : x ∈ (s.getD k default).refs := by
      simpa [List.getD_eq_getElem?_getD, hlen] using hx
    have hc := copyable_ref s r k x hk.2 hx'
    exact ⟨wanted_lt s r x (copyable_wanted s r x hc), hc⟩

/-- **Maximality**: any dependency-closed set of wanted frames is contained in
the copyable frames. So no correct copy plan re-encodes fewer frames. -/
theorem copyable_maximal (s : Stream α) (r : DisplayRange) (hwf : s.WellFormed)
    (T : Nat → Prop)
    (hT : ∀ i, T i → wanted s r i = true ∧ ∀ x ∈ (s.getD i default).refs, T x) :
    ∀ i, T i → copyable s r i = true := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
  intro hi
  obtain ⟨hw, hrefs⟩ := hT i hi
  have hlt := wanted_lt s r i hw
  rw [copyable_eq]
  simp only [hw, Bool.true_and, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  intro x hx
  have hx' : x ∈ s[i].refs := by simpa [List.getD_eq_getElem?_getD, hlt] using hx
  have hxi : x < i := hwf i hlt x hx'
  exact ⟨hxi, ih x hxi (hrefs x hx)⟩

end SmartCut
