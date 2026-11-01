import Lossy.Spec.Quantize

namespace Lossy

/-- A multiple of `2^s` that fits in `bits` bits. -/
def OnGrid (bits s : Nat) (g : Int) : Prop := (2 : Int) ^ s ∣ g ∧ lo bits ≤ g ∧ g ≤ hi bits

theorem two_pow_pos (s : Nat) : (0 : Int) < 2 ^ s := by
  have : (0 : Nat) < 2 ^ s := Nat.two_pow_pos s
  exact_mod_cast this

theorem two_pow_le {a b : Nat} (h : a ≤ b) : (2 : Int) ^ a ≤ 2 ^ b := by
  have : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) h
  exact_mod_cast this

private theorem mul_step {D j k : Int} (hD : 0 < D) (h : D * j < D * k) : D * j + D ≤ D * k := by
  have hjk : j < k := Int.lt_of_mul_lt_mul_left h (by omega)
  have := Int.mul_le_mul_of_nonneg_left (show j + 1 ≤ k by omega) (Int.le_of_lt hD)
  rw [Int.mul_add, Int.mul_one] at this; exact this

/-- Either `2^s` divides `2^(bits-1)`, or it is at least `2^bits`. -/
private theorem pow_cases (bits s : Nat) (hb : 1 ≤ bits) :
    (∃ m : Int, (2 : Int) ^ (bits - 1) = 2 ^ s * m ∧ 1 ≤ m) ∨
      2 * (2 : Int) ^ (bits - 1) ≤ 2 ^ s := by
  by_cases h : s ≤ bits - 1
  · left
    refine ⟨2 ^ (bits - 1 - s), by rw [← Int.pow_add]; congr 1; omega, ?_⟩
    exact two_pow_pos _
  · right
    rw [← Int.pow_succ']
    exact two_pow_le (by omega)

private theorem round_core (D H v : Int) (hD : 0 < D) (hlo : -H ≤ v) (hhi : v ≤ H - 1)
    (hcases : (∃ m : Int, H = D * m ∧ 1 ≤ m) ∨ 2 * H ≤ D) :
    let r := if (v + D / 2) / D * D ≤ H - 1 then (v + D / 2) / D * D else (v + D / 2) / D * D - D
    (D ∣ r ∧ -H ≤ r ∧ r ≤ H - 1) ∧
      (∀ g, D ∣ g ∧ -H ≤ g ∧ g ≤ H - 1 → (v - r).natAbs ≤ (v - g).natAbs) ∧
      v - r < D ∧ r - v < D := by
  intro r
  have h1 := Int.mul_ediv_self_le (x := v + D / 2) (k := D) (by omega)
  have h2 := Int.lt_mul_ediv_self_add (x := v + D / 2) (k := D) hD
  simp only [r]
  generalize (v + D / 2) / D = k at *
  rw [Int.mul_comm k D]
  have hdvd : D ∣ D * k := ⟨k, rfl⟩
  have pt : ∀ {a b : Int}, D ∣ a → D ∣ b → a < b → a + D ≤ b := by
    rintro a b ⟨j, rfl⟩ ⟨j', rfl⟩ h; exact mul_step hD h
  -- a grid point in range: `-H` if `D ∣ H`, else `0`
  have lo_ok : -H ≤ D * k := by
    rcases hcases with ⟨m, hm, _⟩ | hc
    · refine Classical.byContradiction fun c => ?_
      have := pt (b := -H) hdvd ⟨-m, by rw [hm, Int.mul_neg]⟩ (by omega); omega
    · refine Classical.byContradiction fun c => ?_
      have := pt (b := 0) hdvd ⟨0, by simp⟩ (by omega); omega
  split
  · refine ⟨⟨hdvd, lo_ok, by omega⟩, fun g ⟨hg, glo, ghi⟩ => ?_, by omega, by omega⟩
    rcases Int.lt_trichotomy g (D * k) with c | c | c
    · have := pt hg hdvd c; omega
    · subst c; exact Nat.le_refl _
    · have := pt hdvd hg c; omega
  · have hDk : D ∣ D * k - D := Int.dvd_sub hdvd (Int.dvd_refl D)
    refine ⟨⟨hDk, ?_, by omega⟩, fun g ⟨hg, glo, ghi⟩ => ?_, by omega, by omega⟩
    · rcases hcases with ⟨m, hm, hm1⟩ | hc
      · have : D ≤ H := by
          rw [hm]; have := Int.mul_le_mul_of_nonneg_left hm1 (Int.le_of_lt hD); omega
        omega
      · have := pt (a := 0) ⟨0, by simp⟩ hdvd (by omega); omega
    · have := pt hg hdvd (by omega); omega

/-- What `roundTo` computes: a point of the grid, a nearest one, and less
than one grid step away. -/
theorem roundTo_spec {bits s : Nat} {v : Int} (hb : 1 ≤ bits) (hlo : lo bits ≤ v) (hhi : v ≤ hi bits) :
    OnGrid bits s (roundTo bits s v) ∧
      (∀ g, OnGrid bits s g → (v - roundTo bits s v).natAbs ≤ (v - g).natAbs) ∧
      (v - roundTo bits s v).natAbs < 2 ^ s := by
  have h := round_core (2 ^ s) (2 ^ (bits - 1)) v (two_pow_pos s) hlo hhi (pow_cases bits s hb)
  have hcast : (((2 ^ s : Nat) : Int)) = 2 ^ s := by simp
  refine ⟨h.1, h.2.1, ?_⟩
  have := h.2.2
  simp only [roundTo, lo, hi] at *
  omega

theorem roundTo_zero {bits : Nat} {v : Int} (hhi : v ≤ hi bits) : roundTo bits 0 v = v := by
  simp [roundTo, hhi]

end Lossy
