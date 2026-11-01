import VeriCut.Proofs.Predict
import VeriCut.Flac.Fast.Predict

namespace VeriCut.Flac.Fast


theorem toInt_toInt64 (x : Int) (h : x.natAbs < 2 ^ 62) : x.toInt64.toInt = x := by
  show (Int64.ofInt x).toInt = x
  rw [Int64.toInt_ofInt]
  apply Int.bmod_eq_of_le <;> simp [Int64.size] <;> omega

theorem bmod64 (x : Int) (h : x.natAbs < 2 ^ 62) : x.bmod (2 ^ 64) = x := by
  apply Int.bmod_eq_of_le <;> omega

theorem natAbs_mul_lt (a b : Int) (ha : a.natAbs < 2 ^ 20) (hb : b.natAbs < 2 ^ 36) :
    (a * b).natAbs < 2 ^ 56 := by
  rw [Int.natAbs_mul]
  calc a.natAbs * b.natAbs < 2 ^ 20 * 2 ^ 36 := Nat.mul_lt_mul_of_lt_of_lt ha hb
    _ = 2 ^ 56 := by rw [← Nat.pow_add]

theorem dot64_toInt (coefs : Array Int) (s : Array Int) (i : Nat)
    (hc : ∀ j : Nat, Int.natAbs coefs[j]! < 2 ^ 20) (hs : ∀ k : Nat, Int.natAbs s[k]! < 2 ^ 36) (h32 : coefs.size ≤ 32) :
    ∀ j, j ≤ coefs.size → ∀ acc : Int64, acc.toInt.natAbs ≤ (coefs.size - j) * 2 ^ 56 →
      (dot64 (coefs.map Int.toInt64) s i j acc).toInt = dot coefs s i j acc.toInt := by
  intro j
  induction j with
  | zero => intro _ acc _; rfl
  | succ j ih =>
    intro hj acc hacc
    simp only [dot64, dot]
    have hcj : (coefs.map Int.toInt64)[j]! = (coefs[j]!).toInt64 := by
      rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by omega)]; simp
    rw [hcj]
    have h1 : ((coefs[j]!).toInt64).toInt = coefs[j]! := toInt_toInt64 _ (by have := hc j; omega)
    have h2 : ((s[i - 1 - j]!).toInt64).toInt = s[i - 1 - j]! := toInt_toInt64 _ (by have := hs (i - 1 - j); omega)
    have hp := natAbs_mul_lt _ _ (hc j) (hs (i - 1 - j))
    have hprod : ((coefs[j]!).toInt64 * (s[i - 1 - j]!).toInt64).toInt = coefs[j]! * s[i - 1 - j]! := by
      rw [Int64.toInt_mul, h1, h2]; exact bmod64 _ (by omega)
    have hsum : (acc + (coefs[j]!).toInt64 * (s[i - 1 - j]!).toInt64).toInt =
        acc.toInt + coefs[j]! * s[i - 1 - j]! := by
      rw [Int64.toInt_add, hprod]
      apply bmod64
      have : (coefs.size - (j + 1)) * 2 ^ 56 + 2 ^ 56 ≤ 32 * 2 ^ 56 := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      have := Int.natAbs_add_le acc.toInt (coefs[j]! * s[i - 1 - j]!)
      omega
    rw [ih (by omega) _ (by
      rw [hsum]
      have := Int.natAbs_add_le acc.toInt (coefs[j]! * s[i - 1 - j]!)
      have e : (coefs.size - (j + 1)) * 2 ^ 56 + 2 ^ 56 = (coefs.size - j) * 2 ^ 56 := by
        rw [← Nat.succ_mul]; congr 1; omega
      omega), hsum]

theorem getElem!_bound (a : Array Int) (L : Nat) (h : a.all (·.natAbs < L) = true) (hL : 0 < L) :
    ∀ j : Nat, Int.natAbs a[j]! < L := by
  intro j
  by_cases hj : j < a.size
  · rw [getElem!_pos a j hj]
    have := (Array.all_eq_true.1 h) j hj
    simpa using this
  · rw [getElem!_neg a j hj]; simpa using hL

theorem smallCoefs_spec (coefs : Array Int) (h : smallCoefs coefs = true) :
    coefs.size ≤ 32 ∧ ∀ j : Nat, Int.natAbs coefs[j]! < 2 ^ 20 := by
  simp only [smallCoefs, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, getElem!_bound coefs _ h.2 (by decide)⟩

/-- The `Int64` prediction is the `Int` one, for small coefficients and samples. -/
theorem predict64 (coefs s : Array Int) (shift : Nat) (hc : smallCoefs coefs = true)
    (hs : ∀ k : Nat, Int.natAbs s[k]! < 2 ^ 36) (i : Nat) :
    (dot64 (coefs.map Int.toInt64) s i (coefs.map Int.toInt64).size 0).toInt >>> shift = predict coefs shift s i := by
  obtain ⟨h32, hc'⟩ := smallCoefs_spec coefs hc
  rw [Array.size_map, dot64_toInt coefs s i hc' hs h32 coefs.size (Nat.le_refl _) 0 (by simp),
    Int.shiftRight_eq_div_pow]
  unfold predict
  push_cast
  rfl

theorem residualFast_eq (coefs : Array Int) (shift : Nat) (s : Array Int) (order : Nat) :
    residualFast coefs shift s order = residualOf coefs shift s order := by
  unfold residualFast
  split
  · rename_i hg
    simp only [Bool.and_eq_true] at hg
    have hs' := getElem!_bound s _ hg.2 (by decide)
    simp only [sampleLimit] at hs'
    apply Array.ext (by simp [residualOf])
    intro i h1 h2
    simp only [Array.getElem_ofFn, residualOf]
    rw [predict64 coefs s shift hg.1 hs']
  · rfl

theorem restoreFast_eq (coefs : Array Int) (shift : Nat) (warmup residual : Array Int) :
    restoreFast coefs shift warmup residual = restore coefs shift warmup residual := by
  unfold restoreFast
  split
  · rename_i hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hc, hw⟩ := hg
    let g := fun (s : Array Int) (r : Int) => s.push (r + predict coefs shift s s.size)
    -- while `ok`, the fast state is the slow fold so far, and every sample is in bounds
    have inv := Array.foldl_induction (as := residual) (init := (warmup, true))
      (f := restoreStep (coefs.map Int.toInt64) shift)
      (motive := fun i st => st.2 = true →
        st.1 = (residual.extract 0 i).foldl g warmup ∧ ∀ k : Nat, Int.natAbs st.1[k]! < 2 ^ 36)
      (fun _ => ⟨by simp, by have := getElem!_bound warmup _ hw (by decide); simpa [sampleLimit] using this⟩)
      (by
        intro i st ih hok
        obtain ⟨acc, ok⟩ := st
        cases ok with
        | false => simp [restoreStep] at hok
        | true =>
          obtain ⟨e, hb⟩ := ih rfl
          simp only [restoreStep, if_true] at hok ⊢
          simp only [sampleLimit] at hok
          refine ⟨?_, ?_⟩
          · rw [Array.extract_succ_right (by omega) (by simp), Array.foldl_push, ← e, predict64 coefs acc shift hc hb]
            rfl
          · intro k
            by_cases hk : k < acc.size
            · rw [getElem!_pos _ k (by simp; omega), Array.getElem_push_lt hk, ← getElem!_pos acc k hk]
              exact hb k
            · by_cases hk' : k = acc.size
              · subst hk'
                rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]
                simpa using hok
              · rw [getElem!_neg _ _ (by simp; omega)]; simp)
    simp only []
    split
    · rename_i hok
      rw [(inv hok).1, Array.extract_eq_self_of_le (Nat.le_refl _)]
      rfl
    · rfl
  · rfl


end VeriCut.Flac.Fast
