import VeriCut.Flac.Encode

/-! Prediction is undone by `restore`: the decoder's loop recomputes the encoder's predictions. -/

namespace VeriCut.Flac

theorem dot_congr (coefs a b : Array Int) (i : Nat) :
    ∀ m acc, (∀ j < m, a[i - 1 - j]! = b[i - 1 - j]!) → dot coefs a i m acc = dot coefs b i m acc
  | 0, _, _ => rfl
  | m + 1, acc, h => by
    simp only [dot]
    rw [h m (by omega)]
    exact dot_congr coefs a b i m _ (fun j hj => h j (by omega))

theorem getElem!_extract (s : Array Int) (i t : Nat) (ht : t < i) (hi : i ≤ s.size) :
    (s.extract 0 i)[t]! = s[t]! := by
  rw [getElem!_pos _ _ (by simp [Array.size_extract]; omega), getElem!_pos _ _ (by omega)]
  simp [Array.getElem_extract]

theorem predict_extract (coefs : Array Int) (shift : Nat) (s : Array Int) (i : Nat)
    (hc : coefs.size ≤ i) (hi : i ≤ s.size) :
    predict coefs shift (s.extract 0 i) i = predict coefs shift s i := by
  unfold predict
  rw [dot_congr coefs _ s i coefs.size 0 (fun j hj => getElem!_extract s i _ (by omega) hi)]

theorem size_residualOf (coefs : Array Int) (shift : Nat) (s : Array Int) (k : Nat) :
    (residualOf coefs shift s k).size = s.size - k := by simp [residualOf]

theorem getElem_residualOf (coefs : Array Int) (shift : Nat) (s : Array Int) (k i : Nat)
    (h : i < (residualOf coefs shift s k).size) :
    (residualOf coefs shift s k)[i] = s[k + i]! - predict coefs shift s (k + i) := by
  simp [residualOf]

theorem restore_residualOf (coefs : Array Int) (shift : Nat) (s : Array Int) (k : Nat)
    (hc : coefs.size ≤ k) (hk : k ≤ s.size) :
    restore coefs shift (s.extract 0 k) (residualOf coefs shift s k) = s := by
  unfold restore
  have := Array.foldl_induction (as := residualOf coefs shift s k) (init := s.extract 0 k)
    (motive := fun i acc => acc = s.extract 0 (k + i)) (by simp)
    (f := fun acc r => acc.push (r + predict coefs shift acc acc.size)) (by
      intro i b hb
      have hi : i.1 < s.size - k := (size_residualOf coefs shift s k) ▸ i.2
      subst hb
      have hsize : (s.extract 0 (k + i.1)).size = k + i.1 := by simp [Array.size_extract]; omega
      rw [hsize, predict_extract coefs shift s _ (by omega) (by omega),
        show k + (i.1 + 1) = (k + i.1) + 1 by omega, Array.extract_succ_right (by omega) (by omega)]
      congr 1
      rw [Fin.getElem_fin, getElem_residualOf, getElem!_pos s _ (by omega)]
      omega)
  rw [this, size_residualOf,
    show k + (s.size - k) = s.size by omega, Array.extract_eq_self_of_le (Nat.le_refl _)]

theorem size_fixedCoefs (k : Nat) (hk : k ≤ 4) : (fixedCoefs k).size = k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with h | h | h | h | h <;> subst h <;> rfl

/-! ## The `Int64` residual -/

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
    have hsum : (acc + (coefs[j]!).toInt64 * (s[i - 1 - j]!).toInt64).toInt = acc.toInt + coefs[j]! * s[i - 1 - j]! := by
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

theorem residual_eq (coefs : Array Int) (shift : Nat) (s : Array Int) (order : Nat) :
    residual coefs shift s order = residualOf coefs shift s order := by
  unfold residual
  simp only []
  split
  · rename_i hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨⟨h32, hc⟩, hs⟩ := hg
    have hc' := getElem!_bound coefs _ hc (by decide)
    have hs' := getElem!_bound s _ hs (by decide)
    simp only [sampleLimit] at hs'
    apply Array.ext (by simp [residualOf])
    intro i h1 h2
    simp only [Array.getElem_ofFn, residualOf, predict]
    rw [Array.size_map, dot64_toInt coefs s _ hc' hs' h32 coefs.size (Nat.le_refl _) 0 (by simp)]
    rfl
  · rfl

end VeriCut.Flac
