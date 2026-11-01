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

end VeriCut.Flac
