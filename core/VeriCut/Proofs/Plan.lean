import VeriCut.Proofs.Predict
import VeriCut.Proofs.Subframe

/-! The encoder's choices are well formed and keep the samples. -/

namespace VeriCut.Flac

theorem foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) (l : List α) (init : β) (h0 : P init)
    (step : ∀ b x, x ∈ l → P b → P (f b x)) : P (l.foldl f init) := by
  induction l generalizing init with
  | nil => exact h0
  | cons x l ih => exact ih _ (step _ _ (by simp) h0) (fun b y hy hb => step b y (by simp [hy]) hb)

theorem bestRice_lt (sum count : Nat) : (bestRice sum count).1 < 31 := by
  unfold bestRice
  refine foldl_inv (fun b : Nat × Nat => b.1 < 31) _ _ _ (by simp) ?_
  intro b k hk hb
  simp only [List.mem_range] at hk
  simp only
  split <;> simp_all

/-! ## Residual partitions -/

section Residual

variable (maxOrder n warmup : Nat) (r : Array Int)

theorem bestOrder_ok (hw : warmup ≤ n) :
    let p := (bestOrder maxOrder n warmup r).1
    p ≤ maxOrder ∧ n % 2 ^ p = 0 ∧ warmup ≤ n / 2 ^ p := by
  simp only [bestOrder]
  refine foldl_inv (fun b : Nat × Nat => b.1 ≤ maxOrder ∧ n % 2 ^ b.1 = 0 ∧ warmup ≤ n / 2 ^ b.1) _ _ _
    ⟨Nat.zero_le _, by simp [Nat.mod_one], by simpa using hw⟩ ?_
  intro b p hp hb
  simp only [List.mem_range] at hp
  split
  · rename_i hok
    simp only [orderFits, Bool.and_eq_true, decide_eq_true_eq, Nat.shiftRight_eq_div_pow] at hok
    split
    · exact ⟨by omega, hok.1, hok.2⟩
    · exact hb
  · exact hb

/-- Values of the first `m` of `2 ^ p` partitions of size `size`. -/
theorem partitions_values (size p : Nat) (g : Nat → Partition)
    (hg : ∀ j, (g j).values = r.extract (partBounds n warmup p j).1 (partBounds n warmup p j).2)
    (hsize : n >>> p = size) :
    ∀ m, 1 ≤ m → ((List.range m).map g).foldl (· ++ ·.values) #[] = r.extract 0 (m * size - warmup) := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, hg, partBounds, hsize]
    by_cases h0 : m = 0
    · subst h0; simp
    · rw [ih (by omega), if_neg h0, Array.extract_append_extract]
      congr 1
      exact Nat.max_eq_right (Nat.sub_le_sub_right (Nat.mul_le_mul_right _ (by omega)) _)

theorem planResidual_rice31 (q : Partition) (hq : q ∈ (planResidual maxOrder n warmup r).1.parts) :
    ∃ k, q.coding = .rice k ∧ k < 31 := by
  simp only [planResidual, Array.mem_map, Array.mem_range] at hq
  obtain ⟨j, -, rfl⟩ := hq
  exact ⟨_, rfl, bestRice_lt _ _⟩

theorem planResidual_rice (q : Partition) (hq : q ∈ (planResidual maxOrder n warmup r).1.parts) :
    ∃ k, q.coding = .rice k ∧ k < 2 ^ (planResidual maxOrder n warmup r).1.paramBits - 1 := by
  obtain ⟨k, hk, hlt⟩ := planResidual_rice31 maxOrder n warmup r q hq
  refine ⟨k, hk, ?_⟩
  unfold Residual.paramBits
  cases hwide : (planResidual maxOrder n warmup r).1.wide
  · have hnot := Array.any_eq_false'.1 (show (planResidual maxOrder n warmup r).1.parts.any
        (fun q => match q.coding with | .rice k => decide (15 ≤ k) | .raw _ => false) = false from hwide) q hq
    rw [hk] at hnot
    simp at hnot
    simp only [Bool.false_eq_true, if_false, Nat.reducePow]; omega
  · simp only [if_true, Nat.reducePow]; omega

theorem planResidual_spec (hmax : maxOrder ≤ 15) (hw : warmup ≤ n) (hr : r.size = n - warmup) :
    (planResidual maxOrder n warmup r).1.values = r ∧ (planResidual maxOrder n warmup r).1.WF n warmup := by
  obtain ⟨hp, hdiv, hwp⟩ := bestOrder_ok maxOrder n warmup r hw
  generalize hbo : bestOrder maxOrder n warmup r = bo at hp hdiv hwp
  have hres : (planResidual maxOrder n warmup r).1.parts.toList =
      (List.range (2 ^ bo.1)).map (planPartition r n warmup bo.1) := by
    simp [planResidual, hbo]
  have horder : (planResidual maxOrder n warmup r).1.order = bo.1 := by simp [planResidual, hbo]
  have hsize : n >>> bo.1 = n / 2 ^ bo.1 := Nat.shiftRight_eq_div_pow _ _
  have hn : n = 2 ^ bo.1 * (n / 2 ^ bo.1) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hdiv)).symm
  have hpos : 1 ≤ 2 ^ bo.1 := Nat.one_le_two_pow
  refine ⟨?_, ?_⟩
  · simp only [Residual.values, ← Array.foldl_toList, hres]
    rw [partitions_values n warmup r (n / 2 ^ bo.1) bo.1 _ (fun j => rfl) hsize _ hpos, ← hn]
    exact Array.extract_eq_self_of_le (by omega)
  · have hsplit : List.range (2 ^ bo.1) = 0 :: (List.range (2 ^ bo.1 - 1)).map Nat.succ := by
      rw [← List.range_succ_eq_map, Nat.sub_add_cancel hpos]
    have hmem : ∀ q ∈ (List.range (2 ^ bo.1)).map (planPartition r n warmup bo.1),
        q ∈ (planResidual maxOrder n warmup r).1.parts := by
      intro q hq; rw [← Array.mem_toList_iff, hres]; exact hq
    refine ⟨by omega, horder ▸ hdiv, horder ▸ hwp, planPartition r n warmup bo.1 0,
      (List.range (2 ^ bo.1 - 1)).map (planPartition r n warmup bo.1 ∘ Nat.succ), ?_, ?_, ?_, ?_⟩
    · rw [hres, hsplit]; simp
    · refine ⟨planResidual_rice _ _ _ _ _ (hmem _ (by rw [hsplit]; simp)), ?_⟩
      simp [planPartition, partBounds, horder, hsize, Array.size_extract, hr]
      have : n / 2 ^ bo.1 ≤ n := Nat.div_le_self _ _
      omega
    · intro q hq
      simp only [List.mem_map, List.mem_range, Function.comp] at hq
      obtain ⟨j, hj, rfl⟩ := hq
      refine ⟨planResidual_rice _ _ _ _ _ (hmem _ (by rw [hsplit]; simp; exact Or.inr ⟨j, hj, rfl⟩)), ?_⟩
      simp only [planPartition, partBounds, horder, hsize, Array.size_extract, hr, Nat.succ_ne_zero, if_false]
      have : (j + 1 + 1) * (n / 2 ^ bo.1) ≤ 2 ^ bo.1 * (n / 2 ^ bo.1) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [← hn] at this
      have hwp' := horder ▸ hwp
      clear hres hmem hsplit hn
      generalize n / 2 ^ bo.1 = S at *
      simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at *
      omega
    · simp [horder]

end Residual

end VeriCut.Flac

namespace VeriCut.Flac

theorem mem_extract {s : Array Int} {v : Int} {i j : Nat} (h : v ∈ s.extract i j) : v ∈ s := by
  obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.1 h
  exact Array.getElem_mem _

theorem inRange_div (bits w : Nat) (v : Int) (hv : InRange bits v) (hw : w ≤ bits - 1) (hd : v % 2 ^ w = 0) :
    InRange (bits - w) (v / 2 ^ w) := by
  obtain ⟨lo, hi⟩ := hv
  have hpos : (0 : Int) < 2 ^ w := Int.pow_pos (by decide)
  have he : v / 2 ^ w * 2 ^ w = v := Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hd)
  have hp : (2 : Int) ^ (bits - 1) = 2 ^ (bits - w - 1) * 2 ^ w := by
    rw [← Int.pow_add]; congr 1; omega
  constructor
  · apply Int.le_of_mul_le_mul_right _ hpos
    rw [he, Int.neg_mul, ← hp]; exact lo
  · apply Int.lt_of_mul_lt_mul_right _ (Int.le_of_lt hpos)
    rw [he, ← hp]; exact hi

theorem planBody_spec (st : Settings) (bits : Nat) (s : Array Int)
    (hr : ∀ v ∈ s, InRange bits v) :
    (planBody st bits s).1.samples s.size = s ∧ (planBody st bits s).1.WF bits s.size := by
  have verbatim : (Body.verbatim s).samples s.size = s ∧ (Body.verbatim s).WF bits s.size :=
    ⟨rfl, rfl, hr⟩
  have hk4 : bestFixedOrder st.maxFixedOrder s.size s ≤ 4 := by
    unfold bestFixedOrder
    exact foldl_inv (· ≤ 4) _ _ _ (by omega) (fun b k hk hb => by
      simp only [List.mem_range] at hk; split <;> omega)
  dsimp only [planBody]
  generalize bestFixedOrder st.maxFixedOrder s.size s = k at hk4
  split
  · rename_i hkn
    have hsize : (s.extract 0 k).size = k := by simp [Array.size_extract]; omega
    obtain ⟨hvals, hwf⟩ := planResidual_spec (min st.maxPartitionOrder 15) s.size k
      (residualOf (fixedCoefs k) 0 s k) (by omega) hkn (size_residualOf _ _ _ _)
    split
    · constructor
      · simp only [Body.samples, hsize, hvals]
        exact restore_residualOf _ _ _ _ (by rw [size_fixedCoefs k hk4]; exact Nat.le_refl _) hkn
      · simp only [Body.WF, hsize]
        exact ⟨hk4, hkn, fun v hv => hr v (mem_extract hv), hwf⟩
    · exact verbatim
  · exact verbatim

theorem planSubframe_spec (st : Settings) (bits : Nat) (s : Array Int) (hb : 0 < bits) (hn : 0 < s.size)
    (hr : ∀ v ∈ s, InRange bits v) :
    (planSubframe st bits s).1.samples s.size = s ∧ (planSubframe st bits s).1.WF bits s.size := by
  dsimp only [planSubframe]
  split
  · rename_i hall
    rw [Array.all_eq_true] at hall
    refine ⟨?_, ⟨hb, hr _ (by rw [getElem!_pos s 0 hn]; exact Array.getElem_mem hn)⟩⟩
    · simp only [Subframe.samples, if_true, Body.samples]
      apply Array.ext (by simp)
      intro i h1 h2
      have := hall i h2
      simp only [beq_iff_eq] at this
      simp [this]
  · generalize hw : min (trailingZeros _) (bits - 1) = w
    split
    · rename_i hdiv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hdiv
      obtain ⟨h0, hdiv⟩ := hdiv
      rw [Array.all_eq_true] at hdiv
      · simp only [h0, if_false]
        have hdiv' : ∀ v ∈ s, v % 2 ^ w = 0 := by
          intro v hv
          obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hv
          simpa using hdiv i hi
        obtain ⟨hs, hwf⟩ := planBody_spec st (bits - w) (s.map (· / 2 ^ w)) (by
          intro v hv
          obtain ⟨u, hu, rfl⟩ := Array.mem_map.1 hv
          exact inRange_div bits w u (hr u hu) (by omega) (hdiv' u hu))
        rw [Array.size_map] at hs hwf
        refine ⟨?_, show w < bits by omega, hwf⟩
        simp only [Subframe.samples, h0, if_false, hs, Array.map_map]
        apply Array.ext (by simp)
        intro i h1 h2
        simp only [Array.getElem_map, Function.comp]
        exact Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero (hdiv' _ (Array.getElem_mem h2)))
    · simp only [if_true, Nat.sub_zero]
      obtain ⟨hs, hwf⟩ := planBody_spec st bits s hr
      exact ⟨by simpa [Subframe.samples] using hs, hb, hwf⟩

end VeriCut.Flac
