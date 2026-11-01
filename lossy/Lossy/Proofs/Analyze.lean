import Lossy.Proofs.Sub
import Lossy.Proofs.Round

namespace Lossy.Flac

theorem restore_residuals (o : Nat) (w : Window) (xs : List Int) :
    restore o w (residuals o w xs) = xs := by
  induction xs generalizing w with
  | nil => rfl
  | cons x xs ih => simp [residuals, restore, ih]

theorem length_residuals (o : Nat) (w : Window) (xs : List Int) :
    (residuals o w xs).length = xs.length := by
  induction xs generalizing w with
  | nil => rfl
  | cons x xs ih => simp [residuals, ih]

/-- Picking the cheaper of two keeps any property both have. -/
theorem foldl_pick {P : α → Prop} {better : α → α → Prop} [∀ a b, Decidable (better a b)]
    {init : α} {l : List α}
    (h₀ : P init) (h : ∀ a ∈ l, P a) :
    P (l.foldl (fun s s' => if better s s' then s' else s) init) := by
  induction l generalizing init with
  | nil => exact h₀
  | cons a l ih =>
    simp only [List.foldl_cons]
    exact ih (by split <;> simp_all) (fun b hb => h b (by simp [hb]))

theorem bestK_lt (res : List Int) : bestK res < 15 := by
  unfold bestK
  exact foldl_pick (P := (· < 15)) (better := fun k k' => riceCost k' res < riceCost k res)
    (init := 0) (by decide) (fun k hk => List.mem_range.mp hk)

theorem tz_le : ∀ (cap n : Nat), wasted.tz cap n ≤ cap
  | 0, _ => Nat.le_refl 0
  | cap + 1, n => by
    simp only [wasted.tz]; split
    · have := tz_le cap (n / 2); omega
    · omega

theorem wasted_spec (cap : Nat) (xs : List Int) :
    wasted cap xs ≤ cap ∧ ∀ v ∈ xs, (2 : Int) ^ wasted cap xs ∣ v := by
  unfold wasted
  simp only
  split
  · rename_i h
    refine ⟨tz_le _ _, fun v hv => Int.dvd_of_emod_eq_zero ?_⟩
    have := List.all_eq_true.mp h v hv
    simpa using this
  · exact ⟨Nat.zero_le _, fun v _ => by simp⟩

theorem fits_div {bps w : Nat} {v : Int} (hw : w < bps) (hd : (2 : Int) ^ w ∣ v)
    (hv : -2 ^ (bps - 1) ≤ v ∧ v < 2 ^ (bps - 1)) : Fits (bps - w) (v / 2 ^ w) := by
  obtain ⟨y, rfl⟩ := hd
  have hp : (0 : Int) < 2 ^ w := two_pow_pos w
  rw [Int.mul_ediv_cancel_left _ (by omega)]
  have e : (2 : Int) ^ (bps - 1) = 2 ^ (bps - w - 1) * 2 ^ w := by
    rw [← Int.pow_add]; congr 1; omega
  rw [e] at hv
  have hy := two_pow_pos (bps - w - 1)
  constructor
  · refine Classical.byContradiction fun c => ?_
    have : y * 2 ^ w < -2 ^ (bps - w - 1) * 2 ^ w :=
      Int.mul_lt_mul_of_pos_right (by omega) hp
    rw [Int.mul_comm y] at this; rw [Int.neg_mul] at this; omega
  · refine Classical.byContradiction fun c => ?_
    have : 2 ^ (bps - w - 1) * 2 ^ w ≤ y * 2 ^ w :=
      Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    rw [Int.mul_comm y] at this; omega

/-- What `analyze` promises: the subframe reads back and stands for `xs`. -/
def Faithful (bps : Nat) (xs : List Int) (ws : Nat × Sub) : Prop :=
  ws.1 < bps ∧ ws.2.Ok (bps - ws.1) xs.length ∧ (ws.2.samples xs.length).map (· * 2 ^ ws.1) = xs

theorem fixedSub_ok {o width : Nat} {ys : List Int} (ho : o < min 5 ys.length)
    (hys : ∀ y ∈ ys, Fits width y) :
    (fixedSub o ys).Ok width ys.length ∧ (fixedSub o ys).samples ys.length = ys := by
  simp only [fixedSub, Sub.Ok, Sub.samples, restore_residuals, List.take_append_drop,
    length_residuals, List.length_drop, List.length_take, and_true]
  refine ⟨by omega, by omega, fun v hv => hys v (List.mem_of_mem_take hv), bestK_lt _⟩

theorem analyze_ok {bps : Nat} {xs : List Int} (hb : 1 ≤ bps)
    (hxs : ∀ v ∈ xs, -2 ^ (bps - 1) ≤ v ∧ v < 2 ^ (bps - 1)) : Faithful bps xs (analyze bps xs) := by
  obtain ⟨hcap, hdvd⟩ := wasted_spec (bps - 1) xs
  have hw : wasted (bps - 1) xs < bps := by omega
  unfold analyze
  simp only
  generalize wasted (bps - 1) xs = w at *
  have hback : (xs.map (· / 2 ^ w)).map (· * 2 ^ w) = xs := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id xs]
    exact List.map_congr_left fun v hv => Int.ediv_mul_cancel (hdvd v hv)
  have hfits : ∀ y ∈ xs.map (· / 2 ^ w), Fits (bps - w) y := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
    exact fits_div hw (hdvd v hv) (hxs v hv)
  have hlen : (xs.map (· / 2 ^ w)).length = xs.length := List.length_map ..
  generalize xs.map (· / 2 ^ w) = ys at *
  subst hback
  -- every candidate is faithful
  have good : ∀ s : Sub, s.Ok (bps - w) ys.length → s.samples ys.length = ys →
      Faithful bps (ys.map (· * 2 ^ w)) (w, s) := by
    intro s h1 h2
    exact ⟨hw, by simpa using h1, by simp [h2]⟩
  match ys, hfits with
  | [], _ => exact good (.verbatim []) ⟨rfl, by simp⟩ rfl
  | y :: ys', hfits =>
    simp only
    split
    · rename_i hall
      refine good (.const y) (hfits y (by simp)) ?_
      simp only [Sub.samples]
      refine (List.eq_replicate_iff.mpr ⟨rfl, fun b hb => ?_⟩).symm
      simpa using List.all_eq_true.mp hall b hb
    · refine foldl_pick (P := fun s => Faithful bps ((y :: ys').map (· * 2 ^ w)) (w, s)) ?_ ?_
      · exact good (.verbatim (y :: ys')) ⟨rfl, hfits⟩ rfl
      · intro s hs
        obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hs
        have := fixedSub_ok (List.mem_range.mp ho) hfits
        exact good _ this.1 this.2

end Lossy.Flac
