import Lossy.Proofs.Round
import Lossy.Spec.Error

namespace Lossy

/-- Every sample with its position in its channel. -/
def indexed (x : Pcm) : List (Int × Nat) := (x.chans.map fun c => c.toList.zipIdx).flatten

/-- The error of sample `v` at position `i` after `quantize q x`. -/
def sampleErr (q : Nat) (x : Pcm) (vi : Int × Nat) : Nat :=
  (vi.1 - roundTo x.bits (shift q x (vi.2 / blockSize)) vi.1).natAbs

theorem diffs_quantize (q : Nat) (x : Pcm) :
    diffs x (quantize q x) = (indexed x).map (sampleErr q x) := by
  simp only [diffs, quantize, indexed, List.zipWith_map_right, List.zipWith_self, List.map_flatten,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  simp only [Function.comp, Array.toList_mapIdx, List.mapIdx_eq_zipIdx_map]
  conv => lhs; arg 2; rw [← List.zipIdx_map_fst 0 c.toList]
  rw [List.zipWith_map, List.zipWith_self]
  rfl

theorem mem_indexed {x : Pcm} {vi : Int × Nat} (h : vi ∈ indexed x) : ∃ c ∈ x.chans, vi.1 ∈ c := by
  simp only [indexed, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨c, hc, rfl⟩, hv⟩ := h
  obtain ⟨_, hi, e⟩ := List.mem_zipIdx hv
  refine ⟨c, hc, ?_⟩
  rw [e, ← Array.mem_toList_iff]
  exact List.getElem_mem _

theorem foldl_max_mono {l : List α} {f g : α → Nat} (h : ∀ a ∈ l, f a ≤ g a) {m m' : Nat}
    (hm : m ≤ m') : (l.map f).foldl max m ≤ (l.map g).foldl max m' := by
  induction l generalizing m m' with
  | nil => simpa
  | cons a l ih =>
    simp only [List.map_cons, List.foldl_cons]
    exact ih (fun b hb => h b (by simp [hb])) (by have := h a (by simp); omega)

theorem foldl_max_lt {l : List α} {f : α → Nat} {B m : Nat} (h : ∀ a ∈ l, f a < B) (hm : m < B) :
    (l.map f).foldl max m < B := by
  induction l generalizing m with
  | nil => simpa
  | cons a l ih =>
    simp only [List.map_cons, List.foldl_cons]
    exact ih (fun b hb => h b (by simp [hb])) (by have := h a (by simp); omega)

theorem sum_sq_mono {l : List α} {f g : α → Nat} (h : ∀ a ∈ l, f a ≤ g a) :
    ((l.map f).map (· ^ 2)).sum ≤ ((l.map g).map (· ^ 2)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := Nat.pow_le_pow_left (h a (by simp)) 2
    have := ih (fun b hb => h b (by simp [hb]))
    omega

theorem sampleErr_mono {q q' : Nat} {x : Pcm} (hx : x.Valid) (hq : q ≤ q') {vi : Int × Nat}
    (h : vi ∈ indexed x) : sampleErr q x vi ≤ sampleErr q' x vi := by
  obtain ⟨c, hc, hv⟩ := mem_indexed h
  have ⟨hlo, hhi⟩ := hx.range c hc vi.1 hv
  have hb : 1 ≤ x.bits := by have := hx.bits; omega
  have hs : shift q x (vi.2 / blockSize) ≤ shift q' x (vi.2 / blockSize) := by
    simp only [shift]; omega
  have fine := (roundTo_spec (s := shift q x (vi.2 / blockSize)) hb hlo hhi).2.1
  have ⟨⟨hd, glo, ghi⟩, _⟩ := roundTo_spec (s := shift q' x (vi.2 / blockSize)) hb hlo hhi
  refine fine _ ⟨?_, glo, ghi⟩
  exact Int.dvd_trans ⟨2 ^ (shift q' x (vi.2 / blockSize) - shift q x (vi.2 / blockSize)),
    by rw [← Int.pow_add]; congr 1; omega⟩ hd

theorem sampleErr_lt {q : Nat} {x : Pcm} (hx : x.Valid) {vi : Int × Nat} (h : vi ∈ indexed x) :
    sampleErr q x vi < 2 ^ q := by
  obtain ⟨c, hc, hv⟩ := mem_indexed h
  have ⟨hlo, hhi⟩ := hx.range c hc vi.1 hv
  have := (roundTo_spec (s := shift q x (vi.2 / blockSize)) (by have := hx.bits; omega) hlo hhi).2.2
  exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) (by simp [shift]))

theorem quantize_mono_maxErr {q q' : Nat} {x : Pcm} (hx : x.Valid) (hq : q ≤ q') :
    maxErr x (quantize q x) ≤ maxErr x (quantize q' x) := by
  simp only [maxErr, diffs_quantize]
  exact foldl_max_mono (fun _ h => sampleErr_mono hx hq h) (Nat.le_refl 0)

theorem quantize_mono_sqErr {q q' : Nat} {x : Pcm} (hx : x.Valid) (hq : q ≤ q') :
    sqErr x (quantize q x) ≤ sqErr x (quantize q' x) := by
  simp only [sqErr, diffs_quantize]
  exact sum_sq_mono (fun _ h => sampleErr_mono hx hq h)

theorem quantize_maxErr_lt {q : Nat} {x : Pcm} (hx : x.Valid) : maxErr x (quantize q x) < 2 ^ q := by
  simp only [maxErr, diffs_quantize]
  exact foldl_max_lt (fun _ h => sampleErr_lt hx h) (Nat.two_pow_pos q)

theorem quantize_zero {x : Pcm} (hx : x.Valid) : quantize 0 x = x := by
  cases x with
  | mk rate bits chans =>
  simp only [quantize, Pcm.mk.injEq, true_and]
  conv => rhs; rw [← List.map_id chans]
  apply List.map_congr_left
  intro c hc
  apply Array.ext (by simp)
  intro i h₁ h₂
  simp only [Array.getElem_mapIdx, id, shift, Nat.zero_sub]
  exact roundTo_zero (hx.range c hc _ (Array.getElem_mem _)).2

end Lossy
