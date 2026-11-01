import VeriCut.Spec.Export
import VeriCut.Proofs.Decode

namespace VeriCut

variable {α Pic : Type} {c : Codec α Pic} {approx : Pic → Pic → Prop}

theorem AllRel.append {β γ} {R : β → γ → Prop} {a b : List β} {x y : List γ}
    (h1 : AllRel R a x) (h2 : AllRel R b y) : AllRel R (a ++ b) (x ++ y) := by
  induction h1 with
  | nil => simpa using h2
  | cons hr _ ih => exact AllRel.cons hr ih

theorem AllRel.refl {β} {R : β → β → Prop} (hR : ∀ x, R x x) : ∀ l, AllRel R l l
  | [] => .nil
  | x :: xs => .cons (hR x) (AllRel.refl hR xs)

theorem AllRel.eq_of {β} {a b : List β} (h : AllRel (· = ·) a b) : a = b := by
  induction h with
  | nil => rfl
  | cons hr _ ih => subst hr; rw [ih]

/-- Copying a valid copy set yields a well-formed stream. -/
theorem extract_wellFormed (s : Stream α) (ks : List Nat)
    (hwf : s.WellFormed) (hks : CopySet s ks) : (extract s ks).WellFormed := by
  intro j hj r hr
  have hj' : j < ks.length := by simpa [length_extract s ks hks.bound] using hj
  have hk : ks[j] < s.length := hks.bound _ (List.getElem_mem hj')
  have hget : (extract s ks)[j] = { s[ks[j]] with refs := s[ks[j]].refs.map (ks.idxOf ·) } :=
    getElem_extract s ks hks.bound j hj hj' hk
  rw [hget] at hr
  simp only [List.mem_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  have hrk : r0 < ks[j] := hwf _ hk r0 hr0
  have hmem : r0 ∈ ks := hks.closed _ (List.getElem_mem hj') hk r0 hr0
  have hm : ks.idxOf r0 < ks.length := List.idxOf_lt_length_of_mem hmem
  have hkm : ks[ks.idxOf r0] = r0 := List.getElem_idxOf hm
  have hp := List.pairwise_iff_getElem.mp hks.sorted
  rcases Nat.lt_trichotomy (ks.idxOf r0) j with h | h | h
  · exact h
  · exfalso; subst h; omega
  · exfalso; have := hp j _ hj' hm h; omega

theorem render_wellFormed (s : Stream α) (enc : Encoder α Pic c approx)
    (hwf : s.WellFormed) (seg : Segment) (hseg : ∀ ks, seg = .copy ks → CopySet s ks) :
    (seg.render s enc).WellFormed := by
  cases seg with
  | encode ks => exact enc.wellFormed _
  | copy ks => exact extract_wellFormed s ks hwf (hseg ks rfl)

/-- Each segment decodes to its target pictures: exactly for copies,
`approx`-closely for re-encodes. -/
theorem render_correct (s : Stream α) (enc : Encoder α Pic c approx)
    (hwf : s.WellFormed) (hR : ∀ p, approx p p) (seg : Segment)
    (hseg : ∀ ks, seg = .copy ks → CopySet s ks) :
    AllRel approx (decode c (seg.render s enc)) (seg.frames.map (picture c s)) := by
  cases seg with
  | encode ks => exact enc.faithful _
  | copy ks =>
    simp only [Segment.render, Segment.frames]
    rw [decode_extract c s ks hwf (hseg ks rfl)]
    exact AllRel.refl hR _

/-- **Smart-cut correctness.** For any codec and any encoder meeting its
contract, a valid plan's export decodes to the requested source pictures,
up to `approx` on re-encoded frames. -/
theorem export_correct (s : Stream α) (enc : Encoder α Pic c approx)
    (plan : List Segment) (hwf : s.WellFormed) (hplan : PlanValid s plan)
    (hR : ∀ p, approx p p) :
    DecodesTo c approx (exportPlan s enc plan) (target c s plan) := by
  have hseg : ∀ seg ∈ plan, ∀ ks, seg = .copy ks → CopySet s ks := by
    intro seg hmem ks h; subst h; exact hplan ks hmem
  unfold DecodesTo exportPlan target
  rw [decode_concatStreams c _ (by
    intro x hx
    obtain ⟨seg, hmem, rfl⟩ := List.mem_map.mp hx
    exact render_wellFormed s enc hwf seg (hseg seg hmem))]
  induction plan with
  | nil => exact .nil
  | cons seg rest ih =>
    simp only [List.map_cons, List.flatten_cons]
    exact AllRel.append (render_correct s enc hwf hR seg (hseg seg (by simp)))
      (ih (fun ks h => hplan ks (by simp [h])) (fun s' h => hseg s' (by simp [h])))

/-- **Lossless when nothing is re-encoded.** A copy-only valid plan decodes to
exactly the requested pictures. -/
theorem export_exact (s : Stream α) (enc : Encoder α Pic c approx)
    (plan : List Segment) (hwf : s.WellFormed) (hplan : PlanValid s plan)
    (hcopy : ∀ seg ∈ plan, seg.isCopy = true) :
    decode c (exportPlan s enc plan) = target c s plan := by
  have hseg : ∀ seg ∈ plan, ∀ ks, seg = .copy ks → CopySet s ks := by
    intro seg hmem ks h; subst h; exact hplan ks hmem
  unfold exportPlan target
  rw [decode_concatStreams c _ (by
    intro x hx
    obtain ⟨seg, hmem, rfl⟩ := List.mem_map.mp hx
    exact render_wellFormed s enc hwf seg (hseg seg hmem))]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro seg hmem
  cases seg with
  | encode ks => exact absurd (hcopy _ hmem) (by simp [Segment.isCopy])
  | copy ks =>
    simp only [Segment.frames]
    exact decode_extract c s ks hwf (hplan ks hmem)

end VeriCut
