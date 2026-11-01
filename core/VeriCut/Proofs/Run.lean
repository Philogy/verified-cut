import VeriCut.Impl.Export
import VeriCut.Impl.Planner
import VeriCut.Proofs.Export
import VeriCut.Proofs.Impl

/-!
# Proof: the exporter the CLI runs is correct

`exportTimeline` is the code `vericut export` executes (in `IO`, with ffmpeg
as the encoder). Here it runs with the encoder replaced by an arbitrary
function `f`; `exportTimeline_correct` holds for every `f` meeting the
per-job encoder contract.
-/

namespace VeriCut

variable {α Pic : Type} [Inhabited α] {c : Codec α Pic} {approx : Pic → Pic → Prop}

/-- What one segment renders to when the encoder is the function `f`. -/
def Segment.renderWith (clip : Nat) (s : Stream α) (f : Job → Stream α) : Segment → Stream α
  | .copy ks => extract s ks
  | .encode ks => f ⟨clip, ks⟩

/-- `exportFrom` with the encoder replaced by `f`, as a plain function. -/
def renderFrom (f : Job → Stream α) : Nat → List (Stream α × List Segment) → List (List (Stream α))
  | _, [] => []
  | i, (s, segs) :: rest => segs.map (Segment.renderWith i s f) :: renderFrom f (i + 1) rest

theorem extractA_toArray (s : Stream α) (ks : List Nat) : extractA s.toArray ks = extract s ks := by
  simp only [extractA, extract, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]

omit [Inhabited α] in
theorem mapM_run {β γ : Type} (g : β → PureEncode α γ) (f : Job → Stream α) (xs : List β) :
    (xs.mapM g).run f = xs.map fun x => (g x).run f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, List.map_cons]
    simp only [ReaderT.run, bind, ReaderT.bind, pure, ReaderT.pure] at ih ⊢
    rw [← ih]

theorem exportFrom_run (f : Job → Stream α) (i : Nat) (clips : List (Stream α × List Segment)) :
    (exportFrom (m := PureEncode α) i clips).run f = renderFrom f i clips := by
  induction clips generalizing i with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨s, segs⟩ := x
    have hseg : (fun seg => (renderSegment (m := PureEncode α) i s seg).run f) =
        Segment.renderWith i s f := by
      funext seg; cases seg
      · exact extractA_toArray s _
      · rfl
    have h1 := mapM_run (renderSegment (m := PureEncode α) i s) f segs
    rw [hseg] at h1
    simp only [exportFrom, renderFrom]
    rw [← h1, ← ih (i + 1)]
    rfl

/-- The hypotheses for clip number `i`: its stream is well-formed, its plan
valid, and `f` meets the contract on each of its encode jobs. -/
def ClipOK (c : Codec α Pic) (approx : Pic → Pic → Prop) (f : Job → Stream α) (i : Nat)
    (x : Stream α × List Segment) : Prop :=
  x.1.WellFormed ∧ PlanValid x.1 x.2 ∧
    ∀ ks, Segment.encode ks ∈ x.2 → JobContract c approx x.1 ks (f ⟨i, ks⟩)

theorem renderWith_ok (f : Job → Stream α) (i : Nat) (s : Stream α) (segs : List Segment)
    (h : ClipOK c approx f i (s, segs)) (hR : ∀ p, approx p p) (seg : Segment) (hm : seg ∈ segs) :
    (seg.renderWith i s f).WellFormed ∧
      AllRel approx (decode c (seg.renderWith i s f)) (seg.frames.map (picture c s)) := by
  obtain ⟨hwf, hplan, henc⟩ := h
  cases seg with
  | copy ks =>
    refine ⟨extract_wellFormed s ks hwf (hplan ks hm), ?_⟩
    simp only [Segment.renderWith, Segment.frames]
    rw [decode_extract c s ks hwf (hplan ks hm)]
    exact AllRel.refl hR _
  | encode ks => exact henc ks hm

theorem renderFrom_ok (f : Job → Stream α) (hR : ∀ p, approx p p) :
    ∀ (i : Nat) (clips : List (Stream α × List Segment)),
    (∀ j (h : j < clips.length), ClipOK c approx f (i + j) clips[j]) →
    (∀ x ∈ (renderFrom f i clips).flatten, x.WellFormed) ∧
      AllRel approx ((renderFrom f i clips).flatten.map (decode c)).flatten
        (clips.map fun x => target c x.1 x.2).flatten
  | _, [], _ => ⟨by simp [renderFrom], by simpa [renderFrom] using AllRel.nil⟩
  | i, (s, segs) :: rest, h => by
    have h0 : ClipOK c approx f i (s, segs) := h 0 (by simp)
    have ih := renderFrom_ok f hR (i + 1) rest fun j hj => by
      have := h (j + 1) (by simp; omega)
      simpa [show i + (j + 1) = i + 1 + j by omega] using this
    have hseg := fun seg hm => renderWith_ok f i s segs h0 hR seg hm
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [renderFrom, List.flatten_cons, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨seg, hm, rfl⟩ | hx
      · exact (hseg seg hm).1
      · exact ih.1 x hx
    · simp only [renderFrom, List.flatten_cons, List.map_append, List.flatten_append, List.map_cons,
        List.flatten_cons, target]
      refine AllRel.append ?_ ih.2
      clear ih h
      induction segs with
      | nil => exact .nil
      | cons seg segs ihs =>
        simp only [List.map_cons, List.flatten_cons]
        exact AllRel.append (hseg seg (by simp)).2
          (ihs ⟨h0.1, fun ks hk => h0.2.1 ks (by simp [hk]),
                 fun ks hk => h0.2.2 ks (by simp [hk])⟩
               (fun seg' hm => hseg seg' (by simp [hm])))

/-- **End-to-end correctness of the export the CLI runs.** For any codec, any
encoder function `f` meeting the per-job contract on the jobs the plans ask
for, and any clips with their cut ranges: running `exportTimeline` on the
planner's plans, with `f` as the encoder, yields a stream that decodes to the
requested source pictures of every clip, in timeline order (exactly for copied
frames, `approx`-close for re-encoded ones). -/
theorem exportTimeline_correct (cuts : List (Stream α × DisplayRange)) (f : Job → Stream α)
    (hwf : ∀ x ∈ cuts, x.1.WellFormed) (hR : ∀ p, approx p p)
    (henc : ∀ i (h : i < cuts.length) ks, Segment.encode ks ∈ plan cuts[i].1 cuts[i].2 →
      JobContract c approx cuts[i].1 ks (f ⟨i, ks⟩)) :
    AllRel approx
      (decode c (concatStreams
        ((exportTimeline (m := PureEncode α) (cuts.map fun x => (x.1, plan x.1 x.2))).run f).flatten))
      (cuts.map fun x => target c x.1 (plan x.1 x.2)).flatten := by
  have hok := renderFrom_ok (c := c) f hR 0 (cuts.map fun x => (x.1, plan x.1 x.2))
    fun j hj => by
      simp only [List.getElem_map, Nat.zero_add]
      have hj' : j < cuts.length := by simpa using hj
      exact ⟨hwf _ (List.getElem_mem hj'), plan_valid _ _, henc j hj'⟩
  rw [exportTimeline, exportFrom_run, decode_concatStreams c _ hok.1]
  simpa [List.map_map, Function.comp_def] using hok.2

end VeriCut
