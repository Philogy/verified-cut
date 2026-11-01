import VeriCut.Impl.Planner
import VeriCut.Impl.Export

/-!
# Spec: exporting a timeline

Trusted surface, the definitions `exportTimeline_correct` (`Correctness.lean`)
is stated with. A timeline is a list of cuts, each a source stream and the
display range to keep. The planner (`plan`) decides which kept frames are
copied and which re-encoded; `exportTimeline` renders the plans, asking the
encoder for each re-encode job.

The pictures a cut should decode to are read off its plan (`Cut.target`), so
`plan` is part of this surface: `plan_covers` shows it lists exactly the
wanted frames, `plan_copy_copyable` and `copyable_maximal` that it copies as
many as any correct plan can.
-/

namespace VeriCut

/-- One clip of the timeline: keep the frames of `source` whose display
position lies in `range`. -/
structure Cut (α : Type) where
  source : Stream α
  range  : DisplayRange

/-- The clips to export, in output order. -/
abbrev Timeline (α : Type) := List (Cut α)

variable {α Pic : Type}

/-- The planner's plan for a cut. -/
def Cut.plan (cut : Cut α) : List Segment := VeriCut.plan cut.source cut.range

/-- The pictures a cut should decode to: the source pictures of its planned
frames, in plan order. -/
def Cut.target (c : Codec α Pic) (cut : Cut α) : List Pic := VeriCut.target c cut.source cut.plan

/-- The pictures the whole timeline should decode to. -/
def Timeline.target (c : Codec α Pic) (timeline : Timeline α) : List Pic :=
  (timeline.map (Cut.target c)).flatten

/-- Every source stream is well-formed. -/
def Timeline.WellFormed (timeline : Timeline α) : Prop :=
  ∀ cut ∈ timeline, cut.source.WellFormed

/-- `encode` meets `JobContract` on every job the timeline's plans ask for:
each job `j` whose frames are an `encode` segment of clip `j.clip`'s plan. -/
def EncoderContract (c : Codec α Pic) (approx : Pic → Pic → Prop) (timeline : Timeline α)
    (encode : Job → Stream α) : Prop :=
  ∀ (j : Job) (cut : Cut α), timeline[j.clip]? = some cut → .encode j.frames ∈ cut.plan →
    JobContract c approx cut.source j.frames (encode j)

/-- The stream `vericut export` writes for `timeline`, with `encode` as the
encoder: `exportTimeline` run on the planner's plans, all rendered segments
concatenated. -/
def Timeline.exportWith (encode : Job → Stream α) (timeline : Timeline α) : Stream α :=
  let clips := timeline.map fun cut => (cut.source, cut.plan)
  concatStreams ((exportTimeline (m := PureEncode α) clips).run encode).flatten

end VeriCut
