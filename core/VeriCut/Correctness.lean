import VeriCut.Spec.Timeline
import VeriCut.Proofs.Run

/-!
The correctness theorem of the export the CLI runs. Its statement lives
here, its definitions in `Spec/`, the proof in `Proofs/Run.lean`.

`approx` is how close a re-encoded picture must be to its source. It is
assumed reflexive because copied frames decode exactly, and the conclusion
uses one relation for both.
-/

namespace VeriCut

variable {α Pic : Type}

/-- For any codec `c`, closeness `approx`, timeline and encoder `encode`:
if every source stream is well-formed (`Timeline.WellFormed`) and `encode`
meets the per-job contract on the jobs the plans ask for (`EncoderContract`),
the exported stream decodes to the timeline's target pictures, in timeline
order: exactly for copied frames, `approx`-close for re-encoded ones. -/
theorem exportTimeline_correct (c : Codec α Pic) (approx : Pic → Pic → Prop)
    (timeline : Timeline α) (encode : Job → Stream α)
    (approxRefl : ∀ p, approx p p)
    (wellFormed : timeline.WellFormed)
    (contract : EncoderContract c approx timeline encode) :
    DecodesTo c approx (timeline.exportWith encode) (timeline.target c) :=
  exportWith_correct c approx timeline encode approxRefl wellFormed contract

/-- info: 'VeriCut.exportTimeline_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exportTimeline_correct

end VeriCut
