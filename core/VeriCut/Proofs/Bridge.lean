import VeriCut.MP4.Parse
import VeriCut.Proofs.Decode

/-!
# Proof: the bridge stream is well-formed

`toStream t` satisfies `Stream.WellFormed` whenever the first sample is a sync
sample, which the CLI checks before planning (`planClip`). This discharges the
`hwf` hypothesis of `exportTimeline_correct` for real tracks.
-/

namespace VeriCut.MP4

theorem toStream_wellFormed (t : VideoTrack) (h0 : ∀ h : 0 < t.samples.size, t.samples[0].sync = true) :
    (toStream t).WellFormed := by
  intro i hi r hr
  simp only [toStream, List.length_map, List.length_range] at hi
  simp only [toStream, List.getElem_map, List.getElem_range] at hr
  split at hr
  · simp at hr
  · rename_i hs
    simp only [List.mem_singleton] at hr
    subst hr
    cases i with
    | zero => exact absurd (by simpa [getElem!_pos t.samples 0 hi] using h0 hi) hs
    | succ k => omega

end VeriCut.MP4
