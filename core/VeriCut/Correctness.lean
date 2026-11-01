import VeriCut.Spec.Timeline
import VeriCut.Proofs.Run
import VeriCut.Proofs.Audio

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

/-! ## Audio

`exportAudioClips` is what `vericut export` runs for the audio track. Its
statements are in `Spec/Audio.lean`, proofs in `Proofs/Audio.lean`. -/

section Audio
variable {S : Type}

/-- For any audio codec `c` with one packet of overlap and `n` samples per
packet (AAC-LC: 1024), the copied packets, decoded and presented through the
written edit list, play exactly each clip's cut: its source samples, padded
with `silence` where the source has none. No sample is approximate. -/
theorem exportAudio_exact (c : AudioCodec α S) (n : Nat) (frameLength : c.FrameLength n)
    (silence : S) (sampleRate rate : Nat) (clips : List (AudioClip α)) :
    let (packets, edits) := exportAudioClips n sampleRate rate clips
    present silence (decodeAudio c packets) edits =
      ((audioCuts n sampleRate rate true 0 clips).map (·.target c silence)).flatten :=
  exportAudioClips_present frameLength silence clips

/-- Every clip's audio starts within half a sample of its video (`rate` video
ticks and `sampleRate` audio samples per second), so rounding never adds up.
For `i = clips.length`: the audio is as long as the video, to half a sample. -/
theorem exportAudio_synced (n sampleRate rate : Nat) (hrate : 0 < rate)
    (clips : List (AudioClip α)) (i : Nat) (hi : i ≤ clips.length) :
    2 * ((audioStart (audioCuts n sampleRate rate true 0 clips) i : Int) * rate -
      videoStart clips i * sampleRate).natAbs ≤ rate :=
  exportAudioClips_synced hrate clips i hi

/-- Within a clip, the source samples played are those from `srcStart` on: the
cut's sample `j` is source sample `srcStart + j` (or silence). -/
theorem exportAudio_aligned (n sampleRate rate : Nat) (clip : AudioClip α) (first : Bool) (t0 : Nat)
    (plays : 0 < (clip.cut n sampleRate rate first t0).len) :
    ((clip.cut n sampleRate rate first t0).start : Int) - (clip.cut n sampleRate rate first t0).lead =
      clip.srcStart :=
  clip.cut_start first t0 plays

/-- info: 'VeriCut.exportAudio_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exportAudio_exact
/-- info: 'VeriCut.exportAudio_synced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exportAudio_synced
/-- info: 'VeriCut.exportAudio_aligned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exportAudio_aligned

end Audio

end VeriCut
