import VeriCut.Proofs.Splice

/-!
The correctness theorems. Their statements live here; the definitions they
mention are in `Spec/Audio.lean` (PCM, clips, splicing) and `Flac/` (the
codec), the proofs in `Proofs/`.

The round trip says the codec loses nothing, whatever the encoder settings.
It does not say the bytes are standard FLAC: that is tested against libFLAC
(`tests/test_vericut.py`).
-/

namespace VeriCut

/-- Any PCM audio FLAC can carry (`Pcm.Valid`), encoded with any settings `st`
and decoded again, comes back unchanged. -/
theorem flac_roundTrip (st : Flac.Settings) (x : Pcm) (valid : x.Valid) :
    Flac.decode (Flac.encode st x) = .ok x :=
  Flac.decode_encode st x valid

/-- Clips of valid sources in one `format` (`Clip.Valid`: in bounds, `start ≤ stop`),
at least one and fewer than `2 ^ 36` samples in all: the exported file decodes to
exactly the clips' samples, one after another (`splice`). -/
theorem export_correct (st : Flac.Settings) (format : Format) (clips : List Clip)
    (valid : ∀ c ∈ clips, c.Valid format) (nonempty : clips ≠ [])
    (short : (clips.map fun c => c.stop - c.start).sum < 2 ^ 36) :
    Flac.decode (exportClips st format clips) = .ok (splice format clips) :=
  flac_roundTrip st _ (splice_valid format clips valid nonempty short)

/-- info: 'VeriCut.flac_roundTrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms flac_roundTrip

/-- info: 'VeriCut.export_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms export_correct

end VeriCut
