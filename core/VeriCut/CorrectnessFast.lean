import VeriCut.Correctness
import VeriCut.Flac.Fast.Export
import VeriCut.Proofs.Fast.RoundTrip
import VeriCut.Proofs.Fast.Decode

/-!
The theorems for what the CLI runs. `Correctness.lean` states the round trip for the spec's
`encode` and `decode`, written for review rather than speed; the CLI runs `decodeFast` and
`encodeFast` (`Flac/Fast/`). This file ties those to the same spec `decode`:

* `decodeFast` *is* `decode`, on every input;
* whatever `encodeFast` writes, the spec's `decode` reads back as the input.

No hypotheses beyond the ones `Correctness.lean` already has.
-/

namespace VeriCut

/-- The fast decoder computes the spec's `decode`, for every input. -/
theorem decodeFast_eq (d : ByteArray) : Flac.Fast.decodeFast d = Flac.decode d :=
  Flac.Fast.decodeFast_eq d

/-- `flac_roundTrip` for the fast encoder (any settings, including LPC). -/
theorem flac_roundTrip_fast (st : Flac.Fast.Settings) (x : Pcm) (valid : x.Valid) :
    Flac.decode (Flac.Fast.encodeFast st x) = .ok x :=
  Flac.Fast.decode_encodeFast st x valid

/-- `export_correct` for the fast encoder, same hypotheses. -/
theorem export_correct_fast (st : Flac.Fast.Settings) (format : Format) (clips : List Clip)
    (valid : ∀ c ∈ clips, c.Valid format) (nonempty : clips ≠ [])
    (short : (clips.map fun c => c.stop - c.start).sum < 2 ^ 36) :
    Flac.decode (exportClipsFast st format clips) = .ok (splice format clips) :=
  flac_roundTrip_fast st _ (splice_valid format clips valid nonempty short)

/-- And so what the CLI decodes from its own export is the spliced clips. -/
example (st : Flac.Fast.Settings) (format : Format) (clips : List Clip)
    (valid : ∀ c ∈ clips, c.Valid format) (nonempty : clips ≠ [])
    (short : (clips.map fun c => c.stop - c.start).sum < 2 ^ 36) :
    Flac.Fast.decodeFast (exportClipsFast st format clips) = .ok (splice format clips) := by
  rw [decodeFast_eq]; exact export_correct_fast st format clips valid nonempty short

/-- info: 'VeriCut.decodeFast_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decodeFast_eq

/-- info: 'VeriCut.flac_roundTrip_fast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms flac_roundTrip_fast

/-- info: 'VeriCut.export_correct_fast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms export_correct_fast

end VeriCut
