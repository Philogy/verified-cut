import VeriCut.Flac.Decode
import VeriCut.Flac.Fast.Export
import VeriCut.Flac.Fast.Decode
import VeriCut.Impl.Packed

/-!
The statements `lake comparator` checks (`comparator.json`), proofs left out. Each must be
proved with the same statement in `VeriCut.CorrectnessFast` (which imports `Correctness`),
using only `propext`, `Classical.choice` and `Quot.sound`. Imports only definitions, no proofs.
-/

namespace VeriCut

theorem flac_roundTrip (st : Flac.Settings) (x : Pcm) (valid : x.Valid) :
    Flac.decode (Flac.encode st x) = .ok x := sorry

theorem export_correct (st : Flac.Settings) (format : Format) (clips : List Clip)
    (valid : ∀ c ∈ clips, c.Valid format) (nonempty : clips ≠ [])
    (short : (clips.map fun c => c.stop - c.start).sum < 2 ^ 36) :
    Flac.decode (exportClips st format clips) = .ok (splice format clips) := sorry

theorem decodeFast_eq (d : ByteArray) : Flac.Fast.decodeFast d = Flac.decode d := sorry

theorem flac_roundTrip_fast (st : Flac.Fast.Settings) (x : Pcm) (valid : x.Valid) :
    Flac.decode (Flac.Fast.encodeFast st x) = .ok x := sorry

theorem export_correct_fast (st : Flac.Fast.Settings) (format : Format) (clips : List Clip)
    (valid : ∀ c ∈ clips, c.Valid format) (nonempty : clips ≠ [])
    (short : (clips.map fun c => c.stop - c.start).sum < 2 ^ 36) :
    Flac.decode (exportClipsFast st format clips) = .ok (splice format clips) := sorry

theorem flac_roundTrip_packed (st : Flac.Fast.Settings) (p : PackedPcm) (valid : p.toSpec.Valid) :
    Flac.decode (Flac.Fast.encodePacked st p) = .ok p.toSpec := sorry

end VeriCut
