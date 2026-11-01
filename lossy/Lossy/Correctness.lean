import Lossy.Proofs.Codec

/-!
The headline theorems. Statements here, proofs in `Lossy/Proofs/`.

`encode q x` is a FLAC file (a subset of the format, see `Flac/Encode.lean`)
and `decode` reads it back. What comes back is `quantize q x`
(`Spec/Quantize.lean`): every block of 4096 samples rounded to multiples
of `2^s`, `s` being `q` bits below the block's peak. Errors are measured
with `maxErr` and `sqErr` (`Spec/Error.lean`).
-/

namespace Lossy

/-- Decoding gives back the quantized signal. -/
theorem decode_encode_eq_quantize (q : Nat) (x : Pcm) (valid : x.Valid) :
    decode (encode q x) = some (quantize q x) :=
  Lossy.decode_encode valid

/-- At loss 0 the codec is lossless. -/
theorem lossless (x : Pcm) (valid : x.Valid) : decode (encode 0 x) = some x := by
  rw [decode_encode valid, quantize_zero valid]

/-- More loss never means less error, by either measure. -/
theorem error_mono (x : Pcm) (valid : x.Valid) {q q' : Nat} (more : q ≤ q') :
    ∃ y y', decode (encode q x) = some y ∧ decode (encode q' x) = some y' ∧
      maxErr x y ≤ maxErr x y' ∧ sqErr x y ≤ sqErr x y' :=
  ⟨_, _, decode_encode valid, decode_encode valid,
    quantize_mono_maxErr valid more, quantize_mono_sqErr valid more⟩

/-- No sample moves by `2^q` or more. -/
theorem error_lt (x : Pcm) (valid : x.Valid) (q : Nat) :
    ∃ y, decode (encode q x) = some y ∧ maxErr x y < 2 ^ q :=
  ⟨_, decode_encode valid, quantize_maxErr_lt valid⟩

/-- info: 'Lossy.decode_encode_eq_quantize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decode_encode_eq_quantize

/-- info: 'Lossy.lossless' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lossless

/-- info: 'Lossy.error_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms error_mono

/-- info: 'Lossy.error_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms error_lt

end Lossy
