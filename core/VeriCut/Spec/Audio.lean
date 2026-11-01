/-!
Audio as the theorems talk about it: integer samples, and splicing.
-/

namespace VeriCut

structure Format where
  sampleRate : Nat
  channels : Nat
  bitsPerSample : Nat
  deriving DecidableEq, Repr, Inhabited

/-- PCM audio. Sample `c` of frame `i` is `samples[i * channels + c]`. -/
structure Pcm where
  format : Format
  samples : Array Int
  deriving DecidableEq, Repr, Inhabited

/-- Samples per channel. -/
def Pcm.length (x : Pcm) : Nat := x.samples.size / x.format.channels

/-- What FLAC can carry: 1 to 8 channels of 4 to 32 bits, a sample rate that
fits in 20 bits, fewer than `2 ^ 36` samples per channel, and every sample
in range for its bit depth. -/
structure Pcm.Valid (x : Pcm) : Prop where
  channels : 1 ≤ x.format.channels ∧ x.format.channels ≤ 8
  bitsPerSample : 4 ≤ x.format.bitsPerSample ∧ x.format.bitsPerSample ≤ 32
  sampleRate : 1 ≤ x.format.sampleRate ∧ x.format.sampleRate < 2 ^ 20
  whole : x.samples.size % x.format.channels = 0
  length : x.length < 2 ^ 36
  range : ∀ s ∈ x.samples, -2 ^ (x.format.bitsPerSample - 1) ≤ s ∧ s < 2 ^ (x.format.bitsPerSample - 1)

/-- Samples `start` (inclusive) to `stop` (exclusive) of `src`, per channel. -/
structure Clip where
  src : Pcm
  start : Nat
  stop : Nat

/-- The clip's samples, all channels interleaved. -/
def Clip.samples (c : Clip) : Array Int :=
  c.src.samples.extract (c.start * c.src.format.channels) (c.stop * c.src.format.channels)

/-- The clips one after another. -/
def splice (format : Format) (clips : List Clip) : Pcm :=
  ⟨format, (clips.map Clip.samples).foldl (· ++ ·) #[]⟩

/-- A clip of a valid source in `format`, with `start ≤ stop ≤` its length. -/
structure Clip.Valid (format : Format) (c : Clip) : Prop where
  src : c.src.Valid
  format : c.src.format = format
  range : c.start ≤ c.stop ∧ c.stop ≤ c.src.length

end VeriCut
