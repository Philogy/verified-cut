/-! Integer PCM audio. -/

namespace Lossy

/-- A sample rate in Hz, a bit depth and one array of samples per channel. -/
structure Pcm where
  rate : Nat
  bits : Nat
  chans : List (Array Int)
  deriving DecidableEq, Repr

/-- Samples per channel. -/
def Pcm.length (x : Pcm) : Nat :=
  match x.chans with
  | [] => 0
  | c :: _ => c.size

/-- The smallest and largest `bits`-bit sample. -/
def lo (bits : Nat) : Int := -2 ^ (bits - 1)
def hi (bits : Nat) : Int := 2 ^ (bits - 1) - 1

/-- What the FLAC container can carry: 4 to 32 bits, 1 to 8 channels of
equal length, under 2^32 samples, and every sample fits the bit depth. -/
structure Pcm.Valid (x : Pcm) : Prop where
  bits : 4 ≤ x.bits ∧ x.bits ≤ 32
  chans : 1 ≤ x.chans.length ∧ x.chans.length ≤ 8
  rate : 0 < x.rate ∧ x.rate < 2 ^ 20
  sizes : ∀ c ∈ x.chans, c.size = x.length
  short : x.length < 2 ^ 32
  range : ∀ c ∈ x.chans, ∀ v ∈ c, lo x.bits ≤ v ∧ v ≤ hi x.bits

end Lossy
