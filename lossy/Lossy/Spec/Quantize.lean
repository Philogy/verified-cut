import Lossy.Spec.Pcm

/-!
The loss. Each block of `blockSize` samples is rounded to a grid of
multiples of `2^s`, where `s` grows with the loss setting `q` and shrinks
for quiet blocks, so every block keeps about the same signal-to-noise
ratio. A larger `s` gives a coarser grid that is a subset of every finer
one, which is why more loss never means less error.
-/

namespace Lossy

def blockSize : Nat := 4096

/-- The nearest multiple of `2^s` to `v` that fits in `bits` bits. Ties
round up. -/
def roundTo (bits s : Nat) (v : Int) : Int :=
  let d : Int := 2 ^ s
  let r := (v + d / 2) / d * d
  if r ≤ hi bits then r else r - d

/-- The largest magnitude in block `f`, over all channels. -/
def peak (x : Pcm) (f : Nat) : Nat :=
  x.chans.foldl (fun m c =>
    (c.extract (f * blockSize) (f * blockSize + blockSize)).foldl (fun m v => max m v.natAbs) m) 0

/-- Bits needed for a magnitude `p`: 0 for 0. -/
def bitLength (p : Nat) : Nat := if p = 0 then 0 else p.log2 + 1

/-- The grid for block `f` at loss `q`: `q` bits below the block's peak. -/
def shift (q : Nat) (x : Pcm) (f : Nat) : Nat :=
  q - ((x.bits - 1) - bitLength (peak x f))

/-- `x` with every sample rounded to its block's grid. -/
def quantize (q : Nat) (x : Pcm) : Pcm :=
  { x with chans := x.chans.map fun c =>
      c.mapIdx fun i v => roundTo x.bits (shift q x (i / blockSize)) v }

end Lossy
