import Lossy.Spec.Pcm

/-! How far one signal is from another, in integer sample units. -/

namespace Lossy

/-- Absolute sample differences, channel by channel. -/
def diffs (x y : Pcm) : List Nat :=
  (List.zipWith (fun a b => List.zipWith (fun u v => (u - v).natAbs) a.toList b.toList)
    x.chans y.chans).flatten

/-- The largest absolute sample error. -/
def maxErr (x y : Pcm) : Nat := (diffs x y).foldl max 0

/-- The sum of squared sample errors. -/
def sqErr (x y : Pcm) : Nat := ((diffs x y).map (· ^ 2)).sum

end Lossy
