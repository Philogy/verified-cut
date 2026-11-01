import VeriCut.Flac.Encode

/-!
Prediction in `Int64`: `residualFast` and `restoreFast` sum in `Int64` when no sum can overflow
and fall back to the spec's `residualOf` and `restore` otherwise; `Proofs/Fast/Predict.lean`
proves them equal to those for every input.

The bound: at most 32 coefficients under `2 ^ 20` and samples under `2 ^ 36` in magnitude keep
every partial sum under `2 ^ 61`.
-/

namespace VeriCut.Flac.Fast

/-- `dot` in `Int64`. -/
def dot64 (coefs : Array Int64) (s : Array Int) (i : Nat) : Nat → Int64 → Int64
  | 0, acc => acc
  | j + 1, acc => dot64 coefs s i j (acc + coefs[j]! * s[i - 1 - j]!.toInt64)

-- A constant, not a literal: a `Nat` literal of `2 ^ 32` or more in a loop is parsed from a
-- string on every iteration.
@[noinline] def sampleLimit : Nat := 2 ^ 36

/-- Whether `coefs` qualify for `Int64` sums. -/
def smallCoefs (coefs : Array Int) : Bool :=
  let lc : Nat := 2 ^ 20
  coefs.size ≤ 32 && coefs.all (·.natAbs < lc)

def residualFast (coefs : Array Int) (shift : Nat) (s : Array Int) (order : Nat) : Array Int :=
  if smallCoefs coefs && s.all (·.natAbs < sampleLimit) then
    let c := coefs.map Int.toInt64
    .ofFn (n := s.size - order) fun i => s[order + i.1]! - ((dot64 c s (order + i.1) c.size 0).toInt >>> shift)
  else residualOf coefs shift s order

/-- One step of `restore` in `Int64`; `ok` turns false, for good, on a sample out of bounds. -/
@[inline] def restoreStep (c : Array Int64) (shift : Nat) (st : Array Int × Bool) (r : Int) : Array Int × Bool :=
  if st.2 then
    let v := r + ((dot64 c st.1 st.1.size c.size 0).toInt >>> shift)
    (st.1.push v, v.natAbs < sampleLimit)
  else st

def restoreFast (coefs : Array Int) (shift : Nat) (warmup residual : Array Int) : Array Int :=
  if smallCoefs coefs && warmup.all (·.natAbs < sampleLimit) then
    let st := residual.foldl (restoreStep (coefs.map Int.toInt64) shift) (warmup, true)
    if st.2 then st.1 else restore coefs shift warmup residual
  else restore coefs shift warmup residual

end VeriCut.Flac.Fast
