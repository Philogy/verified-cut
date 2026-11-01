/-!
Choosing linear predictors, as libFLAC does: window the block, autocorrelate, solve for
predictors of every order with Levinson-Durbin, pick an order by the expected residual size,
and quantize the coefficients.

All of this is in `Float` and only proposes coefficients. The encoder computes the residual
with integers and checks what the format needs, so nothing here affects correctness.
-/

namespace VeriCut.Flac.Lpc

-- Float literals elaborate to `OfScientific.ofScientific`, which parses through GMP at run
-- time; as top-level constants they are computed once.
def half : Float := 0.5
def one : Float := 1.0
def zero : Float := 0.0
def pi : Float := 3.141592653589793
def huge : Float := 1e300

/-- Tukey window: flat in the middle, a Hann taper over `p / 2` of the length at each end. -/
def tukey (n : Nat) (p : Float) : FloatArray := Id.run do
  let mut w := FloatArray.mk (Array.replicate n one)
  let np := (p * half * n.toUInt64.toFloat).toUInt64.toNat
  if np < 2 then return w
  let m := np - 1
  for i in [0:m + 1] do
    w := w.set! i (half - half * Float.cos (pi * i.toUInt64.toFloat / m.toUInt64.toFloat))
    w := w.set! (n - m - 1 + i) (half - half * Float.cos (pi * (i + m).toUInt64.toFloat / m.toUInt64.toFloat))
  return w

def windowed (s : Array Int) (w : FloatArray) : FloatArray := Id.run do
  let mut x := FloatArray.mk (Array.replicate s.size zero)
  for i in [0:s.size] do
    x := x.set! i (s[i]!.toInt64.toFloat * w[i]!)
  return x

/-- `Σ_{i ≥ lag} x[i] * x[i - lag]`. -/
def lagSum (x : FloatArray) (lag i : Nat) (acc : Float) : Float :=
  if h : i < x.size then lagSum x lag (i + 1) (acc + x[i] * x[i - lag]!) else acc
termination_by x.size - i

/-- Autocorrelation at lags `0` to `maxLag`. -/
def autocorrelation (x : FloatArray) (maxLag : Nat) : Array Float :=
  (Array.range (maxLag + 1)).map fun lag => lagSum x lag lag zero

/-- Levinson-Durbin: the predictor coefficients of every order `1..maxOrder`
(coefficient `j` multiplies the sample `j + 1` back), and the prediction error of each. -/
def levinson (r : Array Float) (maxOrder : Nat) : Array (Array Float) × Array Float := Id.run do
  let mut lpc : Array Float := Array.replicate maxOrder zero
  let mut err := r[0]!
  let mut coefs := #[]
  let mut errs := #[]
  for i in [0:maxOrder] do
    if err ≤ zero then break
    let mut acc := -r[i + 1]!
    for j in [0:i] do acc := acc - lpc[j]! * r[i - j]!
    let k := acc / err
    let prev := lpc
    lpc := lpc.set! i k
    for j in [0:i] do lpc := lpc.set! j (prev[j]! + k * prev[i - 1 - j]!)
    err := err * (one - k * k)
    coefs := coefs.push ((lpc.extract 0 (i + 1)).map (- ·))
    errs := errs.push err
  return (coefs, errs)

/-- Expected bits per residual sample for prediction error `err` over `n` samples. -/
def expectedBits (err : Float) (n : Nat) : Float :=
  if err > zero && n > 0 then
    let b := half * Float.log2 (half / n.toUInt64.toFloat * err)
    if b ≥ zero then b else zero
  else if err < zero then huge else zero

/-- The order (index into `errs`, plus one) with the least expected size. -/
def bestOrder (errs : Array Float) (n overhead : Nat) : Nat := Id.run do
  let mut best := 0
  let mut bestBits := huge
  for i in [0:errs.size] do
    let order := i + 1
    if order < n then
      let bits := expectedBits errs[i]! (n - order) * (n - order).toUInt64.toFloat + (order * overhead).toUInt64.toFloat
      if bits < bestBits then
        best := order
        bestBits := bits
  return best

def roundToInt (x : Float) : Int :=
  let r := x.round
  if r < zero then -((-r).toUInt64.toNat : Int) else (r.toUInt64.toNat : Int)

/-- Coefficients as `precision`-bit integers scaled by `2 ^ shift`, with error feedback; `none`
when they don't fit. -/
def quantize (lp : Array Float) (precision : Nat) : Option (Nat × Array Int) := Id.run do
  let cmax := lp.foldl (fun m c => max m c.abs) zero
  if cmax ≤ zero || precision < 2 then return none
  let qmax : Int := 2 ^ (precision - 1) - 1
  let qmin : Int := -(2 ^ (precision - 1))
  let log2cmax := cmax.frExp.2 - 1
  let shift := (precision : Int) - 1 - log2cmax - 1
  if shift < 0 then return none
  let shift := min shift.toNat 15
  let scale := (2 ^ shift : Nat).toUInt64.toFloat
  let mut err := zero
  let mut q := #[]
  for c in lp do
    err := err + c * scale
    let v := max qmin (min qmax (roundToInt err))
    err := err - Float.ofInt v
    q := q.push v
  return some (shift, q)

/-- libFLAC's coefficient precision for a block of `n` at `bits` bits per sample. -/
def defaultPrecision (bits n : Nat) : Nat :=
  if bits < 16 then max 5 (2 + bits / 2)
  else if bits ≤ 17 then
    if n ≤ 192 then 7 else if n ≤ 384 then 8 else if n ≤ 576 then 9 else if n ≤ 1152 then 10
    else if n ≤ 2304 then 11 else if n ≤ 4608 then 12 else 13
  else if n ≤ 384 then 13 else if n ≤ 1152 then 14 else 15

/-- A predictor for `s`: `(precision, shift, coefficients)`, for each window in `windows`
(each as long as `s`). -/
def candidates (bits maxOrder : Nat) (windows : List FloatArray) (s : Array Int) : List (Nat × Nat × Array Int) :=
  let n := s.size
  let maxOrder := min maxOrder 32
  if maxOrder = 0 || n ≤ maxOrder then [] else
  let precision := defaultPrecision bits n
  windows.filterMap fun w =>
    let x := windowed s w
    let r := autocorrelation x maxOrder
    if r[0]! ≤ zero then none else
    let (coefs, errs) := levinson r maxOrder
    let order := bestOrder errs n (precision + bits)
    if order = 0 then none else
    (quantize coefs[order - 1]! precision).map fun (shift, q) => (precision, shift, q)

end VeriCut.Flac.Lpc
