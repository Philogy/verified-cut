import VeriCut.Flac.Fast.Write
import VeriCut.Flac.Fast.Predict
import VeriCut.Flac.Fast.Lpc
import VeriCut.Flac.Fast.Md5

/-!
The encoder: choose a `Stream` for the samples, then write it.

Every choice here (block size, predictor, partitions, Rice parameters,
stereo mode) only affects size. The round-trip theorem holds for all of them,
so the cost estimates may be as rough as we like.
-/

namespace VeriCut.Flac.Fast

structure Settings where
  blockSize : Nat := 4096
  maxFixedOrder : Nat := 4
  /-- Highest linear predictor order tried; 0 for fixed predictors only. -/
  maxLpcOrder : Nat := 8
  /-- Tukey window parameters to try for linear prediction, each giving one candidate. -/
  windows : List Float := [0.5]
  maxPartitionOrder : Nat := 5
  /-- Try left/side, right/side and mid/side on stereo frames. -/
  stereo : Bool := true
  deriving Repr, Inhabited

/-- Roughly `flac -N`. -/
def Settings.level : Nat → Settings
  | 0 => { blockSize := 1152, maxLpcOrder := 0, maxPartitionOrder := 3, stereo := false }
  | 1 | 2 => { blockSize := 1152, maxLpcOrder := 0, maxPartitionOrder := 3 }
  | 3 => { maxLpcOrder := 6, maxPartitionOrder := 4 }
  | 4 => { maxPartitionOrder := 4 }
  | 5 => {}
  | 6 => { maxPartitionOrder := 6 }
  | 7 => { maxLpcOrder := 12, maxPartitionOrder := 6 }
  | _ => { maxLpcOrder := 12, windows := [0.5, 0.1, 0.9], maxPartitionOrder := 6 }

def Settings.clampedBlockSize (st : Settings) : Nat := min (max st.blockSize 16) 65535

/-- The least `k ≤ 30` with `count * 2 ^ k ≥ sum`, libFLAC's estimate of the best parameter. -/
def riceGuess (sum count : Nat) (k : Nat := 0) : Nat :=
  if 30 ≤ k || sum ≤ (count.toUInt64 <<< k.toUInt64).toNat then k else riceGuess sum count (k + 1)
termination_by 30 - k
decreasing_by simp_all; omega

/-- The Rice parameter in `0..30` with the least estimated cost near the guess, and that cost. -/
def bestRice (sum count : Nat) : Nat × Nat :=
  let k := min (riceGuess sum count) 30
  [k - 1, k + 1].foldl (init := (k, riceCost sum count k)) fun best j =>
    if j < 31 then
      let c := riceCost sum count j
      if c < best.2 then (j, c) else best
    else best

/-- Sum of the zigzagged values `r[start:stop]`, in `UInt64` (only used to choose). -/
def zigzagSum (r : Array Int) (start stop : Nat) (acc : UInt64 := 0) : Nat :=
  if h : start < stop ∧ start < r.size then
    let v := r[start].toInt64
    zigzagSum r (start + 1) stop (acc + ((v <<< 1) ^^^ (v >>> 63)).toUInt64)
  else acc.toNat
termination_by stop - start

/-- Partition `j` of `2 ^ p`, Rice-coded with the best parameter. -/
def planPartition (r : Array Int) (n warmup p j : Nat) : Partition :=
  let ab := partBounds n warmup p j
  { coding := .rice (bestRice (zigzagSum r ab.1 ab.2) (ab.2 - ab.1)).1, values := r.extract ab.1 ab.2 }

/-- Whether `2 ^ p` partitions fit a block of `n` after `warmup` samples. -/
def orderFits (n warmup p : Nat) : Bool := n % 2 ^ p = 0 && warmup ≤ n >>> p

/-- The highest order up to `maxOrder` that fits (fitting is closed downwards). -/
def finestOrder (maxOrder n warmup : Nat) : Nat :=
  (List.range (maxOrder + 1)).foldl (fun b p => if orderFits n warmup p then p else b) 0

/-- Zigzag sums of the partitions at every order up to `fine`, finest first merged pairwise:
`sums[p][j]` is partition `j` of `2 ^ p`. -/
def partitionSums (r : Array Int) (n warmup fine : Nat) : Array (Array Nat) := Id.run do
  let leaves := (Array.range (2 ^ fine)).map fun j =>
    let ab := partBounds n warmup fine j
    zigzagSum r ab.1 ab.2
  let mut levels := #[leaves]
  let mut cur := leaves
  for _ in [0:fine] do
    cur := (Array.range (cur.size / 2)).map fun j => cur[2 * j]! + cur[2 * j + 1]!
    levels := levels.push cur
  return levels.reverse

/-- The partition order with the least estimated size, among those that divide the block. -/
def bestOrder (maxOrder n warmup : Nat) (r : Array Int) : Nat × Nat :=
  let fine := finestOrder maxOrder n warmup
  let sums := partitionSums r n warmup fine
  let cost p := (List.range (2 ^ p)).foldl (init := 6) fun c j =>
    let ab := partBounds n warmup p j
    c + 4 + (bestRice (sums[p]!)[j]! (ab.2 - ab.1)).2
  let ok p := orderFits n warmup p
  (List.range (maxOrder + 1)).foldl (init := (0, cost 0)) fun best p =>
    if ok p then let c := cost p; if c < best.2 then (p, c) else best else best

def planResidual (maxOrder n warmup : Nat) (r : Array Int) : Residual × Nat :=
  let best := bestOrder maxOrder n warmup r
  let parts := (Array.range (2 ^ best.1)).map (planPartition r n warmup best.1)
  let wide := parts.any fun q => match q.coding with | .rice k => 15 ≤ k | .raw _ => false
  (⟨wide, best.1, parts⟩, best.2)

@[inline] def abs64 (v : Int64) : Int64 := if v < 0 then -v else v

/-- From sample `i` on: `p1` is the previous sample, `d1 d2 d3` its residuals at orders 1 to 3,
`a0 … a4` the sums so far. -/
def fixedSumsLoop (s : Array Int) (i : Nat) (p1 d1 d2 d3 a0 a1 a2 a3 a4 : Int64) : Array Nat :=
  if h : i < s.size then
    let v := s[i].toInt64
    let e1 := v - p1
    let e2 := e1 - d1
    let e3 := e2 - d2
    let e4 := e3 - d3
    fixedSumsLoop s (i + 1) v e1 e2 e3 (a0 + abs64 v) (a1 + abs64 e1) (a2 + abs64 e2) (a3 + abs64 e3)
      (a4 + abs64 e4)
  else #[a0, a1, a2, a3, a4].map (·.toInt.toNat)
termination_by s.size - i

/-- Sums of `|residual|` of the fixed predictors of orders 0 to 4, from sample 4 on, in one pass.
Only used to choose the order, so `Int64` wrapping on absurd inputs costs size, not correctness. -/
def fixedSums (s : Array Int) : Array Nat :=
  if s.size < 5 then #[0, 0, 0, 0, 0] else
  let x0 := s[0]!.toInt64
  let x1 := s[1]!.toInt64
  let x2 := s[2]!.toInt64
  let x3 := s[3]!.toInt64
  let d1 := x3 - x2
  let d2 := d1 - (x2 - x1)
  let d3 := d2 - ((x2 - x1) - (x1 - x0))
  fixedSumsLoop s 4 x3 d1 d2 d3 0 0 0 0 0

/-- The fixed order with the least `|residual|` sum, at most `maxOrder` and `n`. -/
def bestFixedOrder (maxOrder n : Nat) (s : Array Int) : Nat :=
  let sums := fixedSums s
  (List.range (min maxOrder 4 + 1)).foldl (init := 0) fun best k =>
    if k ≤ n && sums[k]! < sums[best]! then k else best

/-- Fits in `bits`-bit two's complement. -/
def inRange (bits : Nat) (v : Int) : Bool := decide (-2 ^ (bits - 1) ≤ v ∧ v < 2 ^ (bits - 1))

/-- A linear-prediction body for the proposed `(precision, shift, coefs)`, if the format can
carry it, and its estimated size. The residual must also fit in 31 bits for other decoders. -/
def lpcBody (st : Settings) (bits : Nat) (s : Array Int) (c : Nat × Nat × Array Int) : Option (Body × Nat) :=
  let precision := c.1
  let shift := c.2.1
  let coefs := c.2.2
  let n := s.size
  let order := coefs.size
  if 1 ≤ order && order ≤ 32 && order ≤ n && 1 ≤ precision && precision ≤ 15 && shift < 16 &&
      coefs.all (inRange precision) then
    let r := residualFast coefs shift s order
    let lim : Nat := 2 ^ 30
    if r.all (·.natAbs < lim) then
      let res := planResidual (min st.maxPartitionOrder 15) n order r
      some (.lpc precision shift coefs (s.extract 0 order) res.1, order * (bits + precision) + 9 + res.2)
    else none
  else none

/-- The cheapest of verbatim, the best fixed predictor and the proposed linear predictors. -/
def planBody (st : Settings) (ws : List FloatArray) (bits : Nat) (s : Array Int) : Body × Nat :=
  let n := s.size
  let verbatim := (Body.verbatim s, n * bits)
  let k := bestFixedOrder st.maxFixedOrder n s
  let fixed := if k ≤ n then
      let res := planResidual (min st.maxPartitionOrder 15) n k (residualFast (fixedCoefs k) 0 s k)
      [(Body.fixed (s.extract 0 k) res.1, k * bits + res.2)]
    else []
  let lpcs := (Lpc.candidates bits st.maxLpcOrder ws s).filterMap (lpcBody st bits s)
  (fixed ++ lpcs).foldl (fun best c => if c.2 < best.2 then c else best) verbatim

/-- A subframe for `s` (nonempty) at `bits` bits per sample, and its estimated size. -/
def planSubframe (st : Settings) (ws : List FloatArray) (bits : Nat) (s : Array Int) : Subframe × Nat :=
  if s.all (· == s[0]!) then (⟨0, .constant s[0]!⟩, bits)
  else
    let w := min (trailingZeros (s.foldl (· ||| ·.natAbs) 0)) (bits - 1)
    -- Checked rather than proved: the round trip only needs the samples to be multiples.
    let wasted := if w ≠ 0 && (let m : Int := 2 ^ w; s.all (· % m == 0)) then w else 0
    let body := planBody st ws (bits - wasted) (if wasted = 0 then s else s.map (· / 2 ^ wasted))
    (⟨wasted, body.1⟩, body.2 + wasted)

/-- The LPC windows for a block of `n`, computed once per frame rather than per channel. -/
def frameWindows (st : Settings) (n : Nat) : List FloatArray :=
  if st.maxLpcOrder = 0 then [] else st.windows.map (Lpc.tukey n)

def planFrame (st : Settings) (x : Pcm) (number offset n : Nat) : Frame :=
  let f := x.format
  let header channels : Header := ⟨n, f.sampleRate, f.bitsPerSample, channels, number⟩
  let blocks := (Array.range f.channels).map (channelBlock x offset n)
  let ws := frameWindows st n
  let plain := blocks.map (planSubframe st ws f.bitsPerSample)
  if st.stereo && f.channels = 2 then
    let l := plain[0]!
    let r := plain[1]!
    let side := planSubframe st ws (f.bitsPerSample + 1) (Array.zipWith (· - ·) blocks[0]! blocks[1]!)
    let mid := planSubframe st ws f.bitsPerSample (Array.zipWith (fun a b => (a + b) / 2) blocks[0]! blocks[1]!)
    let options := [(Channels.leftSide, l, side), (.rightSide, side, r), (.midSide, mid, side)]
    let best := options.foldl (init := (Channels.independent 2, l, r)) fun best o =>
      if o.2.1.2 + o.2.2.2 < best.2.1.2 + best.2.2.2 then o else best
    ⟨header best.1, #[best.2.1.1, best.2.2.1]⟩
  else ⟨header (.independent f.channels), plain.map (·.1)⟩

def planFrames (st : Settings) (x : Pcm) : Array Frame :=
  let b := st.clampedBlockSize
  let len := x.length
  (Array.range ((len + b - 1) / b)).map fun k => planFrame st x k (k * b) (min b (len - k * b))

/-- Plan and write frame `k`. -/
def encodeFrame (st : Settings) (x : Pcm) (k : Nat) : ByteArray :=
  let b := st.clampedBlockSize
  writeFrame (planFrame st x k (k * b) (min b (x.length - k * b)))

/-- The frames' bytes one after another, and their smallest and largest size. Each frame is
planned and written before the next, so only one is held at a time. -/
def encodeFrames (st : Settings) (x : Pcm) : ByteArray × Nat × Nat :=
  let b := st.clampedBlockSize
  -- Reserved up front: appending to a full `ByteArray` copies it, which costs time and peak
  -- memory. The input's size in bytes bounds the output of any sensible encoding.
  let cap := x.samples.size * ((x.format.bitsPerSample + 7) / 8) + 4096
  (List.range ((x.length + b - 1) / b)).foldl (init := (.emptyWithCapacity cap, 0, 0)) fun (out, lo, hi) k =>
    let f := encodeFrame st x k
    (out ++ f, if k = 0 then f.size else min lo f.size, max hi f.size)

def encodeFast (st : Settings) (x : Pcm) : ByteArray :=
  let (body, minSize, maxSize) := encodeFrames st x
  let f := x.format
  let info : StreamInfo := {
    minBlockSize := st.clampedBlockSize, maxBlockSize := st.clampedBlockSize,
    minFrameSize := fitFrameSize minSize, maxFrameSize := fitFrameSize maxSize,
    sampleRate := f.sampleRate, channels := f.channels, bitsPerSample := f.bitsPerSample,
    totalSamples := x.length, md5 := Md5.ofSamples f.bitsPerSample x.samples % 2 ^ 128 }
  (writeHead info .empty).bytes ++ body

end VeriCut.Flac.Fast
