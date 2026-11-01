import VeriCut.Spec.Audio
import VeriCut.Flac.Write

/-!
The encoder: choose a `Stream` for the samples, then write it.

Every choice here (block size, predictor, partitions, Rice parameters,
stereo mode) only affects size. The round-trip theorem holds for all of them,
so the cost estimates may be as rough as we like.
-/

namespace VeriCut.Flac

structure Settings where
  blockSize : Nat := 4096
  maxFixedOrder : Nat := 4
  maxPartitionOrder : Nat := 5
  /-- Try left/side, right/side and mid/side on stereo frames. -/
  stereo : Bool := true
  deriving Repr, Inhabited

/-- Roughly `flac -N`, with fixed predictors only. -/
def Settings.level : Nat → Settings
  | 0 => { blockSize := 1152, maxPartitionOrder := 3, stereo := false }
  | 1 | 2 => { blockSize := 1152, maxPartitionOrder := 3 }
  | 3 | 4 => { maxPartitionOrder := 4 }
  | 5 => {}
  | _ => { maxPartitionOrder := 6 }

def Settings.clampedBlockSize (st : Settings) : Nat := min (max st.blockSize 16) 65535

/-- Bits to Rice-code `count` values with zigzags summing to `sum`, roughly. -/
def riceCost (sum count k : Nat) : Nat := count * (k + 1) + (sum >>> k)

/-- The Rice parameter in `0..30` with the least estimated cost, and that cost. -/
def bestRice (sum count : Nat) : Nat × Nat :=
  (List.range 31).foldl (init := (0, riceCost sum count 0)) fun best k =>
    let c := riceCost sum count k
    if c < best.2 then (k, c) else best

def zigzagSum (r : Array Int) (start stop : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [start:stop] do s := s + zigzag r[i]!
  return s

/-- Partition `j` of `2 ^ p` over a block of `n`, minus the warm-up samples. -/
def partBounds (n warmup p j : Nat) : Nat × Nat :=
  let size := n >>> p
  (if j = 0 then 0 else j * size - warmup, (j + 1) * size - warmup)

def planResidual (maxOrder n warmup : Nat) (r : Array Int) : Residual × Nat :=
  let cost p := (List.range (2 ^ p)).foldl (init := 6) fun c j =>
    let (a, b) := partBounds n warmup p j
    c + 4 + (bestRice (zigzagSum r a b) (b - a)).2
  let ok p := n % 2 ^ p = 0 && warmup ≤ n >>> p
  let (p, c) := (List.range (maxOrder + 1)).foldl (init := (0, cost 0)) fun best p =>
    if ok p then let c := cost p; if c < best.2 then (p, c) else best else best
  let parts := (Array.range (2 ^ p)).map fun j =>
    let (a, b) := partBounds n warmup p j
    ({ coding := .rice (bestRice (zigzagSum r a b) (b - a)).1, values := r.extract a b } : Partition)
  let wide := parts.any fun q => match q.coding with | .rice k => 15 ≤ k | .raw _ => false
  (⟨wide, p, parts⟩, c)

/-- Samples from `order` on, minus their prediction. -/
def residualOf (coefs : Array Int) (shift : Nat) (s : Array Int) (order : Nat) : Array Int :=
  .ofFn (n := s.size - order) fun i => s[order + i.1]! - predict coefs shift s (order + i.1)

def absSum (r : Array Int) : Nat := r.foldl (· + ·.natAbs) 0

def planBody (st : Settings) (bits : Nat) (s : Array Int) : Body × Nat :=
  let n := s.size
  let verbatim := (Body.verbatim s, n * bits)
  let orders := (List.range (min st.maxFixedOrder 4 + 1)).filter (· ≤ n)
  let scored := orders.map fun k => let r := residualOf (fixedCoefs k) 0 s k; (k, r, absSum r)
  match scored with
  | [] => verbatim
  | first :: rest =>
    let (k, r, _) := rest.foldl (init := first) fun best c => if c.2.2 < best.2.2 then c else best
    let (res, c) := planResidual st.maxPartitionOrder n k r
    let fixed := (Body.fixed (s.extract 0 k) res, k * bits + c)
    if fixed.2 < verbatim.2 then fixed else verbatim

def trailingZeros (g : Nat) : Nat :=
  if g = 0 then 0 else go g 0 64
where
  go (g z : Nat) : Nat → Nat
    | 0 => z
    | fuel + 1 => if g % 2 = 0 then go (g / 2) (z + 1) fuel else z

/-- A subframe for `s` (nonempty) at `bits` bits per sample, and its estimated size. -/
def planSubframe (st : Settings) (bits : Nat) (s : Array Int) : Subframe × Nat :=
  if s.all (· == s[0]!) then (⟨0, .constant s[0]!⟩, bits)
  else
    let wasted := min (trailingZeros (s.foldl (· ||| ·.natAbs) 0)) (bits - 1)
    let (b, c) := planBody st (bits - wasted) (if wasted = 0 then s else s.map (· / 2 ^ wasted))
    (⟨wasted, b⟩, c + wasted)

/-- Channel `c` of the `n` frames from `offset` on. -/
def channelBlock (x : Pcm) (offset n c : Nat) : Array Int :=
  .ofFn (n := n) fun i => x.samples[(offset + i.1) * x.format.channels + c]!

def planFrame (st : Settings) (x : Pcm) (number offset n : Nat) : Frame :=
  let f := x.format
  let header channels : Header := ⟨n, f.sampleRate, f.bitsPerSample, channels, number⟩
  let blocks := (Array.range f.channels).map (channelBlock x offset n)
  let plain := blocks.map (planSubframe st f.bitsPerSample)
  if st.stereo && f.channels = 2 then
    let l := plain[0]!
    let r := plain[1]!
    let side := planSubframe st (f.bitsPerSample + 1) (Array.zipWith (· - ·) blocks[0]! blocks[1]!)
    let mid := planSubframe st f.bitsPerSample (Array.zipWith (fun a b => (a + b) / 2) blocks[0]! blocks[1]!)
    let options := [(Channels.leftSide, l, side), (.rightSide, side, r), (.midSide, mid, side)]
    let (ch, a, b) := options.foldl (init := (Channels.independent 2, l, r)) fun best o =>
      if o.2.1.2 + o.2.2.2 < best.2.1.2 + best.2.2.2 then o else best
    ⟨header ch, #[a.1, b.1]⟩
  else ⟨header (.independent f.channels), plain.map (·.1)⟩

def planFrames (st : Settings) (x : Pcm) : Array Frame :=
  let b := st.clampedBlockSize
  let len := x.length
  (Array.range ((len + b - 1) / b)).map fun k => planFrame st x k (k * b) (min b (len - k * b))

/-- Frame sizes go in 24 bits; 0 means unknown. -/
def fitFrameSize (v : Nat) : Nat := if v < 2 ^ 24 then v else 0

def encode (st : Settings) (x : Pcm) : ByteArray :=
  let frames := (planFrames st x).map writeFrame
  let maxSize := frames.foldl (max · ·.size) 0
  let minSize := frames.foldl (min · ·.size) maxSize
  let f := x.format
  let info : StreamInfo := {
    minBlockSize := st.clampedBlockSize, maxBlockSize := st.clampedBlockSize,
    minFrameSize := fitFrameSize minSize, maxFrameSize := fitFrameSize maxSize,
    sampleRate := f.sampleRate, channels := f.channels, bitsPerSample := f.bitsPerSample,
    totalSamples := x.length, md5 := 0 }
  writeStream info frames

end VeriCut.Flac
