import Lossy.Bits
import Lossy.Spec.Quantize

/-!
A FLAC encoder for a subset of the format: fixed block size, independent
channels, CONSTANT, VERBATIM and FIXED subframes, one Rice partition, and
wasted bits, which is where the loss turns into smaller files: a block
rounded to multiples of `2^s` is coded with `s` fewer bits per sample.
-/

namespace Lossy.Flac

/-- A subframe's samples, after removing the wasted bits. -/
inductive Sub where
  | const (v : Int)
  | verbatim (vs : List Int)
  /-- Fixed polynomial predictor of order `order`, warm-up samples, Rice
  parameter `k`, residuals. -/
  | fixed (order : Nat) (warm : List Int) (k : Nat) (res : List Int)
  deriving Repr, DecidableEq

/-- The last four samples, newest first. -/
abbrev Window := Int × Int × Int × Int

def Window.push (w : Window) (x : Int) : Window := (x, w.1, w.2.1, w.2.2.1)

def Window.ofList (xs : List Int) : Window := xs.foldl Window.push (0, 0, 0, 0)

/-- The FLAC fixed predictors. -/
def predict : Nat → Window → Int
  | 0, _ => 0
  | 1, (a, _, _, _) => a
  | 2, (a, b, _, _) => 2 * a - b
  | 3, (a, b, c, _) => 3 * a - 3 * b + c
  | _, (a, b, c, d) => 4 * a - 6 * b + 4 * c - d

def residuals (o : Nat) : Window → List Int → List Int
  | _, [] => []
  | w, x :: xs => (x - predict o w) :: residuals o (w.push x) xs

def restore (o : Nat) : Window → List Int → List Int
  | _, [] => []
  | w, e :: es =>
    let x := e + predict o w
    x :: restore o (w.push x) es

/-- The `n` samples a subframe stands for. -/
def Sub.samples (n : Nat) : Sub → List Int
  | .const v => List.replicate n v
  | .verbatim vs => vs
  | .fixed o warm _ res => warm ++ restore o (Window.ofList warm) res

def Sub.type : Sub → Nat
  | .const _ => 0
  | .verbatim _ => 1
  | .fixed o _ _ _ => 8 + o

def Sub.body (width : Nat) : Sub → List Bool
  | .const v => bitsInt width v
  | .verbatim vs => vs.flatMap (bitsInt width)
  | .fixed _ warm k res =>
    warm.flatMap (bitsInt width) ++ bitsOf 2 0 ++ bitsOf 4 0 ++ bitsOf 4 k ++ res.flatMap (rice k)

def wastedBits (w : Nat) : List Bool := if w = 0 then [false] else true :: unary (w - 1)

/-- A subframe of a `bps`-bit channel with `w` wasted bits. -/
def subframeBits (bps : Nat) (ws : Nat × Sub) : List Bool :=
  [false] ++ bitsOf 6 ws.2.type ++ wastedBits ws.1 ++ ws.2.body (bps - ws.1)

/-! Choosing a subframe. -/

/-- Rice bits with parameter `k` for residuals already folded by `zig`. -/
def riceCost (k : Nat) (us : List Nat) : Nat :=
  us.foldl (fun c u => c + (u >>> k) + 1 + k) 0

/-- The smallest `k` below 15 with `n * 2^k` at least `sum`. -/
def meanK (n sum : Nat) : Nat :=
  ((List.range 15).find? fun k => sum ≤ n <<< k).getD 14

/-- A Rice parameter below 15: the cheapest next to the mean's, like libFLAC. -/
def bestK (res : List Int) : Nat :=
  let us := res.map zig
  let k := meanK us.length (us.foldl (· + ·) 0)
  [k - 1, min 14 (k + 1)].foldl (fun k k' => if riceCost k' us < riceCost k us then k' else k) k

def Sub.cost (width : Nat) : Sub → Nat
  | .const _ => width
  | .verbatim vs => vs.length * width
  | .fixed o _ k res => o * width + 10 + riceCost k (res.map zig)

def fixedSub (o : Nat) (ys : List Int) : Sub :=
  let warm := ys.take o
  let res := residuals o (Window.ofList warm) (ys.drop o)
  .fixed o warm (bestK res) res

/-- The trailing zero bits shared by all of `xs`, at most `cap`. -/
def wasted (cap : Nat) (xs : List Int) : Nat :=
  let any := xs.foldl (fun a v => a ||| v.natAbs) 0
  let rec tz : Nat → Nat → Nat
    | 0, _ => 0
    | fuel + 1, n => if n % 2 = 0 then tz fuel (n / 2) + 1 else 0
  let c := tz cap any
  if xs.all (· % 2 ^ c == 0) then c else 0

/-- The cheapest subframe for the samples `xs` of a `bps`-bit channel. -/
def analyze (bps : Nat) (xs : List Int) : Nat × Sub :=
  let w := wasted (bps - 1) xs
  let ys := xs.map (· / 2 ^ w)
  let width := bps - w
  match ys with
  | [] => (w, .verbatim [])
  | y :: _ =>
    if ys.all (· == y) then (w, .const y) else
    let cands := (List.range (min 5 ys.length)).map (fixedSub · ys)
    (w, cands.foldl (fun s s' => if s'.cost width < s.cost width then s' else s) (.verbatim ys))

/-! Frames and the stream. -/

/-- Frame numbers below 2^21, coded like UTF-8. -/
def utf8 (n : Nat) : List Bool :=
  let cont (m : Nat) := bitsOf 8 (128 + m % 64)
  if n < 128 then bitsOf 8 n
  else if n < 2048 then bitsOf 8 (192 + n / 64) ++ cont n
  else if n < 65536 then bitsOf 8 (224 + n / 4096) ++ cont (n / 64) ++ cont n
  else bitsOf 8 (240 + n / 262144) ++ cont (n / 4096) ++ cont (n / 64) ++ cont n

structure Frame where
  number : Nat
  size : Nat
  subs : List (Nat × Sub)

/-- Sync code, fixed block size, block size in 16 bits after the frame
number, rate and depth from STREAMINFO, independent channels. -/
def headerBits (fr : Frame) : List Bool :=
  bitsOf 16 0xFFF8 ++ bitsOf 8 0x70 ++ bitsOf 4 (fr.subs.length - 1) ++ bitsOf 4 0 ++
    utf8 fr.number ++ bitsOf 16 (fr.size - 1)

def bodyBits (bps : Nat) (fr : Frame) : List Bool :=
  let h := headerBits fr
  h ++ bitsOf 8 (crc8 h) ++ fr.subs.flatMap (subframeBits bps)

def padBits (l : List Bool) : List Bool := zeros ((8 - l.length % 8) % 8)

/-- The CRC is computed from the packed bytes: bit by bit it was half the
encoding time. The decoder does not check it. -/
def frameBits (bps : Nat) (fr : Frame) : List Bool :=
  let b := bodyBits bps fr ++ padBits (bodyBits bps fr)
  b ++ bitsOf 16 (crc16Bytes (packInto .empty b))

/-- `fLaC` and a STREAMINFO block; MD5 left zero (unknown). -/
def streamHeader (x : Pcm) : List Bool :=
  bitsOf 32 0x664C6143 ++ bitsOf 8 0x80 ++ bitsOf 24 34 ++
    bitsOf 16 blockSize ++ bitsOf 16 blockSize ++ bitsOf 24 0 ++ bitsOf 24 0 ++
    bitsOf 20 x.rate ++ bitsOf 3 (x.chans.length - 1) ++ bitsOf 5 (x.bits - 1) ++
    bitsOf 36 x.length ++ bitsOf 128 0

def frameCount (n : Nat) : Nat := (n + blockSize - 1) / blockSize

/-- Block `f` of every channel. -/
def block (x : Pcm) (f : Nat) : List (List Int) :=
  x.chans.map fun c => (c.extract (f * blockSize) (f * blockSize + blockSize)).toList

def encodeFrame (q : Nat) (x : Pcm) (f : Nat) : Frame :=
  let s := shift q x f
  { number := f
    size := min blockSize (x.length - f * blockSize)
    subs := (block x f).map fun b => analyze x.bits (b.map (roundTo x.bits s)) }

end Flac

/-- Lossy FLAC: loss `q` = 0 is lossless. -/
def encode (q : Nat) (x : Pcm) : ByteArray :=
  (List.range (Flac.frameCount x.length)).foldl
    (fun out f => packInto out (Flac.frameBits x.bits (Flac.encodeFrame q x f)))
    (packInto .empty (Flac.streamHeader x))

end Lossy
