/-!
The FLAC stream as data (RFC 9639), and what it decodes to.

`Parse.lean` reads bytes into these types, `Write.lean` writes them back. The
meaning of a stream is `Stream.samples`: the bitstream itself carries no
arithmetic, all of it is here.
-/

namespace VeriCut.Flac

/-- How a residual partition is coded. -/
inductive Coding where
  /-- Rice code with parameter `k`. -/
  | rice (k : Nat)
  /-- Escape: plain `bits`-bit two's complement values. -/
  | raw (bits : Nat)
  deriving Repr, DecidableEq, Inhabited

structure Partition where
  coding : Coding
  values : Array Int
  deriving Repr, Inhabited

structure Residual where
  /-- 5-bit Rice parameters (coding method 1) instead of 4-bit. -/
  wide : Bool
  /-- `2 ^ order` partitions. -/
  order : Nat
  parts : Array Partition
  deriving Repr, Inhabited

def Residual.values (r : Residual) : Array Int :=
  r.parts.foldl (· ++ ·.values) #[]

inductive Body where
  | constant (v : Int)
  | verbatim (samples : Array Int)
  /-- Fixed predictor of order `warmup.size`. -/
  | fixed (warmup : Array Int) (residual : Residual)
  /-- Linear predictor of order `warmup.size = coefs.size`. -/
  | lpc (precision shift : Nat) (coefs warmup : Array Int) (residual : Residual)
  deriving Repr, Inhabited

structure Subframe where
  /-- Every sample is a multiple of `2 ^ wasted`, and the body codes the quotients. -/
  wasted : Nat
  body : Body
  deriving Repr, Inhabited

/-- Interchannel decorrelation of a frame. -/
inductive Channels where
  | independent (n : Nat)
  /-- Left, then side = left - right. -/
  | leftSide
  /-- Side, then right. -/
  | rightSide
  /-- Mid = (left + right) / 2 rounded down, then side. -/
  | midSide
  deriving Repr, DecidableEq, Inhabited

def Channels.count : Channels → Nat
  | .independent n => n
  | _ => 2

/-- Whether coded channel `c` is a side channel, which has one bit more. -/
def Channels.isSide : Channels → Nat → Bool
  | .leftSide, 1 | .rightSide, 0 | .midSide, 1 => true
  | _, _ => false

structure Header where
  blockSize : Nat
  sampleRate : Nat
  bitsPerSample : Nat
  channels : Channels
  /-- Frame number, or first sample number for variable block sizes. -/
  number : Nat
  deriving Repr, Inhabited

def Header.subframeBits (h : Header) (c : Nat) : Nat :=
  h.bitsPerSample + if h.channels.isSide c then 1 else 0

structure Frame where
  header : Header
  subframes : Array Subframe
  deriving Repr, Inhabited

structure StreamInfo where
  minBlockSize : Nat
  maxBlockSize : Nat
  /-- In bytes, 0 if unknown. -/
  minFrameSize : Nat
  maxFrameSize : Nat
  sampleRate : Nat
  channels : Nat
  bitsPerSample : Nat
  /-- Samples per channel, 0 if unknown. -/
  totalSamples : Nat
  /-- MD5 of the decoded samples, 0 if not computed. -/
  md5 : Nat
  deriving Repr, Inhabited

structure Stream where
  info : StreamInfo
  frames : Array Frame
  deriving Repr, Inhabited

/-! ## Decoding -/

def fixedCoefs : Nat → Array Int
  | 0 => #[]
  | 1 => #[1]
  | 2 => #[2, -1]
  | 3 => #[3, -3, 1]
  | _ => #[4, -6, 4, -1]

/-- `acc + Σ_{j < k} coefs[j] * s[i - 1 - j]`. -/
def dot (coefs s : Array Int) (i : Nat) : Nat → Int → Int
  | 0, acc => acc
  | j + 1, acc => dot coefs s i j (acc + coefs[j]! * s[i - 1 - j]!)

/-- The prediction for sample `i` from the samples before it. -/
def predict (coefs : Array Int) (shift : Nat) (s : Array Int) (i : Nat) : Int :=
  dot coefs s i coefs.size 0 / 2 ^ shift

/-- Undo prediction: append `r + prediction` for each residual `r`. -/
def restore (coefs : Array Int) (shift : Nat) (warmup residual : Array Int) : Array Int :=
  residual.foldl (fun s r => s.push (r + predict coefs shift s s.size)) warmup

def Body.samples (n : Nat) : Body → Array Int
  | .constant v => .replicate n v
  | .verbatim s => s
  | .fixed warmup r => restore (fixedCoefs warmup.size) 0 warmup r.values
  | .lpc _ shift coefs warmup r => restore coefs shift warmup r.values

def Subframe.samples (n : Nat) (sf : Subframe) : Array Int :=
  if sf.wasted = 0 then sf.body.samples n else (sf.body.samples n).map (· * 2 ^ sf.wasted)

/-- Coded channels to left/right (or the independent channels). -/
def Channels.undo : Channels → Array (Array Int) → Array (Array Int)
  | .leftSide, cs => #[cs[0]!, Array.zipWith (· - ·) cs[0]! cs[1]!]
  | .rightSide, cs => #[Array.zipWith (· + ·) cs[0]! cs[1]!, cs[1]!]
  | .midSide, cs =>
    let mid := Array.zipWith (fun (m s : Int) => 2 * m + s % 2) cs[0]! cs[1]!
    #[Array.zipWith (fun m s => (m + s) / 2) mid cs[1]!, Array.zipWith (fun m s => (m - s) / 2) mid cs[1]!]
  | .independent _, cs => cs

/-- Channel arrays of length `n` to one interleaved array. -/
def interleave (n : Nat) (cs : Array (Array Int)) : Array Int :=
  .ofFn (n := n * cs.size) fun k => cs[k.1 % cs.size]![k.1 / cs.size]!

/-- The frame's samples, interleaved. -/
def Frame.samples (f : Frame) : Array Int :=
  let n := f.header.blockSize
  interleave n (f.header.channels.undo (f.subframes.map (·.samples n)))

def Stream.samples (s : Stream) : Array Int :=
  s.frames.foldl (· ++ ·.samples) #[]

end VeriCut.Flac
