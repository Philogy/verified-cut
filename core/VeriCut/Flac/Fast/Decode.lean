import VeriCut.Flac.Decode
import VeriCut.Flac.Fast.Bits
import VeriCut.Flac.Fast.Predict

/-!
`decodeFast`, what the CLI runs; `Proofs/Fast/Decode.lean` proves `decodeFast d = decode d` for
every `d`. Same parse as `Parse.lean`, except: Rice partitions are read without allocating per
value, `2 ^ k` is a `UInt64` shift, prediction is undone in `Int64` (`restoreFast`), and each
frame's samples are appended as it is parsed, so no `Stream` of all frames is held.
-/

namespace VeriCut.Flac.Fast

open Parser

/-- `count` Rice codes with parameter `k`, appended to `acc`: `many (riceP k)`. -/
def ricesLoop (d : ByteArray) (k : Nat) : Nat → Array Int → Nat → Except String (Array Int × Nat)
  | 0, acc, p => .ok (acc, p)
  | c + 1, acc, p =>
    let p1 := nextOne d p
    if p1 < 8 * d.size then
      if k = 0 ∨ p1 + 1 + k ≤ 8 * d.size then
        ricesLoop d k c (acc.push (unzigzag ((p1 - p) * pow2 k + bitsVal d k 0 (p1 + 1)))) (p1 + 1 + k)
      else .error "unexpected end of stream"
    else .error "unexpected end of stream"

def ricesP (k count : Nat) (acc : Array Int) : Parser (Array Int) := fun d p => ricesLoop d k count acc p

def partitionP (paramBits count : Nat) : Parser Partition := do
  let k ← readBits paramBits
  if k = 2 ^ paramBits - 1 then
    let bits ← readBits 5
    let values ← many (readSigned bits) count #[]
    pure ⟨.raw bits, values⟩
  else
    let values ← ricesP k count #[]
    pure ⟨.rice k, values⟩

def residualP (n warmup : Nat) : Parser Residual := do
  let method ← readBits 2
  check (method < 2) "reserved residual coding method"
  let order ← readBits 4
  check (n % 2 ^ order = 0 && warmup ≤ n / 2 ^ order) "bad partition order"
  let paramBits := if method = 1 then 5 else 4
  let first ← partitionP paramBits (n / 2 ^ order - warmup)
  let parts ← many (partitionP paramBits (n / 2 ^ order)) (2 ^ order - 1) #[first]
  pure ⟨method = 1, order, parts⟩

def bodyP (bits n type : Nat) : Parser Body := do
  if type = 0 then
    pure (.constant (← readSigned bits))
  else if type = 1 then
    pure (.verbatim (← many (readSigned bits) n #[]))
  else if 8 ≤ type ∧ type ≤ 12 then
    let order := type - 8
    check (order ≤ n) "predictor order above block size"
    let warmup ← many (readSigned bits) order #[]
    pure (.fixed warmup (← residualP n order))
  else if 32 ≤ type then
    let order := type - 31
    check (order ≤ n) "predictor order above block size"
    let warmup ← many (readSigned bits) order #[]
    let precision ← readBits 4
    check (precision < 15) "bad coefficient precision"
    let shift ← readSigned 5
    check (0 ≤ shift) "negative prediction shift"
    let coefs ← many (readSigned (precision + 1)) order #[]
    pure (.lpc (precision + 1) shift.toNat coefs warmup (← residualP n order))
  else fail "reserved subframe type"

def subframeP (bits n : Nat) : Parser Subframe := do
  check ((← readBits 1) = 0) "subframe padding bit set"
  let type ← readBits 6
  let wasted ← wastedP
  check (wasted < bits) "too many wasted bits"
  pure ⟨wasted, ← bodyP (bits - wasted) n type⟩

def subframesP (h : Header) : Nat → Array Subframe → Parser (Array Subframe)
  | 0, acc => pure acc
  | k + 1, acc => do subframesP h k (acc.push (← subframeP (h.subframeBits acc.size) h.blockSize))

def frameP (info : StreamInfo) : Parser Frame := do
  let start ← pos
  let header ← headerP info
  let headerEnd ← pos
  let crc ← readBits 8
  let d ← data
  check (crc8 (d.extract (start / 8) (headerEnd / 8)) = crc) "frame header CRC mismatch"
  let subframes ← subframesP header header.channels.count #[]
  align
  let frameEnd ← pos
  let crc ← readBits 16
  check (crc16 (d.extract (start / 8) (frameEnd / 8)) = crc) "frame CRC mismatch"
  pure ⟨header, subframes⟩

/-! ## Samples -/

def bodySamples (n : Nat) : Body → Array Int
  | .constant v => .replicate n v
  | .verbatim s => s
  | .fixed warmup r => restoreFast (fixedCoefs warmup.size) 0 warmup r.values
  | .lpc _ shift coefs warmup r => restoreFast coefs shift warmup r.values

def subframeSamples (n : Nat) (sf : Subframe) : Array Int :=
  if sf.wasted = 0 then bodySamples n sf.body
  else let m : Int := pow2 sf.wasted; (bodySamples n sf.body).map (· * m)

def frameSamples (f : Frame) : Array Int :=
  let n := f.header.blockSize
  interleave n (f.header.channels.undo (f.subframes.map (subframeSamples n)))

/-- Frames until the end of the data, keeping only their samples (appended to `acc`). -/
def framesSamplesP (info : StreamInfo) : Nat → Array Int → Parser (Array Int)
  | 0, acc => pure acc
  | fuel + 1, acc => do
    if ← atEnd then pure acc else framesSamplesP info fuel (acc ++ frameSamples (← frameP info))

def streamSamplesP : Parser (StreamInfo × Array Int) := do
  let head ← streamHeadP
  let d ← data
  skipMetadata d.size head.1
  -- Capacity is not observable; it saves regrowing the output. Capped by what the data could hold.
  let cap := min (head.2.totalSamples * head.2.channels) (8192 * d.size + 65536)
  let samples ← framesSamplesP head.2 d.size (.emptyWithCapacity cap)
  pure (head.2, samples)

def decodeFast (d : ByteArray) : Except String Pcm := do
  let ((info, samples), _) ← streamSamplesP d 0
  if info.totalSamples ≠ 0 ∧ info.totalSamples * info.channels ≠ samples.size then
    throw s!"STREAMINFO says {info.totalSamples} samples, frames hold {samples.size / info.channels}"
  pure ⟨info.format, samples⟩

end VeriCut.Flac.Fast
