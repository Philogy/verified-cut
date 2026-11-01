import VeriCut.Flac.Bits
import VeriCut.Flac.Crc
import VeriCut.Flac.Codes

/-!
Reading bytes into a `Stream` (RFC 9639).
-/

namespace VeriCut.Flac

open Parser

def riceP (k : Nat) : Parser Int := do
  let q ← unary
  let r ← readBits k
  pure (unzigzag (q * pow2 k + r))

/-- `count` Rice codes with parameter `k`, appended to `acc`: `many (riceP k)` without
allocating per value (`ricesLoop_eq`). -/
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

/-- The residual of a block of `n` samples after `warmup` warm-up samples. -/
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

def wastedP : Parser Nat := do
  if (← readBits 1) = 1 then pure ((← unary) + 1) else pure 0

def subframeP (bits n : Nat) : Parser Subframe := do
  check ((← readBits 1) = 0) "subframe padding bit set"
  let type ← readBits 6
  let wasted ← wastedP
  check (wasted < bits) "too many wasted bits"
  pure ⟨wasted, ← bodyP (bits - wasted) n type⟩

def lookupCode (table : List (Nat × Nat)) (code : Nat) (what : String) : Parser Nat :=
  match table.lookup code with
  | some v => pure v
  | none => fail s!"reserved {what} code"

/-- Remaining bytes of a frame or sample number after its lead byte, and the lead byte's value bits. -/
def codedRest (b : Nat) : Option (Nat × Nat) :=
  if b < 0x80 then some (0, b) else if b < 0xC0 then none
  else if b < 0xE0 then some (1, b - 0xC0) else if b < 0xF0 then some (2, b - 0xE0)
  else if b < 0xF8 then some (3, b - 0xF0) else if b < 0xFC then some (4, b - 0xF8)
  else if b < 0xFE then some (5, b - 0xFC) else if b < 0xFF then some (6, 0) else none

def continuationP : Nat → Nat → Parser Nat
  | 0, v => pure v
  | m + 1, v => do continuationP m (64 * v + (← readBits 8) % 64)

def codedNumberP : Parser Nat := do
  match codedRest (← readBits 8) with
  | some (m, v) => continuationP m v
  | none => fail "bad frame number"

def channelsP (code : Nat) : Parser Channels :=
  if code < 8 then pure (.independent (code + 1))
  else if code = 8 then pure .leftSide
  else if code = 9 then pure .rightSide
  else if code = 10 then pure .midSide
  else fail "reserved channel assignment"

/-- The block size, after the frame number, from its 4-bit code. -/
def blockSizeP (code : Nat) : Parser Nat :=
  if code = 6 then do pure ((← readBits 8) + 1)
  else if code = 7 then do pure ((← readBits 16) + 1)
  else lookupCode blockSizeCodes code "block size"

def sampleRateP (info : StreamInfo) (code : Nat) : Parser Nat :=
  if code = 0 then pure info.sampleRate
  else if code = 12 then do pure ((← readBits 8) * 1000)
  else if code = 13 then readBits 16
  else if code = 14 then do pure ((← readBits 16) * 10)
  else lookupCode sampleRateCodes code "sample rate"

def bitsPerSampleP (info : StreamInfo) (code : Nat) : Parser Nat :=
  if code = 0 then pure info.bitsPerSample else lookupCode bitsPerSampleCodes code "sample size"

def headerP (info : StreamInfo) : Parser Header := do
  check ((← readBits 14) = 0x3FFE) "lost frame sync"
  check ((← readBits 1) = 0) "reserved header bit set"
  let _variable ← readBits 1
  let sizeCode ← readBits 4
  let rateCode ← readBits 4
  let channels ← channelsP (← readBits 4)
  let bitsCode ← readBits 3
  check ((← readBits 1) = 0) "reserved header bit set"
  let number ← codedNumberP
  let blockSize ← blockSizeP sizeCode
  let sampleRate ← sampleRateP info rateCode
  let bitsPerSample ← bitsPerSampleP info bitsCode
  check (sampleRate = info.sampleRate) "frame sample rate differs from STREAMINFO"
  check (bitsPerSample = info.bitsPerSample) "frame sample size differs from STREAMINFO"
  check (channels.count = info.channels) "frame channel count differs from STREAMINFO"
  pure ⟨blockSize, sampleRate, bitsPerSample, channels, number⟩

def subframesP (h : Header) : Nat → Array Subframe → Parser (Array Subframe)
  | 0, acc => pure acc
  | k + 1, acc => do subframesP h k (acc.push (← subframeP (h.subframeBits acc.size) h.blockSize))

/-- A frame, starting at a byte boundary. -/
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

/-- Frames until the end of the data. `fuel` bounds their number; every frame takes a byte at least. -/
def framesP (info : StreamInfo) : Nat → Array Frame → Parser (Array Frame)
  | 0, acc => pure acc
  | fuel + 1, acc => do
    if ← atEnd then pure acc else framesP info fuel (acc.push (← frameP info))

def infoP : Parser StreamInfo := do
  let minBlockSize ← readBits 16
  let maxBlockSize ← readBits 16
  let minFrameSize ← readBits 24
  let maxFrameSize ← readBits 24
  let sampleRate ← readBits 20
  let channels ← readBits 3
  let bits ← readBits 5
  let totalSamples ← readBits 36
  let md5 ← readBits 128
  pure ⟨minBlockSize, maxBlockSize, minFrameSize, maxFrameSize, sampleRate, channels + 1, bits + 1,
    totalSamples, md5⟩

/-- Metadata blocks after STREAMINFO, skipped. -/
def skipMetadata : Nat → Bool → Parser Unit
  | _, true => pure ()
  | 0, false => fail "metadata does not end"
  | fuel + 1, false => do
    let last ← readBits 1
    let _type ← readBits 7
    skip (8 * (← readBits 24))
    skipMetadata fuel (last = 1)

/-- The magic and STREAMINFO, and whether it is the last metadata block. -/
def streamHeadP : Parser (Bool × StreamInfo) := do
  check ((← readBits 32) = streamMagic) "not a FLAC stream"
  let last ← readBits 1
  check ((← readBits 7) = 0 && (← readBits 24) = 34) "first metadata block is not STREAMINFO"
  let info ← infoP
  pure (last = 1, info)

def streamP : Parser Stream := do
  let head ← streamHeadP
  let d ← data
  skipMetadata d.size head.1
  let frames ← framesP head.2 d.size #[]
  pure ⟨head.2, frames⟩

end VeriCut.Flac
