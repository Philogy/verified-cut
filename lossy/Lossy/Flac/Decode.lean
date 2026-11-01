import Lossy.Reader
import Lossy.Flac.Encode

/-! Reads back what `encode` writes. -/

namespace Lossy.Flac
open Reader

def readBody (width n t : Nat) : Reader Sub :=
  if t = 0 then do
    return .const (← int width)
  else if t = 1 then do
    return .verbatim (← many (int width) n)
  else if 8 ≤ t ∧ t ≤ 12 then do
    let warm ← many (int width) (t - 8)
    expect 2 0
    expect 4 0
    let k ← nat 4
    if k = 15 then fail else do
    let res ← many (Reader.rice k) (n - (t - 8))
    return .fixed (t - 8) warm k res
  else fail

def readWasted : Reader Nat := do
  if (← bit) then return (← Reader.unary) + 1 else return 0

def readSub (bps n : Nat) : Reader (Nat × Sub) := do
  expect 1 0
  let t ← nat 6
  let w ← readWasted
  let s ← readBody (bps - w) n t
  return (w, s)

def readUtf8 : Reader Nat := do
  let b ← nat 8
  if b < 128 then return b
  else if b < 224 then do
    let c ← nat 8
    return (b - 192) * 64 + (c - 128)
  else if b < 240 then do
    let c ← nat 8
    let d ← nat 8
    return ((b - 224) * 64 + (c - 128)) * 64 + (d - 128)
  else do
    let c ← nat 8
    let d ← nat 8
    let e ← nat 8
    return (((b - 240) * 64 + (c - 128)) * 64 + (d - 128)) * 64 + (e - 128)

/-- Header, its CRC and subframes: the block size minus one and the subframes. -/
def readFrameBody (bps ch : Nat) : Reader (Nat × List (Nat × Sub)) := do
  expect 16 0xFFF8
  expect 8 0x70
  expect 4 (ch - 1)
  expect 4 0
  let _ ← readUtf8
  let n ← nat 16
  let _ ← nat 8
  let subs ← many (readSub bps (n + 1)) ch
  return (n, subs)

def samplesOf (n : Nat) (subs : List (Nat × Sub)) : List (List Int) :=
  subs.map fun (w, s) => (s.samples n).map (· * 2 ^ w)

def readFrame (bps ch : Nat) : Reader (List (List Int)) := do
  let (n, subs) ← readFrameBody bps ch
  align
  let _ ← nat 16
  return samplesOf (n + 1) subs

/-- Rate, channels, bits per sample, samples per channel. -/
def readHeader : Reader (Nat × Nat × Nat × Nat) := do
  expect 32 0x664C6143
  expect 8 0x80
  expect 24 34
  expect 16 blockSize
  expect 16 blockSize
  expect 24 0
  expect 24 0
  let rate ← nat 20
  let ch ← nat 3
  let bps ← nat 5
  let n ← nat 36
  expect 128 0
  return (rate, ch + 1, bps + 1, n)

/-- Appends each block's channels to the channels so far. -/
def join (ch : Nat) (blocks : List (List (List Int))) : List (Array Int) :=
  blocks.foldl (fun acc b => List.zipWith (fun c s => c ++ s.toArray) acc b) (List.replicate ch #[])

/-- `quantize`, a block at a time: `quantize` itself finds the block's peak
again for every sample. Equal for valid input (`quantizeBlocks_eq`). -/
def quantizeBlocks (q : Nat) (x : Pcm) : Pcm :=
  ⟨x.rate, x.bits, join x.chans.length ((List.range (frameCount x.length)).map fun f =>
    let s := shift q x f
    (block x f).map (·.map (roundTo x.bits s)))⟩

def readStream : Reader Pcm := do
  let (rate, ch, bps, n) ← readHeader
  let blocks ← many (readFrame bps ch) (frameCount n)
  return ⟨rate, bps, join ch blocks⟩

end Flac

def decode (a : ByteArray) : Option Pcm := (Flac.readStream.run a 0).map (·.1)

end Lossy
