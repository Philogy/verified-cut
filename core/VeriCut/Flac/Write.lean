import VeriCut.Flac.Bits
import VeriCut.Flac.Crc
import VeriCut.Flac.Codes

/-!
Writing a `Stream` as bytes. The inverse of `Parse.lean`.
-/

namespace VeriCut.Flac

open Writer

def writeRice (k : Nat) (w : Writer) (v : Int) : Writer :=
  let u := zigzag v
  ((w.zeros (u >>> k)).write 1 1).write k u

def writePartition (paramBits : Nat) (w : Writer) (p : Partition) : Writer :=
  match p.coding with
  | .rice k => p.values.foldl (writeRice k) (w.write paramBits k)
  | .raw bits => p.values.foldl (·.writeSigned bits ·) ((w.write paramBits (2 ^ paramBits - 1)).write 5 bits)

def writeResidual (r : Residual) (w : Writer) : Writer :=
  let w := (w.write 2 (if r.wide then 1 else 0)).write 4 r.order
  r.parts.foldl (writePartition (if r.wide then 5 else 4)) w

def writeSamples (bits : Nat) (w : Writer) (s : Array Int) : Writer :=
  s.foldl (·.writeSigned bits ·) w

def writeBody (bits : Nat) (w : Writer) : Body → Writer
  | .constant v => w.writeSigned bits v
  | .verbatim s => writeSamples bits w s
  | .fixed warmup r => writeResidual r (writeSamples bits w warmup)
  | .lpc precision shift coefs warmup r =>
    let w := ((writeSamples bits w warmup).write 4 (precision - 1)).writeSigned 5 shift
    writeResidual r (writeSamples precision w coefs)

def writeSubframe (bits : Nat) (w : Writer) (sf : Subframe) : Writer :=
  let w := (w.write 1 0).write 6 sf.body.typeCode
  let w := if sf.wasted = 0 then w.write 1 0 else ((w.write 1 1).zeros (sf.wasted - 1)).write 1 1
  writeBody (bits - sf.wasted) w sf.body

def writeHeader (h : Header) (w : Writer) : Writer :=
  let (sizeCode, sizeBits) := match codeOf blockSizeCodes h.blockSize with
    | some c => (c, 0)
    | none => if h.blockSize ≤ 256 then (6, 8) else (7, 16)
  let w := ((((w.write 14 0x3FFE).write 1 0).write 1 0).write 4 sizeCode)
  let w := (w.write 4 ((codeOf sampleRateCodes h.sampleRate).getD 0)).write 4 h.channels.code
  let w := (w.write 3 ((codeOf bitsPerSampleCodes h.bitsPerSample).getD 0)).write 1 0
  let w := (codedBytes h.number).foldl (·.write 8 ·) w
  w.write sizeBits (h.blockSize - 1)

def writeFrame (f : Frame) : ByteArray :=
  let w := writeHeader f.header .empty
  let w := w.write 8 (crc8 w.bytes)
  let w := (f.subframes.zipIdx.foldl (fun w (sf, c) => writeSubframe (f.header.subframeBits c) w sf) w).align
  (w.write 16 (crc16 w.bytes)).bytes

def writeInfo (i : StreamInfo) (w : Writer) : Writer :=
  let w := (((w.write 16 i.minBlockSize).write 16 i.maxBlockSize).write 24 i.minFrameSize).write 24 i.maxFrameSize
  let w := (((w.write 20 i.sampleRate).write 3 (i.channels - 1)).write 5 (i.bitsPerSample - 1)).write 36 i.totalSamples
  w.write 128 i.md5

/-- Magic, a single STREAMINFO block, then the frames. -/
def writeStream (info : StreamInfo) (frames : Array ByteArray) : ByteArray :=
  let w := ((((Writer.empty.write 32 streamMagic).write 1 1).write 7 0).write 24 34)
  frames.foldl (· ++ ·) (writeInfo info w).bytes

end VeriCut.Flac
