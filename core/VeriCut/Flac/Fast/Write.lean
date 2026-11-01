import VeriCut.Flac.Fast.Bits
import VeriCut.Flac.Write

/-!
`writeFrame` on the fast `Writer`. Same structure as `Flac/Write.lean`, so it writes the same
bytes (`Fast.writeFrame_eq`); only Rice codes are written differently, in one write.
-/

namespace VeriCut.Flac.Fast


/-- `u >>> k` zeros, a one, then the low `k` bits of `u` (`u = zigzag v`); one write when it fits. -/
def writeRice (k : Nat) (w : Writer) (v : Int) : Writer :=
  let u := zigzag v
  let q := u >>> k
  if q + 1 + k ≤ 56 then
    let m : UInt64 := 1 <<< k.toUInt64
    w.write (q + 1 + k) ((u.toUInt64 &&& (m - 1)) + m).toNat
  else ((w.zeros q).write 1 1).write k u

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
  let size := blockSizeCode h.blockSize
  let w := ((((w.write 14 0x3FFE).write 1 0).write 1 0).write 4 size.1)
  let w := (w.write 4 ((codeOf sampleRateCodes h.sampleRate).getD 0)).write 4 h.channels.code
  let w := (w.write 3 ((codeOf bitsPerSampleCodes h.bitsPerSample).getD 0)).write 1 0
  let w := (codedBytes h.number).foldl (·.write 8 ·) w
  w.write size.2 (h.blockSize - 1)

def writeFrame (f : Frame) : ByteArray :=
  let w := writeHeader f.header .empty
  let w := w.write 8 (crc8 w.bytes)
  let w := (f.subframes.zipIdx.foldl (fun w (sf, c) => writeSubframe (f.header.subframeBits c) w sf) w).align
  (w.write 16 (crc16 w.bytes)).bytes

end VeriCut.Flac.Fast
