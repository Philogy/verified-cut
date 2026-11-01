import VeriCut.MP4.Parse

/-!
# MP4 muxing (unverified implementation, tested with ffmpeg)

Writes `ftyp`, then `mdat` with every output sample back to back, then `moov`.
Output timing is rebuilt from scratch: decode slot `j` gets `dts = j·dur`, and
the sample's display slot `k` gets `pts = k·dur + delay`, where `delay` is the
smallest shift that keeps every composition offset non-negative. An edit list
hides `delay`, so playback starts at time 0.
-/
namespace VeriCut.MP4

/-- One sample to write. `src` indexes the input buffers. `entry` is the
1-based sample-description index. `disp` is its display slot in the output. -/
structure OutSample where
  /-- Bytes written before the sample (in-band parameter sets at a switch), usually empty. -/
  inband : ByteArray := ByteArray.empty
  src    : Nat
  offset : Nat
  size   : Nat
  sync   : Bool
  entry  : Nat
  disp   : Nat
  deriving Inhabited

structure OutTrack where
  timescale : Nat
  dur       : Nat
  width     : Nat
  height    : Nat
  entries   : Array ByteArray   -- sample entries, in description-index order
  samples   : Array OutSample   -- decode order
  deriving Inhabited

/-- Run-length encode a list of values. -/
def rle (xs : Array Nat) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  for x in xs do
    match out.back? with
    | some (c, v) => if v == x then out := out.pop.push (c + 1, v) else out := out.push (1, x)
    | none => out := out.push (1, x)
  return out

def identityMatrix : ByteArray :=
  concat [be32 0x10000, be32 0, be32 0, be32 0, be32 0x10000, be32 0, be32 0, be32 0, be32 0x40000000]

/-- Chunks: maximal runs of consecutive samples sharing a description. -/
def chunks (t : OutTrack) : Array (Nat × Nat × Nat) := Id.run do  -- (first sample, count, entry)
  let mut out : Array (Nat × Nat × Nat) := #[]
  for i in [0:t.samples.size] do
    let e := t.samples[i]!.entry
    match out.back? with
    | some (f, c, e') => if e' == e then out := out.pop.push (f, c + 1, e) else out := out.push (i, 1, e)
    | none => out := out.push (i, 1, e)
  return out

def moovBox (t : OutTrack) (mdatDataStart : Nat) : ByteArray :=
  let n := t.samples.size
  let duration := n * t.dur
  let dts := fun j => j * t.dur
  let pts := fun j => t.samples[j]!.disp * t.dur
  let delay := (List.range n).foldl (fun m j => max m (dts j - pts j)) 0
  let cts := (Array.range n).map fun j => pts j + delay - dts j
  let needCtts := cts.any (· != 0)
  let syncIdx := (Array.range n).filter fun j => t.samples[j]!.sync
  -- byte offset of each sample inside the output file
  let starts := (t.samples.foldl (fun (acc : Array Nat × Nat) s => (acc.1.push acc.2, acc.2 + s.inband.size + s.size))
    (#[], mdatDataStart)).1
  let cks := chunks t
  let stsd := fullBox "stsd" 0 0 [be32 t.entries.size, concat t.entries.toList]
  let stts := fullBox "stts" 0 0 [be32 1, be32 n, be32 t.dur]
  let cttsRuns := rle cts
  let ctts := fullBox "ctts" 0 0 (be32 cttsRuns.size :: cttsRuns.toList.map fun (c, v) => be32 c ++ be32 v)
  let stss := fullBox "stss" 0 0 (be32 syncIdx.size :: syncIdx.toList.map fun j => be32 (j + 1))
  let stsz := fullBox "stsz" 0 0 (be32 0 :: be32 n :: t.samples.toList.map fun s => be32 (s.inband.size + s.size))
  let stsc := fullBox "stsc" 0 0 (be32 cks.size :: (cks.toList.zipIdx.map fun ((_, c, e), k) =>
    be32 (k + 1) ++ be32 c ++ be32 e))
  let co64 := fullBox "co64" 0 0 (be32 cks.size :: cks.toList.map fun (f, _, _) => be64 starts[f]!)
  let stbl := box "stbl" ([stsd, stts] ++ (if needCtts then [ctts] else []) ++
    (if syncIdx.size == n then [] else [stss]) ++ [stsz, stsc, co64])
  let vmhd := fullBox "vmhd" 0 1 [zeros 8]
  let dinf := box "dinf" [fullBox "dref" 0 0 [be32 1, fullBox "url " 0 1 []]]
  let minf := box "minf" [vmhd, dinf, stbl]
  let hdlr := fullBox "hdlr" 0 0 [be32 0, ascii "vide", zeros 12, ascii "VideoHandler", zeros 1]
  let mdhd := fullBox "mdhd" 0 0 [be32 0, be32 0, be32 t.timescale, be32 duration, be16 0x55c4, be16 0]
  let mdia := box "mdia" [mdhd, hdlr, minf]
  let elst := box "edts" [fullBox "elst" 0 0 [be32 1, be32 duration, be32 delay, be32 0x10000]]
  let tkhd := fullBox "tkhd" 0 3 [be32 0, be32 0, be32 1, be32 0, be32 duration, zeros 8,
    be16 0, be16 0, be16 0, be16 0, identityMatrix, be32 t.width, be32 t.height]
  let trak := box "trak" [tkhd, elst, mdia]
  let mvhd := fullBox "mvhd" 0 0 [be32 0, be32 0, be32 t.timescale, be32 duration, be32 0x10000,
    be16 0x100, zeros 10, identityMatrix, zeros 24, be32 2]
  box "moov" [mvhd, trak]

def ftypBox : ByteArray :=
  box "ftyp" [ascii "isom", be32 0x200, ascii "isom", ascii "iso2", ascii "avc1", ascii "mp41"]

/-- Write the file. Sample bytes are copied from `srcs` without inspection, and
contiguous source ranges are merged into single writes. -/
def writeFile (path : System.FilePath) (srcs : Array ByteArray) (t : OutTrack) : IO Unit := do
  let total := t.samples.foldl (fun a s => a + s.inband.size + s.size) 0
  let mdatHdr := be32 1 ++ ascii "mdat" ++ be64 (total + 16)
  let dataStart := ftypBox.size + mdatHdr.size
  IO.FS.withFile path .write fun h => do
    h.write ftypBox
    h.write mdatHdr
    -- merge runs of samples that are contiguous in the same source
    let mut cur : Option (Nat × Nat × Nat) := none  -- (src, start, stop)
    for s in t.samples do
      if s.inband.size > 0 then
        if let some (src, a, z) := cur then h.write (srcs[src]!.extract a z)
        cur := none
        h.write s.inband
      match cur with
      | some (src, a, z) =>
        if src == s.src && z == s.offset then cur := some (src, a, z + s.size)
        else
          h.write (srcs[src]!.extract a z)
          cur := some (s.src, s.offset, s.offset + s.size)
      | none => cur := some (s.src, s.offset, s.offset + s.size)
    if let some (src, a, z) := cur then h.write (srcs[src]!.extract a z)
    h.write (moovBox t dataStart)

end VeriCut.MP4
