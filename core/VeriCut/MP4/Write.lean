import VeriCut.MP4.Parse
import VeriCut.Spec.Audio

/-!
# MP4 muxing (unverified implementation, tested with ffmpeg)

Writes `ftyp`, then `mdat` with every video sample back to back followed by
every audio sample, then `moov`.
Output timing is rebuilt from scratch: decode slot `j` gets `dts = j·dur`, and
the sample's display slot `k` gets `pts = k·dur + delay`, where `delay` is the
smallest shift that keeps every composition offset non-negative. An edit list
hides `delay`, so playback starts at time 0.

The audio track's packets all last `frameLen` samples; its edit list
(`exportAudioClips`) says which media samples play. With audio the movie
timescale is the least common multiple of the two media timescales, so every
edit is exact in it.
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

structure AudioOut where
  /-- Media timescale: the sample rate. -/
  timescale : Nat
  frameLen  : Nat
  entries   : Array ByteArray
  samples   : Array OutSample   -- `disp` unused
  /-- In media samples. -/
  edits     : List VeriCut.Edit
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
def chunks (samples : Array OutSample) : Array (Nat × Nat × Nat) := Id.run do  -- (first sample, count, entry)
  let mut out : Array (Nat × Nat × Nat) := #[]
  for i in [0:samples.size] do
    let e := samples[i]!.entry
    match out.back? with
    | some (f, c, e') => if e' == e then out := out.pop.push (f, c + 1, e) else out := out.push (i, 1, e)
    | none => out := out.push (i, 1, e)
  return out

/-- Byte offset of each sample in the output file, the first at `start`. -/
def sampleStarts (samples : Array OutSample) (start : Nat) : Array Nat :=
  (samples.foldl (fun (acc : Array Nat × Nat) s => (acc.1.push acc.2, acc.2 + s.inband.size + s.size))
    (#[], start)).1

/-- `stsc` and `co64` for samples starting at file offsets `starts`. -/
def chunkBoxes (samples : Array OutSample) (starts : Array Nat) : List ByteArray :=
  let cks := chunks samples
  [fullBox "stsc" 0 0 (be32 cks.size :: (cks.toList.zipIdx.map fun ((_, c, e), k) =>
    be32 (k + 1) ++ be32 c ++ be32 e)),
   fullBox "co64" 0 0 (be32 cks.size :: cks.toList.map fun (f, _, _) => be64 starts[f]!)]

def fits32 (x : Nat) : Bool := x < 2 ^ 32

/-- `elst` with entries `(duration in movie units, media time or -1)` at rate 1. -/
def elstBox (es : List (Nat × Int)) : ByteArray :=
  if es.all fun (d, m) => fits32 d && m < 2 ^ 31 then
    fullBox "elst" 0 0 (be32 es.length :: es.map fun (d, m) => be32 d ++ beI32 m ++ be32 0x10000)
  else
    fullBox "elst" 1 0 (be32 es.length :: es.map fun (d, m) =>
      be64 d ++ be64 (if m < 0 then (m + 2 ^ 64).toNat else m.toNat) ++ be32 0x10000)

/-- `tkhd` for track `id`, enabled and in the movie. -/
def tkhdBox (id duration : Nat) (rest : List ByteArray) : ByteArray :=
  if fits32 duration then fullBox "tkhd" 0 3 ([be32 0, be32 0, be32 id, be32 0, be32 duration] ++ rest)
  else fullBox "tkhd" 1 3 ([be64 0, be64 0, be32 id, be32 0, be64 duration] ++ rest)

def dinfBox : ByteArray := box "dinf" [fullBox "dref" 0 0 [be32 1, fullBox "url " 0 1 []]]

/-- The audio edit list in movie units: zero-length edits dropped, neighbouring
silences merged. -/
def audioElst (a : AudioOut) (movieScale : Nat) : List (Nat × Int) :=
  let k := movieScale / a.timescale
  (a.edits.foldl (fun (acc : List (Nat × Int)) e => match e with
    | .media start len => if len == 0 then acc else (len * k, (start : Int)) :: acc
    | .empty len =>
      if len == 0 then acc else match acc with
        | (d, -1) :: rest => (d + len * k, -1) :: rest
        | _ => (len * k, -1) :: acc) []).reverse

/-- The audio `trak` (track 2), its samples starting at file offset `start`. -/
def audioTrak (a : AudioOut) (movieScale start : Nat) : ByteArray :=
  let n := a.samples.size
  let elst := audioElst a movieScale
  let duration := (elst.map (·.1)).sum
  let stbl := box "stbl" ([fullBox "stsd" 0 0 [be32 a.entries.size, concat a.entries.toList],
    fullBox "stts" 0 0 [be32 1, be32 n, be32 a.frameLen],
    fullBox "stsz" 0 0 (be32 0 :: be32 n :: a.samples.toList.map fun s => be32 s.size)] ++
    chunkBoxes a.samples (sampleStarts a.samples start) ++
    -- Each packet needs the one before it decoded first (AAC's MDCT overlap).
    -- Apple readers also take this group as the sign that the edit list, not
    -- an implicit 2112-sample delay, says where the audio starts.
    [fullBox "sgpd" 1 0 [ascii "roll", be32 2, be32 1, be16 0xFFFF],
     fullBox "sbgp" 0 0 [ascii "roll", be32 1, be32 n, be32 1]])
  let minf := box "minf" [fullBox "smhd" 0 0 [be16 0, be16 0], dinfBox, stbl]
  let hdlr := fullBox "hdlr" 0 0 [be32 0, ascii "soun", zeros 12, ascii "SoundHandler", zeros 1]
  let mdhd := fullBox "mdhd" 0 0 [be32 0, be32 0, be32 a.timescale, be32 (n * a.frameLen), be16 0x55c4, be16 0]
  box "trak" [tkhdBox 2 duration [zeros 8, be16 0, be16 1, be16 0x100, be16 0, identityMatrix, be32 0, be32 0],
    box "edts" [elstBox elst], box "mdia" [mdhd, hdlr, minf]]

def moovBox (t : OutTrack) (audio : Option AudioOut) (mdatDataStart : Nat) : ByteArray :=
  let movieScale := match audio with
    | some a => Nat.lcm t.timescale a.timescale
    | none => t.timescale
  let toMovie := fun d => d * (movieScale / t.timescale)
  let n := t.samples.size
  let duration := n * t.dur
  let dts := fun j => j * t.dur
  let pts := fun j => t.samples[j]!.disp * t.dur
  let delay := (List.range n).foldl (fun m j => max m (dts j - pts j)) 0
  let cts := (Array.range n).map fun j => pts j + delay - dts j
  let needCtts := cts.any (· != 0)
  let syncIdx := (Array.range n).filter fun j => t.samples[j]!.sync
  -- byte offset of each sample inside the output file
  let starts := sampleStarts t.samples mdatDataStart
  let stsd := fullBox "stsd" 0 0 [be32 t.entries.size, concat t.entries.toList]
  let stts := fullBox "stts" 0 0 [be32 1, be32 n, be32 t.dur]
  let cttsRuns := rle cts
  let ctts := fullBox "ctts" 0 0 (be32 cttsRuns.size :: cttsRuns.toList.map fun (c, v) => be32 c ++ be32 v)
  let stss := fullBox "stss" 0 0 (be32 syncIdx.size :: syncIdx.toList.map fun j => be32 (j + 1))
  let stsz := fullBox "stsz" 0 0 (be32 0 :: be32 n :: t.samples.toList.map fun s => be32 (s.inband.size + s.size))
  let stbl := box "stbl" ([stsd, stts] ++ (if needCtts then [ctts] else []) ++
    (if syncIdx.size == n then [] else [stss]) ++ [stsz] ++ chunkBoxes t.samples starts)
  let vmhd := fullBox "vmhd" 0 1 [zeros 8]
  let minf := box "minf" [vmhd, dinfBox, stbl]
  let hdlr := fullBox "hdlr" 0 0 [be32 0, ascii "vide", zeros 12, ascii "VideoHandler", zeros 1]
  let mdhd := fullBox "mdhd" 0 0 [be32 0, be32 0, be32 t.timescale, be32 duration, be16 0x55c4, be16 0]
  let mdia := box "mdia" [mdhd, hdlr, minf]
  let elst := box "edts" [elstBox [(toMovie duration, (delay : Int))]]
  let tkhd := tkhdBox 1 (toMovie duration) [zeros 8,
    be16 0, be16 0, be16 0, be16 0, identityMatrix, be32 t.width, be32 t.height]
  let trak := box "trak" [tkhd, elst, mdia]
  let audioStart := starts.back?.getD mdatDataStart + (t.samples.back?.map fun s => s.inband.size + s.size).getD 0
  let atrak := audio.map (audioTrak · movieScale audioStart)
  let movieDur := max (toMovie duration) ((audio.map fun a => ((audioElst a movieScale).map (·.1)).sum).getD 0)
  let mvhdRest := [be32 0x10000, be16 0x100, zeros 10, identityMatrix, zeros 24,
    be32 (if audio.isSome then 3 else 2)]
  let mvhd := if fits32 movieDur then fullBox "mvhd" 0 0 ([be32 0, be32 0, be32 movieScale, be32 movieDur] ++ mvhdRest)
    else fullBox "mvhd" 1 0 ([be64 0, be64 0, be32 movieScale, be64 movieDur] ++ mvhdRest)
  box "moov" ([mvhd, trak] ++ atrak.toList)

def ftypBox : ByteArray :=
  box "ftyp" [ascii "isom", be32 0x200, ascii "isom", ascii "iso2", ascii "avc1", ascii "mp41"]

/-- Write the file. Sample bytes are copied from `srcs` without inspection, and
contiguous source ranges are merged into single writes. -/
def writeFile (path : System.FilePath) (srcs : Array ByteArray) (t : OutTrack) (audio : Option AudioOut := none) :
    IO Unit := do
  let all := t.samples ++ (audio.map (·.samples)).getD #[]
  let total := all.foldl (fun a s => a + s.inband.size + s.size) 0
  let mdatHdr := be32 1 ++ ascii "mdat" ++ be64 (total + 16)
  let dataStart := ftypBox.size + mdatHdr.size
  IO.FS.withFile path .write fun h => do
    h.write ftypBox
    h.write mdatHdr
    -- merge runs of samples that are contiguous in the same source
    let mut cur : Option (Nat × Nat × Nat) := none  -- (src, start, stop)
    for s in all do
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
    h.write (moovBox t audio dataStart)

end VeriCut.MP4
