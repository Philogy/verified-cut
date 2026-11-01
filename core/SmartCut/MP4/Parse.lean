import SmartCut.MP4.Bytes
import SmartCut.Spec.Stream

/-!
# MP4 / MOV demuxing: sample tables of the video track

Unverified implementation. `tests/` checks it against ffprobe on every sample
file. Only the index (`moov`) is parsed; frame bytes are never inspected.
-/
namespace SmartCut.MP4

/-- A box located in a byte buffer. -/
structure Box where
  type  : String
  start : Nat
  body  : Nat
  stop  : Nat
  deriving Repr, Inhabited

/-- Parse the boxes laid out back to back in `[start, stop)`. -/
def parseBoxes (b : ByteArray) (start stop : Nat) : Except String (Array Box) :=
  go (stop - start + 1) start #[]
where
  go : Nat → Nat → Array Box → Except String (Array Box)
    | 0, _, acc => .ok acc
    | fuel + 1, pos, acc =>
      if pos + 8 > stop then .ok acc else
      let size32 := u32 b pos
      let typ := fourcc b (pos + 4)
      let (hdr, size) :=
        if size32 == 1 then (16, u64 b (pos + 8))
        else if size32 == 0 then (8, stop - pos)
        else (8, size32)
      if size < hdr || pos + size > stop then
        .error s!"malformed box '{typ}' at offset {pos} (size {size})"
      else go fuel (pos + size) (acc.push { type := typ, start := pos, body := pos + hdr, stop := pos + size })

def children (b : ByteArray) (bx : Box) (skip : Nat := 0) : Except String (Array Box) :=
  parseBoxes b (bx.body + skip) bx.stop

def find? (bs : Array Box) (t : String) : Option Box := bs.find? (·.type == t)

def need (bs : Array Box) (t : String) (ctx : String) : Except String Box :=
  match find? bs t with
  | some x => .ok x
  | none => .error s!"missing '{t}' box in {ctx}"

/-- One compressed frame as the container describes it. -/
structure Sample where
  offset : Nat
  size   : Nat
  dts    : Nat
  ctsOff : Int
  dur    : Nat
  sync   : Bool
  deriving Repr, Inhabited, BEq

def Sample.cts (s : Sample) : Int := s.dts + s.ctsOff

structure VideoTrack where
  timescale : Nat
  width     : Nat   -- tkhd 16.16 fixed point, raw
  height    : Nat
  /-- The sample entries inside `stsd` (raw bytes, e.g. an `avc1` box with its `avcC`). -/
  entries   : ByteArray
  codec     : String
  samples   : Array Sample
  deriving Inhabited

/-- Expand a run-length table of (count, value) pairs. -/
def expandRuns (b : ByteArray) (body : Nat) (val : Nat → Int) : Array Int := Id.run do
  let n := u32 b (body + 4)
  let mut out := #[]
  for k in [0:n] do
    let o := body + 8 + 8 * k
    let cnt := u32 b o
    let v := val (o + 4)
    for _ in [0:cnt] do out := out.push v
  return out

def parseTrack (b : ByteArray) (trak : Box) : Except String (Option VideoTrack) := do
  let tk ← children b trak
  let mdia ← need tk "mdia" "trak"
  let md ← children b mdia
  let hdlr ← need md "hdlr" "mdia"
  if fourcc b (hdlr.body + 8) != "vide" then return none
  let mdhd ← need md "mdhd" "mdia"
  let timescale := if u8 b mdhd.body == 1 then u32 b (mdhd.body + 20) else u32 b (mdhd.body + 12)
  let tkhd ← need tk "tkhd" "trak"
  let minf ← need md "minf" "mdia"
  let stbl ← need (← children b minf) "stbl" "minf"
  let st ← children b stbl
  -- sample descriptions
  let stsd ← need st "stsd" "stbl"
  if u32 b (stsd.body + 4) != 1 then throw "source with several sample descriptions is not supported"
  let entries := b.extract (stsd.body + 8) stsd.stop
  let codec := fourcc b (stsd.body + 12)
  -- sizes
  let stsz ← need st "stsz" "stbl"
  let n := u32 b (stsz.body + 8)
  let fixed := u32 b (stsz.body + 4)
  let sizes := (Array.range n).map fun i => if fixed != 0 then fixed else u32 b (stsz.body + 12 + 4 * i)
  -- chunk offsets
  let chunkOffs ← match find? st "stco", find? st "co64" with
    | some x, _ => pure <| (Array.range (u32 b (x.body + 4))).map fun i => u32 b (x.body + 8 + 4 * i)
    | none, some x => pure <| (Array.range (u32 b (x.body + 4))).map fun i => u64 b (x.body + 8 + 8 * i)
    | none, none => throw "missing stco/co64"
  -- sample-to-chunk
  let stsc ← need st "stsc" "stbl"
  let nsc := u32 b (stsc.body + 4)
  let scEntry := fun k => (u32 b (stsc.body + 8 + 12 * k), u32 b (stsc.body + 12 + 12 * k))
  let mut offsets : Array Nat := #[]
  let mut si := 0
  for c in [0:chunkOffs.size] do
    -- last stsc entry whose first_chunk ≤ c + 1
    let mut spc := 0
    for k in [0:nsc] do
      let (fc, s) := scEntry k
      if fc ≤ c + 1 then spc := s
    let mut off := chunkOffs[c]!
    for _ in [0:spc] do
      if si < n then
        offsets := offsets.push off
        off := off + sizes[si]!
        si := si + 1
  if offsets.size != n then throw s!"sample-to-chunk table covers {offsets.size} of {n} samples"
  -- timing
  let stts ← need st "stts" "stbl"
  let durs := expandRuns b stts.body fun o => (u32 b o : Int)
  if durs.size != n then throw "stts does not cover all samples"
  let ctts := match find? st "ctts" with
    | some x =>
      let v1 := u8 b x.body == 1
      expandRuns b x.body fun o => if v1 then i32 b o else (u32 b o : Int)
    | none => Array.replicate n 0
  if ctts.size != n then throw "ctts does not cover all samples"
  -- sync samples (absent table = every sample is a sync sample)
  let syncs : Array Bool := match find? st "stss" with
    | some x => Id.run do
      let mut a := Array.replicate n false
      for k in [0:u32 b (x.body + 4)] do
        let idx := u32 b (x.body + 8 + 4 * k)
        if 1 ≤ idx && idx ≤ n then a := a.set! (idx - 1) true
      return a
    | none => Array.replicate n true
  let mut samples := #[]
  let mut dts := 0
  for i in [0:n] do
    let d := durs[i]!.toNat
    samples := samples.push { offset := offsets[i]!, size := sizes[i]!, dts, ctsOff := ctts[i]!,
                              dur := d, sync := syncs[i]! }
    dts := dts + d
  return some { timescale, width := u32 b (tkhd.stop - 8), height := u32 b (tkhd.stop - 4),
                entries, codec, samples }

/-- The first video track of a file. -/
def parseVideo (b : ByteArray) : Except String VideoTrack := do
  let top ← parseBoxes b 0 b.size
  let moov ← need top "moov" "file"
  for t in (← children b moov) do
    if t.type == "trak" then
      if let some v ← parseTrack b t then return v
  throw "no video track"

/-- H.264 parameter sets from an `avc1` sample entry's `avcC`, as in-band NAL
units (each prefixed by its length in `lengthSize` bytes, like sample data).
Returns `(lengthSize, bytes)`. -/
def avcParamSets (entries : ByteArray) : Except String (Nat × ByteArray) := do
  if fourcc entries 4 != "avc1" then throw s!"re-encoding needs avc1 (H.264), found {fourcc entries 4}"
  let kids ← parseBoxes entries 86 (u32 entries 0)
  let c ← need kids "avcC" "avc1"
  let o := c.body
  let lenSize := u8 entries (o + 4) % 4 + 1
  let mut pos := o + 6
  let mut out := ByteArray.empty
  for _ in [0:u8 entries (o + 5) % 32] do
    let l := u16 entries pos
    out := out ++ be lenSize l ++ entries.extract (pos + 2) (pos + 2 + l)
    pos := pos + 2 + l
  let npps := u8 entries pos
  pos := pos + 1
  for _ in [0:npps] do
    let l := u16 entries pos
    out := out ++ be lenSize l ++ entries.extract (pos + 2) (pos + 2 + l)
    pos := pos + 2 + l
  return (lenSize, out)

/-- Display position (0-based rank by composition time) of each sample. -/
def displayRanks (t : VideoTrack) : Array Nat := Id.run do
  let order := (Array.range t.samples.size).qsort fun i j =>
    t.samples[i]!.cts < t.samples[j]!.cts || (t.samples[i]!.cts == t.samples[j]!.cts && i < j)
  let mut rank := Array.replicate t.samples.size 0
  for k in [0:order.size] do rank := rank.set! order[k]! k
  return rank

/-- **The bridge to the verified model.** Each packet's data is its sample
index. A sync sample depends on nothing; every other sample depends on the
decoder state after the previous sample. Decoder state here means the whole
decoded picture buffer, and that is exactly what a sync (IDR) sample resets.
Trusted assumption: `stss` marks only samples that reset the decoder (closed
GOPs). The ffmpeg tests check it on every sample file. -/
def toStream (t : VideoTrack) : SmartCut.Stream Nat :=
  let ranks := displayRanks t
  (List.range t.samples.size).map fun i =>
    { data := i, refs := if t.samples[i]!.sync then [] else [i - 1], pts := ranks[i]! }

end SmartCut.MP4
