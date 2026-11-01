import VeriCut.MP4.Bytes
import VeriCut.Spec.Stream

/-!
# MP4 / MOV demuxing: sample tables of the video and audio tracks

Unverified implementation. `tests/` checks it against ffprobe on every sample
file. Besides the index (`moov`), only the NAL unit headers of `stss` samples
are read, to confirm they are IDR pictures.
-/
namespace VeriCut.MP4

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
  /-- Listed in `stss`. Encoders also list open-GOP I-frames there, whose
  leading pictures reference the previous GOP. -/
  keyframe : Bool
  /-- Decoding can start here: a keyframe that is an IDR picture (H.264/HEVC),
  or any keyframe of another codec. This is what the bridge trusts. -/
  sync   : Bool
  deriving Repr, Inhabited, BEq

def Sample.cts (s : Sample) : Int := s.dts + s.ctsOff

/-- Where a track's media starts on the movie timeline: its first edit that
shows media, after any leading empty edits. Later edits are ignored. -/
structure TrackEdit where
  /-- Empty time before the media, in movie timescale units. -/
  empty     : Nat := 0
  /-- The media time shown first, in media timescale units. -/
  mediaTime : Int := 0
  deriving Repr, Inhabited

/-- The track's `elst` (no edit list: media from time 0). -/
def parseEdit (b : ByteArray) (tk : Array Box) : Except String TrackEdit := do
  let some edts := find? tk "edts" | return {}
  let some elst := find? (← children b edts) "elst" | return {}
  let v1 := u8 b elst.body == 1
  let w := if v1 then 20 else 12
  let mut empty := 0
  for k in [0:u32 b (elst.body + 4)] do
    let o := elst.body + 8 + w * k
    let (dur, mt) := if v1 then (u64 b o, (u64 b (o + 8) : Int) - if u64 b (o + 8) ≥ 2 ^ 63 then 2 ^ 64 else 0)
                     else (u32 b o, i32 b (o + 4))
    if mt == -1 then empty := empty + dur
    else return { empty, mediaTime := mt }
  return { empty }

structure VideoTrack where
  timescale : Nat
  width     : Nat   -- tkhd 16.16 fixed point, raw
  height    : Nat
  /-- The sample entries inside `stsd` (raw bytes, e.g. an `avc1` box with its `avcC`). -/
  entries   : ByteArray
  codec     : String
  samples   : Array Sample
  edit      : TrackEdit := {}
  deriving Inhabited

/-- One audio packet. -/
structure AudioSample where
  offset : Nat
  size   : Nat
  dur    : Nat
  deriving Repr, Inhabited

structure AudioTrack where
  /-- Media timescale. For the audio we copy this is the sample rate. -/
  timescale  : Nat
  sampleRate : Nat
  channels   : Nat
  /-- The sample entries inside `stsd` (raw bytes, e.g. an `mp4a` box with its `esds`). -/
  entries    : ByteArray
  codec      : String
  /-- MPEG-4 audio object type from the `esds` (2 = AAC-LC), 0 if none. -/
  objectType : Nat
  samples    : Array AudioSample
  edit       : TrackEdit
  deriving Inhabited

/-- A file's movie timescale (`mvhd`), first video track and first audio track. -/
structure Movie where
  timescale : Nat
  video     : VideoTrack
  audio     : Option AudioTrack
  deriving Inhabited

/-- NAL unit length size of an H.264 (`avcC`) or HEVC (`hvcC`) sample entry,
with the IDR test for one NAL header byte. `none` for other codecs. -/
def nalFormat (entries : ByteArray) : Except String (Option (Nat × (UInt8 → Bool))) := do
  let codec := fourcc entries 4
  let isAvc := codec == "avc1" || codec == "avc3"
  if !isAvc && codec != "hvc1" && codec != "hev1" then return none
  let kids ← parseBoxes entries 86 (u32 entries 0)
  if isAvc then
    let c ← need kids "avcC" codec
    return some (u8 entries (c.body + 4) % 4 + 1, fun h => h &&& 0x1f == 5)
  else
    let c ← need kids "hvcC" codec
    -- IDR_W_RADL, IDR_N_LP. CRA and BLA pictures may have RASL leading pictures
    -- that reference the previous GOP, so they don't count.
    return some (u8 entries (c.body + 21) % 4 + 1, fun h => let t := (h >>> 1) &&& 0x3f; t == 19 || t == 20)

/-- Whether the sample at `[offset, offset + size)` holds an IDR NAL unit
(length-prefixed NAL units, as in MP4 sample data). -/
def hasIdr (b : ByteArray) (lenSize : Nat) (isIdr : UInt8 → Bool) (offset size : Nat) : Bool :=
  go (size + 1) offset
where
  go : Nat → Nat → Bool
    | 0, _ => false
    | fuel + 1, pos =>
      if pos + lenSize + 1 > offset + size || offset + size > b.size then false else
      let len := (List.range lenSize).foldl (fun acc k => acc * 256 + u8 b (pos + k)) 0
      if len == 0 then false
      else isIdr (b.get! (pos + lenSize)) || go fuel (pos + lenSize + len)

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

/-- Offsets, sizes and durations of every sample of a sample table. -/
def sampleTable (b : ByteArray) (st : Array Box) : Except String (Array Nat × Array Nat × Array Int) := do
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
  return (offsets, sizes, durs)

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
  let (offsets, sizes, durs) ← sampleTable b st
  let n := sizes.size
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
  let fmt ← nalFormat entries
  let mut samples := #[]
  let mut dts := 0
  for i in [0:n] do
    let d := durs[i]!.toNat
    samples := samples.push { offset := offsets[i]!, size := sizes[i]!, dts, ctsOff := ctts[i]!,
                              dur := d, keyframe := syncs[i]!,
                              sync := syncs[i]! && fmt.all fun (ls, idr) => hasIdr b ls idr offsets[i]! sizes[i]! }
    dts := dts + d
  return some { timescale, width := u32 b (tkhd.stop - 8), height := u32 b (tkhd.stop - 4),
                entries, codec, samples, edit := ← parseEdit b tk }

/-- A descriptor of an `esds` box at `o`: its tag, and where its payload starts and ends. -/
def descriptor (b : ByteArray) (o : Nat) : Nat × Nat × Nat := Id.run do
  let mut len := 0
  let mut p := o + 1
  for _ in [0:4] do
    let x := u8 b p
    len := len * 128 + x % 128
    p := p + 1
    if x < 128 then break
  return (u8 b o, p, p + len)

/-- The MPEG-4 audio object type in an `esds` box (2 = AAC-LC), 0 if not found. -/
def esdsObjectType (b : ByteArray) (esds : Box) : Nat := Id.run do
  let (t3, p3, _) := descriptor b (esds.body + 4)
  if t3 != 3 then return 0
  let flags := u8 b (p3 + 2)
  let mut p := p3 + 3
  if flags &&& 0x80 != 0 then p := p + 2
  if flags &&& 0x40 != 0 then p := p + 1 + u8 b p
  if flags &&& 0x20 != 0 then p := p + 2
  let (t4, p4, _) := descriptor b p
  if t4 != 4 then return 0
  let (t5, p5, _) := descriptor b (p4 + 13)
  if t5 != 5 then return 0
  let aot := u8 b p5 / 8
  return if aot == 31 then 32 + (u8 b p5 % 8) * 8 + u8 b (p5 + 1) / 32 else aot

def parseAudioTrack (b : ByteArray) (trak : Box) : Except String (Option AudioTrack) := do
  let tk ← children b trak
  let mdia ← need tk "mdia" "trak"
  let md ← children b mdia
  let hdlr ← need md "hdlr" "mdia"
  if fourcc b (hdlr.body + 8) != "soun" then return none
  let mdhd ← need md "mdhd" "mdia"
  let timescale := if u8 b mdhd.body == 1 then u32 b (mdhd.body + 20) else u32 b (mdhd.body + 12)
  let minf ← need md "minf" "mdia"
  let st ← children b (← need (← children b minf) "stbl" "minf")
  let stsd ← need st "stsd" "stbl"
  if u32 b (stsd.body + 4) != 1 then throw "audio with several sample descriptions is not supported"
  let e := stsd.body + 8
  let codec := fourcc b (e + 4)
  -- QuickTime sound description version 1 has 16 more bytes before the child boxes.
  let ver := u16 b (e + 16)
  let kids := (children b ⟨codec, e, e + 36 + (if ver == 1 then 16 else 0), e + u32 b e⟩).toOption.getD #[]
  let esds := (find? kids "esds").orElse fun _ =>
    (find? kids "wave").bind fun w => (children b w).toOption.bind (find? · "esds")
  let (offsets, sizes, durs) ← sampleTable b st
  return some {
    timescale, sampleRate := u32 b (e + 32) / 65536, channels := u16 b (e + 24),
    entries := b.extract e stsd.stop, codec,
    objectType := (esds.map (esdsObjectType b)).getD 0,
    samples := (Array.range sizes.size).map fun i => ⟨offsets[i]!, sizes[i]!, durs[i]!.toNat⟩,
    edit := ← parseEdit b tk }

/-- The movie timescale, first video track and first audio track of a file. -/
def parseMovie (b : ByteArray) : Except String Movie := do
  let top ← parseBoxes b 0 b.size
  let moov ← need top "moov" "file"
  let kids ← children b moov
  let mvhd ← need kids "mvhd" "moov"
  let timescale := if u8 b mvhd.body == 1 then u32 b (mvhd.body + 20) else u32 b (mvhd.body + 12)
  let mut video := none
  let mut audio := none
  for t in kids do
    if t.type == "trak" then
      if video.isNone then video ← parseTrack b t
      if audio.isNone then audio ← parseAudioTrack b t
  let some v := video | throw "no video track"
  return { timescale, video := v, audio }

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
Trusted assumption: an IDR picture (or, for codecs without NAL units, an
`stss` sample) resets the decoder. `parseTrack` drops open-GOP keyframes from
`sync`. The ffmpeg tests check it on every sample file. -/
def toStream (t : VideoTrack) : VeriCut.Stream Nat :=
  let ranks := displayRanks t
  (List.range t.samples.size).map fun i =>
    { data := i, refs := if t.samples[i]!.sync then [] else [i - 1], pts := ranks[i]! }

end VeriCut.MP4
