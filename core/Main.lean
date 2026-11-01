import Lean.Data.Json
import VeriCut.Impl.Planner
import VeriCut.Impl.Export
import VeriCut.Spec.Audio
import VeriCut.MP4.Write

/-!
# `vericut` command line

    vericut probe  <file>                      frame table as JSON
    vericut plan   <timeline.json>             plan as JSON (no output written)
    vericut export <timeline.json> <out.mp4>   [--encoder NAME] [--encoder-args "..."]
                                                [--ffmpeg PATH] [--strict] [--no-audio]

timeline.json: {"clips": [{"path": "a.mp4", "in": 0, "out": 120}, ...]}
`in`/`out` are display frame numbers, half-open, 0-based.
-/

open Lean VeriCut VeriCut.MP4

structure Clip where
  path : String
  inF  : Nat
  outF : Nat
  deriving Inhabited

def parseTimeline (j : Json) : Except String (Array Clip) := do
  let clips ← (← j.getObjVal? "clips").getArr?
  clips.mapM fun c => do
    pure { path := ← (← c.getObjVal? "path").getStr?,
           inF := ← (← c.getObjVal? "in").getNat?, outF := ← (← c.getObjVal? "out").getNat? }

def liftE {α} (ctx : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{ctx}: {e}")

def loadTrack (path : String) : IO (ByteArray × VideoTrack) := do
  let b ← IO.FS.readBinFile path
  let t ← liftE path (parseVideo b)
  if t.samples.size == 0 then throw (IO.userError s!"{path}: no video samples")
  pure (b, t)

/-- Read a file with its audio track (`parseMovie`). -/
def loadMovie (path : String) : IO (ByteArray × Movie) := do
  let b ← IO.FS.readBinFile path
  let m ← liftE path (parseMovie b)
  if m.video.samples.size == 0 then throw (IO.userError s!"{path}: no video samples")
  pure (b, m)

def segJson : Segment → Json
  | .copy ks => Json.mkObj [("kind", "copy"), ("frames", toJson ks.length),
      ("first", toJson ks.head?), ("last", toJson ks.getLast?)]
  | .encode ks => Json.mkObj [("kind", "encode"), ("frames", toJson ks.length),
      ("first", toJson ks.head?), ("last", toJson ks.getLast?)]

def probe (path : String) : IO Unit := do
  let (_, t) ← loadTrack path
  let ranks := displayRanks t
  let frames := (Array.range t.samples.size).map fun i =>
    let s := t.samples[i]!
    Json.mkObj [("offset", toJson s.offset), ("size", toJson s.size), ("dts", toJson s.dts),
      ("cts", toJson s.cts), ("dur", toJson s.dur), ("keyframe", toJson s.keyframe), ("sync", toJson s.sync), ("display", toJson ranks[i]!)]
  IO.println <| Json.compress <| Json.mkObj [("codec", toJson t.codec), ("timescale", toJson t.timescale),
    ("frames", Json.arr frames)]

/-- Check a clip's range and compute the plan of its stream `s` (`toStream t`,
up to packet data). -/
def planClip {α} (c : Clip) (t : VideoTrack) (s : VeriCut.Stream α) :
    IO (List Segment) := do
  let n := t.samples.size
  unless c.inF < c.outF && c.outF ≤ n do
    throw (IO.userError s!"{c.path}: bad range [{c.inF}, {c.outF}) for {n} frames")
  unless t.samples[0]!.sync do throw (IO.userError s!"{c.path}: first sample is not a sync sample")
  pure (plan s ⟨c.inF, c.outF⟩)

structure Opts where
  encoder : Option String := none
  encoderArgs : Array String := #[]
  ffmpeg : String := "ffmpeg"
  strict : Bool := false
  /-- How re-encoded segments carry their parameter sets: `stsd` = one sample
  description per distinct set (QuickTime/AVFoundation native), `inband` = one
  description, new SPS/PPS prepended at each switch. -/
  inband : Bool := false
  /-- Drop the audio instead of copying it. -/
  noAudio : Bool := false

def parseOpts : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--encoder" :: v :: r, o => parseOpts r { o with encoder := some v }
  | "--encoder-args" :: v :: r, o =>
    parseOpts r { o with encoderArgs := (v.splitOn " ").filter (· != "") |>.toArray }
  | "--ffmpeg" :: v :: r, o => parseOpts r { o with ffmpeg := v }
  | "--strict" :: r, o => parseOpts r { o with strict := true }
  | "--no-audio" :: r, o => parseOpts r { o with noAudio := true }
  | "--paramsets" :: "inband" :: r, o => parseOpts r { o with inband := true }
  | "--paramsets" :: "stsd" :: r, o => parseOpts r { o with inband := false }
  | x :: _, _ => .error s!"unknown option {x}"

def defaultArgs : String → Array String
  | "libx264" => #["-preset", "veryfast", "-crf", "16", "-bf", "0"]
  | "h264_videotoolbox" => #["-q:v", "75", "-bf", "0", "-allow_sw", "0"]
  | _ => #["-bf", "0"]

/-- Where `encodeRange` starts decoding: the display rank `rank` of a sync
sample and its presentation time `us` in microseconds, rounded down. -/
structure Seek where
  us   : Nat
  rank : Nat

/-- The seek point for re-encoding samples `frames` of `t`: the last sync sample
at or before the first of them in decode order. Decoding from there yields
exactly the frames of display rank `≥ ranks[k]`, in order (the bridge's
assumption that a sync sample resets the decoder). `none` (decode from the
start) if the demuxer, which seeks by decode time, could land past it. -/
def seekFor (t : VideoTrack) (ranks : Array Nat) (frames : List Nat) : Option Seek := do
  let lo := frames.foldl min (frames.head?.getD 0)
  let k ← (List.range (lo + 1)).reverse.find? (t.samples[·]!.sync)
  let cts := t.samples[k]!.cts
  guard (0 ≤ cts)
  -- The demuxer seeks by `stss`, which may also list open-GOP keyframes.
  guard <| (t.samples.extract (k + 1) t.samples.size).all fun s => !s.keyframe || cts < s.dts
  -- Rounding down keeps the seek at or before sample `k`; the previous frame is a
  -- whole frame earlier, so ffmpeg's accurate seek drops it.
  pure { us := cts.toNat * 1000000 / t.timescale, rank := ranks[k]! }

/-- Re-encode display frames `[a, b]` of `src` with an ffmpeg encoder, decoding
from `seek`. This is the only place pixels are touched. The encoder is trusted
(`Encoder` contract in `Spec/Export.lean`), and the result is checked to have
the right frame count, codec and no reordering. -/
def encodeRange (o : Opts) (src : String) (codec : String) (a b : Nat) (seek : Option Seek)
    (tmp : String) : IO (ByteArray × VideoTrack) := do
  let enc := o.encoder.getD "libx264"
  let extra := if o.encoderArgs.isEmpty then defaultArgs enc else o.encoderArgs
  -- `-seek_timestamp 1`: `-ss` is the stream timestamp, not relative to the
  -- file's start time (which other tracks, e.g. audio, can move).
  let (ss, r0) := match seek with
    | some s => (#["-seek_timestamp", "1", "-ss",
        s!"{s.us / 1000000}.{(toString (s.us % 1000000 + 1000000)).drop 1}"], s.rank)
    | none => (#[], 0)
  let run := fun (sync : Array String) => IO.Process.output {
    cmd := o.ffmpeg,
    args := #["-v", "error", "-y", "-ignore_editlist", "1"] ++ ss ++ #["-i", src,
      "-map", "0:v:0", "-an",
      "-vf", s!"select=between(n\\,{a - r0}\\,{b - r0}),setpts=N/FRAME_RATE/TB",
      "-frames:v", toString (b + 1 - a)] ++ sync ++
      #["-c:v", enc] ++ extra ++ #["-f", "mp4", tmp] }
  let mut out ← run #["-fps_mode", "passthrough"]
  if out.exitCode != 0 then out ← run #["-vsync", "0"]
  if out.exitCode != 0 then throw (IO.userError s!"encoder failed: {out.stderr}")
  let (bytes, t) ← loadTrack tmp
  if t.samples.size != b + 1 - a then
    throw (IO.userError s!"encoder produced {t.samples.size} frames, expected {b + 1 - a}")
  if t.codec != codec then throw (IO.userError s!"encoder produced {t.codec}, source is {codec}")
  if t.samples.any (·.ctsOff != t.samples[0]!.ctsOff) then
    throw (IO.userError "encoder reordered frames (B-frames); pass -bf 0")
  unless t.samples[0]!.sync do throw (IO.userError "encoded segment does not start with a sync sample")
  pure (bytes, t)

/-- The packet data the exporter carries: where a sample's bytes are (buffer
`src`, `offset`, `size`) and the sample description they belong to. -/
structure Pkt where
  src    : Nat
  offset : Nat
  size   : Nat
  sync   : Bool
  entry  : ByteArray
  deriving Inhabited

/-- `toStream t` with each packet's data replaced by its `Pkt` (bytes in buffer
`si`) and its display position by `pts i`. References are unchanged, so the
planner sees the same stream. -/
def pktStream (si : Nat) (t : VideoTrack) (pts : Nat → Nat) : VeriCut.Stream Pkt :=
  (toStream t).map fun p =>
    let s := t.samples[p.data]!
    { p with data := { src := si, offset := s.offset, size := s.size, sync := s.sync,
                       entry := t.entries }, pts := pts p.data }

structure LoadedClip where
  clip   : Clip
  track  : VideoTrack
  ranks  : Array Nat
  deriving Inhabited

/-- The IO encoder: ffmpeg via `encodeRange`. Encoded files are appended to the
byte buffers in the state. -/
abbrev ExportM := ReaderT (Opts × Array LoadedClip) (StateT (Array ByteArray) IO)

instance : MonadEncode Pkt ExportM where
  encode j := do
    let (o, clips) ← read
    let lc := clips[j.clip]!
    let c := lc.clip
    if o.strict then
      throw (IO.userError s!"{c.path}: {j.frames.length} frames need re-encoding (--strict)")
    let a := lc.ranks[j.frames.head!]!
    let b := lc.ranks[j.frames.getLast!]!
    let tmp := s!"{(← IO.getEnv "TMPDIR").getD "/tmp"}/vericut_{(← IO.monoNanosNow)}_{j.clip}_{a}.mp4"
    let (eb, et) ← encodeRange o c.path lc.track.codec a b (seekFor lc.track lc.ranks j.frames) tmp
    IO.FS.removeFile tmp
    let srcs ← get
    set (srcs.push eb)
    -- `encodeRange` checked there is no reordering: output frame `k` shows at `a + k`.
    pure (pktStream srcs.size et (a + ·))

/-- An audio packet the exporter copies: buffer `src`, bytes `[offset, offset + size)`,
sample description `entry` (index into the output's audio descriptions). -/
structure APkt where
  src    : Nat
  offset : Nat
  size   : Nat
  entry  : Nat
  deriving Inhabited

/-- The format a timeline's audio must share: sample rate, channels, samples per packet. -/
structure AudioFormat where
  rate     : Nat
  channels : Nat
  frameLen : Nat
  deriving BEq

/-- Check a source's audio can be copied and return its format, its packets
and how many media samples they hold. Only the last packet may be shorter: it
still decodes to a whole frame, and the edit list never plays past its end. -/
def audioPackets (path : String) (a : AudioTrack) : IO (AudioFormat × Array AudioSample × Nat) := do
  let fail {β} (why : String) : IO β := throw (IO.userError
    s!"{path}: audio {why}; pass --no-audio to export without audio")
  unless a.codec == "mp4a" && a.objectType == 2 do
    fail s!"is {a.codec} (object type {a.objectType}); only AAC-LC can be copied"
  unless a.timescale == a.sampleRate do
    fail s!"timescale {a.timescale} is not its sample rate {a.sampleRate}"
  let some s0 := a.samples[0]? | fail "track is empty"
  let n := s0.dur
  unless n > 0 && (a.samples.pop).all (·.dur == n) && a.samples.back!.dur ≤ n do
    fail "packets have varying durations"
  pure ({ rate := a.sampleRate, channels := a.channels, frameLen := n }, a.samples,
        (a.samples.map (·.dur)).sum)

/-- Round `x / d` to the nearest integer, halves up (`d > 0`). -/
def roundDiv (x : Int) (d : Nat) : Int := Int.fdiv (2 * x + d) (2 * d)

/-- The source audio media sample that plays with the source video sample at
composition time `cts`, by both tracks' edit lists (movie timescale `mts`). -/
def alignedSample (mts : Nat) (v : VideoTrack) (a : AudioTrack) (cts : Int) : Int :=
  a.edit.mediaTime + roundDiv
    (((cts - v.edit.mediaTime) * mts + ((v.edit.empty : Int) - a.edit.empty) * v.timescale) * a.timescale)
    (v.timescale * mts)

def doExport (tlPath outPath : String) (o : Opts) : IO Unit := do
  let t0 ← IO.monoMsNow
  let tl ← liftE tlPath (Json.parse (← IO.FS.readFile tlPath) >>= parseTimeline)
  if tl.isEmpty then throw (IO.userError "timeline has no clips")
  -- 1. load, check and plan every clip
  let mut srcs : Array ByteArray := #[]
  let mut loaded : Array LoadedClip := #[]
  let mut cuts : Array (VeriCut.Stream Pkt × List Segment) := #[]
  let mut fmt : Option (Nat × Nat × Nat × Nat × String) := none
  -- Each source file is read and indexed once, however many clips cut from it.
  let mut sources : Array (String × VideoTrack × Array Nat × VeriCut.Stream Pkt) := #[]
  -- per source: its movie, and its copyable audio packets (`none`: no audio)
  let mut movies : Array (Movie × Option (List APkt × Nat)) := #[]
  let mut audioFmt : Option AudioFormat := none
  let mut audioEntries : Array ByteArray := #[]
  let mut audioClips : Array (AudioClip APkt) := #[]
  for c in tl do
    let mut srcIdx := sources.findIdx? (·.1 == c.path)
    if srcIdx.isNone then
      let (bytes, mv) ← loadMovie c.path
      let t := mv.video
      let ranks := displayRanks t
      let si := srcs.size
      let apkts ← match mv.audio with
        | some a =>
          if o.noAudio then pure none else
          let (f, full, avail) ← audioPackets c.path a
          if audioFmt.any (· != f) then
            throw (IO.userError s!"{c.path}: audio sample rate, channels or packet length differs from the first clip")
          audioFmt := some f
          let e := match audioEntries.findIdx? (·.data == a.entries.data) with
            | some i => i + 1
            | none => audioEntries.size + 1
          if e > audioEntries.size then audioEntries := audioEntries.push a.entries
          pure (some (full.toList.map (fun x => ({ src := si, offset := x.offset, size := x.size, entry := e } : APkt)), avail))
        | none => pure none
      srcIdx := some sources.size
      sources := sources.push (c.path, t, ranks, pktStream si t (ranks[·]!))
      movies := movies.push (mv, apkts)
      srcs := srcs.push bytes
    let some si := srcIdx | unreachable!
    let (_, t, ranks, s) := sources[si]!
    let (mv, apkts) := movies[si]!
    let dur := t.samples[0]!.dur
    if (t.samples.pop).any (·.dur != dur) then
      throw (IO.userError s!"{c.path}: variable frame rate is not supported")
    match fmt with
    | none => fmt := some (t.timescale, dur, t.width, t.height, t.codec)
    | some (ts, d, w, h, cd) =>
      unless ts == t.timescale && d == dur && w == t.width && h == t.height && cd == t.codec do
        throw (IO.userError s!"{c.path}: frame rate, size or codec differs from the first clip")
    loaded := loaded.push { clip := c, track := t, ranks }
    cuts := cuts.push (s, ← planClip c t s)
    -- the clip's audio: the source sample that plays with its first frame
    let srcStart := match mv.audio, (ranks.toList.idxOf? c.inF) with
      | some a, some k => alignedSample mv.timescale t a t.samples[k]!.cts
      | _, _ => 0
    audioClips := audioClips.push
      { source := (apkts.map (·.1)).getD [], avail := (apkts.map (·.2)).getD 0, srcStart,
        ticks := (c.outF - c.inF) * dur }
  -- 2. the proven exporter (`exportTimeline_correct`), with ffmpeg as the encoder
  let (rendered, bufs) ← ((exportTimeline (m := ExportM) cuts.toList).run (o, loaded)).run srcs
  srcs := bufs
  -- 3. mux: sample descriptions, in-band parameter sets, display slots
  let mut entries : Array ByteArray := #[]
  let mut samples : Array OutSample := #[]
  let mut base := 0
  let mut copied := 0
  let mut encoded := 0
  let mut segsOut : Array Json := #[]
  let addEntry := fun (es : Array ByteArray) (e : ByteArray) =>
    match es.findIdx? (·.data == e.data) with
    | some i => (es, i + 1)
    | none => (es.push e, es.size + 1)
  -- in-band parameter-set handling: `active` = the parameter sets the decoder
  -- currently holds; a segment whose sets differ gets them prepended.
  let mut active : Option ByteArray := none
  let mut lenSize : Option Nat := none
  for (lc, (_, segs), outs) in loaded.toList.zip (cuts.toList.zip rendered) do
    let c := lc.clip
    let t := lc.track
    let (es, e) := if o.inband then (if entries.isEmpty then #[t.entries] else entries, 1)
                   else addEntry entries t.entries
    entries := es
    let srcSets : Option ByteArray := match avcParamSets t.entries with
      | .ok (l, ps) => some ps |>.filter fun _ => lenSize.all (· == l)
      | .error _ => none
    if active.isNone then active := srcSets
    if lenSize.isNone then lenSize := (avcParamSets t.entries).toOption.map (·.1)
    for (seg, out) in segs.zip outs do
      segsOut := segsOut.push (segJson seg)
      let (switchTo, entry) ← match seg with
        | .copy _ =>
          if o.inband && t.entries.data != entries[0]!.data && srcSets.isNone then
            throw (IO.userError s!"{c.path}: codec parameters differ from the first clip and cannot be switched in-band")
          pure (if o.inband && srcSets.isSome && srcSets.map (·.data) != active.map (·.data) then srcSets else none, e)
        | .encode _ =>
          let ee := out.head!.data.entry
          let (el, eps) ← liftE "encoder output" (avcParamSets ee)
          if o.inband && lenSize != some el then throw (IO.userError "encoder NAL length size differs from source")
          let (es, ee) := if o.inband then (entries, e) else addEntry entries ee
          entries := es
          pure (if o.inband && active.map (·.data) != some eps.data then some eps else none, ee)
      let mut first := true
      for p in out do
        let pre := if first then switchTo.getD ByteArray.empty else ByteArray.empty
        first := false
        let d := p.data
        let os : OutSample := { inband := pre, src := d.src, offset := d.offset, size := d.size, sync := d.sync, entry, disp := base + p.pts - c.inF }
        samples := samples.push os
      if switchTo.isSome then active := switchTo
      if seg.isCopy then copied := copied + out.length else encoded := encoded + seg.frames.length
    base := base + (c.outF - c.inF)
  let some (ts, dur, w, h, _) := fmt | throw (IO.userError "no clips")
  -- 4. audio: the proven packet selection and edit list (`exportAudio_exact`, `exportAudio_synced`)
  let audio := audioFmt.map fun af =>
    let (pkts, edits) := exportAudioClips af.frameLen af.rate ts audioClips.toList
    ({ timescale := af.rate, frameLen := af.frameLen, entries := audioEntries, edits,
       samples := pkts.toArray.map fun p => { src := p.src, offset := p.offset, size := p.size,
                                              sync := true, entry := p.entry, disp := 0 } } : AudioOut)
  writeFile outPath srcs { timescale := ts, dur, width := w, height := h, entries, samples } audio
  let t1 ← IO.monoMsNow
  let audioJson := match audio with
    | some a => Json.mkObj [("packets", toJson a.samples.size), ("rate", toJson a.timescale),
        ("samples", toJson ((a.edits.map fun | .media _ l => l | .empty l => l).sum)),
        ("silent", toJson ((a.edits.map fun | .media _ _ => 0 | .empty l => l).sum))]
    | none => Json.null
  IO.println <| Json.compress <| Json.mkObj [("output", toJson outPath), ("frames", toJson samples.size),
    ("copied", toJson copied), ("reencoded", toJson encoded), ("ms", toJson (t1 - t0)),
    ("audio", audioJson), ("segments", Json.arr segsOut)]

def doPlan (tlPath : String) : IO Unit := do
  let tl ← liftE tlPath (Json.parse (← IO.FS.readFile tlPath) >>= parseTimeline)
  let mut out := #[]
  for c in tl do
    let (_, t) ← loadTrack c.path
    let segs ← planClip c t (toStream t)
    out := out.push (Json.mkObj [("path", toJson c.path), ("segments", Json.arr (segs.toArray.map segJson))])
  IO.println (Json.compress (Json.arr out))

def usage : String :=
  "usage: vericut probe <file> | plan <timeline.json> | export <timeline.json> <out.mp4> [--encoder NAME] [--encoder-args \"...\"] [--ffmpeg PATH] [--strict] [--paramsets stsd|inband] [--no-audio]"

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["probe", f] => probe f
    | ["plan", tl] => doPlan tl
    | "export" :: tl :: out :: rest => doExport tl out (← liftE "options" (parseOpts rest {}))
    | _ => IO.eprintln usage; return 2
    return 0
  catch e =>
    IO.eprintln s!"error: {e}"
    return 1
