import Lean.Data.Json
import VeriCut.Impl.Planner
import VeriCut.Impl.Export
import VeriCut.MP4.Write

/-!
# `vericut` command line

    vericut probe  <file>                      frame table as JSON
    vericut plan   <timeline.json>             plan as JSON (no output written)
    vericut export <timeline.json> <out.mp4>   [--encoder NAME] [--encoder-args "..."]
                                                [--ffmpeg PATH] [--strict]

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
      ("cts", toJson s.cts), ("dur", toJson s.dur), ("sync", toJson s.sync), ("display", toJson ranks[i]!)]
  IO.println <| Json.compress <| Json.mkObj [("codec", toJson t.codec), ("timescale", toJson t.timescale),
    ("frames", Json.arr frames)]

/-- Check a clip's range and compute the plan of its stream `s` (`toStream t`,
up to packet data). -/
def planClip {α} [Inhabited α] (c : Clip) (t : VideoTrack) (s : VeriCut.Stream α) :
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

def parseOpts : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--encoder" :: v :: r, o => parseOpts r { o with encoder := some v }
  | "--encoder-args" :: v :: r, o =>
    parseOpts r { o with encoderArgs := (v.splitOn " ").filter (· != "") |>.toArray }
  | "--ffmpeg" :: v :: r, o => parseOpts r { o with ffmpeg := v }
  | "--strict" :: r, o => parseOpts r { o with strict := true }
  | "--paramsets" :: "inband" :: r, o => parseOpts r { o with inband := true }
  | "--paramsets" :: "stsd" :: r, o => parseOpts r { o with inband := false }
  | x :: _, _ => .error s!"unknown option {x}"

def defaultArgs : String → Array String
  | "libx264" => #["-preset", "veryfast", "-crf", "16", "-bf", "0"]
  | "h264_videotoolbox" => #["-q:v", "75", "-bf", "0", "-allow_sw", "0"]
  | _ => #["-bf", "0"]

/-- Re-encode display frames `[a, b]` of `src` with an ffmpeg encoder.
This is the only place pixels are touched. The encoder is trusted (`Encoder`
contract in `Spec/Export.lean`), and the result is checked to have the right
frame count, codec and no reordering. -/
def encodeRange (o : Opts) (src : String) (codec : String) (a b : Nat) (tmp : String) :
    IO (ByteArray × VideoTrack) := do
  let enc := o.encoder.getD "libx264"
  let extra := if o.encoderArgs.isEmpty then defaultArgs enc else o.encoderArgs
  let run := fun (sync : Array String) => IO.Process.output {
    cmd := o.ffmpeg,
    args := #["-v", "error", "-y", "-ignore_editlist", "1", "-i", src, "-map", "0:v:0", "-an",
      "-vf", s!"select=between(n\\,{a}\\,{b}),setpts=N/FRAME_RATE/TB"] ++ sync ++
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
    let (eb, et) ← encodeRange o c.path lc.track.codec a b tmp
    IO.FS.removeFile tmp
    let srcs ← get
    set (srcs.push eb)
    -- `encodeRange` checked there is no reordering: output frame `k` shows at `a + k`.
    pure (pktStream srcs.size et (a + ·))

def doExport (tlPath outPath : String) (o : Opts) : IO Unit := do
  let t0 ← IO.monoMsNow
  let tl ← liftE tlPath (Json.parse (← IO.FS.readFile tlPath) >>= parseTimeline)
  if tl.isEmpty then throw (IO.userError "timeline has no clips")
  -- 1. load, check and plan every clip
  let mut srcs : Array ByteArray := #[]
  let mut loaded : Array LoadedClip := #[]
  let mut cuts : Array (VeriCut.Stream Pkt × List Segment) := #[]
  let mut fmt : Option (Nat × Nat × Nat × Nat × String) := none
  for c in tl do
    let (bytes, t) ← loadTrack c.path
    let dur := t.samples[0]!.dur
    if (t.samples.pop).any (·.dur != dur) then
      throw (IO.userError s!"{c.path}: variable frame rate is not supported")
    match fmt with
    | none => fmt := some (t.timescale, dur, t.width, t.height, t.codec)
    | some (ts, d, w, h, cd) =>
      unless ts == t.timescale && d == dur && w == t.width && h == t.height && cd == t.codec do
        throw (IO.userError s!"{c.path}: frame rate, size or codec differs from the first clip")
    let ranks := displayRanks t
    let s := pktStream srcs.size t (ranks[·]!)
    srcs := srcs.push bytes
    loaded := loaded.push { clip := c, track := t, ranks }
    cuts := cuts.push (s, ← planClip c t s)
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
  writeFile outPath srcs { timescale := ts, dur, width := w, height := h, entries, samples }
  let t1 ← IO.monoMsNow
  IO.println <| Json.compress <| Json.mkObj [("output", toJson outPath), ("frames", toJson samples.size),
    ("copied", toJson copied), ("reencoded", toJson encoded), ("ms", toJson (t1 - t0)),
    ("segments", Json.arr segsOut)]

def doPlan (tlPath : String) : IO Unit := do
  let tl ← liftE tlPath (Json.parse (← IO.FS.readFile tlPath) >>= parseTimeline)
  let mut out := #[]
  for c in tl do
    let (_, t) ← loadTrack c.path
    let segs ← planClip c t (toStream t)
    out := out.push (Json.mkObj [("path", toJson c.path), ("segments", Json.arr (segs.toArray.map segJson))])
  IO.println (Json.compress (Json.arr out))

def usage : String :=
  "usage: vericut probe <file> | plan <timeline.json> | export <timeline.json> <out.mp4> [--encoder NAME] [--encoder-args \"...\"] [--ffmpeg PATH] [--strict] [--paramsets stsd|inband]"

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
