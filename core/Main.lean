import Lean.Data.Json
import VeriCut.Export
import VeriCut.Flac.Decode
import VeriCut.Wav

/-!
# `vericut` command line

    vericut probe  <file.wav|file.flac>
    vericut peaks  <file> <buckets>
    vericut export <timeline.json> <out.flac> [--level N]
    vericut encode <in.wav> <out.flac> [--level N]
    vericut decode <in.flac> <out.wav>

JSON on stdout; errors on stderr with a nonzero exit. Contract: `docs/cli.md`.
-/

open Lean VeriCut

def liftE {α} (ctx : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{ctx}: {e}")

def isFlac (d : ByteArray) : Bool := d.size ≥ 4 && d.extract 0 4 == "fLaC".toUTF8

def load (path : String) : IO Pcm := do
  let d ← IO.FS.readBinFile path
  liftE path (if isFlac d then Flac.decode d else Wav.parse d)

def levelArg : List String → IO Flac.Settings
  | [] => pure (.level 5)
  | ["--level", n] => match n.toNat? with
    | some n => pure (.level n)
    | none => throw (IO.userError s!"bad level {n}")
  | a => throw (IO.userError s!"unexpected arguments {a}")

def formatJson (f : VeriCut.Format) (samples : Nat) (kind : String) : Json :=
  Json.mkObj [("sampleRate", toJson f.sampleRate), ("channels", toJson f.channels),
    ("bitsPerSample", toJson f.bitsPerSample), ("samples", toJson samples), ("format", toJson kind)]

def probe (path : String) : IO Unit := do
  let d ← IO.FS.readBinFile path
  if isFlac d then
    let i ← liftE path (Flac.probe d)
    IO.println (formatJson i.format i.totalSamples "flac").compress
  else
    let (f, _, frames) ← liftE path (Wav.header d)
    -- The app converts what this rejects, so reject here what `export` would. Parsed samples
    -- are always in range for their size, so the format decides.
    liftE path (Pcm.validate ⟨f, #[]⟩)
    unless frames < 2 ^ 36 do throw (IO.userError s!"{path}: too long for FLAC")
    IO.println (formatJson f frames "wav").compress

/-- Per bucket, min and max of the channel average, in units of 1/10000 of full scale.
`get k` is interleaved sample `k`, so WAVs are read straight from their bytes. -/
def peaksBy (len ch bits : Nat) (get : Nat → Int64) (buckets : Nat) : Array Int × Array Int := Id.run do
  let full : Int := 2 ^ (bits - 1) * ch
  let per := max 1 ((len + buckets - 1) / max buckets 1)
  let mut lo := #[]
  let mut hi := #[]
  for b in [0:buckets] do
    -- Int64: at most 8 channels of 32 bits, so sums fit and the loop stays unboxed.
    let mut mn : Int64 := 0
    let mut mx : Int64 := 0
    for i in [b * per:min len ((b + 1) * per)] do
      let mut s : Int64 := 0
      for c in [0:ch] do s := s + get (i * ch + c)
      mn := min mn s
      mx := max mx s
    lo := lo.push (mn.toInt * 10000 / full)
    hi := hi.push (mx.toInt * 10000 / full)
  return (lo, hi)

/-- Signed little-endian sample of `bytes` bytes at `i`, as `Wav.sampleAt` but in `Int64`. -/
@[inline] def sampleAt64 (d : ByteArray) (bytes i : Nat) (shift : UInt64) : Int64 :=
  let u : UInt64 := match bytes with
    | 1 => d[i]!.toUInt64
    | 2 => d[i]!.toUInt64 ||| (d[i + 1]!.toUInt64 <<< 8)
    | 3 => d[i]!.toUInt64 ||| (d[i + 1]!.toUInt64 <<< 8) ||| (d[i + 2]!.toUInt64 <<< 16)
    | _ => d[i]!.toUInt64 ||| (d[i + 1]!.toUInt64 <<< 8) ||| (d[i + 2]!.toUInt64 <<< 16) ||| (d[i + 3]!.toUInt64 <<< 24)
  if bytes = 1 then (u.toInt64 - 128) >>> shift.toInt64
  else
    -- sign-extend from 8 * bytes bits, then drop the left-justification padding
    let w : UInt64 := 64 - 8 * bytes.toUInt64
    ((u <<< w).toInt64 >>> w.toInt64) >>> shift.toInt64

def peaks (path : String) (buckets : Nat) : IO (Array Int × Array Int) := do
  let d ← IO.FS.readBinFile path
  if isFlac d then
    let x ← liftE path (Flac.decode d)
    return peaksBy x.length x.format.channels x.format.bitsPerSample (fun k => Int64.ofInt x.samples[k]!) buckets
  let (f, start, frames) ← liftE path (Wav.header d)
  let bytes := (f.bitsPerSample + 7) / 8
  let shift := (8 * bytes - f.bitsPerSample).toUInt64
  return peaksBy frames f.channels f.bitsPerSample (fun k => sampleAt64 d bytes (start + k * bytes) shift) buckets

def fixed4 (v : Int) : Json := Json.num ⟨v, 4⟩

structure Entry where
  src : String
  start : Nat
  stop : Nat

def parseTimeline (j : Json) : Except String (List Entry) := do
  let clips ← (← j.getObjVal? "clips").getArr?
  clips.toList.mapM fun c => do
    pure ⟨← (← c.getObjVal? "src").getStr?, ← (← c.getObjVal? "in").getNat?, ← (← c.getObjVal? "out").getNat?⟩

def formatName (f : VeriCut.Format) : String := s!"{f.sampleRate} Hz, {f.channels} channels, {f.bitsPerSample}-bit"

def writeOut (path : String) (bytes : ByteArray) (samples : Nat) (t0 : Nat) : IO Unit := do
  IO.FS.writeBinFile path bytes
  let t1 ← IO.monoMsNow
  IO.println (Json.mkObj [("samples", toJson samples), ("bytes", toJson bytes.size), ("ms", toJson (t1 - t0))]).compress

def exportCmd (timeline out : String) (st : Flac.Settings) : IO Unit := do
  let t0 ← IO.monoMsNow
  let j ← liftE timeline (Json.parse (← IO.FS.readFile timeline))
  let entries ← liftE timeline (parseTimeline j)
  -- WAV clips load only their own frames (an hour-long source would otherwise be parsed whole);
  -- FLAC sources are decoded once. Either way each clip is a valid `Clip` for `export_correct`.
  let mut files : Std.HashMap String ByteArray := {}
  let mut flacs : Std.HashMap String Pcm := {}
  let mut clips := #[]
  for e in entries do
    let d ← match files[e.src]? with
      | some d => pure d
      | none => IO.FS.readBinFile e.src
    files := files.insert e.src d
    let (src, start) ← if isFlac d then do
        let x ← match flacs[e.src]? with
          | some x => pure x
          | none => do
            let x ← liftE e.src (Flac.decode d)
            liftE e.src x.validate
            pure x
        flacs := flacs.insert e.src x
        pure (x, e.start)
      else do
        let (_, _, frames) ← liftE e.src (Wav.header d)
        unless e.start ≤ e.stop ∧ e.stop ≤ frames do
          throw (IO.userError s!"{e.src}: range [{e.start}, {e.stop}) outside 0..{frames}")
        let x ← liftE e.src (Wav.parseFrames d e.start (e.stop - e.start))
        liftE e.src x.validate
        pure (x, 0)
    let stop := start + (e.stop - e.start)
    unless e.start ≤ e.stop ∧ stop ≤ src.length do
      throw (IO.userError s!"{e.src}: range [{e.start}, {e.stop}) outside 0..{src.length}")
    clips := clips.push (⟨src, start, stop⟩ : Clip)
  let format ← match clips[0]? with
    | some c => pure c.src.format
    | none => throw (IO.userError "timeline has no clips")
  for c in clips do
    unless c.src.format = format do
      throw (IO.userError s!"clip formats differ: {formatName c.src.format} vs {formatName format}")
  let total := clips.foldl (fun n (c : Clip) => n + (c.stop - c.start)) 0
  unless total < 2 ^ 36 do throw (IO.userError "timeline too long for FLAC")
  writeOut out (exportClips st format clips.toList) total t0

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["probe", f] => probe f
    | ["peaks", f, n] =>
      let some n := n.toNat? | throw (IO.userError s!"bad bucket count {n}")
      let (lo, hi) ← peaks f n
      IO.println (Json.mkObj [("min", Json.arr (lo.map fixed4)), ("max", Json.arr (hi.map fixed4))]).compress
    | "export" :: t :: o :: rest => exportCmd t o (← levelArg rest)
    | "encode" :: i :: o :: rest =>
      let st ← levelArg rest
      let t0 ← IO.monoMsNow
      let x ← load i
      liftE i x.validate
      writeOut o (Flac.encode st x) x.length t0
    | ["decode", i, o] =>
      let t0 ← IO.monoMsNow
      let x ← load i
      writeOut o (Wav.write x) x.length t0
    | _ =>
      IO.eprintln "usage: vericut probe|peaks|export|encode|decode … (see docs/cli.md)"
      return 2
    return 0
  catch e =>
    IO.eprintln e
    return 1
