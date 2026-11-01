import Lossy

open Lossy

def usage : String :=
  "usage: lossy encode <q> <in.wav> <out.flac>\n" ++
  "       lossy decode <in.flac> <out.wav>\n" ++
  "       lossy stats <q> <in.wav>   (encode, decode, compare; JSON)"

def readWav (path : String) : IO Pcm := do
  match Wav.parse (← IO.FS.readBinFile path) with
  | .ok x => pure x
  | .error e => throw (IO.userError s!"{path}: {e}")

def main : List String → IO UInt32
  | ["encode", q, i, o] => do
    let x ← readWav i
    IO.FS.writeBinFile o (encode q.toNat! x)
    return 0
  | ["decode", i, o] => do
    match decode (← IO.FS.readBinFile i) with
    | some x => IO.FS.writeBinFile o (Wav.render x); return 0
    | none => IO.eprintln s!"{i}: not a stream this decoder reads"; return 1
  | ["stats", q, i] => do
    let x ← readWav i
    let q := q.toNat!
    let t0 ← IO.monoMsNow
    let bytes := encode q x
    let t1 ← IO.monoMsNow
    let y := decode bytes
    let t2 ← IO.monoMsNow
    let expected := quantize q x
    let ok := y == some expected
    let n := x.length * x.chans.length
    IO.println s!"\{\"q\":{q},\"bytes\":{bytes.size},\"samples\":{n},\"encodeMs\":{t1 - t0},\"decodeMs\":{t2 - t1},\"roundTrip\":{ok},\"maxErr\":{maxErr x expected},\"sqErr\":{sqErr x expected}}"
    return if ok then 0 else 2
  | _ => do IO.eprintln usage; return 1
