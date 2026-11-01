import VeriCut.Spec.Audio

/-!
RIFF WAVE files with integer PCM: format 1, or WAVE_FORMAT_EXTENSIBLE with
the PCM subformat. 8-bit samples are unsigned, wider ones signed, all little
endian.
-/

namespace VeriCut.Wav

def u16 (d : ByteArray) (i : Nat) : Nat := d[i]!.toNat ||| (d[i + 1]!.toNat <<< 8)

def u32 (d : ByteArray) (i : Nat) : Nat := u16 d i ||| (u16 d (i + 2) <<< 16)

def tag (d : ByteArray) (i : Nat) : String :=
  String.ofList ((List.range 4).map fun j => Char.ofNat d[i + j]!.toNat)

/-- Signed little-endian sample of `bytes` bytes at `i`. -/
@[inline] def sampleAt (d : ByteArray) (bytes i : Nat) : Int :=
  let u := match bytes with
    | 1 => d[i]!.toNat
    | 2 => d[i]!.toNat ||| (d[i + 1]!.toNat <<< 8)
    | 3 => d[i]!.toNat ||| (d[i + 1]!.toNat <<< 8) ||| (d[i + 2]!.toNat <<< 16)
    | _ => d[i]!.toNat ||| (d[i + 1]!.toNat <<< 8) ||| (d[i + 2]!.toNat <<< 16) ||| (d[i + 3]!.toNat <<< 24)
  match bytes with
  | 1 => (u : Int) - 128
  | 2 => if u < 0x8000 then u else (u : Int) - 0x10000
  | 3 => if u < 0x800000 then u else (u : Int) - 0x1000000
  | _ => if u < 0x80000000 then u else (u : Int) - 0x100000000

structure Fmt where
  channels : Nat
  sampleRate : Nat
  bits : Nat

/-- Chunks from `i` on: the `fmt ` fields and the `data` byte range. -/
def chunks (d : ByteArray) (i : Nat) (fmt : Option Fmt) (fuel : Nat) : Except String (Fmt × Nat × Nat) :=
  match fuel with
  | 0 => .error "too many chunks"
  | fuel + 1 =>
    if i + 8 > d.size then .error "no data chunk" else
    let size := u32 d (i + 4)
    let body := i + 8
    match tag d i with
    | "fmt " =>
      let code := u16 d body
      let pcm := code = 1 || (code = 0xFFFE && size ≥ 26 && u16 d (body + 24) = 1)
      if !pcm then .error s!"WAV format {code} is not integer PCM" else
      chunks d (body + size + size % 2) (some ⟨u16 d (body + 2), u32 d (body + 4), u16 d (body + 14)⟩) fuel
    | "data" =>
      match fmt with
      | none => .error "data chunk before fmt chunk"
      | some f => .ok (f, body, min (body + size) d.size)
    | _ => chunks d (body + size + size % 2) fmt fuel

/-- The format, and where the samples are and how many (per channel) there are. -/
def header (d : ByteArray) : Except String (Format × Nat × Nat) := do
  if d.size < 12 || tag d 0 != "RIFF" || tag d 8 != "WAVE" then throw "not a WAV file"
  let (f, start, stop) ← chunks d 12 none d.size
  if f.channels = 0 then throw "WAV with no channels"
  if f.bits < 4 || f.bits > 32 then throw s!"unsupported WAV sample size {f.bits}"
  pure (⟨f.sampleRate, f.channels, f.bits⟩, start, (stop - start) / ((f.bits + 7) / 8 * f.channels))

/-- Frames `first` to `first + count` (clamped to the file), all channels interleaved. -/
def parseFrames (d : ByteArray) (first count : Nat) : Except String Pcm := do
  let (f, start, frames) ← header d
  let bytes := (f.bitsPerSample + 7) / 8
  -- Narrower samples are left-justified in their container.
  let shift := 8 * bytes - f.bitsPerSample
  let first := min first frames
  let n := (min count (frames - first)) * f.channels
  let at0 := start + first * f.channels * bytes
  let mut s := Array.emptyWithCapacity n
  for k in [0:n] do
    s := s.push (sampleAt d bytes (at0 + k * bytes) >>> shift)
  return ⟨f, s⟩

def parse (d : ByteArray) : Except String Pcm := do
  let (_, _, frames) ← header d
  parseFrames d 0 frames

def pushLE (d : ByteArray) (bytes v : Nat) : ByteArray := Id.run do
  let mut d := d
  for j in [0:bytes] do d := d.push (v >>> (8 * j)).toUInt8
  return d

/-- A WAV file: format 1 (PCM) up to stereo 16-bit, WAVE_FORMAT_EXTENSIBLE above, which other
tools require there. Sample sizes that aren't whole bytes are written left-justified in the next one. -/
def write (x : Pcm) : ByteArray := Id.run do
  let f := x.format
  let bytes := (f.bitsPerSample + 7) / 8
  let shift := 8 * bytes - f.bitsPerSample
  let dataSize := x.samples.size * bytes
  let extensible := f.channels > 2 || bytes > 2
  let fmtSize := if extensible then 40 else 16
  let mut d := ByteArray.emptyWithCapacity (28 + fmtSize + dataSize)
  d := "RIFF".toUTF8.foldl (·.push ·) d
  d := pushLE d 4 (20 + fmtSize + dataSize)
  d := "WAVEfmt ".toUTF8.foldl (·.push ·) d
  d := pushLE (pushLE (pushLE (pushLE d 4 fmtSize) 2 (if extensible then 0xFFFE else 1)) 2 f.channels) 4 f.sampleRate
  d := pushLE (pushLE (pushLE d 4 (f.sampleRate * f.channels * bytes)) 2 (f.channels * bytes)) 2 (8 * bytes)
  if extensible then
    -- valid bits, channel mask (0: unassigned), then the PCM subformat GUID
    d := pushLE (pushLE (pushLE (pushLE d 2 22) 2 (8 * bytes)) 4 0) 2 1
    d := [0, 0, 0, 0, 0x10, 0, 0x80, 0, 0, 0xAA, 0, 0x38, 0x9B, 0x71].foldl (fun d b => d.push b) d
  d := "data".toUTF8.foldl (·.push ·) d
  d := pushLE d 4 dataSize
  let m : Int := 2 ^ shift
  for v in x.samples do
    let v := if shift = 0 then v else v * m
    -- two's complement through `Int64`; only the low `bytes` bytes are kept
    let u := (if bytes = 1 then v + 128 else v).toInt64.toUInt64
    d := match bytes with
      | 1 => d.push u.toUInt8
      | 2 => (d.push u.toUInt8).push (u >>> 8).toUInt8
      | 3 => ((d.push u.toUInt8).push (u >>> 8).toUInt8).push (u >>> 16).toUInt8
      | _ => (((d.push u.toUInt8).push (u >>> 8).toUInt8).push (u >>> 16).toUInt8).push (u >>> 24).toUInt8
  return d

end VeriCut.Wav
