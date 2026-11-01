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
def sampleAt (d : ByteArray) (bytes i : Nat) : Int :=
  let u := (List.range bytes).foldr (fun j acc => (acc <<< 8) ||| d[i + j]!.toNat) 0
  if bytes = 1 then (u : Int) - 128
  else if u < 2 ^ (8 * bytes - 1) then u else (u : Int) - 2 ^ (8 * bytes)

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

def parse (d : ByteArray) : Except String Pcm := do
  if d.size < 12 || tag d 0 != "RIFF" || tag d 8 != "WAVE" then throw "not a WAV file"
  let (f, start, stop) ← chunks d 12 none d.size
  if f.channels = 0 then throw "WAV with no channels"
  if f.bits < 4 || f.bits > 32 then throw s!"unsupported WAV sample size {f.bits}"
  let bytes := (f.bits + 7) / 8
  -- Narrower samples are left-justified in their container.
  let shift := 8 * bytes - f.bits
  let count := (stop - start) / (bytes * f.channels) * f.channels
  let mut s := Array.emptyWithCapacity count
  for k in [0:count] do
    s := s.push (sampleAt d bytes (start + k * bytes) / 2 ^ shift)
  return ⟨⟨f.sampleRate, f.channels, f.bits⟩, s⟩

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
  for v in x.samples do
    let v := v * 2 ^ shift
    d := pushLE d bytes (if bytes = 1 then (v + 128).toNat else (v % 2 ^ (8 * bytes)).toNat)
  return d

end VeriCut.Wav
