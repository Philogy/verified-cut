import Lossy.Spec.Pcm

/-! WAV files (PCM, little endian). Outside the proofs. -/

namespace Lossy.Wav

def u16 (a : ByteArray) (i : Nat) : Nat := a[i]!.toNat + 256 * a[i + 1]!.toNat
def u32 (a : ByteArray) (i : Nat) : Nat := u16 a i + 65536 * u16 a (i + 2)

def sampleAt (a : ByteArray) (i bytes : Nat) : Int :=
  let u := (List.range bytes).foldr (fun j acc => acc * 256 + a[i + j]!.toNat) 0
  if u < 2 ^ (8 * bytes - 1) then u else (u : Int) - 2 ^ (8 * bytes)

/-- Finds the chunk `id` after the RIFF header: offset of its data and size. -/
partial def findChunk (a : ByteArray) (id : String) (i : Nat) : Option (Nat × Nat) :=
  if i + 8 > a.size then none
  else
    let name := String.fromUTF8! (a.extract i (i + 4))
    let size := u32 a (i + 4)
    if name == id then some (i + 8, size) else findChunk a id (i + 8 + size + size % 2)

def parse (a : ByteArray) : Except String Pcm := do
  if a.size < 12 || String.fromUTF8! (a.extract 0 4) != "RIFF" then throw "not a RIFF file"
  let some (f, _) := findChunk a "fmt " 12 | throw "no fmt chunk"
  let some (d, size) := findChunk a "data" 12 | throw "no data chunk"
  let format := u16 a f
  let ch := u16 a (f + 2)
  let rate := u32 a (f + 4)
  let bits := u16 a (f + 14)
  unless format == 1 || format == 0xFFFE do throw s!"not integer PCM (format {format})"
  unless bits % 8 == 0 && 8 < bits && bits ≤ 32 do throw s!"unsupported bit depth {bits}"
  let bytes := bits / 8
  let size := min size (a.size - d)
  let n := size / (bytes * ch)
  let chans := (List.range ch).map fun c =>
    (Array.range n).map fun i => sampleAt a (d + (i * ch + c) * bytes) bytes
  return ⟨rate, bits, chans⟩

def pushLE (out : ByteArray) (v k : Nat) : ByteArray :=
  (List.range k).foldl (fun o j => o.push (v / 256 ^ j % 256).toUInt8) out

/-- Writes whole-byte depths; others are padded up. -/
def render (x : Pcm) : ByteArray := Id.run do
  let bytes := (x.bits + 7) / 8
  let pad := 8 * bytes - x.bits
  let ch := x.chans.length
  let n := x.length
  let dataSize := n * ch * bytes
  let mut o := ByteArray.empty
  o := "RIFF".toUTF8 ++ o
  o := pushLE o (36 + dataSize) 4
  o := o ++ "WAVEfmt ".toUTF8
  o := pushLE o 16 4
  o := pushLE o 1 2
  o := pushLE o ch 2
  o := pushLE o x.rate 4
  o := pushLE o (x.rate * ch * bytes) 4
  o := pushLE o (ch * bytes) 2
  o := pushLE o (8 * bytes) 2
  o := o ++ "data".toUTF8
  o := pushLE o dataSize 4
  let cs := x.chans.toArray
  for i in [0:n] do
    for c in cs do
      let v := c[i]! * 2 ^ pad
      o := pushLE o (v % 2 ^ (8 * bytes)).toNat bytes
  return o

end Lossy.Wav
