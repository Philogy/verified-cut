import VeriCut.Flac.Fast.Export

/-!
Packed implementation data for PCM, related to the spec's `Pcm` by an abstraction
function `toSpec` (total, not a bijection: trailing bytes past a multiple of 4 are ignored).

`Array Int` boxes every element in an 8-byte slot; a `ByteArray` holding 32-bit
little-endian samples is flat, 4 bytes per sample.
-/

namespace VeriCut

/-- Signed 32-bit samples, 4 bytes each, little-endian two's complement. -/
structure I32Array where
  bytes : ByteArray

/-- Number of whole samples stored. -/
def I32Array.size (a : I32Array) : Nat := a.bytes.size / 4

/-- Sample `i`, read as 4 little-endian bytes in two's complement. -/
def I32Array.get (a : I32Array) (i : Nat) : Int :=
  let b (k : Nat) : Nat := (a.bytes.get! (4 * i + k)).toNat
  let n := b 0 + 256 * b 1 + 65536 * b 2 + 16777216 * b 3
  if n < 2 ^ 31 then (n : Int) else (n : Int) - 2 ^ 32

/-- The abstraction function: the samples as the spec sees them. -/
def I32Array.toSpec (a : I32Array) : Array Int := (Array.range a.size).map a.get

/-- PCM with packed samples, interleaved as in `Pcm`. -/
structure PackedPcm where
  format : Format
  samples : I32Array

/-- The abstraction function from packed to spec PCM. -/
def PackedPcm.toSpec (p : PackedPcm) : Pcm := ⟨p.format, p.samples.toSpec⟩

/-- Encode packed PCM. For now this unpacks and runs `encodeFast`; a packed encoder
can replace the body as long as `flac_roundTrip_packed` still holds. -/
def Flac.Fast.encodePacked (st : Flac.Fast.Settings) (p : PackedPcm) : ByteArray :=
  Flac.Fast.encodeFast st p.toSpec

#guard (I32Array.toSpec ⟨⟨#[1, 0, 0, 0, 0xff, 0xff, 0xff, 0xff, 0, 0, 0, 0x80]⟩⟩) == #[1, -1, -2 ^ 31]

end VeriCut
