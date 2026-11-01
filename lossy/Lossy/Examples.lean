import Lossy.Correctness

/-! The hypotheses can be met, and the spec tells good output from bad. -/

namespace Lossy

/-- Eight samples of 16-bit stereo. -/
def tiny : Pcm := ⟨44100, 16, [#[0, 1000, 2000, 3001, -3, -2000, 32767, -32768],
                               #[5, 5, 5, 5, 7, 7, 7, 7]]⟩

theorem tiny_valid : tiny.Valid where
  bits := by decide
  chans := by decide
  rate := by decide
  sizes := by decide
  short := by decide
  range := by decide

example : decode (encode 0 tiny) = some tiny := lossless tiny tiny_valid
example : ∃ y, decode (encode 6 tiny) = some y ∧ maxErr tiny y < 64 := error_lt tiny tiny_valid 6

-- Block peak 32768 uses all 16 bits, so `q = 4` rounds to multiples of 16;
-- the top sample can't round up to 32768 and goes down to 32752.
#guard (quantize 4 tiny).chans.head! == #[0, 1008, 2000, 3008, 0, -2000, 32752, -32768]
#guard maxErr tiny (quantize 4 tiny) == 15
#guard decode (encode 4 tiny) == some (quantize 4 tiny)

-- The byte-table CRC agrees with the bitwise one.
#guard let l := (List.range 40).flatMap fun i => bitsOf 8 (i * 37 % 256)
  crc16Bytes (packInto .empty l) == crc16 l

/-- A decoder output with one sample off by 64 is not within `2^6` of the input. -/
example : ¬ maxErr tiny ⟨44100, 16, [#[64, 1000, 2000, 3001, -3, -2000, 32767, -32768],
    #[5, 5, 5, 5, 7, 7, 7, 7]]⟩ < 2 ^ 6 := by decide

/-- Swapping channels is far off. -/
example : sqErr tiny ⟨44100, 16, tiny.chans.reverse⟩ ≠ 0 := by decide

end Lossy
