import VeriCut.Correctness

/-! The hypotheses hold on concrete audio, and the statements tell good output from bad. -/

namespace VeriCut

/-- Three stereo 16-bit frames. -/
def tiny : Pcm := ⟨⟨44100, 2, 16⟩, #[0, 1, -32768, 32767, 5, -5]⟩

def tinyMono : Pcm := ⟨⟨8000, 1, 8⟩, #[-128, 0, 127, 3]⟩

theorem tiny_valid : tiny.Valid := ⟨by decide, by decide, by decide, by decide, by decide, by simp [tiny]⟩
theorem tinyMono_valid : tinyMono.Valid :=
  ⟨by decide, by decide, by decide, by decide, by decide, by simp [tinyMono]⟩

example : Flac.decode (Flac.encode {} tiny) = .ok tiny := flac_roundTrip {} tiny tiny_valid
example : Flac.decode (Flac.encode (.level 8) tinyMono) = .ok tinyMono :=
  flac_roundTrip _ tinyMono tinyMono_valid

/-- Frame 2, then frames 0 and 1, of `tiny`. -/
def tinyClips : List Clip := [⟨tiny, 2, 3⟩, ⟨tiny, 0, 2⟩]

example : Flac.decode (exportClips {} tiny.format tinyClips) = .ok (splice tiny.format tinyClips) :=
  export_correct {} tiny.format tinyClips
    (by simp only [tinyClips, List.mem_cons, List.mem_nil_iff, or_false]
        rintro c (rfl | rfl) <;> exact ⟨tiny_valid, rfl, by decide⟩)
    (by simp [tinyClips]) (by decide)

-- The splice is the clips' samples in timeline order, not in source order.
#guard (splice tiny.format tinyClips).samples == #[5, -5, 0, 1, -32768, 32767]
example : splice tiny.format tinyClips ≠ tiny := by decide

-- Out of range for 16 bits: not valid, and the CLI's check says so.
#guard !(⟨⟨44100, 1, 16⟩, #[32768]⟩ : Pcm).isValid
-- A half frame of stereo: not valid.
#guard !(⟨⟨44100, 2, 16⟩, #[1, 2, 3]⟩ : Pcm).isValid

#guard match Flac.decode (Flac.encode {} tiny) with
  | .ok y => y == tiny
  | .error _ => false

end VeriCut
