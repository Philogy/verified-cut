import VeriCut.Spec.Audio
import VeriCut.Flac.Parse

namespace VeriCut.Flac

def StreamInfo.format (i : StreamInfo) : Format := ⟨i.sampleRate, i.channels, i.bitsPerSample⟩

def decode (d : ByteArray) : Except String Pcm := do
  let (s, _) ← streamP d 0
  let samples := s.samples
  if s.info.totalSamples ≠ 0 ∧ s.info.totalSamples * s.info.channels ≠ samples.size then
    throw s!"STREAMINFO says {s.info.totalSamples} samples, frames hold {samples.size / s.info.channels}"
  pure ⟨s.info.format, samples⟩

/-- Just the STREAMINFO block. -/
def probe (d : ByteArray) : Except String StreamInfo := do
  let ((_, i), _) ← streamHeadP d 0
  pure i

end VeriCut.Flac
