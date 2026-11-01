import VeriCut.Spec.Audio
import VeriCut.Flac.Parse

namespace VeriCut.Flac

def StreamInfo.format (i : StreamInfo) : Format := ⟨i.sampleRate, i.channels, i.bitsPerSample⟩

open Parser in
/-- `framesP`, keeping only the frames' samples (appended to `acc`), so a frame is dropped once decoded. -/
def framesSamplesP (info : StreamInfo) : Nat → Array Int → Parser (Array Int)
  | 0, acc => pure acc
  | fuel + 1, acc => do
    if ← atEnd then pure acc else framesSamplesP info fuel (acc ++ (← frameP info).samples)

open Parser in
/-- `streamP`, then `Stream.samples`, a frame at a time. -/
def streamSamplesP : Parser (StreamInfo × Array Int) := do
  let head ← streamHeadP
  let d ← data
  skipMetadata d.size head.1
  -- Capacity is not observable; it only saves regrowing the output. Capped against lying headers
  -- by what the data could hold (a constant subframe codes 65535 samples in a few bytes).
  let cap := min (head.2.totalSamples * head.2.channels) (8192 * d.size + 65536)
  let samples ← framesSamplesP head.2 d.size (.emptyWithCapacity cap)
  pure (head.2, samples)

def decode (d : ByteArray) : Except String Pcm := do
  let ((info, samples), _) ← streamSamplesP d 0
  if info.totalSamples ≠ 0 ∧ info.totalSamples * info.channels ≠ samples.size then
    throw s!"STREAMINFO says {info.totalSamples} samples, frames hold {samples.size / info.channels}"
  pure ⟨info.format, samples⟩

/-- Just the STREAMINFO block. -/
def probe (d : ByteArray) : Except String StreamInfo := do
  let ((_, i), _) ← streamHeadP d 0
  pure i

end VeriCut.Flac
