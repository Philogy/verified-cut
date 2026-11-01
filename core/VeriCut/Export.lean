import VeriCut.Flac.Encode

/-!
What `vericut export` runs, and the run-time checks of the theorems' hypotheses.
-/

namespace VeriCut

/-- Splice the clips, then encode them as FLAC. -/
def exportClips (st : Flac.Settings) (format : Format) (clips : List Clip) : ByteArray :=
  Flac.encode st (splice format clips)

/-- `Pcm.Valid`, decided. -/
def Pcm.isValid (x : Pcm) : Bool :=
  let f := x.format
  let lim : Int := 2 ^ (f.bitsPerSample - 1)
  decide (1 ≤ f.channels ∧ f.channels ≤ 8 ∧ 4 ≤ f.bitsPerSample ∧ f.bitsPerSample ≤ 32 ∧
    1 ≤ f.sampleRate ∧ f.sampleRate < 2 ^ 20 ∧ x.samples.size % f.channels = 0 ∧ x.length < 2 ^ 36) &&
  x.samples.all fun s => -lim ≤ s ∧ s < lim

/-- What makes `x` invalid, if it is. -/
def Pcm.problem (x : Pcm) : String :=
  let f := x.format
  if ¬(1 ≤ f.channels ∧ f.channels ≤ 8) then s!"{f.channels} channels, FLAC has 1 to 8"
  else if ¬(4 ≤ f.bitsPerSample ∧ f.bitsPerSample ≤ 32) then s!"{f.bitsPerSample}-bit samples, FLAC has 4 to 32"
  else if ¬(1 ≤ f.sampleRate ∧ f.sampleRate < 2 ^ 20) then s!"sample rate {f.sampleRate} does not fit FLAC"
  else if x.samples.size % f.channels ≠ 0 then "last frame is incomplete"
  else if ¬x.length < 2 ^ 36 then "too long for FLAC"
  else "sample out of range"

def Pcm.validate (x : Pcm) : Except String Unit :=
  if x.isValid then .ok () else .error x.problem

end VeriCut
