import VeriCut.Flac.Encode

/-!
What `vericut export` runs, and the run-time checks of the theorems' hypotheses.
-/

namespace VeriCut

/-- Splice the clips, then encode them as FLAC. -/
def exportClips (st : Flac.Settings) (format : Format) (clips : List Clip) : ByteArray :=
  Flac.encode st (splice format clips)

/-- `x.Valid`, or what's wrong. -/
def Pcm.validate (x : Pcm) : Except String Unit := do
  let f := x.format
  unless 1 ≤ f.channels ∧ f.channels ≤ 8 do throw s!"{f.channels} channels, FLAC has 1 to 8"
  unless 4 ≤ f.bitsPerSample ∧ f.bitsPerSample ≤ 32 do throw s!"{f.bitsPerSample}-bit samples, FLAC has 4 to 32"
  unless 1 ≤ f.sampleRate ∧ f.sampleRate < 2 ^ 20 do throw s!"sample rate {f.sampleRate} does not fit FLAC"
  unless x.samples.size % f.channels = 0 do throw "last frame is incomplete"
  unless x.length < 2 ^ 36 do throw "too long for FLAC"
  let lim : Int := 2 ^ (f.bitsPerSample - 1)
  unless x.samples.all (fun s => -lim ≤ s ∧ s < lim) do throw "sample out of range"

end VeriCut
