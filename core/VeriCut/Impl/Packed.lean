import VeriCut.Flac.Fast.Export
import VeriCut.Export
import VeriCut.Wav

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
  if i < a.size then
  let b (k : Nat) : Nat := (a.bytes.get! (4 * i + k)).toNat
  let n := b 0 + 256 * b 1 + 65536 * b 2 + 16777216 * b 3
  if n < 2 ^ 31 then (n : Int) else (n : Int) - 2 ^ 32
  else 0

/-- The abstraction function: the samples as the spec sees them. -/
def I32Array.toSpec (a : I32Array) : Array Int := (Array.range a.size).map a.get

/-- PCM with packed samples, interleaved as in `Pcm`. -/
structure PackedPcm where
  format : Format
  samples : I32Array

/-- The abstraction function from packed to spec PCM. -/
def PackedPcm.toSpec (p : PackedPcm) : Pcm := ⟨p.format, p.samples.toSpec⟩

theorem I32Array.toSpec_size (a : I32Array) : a.toSpec.size = a.size := by
  simp [I32Array.toSpec]

theorem I32Array.toSpec_getElem! (a : I32Array) (i : Nat) : a.toSpec[i]! = a.get i := by
  by_cases h : i < a.size
  · simp [I32Array.toSpec, h]
  · have : a.get i = 0 := by simp [I32Array.get, h]
    rw [this]; simp [I32Array.toSpec, h]

namespace Flac.Fast

def pushSamplesP (d : ByteArray) (bytes : Nat) (a : I32Array) (start stop : Nat) : ByteArray := Id.run do
  let mut d := d
  for i in [start:stop] do
    let u := (a.get i).toInt64.toUInt64
    d := match bytes with
      | 1 => d.push u.toUInt8
      | 2 => (d.push u.toUInt8).push (u >>> 8).toUInt8
      | 3 => ((d.push u.toUInt8).push (u >>> 8).toUInt8).push (u >>> 16).toUInt8
      | _ => (((d.push u.toUInt8).push (u >>> 8).toUInt8).push (u >>> 16).toUInt8).push (u >>> 24).toUInt8
  return d

def md5P (bits : Nat) (a : I32Array) : Nat := Id.run do
  let bytes := (bits + 7) / 8
  let chunk := 8192
  let mut st : Md5.State := {}
  let mut tail := ByteArray.empty
  for k in [0:(a.size + chunk - 1) / chunk] do
    let (st', tail') := Md5.blocks st (pushSamplesP tail bytes a (k * chunk) (min a.size ((k + 1) * chunk)))
    st := st'
    tail := tail'
  return Md5.finish st tail (a.size * bytes)

theorem md5P_eq (bits : Nat) (a : I32Array) : md5P bits a = Md5.ofSamples bits a.toSpec := by
  simp only [md5P, Md5.ofSamples, pushSamplesP, Md5.pushSamples, I32Array.toSpec_size,
    I32Array.toSpec_getElem!]
  rfl

def channelBlockP (p : PackedPcm) (offset n c : Nat) : Array Int :=
  .ofFn (n := n) fun i => p.samples.get ((offset + i.1) * p.format.channels + c)

def lengthP (p : PackedPcm) : Nat := p.samples.size / p.format.channels

def planFrameP (st : Settings) (x : PackedPcm) (number offset n : Nat) : Frame :=
  let f := x.format
  let header channels : Header := ⟨n, f.sampleRate, f.bitsPerSample, channels, number⟩
  let blocks := (Array.range f.channels).map (channelBlockP x offset n)
  let ws := frameWindows st n
  let plain := blocks.map (planSubframe st ws f.bitsPerSample)
  if st.stereo && f.channels = 2 then
    let l := plain[0]!
    let r := plain[1]!
    let side := planSubframe st ws (f.bitsPerSample + 1) (Array.zipWith (· - ·) blocks[0]! blocks[1]!)
    let mid := planSubframe st ws f.bitsPerSample (Array.zipWith (fun a b => (a + b) / 2) blocks[0]! blocks[1]!)
    let options := [(Channels.leftSide, l, side), (.rightSide, side, r), (.midSide, mid, side)]
    let best := options.foldl (init := (Channels.independent 2, l, r)) fun best o =>
      if o.2.1.2 + o.2.2.2 < best.2.1.2 + best.2.2.2 then o else best
    ⟨header best.1, #[best.2.1.1, best.2.2.1]⟩
  else ⟨header (.independent f.channels), plain.map (·.1)⟩

theorem planFrameP_eq (st : Settings) (x : PackedPcm) (number offset n : Nat) :
    planFrameP st x number offset n = planFrame st x.toSpec number offset n := by
  have hb : channelBlockP x offset n = channelBlock x.toSpec offset n := by
    funext c; simp only [channelBlockP, channelBlock, PackedPcm.toSpec, I32Array.toSpec_getElem!]
  simp only [planFrameP, planFrame, hb]; rfl

def encodeFrameP (st : Settings) (x : PackedPcm) (k : Nat) : ByteArray :=
  let b := st.clampedBlockSize
  writeFrame (planFrameP st x k (k * b) (min b (lengthP x - k * b)))

def encodeFramesP (st : Settings) (x : PackedPcm) : ByteArray × Nat × Nat :=
  let b := st.clampedBlockSize
  let cap := x.samples.size * ((x.format.bitsPerSample + 7) / 8) + 4096
  (List.range ((lengthP x + b - 1) / b)).foldl (init := (.emptyWithCapacity cap, 0, 0)) fun (out, lo, hi) k =>
    let f := encodeFrameP st x k
    (out ++ f, if k = 0 then f.size else min lo f.size, max hi f.size)

theorem lengthP_eq (x : PackedPcm) : lengthP x = x.toSpec.length := by
  simp [lengthP, Pcm.length, PackedPcm.toSpec, I32Array.toSpec_size]

theorem encodeFramesP_eq (st : Settings) (x : PackedPcm) : encodeFramesP st x = encodeFrames st x.toSpec := by
  have hf : encodeFrameP st x = encodeFrame st x.toSpec := by
    funext k; simp only [encodeFrameP, encodeFrame, planFrameP_eq, lengthP_eq]
  have hs : x.toSpec.samples.size = x.samples.size := I32Array.toSpec_size _
  simp only [encodeFramesP, encodeFrames, hf, lengthP_eq, hs]; rfl

/-- Encode packed PCM: the samples stay packed; each block is unpacked as it is planned. -/
def encodePacked (st : Settings) (x : PackedPcm) : ByteArray :=
  let (body, minSize, maxSize) := encodeFramesP st x
  let f := x.format
  let info : StreamInfo := {
    minBlockSize := st.clampedBlockSize, maxBlockSize := st.clampedBlockSize,
    minFrameSize := fitFrameSize minSize, maxFrameSize := fitFrameSize maxSize,
    sampleRate := f.sampleRate, channels := f.channels, bitsPerSample := f.bitsPerSample,
    totalSamples := lengthP x, md5 := md5P f.bitsPerSample x.samples % 2 ^ 128 }
  (writeHead info .empty).bytes ++ body

theorem encodePacked_eq (st : Settings) (x : PackedPcm) : encodePacked st x = encodeFast st x.toSpec := by
  simp only [encodePacked, encodeFast, encodeFramesP_eq, lengthP_eq, md5P_eq]; rfl

end Flac.Fast


/-- `Pcm.isValid` on the abstraction, read from the packed samples. -/
def PackedPcm.isValid (x : PackedPcm) : Bool :=
  let f := x.format
  let lim : Int := 2 ^ (f.bitsPerSample - 1)
  decide (1 ≤ f.channels ∧ f.channels ≤ 8 ∧ 4 ≤ f.bitsPerSample ∧ f.bitsPerSample ≤ 32 ∧
    1 ≤ f.sampleRate ∧ f.sampleRate < 2 ^ 20 ∧ x.samples.size % f.channels = 0 ∧
    x.samples.size / f.channels < 2 ^ 36) &&
  (List.range x.samples.size).all fun i => let s := x.samples.get i; -lim ≤ s ∧ s < lim

def PackedPcm.validate (x : PackedPcm) : Except String Unit :=
  if x.isValid then .ok () else .error "invalid PCM (format or sample out of range)"

/-- `Wav.parseFrames`, writing samples straight into an `I32Array`. -/
def Wav.parsePacked (d : ByteArray) : Except String PackedPcm := do
  let (f, start, frames) ← Wav.header d
  let bytes := (f.bitsPerSample + 7) / 8
  let shift := 8 * bytes - f.bitsPerSample
  let n := frames * f.channels
  let mut out := ByteArray.emptyWithCapacity (4 * n)
  for k in [0:n] do
    let v := Wav.sampleAt d bytes (start + k * bytes) >>> shift
    let u := v.toInt32.toUInt32
    out := (((out.push u.toUInt8).push (u >>> 8).toUInt8).push (u >>> 16).toUInt8).push (u >>> 24).toUInt8
  return ⟨f, ⟨out⟩⟩

#guard (I32Array.toSpec ⟨⟨#[1, 0, 0, 0, 0xff, 0xff, 0xff, 0xff, 0, 0, 0, 0x80]⟩⟩) == #[1, -1, -2 ^ 31]

end VeriCut
