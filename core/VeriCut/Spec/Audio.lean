/-!
# Spec: copying audio

Trusted surface, the definitions `exportAudio_exact` and `exportAudio_synced`
(`Correctness.lean`) are stated with.

AAC-LC packets are not self-contained: the MDCT windows of neighbouring
packets overlap by half, so the samples of packet `k` are the overlap-add of
packet `k`'s transform and packet `k - 1`'s. An `AudioCodec` is any decoder
with that shape: a packet's samples are a function of its own bytes and the
previous packet's (`none` where decoding starts). Every theorem holds for
every such codec.

So audio is cut by copying packets. Each cut copies one packet more than it
plays (the pre-roll, whose output is wrong after a splice) and an edit list
says which media samples to present. Cut lengths are rounded on the output
video clock, not per cut, so rounding never accumulates.
-/

namespace VeriCut

/-- An audio decoder with one packet of overlap. `frame prev p` is what packet
`p` decodes to after packet `prev`, or as the first packet decoded (`none`). -/
structure AudioCodec (α S : Type) where
  frame : Option α → α → List S

variable {α S : Type}

/-- Every packet decodes to `n` samples (1024 for AAC-LC). -/
def AudioCodec.FrameLength (c : AudioCodec α S) (n : Nat) : Prop :=
  ∀ prev p, (c.frame prev p).length = n

/-- Decode packets in order, `prev` being the packet decoded just before. -/
def decodeAudioAfter (c : AudioCodec α S) : Option α → List α → List S
  | _, [] => []
  | prev, p :: ps => c.frame prev p ++ decodeAudioAfter c (some p) ps

/-- The samples a decoder outputs for a packet list, from a fresh start. -/
def decodeAudio (c : AudioCodec α S) (s : List α) : List S := decodeAudioAfter c none s

/-- One entry of an edit list: present `len` media samples from `start`, or
`len` samples of silence. -/
inductive Edit
  | media (start len : Nat)
  | empty (len : Nat)
  deriving Repr, BEq, DecidableEq

/-- What a player outputs for decoded media samples `pcm` and an edit list. -/
def present (silence : S) (pcm : List S) (edits : List Edit) : List S :=
  edits.flatMap fun
    | .media start len => (pcm.drop start).take len
    | .empty len => List.replicate len silence

/-- The audio of one cut: `lead` samples of silence, source media samples
`[start, start + len)`, `trail` samples of silence. The silence covers the
part of the cut the source audio doesn't reach. -/
structure AudioCut (α : Type) where
  source : List α
  lead   : Nat := 0
  start  : Nat
  len    : Nat
  trail  : Nat := 0

/-- What a cut should sound like: the source samples it names, padded. -/
def AudioCut.target (c : AudioCodec α S) (silence : S) (cut : AudioCut α) : List S :=
  List.replicate cut.lead silence ++ ((decodeAudio c cut.source).drop cut.start).take cut.len ++
    List.replicate cut.trail silence

/-- Its length in samples. -/
def AudioCut.length (cut : AudioCut α) : Nat := cut.lead + cut.len + cut.trail

/-- The first packet a cut copies, with packets of `n` samples: the one before
the packet holding sample `start`, so the splice lands in a packet that is
never presented. At the start of the source there is none. -/
def AudioCut.first (n : Nat) (cut : AudioCut α) : Nat := cut.start / n - 1

/-- The packets a cut copies: from `first` through the packet holding its last
sample. None if it plays no source samples. -/
def AudioCut.packets (n : Nat) (cut : AudioCut α) : List α :=
  if cut.len = 0 then [] else
    (cut.source.drop (cut.first n)).take ((cut.start + cut.len + n - 1) / n - cut.first n)

/-- The edits of a cut whose packets start at output media sample `at`. -/
def AudioCut.edits (n : Nat) (at_ : Nat) (cut : AudioCut α) : List Edit :=
  [.empty cut.lead, .media (at_ + cut.start - n * cut.first n) cut.len, .empty cut.trail]

/-- **The audio exporter.** The copied packets of all cuts, in order, and the
edit list that presents each cut's samples. -/
def exportAudio (n : Nat) : List (AudioCut α) → List α × List Edit :=
  go 0
where
  go (at_ : Nat) : List (AudioCut α) → List α × List Edit
    | [] => ([], [])
    | cut :: rest =>
      let ps := cut.packets n
      let after := go (at_ + n * ps.length) rest
      (ps ++ after.1, cut.edits n at_ ++ after.2)

/-! ## Placing each cut's audio on the output clock -/

/-- The audio sample nearest to time `t / rate` seconds, at `sampleRate` Hz
(halves round up). -/
def sampleAt (sampleRate rate t : Nat) : Nat := (2 * t * sampleRate + rate) / (2 * rate)

/-- One clip as the audio sees it: its source packets, how many media samples
the source has (its last packet may be cut short), the source media sample
(negative if before the first) shown with the clip's first video frame, and
its length in ticks of the output video clock. -/
structure AudioClip (α : Type) where
  source   : List α
  avail    : Nat
  srcStart : Int
  ticks    : Nat

/-- The audio of a clip whose video starts at tick `t0` of the output, with
packets of `n` samples: as many samples as lie between the samples nearest its
video start and end, the source's from `srcStart` on, silence where the source
has none. Only the timeline's first cut (`first`) may play the source's first
packet: elsewhere it has no pre-roll, and is silence. -/
def AudioClip.cut (n sampleRate rate : Nat) (first : Bool) (t0 : Nat) (clip : AudioClip α) :
    AudioCut α :=
  let total := sampleAt sampleRate rate (t0 + clip.ticks) - sampleAt sampleRate rate t0
  let from_ : Int := if first then 0 else n
  let lead := min total (from_ - clip.srcStart).toNat
  let avail := min clip.avail (n * clip.source.length)
  let start := min (max clip.srcStart from_).toNat avail
  let len := min (total - lead) (avail - start)
  { source := clip.source, lead, start, len, trail := total - lead - len }

/-- The cuts of a timeline of clips, starting at tick `t0`. -/
def audioCuts (n sampleRate rate : Nat) (first : Bool) : Nat → List (AudioClip α) → List (AudioCut α)
  | _, [] => []
  | t0, clip :: rest =>
    clip.cut n sampleRate rate first t0 :: audioCuts n sampleRate rate false (t0 + clip.ticks) rest

/-- The audio track for a timeline of clips: the copied packets and the edit
list. This is what `vericut export` writes. -/
def exportAudioClips (n sampleRate rate : Nat) (clips : List (AudioClip α)) : List α × List Edit :=
  exportAudio n (audioCuts n sampleRate rate true 0 clips)

/-- Output video tick at which clip `i` starts. -/
def videoStart (clips : List (AudioClip α)) (i : Nat) : Nat :=
  ((clips.take i).map (·.ticks)).sum

/-- Output audio sample at which cut `i` starts. -/
def audioStart (cuts : List (AudioCut α)) (i : Nat) : Nat :=
  ((cuts.take i).map (·.length)).sum

end VeriCut
