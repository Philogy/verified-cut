import VeriCut.Spec.Stream

/-!
# Spec: export plans and what a correct export means

Trusted surface. An export plan is a list of segments, in output order. A
`copy` segment copies source packets verbatim. An `encode` segment hands the
decoded source pictures to an encoder (VideoToolbox in the app). The encoder is
a black box with a stated contract (`Encoder`): it produces a self-contained
stream that decodes to pictures `approx`-close to its input. Lossy codecs only
promise closeness, so `approx` is a parameter. Nothing is assumed about it,
except reflexivity where a theorem says so.
-/

namespace VeriCut

/-- Pointwise relation between two lists of the same length. -/
inductive AllRel {β γ : Type} (R : β → γ → Prop) : List β → List γ → Prop
  | nil : AllRel R [] []
  | cons {x y xs ys} : R x y → AllRel R xs ys → AllRel R (x :: xs) (y :: ys)

/-- `s` decodes to pictures pointwise `approx`-close to `pics`, one per packet. -/
def DecodesTo {α Pic : Type} (c : Codec α Pic) (approx : Pic → Pic → Prop) (s : Stream α)
    (pics : List Pic) : Prop :=
  AllRel approx (decode c s) pics

/-- One piece of an export plan. Both carry source decode-order indices. -/
inductive Segment
  | copy (ks : List Nat)
  | encode (ks : List Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

def Segment.frames : Segment → List Nat
  | .copy ks => ks
  | .encode ks => ks

def Segment.isCopy : Segment → Bool
  | .copy _ => true
  | .encode _ => false

/-- **Contract for the hardware encoder** (trusted, not proven). Whatever
`encode` is, it must produce a well-formed, self-contained stream whose
decoded pictures are pointwise `approx`-close to the pictures it was given. -/
structure Encoder (α Pic : Type) (c : Codec α Pic) (approx : Pic → Pic → Prop) where
  encode : List Pic → Stream α
  wellFormed : ∀ pics, (encode pics).WellFormed
  faithful : ∀ pics, DecodesTo c approx (encode pics) pics

variable {α Pic : Type} {c : Codec α Pic} {approx : Pic → Pic → Prop}

/-- The compressed packets one segment contributes, before concatenation. -/
def Segment.render (s : Stream α) (enc : Encoder α Pic c approx) :
    Segment → Stream α
  | .copy ks => extract s ks
  | .encode ks => enc.encode (ks.map (picture c s))

/-- The exported stream. -/
def exportPlan (s : Stream α) (enc : Encoder α Pic c approx)
    (plan : List Segment) : Stream α :=
  concatStreams (plan.map (Segment.render s enc))

/-- What the user asked for: the source pictures of the planned frames, in
plan order. -/
def target (c : Codec α Pic) (s : Stream α) (plan : List Segment) : List Pic :=
  (plan.map fun seg => seg.frames.map (picture c s)).flatten

/-- One re-encode request of a timeline: the frames of clip number `clip` that an
`encode` segment lists (source decode-order indices, in display order). -/
structure Job where
  clip   : Nat
  frames : List Nat
  deriving Repr, BEq, DecidableEq, Inhabited

/-- **Contract for one re-encode job** (trusted, not proven), the per-job form
of `Encoder`: the result `out` for frames `ks` of source `s` is a well-formed,
self-contained stream that decodes pointwise `approx`-close to those frames'
source pictures. -/
def JobContract (c : Codec α Pic) (approx : Pic → Pic → Prop) (s : Stream α)
    (ks : List Nat) (out : Stream α) : Prop :=
  out.WellFormed ∧ DecodesTo c approx out (ks.map (picture c s))

/-- A plan may only copy dependency-closed packet sets. -/
def PlanValid (s : Stream α) (plan : List Segment) : Prop :=
  ∀ ks, Segment.copy ks ∈ plan → CopySet s ks

end VeriCut
