/-!
# Spec: compressed video streams and what they decode to

This file is part of the **trusted surface**. Read it before trusting any theorem.

A compressed video stream is a list of packets in *decode order*. Each packet
carries opaque compressed bytes (`data`) and the decode-order indices of the
earlier packets whose *decoded pictures* it predicts from (`refs`).

We never model the codec's arithmetic. Instead a `Codec` is any function that
turns a packet's bytes plus its reference pictures into a picture. Every theorem
is stated for **all** codecs, so it holds for H.264, HEVC and ProRes alike,
and for Apple's VideoToolbox decoder in particular, provided that decoder
really is a function of (bytes, reference pictures). That is the one modelling
assumption, and it is the definition of a block-based predictive codec.
-/

namespace VeriCut

/-- One compressed frame. `refs` are decode-order indices of the packets whose
decoded pictures this packet predicts from. `pts` is its display position. -/
structure Packet (α : Type) where
  data : α
  refs : List Nat := []
  pts  : Nat := 0
  deriving Repr, Inhabited, BEq, DecidableEq

/-- A stream: packets in decode order. -/
abbrev Stream (α : Type) := List (Packet α)

/-- Every reference points strictly backwards in decode order: a decoder can
process the packets one by one. Real codecs guarantee this by construction. -/
def Stream.WellFormed {α} (s : Stream α) : Prop :=
  ∀ i (h : i < s.length), ∀ r ∈ s[i].refs, r < i

/-- An abstract decoder: picture of a packet from its bytes and its reference
pictures (in the order listed in `refs`). `blank` is what a reference to a
missing or later packet decodes to. In a well-formed stream it is never used. -/
structure Codec (α Pic : Type) where
  step  : α → List Pic → Pic
  blank : Pic

/-- The picture a decoder produces for decode-order packet `i` of stream `s`. -/
def picture {α Pic} (c : Codec α Pic) (s : Stream α) (i : Nat) : Pic :=
  if h : i < s.length then
    c.step s[i].data (s[i].refs.map fun r => if r < i then picture c s r else c.blank)
  else c.blank
termination_by i
decreasing_by assumption

/-- Decoding a whole stream: one picture per packet, in decode order. -/
def decode {α Pic} (c : Codec α Pic) (s : Stream α) : List Pic :=
  (List.range s.length).map (picture c s)

/-- A set of packet indices (given as a list) is *dependency-closed* if every
reference of every member is also a member. These are the packets that can be
copied byte-for-byte without their pictures changing. -/
def DepClosed {α} (s : Stream α) (ks : List Nat) : Prop :=
  ∀ k ∈ ks, ∀ (h : k < s.length), ∀ r ∈ s[k].refs, r ∈ ks

/-- A valid selection of packets to copy: strictly increasing (keeps decode
order), in bounds, and dependency-closed. -/
structure CopySet {α} (s : Stream α) (ks : List Nat) : Prop where
  sorted : ks.Pairwise (· < ·)
  bound  : ∀ k ∈ ks, k < s.length
  closed : DepClosed s ks

/-- Copy the selected packets byte-for-byte, rewriting only the reference
indices so they point at the same packets' new positions. This is exactly what
a stream-copy muxer does. -/
def extract {α} [Inhabited α] (s : Stream α) (ks : List Nat) : Stream α :=
  ks.map fun k =>
    let p := s.getD k default
    { p with refs := p.refs.map (ks.idxOf ·) }

/-- Move a stream so it can be appended after `n` packets. -/
def shift {α} (n : Nat) (s : Stream α) : Stream α :=
  s.map fun p => { p with refs := p.refs.map (· + n) }

/-- Concatenate self-contained streams, fixing up reference indices. -/
def concatStreams {α} : List (Stream α) → Stream α
  | [] => []
  | x :: xs => x ++ shift x.length (concatStreams xs)

end VeriCut
