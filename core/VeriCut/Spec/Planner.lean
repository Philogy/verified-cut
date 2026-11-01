import VeriCut.Spec.Export

/-!
# Spec: which frames a cut can copy

Trusted surface. A cut keeps the source frames whose display position `pts`
lies in `[lo, hi)`. The reference definition `copyable` says a frame may be
copied iff it is wanted and everything it depends on may be copied.
`Proofs/Planner.lean` shows this is the *largest* dependency-closed set of
wanted frames, so no correct copy-based plan copies more.
-/

namespace VeriCut

/-- Keep the frames with display position in `[lo, hi)`. -/
structure DisplayRange where
  lo : Nat
  hi : Nat
  deriving Repr, BEq, DecidableEq

variable {α : Type}

/-- Does the user want decode-order frame `i`? -/
def wanted (s : Stream α) (r : DisplayRange) (i : Nat) : Bool :=
  if h : i < s.length then r.lo ≤ s[i].pts && s[i].pts < r.hi else false

/-- Reference definition: frame `i` can be copied iff it is wanted and all of
its references can be copied. (Clear but slow; `Impl.Planner` is the fast
version, proven equal.) -/
def copyable (s : Stream α) (r : DisplayRange) (i : Nat) : Bool :=
  if h : i < s.length then
    wanted s r i && s[i].refs.attach.all fun ⟨x, _⟩ => if x < i then copyable s r x else false
  else false
termination_by i

end VeriCut
