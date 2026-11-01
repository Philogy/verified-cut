import VeriCut.Spec.Planner

/-!
# Implementation: the smart-cut planner

Runs in O(n) for the copyable table plus a closure check per copy run.
Proven against the spec in `Proofs/Impl.lean`.
-/

namespace VeriCut

variable {α : Type} [Inhabited α]

/-- One table entry, using the already-computed entries for earlier frames. -/
def copyEntry (s : Stream α) (r : DisplayRange) (t : Array Bool) (i : Nat) : Bool :=
  wanted s r i && (s.getD i default).refs.all fun x => decide (x < i) && t.getD x false

/-- `copyTable s r k` holds `copyable s r i` for every `i < k`. -/
def copyTable (s : Stream α) (r : DisplayRange) : Nat → Array Bool
  | 0 => #[]
  | k + 1 => let t := copyTable s r k; t.push (copyEntry s r t k)

/-- Split a list into maximal runs on which `f` is constant. -/
def runs (f : Nat → Bool) : List Nat → List (Bool × List Nat)
  | [] => []
  | x :: xs =>
    match runs f xs with
    | [] => [(f x, [x])]
    | (b, run) :: rest =>
      if b == f x then (b, x :: run) :: rest else (f x, [x]) :: (b, run) :: rest

/-- Runtime check that a packet set is dependency-closed. -/
def checkClosed (s : Stream α) (ks : List Nat) : Bool :=
  ks.all fun k => (s.getD k default).refs.all fun x => ks.contains x

/-- Wanted frames in display order. -/
def displayOrder (s : Stream α) (r : DisplayRange) : List Nat :=
  ((List.range s.length).filter (wanted s r)).mergeSort
    fun i j => (s.getD i default).pts ≤ (s.getD j default).pts

/-- Turn one display-order run into a segment. A copyable run is copied in
decode order. If it is somehow not closed, it falls back to re-encoding. -/
def mkSegment (s : Stream α) (b : Bool) (run : List Nat) : Segment :=
  if b then
    let ks := (List.range s.length).filter fun i => run.contains i
    if checkClosed s ks then .copy ks else .encode run
  else .encode run

/-- **The planner.** Display-ordered segments covering exactly the wanted frames. -/
def plan (s : Stream α) (r : DisplayRange) : List Segment :=
  let t := copyTable s r s.length
  (runs (fun i => t.getD i false) (displayOrder s r)).map fun p => mkSegment s p.1 p.2

end VeriCut
