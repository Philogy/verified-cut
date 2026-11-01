import VeriCut.Spec.Planner

/-!
# Implementation: the smart-cut planner

Runs in O(n) for the copyable table plus a closure check per copy run.
It indexes the stream as an `Array` (`a = s.toArray`): `Stream` is a list,
and indexing it is O(n). Proven against the spec in `Proofs/Impl.lean`.
-/

namespace VeriCut

variable {α : Type}

/-- `wanted` on the stream as an array. -/
def wantedA (a : Array (Packet α)) (r : DisplayRange) (i : Nat) : Bool :=
  if h : i < a.size then r.lo ≤ a[i].pts && a[i].pts < r.hi else false

/-- One table entry, using the already-computed entries for earlier frames. -/
def copyEntry (a : Array (Packet α)) (r : DisplayRange) (t : Array Bool) (i : Nat) : Bool :=
  if h : i < a.size then
    wantedA a r i && a[i].refs.all fun x => decide (x < i) && t.getD x false
  else false

/-- `copyTable s.toArray r k` holds `copyable s r i` for every `i < k`. -/
def copyTable (a : Array (Packet α)) (r : DisplayRange) : Nat → Array Bool
  | 0 => #[]
  | k + 1 => let t := copyTable a r k; let e := copyEntry a r t k; t.push e

/-- Split a list into maximal runs on which `f` is constant. -/
def runs (f : Nat → Bool) : List Nat → List (Bool × List Nat)
  | [] => []
  | x :: xs =>
    match runs f xs with
    | [] => [(f x, [x])]
    | (b, run) :: rest =>
      if b == f x then (b, x :: run) :: rest else (f x, [x]) :: (b, run) :: rest

/-- Runtime check that a packet set is dependency-closed, given its members
as a table (`mem.getD k false` iff `k ∈ ks`). -/
def checkClosed (a : Array (Packet α)) (mem : Array Bool) (ks : List Nat) : Bool :=
  ks.all fun k => if h : k < a.size then a[k].refs.all fun x => mem.getD x false else true

/-- Wanted frames in display order. -/
def displayOrder (a : Array (Packet α)) (r : DisplayRange) : List Nat :=
  let ws := (List.finRange a.size).filter fun (i : Fin a.size) => wantedA a r i
  (ws.mergeSort fun i j => a[i].pts ≤ a[j].pts).map Fin.val

/-- Membership table of `run` for indices below `n`. -/
def memTable (n : Nat) (run : List Nat) : Array Bool :=
  run.foldl (fun m i => m.set! i true) (Array.replicate n false)

/-- Turn one display-order run into a segment. A copyable run is copied in
decode order. If it is somehow not closed, it falls back to re-encoding. -/
def mkSegment (a : Array (Packet α)) (b : Bool) (run : List Nat) : Segment :=
  if b then
    let mem := memTable a.size run
    let ks := (List.range a.size).filter fun i => mem.getD i false
    if checkClosed a mem ks then .copy ks else .encode run
  else .encode run

/-- **The planner.** Display-ordered segments covering exactly the wanted frames. -/
def plan (s : Stream α) (r : DisplayRange) : List Segment :=
  let a := s.toArray
  let t := copyTable a r a.size
  (runs (fun i => t.getD i false) (displayOrder a r)).map fun p => mkSegment a p.1 p.2

end VeriCut
