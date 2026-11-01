import SmartCut.Proofs.Impl
import SmartCut.Proofs.Export

/-!
# Examples: hypotheses are satisfiable, the spec rejects bad cuts

Two GOPs of three frames, decode order = display order:
`I0 P1 P2 | I3 P4 P5`, where each P-frame depends on the previous frame.
-/

namespace SmartCut.Examples
open SmartCut

/-- A toy codec on natural numbers: a picture is its packet's value plus ten
times the sum of its reference pictures. Changing any reference changes the picture. -/
def toy : Codec Nat Nat where
  step d refs := d + 10 * refs.sum
  blank := 0

def gop2 : Stream Nat :=
  [ { data := 1, refs := [],  pts := 0 }, { data := 2, refs := [0], pts := 1 },
    { data := 3, refs := [1], pts := 2 }, { data := 4, refs := [],  pts := 3 },
    { data := 5, refs := [3], pts := 4 }, { data := 6, refs := [4], pts := 5 } ]

/-- The hypotheses of `picture_extract` hold on a concrete input. -/
example : gop2.WellFormed := by unfold Stream.WellFormed; decide
example : CopySet gop2 [3, 4, 5] :=
  ⟨by decide, by decide, by unfold DepClosed; decide⟩

/-- The spec rejects a naive cut: frames 1..4 are not a valid copy set,
because frame 1 depends on dropped frame 0. -/
example : ¬ CopySet gop2 [1, 2, 3, 4] := by
  intro h
  have := h.closed 1 (by simp) (by decide) 0 (by decide)
  simp at this

-- Executable checks (compiled code, fail the build if false).
-- Copying a closed set reproduces the source pictures.
#guard decode toy (extract gop2 [3, 4, 5]) == [3, 4, 5].map (picture toy gop2)
-- Naively copying an unclosed set does NOT (frame 1 loses its reference).
#guard decode toy (extract gop2 [1, 2, 3, 4]) != [1, 2, 3, 4].map (picture toy gop2)
-- Cut display range [1, 5): frames 1, 2 must be re-encoded, 3, 4 copied.
#guard plan gop2 ⟨1, 5⟩ == [.encode [1, 2], .copy [3, 4]]
-- A keyframe-aligned cut copies everything.
#guard plan gop2 ⟨3, 6⟩ == [.copy [3, 4, 5]]
-- An intra-only stream copies any cut.
#guard plan ((List.range 6).map fun i => ({ data := i, pts := i } : Packet Nat)) ⟨2, 5⟩
  == [.copy [2, 3, 4]]

/-- B-frames: decode `I0 P3 B1 B2 | I4`, display 0 1 2 3 4. Cutting display
`[0, 3)` drops P3, which B1 and B2 depend on, so they are re-encoded. -/
def bframes : Stream Nat :=
  [ { data := 1, refs := [],  pts := 0 }, { data := 2, refs := [0], pts := 3 },
    { data := 3, refs := [1], pts := 1 }, { data := 4, refs := [2], pts := 2 },
    { data := 5, refs := [],  pts := 4 } ]

#guard plan bframes ⟨0, 3⟩ == [.copy [0], .encode [2, 3]]
#guard plan bframes ⟨0, 4⟩ == [.copy [0, 1, 2, 3]]

end SmartCut.Examples
