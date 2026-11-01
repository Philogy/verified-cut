import VeriCut.Proofs.Impl
import VeriCut.Proofs.Export
import VeriCut.Correctness

/-!
# Examples: hypotheses are satisfiable, the spec rejects bad cuts

Two GOPs of three frames, decode order = display order:
`I0 P1 P2 | I3 P4 P5`, where each P-frame depends on the previous frame.
-/

namespace VeriCut.Examples
open VeriCut

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

/-- A perfect toy encoder: each requested frame becomes an intra packet
carrying its picture. Under `toy`, an intra packet decodes to its data. -/
def intraEnc (s : Stream Nat) (j : Job) : Stream Nat :=
  j.frames.map fun k => { data := picture toy s k }

theorem intraEnc_contract (s : Stream Nat) (j : Job) :
    JobContract toy (· = ·) s j.frames (intraEnc s j) := by
  refine ⟨?_, ?_⟩
  · intro i hi r hr; simp [intraEnc] at hr
  · have : decode toy (intraEnc s j) = j.frames.map (picture toy s) := by
      apply List.ext_getElem (by simp [length_decode, intraEnc])
      intro i h1 h2
      rw [getElem_decode, picture_eq _ _ _ (by simpa [length_decode] using h1)]
      simp [intraEnc, toy]
    unfold DecodesTo; rw [this]; exact AllRel.refl (fun _ => rfl) _

/-- A two-clip timeline for the examples below. -/
def twoClips : Timeline Nat := [⟨gop2, ⟨1, 5⟩⟩, ⟨bframes, ⟨0, 3⟩⟩]

/-- The hypotheses of `exportTimeline_correct` hold on a concrete two-clip
timeline, and the conclusion is equality since this encoder is exact. -/
example : decode toy (twoClips.exportWith fun j => intraEnc (if j.clip = 0 then gop2 else bframes) j) =
    twoClips.target toy := by
  apply AllRel.eq_of
  apply exportTimeline_correct toy (· = ·) twoClips _ (fun _ => rfl)
  · intro cut hcut; simp [twoClips] at hcut
    rcases hcut with rfl | rfl <;> (unfold Stream.WellFormed; decide)
  · intro ⟨i, ks⟩ cut hcut _
    rcases i with _ | _ | _ <;> simp [twoClips] at hcut <;> subst hcut
    · exact intraEnc_contract gop2 ⟨0, ks⟩
    · exact intraEnc_contract bframes ⟨1, ks⟩

-- The exporter, run with the toy encoder: frames 1, 2 re-encoded as intra
-- packets holding their pictures, 3, 4 copied with references renumbered.
#guard ((exportTimeline (m := PureEncode Nat) [(gop2, plan gop2 ⟨1, 5⟩)]).run (intraEnc gop2)).flatten
  == [[{ data := 12 }, { data := 123 }], [{ data := 4, pts := 3 }, { data := 5, refs := [0], pts := 4 }]]

end VeriCut.Examples
