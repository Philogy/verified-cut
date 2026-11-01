import VeriCut.Spec.Export

/-!
# Implementation: the exporter

The export loop, written once against an abstract encode effect. The CLI runs
it in `IO`, where `encode` calls ffmpeg (`Main.lean`). The proofs run it with
a fixed function in place of the encoder (`PureEncode`), and
`Proofs/Run.lean` shows the result decodes to the requested pictures for every
function meeting `JobContract`.
-/

namespace VeriCut

/-- The one effect the exporter performs: re-encode a job. `α` is the packet type. -/
class MonadEncode (α : outParam Type) (m : Type → Type) where
  encode : Job → m (Stream α)

variable {α : Type} {m : Type → Type} [Monad m] [MonadEncode α m]

/-- `extract`, indexing the stream as an array (a list index is O(n)). -/
def extractA (a : Array (Packet α)) (ks : List Nat) : Stream α :=
  ks.filterMap fun k => a[k]?.map fun p => { p with refs := p.refs.map (ks.idxOf ·) }

/-- The packets one segment of clip number `clip` (source `s`) contributes. -/
def renderSegment (clip : Nat) (s : Stream α) : Segment → m (Stream α)
  | .copy ks => pure (extractA s.toArray ks)
  | .encode ks => MonadEncode.encode { clip, frames := ks }

/-- Render the segments of clips `i, i+1, …`. -/
def exportFrom (i : Nat) : List (Stream α × List Segment) → m (List (List (Stream α)))
  | [] => pure []
  | (s, segs) :: rest => do
    let out ← segs.mapM (renderSegment i s)
    return out :: (← exportFrom (i + 1) rest)

/-- **The exporter.** Given each clip's stream and plan, the packets of every
segment, grouped by clip, in output order. The output stream is the
`concatStreams` of all of them. -/
def exportTimeline (clips : List (Stream α × List Segment)) : m (List (List (Stream α))) :=
  exportFrom 0 clips

/-- The encoder replaced by a fixed function from jobs to streams. -/
abbrev PureEncode (α : Type) := ReaderT (Job → Stream α) Id

instance : MonadEncode α (PureEncode α) where
  encode j := fun f => f j

end VeriCut
