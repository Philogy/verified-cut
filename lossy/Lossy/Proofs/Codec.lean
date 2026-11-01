import Lossy.Proofs.Stream

namespace Lossy
open Flac

theorem decode_encode {q : Nat} {x : Pcm} (hx : x.Valid) : decode (encode q x) = some (quantize q x) := by
  have hframes : ∀ f ∈ List.range (frameCount x.length),
      Parses8 (readFrame x.bits x.chans.length)
        ((fun f => (block x f).map (·.map (roundTo x.bits (shift q x f)))) f)
        (frameBits x.bits (encodeFrame q x f)) ∧ (frameBits x.bits (encodeFrame q x f)).length % 8 = 0 := by
    intro f hf
    have ⟨ok, hs⟩ := encodeFrame_ok (q := q) hx (List.mem_range.mp hf)
    have hch : (encodeFrame q x f).subs.length = x.chans.length := by simp [encodeFrame, block]
    refine ⟨?_, length_frameBits _ _⟩
    have := readFrame_ok ok
    rw [hch, hs] at this
    exact this
  have hm := Parses8.many _ hframes
  rw [List.length_range] at hm
  have hh : (streamHeader x).length % 8 = 0 := by simp [streamHeader]
  have hq : quantize q x = ⟨x.rate, x.bits, join x.chans.length ((List.range (frameCount x.length)).map
      fun f => (block x f).map (·.map (roundTo x.bits (shift q x f))))⟩ := by
    rw [join_encode hx]; rfl
  have hs : Parses8 readStream (quantize q x) (streamHeader x ++
      ((List.range (frameCount x.length)).flatMap (fun f => frameBits x.bits (encodeFrame q x f)) ++ [])) := by
    unfold readStream
    refine Parses8.bind (Parses.parses8 (readHeader_ok hx)) hh ?_
    refine Parses8.bind hm (flatMap_len8 _ fun f hf => (hframes f hf).2) ?_
    rw [hq]
    exact Parses.parses8 (Parses.pure _)
  have := hs (encode q x) 0 rfl (by simpa using at_encode q x)
  simp only [decode, this, Option.map_some]

end Lossy
