import Lossy.Proofs.Frame
import Lossy.Proofs.Quantize

namespace Lossy.Flac
open Reader

theorem readHeader_ok {x : Pcm} (hx : x.Valid) :
    Parses readHeader (x.rate, x.chans.length, x.bits, x.length) (streamHeader x) := by
  simp only [readHeader, streamHeader, List.append_assoc]
  refine (Parses.expect (k := 32) (n := 0x664C6143) (by decide)).bind ?_
  refine (Parses.expect (k := 8) (n := 0x80) (by decide)).bind ?_
  refine (Parses.expect (k := 24) (n := 34) (by decide)).bind ?_
  refine (Parses.expect (k := 16) (n := blockSize) (by decide)).bind ?_
  refine (Parses.expect (k := 16) (n := blockSize) (by decide)).bind ?_
  refine (Parses.expect (k := 24) (n := 0) (by decide)).bind ?_
  refine (Parses.expect (k := 24) (n := 0) (by decide)).bind ?_
  refine (Parses.nat_lt (k := 20) (n := x.rate) hx.rate.2).bind ?_
  refine (Parses.nat_lt (k := 3) (n := x.chans.length - 1) (by have := hx.chans; omega)).bind ?_
  refine (Parses.nat_lt (k := 5) (n := x.bits - 1) (by have := hx.bits; omega)).bind ?_
  refine (Parses.nat_lt (k := 36) (n := x.length) (by have := hx.short; omega)).bind ?_
  refine ((Parses.expect (k := 128) (n := 0) (by decide)).bind
    (Parses.pure (x.rate, x.chans.length - 1 + 1, x.bits - 1 + 1, x.length))).congr ?_ ?_
  · have := hx.chans; have := hx.bits
    simp only [Prod.mk.injEq]; exact ⟨trivial, by omega, by omega, trivial⟩
  · simp

theorem at_encode_frames {β : Type} (g : β → List Bool) (h8 : ∀ f, (g f).length % 8 = 0) :
    ∀ (fs : List β) (out : ByteArray) (L : List Bool), At out 0 L → L.length = 8 * out.size →
      At (fs.foldl (fun out f => packInto out (g f)) out) 0 (L ++ fs.flatMap g)
  | [], out, L, h, _ => by simpa using h
  | f :: fs, out, L, h, hl => by
    simp only [List.foldl_cons, List.flatMap_cons, ← List.append_assoc]
    refine at_encode_frames g h8 fs _ _ ?_ ?_
    · rw [At.append_iff]
      refine ⟨h.packInto _ (h8 f), ?_⟩
      simpa [hl] using at_packInto out (g f) (h8 f)
    · rw [size_packInto _ _ (h8 f), List.length_append, hl]
      have := h8 f; omega

theorem at_encode (q : Nat) (x : Pcm) :
    At (encode q x) 0 (streamHeader x ++
      (List.range (frameCount x.length)).flatMap fun f => frameBits x.bits (encodeFrame q x f)) := by
  have hh : (streamHeader x).length = 336 := by simp [streamHeader]
  refine at_encode_frames _ (fun f => length_frameBits _ _) _ _ _ ?_ ?_
  · simpa using at_packInto .empty (streamHeader x) (by rw [hh])
  · rw [size_packInto _ _ (by rw [hh]), hh]; rfl

/-! The frames `encode` writes. -/

theorem length_block {x : Pcm} (hx : x.Valid) {f : Nat} {b : List Int} (hb : b ∈ block x f) :
    b.length = min blockSize (x.length - f * blockSize) := by
  simp only [block, List.mem_map] at hb
  obtain ⟨c, hc, rfl⟩ := hb
  simp [hx.sizes c hc]

theorem mem_block {x : Pcm} {f : Nat} {b : List Int} (hb : b ∈ block x f) {v : Int} (hv : v ∈ b) :
    ∃ c ∈ x.chans, v ∈ c := by
  simp only [block, List.mem_map] at hb
  obtain ⟨c, hc, rfl⟩ := hb
  refine ⟨c, hc, ?_⟩
  rw [Array.toList_extract] at hv
  rw [List.extract_eq_take_drop] at hv
  exact Array.mem_toList_iff.mp (List.mem_of_mem_drop (List.mem_of_mem_take hv))

theorem frameCount_le {n : Nat} (hn : n < 2 ^ 32) : frameCount n ≤ 2 ^ 20 := by
  simp only [frameCount, blockSize]; omega

theorem encodeFrame_ok {q : Nat} {x : Pcm} (hx : x.Valid) {f : Nat} (hf : f < frameCount x.length) :
    FrameOk x.bits (encodeFrame q x f) ∧
      samplesOf (encodeFrame q x f).size (encodeFrame q x f).subs =
        (block x f).map (·.map (roundTo x.bits (shift q x f))) := by
  have hF := frameCount_le hx.short
  have hb : 1 ≤ x.bits := by have := hx.bits; omega
  have hround : ∀ b ∈ block x f, ∀ v ∈ b.map (roundTo x.bits (shift q x f)),
      -2 ^ (x.bits - 1) ≤ v ∧ v < 2 ^ (x.bits - 1) := by
    intro b hb' v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    obtain ⟨c, hc, huc⟩ := mem_block hb' hu
    have ⟨hlo, hhi⟩ := hx.range c hc u huc
    have := (roundTo_spec (s := shift q x f) hb hlo hhi).1.2
    simp only [lo, hi] at this; omega
  have faith : ∀ b ∈ block x f, Faithful x.bits (b.map (roundTo x.bits (shift q x f)))
      (analyze x.bits (b.map (roundTo x.bits (shift q x f)))) :=
    fun b hb' => analyze_ok hb (hround b hb')
  have hsize : ∀ b ∈ block x f, (b.map (roundTo x.bits (shift q x f))).length =
      (encodeFrame q x f).size := by
    intro b hb'; simp only [List.length_map, length_block hx hb', encodeFrame]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have := hx.chans; simp [encodeFrame, block]; omega
  · simp only [encodeFrame]; omega
  · simp only [encodeFrame, frameCount, blockSize] at hf ⊢; omega
  · intro ws hws
    simp only [encodeFrame, List.mem_map] at hws
    obtain ⟨b, hb', rfl⟩ := hws
    have := faith b hb'
    rw [← hsize b hb']
    exact ⟨this.1, this.2.1⟩
  · simp only [samplesOf, encodeFrame, List.map_map]
    apply List.map_congr_left
    intro b hb'
    have := (faith b hb').2.2
    simp only [List.length_map] at this
    rw [length_block hx hb'] at this
    exact this

/-! Putting the blocks back together. -/

theorem join_blocks (chans : List (Array Int)) (h : Nat → Array Int → List Int) :
    ∀ (fs : List Nat) (A : Array Int → Array Int),
      (fs.map fun f => chans.map (h f)).foldl
          (fun acc b => List.zipWith (fun c s => c ++ s.toArray) acc b) (chans.map A) =
        chans.map fun c => fs.foldl (fun acc f => acc ++ (h f c).toArray) (A c)
  | [], A => by simp
  | f :: fs, A => by
    simp only [List.map_cons, List.foldl_cons, List.zipWith_map, List.zipWith_self]
    exact join_blocks chans h fs (fun c => A c ++ (h f c).toArray)

theorem concat_blocks (L : List Int) (g : Nat → Int → Int) :
    ∀ F, (List.range F).foldl (fun acc f => acc ++ ((L.drop (f * blockSize)).take blockSize).map (g f)) [] =
      (L.take (F * blockSize)).mapIdx fun i v => g (i / blockSize) v
  | 0 => by simp
  | F + 1 => by
    rw [List.range_succ, List.foldl_append, concat_blocks L g F]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [show (F + 1) * blockSize = F * blockSize + blockSize by rw [Nat.succ_mul],
      List.take_add, List.mapIdx_append]
    congr 1
    by_cases hF : F * blockSize ≤ L.length
    · rw [List.length_take, Nat.min_eq_left hF]
      apply List.ext_getElem (by simp)
      intro i h₁ h₂
      simp only [List.getElem_map, List.getElem_mapIdx]
      congr 1
      simp only [List.length_map, List.length_take] at h₁
      have : i < blockSize := by omega
      rw [show (i + F * blockSize) / blockSize = F by
        rw [Nat.add_mul_div_right _ _ (by decide : 0 < blockSize), Nat.div_eq_of_lt this, Nat.zero_add]]
    · rw [List.drop_eq_nil_of_le (by omega)]; simp only [List.take_nil, List.map_nil, List.mapIdx_nil]

theorem join_encode {q : Nat} {x : Pcm} (hx : x.Valid) :
    join x.chans.length ((List.range (frameCount x.length)).map fun f =>
      (block x f).map (·.map (roundTo x.bits (shift q x f)))) = (quantize q x).chans := by
  simp only [join, block, List.map_map]
  rw [show List.replicate x.chans.length (#[] : Array Int) = x.chans.map fun _ => #[] by
      rw [List.map_const'],
    show (fun f => List.map ((fun l => List.map (roundTo x.bits (shift q x f)) l) ∘
      fun c => (c.extract (f * blockSize) (f * blockSize + blockSize)).toList) x.chans) =
      (fun f => x.chans.map fun c => ((c.extract (f * blockSize) (f * blockSize + blockSize)).toList.map
        (roundTo x.bits (shift q x f)))) from rfl,
    join_blocks]
  simp only [quantize]
  apply List.map_congr_left
  intro c hc
  apply Array.ext'
  have key := concat_blocks c.toList (fun f => roundTo x.bits (shift q x f)) (frameCount x.length)
  rw [List.take_of_length_le (by
    simp only [Array.length_toList, hx.sizes c hc, frameCount, blockSize]; omega)] at key
  rw [Array.toList_mapIdx, ← key]
  -- both sides fold appends; compare their lists
  generalize List.range (frameCount x.length) = fs
  suffices ∀ (acc : Array Int) (lacc : List Int), acc.toList = lacc →
      (fs.foldl (fun acc f => acc ++ ((c.extract (f * blockSize) (f * blockSize + blockSize)).toList.map
        (roundTo x.bits (shift q x f))).toArray) acc).toList =
      fs.foldl (fun acc f => acc ++ ((c.toList.drop (f * blockSize)).take blockSize).map
        (roundTo x.bits (shift q x f))) lacc from this #[] [] rfl
  induction fs with
  | nil => intro acc lacc h; simpa using h
  | cons f fs ih =>
    intro acc lacc h
    simp only [List.foldl_cons]
    apply ih
    simp [h, Array.toList_extract, List.extract_eq_take_drop]

end Lossy.Flac
