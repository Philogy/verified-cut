import Lossy.Proofs.Bits

namespace Lossy

theorem bitAt_push_lt {out : ByteArray} {b : UInt8} {i : Nat} (h : i < 8 * out.size) :
    bitAt (out.push b) i = bitAt out i := by
  have hs : out.size = out.data.size := rfl
  have hi : i / 8 < out.data.size := by omega
  simp only [bitAt, ByteArray.push, Array.size_push, dif_pos hi, dif_pos (show i / 8 < out.data.size + 1 by omega)]
  rw [Array.getElem_push_lt]

theorem byte_testBit' : ∀ (r : Fin 8) (b0 b1 b2 b3 b4 b5 b6 b7 : Bool),
    (byte b0 b1 b2 b3 b4 b5 b6 b7).toNat.testBit (7 - r) = [b0, b1, b2, b3, b4, b5, b6, b7][r] := by
  decide

theorem byte_testBit (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) (r : Nat) (hr : r < 8) :
    (byte b0 b1 b2 b3 b4 b5 b6 b7).toNat.testBit (7 - r) = [b0, b1, b2, b3, b4, b5, b6, b7][r] :=
  byte_testBit' ⟨r, hr⟩ b0 b1 b2 b3 b4 b5 b6 b7

theorem short_nil {l : List Bool} (h : l.length % 8 = 0)
    (hl : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) (rest : List Bool),
      l = b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest → False) : l = [] := by
  match l with
  | [] => rfl
  | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
  | [_, _, _, _, _, _, _] => simp at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => exact absurd rfl (hl _ _ _ _ _ _ _ _ _)

theorem bitAt_push_last {out : ByteArray} {b : UInt8} {r : Nat} (hr : r < 8) :
    bitAt (out.push b) (8 * out.size + r) = b.toNat.testBit (7 - r) := by
  have hs : out.size = out.data.size := rfl
  have hq : (8 * out.size + r) / 8 = out.data.size := by omega
  have hm : (8 * out.size + r) % 8 = r := by omega
  simp only [bitAt, ByteArray.push, Array.size_push, hq, hm, dif_pos (Nat.lt_succ_self _)]
  rw [Array.getElem_push_eq]

theorem size_packInto (out : ByteArray) (l : List Bool) (h : l.length % 8 = 0) :
    (packInto out l).size = out.size + l.length / 8 := by
  induction out, l using packInto.induct with
  | case1 out b0 b1 b2 b3 b4 b5 b6 b7 rest ih =>
    simp only [packInto]; rw [ih (by simp at h; omega)]; simp; omega
  | case2 l out hl => cases short_nil h hl; simp [packInto]

theorem bitAt_packInto_lt (out : ByteArray) (l : List Bool) {i : Nat} (hi : i < 8 * out.size) :
    bitAt (packInto out l) i = bitAt out i := by
  induction out, l using packInto.induct with
  | case1 out b0 b1 b2 b3 b4 b5 b6 b7 rest ih =>
    simp only [packInto]
    rw [ih (by simp; omega), bitAt_push_lt hi]
  | case2 l out hl =>
    match l with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest => exact absurd rfl (hl _ _ _ _ _ _ _ _ _)
    | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
    | [_, _, _, _, _, _, _] => simp [packInto]

theorem at_packInto (out : ByteArray) (l : List Bool) (h : l.length % 8 = 0) :
    At (packInto out l) (8 * out.size) l := by
  induction out, l using packInto.induct with
  | case1 out b0 b1 b2 b3 b4 b5 b6 b7 rest ih =>
    simp only [packInto]
    have ih := ih (by simp at h; omega)
    simp only [ByteArray.size_push] at ih
    have e : b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =
      [b0, b1, b2, b3, b4, b5, b6, b7] ++ rest := rfl
    rw [e, At.append_iff]
    refine ⟨⟨?_, fun r hr => ?_⟩, by simpa [Nat.mul_add] using ih⟩
    · have := ih.1; simp at this ⊢; omega
    · simp only [List.length_cons, List.length_nil] at hr
      rw [bitAt_packInto_lt _ _ (by simp; omega), bitAt_push_last hr, byte_testBit _ _ _ _ _ _ _ _ _ hr]
  | case2 l out hl => cases short_nil h hl; simp [packInto, At]

/-- Bits already in `out` survive appending more. -/
theorem At.packInto {out : ByteArray} {pos : Nat} {l : List Bool} (h : At out pos l)
    (l' : List Bool) (h' : l'.length % 8 = 0) : At (Lossy.packInto out l') pos l := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [size_packInto _ _ h']; have := h.1; omega
  · rw [bitAt_packInto_lt _ _ (by have := h.1; omega)]; exact h.2 i hi

end Lossy
