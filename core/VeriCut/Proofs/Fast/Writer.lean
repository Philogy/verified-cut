import VeriCut.Proofs.Bits
import VeriCut.Flac.Fast.Write

/-!
The fast writer writes the same bits as the spec's, so `Fast.writeFrame = Flac.writeFrame`.
-/

namespace VeriCut.Flac.Fast

@[simp] theorem pow2_eq (k : Nat) : pow2 k = 2 ^ k := by
  unfold pow2
  split
  · rename_i hk
    have hk' : (k.toUInt64).toNat = k := by
      rw [Nat.toUInt64, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    have hp : (2 : Nat) ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
    rw [UInt64.toNat_shiftLeft, hk', Nat.mod_eq_of_lt (by omega : k < 64)]
    simp [Nat.one_shiftLeft, Nat.mod_eq_of_lt hp]
  · rfl

def Writer.bits (w : Writer) : List Bool := bitsOf w.bytes ++ natBits w.n w.acc.toNat

theorem flush_bits (bytes : ByteArray) (acc : UInt64) (n : Nat) (h : n ≤ 64) :
    (Writer.flush bytes acc n h).bits = bitsOf bytes ++ natBits n acc.toNat := by
  induction n using Nat.strongRecOn generalizing bytes with
  | _ n ih =>
    unfold Writer.flush
    split
    · rename_i h8
      rw [ih _ (by omega), bitsOf_push, List.append_assoc]
      have e := natBits_add 8 (n - 8) acc.toNat
      rw [show 8 + (n - 8) = n by omega] at e
      rw [e]
      congr 2
      have hs : ((n - 8).toUInt64).toNat = n - 8 := by
        rw [Nat.toUInt64, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
      rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, hs, Nat.mod_eq_of_lt (by omega : n - 8 < 64),
        Nat.shiftRight_eq_div_pow]
      exact natBits_mod 8 8 _ (Nat.le_refl _)
    · rfl

theorem toNat_low (v k : Nat) (hk : k ≤ 56) :
    (v.toUInt64 &&& ((1 <<< k.toUInt64) - 1)).toNat = v % 2 ^ k := by
  have hk' : (k.toUInt64).toNat = k := by
    rw [Nat.toUInt64, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hp : (2 : Nat) ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  have h1 : ((1 : UInt64) <<< k.toUInt64).toNat = 2 ^ k := by
    rw [UInt64.toNat_shiftLeft, hk', Nat.mod_eq_of_lt (by omega : k < 64)]
    simp [Nat.one_shiftLeft, Nat.mod_eq_of_lt hp]
  have h2 : ((1 : UInt64) <<< k.toUInt64 - 1).toNat = 2 ^ k - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, h1]; simp; exact Nat.one_le_two_pow), h1]
    rfl
  rw [UInt64.toNat_and, h2, Nat.and_two_pow_sub_one_eq_mod, Nat.toUInt64, UInt64.toNat_ofNat',
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

theorem writeFast_bits (w : Writer) (k v : Nat) (hk : k ≤ 56) :
    (w.writeFast k v hk).bits = w.bits ++ natBits k v := by
  unfold Writer.writeFast
  have hn := w.n_lt
  have hk' : (k.toUInt64).toNat = k := by
    rw [Nat.toUInt64, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  rw [flush_bits]
  simp only [Writer.bits, List.append_assoc]
  congr 1
  have hle : w.n + k ≤ 64 := by omega
  rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, hk', Nat.mod_eq_of_lt (by omega : k < 64), toNat_low v k hk,
    Nat.shiftLeft_eq, natBits_mod _ _ _ hle]
  rw [← natBits_mod (w.n + k) 64 _ hle, Nat.add_mod, Nat.mod_mod,
    ← Nat.add_mod, natBits_mod _ _ _ hle, natBits_mul_add _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos k)),
    natBits_mod _ _ _ (Nat.le_refl _)]

theorem writeBits_bits (w : Writer) (k v : Nat) : (w.writeBits k v).bits = w.bits ++ natBits k v := by
  induction k generalizing v with
  | zero => simp [Writer.writeBits]
  | succ k ih =>
    rw [Writer.writeBits, writeFast_bits, ih, List.append_assoc]
    congr 1
    have e := natBits_add k 1 v
    rw [e, Nat.shiftRight_eq_div_pow]

theorem fwrite_bits (w : Writer) (k v : Nat) : (w.write k v).bits = w.bits ++ natBits k v := by
  unfold Writer.write
  split
  · exact writeFast_bits _ _ _ _
  · exact writeBits_bits _ _ _

theorem fzeros_bits (w : Writer) (k : Nat) : (w.zeros k).bits = w.bits ++ List.replicate k false := by
  induction k using Nat.strongRecOn generalizing w with
  | _ k ih =>
    unfold Writer.zeros
    split
    · simp [fwrite_bits, natBits_zero_eq_replicate]
    · rw [ih _ (by omega), fwrite_bits, natBits_zero_eq_replicate, List.append_assoc, List.replicate_append_replicate]
      congr 2; omega

theorem natBits_one (q : Nat) : natBits (q + 1) 1 = List.replicate q false ++ [true] := by
  rw [natBits_add, show 1 / 2 ^ 1 = 0 by rfl, natBits_zero_eq_replicate]
  rfl

theorem writeRice_bits (k : Nat) (w : Writer) (v : Int) :
    (writeRice k w v).bits = ((((w.zeros (zigzag v >>> k)).write 1 1).write k (zigzag v % 2 ^ k))).bits := by
  unfold writeRice
  simp only [fwrite_bits, fzeros_bits, natBits_mod _ _ _ (Nat.le_refl _), List.append_assoc]
  split
  · rename_i hq
    have hk : k ≤ 55 := by generalize zigzag v >>> k = q at hq; omega
    have hlow := toNat_low (zigzag v) k (by omega)
    have hp : (2 : Nat) ^ k < 2 ^ 63 := Nat.pow_lt_pow_right (by decide) (by omega)
    have h1 : ((1 : UInt64) <<< k.toUInt64).toNat = 2 ^ k := by
      have hk' : (k.toUInt64).toNat = k := by
        rw [Nat.toUInt64, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
      rw [UInt64.toNat_shiftLeft, hk', Nat.mod_eq_of_lt (by omega : k < 64)]
      have hp' : (2 : Nat) ^ k < 2 ^ 64 := Nat.lt_trans hp (by decide)
      simp [Nat.one_shiftLeft, Nat.mod_eq_of_lt hp']
    have hm : (((zigzag v).toUInt64 &&& ((1 : UInt64) <<< k.toUInt64 - 1)) + (1 : UInt64) <<< k.toUInt64).toNat =
        2 ^ k + zigzag v % 2 ^ k := by
      rw [UInt64.toNat_add, hlow, h1, Nat.mod_eq_of_lt (by have := Nat.mod_lt (zigzag v) (Nat.two_pow_pos k); omega)]
      omega
    rw [fwrite_bits, hm]
    have e := natBits_mul_add (zigzag v >>> k + 1) k 1 (zigzag v % 2 ^ k) (Nat.mod_lt _ (Nat.two_pow_pos k))
    rw [Nat.one_mul] at e
    rw [e, natBits_one, natBits_mod _ _ _ (Nat.le_refl _)]
    simp [natBits]
  · simp [fzeros_bits, fwrite_bits]

/-! ## The two writers in step -/

/-- A spec writer and a fast writer holding the same bits. -/
def Same (w : VeriCut.Writer) (fw : Writer) : Prop := w.bits = fw.bits ∧ w.n < 8

theorem same_empty : Same .empty .empty := ⟨rfl, by decide⟩

theorem Same.n {w : VeriCut.Writer} {fw : Writer} (h : Same w fw) : w.n = fw.n := by
  have e := congrArg List.length h.1
  rw [VeriCut.length_bits] at e
  simp only [Writer.bits, List.length_append, length_bitsOf, length_natBits] at e
  have := fw.n_lt; have := h.2; omega

theorem Same.bytes {w : VeriCut.Writer} {fw : Writer} (h : Same w fw) : w.bytes = fw.bytes := by
  have e := h.1
  simp only [VeriCut.Writer.bits, Writer.bits, h.n] at e
  have hl := congrArg List.length e
  simp only [List.length_append, length_bitsOf, length_natBits] at hl
  exact bitsOf_inj (List.append_inj e (by simp only [length_bitsOf]; omega)).1

theorem Same.write {w : VeriCut.Writer} {fw : Writer} (h : Same w fw) (k v : Nat) :
    Same (w.write k v) (fw.write k v) :=
  ⟨by rw [VeriCut.write_bits, fwrite_bits, h.1], VeriCut.write_n_lt _ _ _⟩

theorem zeros_n_lt (w : VeriCut.Writer) (hw : w.n < 8) (k : Nat) : (w.zeros k).n < 8 := by
  induction k using Nat.strongRecOn generalizing w with
  | _ k ih =>
    unfold VeriCut.Writer.zeros
    split
    · exact VeriCut.write_n_lt _ _ _
    · exact ih _ (by omega) _ (VeriCut.write_n_lt _ _ _)

theorem Same.zeros {w : VeriCut.Writer} {fw : Writer} (h : Same w fw) (k : Nat) :
    Same (w.zeros k) (fw.zeros k) :=
  ⟨by rw [VeriCut.zeros_bits, fzeros_bits, h.1], zeros_n_lt _ h.2 _⟩

theorem Same.writeSigned {w : VeriCut.Writer} {fw : Writer} (h : Same w fw) (k : Nat) (v : Int) :
    Same (w.writeSigned k v) (fw.writeSigned k v) := by
  unfold VeriCut.Writer.writeSigned Writer.writeSigned
  rw [pow2_eq]; push_cast; exact h.write _ _

theorem Same.align {w : VeriCut.Writer} {fw : Writer} (h : Same w fw) : Same w.align fw.align := by
  unfold VeriCut.Writer.align Writer.align
  rw [h.n]; exact h.write _ _

theorem Same.foldl {β : Type} {f : VeriCut.Writer → β → VeriCut.Writer} {g : Writer → β → Writer}
    (hfg : ∀ w fw x, Same w fw → Same (f w x) (g fw x)) :
    ∀ (l : List β) {w fw}, Same w fw → Same (l.foldl f w) (l.foldl g fw)
  | [], _, _, h => h
  | x :: l, _, _, h => Same.foldl hfg l (hfg _ _ x h)

theorem Same.foldlA {β : Type} {f : VeriCut.Writer → β → VeriCut.Writer} {g : Writer → β → Writer}
    (hfg : ∀ w fw x, Same w fw → Same (f w x) (g fw x)) (a : Array β) {w fw} (h : Same w fw) :
    Same (a.foldl f w) (a.foldl g fw) := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]; exact Same.foldl hfg _ h

theorem Same.rice {w : VeriCut.Writer} {fw : Writer} (h : Same w fw) (k : Nat) (v : Int) :
    Same (Flac.writeRice k w v) (writeRice k fw v) := by
  refine ⟨?_, ?_⟩
  · rw [writeRice_bits, ← ((h.zeros _).write 1 1).write k _ |>.1]
    simp only [Flac.writeRice, VeriCut.write_bits, natBits_mod _ _ _ (Nat.le_refl _)]
  · exact VeriCut.write_n_lt _ _ _

theorem Same.partition {w : VeriCut.Writer} {fw : Writer} (h : Same w fw) (pb : Nat) (p : Partition) :
    Same (Flac.writePartition pb w p) (writePartition pb fw p) := by
  unfold Flac.writePartition writePartition
  cases p.coding
  · exact Same.foldlA (fun _ _ x h => h.rice _ x) _ (h.write _ _)
  · exact Same.foldlA (fun _ _ x h => h.writeSigned _ x) _ ((h.write _ _).write _ _)

theorem Same.residual {w : VeriCut.Writer} {fw : Writer} (h : Same w fw) (r : Residual) :
    Same (Flac.writeResidual r w) (writeResidual r fw) :=
  Same.foldlA (fun _ _ x h => h.partition _ x) _ ((h.write _ _).write _ _)

theorem Same.samples {w : VeriCut.Writer} {fw : Writer} (h : Same w fw) (bits : Nat) (s : Array Int) :
    Same (Flac.writeSamples bits w s) (writeSamples bits fw s) :=
  Same.foldlA (fun _ _ x h => h.writeSigned _ x) _ h

theorem Same.body {w : VeriCut.Writer} {fw : Writer} (h : Same w fw) (bits : Nat) (b : Body) :
    Same (Flac.writeBody bits w b) (writeBody bits fw b) := by
  cases b with
  | constant v => exact h.writeSigned _ _
  | verbatim s => exact h.samples _ _
  | fixed warmup r => exact (h.samples _ _).residual _
  | lpc p sh c wu r => exact ((((h.samples _ _).write _ _).writeSigned _ _).samples _ _).residual _

theorem Same.subframe {w : VeriCut.Writer} {fw : Writer} (h : Same w fw) (bits : Nat) (sf : Subframe) :
    Same (Flac.writeSubframe bits w sf) (writeSubframe bits fw sf) := by
  unfold Flac.writeSubframe writeSubframe
  have h1 := (h.write 1 0).write 6 sf.body.typeCode
  split
  · exact (h1.write _ _).body _ _
  · exact (((h1.write _ _).zeros _).write _ _).body _ _

theorem Same.header {w : VeriCut.Writer} {fw : Writer} (h : Same w fw) (hd : Header) :
    Same (Flac.writeHeader hd w) (writeHeader hd fw) := by
  unfold Flac.writeHeader writeHeader
  refine (Same.foldl (fun _ _ x h => h.write 8 x) _ ?_).write _ _
  exact ((((((((h.write _ _).write _ _).write _ _).write _ _).write _ _).write _ _).write _ _).write _ _)

theorem crc16_eq (d : ByteArray) : crc16 d = VeriCut.crc16 d := by
  unfold crc16 VeriCut.crc16
  simp only [Nat.shiftLeft_eq]

theorem frame_tail {w : VeriCut.Writer} {fw : Writer} (h : Same w fw) :
    (fw.write 16 (VeriCut.crc16 fw.bytes)).bytes = (w.write 16 (VeriCut.crc16 w.bytes)).bytes := by
  rw [← h.bytes]; exact ((h.write 16 _).bytes).symm

theorem writeFrame_eq (f : Frame) : writeFrame f = Flac.writeFrame f := by
  have h1 := same_empty.header f.header
  unfold writeFrame Flac.writeFrame
  dsimp only
  rw [← h1.bytes, crc16_eq]
  apply frame_tail
  apply Same.align
  refine Same.foldlA ?_ _ (h1.write 8 _)
  intro w fw x h; obtain ⟨sf, c⟩ := x; exact h.subframe _ _

end VeriCut.Flac.Fast
