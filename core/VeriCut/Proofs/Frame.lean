import VeriCut.Proofs.Subframe
import VeriCut.Proofs.Header

/-! Round trip of a whole frame, CRCs included. -/

namespace VeriCut.Flac

open Parser

structure Frame.WF (info : StreamInfo) (f : Frame) : Prop where
  header : f.header.WF info
  count : f.subframes.size = f.header.channels.count
  subframes : ∀ c (hc : c < f.subframes.size), f.subframes[c].WF (f.header.subframeBits c) f.header.blockSize

def writeSubframes (h : Header) (sfs : List Subframe) (start : Nat) (w : Writer) : Writer :=
  (sfs.zipIdx start).foldl (fun w (sf, c) => writeSubframe (h.subframeBits c) w sf) w

theorem roundTrip_subframes (h : Header) (sfs : List Subframe) (acc : Array Subframe)
    (wf : ∀ i (hi : i < sfs.length), sfs[i].WF (h.subframeBits (acc.size + i)) h.blockSize) :
    RoundTrip (writeSubframes h sfs acc.size) (subframesP h sfs.length acc) (acc ++ sfs.toArray) := by
  induction sfs generalizing acc with
  | nil => exact RoundTrip.val (RoundTrip.pure' rfl) (by simp)
  | cons sf sfs ih =>
    have h0 := roundTrip_subframe _ _ sf (by exact wf 0 (by simp))
    have hrest := ih (acc.push sf) (fun i hi => by
      have := wf (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    unfold subframesP
    rt h0
    · exact RoundTrip.val hrest (by simp)
    rt_rfl
    intro w; simp [writeSubframes, List.zipIdx_cons]

theorem RoundTrip.canonical {α : Type} {f : Writer → Writer} {p : Parser α} {a : α} (h : RoundTrip f p a) :
    Decodes p (f .empty).bits a ∧ ∀ w, (f w).bits = w.bits ++ (f .empty).bits := by
  obtain ⟨l, e, d⟩ := h
  have : (f .empty).bits = l := by rw [e]; rfl
  rw [this]; exact ⟨d, e⟩

theorem bind_ok {α β : Type} {p : Parser α} {q : α → Parser β} {d : ByteArray} {pos p1 : Nat} {a : α}
    (h : p d pos = .ok (a, p1)) : (p >>= q) d pos = q a d p1 := by
  show Parser.bind p q d pos = _
  simp [Parser.bind, h]

theorem length_write (w : Writer) (k v : Nat) : (w.write k v).bits.length = w.bits.length + k := by
  simp [write_bits]

theorem blockSizeCode_bits (n : Nat) : (blockSizeCode n).2 = 0 ∨ (blockSizeCode n).2 = 8 ∨ (blockSizeCode n).2 = 16 := by
  unfold blockSizeCode; split
  · left; rfl
  · split <;> simp

theorem length_foldl_write8 (l : List Nat) (w : Writer) :
    (l.foldl (·.write 8 ·) w).bits.length = w.bits.length + 8 * l.length := by
  induction l generalizing w with
  | nil => simp
  | cons b l ih => simp [ih, length_write]; omega

theorem writeHeader_length (h : Header) (w : Writer) : (writeHeader h w).bits.length % 8 = w.bits.length % 8 := by
  simp only [writeHeader, length_write, length_foldl_write8]
  rcases blockSizeCode_bits h.blockSize with e | e | e <;> rw [e] <;> omega

theorem skip_ok {d : ByteArray} {p m : Nat} {b : Bool} {t : List Bool} (h : (bitsOf d).drop p = natBits m 0 ++ b :: t) :
    skip m d p = .ok ((), p + m) := by
  have := congrArg List.length h
  simp at this
  simp [skip]; omega

theorem frameP_writeFrame (info : StreamInfo) (f : Frame) (wf : f.WF info) (d : ByteArray) (pos : Nat)
    (t : List Bool) (hpos : pos % 8 = 0) (h : (bitsOf d).drop pos = bitsOf (writeFrame f) ++ t) :
    frameP info d pos = .ok (f, pos + 8 * (writeFrame f).size) := by
  obtain ⟨dh, eh⟩ := RoundTrip.canonical (roundTrip_header info f.header wf.header)
  have hsf : RoundTrip (writeSubframes f.header f.subframes.toList 0)
      (subframesP f.header f.subframes.toList.length #[]) f.subframes := by
    refine RoundTrip.val (roundTrip_subframes f.header f.subframes.toList #[] (fun i hi => ?_)) (by simp)
    simpa using wf.subframes i (by simpa using hi)
  obtain ⟨ds, es⟩ := RoundTrip.canonical hsf
  -- the writer states of `writeFrame`
  let w1 := writeHeader f.header .empty
  let w2 := w1.write 8 (crc8 w1.bytes)
  let w3 := writeSubframes f.header f.subframes.toList 0 w2
  let w4 := w3.align
  let w5 := w4.write 16 (crc16 w4.bytes)
  have hw5 : writeFrame f = w5.bytes := by
    simp only [writeFrame, w5, w4, w3, w2, w1, writeSubframes, ← Array.toList_zipIdx, Array.foldl_toList]
  let lh := w1.bits
  let ls := (writeSubframes f.header f.subframes.toList 0 .empty).bits
  have h1 : w1.bits = bitsOf w1.bytes :=
    bits_aligned _ (by simp only [w1, writeHeader]; exact write_n_lt _ _ _)
      (by have := writeHeader_length f.header .empty; simp [Writer.bits, Writer.empty] at this ⊢; exact this)
  have hlh : lh.length % 8 = 0 := by rw [show lh = w1.bits from rfl, h1]; simp
  let m := (8 - w3.n % 8) % 8
  have h4 : w4.bits = lh ++ natBits 8 (crc8 w1.bytes) ++ ls ++ natBits m 0 := by
    simp only [w4, Writer.align, write_bits, w3]
    rw [es w2]; simp [w2, write_bits, lh, ls, m, w3]
  have hm : (lh.length + 8 + ls.length) % 8 = w3.n % 8 := by
    have := length_bits w3
    have e : w3.bits = lh ++ natBits 8 (crc8 w1.bytes) ++ ls := by rw [es w2]; simp [w2, write_bits, lh, ls]
    rw [e] at this; simp at this; omega
  have h4a : w4.bits = bitsOf w4.bytes := bits_aligned _ (write_n_lt _ _ _) (by
    rw [h4]; simp <;> omega)
  have h5 : bitsOf (writeFrame f) = bitsOf w4.bytes ++ natBits 16 (crc16 w4.bytes) := by
    rw [hw5, ← h4a, ← bits_aligned w5 (write_n_lt _ _ _) (by rw [length_write, h4a]; simp <;> omega)]
    simp [w5, write_bits]
  -- now run the parser
  rw [h5, ← h4a, h4] at h
  have crc8_lt : crc8 w1.bytes < 2 ^ 8 := Nat.mod_lt _ (by decide)
  have crc16_lt : crc16 w4.bytes < 2 ^ 16 := Nat.mod_lt _ (by decide)
  have hhead : headerP info d pos = .ok (f.header, pos + lh.length) :=
    dh d pos (natBits 8 (crc8 w1.bytes) ++ ls ++ natBits m 0 ++ natBits 16 (crc16 w4.bytes) ++ t)
      (by rw [h]; simp only [List.append_assoc]; rfl)
  have hcrc8 : readBits 8 d (pos + lh.length) = .ok (crc8 w1.bytes, pos + lh.length + 8) := by
    have := Decodes.readBits 8 _ crc8_lt d (pos + lh.length) (ls ++ natBits m 0 ++ natBits 16 (crc16 w4.bytes) ++ t)
      (by rw [← List.drop_drop, h]; simp [List.drop_left'])
    simpa using this
  have hx8 : d.extract (pos / 8) ((pos + lh.length) / 8) = w1.bytes := by
    have := extract_of_drop (b := w1.bytes)
      (t := natBits 8 (crc8 w1.bytes) ++ (ls ++ (natBits m 0 ++ (natBits 16 (crc16 w4.bytes) ++ t)))) hpos
      (by rw [h, show lh = w1.bits from rfl, h1]; simp only [List.append_assoc])
    rwa [show (pos + lh.length) / 8 = pos / 8 + w1.bytes.size by
      rw [show lh = w1.bits from rfl, h1]; simp; omega]
  have hsub : subframesP f.header f.header.channels.count #[] d (pos + lh.length + 8) =
      .ok (f.subframes, pos + lh.length + 8 + ls.length) := by
    have := ds d (pos + lh.length + 8) (natBits m 0 ++ natBits 16 (crc16 w4.bytes) ++ t)
      (by rw [← List.drop_drop, ← List.drop_drop, h]; simp [List.drop_left'] <;> rfl)
    simpa [wf.count] using this
  have hpad : (8 - (pos + lh.length + 8 + ls.length) % 8) % 8 = m := by
    simp only [m]; omega
  have hskip : align d (pos + lh.length + 8 + ls.length) = .ok ((), pos + lh.length + 8 + ls.length + m) := by
    unfold align; rw [hpad]
    have e : natBits 16 (crc16 w4.bytes) ++ t = (crc16 w4.bytes).testBit 15 :: (natBits 15 (crc16 w4.bytes) ++ t) := rfl
    exact skip_ok (t := natBits 15 (crc16 w4.bytes) ++ t)
      (by rw [← e, ← List.drop_drop, ← List.drop_drop, ← List.drop_drop, h]; simp [List.drop_left'])
  have hend : pos + lh.length + 8 + ls.length + m = pos + 8 * w4.bytes.size := by
    have := congrArg List.length h4a; rw [h4] at this; simp at this; omega
  have hcrc16 : readBits 16 d (pos + 8 * w4.bytes.size) = .ok (crc16 w4.bytes, pos + 8 * w4.bytes.size + 16) := by
    have := Decodes.readBits 16 _ crc16_lt d (pos + 8 * w4.bytes.size) t
      (by rw [← hend, ← List.drop_drop, ← List.drop_drop, ← List.drop_drop, ← List.drop_drop, h]; simp [List.drop_left'])
    simpa using this
  have hx16 : d.extract (pos / 8) ((pos + 8 * w4.bytes.size) / 8) = w4.bytes := by
    have := extract_of_drop (b := w4.bytes) (t := natBits 16 (crc16 w4.bytes) ++ t) hpos
      (by rw [h, ← h4, h4a, List.append_assoc])
    rwa [show (pos + 8 * w4.bytes.size) / 8 = pos / 8 + w4.bytes.size by omega]
  unfold frameP
  rw [bind_ok (show Parser.pos d pos = .ok (pos, pos) from rfl), bind_ok hhead,
    bind_ok (show Parser.pos d (pos + lh.length) = .ok (pos + lh.length, pos + lh.length) from rfl),
    bind_ok hcrc8, bind_ok (show Parser.data d (pos + lh.length + 8) = .ok (d, pos + lh.length + 8) from rfl),
    bind_ok (show check _ _ d (pos + lh.length + 8) = .ok ((), pos + lh.length + 8) by simp [check, hx8]; rfl),
    bind_ok hsub, bind_ok hskip, hend,
    bind_ok (show Parser.pos d (pos + 8 * w4.bytes.size) = .ok _ from rfl), bind_ok hcrc16,
    bind_ok (show check _ _ d (pos + 8 * w4.bytes.size + 16) = .ok ((), pos + 8 * w4.bytes.size + 16) by
      simp [check, hx16]; rfl)]
  have : (writeFrame f).size = w4.bytes.size + 2 := by
    have := congrArg List.length h5; simp at this; omega
  simp only [this]
  show Except.ok _ = _
  congr 2

end VeriCut.Flac
