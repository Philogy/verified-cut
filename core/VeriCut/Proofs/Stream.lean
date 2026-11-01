import VeriCut.Proofs.Frame

/-! Round trip of a whole stream: STREAMINFO, then the frames. -/

namespace VeriCut.Flac

open Parser

structure StreamInfo.WF (i : StreamInfo) : Prop where
  blockSizes : i.minBlockSize < 2 ^ 16 ∧ i.maxBlockSize < 2 ^ 16
  frameSizes : i.minFrameSize < 2 ^ 24 ∧ i.maxFrameSize < 2 ^ 24
  sampleRate : i.sampleRate < 2 ^ 20
  channels : 1 ≤ i.channels ∧ i.channels ≤ 8
  bitsPerSample : 1 ≤ i.bitsPerSample ∧ i.bitsPerSample ≤ 32
  totalSamples : i.totalSamples < 2 ^ 36
  md5 : i.md5 < 2 ^ 128

theorem roundTrip_info (i : StreamInfo) (wf : i.WF) : RoundTrip (writeInfo i) infoP i := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, ⟨h6, h7⟩, ⟨h8, h9⟩, h10, h11⟩ := wf
  unfold infoP
  rt RoundTrip.readBits 16 _ h1
  rt RoundTrip.readBits 16 _ h2
  rt RoundTrip.readBits 24 _ h3
  rt RoundTrip.readBits 24 _ h4
  rt RoundTrip.readBits 20 _ h5
  rt RoundTrip.readBits 3 (i.channels - 1) (by omega)
  rt RoundTrip.readBits 5 (i.bitsPerSample - 1) (by omega)
  rt RoundTrip.readBits 36 _ h10
  rt RoundTrip.readBits 128 _ h11
  · refine RoundTrip.pure' ?_
    cases i; simp only [StreamInfo.mk.injEq, true_and, and_true] at *
    omega
  rt_rfl

theorem roundTrip_head (i : StreamInfo) (wf : i.WF) : RoundTrip (writeHead i) streamHeadP (true, i) := by
  unfold streamHeadP
  rt RoundTrip.readBits 32 streamMagic (by decide)
  rt RoundTrip.check _ (by decide)
  rt RoundTrip.readBits 1 1 (by decide)
  rt RoundTrip.readBits 7 0 (by decide)
  rt RoundTrip.readBits 24 34 (by decide)
  rt RoundTrip.check _ (by decide)
  rt roundTrip_info i wf
  · exact RoundTrip.pure' rfl
  rt_rfl

theorem bitsOf_foldl_append (l : List ByteArray) (b : ByteArray) :
    bitsOf (l.foldl (· ++ ·) b) = bitsOf b ++ l.flatMap bitsOf := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih => simp [ih]

theorem write_bytes_pos (w : Writer) (k v : Nat) (hk : 8 ≤ k) : 0 < (w.write k v).bytes.size := by
  have := length_bits (w.write k v)
  have := write_n_lt w k v
  rw [length_write] at *
  omega

theorem writeFrame_size_pos (f : Frame) : 0 < (writeFrame f).size :=
  write_bytes_pos _ _ _ (by decide)

theorem length_le_bits (l : List Frame) : 8 * l.length ≤ (l.flatMap (bitsOf ∘ writeFrame)).length := by
  induction l with
  | nil => simp
  | cons f l ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append, Function.comp, length_bitsOf]
    have := writeFrame_size_pos f; omega

theorem framesP_ok (info : StreamInfo) (fs : List Frame) (wf : ∀ f ∈ fs, f.WF info) (d : ByteArray)
    (acc : Array Frame) (fuel pos : Nat) (hfuel : fs.length ≤ fuel) (hpos : pos % 8 = 0)
    (h : (bitsOf d).drop pos = fs.flatMap (bitsOf ∘ writeFrame)) :
    ∃ p, framesP info fuel acc d pos = .ok (acc ++ fs.toArray, p) := by
  induction fs generalizing acc fuel pos with
  | nil =>
    cases fuel with
    | zero => exact ⟨_, by simp [framesP]; rfl⟩
    | succ fuel =>
      have hend : 8 * d.size ≤ pos := by
        have := congrArg List.length h; simp at this; omega
      refine ⟨pos, ?_⟩
      unfold framesP
      rw [bind_ok (show atEnd d pos = .ok (true, pos) by simp [atEnd, hend])]
      simp; rfl
  | cons f fs ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ fuel =>
      have hsize := writeFrame_size_pos f
      simp only [List.flatMap_cons, Function.comp] at h
      have hnot : ¬ 8 * d.size ≤ pos := by
        have := congrArg List.length h; simp at this; omega
      have hf := frameP_writeFrame info f (wf f (by simp)) d pos _ hpos h
      obtain ⟨p, hp⟩ := ih (fun g hg => wf g (by simp [hg])) (acc.push f) fuel (pos + 8 * (writeFrame f).size)
        (by simp at hfuel; omega) (by omega)
        (by rw [← List.drop_drop, h, List.drop_left' (by simp)])
      refine ⟨p, ?_⟩
      unfold framesP
      rw [bind_ok (show atEnd d pos = .ok (false, pos) by simp [atEnd, hnot])]
      simp only [Bool.false_eq_true, if_false]
      rw [bind_ok hf, hp]
      simp

/-- Parsing a written stream gives back its STREAMINFO and frames. -/
theorem streamP_writeStream (info : StreamInfo) (frames : Array Frame) (hinfo : info.WF)
    (wf : ∀ f ∈ frames, f.WF info) :
    ∃ p, streamP (writeStream info (frames.map writeFrame)) 0 = .ok (⟨info, frames⟩, p) := by
  obtain ⟨dh, eh⟩ := RoundTrip.canonical (roundTrip_head info hinfo)
  let d := writeStream info (frames.map writeFrame)
  let hb := (writeHead info .empty).bytes
  have halign : (writeHead info .empty).bits = bitsOf hb := by
    refine bits_aligned _ (write_n_lt _ _ _) ?_
    simp only [writeHead, writeInfo, length_write]
    simp [Writer.bits, Writer.empty]
  have hd : bitsOf d = bitsOf hb ++ frames.toList.flatMap (bitsOf ∘ writeFrame) := by
    simp only [d, writeStream, ← Array.foldl_toList, bitsOf_foldl_append, Array.toList_map, List.flatMap_map]
    rfl
  have hhead : streamHeadP d 0 = .ok ((true, info), hb.size * 8) := by
    have := dh d 0 (frames.toList.flatMap (bitsOf ∘ writeFrame)) (by rw [hd, halign]; simp)
    rw [this, halign]; simp [Nat.mul_comm]
  have hframes := framesP_ok info frames.toList (fun f hf => wf f (by simpa using hf)) d #[] d.size (hb.size * 8)
    (by
      have := congrArg List.length hd
      have := length_le_bits frames.toList
      simp only [length_bitsOf, List.length_append] at *
      omega)
    (by omega) (by rw [hd, Nat.mul_comm, ← length_bitsOf, List.drop_left' rfl])
  obtain ⟨p, hp⟩ := hframes
  refine ⟨p, ?_⟩
  unfold streamP
  rw [bind_ok hhead, bind_ok (show data d (hb.size * 8) = .ok (d, hb.size * 8) from rfl)]
  simp only
  rw [bind_ok (show skipMetadata d.size true d (hb.size * 8) = .ok ((), hb.size * 8) by
      cases d.size <;> rfl), bind_ok hp]
  simp; rfl

end VeriCut.Flac
