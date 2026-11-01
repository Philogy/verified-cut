import VeriCut.Proofs.Encode
import VeriCut.Proofs.Fast.Plan

/-! The frames the fast encoder plans are well formed and decode to its input. -/

namespace VeriCut.Flac.Fast

theorem planSubframe_spec' (st : Settings) (ws : List FloatArray) (b n : Nat) (s : Array Int) (hb : 0 < b) (hs : s.size = n)
    (hn : 0 < n) (hr : ∀ v ∈ s, InRange b v) :
    (planSubframe st ws b s).1.samples n = s ∧ (planSubframe st ws b s).1.WF b n := by
  subst hs; exact planSubframe_spec st ws b s hb hn hr

/-- A stereo coding choice that decodes to `L, R`. -/
def StereoOk (bits n : Nat) (L R : Array Int) (t : Channels × (Subframe × Nat) × (Subframe × Nat)) : Prop :=
  (t.1 = .leftSide ∨ t.1 = .rightSide ∨ t.1 = .midSide ∨ t.1 = .independent 2) ∧
  t.2.1.1.WF (bits + if t.1.isSide 0 then 1 else 0) n ∧ t.2.2.1.WF (bits + if t.1.isSide 1 then 1 else 0) n ∧
  t.1.undo #[t.2.1.1.samples n, t.2.2.1.samples n] = #[L, R]

/-- One planned frame: well formed against any matching STREAMINFO, and its samples
are the input's from `offset` on. -/
theorem planFrame_spec (st : Settings) (x : Pcm) (valid : x.Valid) (info : StreamInfo)
    (hrate : info.sampleRate = x.format.sampleRate) (hbits : info.bitsPerSample = x.format.bitsPerSample)
    (hch : info.channels = x.format.channels)
    (number offset n : Nat) (hn : 1 ≤ n ∧ n ≤ 65535) (hoff : offset + n ≤ x.length) (hnum : number < 2 ^ 36) :
    (planFrame st x number offset n).WF info ∧
      (planFrame st x number offset n).samples =
        x.samples.extract (offset * x.format.channels) ((offset + n) * x.format.channels) := by
  have hbps : 0 < x.format.bitsPerSample := by have := valid.bitsPerSample; omega
  have hC := valid.channels
  have blk : ∀ c, c < x.format.channels →
      (planSubframe st (frameWindows st n) x.format.bitsPerSample (channelBlock x offset n c)).1.samples n = channelBlock x offset n c ∧
      (planSubframe st (frameWindows st n) x.format.bitsPerSample (channelBlock x offset n c)).1.WF x.format.bitsPerSample n :=
    fun c hc => planSubframe_spec' st (frameWindows st n) _ n _ hbps (size_channelBlock x offset n c) (by omega)
      (inRange_channelBlock x valid offset n c hoff hc)
  have hhead : ∀ ch : Channels, ch.count = x.format.channels → (∀ k, ch = .independent k → 1 ≤ k ∧ k ≤ 8) →
      Header.WF info ⟨n, x.format.sampleRate, x.format.bitsPerSample, ch, number⟩ :=
    fun ch hcount hind => ⟨hn, hnum, hrate.symm, hbits.symm, by simpa [hch] using hcount, hind⟩
  have hblocks : ∀ c (h : c < ((Array.range x.format.channels).map (channelBlock x offset n)).size),
      ((Array.range x.format.channels).map (channelBlock x offset n))[c] = channelBlock x offset n c := by
    intro c h; simp
  dsimp only [planFrame]
  split
  · rename_i hst
    have h2 : x.format.channels = 2 := by simp at hst; exact hst.2
    have g0 : ((Array.range x.format.channels).map (channelBlock x offset n))[0]! = channelBlock x offset n 0 := by
      rw [getElem!_pos _ _ (by simp; omega)]; simp
    have g1 : ((Array.range x.format.channels).map (channelBlock x offset n))[1]! = channelBlock x offset n 1 := by
      rw [getElem!_pos _ _ (by simp; omega)]; simp
    have p0 : (((Array.range x.format.channels).map (channelBlock x offset n)).map
        (planSubframe st (frameWindows st n) x.format.bitsPerSample))[0]! =
        planSubframe st (frameWindows st n) x.format.bitsPerSample (channelBlock x offset n 0) := by
      rw [getElem!_pos _ _ (by simp; omega)]; simp
    have p1 : (((Array.range x.format.channels).map (channelBlock x offset n)).map
        (planSubframe st (frameWindows st n) x.format.bitsPerSample))[1]! =
        planSubframe st (frameWindows st n) x.format.bitsPerSample (channelBlock x offset n 1) := by
      rw [getElem!_pos _ _ (by simp; omega)]; simp
    rw [g0, g1, p0, p1]
    generalize hL : channelBlock x offset n 0 = L
    generalize hR : channelBlock x offset n 1 = R
    have hLs : L.size = n := hL ▸ size_channelBlock x offset n 0
    have hRs : R.size = n := hR ▸ size_channelBlock x offset n 1
    have rL : ∀ v ∈ L, InRange x.format.bitsPerSample v := hL ▸ inRange_channelBlock x valid offset n 0 hoff (by omega)
    have rR : ∀ v ∈ R, InRange x.format.bitsPerSample v := hR ▸ inRange_channelBlock x valid offset n 1 hoff (by omega)
    obtain ⟨sL, wL⟩ := hL ▸ blk 0 (by omega)
    obtain ⟨sR, wR⟩ := hR ▸ blk 1 (by omega)
    have hside := planSubframe_spec' st (frameWindows st n) (x.format.bitsPerSample + 1) n (Array.zipWith (· - ·) L R) (by omega)
      (by simp [hLs, hRs]) (by omega) (by
        intro v hv
        obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hv
        simp only [Array.getElem_zipWith]
        exact inRange_side _ hbps _ _ (rL _ (Array.getElem_mem _)) (rR _ (Array.getElem_mem _)))
    have hmid := planSubframe_spec' st (frameWindows st n) x.format.bitsPerSample n (Array.zipWith (fun a b => (a + b) / 2) L R) hbps
      (by simp [hLs, hRs]) (by omega) (by
        intro v hv
        obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hv
        simp only [Array.getElem_zipWith]
        exact inRange_mid _ _ _ (rL _ (Array.getElem_mem _)) (rR _ (Array.getElem_mem _)))
    have hsz : L.size = R.size := by omega
    generalize hbest : List.foldl _ _ _ = best
    have hok : StereoOk x.format.bitsPerSample n L R best := by
      rw [← hbest]
      refine foldl_inv (StereoOk x.format.bitsPerSample n L R) _ _ _ ?_ ?_
      · refine ⟨by simp, by simpa [Channels.isSide] using wL, by simpa [Channels.isSide] using wR, ?_⟩
        simp only [Channels.undo, sL, sR]
      · intro b o ho hb
        split
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
          rcases ho with rfl | rfl | rfl
          · refine ⟨by simp, by simpa [Channels.isSide] using wL, by simpa [Channels.isSide] using hside.2, ?_⟩
            simp only [sL, hside.1]; exact undo_leftSide L R hsz
          · refine ⟨by simp, by simpa [Channels.isSide] using hside.2, by simpa [Channels.isSide] using wR, ?_⟩
            simp only [sR, hside.1]; exact undo_rightSide L R hsz
          · refine ⟨by simp, by simpa [Channels.isSide] using hmid.2, by simpa [Channels.isSide] using hside.2, ?_⟩
            simp only [hmid.1, hside.1]; exact undo_midSide L R hsz
        · exact hb
    obtain ⟨hch2, w0, w1, hundo⟩ := hok
    refine ⟨⟨hhead _ ?_ ?_, by simp; rcases hch2 with h | h | h | h <;> simp [h, Channels.count], ?_⟩, ?_⟩
    · rcases hch2 with h | h | h | h <;> simp [h, Channels.count, h2]
    · intro k hk; rcases hch2 with h | h | h | h <;> rw [h] at hk <;> cases hk; omega
    · intro c hc
      simp only [List.size_toArray, List.length_cons, List.length_nil] at hc
      rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
      · simpa [Header.subframeBits] using w0
      · simpa [Header.subframeBits] using w1
    · simp only [Frame.samples, List.map_toArray, List.map_cons, List.map_nil, hundo]
      refine interleave_blocks x valid offset n hoff _ (by simp [h2]) ?_
      intro c hc
      simp only [List.size_toArray, List.length_cons, List.length_nil] at hc
      rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
      · simp [hL]
      · simp [hR]
  · refine ⟨⟨hhead _ (by simp [Channels.count]) (fun k hk => by cases hk; omega), by simp [Channels.count], ?_⟩, ?_⟩
    · intro c hc
      simp only [Array.size_map, Array.size_range] at hc
      simpa [Header.subframeBits, Channels.isSide] using (blk c hc).2
    · simp only [Frame.samples, Channels.undo]
      refine interleave_blocks x valid offset n hoff _ (by simp) ?_
      intro c hc
      simp only [Array.size_map, Array.size_range] at hc
      simpa using (blk c hc).1

end VeriCut.Flac.Fast
