import VeriCut.Proofs.Plan
import VeriCut.Proofs.Frame

/-! The frames the encoder plans are well formed and decode to its input. -/

namespace VeriCut.Flac

section Frame

variable (x : Pcm) (valid : x.Valid)
include valid

theorem size_eq_length_mul : x.samples.size = x.length * x.format.channels := by
  have := valid.whole
  unfold Pcm.length
  exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero this)).symm

theorem index_lt (offset n i c : Nat) (hoff : offset + n ≤ x.length) (hi : i < n) (hc : c < x.format.channels) :
    (offset + i) * x.format.channels + c < x.samples.size := by
  rw [size_eq_length_mul x valid]
  have : (offset + i + 1) * x.format.channels ≤ x.length * x.format.channels :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at this
  omega

omit valid in
theorem size_channelBlock (offset n c : Nat) : (channelBlock x offset n c).size = n := by
  simp [channelBlock]

omit valid in
theorem getElem_channelBlock (offset n c i : Nat) (h : i < (channelBlock x offset n c).size) :
    (channelBlock x offset n c)[i] = x.samples[(offset + i) * x.format.channels + c]! := by
  simp [channelBlock]

theorem inRange_channelBlock (offset n c : Nat) (hoff : offset + n ≤ x.length) (hc : c < x.format.channels) :
    ∀ v ∈ channelBlock x offset n c, InRange x.format.bitsPerSample v := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hv
  rw [getElem_channelBlock, getElem!_pos x.samples ((offset + i) * x.format.channels + c)
    (index_lt x valid offset n i c hoff (by simpa [size_channelBlock] using hi) hc)]
  exact valid.range _ (Array.getElem_mem _)

/-- Interleaving the channel blocks gives back the samples they came from. -/
theorem interleave_blocks (offset n : Nat) (hoff : offset + n ≤ x.length) (cs : Array (Array Int))
    (hcs : cs.size = x.format.channels) (hc : ∀ c (h : c < cs.size), cs[c] = channelBlock x offset n c) :
    interleave n cs = x.samples.extract (offset * x.format.channels) ((offset + n) * x.format.channels) := by
  have hC := valid.channels.1
  have hsz := size_eq_length_mul x valid
  have hle : offset * x.format.channels + n * x.format.channels ≤ x.samples.size := by
    rw [hsz, ← Nat.add_mul]; exact Nat.mul_le_mul_right _ hoff
  apply Array.ext
  · simp only [interleave, Array.size_ofFn, Array.size_extract, hcs, Nat.add_mul]; omega
  · intro k h1 h2
    simp only [interleave, Array.size_ofFn] at h1
    rw [hcs] at h1
    have hkC : k % cs.size < cs.size := Nat.mod_lt _ (by omega)
    have hq : k / x.format.channels < n := (Nat.div_lt_iff_lt_mul (by omega)).2 h1
    have hidx : (offset + k / x.format.channels) * x.format.channels + k % x.format.channels =
        offset * x.format.channels + k := by
      have := Nat.div_add_mod k x.format.channels
      rw [Nat.add_mul, Nat.mul_comm (k / _)]
      omega
    simp only [interleave, Array.getElem_ofFn, Array.getElem_extract]
    rw [getElem!_pos cs _ hkC, hc _ hkC, getElem!_pos _ _ (by rw [size_channelBlock]; rwa [hcs]),
      getElem_channelBlock, hcs, hidx, getElem!_pos _ _ (by omega)]

end Frame

/-! ## Stereo decorrelation -/

section Stereo

variable (L R : Array Int) (h : L.size = R.size)
include h

theorem undo_leftSide : Channels.undo .leftSide #[L, Array.zipWith (· - ·) L R] = #[L, R] := by
  have e : Array.zipWith (· - ·) L (Array.zipWith (· - ·) L R) = R :=
    Array.ext (by simp [h]) (fun i _ _ => by simp; omega)
  simp [Channels.undo, e]

theorem undo_rightSide : Channels.undo .rightSide #[Array.zipWith (· - ·) L R, R] = #[L, R] := by
  have e : Array.zipWith (· + ·) (Array.zipWith (· - ·) L R) R = L :=
    Array.ext (by simp [h]) (fun i _ _ => by simp)
  simp [Channels.undo, e]

theorem undo_midSide :
    Channels.undo .midSide #[Array.zipWith (fun a b => (a + b) / 2) L R, Array.zipWith (· - ·) L R] = #[L, R] := by
  have mid : Array.zipWith (fun (m s : Int) => 2 * m + s % 2) (Array.zipWith (fun a b => (a + b) / 2) L R)
      (Array.zipWith (· - ·) L R) = Array.zipWith (· + ·) L R :=
    Array.ext (by simp [h]) (fun i _ _ => by simp; omega)
  have e1 : Array.zipWith (fun m s => (m + s) / 2) (Array.zipWith (· + ·) L R) (Array.zipWith (· - ·) L R) = L :=
    Array.ext (by simp [h]) (fun i _ _ => by simp; omega)
  have e2 : Array.zipWith (fun m s => (m - s) / 2) (Array.zipWith (· + ·) L R) (Array.zipWith (· - ·) L R) = R :=
    Array.ext (by simp [h]) (fun i _ _ => by simp; omega)
  simp only [Channels.undo, List.getElem!_toArray, List.getElem!_cons_zero, List.getElem!_cons_succ, mid, e1, e2]

end Stereo

theorem inRange_side (b : Nat) (hb : 0 < b) (l r : Int) (hl : InRange b l) (hr : InRange b r) :
    InRange (b + 1) (l - r) := by
  unfold InRange at *
  have : (2 : Int) ^ (b + 1 - 1) = 2 * 2 ^ (b - 1) := by
    rw [Nat.add_sub_cancel, ← Int.pow_succ', Nat.sub_add_cancel hb]
  rw [this]; omega

theorem inRange_mid (b : Nat) (l r : Int) (hl : InRange b l) (hr : InRange b r) :
    InRange b ((l + r) / 2) := by
  unfold InRange at *; omega


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

end VeriCut.Flac
