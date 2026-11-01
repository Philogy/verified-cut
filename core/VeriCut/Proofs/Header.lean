import VeriCut.Proofs.Codes

/-! Round trip of a frame header. -/

namespace VeriCut.Flac

open Parser

/-- A header the parser accepts against `info`. -/
structure Header.WF (info : StreamInfo) (h : Header) : Prop where
  blockSize : 1 ≤ h.blockSize ∧ h.blockSize ≤ 65535
  number : h.number < 2 ^ 36
  sampleRate : h.sampleRate = info.sampleRate
  bitsPerSample : h.bitsPerSample = info.bitsPerSample
  channels : h.channels.count = info.channels
  independent : ∀ n, h.channels = .independent n → 1 ≤ n ∧ n ≤ 8

theorem codeOf_blockSize {v c : Nat} (h : codeOf blockSizeCodes v = some c) :
    blockSizeCodes.lookup c = some v ∧ c < 16 ∧ c ≠ 6 ∧ c ≠ 7 := by
  simp only [codeOf, blockSizeCodes, List.find?] at h
  repeat' split at h
  all_goals simp_all
  all_goals (subst_vars; decide)

theorem codeOf_sampleRate {v c : Nat} (h : codeOf sampleRateCodes v = some c) :
    sampleRateCodes.lookup c = some v ∧ c < 16 ∧ c ≠ 0 ∧ c ≠ 12 ∧ c ≠ 13 ∧ c ≠ 14 := by
  simp only [codeOf, sampleRateCodes, List.find?] at h
  repeat' split at h
  all_goals simp_all
  all_goals (subst_vars; decide)

theorem codeOf_bitsPerSample {v c : Nat} (h : codeOf bitsPerSampleCodes v = some c) :
    bitsPerSampleCodes.lookup c = some v ∧ c < 8 ∧ c ≠ 0 := by
  simp only [codeOf, bitsPerSampleCodes, List.find?] at h
  repeat' split at h
  all_goals simp_all
  all_goals (subst_vars; decide)

theorem lookupCode_eq {table : List (Nat × Nat)} {c v : Nat} (h : table.lookup c = some v) (what : String) :
    lookupCode table c what = pure v := by
  simp [lookupCode, h]

theorem blockSizeCode_lt (n : Nat) : (blockSizeCode n).1 < 16 := by
  unfold blockSizeCode; split
  · exact (codeOf_blockSize ‹_›).2.1
  · split <;> decide

theorem roundTrip_blockSize (n : Nat) (h : 1 ≤ n ∧ n ≤ 65535) :
    RoundTrip (·.write (blockSizeCode n).2 (n - 1)) (blockSizeP (blockSizeCode n).1) n := by
  unfold blockSizeCode
  split
  · rename_i c hc
    obtain ⟨hl, -, h6, h7⟩ := codeOf_blockSize hc
    simp only [blockSizeP, h6, h7, if_false, lookupCode_eq hl]
    exact RoundTrip.write_zero _
  · split
    · simp only [blockSizeP, if_true]
      rt RoundTrip.readBits 8 (n - 1) (by omega)
      · exact RoundTrip.pure' (by omega)
      rt_rfl
    · simp only [blockSizeP, if_neg (by decide : (7 : Nat) ≠ 6), if_true]
      rt RoundTrip.readBits 16 (n - 1) (by omega)
      · exact RoundTrip.pure' (by omega)
      rt_rfl

theorem roundTrip_sampleRate (info : StreamInfo) :
    RoundTrip id (sampleRateP info ((codeOf sampleRateCodes info.sampleRate).getD 0)) info.sampleRate := by
  cases hc : codeOf sampleRateCodes info.sampleRate with
  | none => exact RoundTrip.pure' rfl
  | some c =>
    obtain ⟨hl, -, h0, h12, h13, h14⟩ := codeOf_sampleRate hc
    simp only [Option.getD, sampleRateP, h0, h12, h13, h14, if_false, lookupCode_eq hl]
    exact RoundTrip.pure' rfl

theorem sampleRateCode_lt (r : Nat) : (codeOf sampleRateCodes r).getD 0 < 2 ^ 4 := by
  cases hc : codeOf sampleRateCodes r with
  | none => decide
  | some c => exact (codeOf_sampleRate hc).2.1

theorem roundTrip_bitsPerSample (info : StreamInfo) :
    RoundTrip id (bitsPerSampleP info ((codeOf bitsPerSampleCodes info.bitsPerSample).getD 0))
      info.bitsPerSample := by
  cases hc : codeOf bitsPerSampleCodes info.bitsPerSample with
  | none => exact RoundTrip.pure' rfl
  | some c =>
    obtain ⟨hl, -, h0⟩ := codeOf_bitsPerSample hc
    simp only [Option.getD, bitsPerSampleP, h0, if_false, lookupCode_eq hl]
    exact RoundTrip.pure' rfl

theorem bitsPerSampleCode_lt (b : Nat) : (codeOf bitsPerSampleCodes b).getD 0 < 2 ^ 3 := by
  cases hc : codeOf bitsPerSampleCodes b with
  | none => decide
  | some c => exact (codeOf_bitsPerSample hc).2.1

theorem roundTrip_channels (ch : Channels) (h : ∀ n, ch = .independent n → 1 ≤ n ∧ n ≤ 8) :
    ch.code < 2 ^ 4 ∧ RoundTrip id (channelsP ch.code) ch := by
  cases ch with
  | independent n =>
    have := h n rfl
    refine ⟨by simp [Channels.code]; omega, ?_⟩
    simp only [Channels.code]
    unfold channelsP
    rw [if_pos (by omega)]
    exact RoundTrip.pure' (by congr 1; omega)
  | leftSide => exact ⟨by decide, RoundTrip.pure' rfl⟩
  | rightSide => exact ⟨by decide, RoundTrip.pure' rfl⟩
  | midSide => exact ⟨by decide, RoundTrip.pure' rfl⟩

theorem roundTrip_header (info : StreamInfo) (h : Header) (wf : h.WF info) :
    RoundTrip (writeHeader h) (headerP info) h := by
  obtain ⟨hbs, hnum, hrate, hbits, hch, hind⟩ := wf
  obtain ⟨hcode, hchan⟩ := roundTrip_channels h.channels hind
  unfold headerP
  rt RoundTrip.readBits 14 0x3FFE (by decide)
  rt RoundTrip.check _ (by decide)
  rt RoundTrip.readBits 1 0 (by decide)
  rt RoundTrip.check _ (by decide)
  rt RoundTrip.readBits 1 0 (by decide)
  rt RoundTrip.readBits 4 _ (blockSizeCode_lt h.blockSize)
  rt RoundTrip.readBits 4 _ (sampleRateCode_lt info.sampleRate)
  rt RoundTrip.readBits 4 _ hcode
  rt hchan
  rt RoundTrip.readBits 3 _ (bitsPerSampleCode_lt info.bitsPerSample)
  rt RoundTrip.readBits 1 0 (by decide)
  rt RoundTrip.check _ (by decide)
  rt roundTrip_codedNumber h.number hnum
  rt roundTrip_blockSize h.blockSize hbs
  rt roundTrip_sampleRate info
  rt roundTrip_bitsPerSample info
  rt RoundTrip.check _ (by simp)
  rt RoundTrip.check _ (by simp)
  rt RoundTrip.check _ (by simpa using hch)
  · exact RoundTrip.pure' (by cases h; simp_all)
  rt_rfl
  intro w
  simp only [writeHeader, hrate, hbits, id]

end VeriCut.Flac
