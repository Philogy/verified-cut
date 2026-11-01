import VeriCut.Proofs.Encode
import VeriCut.Proofs.Stream
import VeriCut.Flac.Decode

/-! `decode (encode st x) = x`. -/

namespace VeriCut.Flac

theorem frame_lt_len (b len m : Nat) (hb : 0 < b) (hm : m < (len + b - 1) / b) : m * b < len := by
  have := (Nat.le_div_iff_mul_le hb).1 (show m + 1 ≤ (len + b - 1) / b by omega)
  rw [Nat.succ_mul] at this; omega

theorem len_le_frames (b len : Nat) (hb : 0 < b) : len ≤ (len + b - 1) / b * b := by
  have h1 := Nat.div_add_mod (len + b - 1) b
  have h2 := Nat.mod_lt (len + b - 1) hb
  rw [Nat.mul_comm] at h1; omega

theorem frames_le_len (b len : Nat) (hb : 0 < b) : (len + b - 1) / b ≤ len := by
  rcases Nat.eq_zero_or_pos len with h | h
  · subst h; simp; omega
  · apply Nat.div_le_of_le_mul
    have h1 : b - 1 ≤ (b - 1) * len := Nat.le_mul_of_pos_right _ h
    have h2 : b * len = (b - 1) * len + len := by
      conv => lhs; rw [show b = (b - 1) + 1 by omega]
      rw [Nat.succ_mul]
    omega

/-! ## Decoding a frame at a time is decoding the stream -/

section
open Parser

theorem bind_ok' {α β : Type} {p : Parser α} {q : α → Parser β} {d : ByteArray} {pos p1 : Nat} {a : α}
    (h : p d pos = .ok (a, p1)) : Parser.bind p q d pos = q a d p1 := by
  simp [Parser.bind, h]

theorem bind_error' {α β : Type} {p : Parser α} {q : α → Parser β} {d : ByteArray} {pos : Nat} {e : String}
    (h : p d pos = .error e) : Parser.bind p q d pos = .error e := by
  simp [Parser.bind, h]

theorem framesSamplesP_eq (info : StreamInfo) : ∀ (fuel : Nat) (fs : Array Frame) (acc : Array Int) (d : ByteArray) (p : Nat),
    framesSamplesP info fuel (fs.foldl (· ++ ·.samples) acc) d p =
      match framesP info fuel fs d p with
      | .ok (fs', p') => .ok (fs'.foldl (· ++ ·.samples) acc, p')
      | .error e => .error e := by
  intro fuel
  induction fuel with
  | zero => intro fs acc d p; rfl
  | succ fuel ih =>
    intro fs acc d p
    simp only [framesSamplesP, framesP, bind, Parser.bind, atEnd]
    split
    · rfl
    · cases h : frameP info d p with
      | error e => rw [bind_error' h, bind_error' h]
      | ok r =>
        obtain ⟨f, p'⟩ := r
        rw [bind_ok' h, bind_ok' h, ← ih (fs.push f) acc d p', Array.foldl_push]

theorem streamSamplesP_eq (d : ByteArray) (pos : Nat) :
    streamSamplesP d pos = match streamP d pos with
      | .ok (s, p) => .ok ((s.info, s.samples), p)
      | .error e => .error e := by
  unfold streamSamplesP streamP
  simp only [bind]
  cases h1 : streamHeadP d pos with
  | error e => rw [bind_error' h1, bind_error' h1]
  | ok r =>
    obtain ⟨head, p1⟩ := r
    rw [bind_ok' h1, bind_ok' h1, bind_ok' (show data d p1 = .ok (d, p1) from rfl),
      bind_ok' (show data d p1 = .ok (d, p1) from rfl)]
    cases h2 : skipMetadata d.size head.1 d p1 with
    | error e => rw [bind_error' h2, bind_error' h2]
    | ok r =>
      obtain ⟨_, p2⟩ := r
      rw [bind_ok' h2, bind_ok' h2, Array.emptyWithCapacity_eq]
      have := framesSamplesP_eq head.2 d.size #[] #[] d p2
      simp only [Array.foldl_empty] at this
      cases h3 : framesP head.2 d.size #[] d p2 with
      | error e => rw [h3] at this; rw [bind_error' this, bind_error' h3]
      | ok r =>
        obtain ⟨fs, p3⟩ := r
        rw [h3] at this
        rw [bind_ok' this, bind_ok' h3]
        rfl

end

section
variable (st : Settings) (x : Pcm) (valid : x.Valid)
include valid

theorem planFrames_spec (info : StreamInfo)
    (hrate : info.sampleRate = x.format.sampleRate) (hbits : info.bitsPerSample = x.format.bitsPerSample)
    (hch : info.channels = x.format.channels) :
    (∀ f ∈ planFrames st x, f.WF info) ∧ (planFrames st x).foldl (· ++ ·.samples) #[] = x.samples := by
  have hb : 0 < st.clampedBlockSize := by unfold Settings.clampedBlockSize; omega
  have hb' : st.clampedBlockSize ≤ 65535 := by unfold Settings.clampedBlockSize; omega
  have hlen := valid.length
  have spec := fun k (hk : k < (x.length + st.clampedBlockSize - 1) / st.clampedBlockSize) =>
    have := frame_lt_len _ _ _ hb hk
    have := frames_le_len st.clampedBlockSize x.length hb
    planFrame_spec st x valid info hrate hbits hch k (k * st.clampedBlockSize)
      (min st.clampedBlockSize (x.length - k * st.clampedBlockSize)) ⟨by omega, by omega⟩ (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · intro f hf
    simp only [planFrames, Array.mem_map, Array.mem_range] at hf
    obtain ⟨k, hk, rfl⟩ := hf
    exact (spec k hk).1
  · generalize hK : (x.length + st.clampedBlockSize - 1) / st.clampedBlockSize = K at spec
    have step : ∀ m, m ≤ K → ((List.range m).map fun k => planFrame st x k (k * st.clampedBlockSize)
        (min st.clampedBlockSize (x.length - k * st.clampedBlockSize))).foldl (· ++ ·.samples) #[] =
        x.samples.extract 0 (min (m * st.clampedBlockSize) x.length * x.format.channels) := by
      intro m hm
      induction m with
      | zero => simp
      | succ m ih =>
        rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
        simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, (spec m (by omega)).2]
        have := frame_lt_len _ _ _ hb (hK ▸ (show m < K by omega))
        rw [Nat.min_eq_left (Nat.le_of_lt this), Array.extract_append_extract]
        congr 1
        rw [Nat.max_eq_right (Nat.mul_le_mul_right _ (by omega)), Nat.succ_mul]
        congr 1; omega
    simp only [planFrames, hK, ← Array.foldl_toList, Array.toList_map, Array.toList_range]
    rw [step K (Nat.le_refl _), Nat.min_eq_right (hK ▸ len_le_frames _ _ hb), ← size_eq_length_mul x valid,
      Array.extract_eq_self_of_le (Nat.le_refl _)]

omit valid in
theorem foldl_append_fst (g : Nat → ByteArray) (l : List Nat) (o : ByteArray) (lo hi : Nat) :
    (l.foldl (init := (o, lo, hi)) fun (acc : ByteArray × Nat × Nat) k =>
      (acc.1 ++ g k, if k = 0 then (g k).size else min acc.2.1 (g k).size, max acc.2.2 (g k).size)).1 =
    l.foldl (fun out k => out ++ g k) o := by
  induction l generalizing o lo hi with
  | nil => rfl
  | cons k l ih => exact ih _ _ _

omit valid in
theorem foldl_append_assoc (g : Nat → ByteArray) (l : List Nat) (a b : ByteArray) :
    a ++ l.foldl (fun out k => out ++ g k) b = l.foldl (fun out k => out ++ g k) (a ++ b) := by
  induction l generalizing b with
  | nil => rfl
  | cons k l ih => simp only [List.foldl_cons]; rw [ih, ByteArray.append_assoc]

omit valid in
/-- Writing frame by frame is writing the planned frames. -/
theorem encode_body (info : StreamInfo) :
    (writeHead info .empty).bytes ++ (encodeFrames st x).1 = writeStream info ((planFrames st x).map writeFrame) := by
  unfold encodeFrames writeStream
  rw [foldl_append_fst (encodeFrame st x), foldl_append_assoc, ByteArray.append_empty]
  simp only [planFrames, Array.map_map, ← Array.foldl_toList, Array.toList_map, Array.toList_range, List.foldl_map]
  rfl

theorem decode_encode : decode (encode st x) = .ok x := by
  have hb' : st.clampedBlockSize ≤ 65535 := by unfold Settings.clampedBlockSize; omega
  have hC := valid.channels
  have hB := valid.bitsPerSample
  have hR := valid.sampleRate
  have hL := valid.length
  dsimp only [encode]
  generalize (encodeFrames st x).2.1 = minSize
  generalize (encodeFrames st x).2.2 = maxSize
  have fit : ∀ v, fitFrameSize v < 2 ^ 24 := fun v => by unfold fitFrameSize; split <;> omega
  let info : StreamInfo := {
    minBlockSize := st.clampedBlockSize, maxBlockSize := st.clampedBlockSize,
    minFrameSize := fitFrameSize minSize, maxFrameSize := fitFrameSize maxSize,
    sampleRate := x.format.sampleRate, channels := x.format.channels, bitsPerSample := x.format.bitsPerSample,
    totalSamples := x.length, md5 := Md5.ofSamples x.format.bitsPerSample x.samples % 2 ^ 128 }
  obtain ⟨wf, hsamples⟩ := planFrames_spec st x valid info rfl rfl rfl
  have hinfo : info.WF :=
    ⟨⟨show st.clampedBlockSize < 2 ^ 16 by omega, show st.clampedBlockSize < 2 ^ 16 by omega⟩, ⟨fit _, fit _⟩,
      hR.2, hC, show 1 ≤ x.format.bitsPerSample ∧ x.format.bitsPerSample ≤ 32 by omega, hL,
      Nat.mod_lt _ (by decide)⟩
  obtain ⟨p, hp⟩ := streamP_writeStream info (planFrames st x) hinfo wf
  rw [← encode_body st x info] at hp
  unfold decode
  rw [streamSamplesP_eq, hp]
  simp only [bind, Except.bind]
  simp only [Stream.samples, hsamples]
  have hsz : info.totalSamples * info.channels = x.samples.size := (size_eq_length_mul x valid).symm
  rw [if_neg (fun h => h.2 hsz)]
  cases x; rfl

end

end VeriCut.Flac
