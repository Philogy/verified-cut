import VeriCut.Spec.Audio

/-!
# Proof: copied audio plays exactly the source samples, in sync

`exportAudio_present` shows the edit list over the copied packets presents
each cut's target samples, for every codec with one packet of overlap;
`audioStart_eq` and `sampleAt_near` that every cut's audio starts at the
sample nearest its video start. Restated in `Correctness.lean`.
-/

namespace VeriCut

variable {α S : Type} {c : AudioCodec α S} {n : Nat}

theorem decodeAudioAfter_length (hc : c.FrameLength n) (prev : Option α) (xs : List α) :
    (decodeAudioAfter c prev xs).length = n * xs.length := by
  induction xs generalizing prev with
  | nil => simp [decodeAudioAfter]
  | cons x xs ih => simp only [decodeAudioAfter, List.length_append, ih, hc prev x, List.length_cons, Nat.mul_succ]; omega

theorem decodeAudioAfter_take (hc : c.FrameLength n) (prev : Option α) (xs : List α) (m : Nat) :
    decodeAudioAfter c prev (xs.take m) = (decodeAudioAfter c prev xs).take (n * m) := by
  induction xs generalizing prev m with
  | nil => simp [decodeAudioAfter]
  | cons x xs ih =>
    cases m with
    | zero => simp [decodeAudioAfter]
    | succ m =>
      simp only [List.take_succ_cons, decodeAudioAfter, ih, Nat.mul_succ]
      rw [List.take_append, hc prev x, List.take_of_length_le (l := c.frame prev x) (by rw [hc prev x]; omega)]
      congr 2; omega

/-- Decoding after packet `k` from packet `k + 1` on gives the samples a
decoder started anywhere earlier gives there. -/
theorem decodeAudioAfter_drop (hc : c.FrameLength n) (prev : Option α) (xs : List α) (k : Nat)
    (hk : k < xs.length) :
    decodeAudioAfter c (some xs[k]) (xs.drop (k + 1)) = (decodeAudioAfter c prev xs).drop (n * (k + 1)) := by
  induction xs generalizing prev k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => simp [decodeAudioAfter, hc prev x]
    | succ k =>
      simp only [List.getElem_cons_succ, List.drop_succ_cons, decodeAudioAfter]
      rw [ih (some x) k (by simpa using hk), List.drop_append, hc prev x,
        List.drop_of_length_le (l := c.frame prev x) (by rw [hc prev x]; exact Nat.le_mul_of_pos_right n (by omega))]
      simp only [List.nil_append]; congr 1; rw [Nat.mul_succ n (k + 1)]; omega

theorem take_drop_take {β : Type} (l : List β) (k j len : Nat) (h : j + len ≤ k) :
    ((l.take k).drop j).take len = (l.drop j).take len := by
  rw [List.drop_take, List.take_take]; congr 1; omega

theorem take_drop_append {β : Type} (a b : List β) (j len : Nat) (h : j + len ≤ a.length) :
    ((a ++ b).drop j).take len = (a.drop j).take len := by
  rw [List.drop_append, List.take_append, List.length_drop,
    show len - (a.length - j) = 0 by omega, List.take_zero, List.append_nil]

/-- Packets `[f, e)` of `src`, decoded after any packet `prev`, contain the
source samples `[start, start + len)` at offset `start - n * f`, if packet
`f` lies wholly before `start` (a pre-roll), or decoding starts fresh at
packet 0. -/
theorem decode_slice (hc : c.FrameLength n) (prev : Option α) (src : List α) (f e start len : Nat)
    (hcover : start + len ≤ n * e)
    (hpre : (n * f + n ≤ start ∧ f < src.length) ∨ (prev = none ∧ f = 0)) :
    ((decodeAudioAfter c prev ((src.drop f).take (e - f))).drop (start - n * f)).take len =
      ((decodeAudio c src).drop start).take len := by
  rw [decodeAudioAfter_take hc, take_drop_take _ _ _ _ (by
    rw [Nat.mul_sub]; rcases hpre with ⟨h1, _⟩ | ⟨_, rfl⟩ <;> (try simp only [Nat.mul_zero, Nat.sub_zero]) <;> omega)]
  rcases hpre with ⟨h1, hf⟩ | ⟨rfl, rfl⟩
  · rw [List.drop_eq_getElem_cons hf, decodeAudioAfter, decodeAudioAfter_drop hc none src f hf,
      List.drop_append, hc prev, List.drop_of_length_le (l := c.frame prev src[f]) (by rw [hc prev]; omega),
      List.nil_append, List.drop_drop]
    unfold decodeAudio; congr 2; rw [Nat.mul_succ]; omega
  · simp [decodeAudio]

/-- The samples a cut plays exist in its source. -/
def AudioCut.InSource (n : Nat) (cut : AudioCut α) : Prop := cut.start + cut.len ≤ n * cut.source.length

/-- Where a cut's packets start and end, as facts `omega` can use. -/
theorem AudioCut.bounds (cut : AudioCut α) (h : cut.InSource n) (hlen : 0 < cut.len) :
    0 < n ∧ n * (cut.start / n) ≤ cut.start ∧ cut.start < n * (cut.start / n) + n ∧
    cut.start + cut.len ≤ n * ((cut.start + cut.len + n - 1) / n) ∧
    (cut.start + cut.len + n - 1) / n ≤ cut.source.length := by
  unfold InSource at h
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at h; omega
  have h1 := Nat.mul_div_le cut.start n
  have h2 := Nat.lt_mul_div_succ cut.start hn
  rw [Nat.mul_succ] at h2
  refine ⟨hn, h1, h2, ?_⟩
  generalize hx : cut.start + cut.len + n - 1 = x
  have h3 := Nat.div_add_mod x n
  have h4 := Nat.mod_lt x hn
  have h5 := (Nat.div_lt_iff_lt_mul (x := x) (y := cut.source.length + 1) hn).2
    (by rw [Nat.succ_mul, Nat.mul_comm cut.source.length n]; omega)
  exact ⟨by omega, by omega⟩

theorem AudioCut.packets_length (hc : c.FrameLength n) (prev : Option α) (cut : AudioCut α)
    (h : cut.InSource n) (hlen : 0 < cut.len) :
    (decodeAudioAfter c prev (cut.packets n)).length = n * ((cut.start + cut.len + n - 1) / n - cut.first n) := by
  obtain ⟨_, _, _, _, he⟩ := cut.bounds h hlen
  rw [decodeAudioAfter_length hc, packets, if_neg (by omega), List.length_take, List.length_drop,
    Nat.min_eq_left (by unfold first; omega)]

/-- **One cut.** Its packets, decoded after anything (or from a fresh start
if it begins in the source's first packet), contain its source samples where
its edit points. -/
theorem AudioCut.decode_packets (hc : c.FrameLength n) (prev : Option α) (cut : AudioCut α)
    (h : cut.InSource n) (hlen : 0 < cut.len) (hpre : prev = none ∨ n ≤ cut.start) :
    ((decodeAudioAfter c prev (cut.packets n)).drop (cut.start - n * cut.first n)).take cut.len =
      ((decodeAudio c cut.source).drop cut.start).take cut.len := by
  obtain ⟨hn, h1, h2, h3, h4⟩ := cut.bounds h hlen
  rw [packets, if_neg (by omega)]
  apply decode_slice hc prev cut.source _ _ _ _ h3
  unfold first
  by_cases hs : n ≤ cut.start
  · left
    have hq : 1 ≤ cut.start / n := (Nat.le_div_iff_mul_le hn).2 (by omega)
    refine ⟨?_, ?_⟩
    · rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hq]; exact h1
    · unfold InSource at h
      have := (Nat.div_lt_iff_lt_mul hn).2 (show cut.start < cut.source.length * n by rw [Nat.mul_comm]; omega)
      omega
  · right
    refine ⟨hpre.resolve_right hs, ?_⟩
    rw [Nat.div_eq_of_lt (by omega)]

theorem decodeAudioAfter_append (prev : Option α) (xs ys : List α) :
    decodeAudioAfter c prev (xs ++ ys) =
      decodeAudioAfter c prev xs ++ decodeAudioAfter c (xs.getLast?.or prev) ys := by
  induction xs generalizing prev with
  | nil => simp [decodeAudioAfter]
  | cons x xs ih =>
    simp only [List.cons_append, decodeAudioAfter, ih, List.append_assoc]
    congr 3
    cases xs with
    | nil => rfl
    | cons y ys => rw [List.getLast?_cons_cons, List.getLast?_eq_some_getLast (by simp)]; rfl

theorem present_append (silence : S) (pcm : List S) (a b : List Edit) :
    present silence pcm (a ++ b) = present silence pcm a ++ present silence pcm b := by
  simp [present, List.flatMap_append]

/-- A cut that can follow other audio: it has a pre-roll packet, or plays nothing. -/
def AudioCut.Splices (n : Nat) (cut : AudioCut α) : Prop := n ≤ cut.start ∨ cut.len = 0

/-- The edits of a cut, over media whose first `at_` samples are anything and
whose rest is its packets decoded after `prev`, followed by anything, present
its target. -/
theorem AudioCut.present_edits (hc : c.FrameLength n) (silence : S) (cut : AudioCut α)
    (prev : Option α) (X R : List S) (h : cut.InSource n) (hpre : prev = none ∨ cut.Splices n) :
    present silence (X ++ (decodeAudioAfter c prev (cut.packets n) ++ R)) (cut.edits n X.length) =
      cut.target c silence := by
  simp only [edits, present, List.flatMap_cons, List.flatMap_nil, List.append_nil, target,
    List.append_assoc]
  congr 2
  rw [Nat.add_sub_assoc (by
      unfold first; exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) (Nat.mul_div_le _ _)),
    List.drop_append, List.drop_of_length_le (l := X) (by omega), List.nil_append,
    show X.length + (cut.start - n * first n cut) - X.length = cut.start - n * first n cut by omega]
  by_cases hlen : cut.len = 0
  · simp [hlen]
  · have hb := cut.bounds h (by omega)
    rw [take_drop_append _ _ _ _ (by
      rw [packets_length hc prev cut h (by omega), Nat.mul_sub]
      unfold first; have := Nat.mul_le_mul_left n (Nat.sub_le (cut.start / n) 1); omega)]
    exact cut.decode_packets hc prev h (by omega) (hpre.imp_right (·.resolve_right hlen))

theorem exportAudio_go_present (hc : c.FrameLength n) (silence : S) :
    ∀ (cuts : List (AudioCut α)) (X : List S) (prev : Option α),
      (∀ cut ∈ cuts, cut.InSource n) → (∀ cut ∈ cuts.tail, cut.Splices n) →
      (prev = none ∨ ∀ cut ∈ cuts.head?, cut.Splices n) →
      present silence (X ++ decodeAudioAfter c prev (exportAudio.go n X.length cuts).1)
        (exportAudio.go n X.length cuts).2 = (cuts.map (·.target c silence)).flatten
  | [], _, _, _, _, _ => by simp [exportAudio.go, present]
  | cut :: rest, X, prev, hin, htail, hhead => by
    simp only [exportAudio.go, decodeAudioAfter_append, present_append, List.map_cons, List.flatten_cons]
    have hD := decodeAudioAfter_length hc prev (cut.packets n)
    rw [cut.present_edits hc silence prev X _ (hin cut (by simp))
      (hhead.imp_right fun h => h cut (by simp))]
    congr 1
    have ih := exportAudio_go_present hc silence rest (X ++ decodeAudioAfter c prev (cut.packets n))
      ((cut.packets n).getLast?.or prev) (fun x hx => hin x (by simp [hx]))
      (fun x hx => htail x (List.mem_of_mem_tail hx))
      (Or.inr fun x hx => htail x (by cases rest <;> simp_all))
    rw [List.length_append, hD, List.append_assoc] at ih
    exact ih

/-- The audio exporter's edit list over its packets presents every cut's target. -/
theorem exportAudio_present (hc : c.FrameLength n) (silence : S) (cuts : List (AudioCut α))
    (hin : ∀ cut ∈ cuts, cut.InSource n) (htail : ∀ cut ∈ cuts.tail, cut.Splices n) :
    present silence (decodeAudio c (exportAudio n cuts).1) (exportAudio n cuts).2 =
      (cuts.map (·.target c silence)).flatten := by
  simpa [exportAudio, decodeAudio] using exportAudio_go_present hc silence cuts [] none hin htail (.inl rfl)

/-! ## The cuts `exportAudioClips` makes -/

variable {sampleRate rate : Nat}

theorem AudioClip.cut_inSource (clip : AudioClip α) (first : Bool) (t0 : Nat) :
    (clip.cut n sampleRate rate first t0).InSource n := by
  simp only [AudioCut.InSource, cut]; omega

theorem AudioClip.cut_splices (clip : AudioClip α) (t0 : Nat) :
    (clip.cut n sampleRate rate false t0).Splices n := by
  simp only [AudioCut.Splices, cut, Bool.false_eq_true, ↓reduceIte]; omega

theorem audioCuts_inSource (first : Bool) :
    ∀ (t0 : Nat) (clips : List (AudioClip α)), ∀ cut ∈ audioCuts n sampleRate rate first t0 clips, cut.InSource n
  | _, [] => by simp [audioCuts]
  | t0, clip :: rest => by
    simp only [audioCuts, List.mem_cons, forall_eq_or_imp]
    exact ⟨clip.cut_inSource first t0, audioCuts_inSource false _ rest⟩

theorem audioCuts_splices :
    ∀ (t0 : Nat) (clips : List (AudioClip α)), ∀ cut ∈ audioCuts n sampleRate rate false t0 clips, cut.Splices n
  | _, [] => by simp [audioCuts]
  | t0, clip :: rest => by
    simp only [audioCuts, List.mem_cons, forall_eq_or_imp]
    exact ⟨clip.cut_splices t0, audioCuts_splices _ rest⟩

/-- The audio track of a timeline presents each clip's cut. -/
theorem exportAudioClips_present (hc : c.FrameLength n) (silence : S) (clips : List (AudioClip α)) :
    let cuts := audioCuts n sampleRate rate true 0 clips
    present silence (decodeAudio c (exportAudioClips n sampleRate rate clips).1)
      (exportAudioClips n sampleRate rate clips).2 = (cuts.map (·.target c silence)).flatten := by
  apply exportAudio_present hc silence _ (audioCuts_inSource true 0 clips)
  cases clips with
  | nil => simp [audioCuts]
  | cons clip rest => exact audioCuts_splices _ rest

/-- The source samples a cut plays are the ones from `srcStart` on: the
cut's `lead` silence stands in for source samples `srcStart, …` that are
not played. -/
theorem AudioClip.cut_start (clip : AudioClip α) (first : Bool) (t0 : Nat)
    (h : 0 < (clip.cut n sampleRate rate first t0).len) :
    ((clip.cut n sampleRate rate first t0).start : Int) - (clip.cut n sampleRate rate first t0).lead =
      clip.srcStart := by
  simp only [cut] at h ⊢; cases first <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> omega

/-- A cut lasts from the sample nearest its video start to the one nearest its video end. -/
theorem AudioClip.cut_length (clip : AudioClip α) (first : Bool) (t0 : Nat) :
    (clip.cut n sampleRate rate first t0).length =
      sampleAt sampleRate rate (t0 + clip.ticks) - sampleAt sampleRate rate t0 := by
  simp only [AudioCut.length, cut]; omega

theorem sampleAt_mono (t d : Nat) : sampleAt sampleRate rate t ≤ sampleAt sampleRate rate (t + d) :=
  Nat.div_le_div_right (by rw [Nat.mul_add, Nat.add_mul]; omega)

theorem sampleAt_zero : sampleAt sampleRate rate 0 = 0 := by
  unfold sampleAt; rcases Nat.eq_zero_or_pos rate with h | h
  · simp [h]
  · exact Nat.div_eq_of_lt (by omega)

theorem audioStart_audioCuts (first : Bool) :
    ∀ (t0 : Nat) (clips : List (AudioClip α)) (i : Nat), i ≤ clips.length →
      audioStart (audioCuts n sampleRate rate first t0 clips) i =
        sampleAt sampleRate rate (t0 + videoStart clips i) - sampleAt sampleRate rate t0
  | t0, [], i, hi => by simp_all [audioStart, videoStart, audioCuts]
  | t0, clip :: rest, 0, _ => by simp [audioStart, videoStart]
  | t0, clip :: rest, i + 1, hi => by
    have ih := audioStart_audioCuts false (t0 + clip.ticks) rest i (by simpa using hi)
    simp only [audioStart, videoStart, audioCuts, List.take_succ_cons, List.map_cons, List.sum_cons] at *
    rw [ih, clip.cut_length]
    have h1 := sampleAt_mono (sampleRate := sampleRate) (rate := rate) t0 clip.ticks
    have h2 := sampleAt_mono (sampleRate := sampleRate) (rate := rate) (t0 + clip.ticks)
      ((rest.take i).map (·.ticks)).sum
    rw [Nat.add_assoc] at h2 ⊢; omega

/-- The sample nearest a time is within half a sample of it. -/
theorem sampleAt_near (hrate : 0 < rate) (t : Nat) :
    2 * ((sampleAt sampleRate rate t : Int) * rate - t * sampleRate).natAbs ≤ rate := by
  have h1 := Nat.div_add_mod (2 * t * sampleRate + rate) (2 * rate)
  have h2 := Nat.mod_lt (2 * t * sampleRate + rate) (show 0 < 2 * rate by omega)
  unfold sampleAt
  generalize (2 * t * sampleRate + rate) / (2 * rate) = q at *
  have : 2 * rate * q = 2 * (q * rate) := by rw [Nat.mul_comm q, Nat.mul_assoc]
  have : 2 * t * sampleRate = 2 * (t * sampleRate) := Nat.mul_assoc _ _ _
  push_cast
  omega

theorem exportAudioClips_synced (hrate : 0 < rate) (clips : List (AudioClip α)) (i : Nat)
    (hi : i ≤ clips.length) :
    2 * ((audioStart (audioCuts n sampleRate rate true 0 clips) i : Int) * rate -
      videoStart clips i * sampleRate).natAbs ≤ rate := by
  rw [audioStart_audioCuts true 0 clips i hi, sampleAt_zero, Nat.zero_add, Nat.sub_zero]
  exact sampleAt_near hrate _

end VeriCut
