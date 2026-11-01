import VeriCut.Proofs.Fast.Writer
import VeriCut.Proofs.Fast.Predict
import VeriCut.Flac.Fast.Decode

/-! `decodeFast d = decode d` for every `d`. -/

namespace VeriCut.Flac.Fast

open Parser

theorem readSigned_eq (k : Nat) : Fast.readSigned k = Parser.readSigned k := by
  unfold Fast.readSigned Parser.readSigned
  simp only [pow2_eq]; push_cast; rfl

theorem le_nextOne (d : ByteArray) (p : Nat) (hp : p ≤ 8 * d.size) : p ≤ nextOne d p := by
  induction p using nextOne.induct d with
  | case1 p h hb => rw [nextOne]; simp [h, hb]
  | case2 p h hb ih => rw [nextOne]; simp only [h, dite_true, hb, if_false]; have := ih (by omega); omega
  | case3 p h => rw [nextOne]; simp [h]; omega

theorem unaryAux_nextOne (d : ByteArray) (p q : Nat) :
    unaryAux d p q = if nextOne d p < 8 * d.size then .ok (q + (nextOne d p - p), nextOne d p + 1)
      else .error "unexpected end of stream" := by
  induction p, q using unaryAux.induct d with
  | case1 p q h hb =>
    rw [unaryAux, nextOne]
    simp only [h, dite_true, hb, if_true]
    rw [if_pos (by omega)]; simp
  | case2 p q h hb ih =>
    rw [unaryAux, nextOne]
    simp only [h, dite_true, hb, if_false, ih]
    have : p + 1 ≤ nextOne d (p + 1) := le_nextOne d (p + 1) (by omega)
    split <;> simp; omega
  | case3 p q h =>
    rw [unaryAux, nextOne]
    simp [h]

theorem readBitsAux_bitsVal (d : ByteArray) (k acc p : Nat) :
    readBitsAux d k acc p = if k = 0 ∨ p + k ≤ 8 * d.size then .ok (bitsVal d k acc p, p + k)
      else .error "unexpected end of stream" := by
  induction k generalizing acc p with
  | zero => simp [readBitsAux, bitsVal]
  | succ k ih =>
    rw [readBitsAux]
    split
    · rename_i h
      rw [ih, bitsVal, dif_pos h]
      by_cases hk : k = 0 ∨ p + 1 + k ≤ 8 * d.size
      · rw [if_pos hk, if_pos (by omega)]; congr 2; omega
      · rw [if_neg hk, if_neg (by omega)]
    · rename_i h
      rw [if_neg (by omega)]

theorem ricesLoop_eq (d : ByteArray) (k : Nat) :
    ∀ c acc p, ricesLoop d k c acc p = many (riceP k) c acc d p := by
  intro c
  induction c with
  | zero => intro acc p; rfl
  | succ c ih =>
    intro acc p
    show _ = Parser.bind (riceP k) (fun a => many (riceP k) c (acc.push a)) d p
    simp only [ricesLoop, riceP, bind, Parser.bind, unary, readBits, unaryAux_nextOne, readBitsAux_bitsVal]
    by_cases h1 : nextOne d p < 8 * d.size
    · rw [if_pos h1, if_pos h1]
      dsimp only
      by_cases h2 : k = 0 ∨ nextOne d p + 1 + k ≤ 8 * d.size
      · rw [if_pos h2, if_pos h2]
        simp only [pure, Parser.pure, Nat.zero_add, pow2_eq]
        exact ih _ _
      · rw [if_neg h2, if_neg h2]
    · rw [if_neg h1, if_neg h1]

theorem ricesP_eq (k c : Nat) (acc : Array Int) : ricesP k c acc = many (riceP k) c acc := by
  funext d p; exact ricesLoop_eq d k c acc p

theorem partitionP_eq (pb c : Nat) : Fast.partitionP pb c = Flac.partitionP pb c := by
  unfold Fast.partitionP Flac.partitionP
  simp only [readSigned_eq, ricesP_eq]

theorem residualP_eq (n w : Nat) : Fast.residualP n w = Flac.residualP n w := by
  unfold Fast.residualP Flac.residualP
  simp only [partitionP_eq]

theorem bodyP_eq (bits n type : Nat) : Fast.bodyP bits n type = Flac.bodyP bits n type := by
  unfold Fast.bodyP Flac.bodyP
  simp only [readSigned_eq, residualP_eq]

theorem subframeP_eq (bits n : Nat) : Fast.subframeP bits n = Flac.subframeP bits n := by
  unfold Fast.subframeP Flac.subframeP
  simp only [bodyP_eq]

theorem subframesP_eq (h : Header) : ∀ k acc, Fast.subframesP h k acc = Flac.subframesP h k acc
  | 0, _ => rfl
  | k + 1, acc => by
    unfold Fast.subframesP Flac.subframesP
    simp only [subframeP_eq, subframesP_eq h k]

theorem frameP_eq (info : StreamInfo) : Fast.frameP info = Flac.frameP info := by
  unfold Fast.frameP Flac.frameP
  simp only [subframesP_eq, crc16_eq]

theorem frameSamples_eq (f : Frame) : frameSamples f = f.samples := by
  have hb : ∀ n b, bodySamples n b = b.samples n := by
    intro n b; cases b <;> simp [bodySamples, Body.samples, restoreFast_eq]
  have hs : subframeSamples = Subframe.samples := by
    funext n sf; unfold subframeSamples Subframe.samples; simp [hb, pow2_eq]
  unfold frameSamples Frame.samples
  rw [hs]

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
    simp only [framesSamplesP, framesP, bind, Parser.bind, atEnd, frameP_eq, frameSamples_eq]
    split
    · rfl
    · cases h : Flac.frameP info d p with
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

/-- The fast decoder is the spec's decoder, on every input. -/
theorem decodeFast_eq (d : ByteArray) : decodeFast d = decode d := by
  unfold decodeFast decode
  rw [streamSamplesP_eq]
  cases streamP d 0 with
  | error e => rfl
  | ok r => obtain ⟨s, p⟩ := r; rfl

end VeriCut.Flac.Fast
