import Lossy.Proofs.Analyze

namespace Lossy.Flac
open Reader

theorem run_bind (p : Reader α) (f : α → Reader β) (a : ByteArray) (pos : Nat) :
    (p >>= f).run a pos = (match p.run a pos with
      | some (v, pos') => (f v).run a pos'
      | none => none) := rfl

theorem readUtf8_ok {n : Nat} (hn : n < 2 ^ 21) : Parses readUtf8 n (utf8 n) := by
  unfold readUtf8 utf8
  by_cases h1 : n < 128
  · simp only [if_pos h1]
    refine ((Parses.nat_lt (by omega)).bind ?_).congr rfl (List.append_nil _)
    simp only [if_pos h1]; exact Parses.pure n
  by_cases h2 : n < 2048
  · simp only [if_neg h1, if_pos h2]
    refine ((Parses.nat_lt (k := 8) (n := 192 + n / 64) (by omega)).bind ?_).congr rfl rfl
    simp only [if_neg (show ¬ 192 + n / 64 < 128 by omega), if_pos (show 192 + n / 64 < 224 by omega)]
    refine (Parses.map _ (Parses.nat_lt (k := 8) (n := 128 + n % 64) (by omega))).congr ?_ rfl
    omega
  by_cases h3 : n < 65536
  · simp only [if_neg h1, if_neg h2, if_pos h3, List.append_assoc]
    refine (Parses.nat_lt (k := 8) (n := 224 + n / 4096) (by omega)).bind ?_
    simp only [if_neg (show ¬ 224 + n / 4096 < 128 by omega),
      if_neg (show ¬ 224 + n / 4096 < 224 by omega), if_pos (show 224 + n / 4096 < 240 by omega)]
    refine (Parses.nat_lt (k := 8) (n := 128 + n / 64 % 64) (by omega)).bind ?_
    refine (Parses.map _ (Parses.nat_lt (k := 8) (n := 128 + n % 64) (by omega))).congr ?_ rfl
    omega
  · simp only [if_neg h1, if_neg h2, if_neg h3, List.append_assoc]
    refine (Parses.nat_lt (k := 8) (n := 240 + n / 262144) (by omega)).bind ?_
    simp only [if_neg (show ¬ 240 + n / 262144 < 128 by omega),
      if_neg (show ¬ 240 + n / 262144 < 224 by omega),
      if_neg (show ¬ 240 + n / 262144 < 240 by omega)]
    refine (Parses.nat_lt (k := 8) (n := 128 + n / 4096 % 64) (by omega)).bind ?_
    refine (Parses.nat_lt (k := 8) (n := 128 + n / 64 % 64) (by omega)).bind ?_
    refine (Parses.map _ (Parses.nat_lt (k := 8) (n := 128 + n % 64) (by omega))).congr ?_ rfl
    omega

/-- A frame `readFrame` can read back. -/
structure FrameOk (bps : Nat) (fr : Frame) : Prop where
  chans : 1 ≤ fr.subs.length ∧ fr.subs.length ≤ 16
  number : fr.number < 2 ^ 21
  size : 1 ≤ fr.size ∧ fr.size ≤ 2 ^ 16
  subs : ∀ ws ∈ fr.subs, ws.1 < bps ∧ ws.2.Ok (bps - ws.1) fr.size

theorem readFrameBody_ok {bps : Nat} {fr : Frame} (h : FrameOk bps fr) :
    Parses (readFrameBody bps fr.subs.length) (fr.size - 1, fr.subs) (bodyBits bps fr) := by
  simp only [readFrameBody, bodyBits, headerBits, List.append_assoc]
  refine (Parses.expect (k := 16) (n := 0xFFF8) (by decide)).bind ?_
  refine (Parses.expect (k := 8) (n := 0x70) (by decide)).bind ?_
  refine (Parses.expect (k := 4) (n := fr.subs.length - 1) (by have := h.chans; omega)).bind ?_
  refine (Parses.expect (k := 4) (n := 0) (by decide)).bind ?_
  refine (readUtf8_ok h.number).bind ?_
  refine (Parses.nat_lt (k := 16) (n := fr.size - 1) (by have := h.size; omega)).bind ?_
  refine (Parses.nat 8 _).bind ?_
  rw [show fr.size - 1 + 1 = fr.size by have := h.size; omega]
  exact Parses.map _ (Parses.many fr.subs fun ws hws => by
    have := h.subs ws hws
    exact readSub_ok this.1 this.2)

/-- Like `Parses`, for readers that start on a byte boundary. -/
def Parses8 (p : Reader α) (v : α) (l : List Bool) : Prop :=
  ∀ a pos, pos % 8 = 0 → At a pos l → p.run a pos = some (v, pos + l.length)

theorem Parses.parses8 {p : Reader α} {v : α} {l : List Bool} (h : Parses p v l) : Parses8 p v l :=
  fun a pos _ hat => h a pos hat

theorem Parses8.bind {p : Reader α} {f : α → Reader β} {v : α} {w : β} {l₁ l₂ : List Bool}
    (h₁ : Parses8 p v l₁) (h8 : l₁.length % 8 = 0) (h₂ : Parses8 (f v) w l₂) :
    Parses8 (p >>= f) w (l₁ ++ l₂) := by
  intro a pos hpos h
  rw [At.append_iff] at h
  rw [run_bind, h₁ a pos hpos h.1]
  simp only
  rw [h₂ a _ (by omega) h.2]
  simp [Nat.add_assoc]

theorem flatMap_len8 {ser : α → List Bool} :
    ∀ (vs : List α), (∀ v ∈ vs, (ser v).length % 8 = 0) → (vs.flatMap ser).length % 8 = 0
  | [], _ => rfl
  | v :: vs, h => by
    simp only [List.flatMap_cons, List.length_append]
    have := h v (by simp)
    have := flatMap_len8 vs fun w hw => h w (by simp [hw])
    omega

theorem Parses8.many {p : Reader α} {val : β → α} {ser : β → List Bool} :
    ∀ (fs : List β), (∀ f ∈ fs, Parses8 p (val f) (ser f) ∧ (ser f).length % 8 = 0) →
      Parses8 (Reader.many p fs.length) (fs.map val) (fs.flatMap ser)
  | [], _ => Parses.parses8 (Parses.pure [])
  | f :: fs, h => by
    have hrest := Parses8.many fs fun g hg => h g (by simp [hg])
    have := Parses8.bind (h f (by simp)).1 (h f (by simp)).2 (f := fun v => do
        let vs ← Reader.many p fs.length; Pure.pure (v :: vs))
      (Parses8.bind hrest (flatMap_len8 fs fun g hg => (h g (by simp [hg])).2)
        (Parses.parses8 (Parses.pure (val f :: fs.map val))))
    simpa [Reader.many] using this

theorem length_frameBits (bps : Nat) (fr : Frame) : (frameBits bps fr).length % 8 = 0 := by
  simp only [frameBits, padBits, zeros, List.length_append, List.length_replicate, length_bitsOf]
  omega

theorem readFrame_ok {bps : Nat} {fr : Frame} (h : FrameOk bps fr) :
    Parses8 (readFrame bps fr.subs.length) (samplesOf fr.size fr.subs) (frameBits bps fr) := by
  intro a pos hpos hat
  have hbody := readFrameBody_ok h
  simp only [frameBits, At.append_iff] at hat
  obtain ⟨⟨hb, hpad⟩, hcrc⟩ := hat
  simp only [readFrame]
  rw [run_bind, hbody a pos hb]
  simp only
  rw [run_bind]
  have hal : align.run a (pos + (bodyBits bps fr).length) =
      some ((), pos + (bodyBits bps fr).length + (padBits (bodyBits bps fr)).length) := by
    simp only [align, padBits, zeros, List.length_replicate]
    have := hpad.1
    simp only [padBits, zeros, List.length_replicate] at this
    rw [if_pos (by omega)]
    congr 3; omega
  rw [hal]
  simp only
  rw [run_bind, Parses.nat 16 _ a _ (by simpa [Nat.add_assoc] using hcrc)]
  simp only [Pure.pure, Option.some.injEq, Prod.mk.injEq]
  rw [show fr.size - 1 + 1 = fr.size by have := h.size; omega]
  simp [frameBits, Nat.add_assoc]

end Lossy.Flac
