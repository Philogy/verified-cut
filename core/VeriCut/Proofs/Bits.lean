import VeriCut.Flac.Bits

/-!
The bit layer, as lists of bits: `Writer.write k v` appends `natBits k v`, and
`Parser.readBits k` reads it back.

`Encodes f l`: the writer step `f` appends `l`.
`Decodes p l a`: on any data whose bits from the position on start with `l`,
`p` returns `a` and moves past `l`.
-/

namespace VeriCut

/-- The low `k` bits of `v`, most significant first. -/
def natBits : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, v => v.testBit k :: natBits k v

def bitsOf (d : ByteArray) : List Bool := d.data.toList.flatMap fun b => natBits 8 b.toNat

def Writer.bits (w : Writer) : List Bool := bitsOf w.bytes ++ natBits w.n w.acc

def Encodes (f : Writer → Writer) (l : List Bool) : Prop := ∀ w, (f w).bits = w.bits ++ l

def Decodes {α : Type} (p : Parser α) (l : List Bool) (a : α) : Prop :=
  ∀ d pos t, (bitsOf d).drop pos = l ++ t → p d pos = .ok (a, pos + l.length)

/-! ## `natBits` -/

@[simp] theorem natBits_zero (v : Nat) : natBits 0 v = [] := rfl

@[simp] theorem length_natBits (k v : Nat) : (natBits k v).length = k := by
  induction k <;> simp [natBits, *]

theorem natBits_add (a b x : Nat) : natBits (a + b) x = natBits a (x / 2 ^ b) ++ natBits b x := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp [natBits, ih, Nat.testBit_div_two_pow]

theorem natBits_mod (k m x : Nat) (h : k ≤ m) : natBits k (x % 2 ^ m) = natBits k x := by
  induction k with
  | zero => rfl
  | succ k ih => simp [natBits, ih (by omega), Nat.testBit_mod_two_pow, show k < m by omega]

theorem natBits_mul_add (n k a b : Nat) (hb : b < 2 ^ k) :
    natBits (n + k) (a * 2 ^ k + b) = natBits n a ++ natBits k b := by
  rw [natBits_add, ← natBits_mod k k (a * 2 ^ k + b) (Nat.le_refl _)]
  have : (a * 2 ^ k + b) / 2 ^ k = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hb, Nat.zero_add]
  rw [this, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

theorem natBits_zero_eq_replicate (k : Nat) : natBits k 0 = List.replicate k false := by
  induction k <;> simp [natBits, List.replicate_succ, *]

theorem getElem_natBits (k x i : Nat) (h : i < (natBits k x).length) :
    (natBits k x)[i] = x.testBit (k - 1 - i) := by
  induction k generalizing i with
  | zero => simp at h
  | succ k ih =>
    cases i with
    | zero => simp [natBits]
    | succ i => simp [natBits, ih]; congr 1; omega

/-! ## Bytes -/

@[simp] theorem bitsOf_empty : bitsOf .empty = [] := rfl

@[simp] theorem bitsOf_push (d : ByteArray) (b : UInt8) : bitsOf (d.push b) = bitsOf d ++ natBits 8 b.toNat := by
  rw [bitsOf, ByteArray.data_push, Array.toList_push, List.flatMap_append]; rfl

@[simp] theorem bitsOf_append (a b : ByteArray) : bitsOf (a ++ b) = bitsOf a ++ bitsOf b := by
  rw [bitsOf, ByteArray.data_append, Array.toList_append, List.flatMap_append]; rfl

theorem length_flatMap_bytes (l : List UInt8) : (l.flatMap fun b => natBits 8 b.toNat).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.flatMap_cons, List.length_append, length_natBits, ih, List.length_cons]; omega

@[simp] theorem length_bitsOf (d : ByteArray) : (bitsOf d).length = 8 * d.size := by
  rw [bitsOf, length_flatMap_bytes, Array.length_toList, ByteArray.size_data]

theorem getElem_flatMap_bytes (l : List UInt8) (i : Nat) (h : i < (l.flatMap fun b => natBits 8 b.toNat).length) :
    ∃ h' : i / 8 < l.length,
      (l.flatMap fun b => natBits 8 b.toNat)[i] = l[i / 8].toNat.testBit (7 - i % 8) := by
  induction l generalizing i with
  | nil => simp at h
  | cons b l ih =>
    rw [length_flatMap_bytes] at h
    simp only [List.length_cons] at h
    by_cases hi : i < 8
    · refine ⟨by simp; omega, ?_⟩
      simp only [List.flatMap_cons, List.getElem_append, length_natBits, hi, dite_true, getElem_natBits]
      simp [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · obtain ⟨h', e⟩ := ih (i - 8) (by rw [length_flatMap_bytes]; omega)
      refine ⟨by simp; omega, ?_⟩
      simp only [List.flatMap_cons, List.getElem_append, length_natBits, hi, dite_false, e]
      have h8 : i / 8 = (i - 8) / 8 + 1 := by omega
      have m8 : (i - 8) % 8 = i % 8 := by omega
      simp [h8, m8]

theorem getElem_bitsOf (d : ByteArray) (i : Nat) (h : i < (bitsOf d).length) :
    ∃ h' : i / 8 < d.size, (bitsOf d)[i] = d[i / 8].toNat.testBit (7 - i % 8) := by
  obtain ⟨h', e⟩ := getElem_flatMap_bytes d.data.toList i h
  have hs : i / 8 < d.size := by rw [Array.length_toList, ByteArray.size_data] at h'; exact h'
  refine ⟨hs, ?_⟩
  show (d.data.toList.flatMap fun b => natBits 8 b.toNat)[i] = _
  rw [e, ByteArray.getElem_eq_getElem_data, Array.getElem_toList]

theorem natBits_inj {k x y : Nat} (hx : x < 2 ^ k) (hy : y < 2 ^ k) (h : natBits k x = natBits k y) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · have e := congrArg (fun l => l[k - 1 - i]?) h
    simp only [List.getElem?_eq_getElem (by simp; omega : k - 1 - i < (natBits k x).length),
      List.getElem?_eq_getElem (by simp; omega : k - 1 - i < (natBits k y).length), Option.some.injEq,
      getElem_natBits] at e
    rwa [show k - 1 - (k - 1 - i) = i by omega] at e
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega)))]

theorem flatMap_bytes_inj : ∀ {l l' : List UInt8},
    (l.flatMap fun b => natBits 8 b.toNat) = (l'.flatMap fun b => natBits 8 b.toNat) → l = l'
  | [], [], _ => rfl
  | [], b :: l', h => by have := congrArg List.length h; rw [length_flatMap_bytes, length_flatMap_bytes] at this; simp at this
  | b :: l, [], h => by have := congrArg List.length h; rw [length_flatMap_bytes, length_flatMap_bytes] at this; simp at this
  | b :: l, b' :: l', h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    have : b.toNat = b'.toNat := natBits_inj b.toNat_lt b'.toNat_lt h1
    rw [UInt8.toNat_inj.1 this, flatMap_bytes_inj h2]

theorem bitsOf_inj {a b : ByteArray} (h : bitsOf a = bitsOf b) : a = b := by
  apply ByteArray.ext
  apply Array.toList_inj.1
  exact flatMap_bytes_inj h

theorem bitsOf_split (d : ByteArray) (i : Nat) (hi : i ≤ d.size) :
    bitsOf d = bitsOf (d.extract 0 i) ++ bitsOf (d.extract i d.size) := by
  rw [← bitsOf_append, ← ByteArray.extract_eq_extract_append_extract i (Nat.zero_le _) hi,
    ByteArray.extract_zero_size]

/-- The bytes at a byte-aligned bit position. -/
theorem extract_of_drop {d b : ByteArray} {pos : Nat} {t : List Bool} (hpos : pos % 8 = 0)
    (h : (bitsOf d).drop pos = bitsOf b ++ t) : d.extract (pos / 8) (pos / 8 + b.size) = b := by
  have hlen := congrArg List.length h
  simp only [List.length_drop, length_bitsOf, List.length_append] at hlen
  by_cases hb : b.size = 0
  · rw [ByteArray.size_eq_zero_iff.1 hb]; simp [ByteArray.extract_same]
  have hi : pos / 8 + b.size ≤ d.size := by omega
  have hp : pos = 8 * (pos / 8) := by omega
  rw [bitsOf_split d (pos / 8) (by omega), hp,
    List.drop_left' (by simp [ByteArray.size_extract]; omega),
    ByteArray.extract_eq_extract_append_extract (pos / 8 + b.size) (by omega) hi, bitsOf_append] at h
  rw [← hp] at h
  exact bitsOf_inj (List.append_inj h (by simp [ByteArray.size_extract]; omega)).1

/-! ## Writer -/

theorem flush_bits (bytes : ByteArray) (acc n : Nat) :
    (Writer.flush bytes acc n).bits = bitsOf bytes ++ natBits n acc := by
  induction n using Nat.strongRecOn generalizing bytes acc with
  | _ n ih =>
    unfold Writer.flush
    split
    · rw [ih _ (by omega), bitsOf_push, List.append_assoc, natBits_mod _ _ _ (Nat.le_refl _)]
      have e := natBits_add 8 (n - 8) acc
      rw [show 8 + (n - 8) = n by omega] at e
      rw [e, Nat.shiftRight_eq_div_pow]
      congr 2
      rw [Nat.toUInt8, UInt8.toNat_ofNat', show (2 : Nat) ^ 8 = 2 ^ 8 from rfl] <;> try rfl
      exact natBits_mod 8 8 _ (Nat.le_refl _)
    · rfl

theorem flush_n_lt (bytes : ByteArray) (acc n : Nat) : (Writer.flush bytes acc n).n < 8 := by
  induction n using Nat.strongRecOn generalizing bytes acc with
  | _ n ih =>
    unfold Writer.flush
    split
    · exact ih _ (by omega) _ _
    · simp; omega

theorem write_bits (w : Writer) (k v : Nat) : (w.write k v).bits = w.bits ++ natBits k v := by
  unfold Writer.write
  rw [flush_bits]
  simp only [Writer.bits, Nat.shiftLeft_eq]
  rw [natBits_mul_add _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos k)), natBits_mod _ _ _ (Nat.le_refl _)]
  simp

theorem length_bits (w : Writer) : w.bits.length = 8 * w.bytes.size + w.n := by
  simp [Writer.bits]

/-- A writer at a byte boundary holds just its bytes. -/
theorem bits_aligned (w : Writer) (hn : w.n < 8) (h : w.bits.length % 8 = 0) : w.bits = bitsOf w.bytes := by
  have : w.n = 0 := by rw [length_bits] at h; omega
  simp [Writer.bits, this]

theorem write_n_lt (w : Writer) (k v : Nat) : (w.write k v).n < 8 := flush_n_lt _ _ _

theorem encodes_write (k v : Nat) : Encodes (·.write k v) (natBits k v) := fun w => write_bits w k v

theorem zeros_bits (w : Writer) (k : Nat) : (w.zeros k).bits = w.bits ++ List.replicate k false := by
  induction k using Nat.strongRecOn generalizing w with
  | _ k ih =>
    unfold Writer.zeros
    split
    · simp [write_bits, natBits_zero_eq_replicate]
    · rw [ih _ (by omega), write_bits, natBits_zero_eq_replicate, List.append_assoc, List.replicate_append_replicate]
      congr 2; omega

theorem Encodes.comp {f g : Writer → Writer} {l l' : List Bool} (hf : Encodes f l) (hg : Encodes g l') :
    Encodes (fun w => g (f w)) (l ++ l') := by
  intro w; simp [hg (f w), hf w]

theorem Encodes.foldl {β : Type} (step : Writer → β → Writer) (ser : β → List Bool)
    (h : ∀ x, Encodes (step · x) (ser x)) (xs : List β) :
    Encodes (fun w => xs.foldl step w) (xs.flatMap ser) := by
  induction xs with
  | nil => intro w; simp
  | cons x xs ih => intro w; simp [ih (step w x), h x w]

/-! ## Parser -/

namespace Decodes

variable {α β : Type}

theorem pure (a : α) : Decodes (Pure.pure a : Parser α) [] a := by
  intro d pos t _; rfl

theorem bind {p : Parser α} {f : α → Parser β} {l l' : List Bool} {a : α} {b : β}
    (hp : Decodes p l a) (hf : Decodes (f a) l' b) : Decodes (p >>= f) (l ++ l') b := by
  intro d pos t h
  have e := hp d pos (l' ++ t) (by simp [h])
  have e' := hf d (pos + l.length) t (by rw [← List.drop_drop, h, List.append_assoc, List.drop_left])
  show Parser.bind p f d pos = _
  simp only [Parser.bind, e, e', List.length_append, Nat.add_assoc]

theorem bind' {p : Parser α} {f : α → Parser β} {l l' l'' : List Bool} {a : α} {b : β}
    (hp : Decodes p l a) (hf : Decodes (f a) l' b) (hl : l'' = l ++ l') : Decodes (p >>= f) l'' b :=
  hl ▸ bind hp hf

theorem check {c : Bool} (msg : String) (h : c = true) : Decodes (Parser.check c msg) [] () := by
  subst h; exact pure ()

theorem drop_cons {l : List Bool} {p : Nat} {b : Bool} {r : List Bool} (h : l.drop p = b :: r) :
    ∃ hp : p < l.length, l[p] = b ∧ l.drop (p + 1) = r := by
  have hp : p < l.length := by
    have := congrArg List.length h; simp at this; omega
  rw [List.drop_eq_getElem_cons hp] at h
  obtain ⟨h1, h2⟩ := List.cons.inj h
  exact ⟨hp, h1, h2⟩

theorem readBitsAux_eq (d : ByteArray) (k v acc pos : Nat) (t : List Bool)
    (h : (bitsOf d).drop pos = natBits k v ++ t) :
    Parser.readBitsAux d k acc pos = .ok (acc * 2 ^ k + v % 2 ^ k, pos + k) := by
  induction k generalizing acc pos with
  | zero => simp [Parser.readBitsAux, Nat.mod_one]
  | succ k ih =>
    obtain ⟨hp, hb, hr⟩ := drop_cons (l := bitsOf d) (h.trans rfl)
    obtain ⟨h8, hbit⟩ := getElem_bitsOf d pos hp
    simp only [Parser.readBitsAux, h8, dite_true]
    rw [ih _ _ hr]
    have : Parser.bitAt d pos h8 = v / 2 ^ k % 2 := by
      have hb' := hb
      rw [hbit] at hb'
      unfold Parser.bitAt
      simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow] at hb' ⊢
      have h1 := Nat.mod_two_eq_zero_or_one (d[pos / 8].toNat / 2 ^ (7 - pos % 8))
      have h2 := Nat.mod_two_eq_zero_or_one (v / 2 ^ k)
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all
    rw [this, Nat.mod_pow_succ, Nat.pow_succ]
    congr 1
    generalize 2 ^ k = P; generalize v / P % 2 = b; generalize v % P = r
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm P 2, Nat.mul_comm P b, Nat.mul_left_comm 2 acc P]
    exact Prod.ext (by simp only; omega) (by simp only; omega)

theorem readBits (k v : Nat) (h : v < 2 ^ k) : Decodes (Parser.readBits k) (natBits k v) v := by
  intro d pos t e
  simp [Parser.readBits, readBitsAux_eq d k v 0 pos t e, Nat.mod_eq_of_lt h]

end Decodes

end VeriCut

namespace VeriCut

/-- `f` writes some bits that `p` reads back as `a`, whatever follows. -/
def RoundTrip {α : Type} (f : Writer → Writer) (p : Parser α) (a : α) : Prop :=
  ∃ l, Encodes f l ∧ Decodes p l a

namespace RoundTrip

variable {α β : Type}

theorem pure (a : α) : RoundTrip id (Pure.pure a : Parser α) a :=
  ⟨[], fun w => by simp, Decodes.pure a⟩

theorem bind {f g : Writer → Writer} {p : Parser α} {q : α → Parser β} {a : α} {b : β}
    (hp : RoundTrip f p a) (hq : RoundTrip g (q a) b) : RoundTrip (fun w => g (f w)) (p >>= q) b := by
  obtain ⟨l, ef, dp⟩ := hp
  obtain ⟨l', eg, dq⟩ := hq
  exact ⟨l ++ l', ef.comp eg, dp.bind dq⟩

/-- Like `bind`, when the parser's continuation ignores the value. -/
theorem seq {f g : Writer → Writer} {p : Parser α} {q : Parser β} {a : α} {b : β}
    (hp : RoundTrip f p a) (hq : RoundTrip g q b) : RoundTrip (fun w => g (f w)) (p >>= fun _ => q) b :=
  bind hp hq

/-- `bind`, stated for `refine` on a goal: the writer is matched last. -/
theorem bind' {f g h : Writer → Writer} {p : Parser α} {q : α → Parser β} {a : α} {b : β}
    (hp : RoundTrip f p a) (hq : RoundTrip g (q a) b) (hh : ∀ w, h w = g (f w)) : RoundTrip h (p >>= q) b := by
  obtain ⟨l, ef, dp⟩ := hp
  obtain ⟨l', eg, dq⟩ := hq
  exact ⟨l ++ l', fun w => by rw [hh]; exact (ef.comp eg) w, dp.bind dq⟩

theorem pure' {a b : α} (ha : a = b) : RoundTrip id (Pure.pure a : Parser α) b :=
  ⟨[], fun w => by simp, ha ▸ Decodes.pure a⟩

theorem write_zero {a : α} (v : Nat) : RoundTrip (·.write 0 v) (Pure.pure a : Parser α) a :=
  ⟨[], fun w => by simp [write_bits], Decodes.pure a⟩

theorem val {f : Writer → Writer} {p : Parser α} {a b : α} (h : RoundTrip f p a) (ha : a = b) :
    RoundTrip f p b := ha ▸ h

theorem congr {f g : Writer → Writer} {p q : Parser α} {a b : α}
    (h : RoundTrip f p a) (hf : ∀ w, f w = g w) (hp : p = q) (ha : a = b) : RoundTrip g q b := by
  obtain ⟨l, e, d⟩ := h
  subst hp ha
  exact ⟨l, fun w => by rw [← hf]; exact e w, d⟩

theorem check {c : Bool} (msg : String) (h : c = true) : RoundTrip id (Parser.check c msg) () :=
  ⟨[], fun w => by simp, Decodes.check msg h⟩

theorem readBits (k v : Nat) (h : v < 2 ^ k) : RoundTrip (·.write k v) (Parser.readBits k) v :=
  ⟨_, encodes_write k v, Decodes.readBits k v h⟩

theorem signed_value (k : Nat) (v : Int) (h : -2 ^ (k - 1) ≤ v ∧ v < 2 ^ (k - 1)) (hk : 0 < k) :
    (v % 2 ^ k).toNat < 2 ^ k ∧
    (if 2 * (v % 2 ^ k).toNat < 2 ^ k then (((v % 2 ^ k).toNat : Nat) : Int)
      else (((v % 2 ^ k).toNat : Nat) : Int) - 2 ^ k) = v := by
  have hc : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by push_cast; rfl
  have hc' : ((2 ^ (k - 1) : Nat) : Int) = (2 : Int) ^ (k - 1) := by push_cast; rfl
  have hk2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp [Nat.pow_succ]; omega
  have hpos : (0 : Int) < 2 ^ k := by rw [← hc]; exact_mod_cast Nat.two_pow_pos k
  have h1 := Int.emod_lt_of_pos v hpos
  have h2 := Int.emod_nonneg v (by omega : (2 : Int) ^ k ≠ 0)
  have h3 : v % 2 ^ k = if 0 ≤ v then v else v + 2 ^ k := by
    split
    · exact Int.emod_eq_of_lt (by assumption) (by rw [← hc]; omega)
    · rw [← Int.add_emod_right]; exact Int.emod_eq_of_lt (by omega) (by rw [← hc]; omega)
  rw [← hc] at h1 h3 ⊢
  rw [← hc'] at h
  refine ⟨by omega, ?_⟩
  split <;> split at h3 <;> omega

theorem readSigned (k : Nat) (v : Int) (h : -2 ^ (k - 1) ≤ v ∧ v < 2 ^ (k - 1)) (hk : 0 < k) :
    RoundTrip (·.writeSigned k v) (Parser.readSigned k) v :=
  have ⟨hlt, e⟩ := signed_value k v h hk
  congr (bind (readBits k _ hlt) (pure _)) (fun _ => rfl) rfl e

/-- Writing each element of `xs` in turn, then reading as many. -/
theorem many {step : Writer → β → Writer} {p : Parser β} {xs : List β}
    (h : ∀ x ∈ xs, RoundTrip (step · x) p x) (acc : Array β) :
    RoundTrip (fun w => xs.foldl step w) (Parser.many p xs.length acc) (acc ++ xs.toArray) := by
  induction xs generalizing acc with
  | nil => exact congr (pure acc) (fun _ => rfl) rfl (by simp)
  | cons x xs ih =>
    have hx := h x (by simp)
    have := bind (q := fun a => Parser.many p xs.length (acc.push a)) hx
      (ih (fun y hy => h y (by simp [hy])) (acc.push x))
    exact congr this (fun _ => rfl) rfl (by simp)

theorem many' {step : Writer → β → Writer} {p : Parser β} {xs : List β} {count : Nat}
    (h : ∀ x ∈ xs, RoundTrip (step · x) p x) (acc : Array β) (hc : count = xs.length) :
    RoundTrip (fun w => xs.foldl step w) (Parser.many p count acc) (acc ++ xs.toArray) :=
  hc ▸ many h acc

end RoundTrip

/-- Close the writer equations `rt` left that hold by definition, innermost first. -/
macro "rt_rfl" : tactic => `(tactic| all_goals try (intro w; rfl))

/-- `rt h`: the parser is `p >>= q` with `h : RoundTrip f p a`. Leaves the round trip of `q a`,
then the writer equation. -/
macro "rt " h:term : tactic =>
  `(tactic| apply RoundTrip.bind' $h)

end VeriCut
