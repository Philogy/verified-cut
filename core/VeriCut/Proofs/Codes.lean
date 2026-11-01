import VeriCut.Proofs.Bits
import VeriCut.Flac.Codes
import VeriCut.Flac.Parse
import VeriCut.Flac.Write

/-! Round trips of the small codes: unary, Rice, frame numbers, table codes. -/

namespace VeriCut.Flac

open Parser

theorem unaryAux_eq (d : ByteArray) (q acc pos : Nat) (t : List Bool)
    (h : (bitsOf d).drop pos = List.replicate q false ++ true :: t) :
    unaryAux d pos acc = .ok (acc + q, pos + q + 1) := by
  induction q generalizing acc pos with
  | zero =>
    obtain ⟨hp, hb, _⟩ := Decodes.drop_cons h
    obtain ⟨h8, hbit⟩ := getElem_bitsOf d pos hp
    unfold unaryAux
    have : bitAt d pos h8 = 1 := by
      rw [hbit] at hb; unfold bitAt
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow] at *
      simpa using hb
    simp [h8, this]
  | succ q ih =>
    obtain ⟨hp, hb, hr⟩ := Decodes.drop_cons (by simpa [List.replicate_succ] using h)
    obtain ⟨h8, hbit⟩ := getElem_bitsOf d pos hp
    unfold unaryAux
    have : bitAt d pos h8 ≠ 1 := by
      rw [hbit] at hb; unfold bitAt
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow] at *
      simp at hb; omega
    simp only [h8, dite_true, this, if_false]
    rw [ih _ _ hr]; congr 2 <;> omega

/-! ## The allocation-free Rice reader -/

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
        simp only [pure, Parser.pure, Nat.zero_add]
        exact ih _ _
      · rw [if_neg h2, if_neg h2]
    · rw [if_neg h1, if_neg h1]

theorem ricesP_eq (k c : Nat) (acc : Array Int) : ricesP k c acc = many (riceP k) c acc := by
  funext d p; exact ricesLoop_eq d k c acc p

theorem roundTrip_unary (q : Nat) : RoundTrip (fun w => (w.zeros q).write 1 1) unary q := by
  refine ⟨List.replicate q false ++ [true], fun w => by simp [write_bits, zeros_bits, natBits], ?_⟩
  intro d pos t h
  simp only [List.append_assoc, List.singleton_append] at h
  simp [unary, unaryAux_eq d q 0 pos t h]; omega

theorem unzigzag_zigzag (v : Int) : unzigzag (zigzag v) = v := by
  unfold zigzag unzigzag
  split <;> split <;> omega

theorem natBits_one (q : Nat) : natBits (q + 1) 1 = List.replicate q false ++ [true] := by
  rw [natBits_add, show 1 / 2 ^ 1 = 0 by rfl, natBits_zero_eq_replicate]
  rfl

theorem writeRice_bits (k : Nat) (w : Writer) (v : Int) :
    (writeRice k w v).bits = ((((w.zeros (zigzag v >>> k)).write 1 1).write k (zigzag v % 2 ^ k))).bits := by
  unfold writeRice
  simp only [write_bits, zeros_bits, natBits_mod _ _ _ (Nat.le_refl _), List.append_assoc]
  split
  · rename_i hq
    have hk : k ≤ 55 := by generalize zigzag v >>> k = q at hq; omega
    have hlow := toNat_low (zigzag v) k (by omega)
    have hp : (2 : Nat) ^ k < 2 ^ 63 := Nat.pow_lt_pow_right (by decide) (by omega)
    have h1 : ((1 : UInt64) <<< k.toUInt64).toNat = 2 ^ k := by
      have hk' : (k.toUInt64).toNat = k := by
        rw [Nat.toUInt64, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
      rw [UInt64.toNat_shiftLeft, hk', Nat.mod_eq_of_lt (by omega : k < 64)]
      have hp' : (2 : Nat) ^ k < 2 ^ 64 := Nat.lt_trans hp (by decide)
      simp [Nat.one_shiftLeft, Nat.mod_eq_of_lt hp']
    have hm : (((zigzag v).toUInt64 &&& ((1 : UInt64) <<< k.toUInt64 - 1)) + (1 : UInt64) <<< k.toUInt64).toNat =
        2 ^ k + zigzag v % 2 ^ k := by
      rw [UInt64.toNat_add, hlow, h1, Nat.mod_eq_of_lt (by have := Nat.mod_lt (zigzag v) (Nat.two_pow_pos k); omega)]
      omega
    rw [write_bits, hm]
    have e := natBits_mul_add (zigzag v >>> k + 1) k 1 (zigzag v % 2 ^ k) (Nat.mod_lt _ (Nat.two_pow_pos k))
    rw [Nat.one_mul] at e
    rw [e, natBits_one, natBits_mod _ _ _ (Nat.le_refl _)]
    simp [natBits]
  · simp [zeros_bits, write_bits]

theorem roundTrip_rice (k : Nat) (v : Int) : RoundTrip (writeRice k · v) (riceP k) v := by
  refine RoundTrip.congrBits ?_ (fun w => (writeRice_bits k w v).symm)
  rt roundTrip_unary (zigzag v >>> k)
  rt RoundTrip.readBits k (zigzag v % 2 ^ k) (Nat.mod_lt _ (Nat.two_pow_pos k))
  · refine RoundTrip.pure' ?_
    rw [pow2_eq, Nat.shiftRight_eq_div_pow, Nat.mul_comm, Nat.div_add_mod, unzigzag_zigzag]
  · intro w; rfl
  · intro w; rfl

/-! ## Frame numbers -/

theorem roundTrip_continuation (m v i : Nat) :
    RoundTrip (fun w => ((digits64 m i).map (128 + ·)).foldl (·.write 8 ·) w)
      (continuationP m v) (v * 64 ^ m + i % 64 ^ m) := by
  induction m generalizing v with
  | zero => exact RoundTrip.val (RoundTrip.pure' rfl) (by simp [Nat.mod_one])
  | succ m ih =>
    have hb : 128 + i / 64 ^ m % 64 < 2 ^ 8 := by have := Nat.mod_lt (i / 64 ^ m) (by omega : 64 > 0); omega
    rt RoundTrip.readBits 8 _ hb
    · refine RoundTrip.val (ih (64 * v + (128 + i / 64 ^ m % 64) % 64)) ?_
      have : (128 + i / 64 ^ m % 64) % 64 = i / 64 ^ m % 64 := by omega
      rw [this, Nat.mod_pow_succ, Nat.pow_succ]
      generalize 64 ^ m = P; generalize i / P % 64 = a; generalize i % P = r
      rw [Nat.add_mul, Nat.mul_comm 64 v, Nat.mul_assoc, Nat.mul_comm 64 P, Nat.mul_comm a P]; omega
    · intro w; rfl

theorem codedLength_eq_one (i : Nat) : codedLength i = 1 ↔ i < 2 ^ 7 := by
  unfold codedLength
  constructor
  · repeat' split
    all_goals intro h; first | assumption | (exfalso; omega) | simp at h
  · intro h; simp [h]

theorem codedLength_ge_two (i : Nat) (h : codedLength i ≠ 1) : 2 ≤ codedLength i := by
  revert h; unfold codedLength; repeat' split
  all_goals intro h; omega

theorem codedRest_lead (i : Nat) (h : i < 2 ^ 36) : ∀ n, codedLength i = n → 2 ≤ n →
      (256 - 2 ^ (8 - n) + i / 64 ^ (n - 1) < 2 ^ 8 ∧
        codedRest (256 - 2 ^ (8 - n) + i / 64 ^ (n - 1)) = some (n - 1, i / 64 ^ (n - 1))) := by
  intro n hn h2
  unfold codedLength at hn
  repeat' split at hn
  all_goals subst hn
  all_goals simp only [Nat.reducePow, Nat.reduceSub] at *
  all_goals first | (exfalso; omega) | skip
  all_goals refine ⟨by omega, ?_⟩
  all_goals unfold codedRest
  all_goals repeat' split
  all_goals first | (exfalso; omega) | (simp only [Option.some.injEq, Prod.mk.injEq, true_and]; omega)

theorem roundTrip_codedNumber (i : Nat) (h : i < 2 ^ 36) :
    RoundTrip (fun w => (codedBytes i).foldl (·.write 8 ·) w) codedNumberP i := by
  unfold codedNumberP
  by_cases h1 : codedLength i = 1
  · have hi : i < 2 ^ 7 := (codedLength_eq_one i).1 h1
    rt RoundTrip.readBits 8 i (by omega)
    · have : codedRest i = some (0, i) := by unfold codedRest; simp; omega
      rw [this]; exact RoundTrip.pure' (by simp)
    · intro w; simp [codedBytes, h1]
  · have h2 : 2 ≤ codedLength i := codedLength_ge_two i h1
    obtain ⟨hb, hr⟩ := codedRest_lead i h _ rfl h2
    rt RoundTrip.readBits 8 _ hb
    · rw [hr]
      exact RoundTrip.val (roundTrip_continuation _ _ i) (by rw [Nat.mul_comm, Nat.div_add_mod])
    · intro w; simp [codedBytes, h1]

end VeriCut.Flac
