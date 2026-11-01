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

theorem roundTrip_unary (q : Nat) : RoundTrip (fun w => (w.zeros q).write 1 1) unary q := by
  refine ⟨List.replicate q false ++ [true], fun w => by simp [write_bits, zeros_bits, natBits], ?_⟩
  intro d pos t h
  simp only [List.append_assoc, List.singleton_append] at h
  simp [unary, unaryAux_eq d q 0 pos t h]; omega

theorem unzigzag_zigzag (v : Int) : unzigzag (zigzag v) = v := by
  unfold zigzag unzigzag
  split <;> split <;> omega

theorem write_mod (w : Writer) (k v : Nat) : w.write k (v % 2 ^ k) = w.write k v := by
  simp [Writer.write]

theorem roundTrip_rice (k : Nat) (v : Int) : RoundTrip (writeRice k · v) (riceP k) v := by
  rt roundTrip_unary (zigzag v >>> k)
  rt RoundTrip.readBits k (zigzag v % 2 ^ k) (Nat.mod_lt _ (Nat.two_pow_pos k))
  · refine RoundTrip.pure' ?_
    rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm, Nat.div_add_mod, unzigzag_zigzag]
  · intro w; rfl
  · intro w; simp only [writeRice, write_mod, id]

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
