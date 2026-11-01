import Lossy.Reader

namespace Lossy

@[simp] theorem length_bitsOf (k n : Nat) : (bitsOf k n).length = k := by
  induction k <;> simp [bitsOf, *]

theorem At.cons_iff {a : ByteArray} {pos : Nat} {b : Bool} {l : List Bool} :
    At a pos (b :: l) ↔ bitAt a pos = b ∧ At a (pos + 1) l := by
  constructor
  · rintro ⟨hlen, h⟩
    refine ⟨h 0 (by simp), by simp at hlen; omega, fun i hi => ?_⟩
    have := h (i + 1) (by simp; omega)
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
  · rintro ⟨h0, hlen, h⟩
    refine ⟨by simp; omega, fun i hi => ?_⟩
    cases i with
    | zero => simpa using h0
    | succ i =>
      have := h i (by simp at hi; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem At.append_iff {a : ByteArray} {pos : Nat} {l₁ l₂ : List Bool} :
    At a pos (l₁ ++ l₂) ↔ At a pos l₁ ∧ At a (pos + l₁.length) l₂ := by
  induction l₁ generalizing pos with
  | nil => simp only [At, List.nil_append, List.length_nil]; constructor <;> intro h <;> simp_all <;> omega
  | cons b l ih =>
    simp only [List.cons_append, At.cons_iff, ih, List.length_cons]
    constructor
    · rintro ⟨h0, h1, h2⟩; exact ⟨⟨h0, h1⟩, by simpa [Nat.add_assoc, Nat.add_comm 1] using h2⟩
    · rintro ⟨⟨h0, h1⟩, h2⟩; exact ⟨h0, h1, by simpa [Nat.add_assoc, Nat.add_comm 1] using h2⟩

theorem At.nil_iff {a : ByteArray} {pos : Nat} : At a pos [] ↔ pos ≤ 8 * a.size := by
  simp [At]

theorem natAt_bitsOf {a : ByteArray} {pos k n : Nat} (h : At a pos (bitsOf k n)) :
    Reader.natAt a pos k = n % 2 ^ k := by
  induction k generalizing pos with
  | zero => simp [Reader.natAt, Nat.mod_one]
  | succ k ih =>
    rw [bitsOf, At.cons_iff] at h
    rw [Reader.natAt, h.1, ih h.2, Nat.mod_pow_succ, Nat.toNat_testBit]
    rw [Nat.add_comm, Nat.mul_comm]

/-! `Parses p v l`: on any input whose bits at the current position start
with `l`, `p` returns `v` and moves past `l`. -/

def Parses (p : Reader α) (v : α) (l : List Bool) : Prop :=
  ∀ a pos, At a pos l → p.run a pos = some (v, pos + l.length)

namespace Parses

theorem pure (v : α) : Parses (Pure.pure v : Reader α) v [] := by
  intro a pos _; simp [Pure.pure]

theorem bind {p : Reader α} {f : α → Reader β} {v : α} {w : β} {l₁ l₂ : List Bool}
    (h₁ : Parses p v l₁) (h₂ : Parses (f v) w l₂) : Parses (p >>= f) w (l₁ ++ l₂) := by
  intro a pos h
  rw [At.append_iff] at h
  show (match p.run a pos with | some (v, pos') => (f v).run a pos' | none => none) = _
  rw [h₁ a pos h.1]
  simp only
  rw [h₂ a _ h.2]
  simp [Nat.add_assoc]

theorem congr {p : Reader α} {v w : α} {l l' : List Bool} (h : Parses p v l) (hv : v = w)
    (hl : l = l') : Parses p w l' := hv ▸ hl ▸ h

theorem map {p : Reader α} {v : α} {l : List Bool} (g : α → β) (h : Parses p v l) :
    Parses (p >>= fun x => Pure.pure (g x)) (g v) l :=
  (bind h (pure (g v))).congr rfl (by simp)

theorem nat (k n : Nat) : Parses (Reader.nat k) (n % 2 ^ k) (bitsOf k n) := by
  intro a pos h
  simp only [Reader.nat, length_bitsOf]
  rw [if_pos (by have := h.1; simpa using this), natAt_bitsOf h]

theorem nat_lt {k n : Nat} (hn : n < 2 ^ k) : Parses (Reader.nat k) n (bitsOf k n) :=
  (nat k n).congr (Nat.mod_eq_of_lt hn) rfl

theorem expect {k n : Nat} (hn : n < 2 ^ k) : Parses (Reader.expect k n) () (bitsOf k n) := by
  have h₂ : Parses ((fun m => if m = n then Pure.pure () else Reader.fail) n) () [] := by
    simpa using pure ()
  exact (bind (nat_lt hn) h₂).congr rfl (by simp)

theorem bit (b : Bool) : Parses Reader.bit b [b] := by
  have := map (fun m => m == 1) (nat_lt (k := 1) (n := b.toNat) (by cases b <;> decide))
  cases b <;> exact this.congr (by decide) (by decide)

theorem int {k : Nat} {v : Int} (hk : 1 ≤ k) (lo : -2 ^ (k - 1) ≤ v) (hi : v < 2 ^ (k - 1)) :
    Parses (Reader.int k) v (bitsInt k v) := by
  have hpow : (2 : Int) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← Int.pow_succ']; congr 1; omega
  have hm : 0 ≤ v % 2 ^ k := Int.emod_nonneg _ (by omega)
  have hm' : v % 2 ^ k < 2 ^ k := Int.emod_lt_of_pos _ (by omega)
  have hlt : (v % 2 ^ k).toNat < 2 ^ k := by
    have : ((v % 2 ^ k).toNat : Int) < ((2 ^ k : Nat) : Int) := by
      rw [Int.toNat_of_nonneg hm]; simpa using hm'
    exact_mod_cast this
  have h := map (fun n : Nat => if n < 2 ^ (k - 1) then (n : Int) else (n : Int) - 2 ^ k)
    (nat_lt hlt)
  refine h.congr ?_ rfl
  by_cases hv : 0 ≤ v
  · have e : v % 2 ^ k = v := Int.emod_eq_of_lt hv (by omega)
    have : v.toNat < 2 ^ (k - 1) := by
      have : (v.toNat : Int) < ((2 ^ (k - 1) : Nat) : Int) := by simp; omega
      exact_mod_cast this
    simp only [e, if_pos this]; omega
  · have hv : v < 0 := by omega
    have e : v % 2 ^ k = v + 2 ^ k := by
      rw [← Int.emod_eq_of_lt (a := v + 2 ^ k) (b := 2 ^ k) (by omega) (by omega)]
      simp
    have : ¬ (v + 2 ^ k).toNat < 2 ^ (k - 1) := by
      intro c
      have : ((v + 2 ^ k).toNat : Int) < ((2 ^ (k - 1) : Nat) : Int) := by exact_mod_cast c
      simp at this; omega
    simp only [e, if_neg this]; omega

theorem zerosFrom {a : ByteArray} {pos n m : Nat} (h : At a pos (Lossy.unary m)) :
    Reader.zerosFrom a pos n = some (n + m, pos + m + 1) := by
  induction m generalizing pos n with
  | zero =>
    simp [Lossy.unary, zeros, At.cons_iff, At.nil_iff] at h
    rw [Reader.zerosFrom, if_pos (by omega), if_pos h.1]; simp
  | succ m ih =>
    simp only [Lossy.unary, zeros, List.replicate_succ, List.cons_append, At.cons_iff] at h
    have hlt : pos < 8 * a.size := by have := h.2.1; simp at this; omega
    rw [Reader.zerosFrom, if_pos hlt, h.1]
    simp only [Bool.false_eq_true, ite_false]
    rw [ih h.2]; congr 2 <;> omega

theorem unary (m : Nat) : Parses Reader.unary m (Lossy.unary m) := by
  intro a pos h
  show Reader.zerosFrom a pos 0 = _
  rw [zerosFrom h]
  simp [Lossy.unary, zeros]; omega

theorem unzig_zig (r : Int) : unzig (zig r) = r := by
  unfold zig unzig; split <;> split <;> omega

theorem rice (k : Nat) (r : Int) : Parses (Reader.rice k) r (Lossy.rice k r) := by
  have h := bind (unary (zig r / 2 ^ k)) (f := fun q => do
      let m ← Reader.nat k; Pure.pure (unzig (q * 2 ^ k + m)))
    (map (fun m => unzig (zig r / 2 ^ k * 2 ^ k + m)) (nat k (zig r)))
  refine h.congr ?_ rfl
  rw [Nat.mul_comm, Nat.div_add_mod]; exact unzig_zig r

theorem many {p : Reader α} {ser : α → List Bool} :
    ∀ (vs : List α), (∀ v ∈ vs, Parses p v (ser v)) →
      Parses (Reader.many p vs.length) vs (vs.flatMap ser)
  | [], _ => pure []
  | v :: vs, h => by
    have := bind (h v (by simp)) (f := fun v => do
        let vs ← Reader.many p vs.length; Pure.pure (v :: vs))
      (map (fun vs => v :: vs) (many vs fun w hw => h w (by simp [hw])))
    exact this.congr rfl (by simp)

end Parses
end Lossy
