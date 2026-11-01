import Lossy.Proofs.Pack
import Lossy.Flac.Decode

namespace Lossy.Flac
open Reader

/-- `v` fits in `width` bits, two's complement. -/
def Fits (width : Nat) (v : Int) : Prop := -2 ^ (width - 1) ≤ v ∧ v < 2 ^ (width - 1)

/-- A subframe `readBody width n` can read back. -/
def Sub.Ok (width n : Nat) : Sub → Prop
  | .const v => Fits width v
  | .verbatim vs => vs.length = n ∧ ∀ v ∈ vs, Fits width v
  | .fixed o warm k res =>
    o ≤ 4 ∧ warm.length = o ∧ (∀ v ∈ warm, Fits width v) ∧ k < 15 ∧ res.length = n - o

theorem readBody_ok {width n : Nat} {s : Sub} (hw : 1 ≤ width) (hs : s.Ok width n) :
    Parses (readBody width n s.type) s (s.body width) := by
  cases s with
  | const v =>
    simp only [readBody, Sub.type, Sub.body, ↓reduceIte]
    exact Parses.map Sub.const (Parses.int hw hs.1 hs.2)
  | verbatim vs =>
    obtain ⟨rfl, h⟩ := hs
    simp only [readBody, Sub.type, Sub.body, ↓reduceIte, Nat.one_ne_zero]
    exact Parses.map Sub.verbatim (Parses.many vs fun v hv => Parses.int hw (h v hv).1 (h v hv).2)
  | fixed o warm k res =>
    obtain ⟨ho, rfl, hwarm, hk, hres⟩ := hs
    have c1 : ¬ 8 + warm.length = 0 := by omega
    have c2 : ¬ 8 + warm.length = 1 := by omega
    have c3 : 8 ≤ 8 + warm.length ∧ 8 + warm.length ≤ 12 := by omega
    simp only [readBody, Sub.type, Sub.body, if_neg c1, if_neg c2, if_pos c3,
      Nat.add_sub_cancel_left, List.append_assoc, ← hres]
    refine (Parses.many warm fun v hv => Parses.int hw (hwarm v hv).1 (hwarm v hv).2).bind ?_
    refine (Parses.expect (k := 2) (n := 0) (by decide)).bind ?_
    refine (Parses.expect (k := 4) (n := 0) (by decide)).bind ?_
    refine (Parses.nat_lt (k := 4) (n := k) (by omega)).bind ?_
    simp only [if_neg (show ¬ k = 15 by omega)]
    exact Parses.map _ (Parses.many res fun r _ => Parses.rice k r)

theorem readWasted_ok (w : Nat) : Parses readWasted w (wastedBits w) := by
  cases w with
  | zero =>
    refine ((Parses.bit false).bind (f := fun b => if b then do return (← Reader.unary) + 1
      else Pure.pure 0) (Parses.pure 0)).congr rfl ?_
    simp [wastedBits]
  | succ w =>
    exact ((Parses.bit true).bind (f := fun b => if b then do return (← Reader.unary) + 1
      else Pure.pure 0) (Parses.map (· + 1) (Parses.unary w))).congr rfl (by simp [wastedBits])

theorem Sub.type_lt (s : Sub) (hs : s.Ok width n) : s.type < 2 ^ 6 := by
  cases s <;> simp [Sub.type, Sub.Ok] at * <;> omega

theorem readSub_ok {bps n w : Nat} {s : Sub} (hw : w < bps) (hs : s.Ok (bps - w) n) :
    Parses (readSub bps n) (w, s) (subframeBits bps (w, s)) := by
  simp only [readSub, subframeBits, List.append_assoc]
  refine (Parses.expect (k := 1) (n := 0) (by decide)).bind ?_
  refine (Parses.nat_lt (k := 6) (s.type_lt hs)).bind ?_
  refine (readWasted_ok w).bind ?_
  exact Parses.map _ (readBody_ok (by omega) hs)

end Lossy.Flac
