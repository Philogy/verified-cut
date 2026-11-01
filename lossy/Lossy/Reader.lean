import Lossy.Bits

/-! A parser over the bits of a byte array. -/

namespace Lossy

/-- From a bit position, a value and the position after it. -/
structure Reader (α : Type) where
  run : ByteArray → Nat → Option (α × Nat)

namespace Reader

instance : Monad Reader where
  pure v := ⟨fun _ pos => some (v, pos)⟩
  bind p f := ⟨fun a pos => match p.run a pos with
    | some (v, pos') => (f v).run a pos'
    | none => none⟩

def fail : Reader α := ⟨fun _ _ => none⟩

/-- `k` bits from `pos` as a number. -/
def natAt (a : ByteArray) (pos : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (bitAt a pos).toNat * 2 ^ k + natAt a (pos + 1) k

def nat (k : Nat) : Reader Nat := ⟨fun a pos =>
  if pos + k ≤ 8 * a.size then some (natAt a pos k, pos + k) else none⟩

def bit : Reader Bool := do return (← nat 1) == 1

/-- Fails unless the next `k` bits are `v`. -/
def expect (k v : Nat) : Reader Unit := do
  if (← nat k) = v then pure () else fail

def int (k : Nat) : Reader Int := do
  let n ← nat k
  return if n < 2 ^ (k - 1) then (n : Int) else (n : Int) - 2 ^ k

def zerosFrom (a : ByteArray) (pos n : Nat) : Option (Nat × Nat) :=
  if pos < 8 * a.size then
    if bitAt a pos then some (n, pos + 1) else zerosFrom a (pos + 1) (n + 1)
  else none
termination_by 8 * a.size - pos

def unary : Reader Nat := ⟨fun a pos => zerosFrom a pos 0⟩

def rice (k : Nat) : Reader Int := do
  let q ← unary
  let r ← nat k
  return unzig (q * 2 ^ k + r)

def many (p : Reader α) : Nat → Reader (List α)
  | 0 => pure []
  | n + 1 => do
    let v ← p
    let vs ← many p n
    return v :: vs

/-- Skips to the next byte boundary. -/
def align : Reader Unit := ⟨fun a pos =>
  let p := (8 - pos % 8) % 8
  if pos + p ≤ 8 * a.size then some ((), pos + p) else none⟩

end Reader
end Lossy
