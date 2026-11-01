/-!
Bit strings, written as `List Bool` (most significant bit first) and read
back from a `ByteArray` by position.
-/

namespace Lossy

/-- `n mod 2^k` as `k` bits, most significant first. -/
def bitsOf : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, n => n.testBit k :: bitsOf k n

/-- `v` as a `k`-bit two's complement number. -/
def bitsInt (k : Nat) (v : Int) : List Bool := bitsOf k (v % 2 ^ k).toNat

def zeros (k : Nat) : List Bool := List.replicate k false

/-- `n` in unary: `n` zeros, then a one. -/
def unary (n : Nat) : List Bool := zeros n ++ [true]

/-- Folds signed into unsigned: 0, -1, 1, -2, ... become 0, 1, 2, 3, ... -/
def zig (r : Int) : Nat := if 0 ≤ r then 2 * r.toNat else 2 * (-r).toNat - 1

def unzig (u : Nat) : Int := if u % 2 = 0 then (u / 2 : Nat) else -((u / 2 : Nat) : Int) - 1

/-- Rice code with parameter `k`: quotient in unary, then the low `k` bits. -/
def rice (k : Nat) (r : Int) : List Bool := unary (zig r / 2 ^ k) ++ bitsOf k (zig r)

def byte (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : UInt8 :=
  (b0.toNat * 128 + b1.toNat * 64 + b2.toNat * 32 + b3.toNat * 16 +
    b4.toNat * 8 + b5.toNat * 4 + b6.toNat * 2 + b7.toNat).toUInt8

/-- Appends the bits to `out`, eight per byte. A trailing partial byte is
dropped; callers pad to whole bytes first. -/
def packInto (out : ByteArray) : List Bool → ByteArray
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    packInto (out.push (byte b0 b1 b2 b3 b4 b5 b6 b7)) rest
  | _ => out

/-- Bit `i` of `a`, counting from the most significant bit of byte 0. -/
def bitAt (a : ByteArray) (i : Nat) : Bool :=
  if h : i / 8 < a.data.size then a.data[i / 8].toNat.testBit (7 - i % 8) else false

/-- The bits of `a` from `pos` on start with `l`. -/
def At (a : ByteArray) (pos : Nat) (l : List Bool) : Prop :=
  pos + l.length ≤ 8 * a.size ∧ ∀ i (h : i < l.length), bitAt a (pos + i) = l[i]

/-- CRC, most significant bit first, initial value 0, of width `w`. -/
def crcBits (w poly : Nat) (l : List Bool) : Nat :=
  l.foldl (fun c b =>
    let top := c.testBit (w - 1) != b
    let c := (2 * c) % 2 ^ w
    if top then c ^^^ poly else c) 0

def crc8 : List Bool → Nat := crcBits 8 0x07
def crc16 : List Bool → Nat := crcBits 16 0x8005

end Lossy
