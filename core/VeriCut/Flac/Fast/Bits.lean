import VeriCut.Flac.Bits
import VeriCut.Flac.Crc

/-!
The bit layer, tuned for speed. `Proofs/Fast/Bits.lean` shows each piece agrees with the spec's
(`Flac/Bits.lean`, `Flac/Crc.lean`).

What made the spec slow: `Nat` powers and `Nat` shifts left go through GMP and allocate, even for
small numbers, and the spec's writer keeps its pending bits in a `Nat` reduced by `2 ^ k` on every
write.
-/

namespace VeriCut.Flac.Fast

/-- `2 ^ k`; for `k < 63` a `UInt64` shift. -/
@[inline] def pow2 (k : Nat) : Nat := if k < 63 then ((1 : UInt64) <<< k.toUInt64).toNat else 2 ^ k

/-- The bytes written so far, then the low `n` bits of `acc`, which don't fill a byte. -/
structure Writer where
  bytes : ByteArray
  acc : UInt64
  n : Nat
  n_lt : n < 8

namespace Writer

def empty : Writer := ⟨.empty, 0, 0, by decide⟩

/-- Move the whole bytes of the `n ≤ 64` pending bits `acc` (its low `n`) to `bytes`. -/
def flush (bytes : ByteArray) (acc : UInt64) (n : Nat) (h : n ≤ 64) : Writer :=
  if h8 : 8 ≤ n then flush (bytes.push (acc >>> (n - 8).toUInt64).toUInt8) acc (n - 8) (by omega)
  else ⟨bytes, acc, n, by omega⟩
termination_by n
decreasing_by omega

/-- Append the low `k ≤ 56` bits of `v`, through the 64-bit buffer at once. -/
@[inline] def writeFast (w : Writer) (k v : Nat) (h : k ≤ 56) : Writer :=
  let low := v.toUInt64 &&& ((1 <<< k.toUInt64) - 1)
  flush w.bytes ((w.acc <<< k.toUInt64) + low) (w.n + k) (by have := w.n_lt; omega)

/-- Append the low `k` bits of `v` one at a time. -/
def writeBits (w : Writer) : Nat → Nat → Writer
  | 0, _ => w
  | k + 1, v => (writeBits w k (v >>> 1)).writeFast 1 v (by decide)

/-- Append the low `k` bits of `v`. -/
def write (w : Writer) (k v : Nat) : Writer :=
  if h : k ≤ 56 then w.writeFast k v h else w.writeBits k v

/-- Append `k` zero bits. -/
def zeros (w : Writer) (k : Nat) : Writer :=
  if k ≤ 32 then w.write k 0 else (w.write 32 0).zeros (k - 32)
termination_by k
decreasing_by omega

/-- Two's complement in `k` bits. -/
def writeSigned (w : Writer) (k : Nat) (v : Int) : Writer :=
  w.write k (v % (pow2 k : Int)).toNat

/-- Pad with zeros to a byte boundary. -/
def align (w : Writer) : Writer :=
  w.write ((8 - w.n % 8) % 8) 0

end Writer

open Parser

/-- `Parser.readSigned`. -/
def readSigned (k : Nat) : Parser Int := do
  let u ← readBits k
  let m := pow2 k
  pure (if 2 * u < m then (u : Int) else (u : Int) - m)

/-- The first position from `p` on holding a one bit, or `8 * d.size` if there is none:
`unaryAux` as a plain number, so nothing is allocated. -/
def nextOne (d : ByteArray) (p : Nat) : Nat :=
  if h : p / 8 < d.size then
    if bitAt d p h = 1 then p else nextOne d (p + 1)
  else 8 * d.size
termination_by 8 * d.size - p
decreasing_by omega

/-- The `k` bits from `p` as a number after `acc` (bits past the end read as zero): the value
of `readBitsAux`. -/
def bitsVal (d : ByteArray) : Nat → Nat → Nat → Nat
  | 0, acc, _ => acc
  | k + 1, acc, p =>
    if h : p / 8 < d.size then bitsVal d k (2 * acc + bitAt d p h) (p + 1) else bitsVal d k (2 * acc) (p + 1)

/-- `crc16` without `Nat` shifts left. -/
def crc16 (d : ByteArray) : Nat :=
  d.foldl (fun c b => (c * 256 % 65536) ^^^ crc16Table[(c >>> 8) ^^^ b.toNat]!) 0 % 65536

end VeriCut.Flac.Fast
