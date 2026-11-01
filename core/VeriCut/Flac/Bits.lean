/-!
Bit writer and bit reader, most significant bit first (FLAC's order).
-/

namespace VeriCut

/-- `2 ^ k`; for `k < 63` in `UInt64`, since `Nat` powers and shifts go through GMP. -/
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

/-- Reads `data` at bit position `pos`; returns the new position. -/
def Parser (α : Type) : Type := ByteArray → Nat → Except String (α × Nat)

namespace Parser

@[inline] protected def pure (a : α) : Parser α := fun _ p => .ok (a, p)

@[inline] protected def bind (m : Parser α) (f : α → Parser β) : Parser β := fun d p =>
  match m d p with
  | .ok (a, p) => f a d p
  | .error e => .error e

instance : Monad Parser where
  pure := Parser.pure
  bind := Parser.bind

def fail (msg : String) : Parser α := fun _ _ => .error msg

def check (ok : Bool) (msg : String) : Parser Unit :=
  if ok then pure () else fail msg

def pos : Parser Nat := fun _ p => .ok (p, p)

def data : Parser ByteArray := fun d p => .ok (d, p)

def atEnd : Parser Bool := fun d p => .ok (8 * d.size ≤ p, p)

@[inline] def bitAt (d : ByteArray) (p : Nat) (h : p / 8 < d.size) : Nat :=
  (d[p / 8].toNat >>> (7 - p % 8)) % 2

def readBitsAux (d : ByteArray) : Nat → Nat → Nat → Except String (Nat × Nat)
  | 0, acc, p => .ok (acc, p)
  | k + 1, acc, p =>
    if h : p / 8 < d.size then readBitsAux d k (2 * acc + bitAt d p h) (p + 1)
    else .error "unexpected end of stream"

/-- `k` bits as an unsigned number. -/
def readBits (k : Nat) : Parser Nat := fun d p => readBitsAux d k 0 p

/-- `k` bits as a two's complement number. -/
def readSigned (k : Nat) : Parser Int := do
  let u ← readBits k
  let m := pow2 k
  pure (if 2 * u < m then (u : Int) else (u : Int) - m)

def unaryAux (d : ByteArray) (p q : Nat) : Except String (Nat × Nat) :=
  if h : p / 8 < d.size then
    if bitAt d p h = 1 then .ok (q, p + 1) else unaryAux d (p + 1) (q + 1)
  else .error "unexpected end of stream"
termination_by 8 * d.size - p
decreasing_by omega

/-- The number of zero bits before the next one bit, which is consumed too. -/
def unary : Parser Nat := fun d p => unaryAux d p 0

def skip (k : Nat) : Parser Unit := fun d p =>
  if p + k ≤ 8 * d.size then .ok ((), p + k) else .error "unexpected end of stream"

/-- Skip to the next byte boundary. -/
def align : Parser Unit := fun d p => skip ((8 - p % 8) % 8) d p

/-- Run `p` `k` times, appending the results to `acc`. -/
def many (p : Parser α) : Nat → Array α → Parser (Array α)
  | 0, acc => pure acc
  | k + 1, acc => do let a ← p; many p k (acc.push a)

end Parser

end VeriCut
