/-!
MD5 (RFC 1321) of the decoded audio, for STREAMINFO: the samples interleaved, each as a
little-endian signed integer of `(bitsPerSample + 7) / 8` bytes, as libFLAC computes it.

Only metadata: decoders may check it, the round trip doesn't depend on it.
-/

namespace VeriCut.Flac.Md5

def shifts : Array UInt32 :=
  #[7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
    5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
    4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
    6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]

/-- `floor (2 ^ 32 * |sin (i + 1)|)`. -/
def table : Array UInt32 :=
  #[0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
    0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
    0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
    0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
    0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
    0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
    0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
    0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

structure State where
  a : UInt32 := 0x67452301
  b : UInt32 := 0xefcdab89
  c : UInt32 := 0x98badcfe
  d : UInt32 := 0x10325476

/-- Little-endian word `g` of the 64-byte block at `off`. -/
@[inline] def word (m : ByteArray) (off g : Nat) : UInt32 :=
  let i := off + 4 * g
  m[i]!.toUInt32 ||| (m[i + 1]!.toUInt32 <<< 8) ||| (m[i + 2]!.toUInt32 <<< 16) ||| (m[i + 3]!.toUInt32 <<< 24)

@[inline] def rotl (x s : UInt32) : UInt32 := (x <<< s) ||| (x >>> (32 - s))

/-- Rounds `i` to 63 on the block at `off`. -/
def rounds (m : ByteArray) (off : Nat) (i : Nat) (a b c d : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  if i < 64 then
    let (f, g) :=
      if i < 16 then ((b &&& c) ||| (~~~b &&& d), i)
      else if i < 32 then ((d &&& b) ||| (~~~d &&& c), (5 * i + 1) % 16)
      else if i < 48 then (b ^^^ c ^^^ d, (3 * i + 5) % 16)
      else (c ^^^ (b ||| ~~~d), (7 * i) % 16)
    let f := f + a + table[i]! + word m off g
    rounds m off (i + 1) d (b + rotl f shifts[i]!) b c
  else (a, b, c, d)
termination_by 64 - i

def block (st : State) (m : ByteArray) (off : Nat) : State :=
  let (a, b, c, d) := rounds m off 0 st.a st.b st.c st.d
  ⟨st.a + a, st.b + b, st.c + c, st.d + d⟩

/-- Hash the whole blocks of `m`; the rest (under 64 bytes) is returned. -/
def blocks (st : State) (m : ByteArray) : State × ByteArray := Id.run do
  let mut st := st
  let n := m.size / 64
  for k in [0:n] do st := block st m (64 * k)
  return (st, m.extract (64 * n) m.size)

/-- Pad the last `tail` bytes of a `len`-byte message and hash them; the digest as a 128-bit
number, first byte most significant. -/
def finish (st : State) (tail : ByteArray) (len : Nat) : Nat := Id.run do
  let mut m := tail.push 0x80
  while m.size % 64 ≠ 56 do m := m.push 0
  let bits := (8 * len).toUInt64
  for j in [0:8] do m := m.push (bits >>> (8 * j).toUInt64).toUInt8
  let st := (blocks st m).1
  let le (w : UInt32) : Nat :=
    (w &&& 0xff).toNat * 2 ^ 24 + ((w >>> 8) &&& 0xff).toNat * 2 ^ 16 + ((w >>> 16) &&& 0xff).toNat * 2 ^ 8 +
      (w >>> 24).toNat
  return ((le st.a * 2 ^ 32 + le st.b) * 2 ^ 32 + le st.c) * 2 ^ 32 + le st.d

def digest (msg : ByteArray) : Nat :=
  let (st, tail) := blocks {} msg
  finish st tail msg.size

/-- Append `samples[start:stop]` as libFLAC hashes them: little-endian, `bytes` bytes each. -/
def pushSamples (d : ByteArray) (bytes : Nat) (samples : Array Int) (start stop : Nat) : ByteArray := Id.run do
  let mut d := d
  for i in [start:stop] do
    let u := samples[i]!.toInt64.toUInt64
    d := match bytes with
      | 1 => d.push u.toUInt8
      | 2 => (d.push u.toUInt8).push (u >>> 8).toUInt8
      | 3 => ((d.push u.toUInt8).push (u >>> 8).toUInt8).push (u >>> 16).toUInt8
      | _ => (((d.push u.toUInt8).push (u >>> 8).toUInt8).push (u >>> 16).toUInt8).push (u >>> 24).toUInt8
  return d

/-- The MD5 of `samples` at `bits` bits per sample, a chunk of samples at a time. -/
def ofSamples (bits : Nat) (samples : Array Int) : Nat := Id.run do
  let bytes := (bits + 7) / 8
  let chunk := 8192
  let mut st : State := {}
  let mut tail := ByteArray.empty
  for k in [0:(samples.size + chunk - 1) / chunk] do
    let (st', tail') := blocks st (pushSamples tail bytes samples (k * chunk) (min samples.size ((k + 1) * chunk)))
    st := st'
    tail := tail'
  return finish st tail (samples.size * bytes)

#guard digest "".toUTF8 == 0xd41d8cd98f00b204e9800998ecf8427e
#guard digest "The quick brown fox jumps over the lazy dog".toUTF8 == 0x9e107d9d372bb6826bd81d3542a419d6
#guard ofSamples 16 ((Array.range 20000).map fun (i : Nat) => ((i % 600 : Nat) : Int) - 300) ==
  digest (pushSamples .empty 2 ((Array.range 20000).map fun (i : Nat) => ((i % 600 : Nat) : Int) - 300) 0 20000)

end VeriCut.Flac.Md5
