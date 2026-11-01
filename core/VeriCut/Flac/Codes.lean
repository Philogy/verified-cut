import VeriCut.Flac.Format

/-!
Small code tables and number codings shared by the parser and the writer.
-/

namespace VeriCut.Flac

/-- Block size codes with an implied size. -/
def blockSizeCodes : List (Nat × Nat) :=
  [(1, 192), (2, 576), (3, 1152), (4, 2304), (5, 4608), (8, 256), (9, 512), (10, 1024),
   (11, 2048), (12, 4096), (13, 8192), (14, 16384), (15, 32768)]

def sampleRateCodes : List (Nat × Nat) :=
  [(1, 88200), (2, 176400), (3, 192000), (4, 8000), (5, 16000), (6, 22050), (7, 24000),
   (8, 32000), (9, 44100), (10, 48000), (11, 96000)]

def bitsPerSampleCodes : List (Nat × Nat) :=
  [(1, 8), (2, 12), (4, 16), (5, 20), (6, 24), (7, 32)]

/-- The code of `v` in `table`, if it has one. -/
def codeOf (table : List (Nat × Nat)) (v : Nat) : Option Nat :=
  (table.find? (·.2 == v)).map (·.1)

/-- Number of bytes in the UTF-8-like coding of a frame or sample number. -/
def codedLength (i : Nat) : Nat :=
  if i < 2 ^ 7 then 1 else if i < 2 ^ 11 then 2 else if i < 2 ^ 16 then 3
  else if i < 2 ^ 21 then 4 else if i < 2 ^ 26 then 5 else if i < 2 ^ 31 then 6 else 7

/-- The low `m` base-64 digits of `i`, most significant first. -/
def digits64 : Nat → Nat → List Nat
  | 0, _ => []
  | m + 1, i => i / 64 ^ m % 64 :: digits64 m i

/-- The UTF-8-like coding of `i < 2 ^ 36`: a lead byte with the length in its
leading ones, then 6 bits per continuation byte. -/
def codedBytes (i : Nat) : List Nat :=
  let n := codedLength i
  if n = 1 then [i]
  else (256 - 2 ^ (8 - n) + i / 64 ^ (n - 1)) :: (digits64 (n - 1) i).map (128 + ·)

/-- Rice codes fold signed values to `0, -1, 1, -2, …`. -/
def zigzag (v : Int) : Nat :=
  if 0 ≤ v then 2 * v.toNat else 2 * (-v).toNat - 1

def unzigzag (u : Nat) : Int :=
  if u % 2 = 0 then ((u / 2 : Nat) : Int) else -((u / 2 : Nat) : Int) - 1

def Channels.code : Channels → Nat
  | .independent n => n - 1
  | .leftSide => 8
  | .rightSide => 9
  | .midSide => 10

def Body.typeCode : Body → Nat
  | .constant _ => 0
  | .verbatim _ => 1
  | .fixed warmup _ => 8 + warmup.size
  | .lpc _ _ coefs _ _ => 31 + coefs.size

def streamMagic : Nat := 0x664C6143  -- "fLaC"

end VeriCut.Flac
