/-!
# Big-endian byte helpers (unverified implementation, tested against ffprobe)
-/
namespace VeriCut.MP4

def u8 (b : ByteArray) (o : Nat) : Nat := (b.get! o).toNat
def u16 (b : ByteArray) (o : Nat) : Nat := u8 b o * 0x100 + u8 b (o + 1)
def u32 (b : ByteArray) (o : Nat) : Nat := u16 b o * 0x10000 + u16 b (o + 2)
def u64 (b : ByteArray) (o : Nat) : Nat := u32 b o * 0x100000000 + u32 b (o + 4)
def i32 (b : ByteArray) (o : Nat) : Int :=
  let v := u32 b o
  if v ≥ 0x80000000 then (v : Int) - 0x100000000 else v

def fourcc (b : ByteArray) (o : Nat) : String :=
  String.ofList ((List.range 4).map fun k => Char.ofNat (u8 b (o + k)))

def be (width n : Nat) : ByteArray :=
  ⟨((List.range width).reverse.map fun k => (n / 256 ^ k % 256).toUInt8).toArray⟩
def be16 := be 2
def be32 := be 4
def be64 := be 8
def beI32 (i : Int) : ByteArray := be32 (if i < 0 then (i + 0x100000000).toNat else i.toNat)

def ascii (s : String) : ByteArray := ⟨(s.toList.map fun c => c.toNat.toUInt8).toArray⟩
def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩
def concat (xs : List ByteArray) : ByteArray := xs.foldl (· ++ ·) ByteArray.empty

/-- A box: 32-bit size, four-character type, payload. -/
def box (typ : String) (payload : List ByteArray) : ByteArray :=
  let body := concat payload
  be32 (body.size + 8) ++ ascii typ ++ body

/-- A full box: a box whose payload starts with version and flags. -/
def fullBox (typ : String) (version flags : Nat) (payload : List ByteArray) : ByteArray :=
  box typ (be 1 version :: be 3 flags :: payload)

end VeriCut.MP4
