/-!
The two CRCs of a FLAC frame: CRC-8 (polynomial `0x07`) over the header and
CRC-16 (polynomial `0x8005`) over the whole frame. Both start at zero and are
not reflected.
-/

namespace VeriCut

def crcTable (width poly : Nat) : Array Nat :=
  (Array.range 256).map fun b => step 8 (b <<< (width - 8))
where
  step : Nat → Nat → Nat
    | 0, c => c
    | k + 1, c =>
      let c := c <<< 1
      step k (if c >>> width = 1 then (c ^^^ poly) % 2 ^ width else c)

def crc8Table : Array Nat := crcTable 8 0x07
def crc16Table : Array Nat := crcTable 16 0x8005

def crc8 (d : ByteArray) : Nat :=
  d.foldl (fun c b => crc8Table[c ^^^ b.toNat]!) 0

def crc16 (d : ByteArray) : Nat :=
  d.foldl (fun c b => ((c <<< 8) % 65536) ^^^ crc16Table[(c >>> 8) ^^^ b.toNat]!) 0

end VeriCut
