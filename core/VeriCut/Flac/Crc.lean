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

-- In `UInt32`, which stays unboxed in the loop. The final `%` never changes the value;
-- it saves proving the table entries fit.
def crc8Table32 : Array UInt32 := crc8Table.map (·.toUInt32)
def crc16Table32 : Array UInt32 := crc16Table.map (·.toUInt32)

def crc8 (d : ByteArray) : Nat :=
  (d.foldl (fun (c : UInt32) b => crc8Table32[((c ^^^ b.toUInt32) &&& 0xFF).toNat]!) (0 : UInt32)).toNat % 256

def crc16 (d : ByteArray) : Nat :=
  (d.foldl (fun (c : UInt32) b => ((c <<< (8 : UInt32)) &&& (0xFFFF : UInt32)) ^^^ crc16Table32[(((c >>> (8 : UInt32)) ^^^ b.toUInt32) &&& 0xFF).toNat]!)
    (0 : UInt32)).toNat % 65536

end VeriCut
