import Cairn.Bytes

/-
Non-reflected CRC-32, init 0, no final xor, polynomial 0x04C11DB7.

This is the segment and header checksum. It is not the reflected ISO
checksum used inside records (`crc32`). A fixed-width checksum cannot
reject every altered string; the proved classes live in `Sum32Thm`.
-/

namespace Cairn

def polySum : UInt32 := 0x04C11DB7

/-- One byte, MSB first, register reduced mod x^32 + polySum. -/
def sumStep (crc : UInt32) (b : UInt8) : UInt32 :=
  let rec go : Nat → UInt32 → UInt32
    | 0, c => c
    | i + 1, c =>
      if c >>> 31 == 1 then
        go i ((c <<< 1) ^^^ polySum)
      else
        go i (c <<< 1)
  go 8 (crc ^^^ (b.toUInt32 <<< 24))

def sum32 (bs : Bytes) : UInt32 :=
  bs.foldl sumStep 0

end Cairn
