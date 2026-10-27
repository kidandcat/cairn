/-
Checksums measured against `sum32`, not stored on disk.

`sum64` is CRC-64-ECMA (poly 0x42F0E1EBA9EA3693), init 0, no final xor,
MSB first. The same "odd polynomial, degree 64" argument would extend the
32-bit burst proof to 64 bits. That argument is not mechanized here.

`mix128` is a pure multiply-xor mixer. It is not xxHash, not BLAKE, and not
a cryptographic hash. It is here so the benchmark can compare a 128-bit
checksum with the CRC the file format actually uses.
-/

import Cairn.Bytes

namespace Cairn

def poly64 : UInt64 := 0x42F0E1EBA9EA3693

def sumStep64 (crc : UInt64) (b : UInt8) : UInt64 :=
  let rec go : Nat → UInt64 → UInt64
    | 0, c => c
    | i + 1, c =>
        if c >>> 63 == 1 then
          go i ((c <<< 1) ^^^ poly64)
        else
          go i (c <<< 1)
  go 8 (crc ^^^ (b.toUInt64 <<< 56))

def sum64 (bs : Bytes) : UInt64 :=
  bs.foldl sumStep64 0

def mixStep (s : UInt64 × UInt64) (b : UInt8) : UInt64 × UInt64 :=
  let x := s.1 ^^^ b.toUInt64
  let x := x * 0x9E3779B185EBCA87
  let y := s.2 ^^^ (x >>> 17)
  let y := y * 0xC2B2AE3D27D4EB4F
  (x ^^^ (y >>> 23), y ^^^ (x >>> 11))

def mix128 (bs : Bytes) : UInt64 × UInt64 :=
  bs.foldl mixStep (0x9E3779B185EBCA87, 0xC2B2AE3D27D4EB4F)

end Cairn
