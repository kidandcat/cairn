/-
Little-endian integers, length-bounded byte strings, and CRC-32.

Widths are fixed (`UInt32` / `UInt64`). Nothing here uses `USize` or the native
pointer width, so the codec is 32-bit clean.
-/

namespace Cairn

abbrev Bytes := List UInt8

/-! ## Disjoint bitwise or is addition -/

theorem or_add (i a b : Nat) (ha : a < 2 ^ i) : a ||| (b <<< i) = a + (b <<< i) := by
  rw [Nat.or_comm]
  rw [← Nat.shiftLeft_add_eq_or_of_lt ha]
  rw [Nat.add_comm]

theorem or4 (a b c d : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) (_hd : d < 256) :
    a ||| (b <<< 8) ||| (c <<< 16) ||| (d <<< 24) =
      a + (b <<< 8) + (c <<< 16) + (d <<< 24) := by
  have h1 : a ||| (b <<< 8) = a + (b <<< 8) := or_add 8 a b (by simpa using ha)
  have hab : a + (b <<< 8) < 65536 := by rw [Nat.shiftLeft_eq] at *; omega
  have h2 : a ||| (b <<< 8) ||| (c <<< 16) = a + (b <<< 8) + (c <<< 16) := by
    rw [h1]; exact or_add 16 (a + (b <<< 8)) c (by simpa [Nat.shiftLeft_eq] using hab)
  have habc : a + (b <<< 8) + (c <<< 16) < 16777216 := by rw [Nat.shiftLeft_eq] at *; omega
  have h3 := or_add 24 (a + (b <<< 8) + (c <<< 16)) d (by simpa [Nat.shiftLeft_eq] using habc)
  rw [h2]
  exact h3

private theorem mul_lt_of_lt_256 (x k bound : Nat) (h : x < 256) (hk : 255 * k < bound) :
    x * k < bound := by
  have hx : x ≤ 255 := Nat.le_pred_of_lt h
  have : x * k ≤ 255 * k := Nat.mul_le_mul_right _ hx
  omega

/-! ## UInt32 little-endian -/

def ofBytes (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

theorem ofBytes_toNat (b0 b1 b2 b3 : UInt8) :
    (ofBytes b0 b1 b2 b3).toNat =
      b0.toNat + (b1.toNat <<< 8) + (b2.toNat <<< 16) + (b3.toNat <<< 24) := by
  simp only [ofBytes, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32]
  rw [show (8 : UInt32).toNat = 8 from rfl, show (16 : UInt32).toNat = 16 from rfl,
      show (24 : UInt32).toNat = 24 from rfl]
  rw [show (8 : Nat) % 32 = 8 by decide, show (16 : Nat) % 32 = 16 by decide,
      show (24 : Nat) % 32 = 24 by decide]
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have hb1 : b1.toNat * 256 < 4294967296 :=
    mul_lt_of_lt_256 _ 256 4294967296 b1.toNat_lt (by decide)
  have hb2 : b2.toNat * 65536 < 4294967296 :=
    mul_lt_of_lt_256 _ 65536 4294967296 b2.toNat_lt (by decide)
  have hb3 : b3.toNat * 16777216 < 4294967296 :=
    mul_lt_of_lt_256 _ 16777216 4294967296 b3.toNat_lt (by decide)
  rw [Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb3]
  simpa [Nat.shiftLeft_eq] using
    or4 b0.toNat b1.toNat b2.toNat b3.toNat b0.toNat_lt b1.toNat_lt b2.toNat_lt b3.toNat_lt

theorem nat_bytes (n : Nat) (h : n < 4294967296) :
    n % 256 + (n / 256 % 256) * 256 + (n / 65536 % 256) * 65536 +
      (n / 16777216 % 256) * 16777216 = n := by
  have hd : n / 256 / 256 = n / 65536 := by rw [Nat.div_div_eq_div_mul]
  have he : n / 65536 / 256 = n / 16777216 := by rw [Nat.div_div_eq_div_mul]
  have h6 : n / 16777216 < 256 := by
    have : n / 16777216 ≤ (4294967296 - 1) / 16777216 :=
      Nat.div_le_div_right (Nat.le_pred_of_lt h)
    omega
  have h7 : n / 16777216 % 256 = n / 16777216 := Nat.mod_eq_of_lt h6
  have h2 : n / 256 = n / 256 % 256 + 256 * (n / 65536) := by
    rw [← hd]; exact (Nat.mod_add_div (n / 256) 256).symm
  have h4 : n / 65536 = n / 65536 % 256 + 256 * (n / 16777216) := by
    rw [← he]; exact (Nat.mod_add_div (n / 65536) 256).symm
  have h1 : n = n % 256 + 256 * (n / 256) := (Nat.mod_add_div n 256).symm
  calc
    n % 256 + (n / 256 % 256) * 256 + (n / 65536 % 256) * 65536 +
        (n / 16777216 % 256) * 16777216
      = n % 256 + (n / 256 % 256) * 256 + (n / 65536 % 256) * 65536 +
          (n / 16777216) * 16777216 := by rw [h7]
    _ = n := by rw [h1, h2, h4]; omega

def writeU32 (n : UInt32) : Bytes :=
  [n.toUInt8, (n >>> 8).toUInt8, (n >>> 16).toUInt8, (n >>> 24).toUInt8]

def readU32 : Bytes → Option (UInt32 × Bytes)
  | b0 :: b1 :: b2 :: b3 :: rest => some (ofBytes b0 b1 b2 b3, rest)
  | _ => none

private theorem low_mod (a b c d : Nat) (ha : a < 256) :
    (a + b * 256 + c * 65536 + d * 16777216) % 256 = a := by
  have hform : a + b * 256 + c * 65536 + d * 16777216 =
      a + 256 * (b + 256 * (c + 256 * d)) := by omega
  rw [hform, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem byte0_of (b0 b1 b2 b3 : UInt8) : (ofBytes b0 b1 b2 b3).toUInt8 = b0 := by
  apply UInt8.toNat_inj.mp
  rw [UInt32.toNat_toUInt8, ofBytes_toNat, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  exact low_mod _ _ _ _ b0.toNat_lt

private theorem div256 (a b c d : Nat) (ha : a < 256) :
    (a + b * 256 + c * 65536 + d * 16777216) / 256 = b + c * 256 + d * 65536 := by
  have hform : a + b * 256 + c * 65536 + d * 16777216 =
      a + 256 * (b + c * 256 + d * 65536) := by omega
  rw [hform, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt ha]
  omega

theorem byte1_of (b0 b1 b2 b3 : UInt8) : ((ofBytes b0 b1 b2 b3) >>> 8).toUInt8 = b1 := by
  apply UInt8.toNat_inj.mp
  rw [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight]
  rw [show (8 : UInt32).toNat = 8 from rfl, show (8 : Nat) % 32 = 8 by decide]
  rw [Nat.shiftRight_eq_div_pow, ofBytes_toNat, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  rw [div256 _ _ _ _ b0.toNat_lt]
  have hform : b1.toNat + b2.toNat * 256 + b3.toNat * 65536 =
      b1.toNat + 256 * (b2.toNat + b3.toNat * 256) := by omega
  rw [hform, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b1.toNat_lt]

private theorem low16 (a b : Nat) (ha : a < 256) (hb : b < 256) : a + b * 256 < 65536 := by
  omega

private theorem div65536 (a b c d : Nat) (hl : a + b * 256 < 65536) :
    (a + b * 256 + c * 65536 + d * 16777216) / 65536 = c + d * 256 := by
  have hform : a + b * 256 + c * 65536 + d * 16777216 =
      (a + b * 256) + 65536 * (c + d * 256) := by omega
  rw [hform, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hl]
  omega

theorem byte2_of (b0 b1 b2 b3 : UInt8) : ((ofBytes b0 b1 b2 b3) >>> 16).toUInt8 = b2 := by
  apply UInt8.toNat_inj.mp
  rw [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight]
  rw [show (16 : UInt32).toNat = 16 from rfl, show (16 : Nat) % 32 = 16 by decide]
  rw [Nat.shiftRight_eq_div_pow, ofBytes_toNat, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  rw [div65536 _ _ _ _ (low16 _ _ b0.toNat_lt b1.toNat_lt)]
  rw [show b2.toNat + b3.toNat * 256 = b2.toNat + 256 * b3.toNat by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b2.toNat_lt]

private theorem low24 (a b c : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    a + b * 256 + c * 65536 < 16777216 := by
  omega

private theorem div16777216 (a b c d : Nat) (hl : a + b * 256 + c * 65536 < 16777216) :
    (a + b * 256 + c * 65536 + d * 16777216) / 16777216 = d := by
  have hform : a + b * 256 + c * 65536 + d * 16777216 =
      (a + b * 256 + c * 65536) + 16777216 * d := by omega
  rw [hform, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hl]
  omega

theorem byte3_of (b0 b1 b2 b3 : UInt8) : ((ofBytes b0 b1 b2 b3) >>> 24).toUInt8 = b3 := by
  apply UInt8.toNat_inj.mp
  rw [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight]
  rw [show (24 : UInt32).toNat = 24 from rfl, show (24 : Nat) % 32 = 24 by decide]
  rw [Nat.shiftRight_eq_div_pow, ofBytes_toNat, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  rw [div16777216 _ _ _ _ (low24 _ _ _ b0.toNat_lt b1.toNat_lt b2.toNat_lt)]
  exact Nat.mod_eq_of_lt b3.toNat_lt

theorem writeU32_ofBytes (b0 b1 b2 b3 : UInt8) :
    writeU32 (ofBytes b0 b1 b2 b3) = [b0, b1, b2, b3] := by
  simp [writeU32, byte0_of, byte1_of, byte2_of, byte3_of]

theorem readU32_write (n : UInt32) (rest : Bytes) :
    readU32 (writeU32 n ++ rest) = some (n, rest) := by
  simp [readU32, writeU32]
  apply UInt32.toNat_inj.mp
  rw [ofBytes_toNat]
  simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [show (8 : UInt32).toNat = 8 from rfl, show (16 : UInt32).toNat = 16 from rfl,
      show (24 : UInt32).toNat = 24 from rfl]
  rw [show (8 : Nat) % 32 = 8 by decide, show (16 : Nat) % 32 = 16 by decide,
      show (24 : Nat) % 32 = 24 by decide]
  have hn : n.toNat < 4294967296 := n.toNat_lt
  simpa [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq] using nat_bytes n.toNat hn

theorem readU32_sound {bs : Bytes} {n : UInt32} {rest : Bytes}
    (h : readU32 bs = some (n, rest)) : bs = writeU32 n ++ rest := by
  match bs with
  | b0 :: b1 :: b2 :: b3 :: rest' =>
      simp [readU32] at h
      rcases h with ⟨rfl, rfl⟩
      rw [writeU32_ofBytes]
      rfl
  | [] => simp [readU32] at h
  | [_] => simp [readU32] at h
  | [_, _] => simp [readU32] at h
  | [_, _, _] => simp [readU32] at h

/-! ## UInt64 little-endian, as two UInt32 halves -/

def ofHalves (lo hi : UInt32) : UInt64 :=
  lo.toUInt64 ||| (hi.toUInt64 <<< 32)

private theorem u64_shift_mod (hi : UInt32) :
    hi.toNat * 4294967296 < 18446744073709551616 := by
  have h : hi.toNat ≤ 4294967295 := Nat.le_pred_of_lt hi.toNat_lt
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ h)
    (by decide : 4294967295 * 4294967296 < 18446744073709551616)

theorem ofHalves_toNat (lo hi : UInt32) :
    (ofHalves lo hi).toNat = lo.toNat + hi.toNat * 4294967296 := by
  have hs : (hi.toUInt64 <<< 32).toNat = hi.toNat * 4294967296 := by
    simp only [UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64]
    rw [show (32 : UInt64).toNat = 32 from rfl, show (32 : Nat) % 64 = 32 by decide,
        Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (u64_shift_mod hi)
  have ho : (lo.toUInt64 ||| (hi.toUInt64 <<< 32)).toNat =
      lo.toNat ||| (hi.toNat * 4294967296) := by
    simp only [UInt64.toNat_or, UInt32.toNat_toUInt64, hs]
  have hdisj : lo.toNat ||| (hi.toNat <<< 32) = lo.toNat + (hi.toNat <<< 32) :=
    or_add 32 lo.toNat hi.toNat lo.toNat_lt
  have : lo.toNat ||| (hi.toNat * 4294967296) = lo.toNat + hi.toNat * 4294967296 := by
    simpa [Nat.shiftLeft_eq] using hdisj
  simpa [ofHalves, ho] using this

theorem halves_split (lo hi : UInt32) :
    (ofHalves lo hi).toUInt32 = lo ∧ ((ofHalves lo hi) >>> 32).toUInt32 = hi := by
  refine ⟨?_, ?_⟩
  · apply UInt32.toNat_inj.mp
    rw [UInt64.toNat_toUInt32, ofHalves_toNat]
    rw [show (2 ^ 32) = 4294967296 by decide, Nat.mul_comm hi.toNat 4294967296,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lo.toNat_lt]
  · apply UInt32.toNat_inj.mp
    rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, ofHalves_toNat]
    rw [show (32 : UInt64).toNat = 32 from rfl, show (32 : Nat) % 64 = 32 by decide,
      Nat.shiftRight_eq_div_pow]
    rw [show (2 ^ 32) = 4294967296 by decide]
    have hform : lo.toNat + hi.toNat * 4294967296 = lo.toNat + 4294967296 * hi.toNat := by omega
    rw [hform, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt lo.toNat_lt, Nat.zero_add]
    exact Nat.mod_eq_of_lt hi.toNat_lt

theorem halves_round (n : UInt64) : ofHalves n.toUInt32 (n >>> 32).toUInt32 = n := by
  apply UInt64.toNat_inj.mp
  rw [ofHalves_toNat]
  have hlo : n.toUInt32.toNat = n.toNat % 4294967296 := by
    simp [UInt64.toNat_toUInt32]
  have hhiNat : (n >>> 32).toNat = n.toNat / 4294967296 := by
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have hsmall : n.toNat / 4294967296 < 4294967296 := by
    have hn : n.toNat ≤ 18446744073709551615 := Nat.le_pred_of_lt n.toNat_lt
    have hle : n.toNat / 4294967296 ≤ 18446744073709551615 / 4294967296 :=
      Nat.div_le_div_right hn
    have hd : 18446744073709551615 / 4294967296 = 4294967295 := by decide
    exact Nat.lt_succ_of_le (by simpa [hd] using hle)
  have hhi : (n >>> 32).toUInt32.toNat = n.toNat / 4294967296 := by
    have hlt : (n >>> 32).toNat < 4294967296 := by rw [hhiNat]; exact hsmall
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hlt, hhiNat]
  rw [hlo, hhi, Nat.mul_comm (n.toNat / 4294967296)]
  exact Nat.mod_add_div n.toNat 4294967296

def writeU64 (n : UInt64) : Bytes :=
  writeU32 n.toUInt32 ++ writeU32 (n >>> 32).toUInt32

def readU64 (bs : Bytes) : Option (UInt64 × Bytes) :=
  match readU32 bs with
  | some (lo, bs) =>
      match readU32 bs with
      | some (hi, bs) => some (ofHalves lo hi, bs)
      | none => none
  | none => none

theorem readU64_write (n : UInt64) (rest : Bytes) :
    readU64 (writeU64 n ++ rest) = some (n, rest) := by
  simp [readU64, writeU64, readU32_write, halves_round]

theorem readU64_sound {bs : Bytes} {n : UInt64} {rest : Bytes}
    (h : readU64 bs = some (n, rest)) : bs = writeU64 n ++ rest := by
  simp [readU64] at h
  cases h1 : readU32 bs with
  | none => simp [h1] at h
  | some p =>
      cases p with
      | mk lo bs1 =>
          simp [h1] at h
          cases h2 : readU32 bs1 with
          | none => simp [h2] at h
          | some q =>
              cases q with
              | mk hi bs2 =>
                  simp [h2] at h
                  rcases h with ⟨rfl, rfl⟩
                  have hb := readU32_sound h1
                  have hb1 := readU32_sound h2
                  have hs := halves_split lo hi
                  simp [writeU64, hb, hb1, hs]

/-! ## Length-bounded strings (`UInt32` length) -/

structure FitBytes where
  bytes : Bytes
  hlen : bytes.length < UInt32.size
  deriving Repr

instance : BEq FitBytes where
  beq a b := a.bytes == b.bytes

theorem FitBytes.eq_of_bytes {a b : FitBytes} (h : a.bytes = b.bytes) : a = b := by
  cases a
  cases b
  cases h
  rfl

def FitBytes.ofList? (b : Bytes) : Option FitBytes :=
  if h : b.length < UInt32.size then some ⟨b, h⟩ else none

def FitBytes.ofString? (s : String) : Option FitBytes :=
  FitBytes.ofList? s.toUTF8.toList

def writeFit (f : FitBytes) : Bytes :=
  writeU32 (UInt32.ofNat f.bytes.length) ++ f.bytes

def readExact (n : Nat) (bs : Bytes) : Option (Bytes × Bytes) :=
  if n ≤ bs.length then some (bs.take n, bs.drop n) else none

theorem readExact_write (data rest : Bytes) :
    readExact data.length (data ++ rest) = some (data, rest) := by
  have hle : data.length ≤ (data ++ rest).length := by
    simp [List.length_append]
  rw [readExact, ite_eq_left hle, List.take_left, List.drop_left]

theorem readExact_none {n : Nat} {bs : Bytes} (h : bs.length < n) :
    readExact n bs = none := by
  rw [readExact, ite_eq_right (Nat.not_le_of_gt h)]

def readFit (bs : Bytes) : Option (FitBytes × Bytes) :=
  Option.bind (readU32 bs) fun p =>
    Option.bind (readExact p.1.toNat p.2) fun q =>
      if hlen : q.1.length < UInt32.size then
        some (⟨q.1, hlen⟩, q.2)
      else
        none

theorem readFit_write (f : FitBytes) (rest : Bytes) :
    readFit (writeFit f ++ rest) = some (f, rest) := by
  cases f with
  | mk bytes hlen =>
      have hn : (UInt32.ofNat bytes.length).toNat = bytes.length :=
        UInt32.toNat_ofNat_of_lt hlen
      rw [readFit, writeFit, List.append_assoc, readU32_write, Option.bind_some, hn,
        readExact_write, Option.bind_some, dite_eq_left hlen]

/-! ## Short reads

A truncated buffer cannot satisfy a fixed-width or a length prefix. These lemmas
are the crash argument: a proper prefix of a framed value does not decode.
-/

theorem writeU32_length (n : UInt32) : (writeU32 n).length = 4 := by
  simp [writeU32]

theorem readU32_short {bs : Bytes} (h : bs.length < 4) : readU32 bs = none := by
  cases bs with
  | nil => rfl
  | cons _ t0 =>
      cases t0 with
      | nil => rfl
      | cons _ t1 =>
          cases t1 with
          | nil => rfl
          | cons _ t2 =>
              cases t2 with
              | nil => rfl
              | cons _ _ =>
                  exfalso
                  simp [List.length_cons] at h
                  omega

theorem readU32_prefix (n : UInt32) (k : Nat) (hk : k < 4) :
    readU32 ((writeU32 n).take k) = none := by
  apply readU32_short
  simpa [writeU32_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] using hk

theorem readU64_prefix (n : UInt64) (k : Nat) (hk : k < 8) :
    readU64 ((writeU64 n).take k) = none := by
  unfold writeU64 readU64
  by_cases hk4 : k < 4
  · rw [List.take_append_of_le_length (by simp [writeU32_length]; omega)]
    simp [readU32_prefix n.toUInt32 k hk4]
  · have hge : 4 ≤ k := by omega
    have hk2 : k - 4 < 4 := by omega
    have hlen4 : (writeU32 n.toUInt32).length = 4 := writeU32_length _
    rw [List.take_append, hlen4, List.take_of_length_le hge, readU32_write]
    simp [readU32_prefix (n >>> 32).toUInt32 (k - 4) hk2]

theorem writeFit_length (f : FitBytes) : (writeFit f).length = 4 + f.bytes.length := by
  simp [writeFit, writeU32_length, List.length_append]

theorem readFit_prefix (f : FitBytes) (k : Nat) (hk : k < (writeFit f).length) :
    readFit ((writeFit f).take k) = none := by
  cases f with
  | mk bytes hlen =>
      simp only [writeFit, readFit]
      by_cases hk4 : k < 4
      · rw [List.take_append_of_le_length (by simp [writeU32_length]; omega)]
        simp [readU32_prefix _ k hk4]
      · have hge : 4 ≤ k := by omega
        have hlen4 : (writeU32 (UInt32.ofNat bytes.length)).length = 4 := writeU32_length _
        rw [List.take_append, hlen4, List.take_of_length_le hge, readU32_write]
        have hn : (UInt32.ofNat bytes.length).toNat = bytes.length :=
          UInt32.toNat_ofNat_of_lt hlen
        simp only [hn, Option.bind_some]
        have hshort : (bytes.take (k - 4)).length < bytes.length := by
          have hk' : k < 4 + bytes.length := by
            simpa [writeFit_length] using hk
          simp [List.length_take]
          omega
        rw [readExact_none hshort, Option.bind_none]

/-! ## CRC-32/ISO-HDLC (polynomial 0xEDB88320)

The truncation proof does not depend on collision-freedom. CRC-32 is a
deterministic filter: a record is accepted only when the stored word equals
`crc32` of the canonical body.
-/

def crcStep (crc : UInt32) (b : UInt8) : UInt32 :=
  let rec go : Nat → UInt32 → UInt32
    | 0, c => c
    | i + 1, c =>
        if c &&& 1 == 1 then
          go i ((0xEDB88320 : UInt32) ^^^ (c >>> 1))
        else
          go i (c >>> 1)
  go 8 (crc ^^^ b.toUInt32)

def crc32 (bs : Bytes) : UInt32 :=
  bs.foldl crcStep (0xFFFFFFFF : UInt32) ^^^ (0xFFFFFFFF : UInt32)

end Cairn
