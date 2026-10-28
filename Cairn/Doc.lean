/-
A record value is a version plus a small typed body. `resolve` is the
compare-and-set: insert only when absent, update and delete only when the
stored version matches. The version does not wrap.
-/

import Cairn.Bytes

namespace Cairn

inductive Val where
  | bytes (b : Bytes)
  | str (s : String)
  | nat (n : UInt64)
  deriving Repr, BEq

def encodeVal? : Val → Option Bytes
  | .bytes b =>
      if _h : b.length < UInt32.size then
        some ((1 : UInt8) :: writeU32 (UInt32.ofNat b.length) ++ b)
      else
        none
  | .str s =>
      let b := s.toUTF8.toList
      if _h : b.length < UInt32.size then
        some ((2 : UInt8) :: writeU32 (UInt32.ofNat b.length) ++ b)
      else
        none
  | .nat n => some ((3 : UInt8) :: writeU64 n)

def decodeVal : Bytes → Option Val
  | [] => none
  | tag :: rest =>
      if tag == 1 then
        match readFit rest with
        | some (f, left) => if left.isEmpty then some (.bytes f.bytes) else none
        | none => none
      else if tag == 2 then
        match readFit rest with
        | some (f, left) =>
            if left.isEmpty then
              match String.fromUTF8? f.bytes.toByteArray with
              | some s => some (.str s)
              | none => none
            else
              none
        | none => none
      else if tag == 3 then
        match readU64 rest with
        | some (n, left) => if left.isEmpty then some (.nat n) else none
        | none => none
      else
        none

private theorem encode_bytes_round (b : Bytes) (h : b.length < UInt32.size) :
    decodeVal ((1 : UInt8) :: writeU32 (UInt32.ofNat b.length) ++ b) = some (.bytes b) := by
  have hfit : readFit (writeFit ⟨b, h⟩) = some (⟨b, h⟩, []) := by
    simpa using readFit_write ⟨b, h⟩ []
  simp only [writeFit] at hfit
  simp [decodeVal, hfit]

theorem decode_encode_bytes (b : Bytes) (h : b.length < UInt32.size) :
    decodeVal (encodeVal? (.bytes b) |>.getD []) = some (.bytes b) := by
  simp [encodeVal?, h]
  exact encode_bytes_round b h

theorem decode_encode_nat (n : UInt64) :
    decodeVal (encodeVal? (.nat n) |>.getD []) = some (.nat n) := by
  have hr : readU64 (writeU64 n) = some (n, []) := by
    simpa using readU64_write n []
  simp [encodeVal?, decodeVal, hr]

def encodeDoc (version : UInt64) (body : Bytes) : Bytes :=
  writeU64 version ++ body

def decodeDoc (bs : Bytes) : Option (UInt64 × Bytes) :=
  match readU64 bs with
  | some (v, rest) => some (v, rest)
  | none => none

theorem decodeDoc_encode (version : UInt64) (body : Bytes) :
    decodeDoc (encodeDoc version body) = some (version, body) := by
  simp [decodeDoc, encodeDoc, readU64_write]

inductive Intent where
  | insert (body : Bytes)
  | update (expect : UInt64) (body : Bytes)
  | delete (expect : UInt64)
  deriving Repr

/-- `none` keeps the row. `some none` deletes it. `some (some b)` writes `b`. -/
def resolve (cur : Option (UInt64 × Bytes)) : Intent → Option (Option Bytes)
  | .insert body =>
      match cur with
      | none => some (some (encodeDoc 1 body))
      | some _ => none
  | .update expect body =>
      match cur with
      | some (v, _) =>
          if v == expect && (expect + 1 != 0) then
            some (some (encodeDoc (expect + 1) body))
          else
            none
      | none => none
  | .delete expect =>
      match cur with
      | some (v, _) =>
          if v == expect then some none else none
      | none => none

theorem resolve_insert_fresh (body : Bytes) :
    resolve none (.insert body) = some (some (encodeDoc 1 body)) := by
  simp [resolve]

theorem resolve_insert_taken (v : UInt64) (body stored : Bytes) :
    resolve (some (v, stored)) (.insert body) = none := by
  simp [resolve]

theorem resolve_update_ok (expect : UInt64) (body stored : Bytes)
    (h : expect + 1 ≠ 0) :
    resolve (some (expect, stored)) (.update expect body) =
      some (some (encodeDoc (expect + 1) body)) := by
  have hne : (expect + 1 == 0) = false := by
    cases hb : expect + 1 == 0
    · rfl
    · exact False.elim (h (eq_of_beq hb))
  have hflag : (expect + 1 != 0) = true := by
    simp [bne, hne]
  simp [resolve, hflag, beq_self_eq_true]

theorem resolve_update_conflict (cur expect : UInt64) (body stored : Bytes)
    (h : cur ≠ expect) :
    resolve (some (cur, stored)) (.update expect body) = none := by
  simp [resolve, h]

theorem resolve_update_missing (expect : UInt64) (body : Bytes) :
    resolve none (.update expect body) = none := by
  simp [resolve]

theorem resolve_delete_ok (expect : UInt64) (stored : Bytes) :
    resolve (some (expect, stored)) (.delete expect) = some none := by
  simp [resolve]

theorem resolve_delete_conflict (cur expect : UInt64) (stored : Bytes) (h : cur ≠ expect) :
    resolve (some (cur, stored)) (.delete expect) = none := by
  simp [resolve, h]

theorem resolve_delete_missing (expect : UInt64) :
    resolve none (.delete expect) = none := by
  simp [resolve]

end Cairn
