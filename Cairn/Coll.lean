/-
A collection is a key prefix. The id is a `Ulid`, so list order is time order.
The value carries a version. `update` and `delete` write only when that
version matches, and the check runs under the shard writer lock.

One document is one key, so it sits in one shard. Listing a collection can
cross shards: it is `ShardSet.prefix`, a merge of per-shard snapshots, not a
global snapshot.
-/

import Cairn.Doc
import Cairn.ShardSet
import Cairn.Ulid

namespace Cairn

def collPrefix (name : Bytes) : Bytes :=
  (1 : UInt8) :: writeU32 (UInt32.ofNat name.length) ++ name ++ [2]

def docKey? (name : Bytes) (id : Ulid) : Option FitBytes :=
  if _h : name.length < UInt32.size then
    FitBytes.ofList? (collPrefix name ++ Ulid.encode id)
  else
    none

inductive CasResult where
  | ok (version : UInt64)
  | conflict
  | missing
  deriving Repr, BEq

private def editOf (cur : Option FitBytes) (intent : Intent) : Edit × CasResult :=
  let decoded :=
    match cur with
    | none => none
    | some f => decodeDoc f.bytes
  match resolve decoded intent with
  | none =>
      match intent, decoded with
      | .insert _, some _ => (.keep, .conflict)
      | .update _ _, none => (.keep, .missing)
      | .delete _, none => (.keep, .missing)
      | _, _ => (.keep, .conflict)
  | some none => (.del, .ok 0)
  | some (some raw) =>
      match FitBytes.ofList? raw, decodeDoc raw with
      | some packed, some (ver, _) => (.put packed, .ok ver)
      | _, _ => (.keep, .conflict)

private def onKey (s : ShardSet) (k : FitBytes) (intent : Intent) : IO CasResult :=
  s.modifyKey k (fun cur => editOf cur intent)

private def requireKey (name : String) (id : Ulid) : IO FitBytes := do
  let raw := name.toUTF8.toList
  match docKey? raw id with
  | some k => return k
  | none => throw (IO.userError "key does not fit")

def collInsert (s : ShardSet) (name : String) (id : Ulid) (val : Val) : IO CasResult := do
  let some body := encodeVal? val | throw (IO.userError "value does not fit")
  onKey s (← requireKey name id) (.insert body)

def collGet (s : ShardSet) (name : String) (id : Ulid) : IO (Option (UInt64 × Val)) := do
  match ← s.get (← requireKey name id) with
  | none => return none
  | some f =>
      match decodeDoc f.bytes with
      | some (ver, body) =>
          match decodeVal body with
          | some v => return some (ver, v)
          | none => return none
      | none => return none

def collUpdate (s : ShardSet) (name : String) (id : Ulid) (expect : UInt64) (val : Val) :
    IO CasResult := do
  let some body := encodeVal? val | throw (IO.userError "value does not fit")
  onKey s (← requireKey name id) (.update expect body)

def collDelete (s : ShardSet) (name : String) (id : Ulid) (expect : UInt64) : IO CasResult := do
  onKey s (← requireKey name id) (.delete expect)

def readBe : Nat → Bytes → Option (Nat × Bytes)
  | 0, bs => some (0, bs)
  | _n + 1, [] => none
  | n + 1, b :: rest =>
      match readBe n rest with
      | none => none
      | some (k, left) => some (b.toNat * 256 ^ n + k, left)

def Ulid.decode? (bs : Bytes) : Option Ulid :=
  match readBe 6 bs with
  | some (t, rest) =>
      match readBe 10 rest with
      | some (r, left) =>
          if left.isEmpty then
            if ht : t < 2 ^ 48 then
              if hr : r < 2 ^ 80 then
                some ⟨t, r, ht, hr⟩
              else
                none
            else
              none
          else
            none
      | none => none
  | none => none

structure Listed where
  id : Ulid
  version : UInt64
  val : Val
  deriving Repr

def collList (s : ShardSet) (name : String) (after : Option Ulid) (limit : Nat) :
    IO (List Listed × Option Ulid) := do
  let raw := name.toUTF8.toList
  if _h : raw.length < UInt32.size then
    let pre := collPrefix raw
    let cursor : Option FitBytes :=
      match after with
      | none => none
      | some id => docKey? raw id
    let (rows, nextKey) ← s.prefix pre cursor limit
    let mut out : List Listed := []
    for e in rows do
      let suf := e.1.bytes.drop pre.length
      match Ulid.decode? suf, decodeDoc e.2.bytes with
      | some id, some (ver, body) =>
          match decodeVal body with
          | some v => out := out ++ [{ id, version := ver, val := v }]
          | none => pure ()
      | _, _ => pure ()
    let next :=
      match nextKey with
      | none => none
      | some k => Ulid.decode? (k.bytes.drop pre.length)
    return (out, next)
  else
    throw (IO.userError "name does not fit")

end Cairn
