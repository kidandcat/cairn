/-
Optimistic commit inside one shard. The caller lists every key the decision
read. At commit those values must still match. A key that changed rejects
the batch and writes nothing.

This is not snapshot isolation. Two transactions that each read a key the
other writes will conflict if that key is in the read set. A decision that
forgets to record a read can still commit a write skew. The read set is
explicit.
-/

import Cairn.Log
import Cairn.ShardSet
import Cairn.Ulid

namespace Cairn

structure Read where
  key : FitBytes
  saw : Option FitBytes
  deriving Repr, BEq

def readsMatch (m : Map) (rs : List Read) : Bool :=
  rs.all fun r => Cairn.get m r.key == r.saw

theorem readsMatch_iff (m : Map) (rs : List Read) :
    readsMatch m rs = true ↔ ∀ r ∈ rs, Cairn.get m r.key == r.saw := by
  simp [readsMatch, List.all_eq_true]

theorem readsMatch_miss (m : Map) (k : FitBytes) (saw : Option FitBytes) (rs : List Read)
    (hmem : ⟨k, saw⟩ ∈ rs) (hget : (Cairn.get m k == saw) = false) :
    readsMatch m rs = false := by
  rw [Bool.eq_false_iff]
  intro hall
  have htrue : (Cairn.get m k == saw) = true := by
    have hall' : ∀ r ∈ rs, (Cairn.get m r.key == r.saw) = true := by
      simpa [readsMatch, List.all_eq_true] using hall
    exact hall' ⟨k, saw⟩ hmem
  simp [hget] at htrue

/-- After `k` changes, a read set that observed the old value does not match. -/
theorem occ_conflict (m : Map) (k old new : FitBytes) (rs : List Read)
    (hmem : ⟨k, some old⟩ ∈ rs) (hne : old ≠ new) :
    readsMatch (insert m k new) rs = false := by
  have hget : (Cairn.get (insert m k new) k == some old) = false := by
    rw [get_insert]
    cases hb : new == old
    · simp [hb]
    · exact absurd (eq_of_beq hb) (Ne.symm hne)
  exact readsMatch_miss (insert m k new) k (some old) rs hmem hget

/--
Obsolete. The annotated read set can miss a write skew. New bodies use
`ShardSet.transact` and `Tx`, which see every read they perform.
This wrapper still checks the recorded reads through `Tx` and then writes.
-/
def occCommit (s : ShardSet) (anchor : FitBytes) (reads : List Read) (writes : List Op) :
    IO Bool := do
  s.transact anchor fun tx => do
    let mut ok := true
    for r in reads do
      let cur ← tx.get r.key
      if cur != r.saw then
        ok := false
    if ok = false then
      return false
    if sameShard tx.bounds writes = false then
      throw (IO.userError "occ crossed a shard")
    for op in writes do
      match op with
      | .put k v => tx.put k v
      | .del k => tx.delete k
    return true

namespace Sec

def indexKey? (idx field : Bytes) (id : Ulid) : Option FitBytes :=
  if _hidx : idx.length < UInt32.size then
    if _hf : field.length < UInt32.size then
      FitBytes.ofList?
        ([5] ++ writeU32 (UInt32.ofNat idx.length) ++ idx ++
          writeU32 (UInt32.ofNat field.length) ++ field ++ Ulid.encode id)
    else
      none
  else
    none

/--
Document and index entries in one batch. The index value is the document key.
Refused when a key would land in another shard. Nothing is written in that case.
-/
def put (s : ShardSet) (doc val : FitBytes) (indexes : List FitBytes) : IO Unit := do
  let ops := [.put doc val] ++ indexes.map fun ik => .put ik doc
  let epoch ← s.epoch.get
  if sameShard epoch.bounds ops = false then
    throw (IO.userError "index crossed a shard")
  s.transact doc fun tx => do
    for op in ops do
      match op with
      | .put k v => tx.put k v
      | .del k => tx.delete k

end Sec

end Cairn
