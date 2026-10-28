/-
A backup of one shard is the committed records whose LSN is `≤ n`.
On a log whose LSNs only grow, that is a prefix: later records are not
older. Restore is opening that byte image. Compaction in the background is
`DB.compact` on its own task. Schema version is one key, written in the
same batch as the migration step when that key shares the shard.
-/

import Cairn.DB
import Cairn.ShardSet
import Cairn.Store

namespace Cairn

def upTo (n : UInt64) : List Record → List Record
  | [] => []
  | r :: rs => if decide (r.lsn ≤ n) then r :: upTo n rs else []

theorem upTo_is_prefix (n : UInt64) (rs : List Record) :
    ∃ k, upTo n rs = rs.take k := by
  induction rs with
  | nil => exact ⟨0, by simp [upTo]⟩
  | cons r rs ih =>
      obtain ⟨k, hk⟩ := ih
      by_cases h : decide (r.lsn ≤ n) = true
      · refine ⟨k + 1, ?_⟩
        simp [upTo, h, hk, List.take_succ_cons]
      · refine ⟨0, ?_⟩
        simp [upTo, h]

def DB.backupRecords (db : DB) (n : UInt64) : IO (List Record) := do
  return upTo n (← db.readLog)

def DB.backupFile (db : DB) (path : System.FilePath) (n : UInt64) : IO Unit := do
  let rs ← db.backupRecords n
  writeDurable path (encodeFile rs)

def DB.compactAsync (db : DB) : IO (Task (Except IO.Error Unit)) :=
  IO.asTask (prio := .dedicated) (db.compact)

def schemaKey : FitBytes :=
  ⟨[0], by decide⟩

theorem writeU64_length (n : UInt64) : (writeU64 n).length = 8 := by
  simp [writeU64, writeU32, List.length_append, List.length_cons, List.length_nil]

def encodeSchema (v : UInt64) : FitBytes :=
  ⟨writeU64 v, by rw [writeU64_length]; decide⟩

def readSchema (v : Option FitBytes) : UInt64 :=
  match v with
  | some f =>
      match readU64 f.bytes with
      | some (n, _) => n
      | none => 0
  | none => 0

theorem schema_visible (m : Map) (ver : FitBytes) :
    get (applyBatch m [.put schemaKey ver]) schemaKey = some ver :=
  get_after_put m schemaKey ver

def migrate (s : ShardSet) (target : UInt64) (step : UInt64 → List Op) : IO UInt64 := do
  s.transact schemaKey fun v => do
    let cur := readSchema (Cairn.get v.index schemaKey)
    if target ≤ cur then
      return ([], cur)
    else
      let ops := step cur ++ [.put schemaKey (encodeSchema target)]
      if sameShard v.epoch.bounds ops = false then
        throw (IO.userError "migration crossed a shard")
      return (ops, target)

end Cairn
