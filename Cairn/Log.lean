/-
Logical log. A record is one atomic batch. Replay folds batches onto the map.

Compaction emits one put per surviving key, in key order. Replaying that log
rebuilds the same entries. The tree that comes back need not have the same
shape as the tree that was compacted. A crash is a prefix of the encoded byte
string; decoding it yields a prefix of the committed records.
-/

import Cairn.Record
import Cairn.FileFmt
import Cairn.FileFmtThm
import Cairn.Map

namespace Cairn

def applyOp (m : Map) : Op → Map
  | .put k v => insert m k v
  | .del k => remove m k

def applyBatch (m : Map) (ops : List Op) : Map :=
  ops.foldl applyOp m

@[simp] theorem applyBatch_nil (m : Map) : applyBatch m [] = m := rfl

@[simp] theorem applyBatch_cons (m : Map) (op : Op) (ops : List Op) :
    applyBatch m (op :: ops) = applyBatch (applyOp m op) ops := rfl

theorem applyBatch_append (m : Map) (a b : List Op) :
    applyBatch m (a ++ b) = applyBatch (applyBatch m a) b := by
  simp [applyBatch, List.foldl_append]

theorem get_after_put (m : Map) (k v : FitBytes) :
    get (applyBatch m [.put k v]) k = some v := by
  simp [applyOp, get_insert]

theorem get_after_del (m : Map) (k : FitBytes) :
    get (applyBatch m [.del k]) k = none := by
  simp [applyOp, get_remove]

theorem get_batch_put (m : Map) (pre : List Op) (k v : FitBytes) :
    get (applyBatch m (pre ++ [.put k v])) k = some v := by
  rw [applyBatch_append]
  simp [applyOp, get_insert]

theorem get_batch_del (m : Map) (pre : List Op) (k : FitBytes) :
    get (applyBatch m (pre ++ [.del k])) k = none := by
  rw [applyBatch_append]
  simp [applyOp, get_remove]

theorem nodup_applyOp (m : Map) (op : Op) (h : NodupKeys m) : NodupKeys (applyOp m op) := by
  cases op with
  | put k v => simpa [applyOp] using nodup_insert m k v h
  | del k => simpa [applyOp] using nodup_remove m k h

theorem nodup_applyBatch (m : Map) (ops : List Op) (h : NodupKeys m) :
    NodupKeys (applyBatch m ops) := by
  induction ops generalizing m with
  | nil => simpa using h
  | cons op ops ih =>
      exact ih (applyOp m op) (nodup_applyOp m op h)

def replay (rs : List Record) : Map :=
  rs.foldl (fun m r => applyBatch m r.ops) Map.empty

theorem replay_append (a b : List Record) :
    replay (a ++ b) = b.foldl (fun m r => applyBatch m r.ops) (replay a) := by
  simp [replay, List.foldl_append]

theorem nodup_replay_from (m : Map) (rs : List Record) (h : NodupKeys m) :
    NodupKeys (rs.foldl (fun acc r => applyBatch acc r.ops) m) := by
  induction rs generalizing m with
  | nil => simpa using h
  | cons r rs ih =>
      exact ih (applyBatch m r.ops) (nodup_applyBatch m r.ops h)

theorem nodup_replay (rs : List Record) : NodupKeys (replay rs) :=
  nodup_replay_from Map.empty rs nodup_nil

/-! ## Compaction -/

/-- One put per live key, in `entries` order. -/
def toPuts (m : Map) : List Op :=
  (entries m).map fun e => .put e.1 e.2

private theorem apply_mapped (m : Map) (es : List (FitBytes × FitBytes)) :
    applyBatch m (es.map fun e => Op.put e.1 e.2) =
      es.foldl (fun acc e => insert acc e.1 e.2) m := by
  induction es generalizing m with
  | nil => rfl
  | cons e es ih =>
      cases e with
      | mk k v =>
          simp only [List.map_cons, applyBatch_cons, applyOp, List.foldl_cons, ih]

theorem apply_toPuts (m : Map) (h : NodupKeys m) :
    entries (applyBatch Map.empty (toPuts m)) = entries m := by
  have _kept : NodupKeys m := h
  rw [toPuts, apply_mapped]
  simpa [ofPairs] using entries_rebuilt m

/-- One record per surviving put. LSNs start at `start` and increase by one. -/
def recordsOf (start : UInt64) : List Op → List Record
  | [] => []
  | op :: ops => Record.ofBatch start (Batch.single op) :: recordsOf (start + 1) ops

theorem fold_records (start : UInt64) (ops : List Op) (m : Map) :
    (recordsOf start ops).foldl (fun acc r => applyBatch acc r.ops) m = applyBatch m ops := by
  induction ops generalizing start m with
  | nil => simp [recordsOf]
  | cons op ops ih =>
      rw [recordsOf, List.foldl_cons, Record.ofBatch, Batch.single]
      rw [show applyBatch m [op] = applyOp m op by simp]
      rw [ih (start + 1) (applyOp m op)]
      simp

theorem replay_records (start : UInt64) (ops : List Op) :
    replay (recordsOf start ops) = applyBatch Map.empty ops := by
  simpa [replay] using fold_records start ops Map.empty

def compactRecords (m : Map) (start : UInt64) : List Record :=
  recordsOf start (toPuts m)

/-- Replaying the compacted log yields the same bindings. The tree shape may differ. -/
theorem compact_eq (m : Map) (h : NodupKeys m) (start : UInt64) :
    entries (replay (compactRecords m start)) = entries m := by
  rw [compactRecords, replay_records]
  exact apply_toPuts m h

theorem compact_roundtrip (m : Map) (h : NodupKeys m) (start : UInt64) :
    entries (replay (decodeLog (encodeLog (compactRecords m start)))) = entries m := by
  rw [decodeLog_encode]
  exact compact_eq m h start

/-! ## Crash as a byte prefix -/

/--
Decoding a prefix of an encoded file replays some prefix of the records.
Whole frames are kept. A frame that does not fit is dropped, not split.
`RecordsFit` excludes a payload that does not fit in the `UInt32` length.
-/
theorem recovery_prefix (rs : List Record) (n : Nat) (h : RecordsFit rs) :
    ∃ k, Except.map replay (decodeFile ((encodeFile rs).take n)) =
      .ok (replay (rs.take k)) := by
  obtain ⟨k, hk⟩ := decodeFile_prefix rs n h
  refine ⟨k, ?_⟩
  rw [hk]
  simp [Except.map]

end Cairn
