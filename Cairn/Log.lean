/-
Logical log. A record is one atomic batch. Replay folds batches onto the map.

Compaction emits one put per surviving key, oldest first, so a fresh replay
rebuilds the same list. A crash is a prefix of the encoded byte string; decoding
it yields a prefix of the committed records.
-/

import Cairn.Record
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
  rs.foldl (fun m r => applyBatch m r.ops) []

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
  nodup_replay_from [] rs nodup_nil

/-! ## Compaction -/

/-- Oldest key first, so replay conses the newest entry back to the head. -/
def toPuts : Map → List Op
  | [] => []
  | (k, v) :: m => toPuts m ++ [.put k v]

theorem nodup_tail {e : FitBytes × FitBytes} {m : Map} (h : NodupKeys (e :: m)) : NodupKeys m := by
  cases h with
  | cons _ ht => exact ht

theorem nodup_head_fresh {e : FitBytes × FitBytes} {m : Map} (h : NodupKeys (e :: m)) :
    ∀ e' ∈ m, e.1.bytes ≠ e'.1.bytes := by
  cases h with
  | cons hf _ => exact hf

theorem remove_keeps (m : Map) (k : FitBytes)
    (h : ∀ e, e ∈ m → k.bytes ≠ e.1.bytes) : remove m k = m := by
  induction m with
  | nil => simp [remove]
  | cons e m ih =>
      have htail : ∀ e', e' ∈ m → k.bytes ≠ e'.1.bytes := by
        intro e' he
        exact h e' (List.mem_cons_of_mem _ he)
      have hpos : (!keyEq k e) = true := by
        have hne : k.bytes ≠ e.1.bytes := h e List.mem_cons_self
        cases hb : keyEq k e <;> simp_all [keyEq]
      simp only [remove, List.filter_cons, hpos]
      have ih' : m.filter (fun e => !keyEq k e) = m := by
        simpa [remove] using ih htail
      simp [ih']

theorem apply_toPuts (m : Map) (h : NodupKeys m) : applyBatch [] (toPuts m) = m := by
  induction m with
  | nil => simp [toPuts]
  | cons e m ih =>
      cases e with
      | mk k v =>
          have hm := nodup_tail h
          have hf := nodup_head_fresh h
          rw [toPuts, applyBatch_append, ih hm]
          have hrm : remove m k = m :=
            remove_keeps m k (fun e he => hf e he)
          simp [applyOp, insert, hrm]

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
    replay (recordsOf start ops) = applyBatch [] ops := by
  simpa [replay] using fold_records start ops []

def compactRecords (m : Map) (start : UInt64) : List Record :=
  recordsOf start (toPuts m)

theorem compact_eq (m : Map) (h : NodupKeys m) (start : UInt64) :
    replay (compactRecords m start) = m := by
  simp [compactRecords, replay_records, apply_toPuts m h]

theorem compact_roundtrip (m : Map) (h : NodupKeys m) (start : UInt64) :
    replay (decodeLog (encodeLog (compactRecords m start))) = m := by
  rw [decodeLog_encode, compact_eq m h start]

/-! ## Crash as a byte prefix -/

/--
Decoding a prefix of an encoded log is the replay of some prefix of the
committed records. A torn record is dropped whole; a batch is not split.
-/
theorem recovery_prefix (rs : List Record) (n : Nat) :
    ∃ k, Except.map replay (decodeFile ((encodeFile rs).take n)) =
      .ok (replay (rs.take k)) := by
  obtain ⟨k, hk⟩ := decodeFile_prefix rs n
  refine ⟨k, ?_⟩
  rw [hk]
  simp [Except.map]

end Cairn
