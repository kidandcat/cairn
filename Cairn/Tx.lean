/-
Serializable transactions inside one shard.

`transact` runs the body under that shard's writer mutex. Every read and
write goes through `Tx`, so a read sees the body's own pending writes.
The body is one batch at the end, or nothing if it throws or touches a key
whose `shardOf` is not this shard.

The pure model is `TxRun`. A successful run is `applyBatch` of the ops it
produced, on the map it started from. An `abort` step produces no map.
The mutex is what orders two bodies; that ordering is not a theorem.
The body should be short: it holds the shard lock. No slow I/O inside.
-/

import Cairn.Log
import Cairn.Map
import Cairn.RangeWalk
import Cairn.Router

namespace Cairn

/-- Warn when a body holds the shard lock longer than this. It still commits. -/
def txWarnNs : Nat := 50000000

structure Tx where
  base : Map
  pending : IO.Ref (List Op)
  bounds : List Bytes
  home : Nat
  /-- LSN this body will commit as. Stable: the shard lock is held. -/
  nextLsn : UInt64

def Tx.seen (tx : Tx) : IO Map := do
  return applyBatch tx.base (← tx.pending.get)

private def guardKey (tx : Tx) (k : FitBytes) : IO Unit := do
  if shardOf tx.bounds k.bytes ≠ tx.home then
    throw (IO.userError "key is on another shard")

def Tx.get (tx : Tx) (k : FitBytes) : IO (Option FitBytes) := do
  return Cairn.get (← tx.seen) k

def Tx.put (tx : Tx) (k v : FitBytes) : IO Unit := do
  guardKey tx k
  let ops ← tx.pending.get
  tx.pending.set (ops ++ [.put k v])

def Tx.delete (tx : Tx) (k : FitBytes) : IO Unit := do
  guardKey tx k
  let ops ← tx.pending.get
  tx.pending.set (ops ++ [.del k])

/--
Write a key into this shard's file without the `shardOf` check.
Outbox and progress keys live in the file of the shard that owns the
batch. `ShardSet.get` will not route to them. Propagators read that file.
-/
def Tx.putLocal (tx : Tx) (k v : FitBytes) : IO Unit := do
  let ops ← tx.pending.get
  tx.pending.set (ops ++ [.put k v])

def Tx.deleteLocal (tx : Tx) (k : FitBytes) : IO Unit := do
  let ops ← tx.pending.get
  tx.pending.set (ops ++ [.del k])

def Tx.range (tx : Tx) (lo hi after : Option FitBytes) (limit : Nat) :
    IO (List (FitBytes × FitBytes) × Option FitBytes) := do
  let page := rangeWalk (← tx.seen) lo hi after limit
  return (page, pageCursor limit page)

def Tx.prefix (tx : Tx) (p : Bytes) (after : Option FitBytes) (limit : Nat) :
    IO (List (FitBytes × FitBytes) × Option FitBytes) := do
  let page := prefixWalk (← tx.seen) p after limit
  return (page, pageCursor limit page)

/-! ## Pure run

A step list is one body. `abort` throws away every step, including the ones
already applied in the scratch map. Success is the batch applied to the start.
-/

inductive TxStep where
  | put (k v : FitBytes)
  | del (k : FitBytes)
  | abort
  deriving Repr

namespace TxRun

def go (seen : Map) : List TxStep → Except Unit (Map × List Op)
  | [] => .ok (seen, [])
  | .abort :: _ => .error ()
  | .put k v :: rest =>
      match go (insert seen k v) rest with
      | .error e => .error e
      | .ok (m, ops) => .ok (m, .put k v :: ops)
  | .del k :: rest =>
      match go (remove seen k) rest with
      | .error e => .error e
      | .ok (m, ops) => .ok (m, .del k :: ops)

def run (m : Map) (steps : List TxStep) : Except Unit (Map × List Op) :=
  go m steps

theorem go_abort (seen : Map) (rest : List TxStep) :
    go seen (.abort :: rest) = .error () := rfl

theorem go_ok_apply (seen : Map) (steps : List TxStep) (m : Map) (ops : List Op)
    (h : go seen steps = .ok (m, ops)) : m = applyBatch seen ops := by
  induction steps generalizing seen m ops with
  | nil =>
      simp [go] at h
      rcases h with ⟨rfl, rfl⟩
      simp
  | cons step rest ih =>
      cases step with
      | abort => simp [go] at h
      | put k v =>
          simp [go] at h
          split at h
          · contradiction
          · next m1 ops1 heq =>
              rcases h with ⟨rfl, rfl⟩
              have hm := ih (insert seen k v) m ops1 heq
              simp [applyBatch, applyOp, hm]
      | del k =>
          simp [go] at h
          split at h
          · contradiction
          · next m1 ops1 heq =>
              rcases h with ⟨rfl, rfl⟩
              have hm := ih (remove seen k) m ops1 heq
              simp [applyBatch, applyOp, hm]

theorem run_ok_apply (start : Map) (steps : List TxStep) (m : Map) (ops : List Op)
    (h : run start steps = .ok (m, ops)) : m = applyBatch start ops :=
  go_ok_apply start steps m ops h

theorem run_abort (start : Map) (rest : List TxStep) :
    run start (.abort :: rest) = .error () := rfl

theorem run_abort_after (start : Map) (pre rest : List TxStep) :
    run start (pre ++ .abort :: rest) = .error () := by
  induction pre generalizing start with
  | nil => rfl
  | cons step pre ih =>
      cases step with
      | abort => rfl
      | put k v =>
          have herr : go (insert start k v) (pre ++ .abort :: rest) = .error () := by
            simpa [run] using ih (insert start k v)
          simp [run, go, herr]
      | del k =>
          have herr : go (remove start k) (pre ++ .abort :: rest) = .error () := by
            simpa [run] using ih (remove start k)
          simp [run, go, herr]

theorem read_own_write (start : Map) (k v : FitBytes) :
    run start [.put k v] = .ok (insert start k v, [.put k v]) := by
  simp [run, go]

/-- Two successful bodies in order are one batch, then the other. -/
theorem compose (seen : Map) (a b : List TxStep) (m1 : Map) (ops1 : List Op)
    (m2 : Map) (ops2 : List Op)
    (h1 : go seen a = .ok (m1, ops1)) (h2 : go m1 b = .ok (m2, ops2)) :
    go seen (a ++ b) = .ok (m2, ops1 ++ ops2) := by
  induction a generalizing seen m1 ops1 with
  | nil =>
      simp [go] at h1
      rcases h1 with ⟨rfl, rfl⟩
      simpa using h2
  | cons step rest ih =>
      cases step with
      | abort => simp [go] at h1
      | put k v =>
          simp [go] at h1
          split at h1
          · contradiction
          · next m0 ops0 heq =>
              rcases h1 with ⟨rfl, rfl⟩
              have hrest := ih (insert seen k v) m1 ops0 heq h2
              simp [go, hrest]
      | del k =>
          simp [go] at h1
          split at h1
          · contradiction
          · next m0 ops0 heq =>
              rcases h1 with ⟨rfl, rfl⟩
              have hrest := ih (remove seen k) m1 ops0 heq h2
              simp [go, hrest]

end TxRun

end Cairn
