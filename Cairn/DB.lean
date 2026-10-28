/-
Single-writer database.

Readers call `IO.Ref.get` on one immutable `View` (tree, newest-first log, next LSN, epoch).
`IO.Ref.set` is a `swap` of that pointer; the Lean runtime documents `swap` as
atomic, so a reader sees the old view or the new one.

The writer mutex admits one commit at a time. Admission order is the serial
order of `Snapshot.Hist`. The lock is not re-entrant. The view is published
only after `append` and `sync`. On the file backend `sync` is a data barrier
(`fdatasync` / `F_FULLFSYNC`), not `Handle.flush`.

A batch is one record, and it must sit in a single shard (`sameShard`). An
empty batch is rejected. There is no cross-shard transaction.

`adopt` is the local move/split step: replace the log with a snapshot and
publish the new epoch in the same view. It does not run a consensus protocol.
-/

import Std.Sync.Mutex
import Cairn.Store
import Cairn.Log
import Cairn.Range
import Cairn.Router
import Cairn.Transport

open System

namespace Cairn

structure View where
  index : Map
  /-- Committed records, newest at the head. `records` is oldest first. -/
  revLog : List Record
  nextLsn : UInt64
  epoch : Epoch

/-- Chronological log. The stored spine stays newest-first so a commit can cons. -/
def View.records (v : View) : List Record :=
  v.revLog.reverse

structure DB where
  store : Store
  view : IO.Ref View
  closed : IO.Ref Bool
  writer : Std.Mutex Unit

def DB.snapshot (db : DB) : IO View :=
  db.view.get

def DB.get (db : DB) (k : FitBytes) : IO (Option FitBytes) := do
  return Cairn.get (← db.snapshot).index k

def DB.iterate (db : DB) : IO (List (FitBytes × FitBytes)) := do
  return entries (← db.snapshot).index

/--
One snapshot. Inclusive `lo`, exclusive `hi`, strict `after` cursor.
`pageCursor` is the last key when the page is full.
-/
def DB.range (db : DB) (lo hi after : Option FitBytes) (limit : Nat) :
    IO (List (FitBytes × FitBytes) × Option FitBytes) := do
  let rows := rangeHits (← db.snapshot).index lo hi after
  return (rows.take limit, pageCursor limit rows)

/-- Keys whose bytes start with `p`, same cursor rule as `range`. -/
def DB.prefix (db : DB) (p : Bytes) (after : Option FitBytes) (limit : Nat) :
    IO (List (FitBytes × FitBytes) × Option FitBytes) := do
  let rows := prefixHits (← db.snapshot).index p after
  return (rows.take limit, pageCursor limit rows)

def DB.readLog (db : DB) : IO (List Record) := do
  return (← db.snapshot).records

def DB.readEpoch (db : DB) : IO Epoch := do
  return (← db.snapshot).epoch

private def appendFrame (store : Store) (payload : Bytes) : IO Unit := do
  if payload.length ≥ UInt32.size then
    throw (IO.userError "record does not fit")
  store.append (encodeFrame segMagic payload)

private def commitNow (db : DB) (ops : List Op) : IO Unit := do
  if ← db.closed.get then
    throw (IO.userError "closed")
  if ops.isEmpty then
    throw (IO.userError "empty batch")
  let some batch := Batch.ofList? ops
    | throw (IO.userError "batch too large")
  let v ← db.view.get
  if sameShard v.epoch.bounds ops = false then
    throw (IO.userError "cross-shard batch")
  let record : Record := Record.ofBatch v.nextLsn batch
  appendFrame db.store (encodeRecord record)
  db.store.sync
  db.view.set {
    index := applyBatch v.index ops
    revLog := record :: v.revLog
    nextLsn := v.nextLsn + 1
    epoch := v.epoch
  }

private def commitManyNow (db : DB) (batches : List (List Op)) : IO Unit := do
  if ← db.closed.get then
    throw (IO.userError "closed")
  if batches.isEmpty then
    throw (IO.userError "empty batch")
  let ops := batches.flatten
  if ops.isEmpty then
    throw (IO.userError "empty batch")
  let v ← db.view.get
  if sameShard v.epoch.bounds ops = false then
    throw (IO.userError "cross-shard batch")
  let mut lsn := v.nextLsn
  -- Newest of this group at the head. `++` below copies only this group.
  let mut built : List Record := []
  for batchOps in batches do
    if batchOps.isEmpty then
      throw (IO.userError "empty batch")
    let some batch := Batch.ofList? batchOps
      | throw (IO.userError "batch too large")
    built := Record.ofBatch lsn batch :: built
    lsn := lsn + 1
  let recs := built.reverse
  appendFrame db.store (encodeLog recs)
  db.store.sync
  db.view.set {
    index := applyBatch v.index ops
    revLog := built ++ v.revLog
    nextLsn := lsn
    epoch := v.epoch
  }

def DB.commit (db : DB) (ops : List Op) : IO Unit :=
  db.writer.atomically fun _ => liftM (commitNow db ops)

/--
Run `f` under the writer lock on the current view. The ops it returns are
one batch. Empty ops publish nothing. `commitNow` still rejects a batch
whose keys are not in this shard.
-/
def DB.transact {α : Type} (db : DB) (f : View → IO (List Op × α)) : IO α :=
  db.writer.atomically fun _ => liftM do
    if ← db.closed.get then
      throw (IO.userError "closed")
    let v ← db.view.get
    let (ops, ans) ← f v
    if ops.isEmpty then
      return ans
    commitNow db ops
    return ans

inductive Edit where
  | keep
  | put (v : FitBytes)
  | del

/--
Read and maybe write one key under the writer lock. `f` sees the value from
that locked view. One key is one shard.
-/
def DB.modifyKey {α : Type} (db : DB) (k : FitBytes)
    (f : Option FitBytes → Edit × α) : IO α :=
  db.writer.atomically fun _ => liftM do
    if ← db.closed.get then
      throw (IO.userError "closed")
    let v ← db.view.get
    let cur := Cairn.get v.index k
    let (edit, ans) := f cur
    match edit with
    | .keep => return ans
    | .del =>
        match cur with
        | none => return ans
        | some _ =>
            commitNow db [.del k]
            return ans
    | .put nv =>
        if cur == some nv then
          return ans
        else
          commitNow db [.put k nv]
          return ans

/-- Several batches, one segment, one `sync`. A crash drops the whole group or keeps it. -/
def DB.commitMany (db : DB) (batches : List (List Op)) : IO Unit :=
  db.writer.atomically fun _ => liftM (commitManyNow db batches)

def DB.put (db : DB) (k v : FitBytes) : IO Unit :=
  db.commit [.put k v]

def DB.delete (db : DB) (k : FitBytes) : IO Unit :=
  db.commit [.del k]

private def fit (s : String) : IO FitBytes := do
  match FitBytes.ofString? s with
  | some f => return f
  | none => throw (IO.userError "string does not fit in a UInt32 length")

def DB.putStr (db : DB) (k v : String) : IO Unit := do
  db.put (← fit k) (← fit v)

def DB.deleteStr (db : DB) (k : String) : IO Unit := do
  db.delete (← fit k)

def DB.getStr (db : DB) (k : String) : IO (Option String) := do
  match ← db.get (← fit k) with
  | none => return none
  | some v => return String.fromUTF8? v.bytes.toByteArray

private def compactNow (db : DB) : IO Unit := do
  if ← db.closed.get then
    throw (IO.userError "closed")
  let v ← db.view.get
  let rs := compactRecords v.index v.nextLsn
  db.store.replaceAll (encodeFile rs)
  let next :=
    match rs.getLast? with
    | some r => r.lsn + 1
    | none => v.nextLsn
  db.view.set { v with revLog := rs.reverse, nextLsn := next }

def DB.compact (db : DB) : IO Unit :=
  db.writer.atomically fun _ => liftM (compactNow db)

private def followNow (db : DB) (rpc : Rpc) : IO RpcReply := do
  if ← db.closed.get then
    throw (IO.userError "closed")
  let v ← db.view.get
  let applied := applyRpc v.epoch.gen v.records rpc
  match applied.1 with
  | .ok _ =>
      match rpc with
      | .appendEntries _ _ entries =>
          if entries.isEmpty then
            pure ()
          else
            appendFrame db.store (encodeLog entries)
            db.store.sync
      | .installSnapshot _ _ =>
          db.store.replaceAll (encodeFile applied.2)
      let next :=
        match applied.2.getLast? with
        | some r => r.lsn + 1
        | none => 0
      db.view.set {
        index := replay applied.2
        revLog := applied.2.reverse
        nextLsn := next
        epoch := v.epoch
      }
      return applied.1
  | .epochMismatch => return applied.1
  | .rejected => return applied.1

/-- Apply a replication message. Epoch mismatch and a bad `prev` leave the log in place. -/
def DB.follow (db : DB) (rpc : Rpc) : IO RpcReply :=
  db.writer.atomically fun _ => liftM (followNow db rpc)

def DB.followSuffix (db : DB) (gen prev : Nat) (entries : List Record) : IO RpcReply :=
  db.follow (.appendEntries gen prev entries)

def DB.installSnapshot (db : DB) (gen : Nat) (records : List Record) : IO RpcReply :=
  db.follow (.installSnapshot gen records)

private def adoptNow (db : DB) (epoch : Epoch) (records : List Record) : IO Unit := do
  if ← db.closed.get then
    throw (IO.userError "closed")
  db.store.replaceAll (encodeFile records)
  let next :=
    match records.getLast? with
    | some r => r.lsn + 1
    | none => 0
  db.view.set {
    index := replay records
    revLog := records.reverse
    nextLsn := next
    epoch := epoch
  }

/--
Replace this node's log with `records` and publish `epoch` in one view.
This is the local half of a shard move. It trusts the caller.
-/
def DB.adopt (db : DB) (epoch : Epoch) (records : List Record) : IO Unit :=
  db.writer.atomically fun _ => liftM (adoptNow db epoch records)

private def setEpochNow (db : DB) (epoch : Epoch) : IO Unit := do
  if ← db.closed.get then
    throw (IO.userError "closed")
  let v ← db.view.get
  db.view.set { v with epoch := epoch }

def DB.setEpoch (db : DB) (epoch : Epoch) : IO Unit :=
  db.writer.atomically fun _ => liftM (setEpochNow db epoch)

private def closeNow (db : DB) : IO Unit := do
  db.store.sync
  db.closed.set true

def DB.close (db : DB) : IO Unit :=
  db.writer.atomically fun _ => liftM (closeNow db)

def DB.openStore (store : Store) (epoch : Epoch := Epoch.single) : IO DB := do
  let bytes ← store.readAll
  let s := scan bytes
  let rs ←
    match s.kind with
    | .reject => throw (IO.userError "not a cairn file")
    | .corrupt => throw (IO.userError "corrupt log")
    | .clean => pure s.records
    | .torn =>
        let kept := if s.consumed = 0 then encodeHeader else bytes.take s.consumed
        if bytes != kept then
          store.replaceAll kept
        pure s.records
  let next : UInt64 :=
    match rs.getLast? with
    | some r => r.lsn + 1
    | none => 0
  let view ← IO.mkRef {
    index := replay rs
    revLog := rs.reverse
    nextLsn := next
    epoch := epoch
  }
  let closed ← IO.mkRef false
  let writer ← Std.Mutex.new ()
  return { store, view, closed, writer := writer }

def DB.openMem (epoch : Epoch := Epoch.single) : IO DB := do
  let chunks ← IO.mkRef ([] : List Bytes)
  DB.openStore (Store.mem chunks) epoch

def DB.openFile (path : FilePath) (epoch : Epoch := Epoch.single) : IO DB := do
  DB.openStore (← Store.openFile path) epoch

/--
Open a file, truncating a torn tail or a mid-log corruption to the last
valid prefix. A file that is not a cairn file is left in place and the call
fails. `openFile` itself does not repair: corruption is an error.
-/
def DB.openFileRepair (path : FilePath) (epoch : Epoch := Epoch.single) : IO DB := do
  Store.repairFile path
  DB.openFile path epoch

end Cairn
