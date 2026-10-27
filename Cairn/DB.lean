/-
Single-writer database.

Readers call `IO.Ref.get` on one immutable `View` (map, log, next LSN, epoch).
`IO.Ref.set` is a `swap` of that pointer; the Lean runtime documents `swap` as
atomic, so a reader sees the old view or the new one.

The writer mutex admits one commit at a time. Admission order is the serial
order of `Snapshot.Hist`. The lock is not re-entrant. The view is published
only after `append` and `sync`.

A batch is one record, and it must sit in a single shard (`sameShard`). An
empty batch is rejected. There is no cross-shard transaction.

`adopt` is the local move/split step: replace the log with a snapshot and
publish the new epoch in the same view. It does not run a consensus protocol.
-/

import Std.Sync.Mutex
import Cairn.Store
import Cairn.Log
import Cairn.Router
import Cairn.Transport

open System

namespace Cairn

structure View where
  index : Map
  log : List Record
  nextLsn : UInt64
  epoch : Epoch

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

def DB.readLog (db : DB) : IO (List Record) := do
  return (← db.snapshot).log

def DB.readEpoch (db : DB) : IO Epoch := do
  return (← db.snapshot).epoch

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
  db.store.append (encodeRecord record)
  db.store.sync
  db.view.set {
    index := applyBatch v.index ops
    log := v.log ++ [record]
    nextLsn := v.nextLsn + 1
    epoch := v.epoch
  }

def DB.commit (db : DB) (ops : List Op) : IO Unit :=
  db.writer.atomically fun _ => liftM (commitNow db ops)

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
  db.view.set { v with log := rs, nextLsn := next }

def DB.compact (db : DB) : IO Unit :=
  db.writer.atomically fun _ => liftM (compactNow db)

private def followNow (db : DB) (rpc : Rpc) : IO RpcReply := do
  if ← db.closed.get then
    throw (IO.userError "closed")
  let v ← db.view.get
  let applied := applyRpc v.epoch.gen v.log rpc
  match applied.1 with
  | .ok _ =>
      match rpc with
      | .appendEntries _ _ entries =>
          for r in entries do
            db.store.append (encodeRecord r)
          db.store.sync
      | .installSnapshot _ _ =>
          db.store.replaceAll (encodeFile applied.2)
      let next :=
        match applied.2.getLast? with
        | some r => r.lsn + 1
        | none => 0
      db.view.set {
        index := replay applied.2
        log := applied.2
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
    log := records
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
  let rs ←
    match decodeFile bytes with
    | .ok rs => pure rs
    | .error msg => throw (IO.userError msg)
  let canon := encodeFile rs
  if bytes != canon then
    store.replaceAll canon
  let next : UInt64 :=
    match rs.getLast? with
    | some r => r.lsn + 1
    | none => 0
  let view ← IO.mkRef {
    index := replay rs
    log := rs
    nextLsn := next
    epoch := epoch
  }
  let closed ← IO.mkRef false
  let writer ← Std.Mutex.new ()
  return { store, view, closed, writer := writer }

def DB.openMem (epoch : Epoch := Epoch.single) : IO DB := do
  let buf ← IO.mkRef ([] : Bytes)
  DB.openStore (Store.mem buf) epoch

def DB.openFile (path : FilePath) (epoch : Epoch := Epoch.single) : IO DB := do
  DB.openStore (← Store.openFile path) epoch

end Cairn
