/-
One writer per shard. No global mutex.

`ShardSet` owns an optional `DB` per shard id. A put, delete, or commit
computes `shardOf` and takes that `DB`'s mutex only. Two commits on
different shards do not share a lock. A batch whose keys fall in more
than one shard is rejected, here and again inside `DB.commit`.

`iterate` reads one snapshot per shard and merges them with `mergeAll`.
The reads are not one picture: a commit can land on shard 1 after shard 0
was read and before shard 1 was. The result is the sorted merge of those
views. It is not a global snapshot and it is not a serial order across
shards. Keys of one epoch sit in one shard (`key_one_shard`), so the merge
does not have to pick a winner between two homes.

`Directory` says whether the shard is local. A remote shard goes through
`remote`, a function of the same shape a socket handler would call
(`ShardReq` / `ShardResp`). The default throws. `serve` is the other side:
what this host does with a request for a shard it owns. Replication is
`pushLog`: `planCatchup` plus `Mailbox.send`. The follower applies it with
`DB.follow`. Nothing here dials a network.

Files: `openFiles` uses `dir/shard-<id>.cairn`, one store per shard. A crash
of one file is that shard's prefix (`crash_shard_independent`). The other
files are not rewritten.
-/

import Cairn.DB
import Cairn.Directory
import Cairn.ShardModel

open System

namespace Cairn

structure ShardSet where
  host : HostId
  epoch : IO.Ref Epoch
  directory : IO.Ref Directory
  slots : Array (Option DB)
  remote : IO.Ref (NodeId → ShardReq → IO ShardResp)

def ShardSet.shardCount (s : ShardSet) : Nat :=
  s.slots.size

def rejectRemote (_dst : NodeId) (_req : ShardReq) : IO ShardResp :=
  throw (IO.userError "remote shard")

private def fresh (epoch : Epoch) (host : HostId) (slots : Array (Option DB))
    (dir : Directory) : IO ShardSet := do
  let epochRef ← IO.mkRef epoch
  let directory ← IO.mkRef dir
  let remote ← IO.mkRef rejectRemote
  return { host, epoch := epochRef, directory, slots, remote }

/-- Every shard of `epoch` is a memory `DB` on `host`. `epoch.bounds.length + 1` shards. -/
def ShardSet.openMem (epoch : Epoch) (host : HostId := { n := 0 }) : IO ShardSet := do
  let n := epoch.bounds.length + 1
  let mut slots : Array (Option DB) := #[]
  for _ in [0:n] do
    slots := slots.push (some (← DB.openMem epoch))
  fresh epoch host slots (Directory.local host n)

/-- One file per shard: `dir/shard-<id>.cairn`. Creating the file data-syncs it and fsyncs the directory. -/
def ShardSet.openFiles (dir : FilePath) (epoch : Epoch) (host : HostId := { n := 0 }) : IO ShardSet := do
  let n := epoch.bounds.length + 1
  let mut slots : Array (Option DB) := #[]
  for i in [0:n] do
    let path := FilePath.mk (dir.toString ++ s!"/shard-{i}.cairn")
    slots := slots.push (some (← DB.openFile path epoch))
  fresh epoch host slots (Directory.local host n)

/--
Slots for every shard id, but `DB`s only for `ids`. The directory on return
owns just those ids; publish the others before routing to them.
-/
def ShardSet.openHosted (epoch : Epoch) (host : HostId) (ids : List Nat) : IO ShardSet := do
  let n := epoch.bounds.length + 1
  let mut slots : Array (Option DB) := #[]
  for i in [0:n] do
    if ids.contains i then
      slots := slots.push (some (← DB.openMem epoch))
    else
      slots := slots.push none
  let owners := ids.map fun s => ShardOwner.primary s host
  fresh epoch host slots { gen := 0, owners := owners }

def ShardSet.shardId (s : ShardSet) (k : FitBytes) : IO Nat := do
  let e ← s.epoch.get
  return shardOf e.bounds k.bytes

def ShardSet.locate (s : ShardSet) (shard : Nat) : IO Locate := do
  return (← s.directory.get).locate s.host shard

private def slot (s : ShardSet) (shard : Nat) : IO DB := do
  match s.slots[shard]? with
  | some (some db) => return db
  | _ => throw (IO.userError "shard not hosted")

/-- Apply a request to a shard this host owns. A transport handler calls this. -/
def ShardSet.serve (s : ShardSet) (shard : Nat) (req : ShardReq) : IO ShardResp := do
  match ← s.locate shard with
  | .here _ =>
      try
        let db ← slot s shard
        match req with
        | .get k => return .value (← db.get k)
        | .commit ops =>
            db.commit ops
            return .ack
        | .commitMany batches =>
            db.commitMany batches
            return .ack
        | .snapshot => return .view (← db.iterate)
      catch e =>
        return .err e.toString
  | .remote _ => return .err "not the owner"
  | .missing => return .err "shard has no owner"

def ShardSet.get (s : ShardSet) (k : FitBytes) : IO (Option FitBytes) := do
  let id ← s.shardId k
  match ← s.locate id with
  | .here _ =>
      let db ← slot s id
      db.get k
  | .remote leader =>
      match ← (← s.remote.get) leader (.get k) with
      | .value v => return v
      | .err msg => throw (IO.userError msg)
      | _ => throw (IO.userError "bad reply")
  | .missing => throw (IO.userError "shard has no owner")

def ShardSet.commit (s : ShardSet) (ops : List Op) : IO Unit := do
  let e ← s.epoch.get
  match ops with
  | [] => throw (IO.userError "empty batch")
  | op :: _ =>
      if sameShard e.bounds ops = false then
        throw (IO.userError "cross-shard batch")
      let id := shardOf e.bounds op.key.bytes
      match ← s.locate id with
      | .here _ =>
          let db ← slot s id
          db.commit ops
      | .remote leader =>
          match ← (← s.remote.get) leader (.commit ops) with
          | .ack => pure ()
          | .err msg => throw (IO.userError msg)
          | _ => throw (IO.userError "bad reply")
      | .missing => throw (IO.userError "shard has no owner")

/-- One segment, one `sync`, on the single shard that owns every key. -/
def ShardSet.commitMany (s : ShardSet) (batches : List (List Op)) : IO Unit := do
  let e ← s.epoch.get
  let ops := batches.flatten
  match ops with
  | [] => throw (IO.userError "empty batch")
  | op :: _ =>
      if sameShard e.bounds ops = false then
        throw (IO.userError "cross-shard batch")
      let id := shardOf e.bounds op.key.bytes
      match ← s.locate id with
      | .here _ =>
          let db ← slot s id
          db.commitMany batches
      | .remote leader =>
          match ← (← s.remote.get) leader (.commitMany batches) with
          | .ack => pure ()
          | .err msg => throw (IO.userError msg)
          | _ => throw (IO.userError "bad reply")
      | .missing => throw (IO.userError "shard has no owner")

def ShardSet.put (s : ShardSet) (k v : FitBytes) : IO Unit :=
  s.commit [.put k v]

def ShardSet.delete (s : ShardSet) (k : FitBytes) : IO Unit :=
  s.commit [.del k]

private def fit (str : String) : IO FitBytes := do
  match FitBytes.ofString? str with
  | some f => return f
  | none => throw (IO.userError "string does not fit in a UInt32 length")

def ShardSet.putStr (s : ShardSet) (k v : String) : IO Unit := do
  s.put (← fit k) (← fit v)

def ShardSet.getStr (s : ShardSet) (k : String) : IO (Option String) := do
  match ← s.get (← fit k) with
  | none => return none
  | some v => return String.fromUTF8? v.bytes.toByteArray

def ShardSet.deleteStr (s : ShardSet) (k : String) : IO Unit := do
  s.delete (← fit k)

/-- One shard's snapshot. Independent of the other shards. -/
def ShardSet.localEntries (s : ShardSet) (shard : Nat) : IO (List (FitBytes × FitBytes)) := do
  let db ← slot s shard
  db.iterate

/--
Sorted merge of one snapshot per shard.

There is no global snapshot. Each part is that shard's `View` at the moment
it was read. A commit on another shard can land in between. There is no
serial order between those views. The merge is `mergeAll` / `clusterEntries`:
sorted by key, and it contains exactly the entries of the parts that were read.
-/
def ShardSet.iterate (s : ShardSet) : IO (List (FitBytes × FitBytes)) := do
  let e ← s.epoch.get
  let n := e.bounds.length + 1
  let mut parts : List (List (FitBytes × FitBytes)) := []
  for i in [0:n] do
    match ← s.locate i with
    | .here _ =>
        parts := parts ++ [← s.localEntries i]
    | .remote leader =>
        match ← (← s.remote.get) leader .snapshot with
        | .view es => parts := parts ++ [es]
        | .err msg => throw (IO.userError msg)
        | _ => throw (IO.userError "bad reply")
    | .missing => throw (IO.userError "shard has no owner")
  return mergeAll parts

def ShardSet.readLog (s : ShardSet) (shard : Nat) : IO (List Record) := do
  let db ← slot s shard
  db.readLog

/-- Publish a new owner. Bumps the directory generation. Does not move bytes. -/
def ShardSet.publish (s : ShardSet) (o : ShardOwner) : IO Unit := do
  let d ← s.directory.get
  s.directory.set (d.reassign o)

def ShardSet.hostView (s : ShardSet) : IO ShardHost := do
  return (← s.directory.get).hostView s.host

/--
Point every local `DB` at `epoch` and publish it for routing.
The slot count must already match `bounds.length + 1`. This does not move
entries. A split still goes through `moved` and `DB.adopt` on each shard
before the bounds change. Not atomic with in-flight commits.
-/
def ShardSet.setEpoch (s : ShardSet) (epoch : Epoch) : IO Unit := do
  if epoch.bounds.length + 1 ≠ s.slots.size then
    throw (IO.userError "epoch width does not match hosted slots")
  for slot in s.slots do
    match slot with
    | some db => db.setEpoch epoch
    | none => pure ()
  s.epoch.set epoch

/--
Send one shard's log to `dst`. `follower` is the log a heartbeat would have
reported. Epoch mismatch throws and sends nothing. The follower applies the
drained `Rpc` with `DB.follow`.
-/
def ShardSet.pushLog (s : ShardSet) (box : Mailbox) (shard : Nat) (follower : Replica)
    (dst : NodeId) : IO Unit := do
  let db ← slot s shard
  let v ← db.snapshot
  let leader : Replica := { epochGen := v.epoch.gen, log := v.records }
  match planCatchup follower leader with
  | none => throw (IO.userError "epoch mismatch")
  | some plan =>
      let src : NodeId := { shard := shard, replica := 0 }
      box.send src dst (plan.rpc leader.epochGen)

def ShardSet.close (s : ShardSet) : IO Unit := do
  for slot in s.slots do
    match slot with
    | some db => db.close
    | none => pure ()

end Cairn
