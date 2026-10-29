/-
Where a shard lives, and how its log is copied.

A host is a process. It serves zero or more shards. `Directory` is the
versioned map from shard id to the host that owns the leader, plus the
follower addresses. `reassign` bumps the generation. There is no membership
protocol here: a later layer calls `reassign` after the bytes have moved.

`NodeId` stays the mailbox address of one replica of one shard (the `InProc`
mailbox). `HostId` is the process that may own several of those addresses.
`Locate` is the branch a client takes: local `DB`, or a remote leader. The
remote arm is the seam a socket would fill. This file does not open one.

Replication is per shard and per log. `planCatchup` chooses `appendEntries`
or `installSnapshot` the same way `catchUp` does. `Mailbox` is the `send` /
`drain` shape `InProc` already has. A wire transport implements that shape
and nothing in `DB` changes.

Not here, on purpose: sockets, heartbeats, quorums, elections, and a
commit index. The follower length that `planCatchup` needs is something a
later heartbeat would report. The caller passes the follower log it has.
-/

import Cairn.Replica

namespace Cairn

/-- A process. One host may serve many shards. -/
structure HostId where
  n : Nat
  deriving DecidableEq, Repr, BEq

/-- Leader host and follower mailbox addresses for one shard. `NodeId` is the mailbox address. -/
structure ShardOwner where
  shard : Nat
  host : HostId
  leader : NodeId
  followers : List NodeId
  deriving DecidableEq, Repr

/-- Leader on `host`, replica 0, with the given followers. -/
def ShardOwner.primary (shard : Nat) (host : HostId) (followers : List NodeId := []) : ShardOwner where
  shard := shard
  host := host
  leader := { shard := shard, replica := 0 }
  followers := followers

/--
Versioned shard → owner map. `gen` increases on every `reassign`.
Readers observe one generation: `IO.Ref.get` of the whole structure.
Two publishes can race; this phase does not run membership concurrently
with itself. Data commits do not take this map's lock.
-/
structure Directory where
  gen : Nat
  owners : List ShardOwner
  deriving DecidableEq, Repr

def Directory.owner? (d : Directory) (shard : Nat) : Option ShardOwner :=
  d.owners.find? fun o => o.shard == shard

def Directory.reassign (d : Directory) (o : ShardOwner) : Directory where
  gen := d.gen + 1
  owners := o :: d.owners.filter fun x => x.shard != o.shard

def Directory.local (host : HostId) (n : Nat) : Directory where
  gen := 0
  owners := (List.range n).map fun s => ShardOwner.primary s host

/-- The shards `id` hosts under this directory. This is the host's assignment. -/
structure ShardHost where
  id : HostId
  serving : List Nat
  deriving DecidableEq, Repr

def Directory.hostView (d : Directory) (id : HostId) : ShardHost where
  id := id
  serving := (d.owners.filter fun o => o.host == id).map fun o => o.shard

/-- Where a request for `shard` goes, as seen from `self`. -/
inductive Locate where
  | here (shard : Nat)
  | remote (leader : NodeId)
  | missing
  deriving DecidableEq, Repr

def Directory.locate (d : Directory) (self : HostId) (shard : Nat) : Locate :=
  match d.owner? shard with
  | none => .missing
  | some o => if o.host = self then .here o.shard else .remote o.leader

theorem reassign_gen (d : Directory) (o : ShardOwner) :
    (d.reassign o).gen = d.gen + 1 := rfl

theorem reassign_owner (d : Directory) (o : ShardOwner) :
    (d.reassign o).owner? o.shard = some o := by
  simp [Directory.reassign, Directory.owner?]

theorem locate_here (d : Directory) (self : HostId) (o : ShardOwner)
    (h : d.owner? o.shard = some o) (hh : o.host = self) :
    d.locate self o.shard = .here o.shard := by
  simp [Directory.locate, h, hh]

theorem locate_remote (d : Directory) (self : HostId) (o : ShardOwner)
    (h : d.owner? o.shard = some o) (hh : o.host ≠ self) :
    d.locate self o.shard = .remote o.leader := by
  simp [Directory.locate, h, hh]

/-! ## Per-shard log route -/

/-- What the leader sends one follower. Same choice as `catchUp`. -/
inductive Catchup where
  | append (prev : Nat) (entries : List Record)
  | install (records : List Record)

def Catchup.rpc (gen : Nat) : Catchup → Rpc
  | .append prev entries => .appendEntries gen prev entries
  | .install records => .installSnapshot gen records

/--
`none` when the epochs differ: the follower is left untouched, as in `catchUp`.
A follower whose log is a prefix receives the missing suffix. Any other log
is replaced with the leader log.
-/
def planCatchup (follower leader : Replica) : Option Catchup :=
  if follower.epochGen != leader.epochGen then
    none
  else if follower.log.isPrefixOf leader.log then
    some (.append follower.log.length (leader.log.drop follower.log.length))
  else
    some (.install leader.log)

theorem plan_agrees (follower leader : Replica) (plan : Catchup)
    (h : follower.epochGen = leader.epochGen) (hp : planCatchup follower leader = some plan) :
    (applyRpc follower.epochGen follower.log (plan.rpc leader.epochGen)).2 =
      (catchUp follower leader).log := by
  unfold planCatchup at hp
  unfold catchUp
  have hne : (follower.epochGen != leader.epochGen) = false := by
    simp [h, bne]
  rw [hne] at hp
  rw [ite_eq_right (by decide)] at hp
  rw [hne, ite_eq_right (by decide)]
  by_cases hpre : follower.log.isPrefixOf leader.log = true
  · rw [ite_eq_left hpre] at hp
    rw [ite_eq_left hpre]
    cases hp
    have hprefix : follower.log <+: leader.log := List.isPrefixOf_iff_prefix.mp hpre
    obtain ⟨suf, hsuf⟩ := hprefix
    have hdrop : leader.log.drop follower.log.length = suf := by
      rw [← hsuf, List.drop_left]
    simp [Catchup.rpc, applyRpc, h, hdrop, hsuf]
  · rw [ite_eq_right hpre] at hp
    rw [ite_eq_right hpre]
    cases hp
    simp [Catchup.rpc, applyRpc, h]

/-- `send` / `drain`, the shape `InProc` already implements. A socket fills the same two fields. -/
structure Mailbox where
  send : NodeId → NodeId → Rpc → BaseIO Unit
  drain : NodeId → BaseIO (List Rpc)

def InProc.mailbox (t : InProc) : Mailbox where
  send := t.send
  drain := t.drain

/-
Client request a transport would carry to the host of one shard.
This is not `Rpc`. `Rpc` copies a log. `ShardReq` is a put, a get, or one
shard's snapshot. A cross-shard batch is still rejected by the receiver.
`snapshot` is that shard alone, not a cluster-wide picture.
-/
inductive ShardReq where
  | get (k : FitBytes)
  | commit (ops : List Op)
  | commitMany (batches : List (List Op))
  | snapshot
  deriving Repr

inductive ShardResp where
  | value (v : Option FitBytes)
  | ack
  | view (entries : List (FitBytes × FitBytes))
  | err (msg : String)
  deriving Repr

end Cairn
