/-
What a node exchanges. There is no socket here.

`Rpc` is the message a future transport would carry. The bytes of a record are
already `encodeRecord`; a payload is a list of those records (`encodeLog`).
`applyRpc` is the local apply step:

* `appendEntries` appends when the epoch matches and `prev` is the follower's
  log length. Otherwise the log is left alone.
* `installSnapshot` replaces the log when the epoch matches.

Not in this version, on purpose:

* no network and no codecs beyond the record frame
* no Raft terms, votes, or election timeout
* no quorum and no commit index
* no membership protocol
* no automatic rebalancer

`InProc` is an in-process mailbox so tests can pass those messages around
without FFI. A real transport would implement `send`/`drain` over bytes.
-/

import Cairn.Record

namespace Cairn

structure NodeId where
  shard : Nat
  replica : Nat
  deriving DecidableEq, Repr, BEq

inductive Rpc where
  | appendEntries (epochGen : Nat) (prev : Nat) (entries : List Record)
  | installSnapshot (epochGen : Nat) (records : List Record)

inductive RpcReply where
  | ok (matched : Nat)
  | epochMismatch
  | rejected
  deriving Repr, BEq

def applyRpc (epochGen : Nat) (log : List Record) : Rpc → RpcReply × List Record
  | .appendEntries gen prev entries =>
      if gen ≠ epochGen then
        (.epochMismatch, log)
      else if prev ≠ log.length then
        (.rejected, log)
      else
        (.ok (log.length + entries.length), log ++ entries)
  | .installSnapshot gen records =>
      if gen ≠ epochGen then
        (.epochMismatch, log)
      else
        (.ok records.length, records)

theorem append_extends (gen : Nat) (log entries : List Record) :
    (applyRpc gen log (.appendEntries gen log.length entries)).2 = log ++ entries := by
  simp [applyRpc]

theorem install_replaces (gen : Nat) (log records : List Record) :
    (applyRpc gen log (.installSnapshot gen records)).2 = records := by
  simp [applyRpc]

theorem append_rejects_epoch (gen here : Nat) (h : gen ≠ here) (log : List Record)
    (prev : Nat) (entries : List Record) :
    (applyRpc here log (.appendEntries gen prev entries)).2 = log := by
  simp [applyRpc, h]

structure Envelope where
  src : NodeId
  dst : NodeId
  rpc : Rpc

structure InProc where
  box : IO.Ref (List Envelope)

def InProc.new : BaseIO InProc := do
  return { box := ← IO.mkRef [] }

def InProc.send (t : InProc) (src dst : NodeId) (rpc : Rpc) : BaseIO Unit :=
  t.box.modify fun q => q ++ [{ src, dst, rpc }]

def InProc.drain (t : InProc) (dst : NodeId) : BaseIO (List Rpc) := do
  let q ← t.box.get
  let mine := q.filter fun e => e.dst == dst
  let rest := q.filter fun e => e.dst != dst
  t.box.set rest
  return mine.map (·.rpc)

end Cairn
