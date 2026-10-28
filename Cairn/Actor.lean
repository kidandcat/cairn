/-
One actor per shard. Not a scheduler and not an actor per entity.

The durable inbox is the outbox of `Copy.propagate`: origin plus ticket, applied
inside one `transact`, with the progress mark in that same batch. The memory
mailbox is a bounded `Std.Channel`. `send` blocks when it is full. That is
the backpressure. A reply is another `send` the other way. There is no
synchronous call: the sender would wait while holding its turn, and the
receiver might be waiting for the sender. That cycle is a deadlock, so this
API does not offer it.

Reads do not enter the mailbox. `ShardSet.get` is still one `Ref.get` of an
immutable view.

If the loop throws, it is logged, the task sleeps with a short backoff, and
the next turn reads the log again from the progress mark. After `maxAttempts`
failures the head notice is copied to a dead-letter key and the mark moves
past it, so one poison message does not stall the shard.
-/

import Cairn.Copy
import Std.Sync.Channel

namespace Cairn

namespace ActorModel

/-- One message is one batch: a single op applied to the map. -/
def process (m : Map) (op : Op) : Map :=
  applyBatch m [op]

theorem process_one (m : Map) (op : Op) : process m op = applyOp m op := by
  simp [process, applyBatch, applyOp]

/-- The mailbox, in order, is the fold of those one-message transactions. -/
theorem process_fold (m : Map) (ops : List Op) :
    ops.foldl process m = applyBatch m ops := by
  induction ops generalizing m with
  | nil => simp [applyBatch]
  | cons op ops ih =>
      simp [process, applyBatch, ih]

end ActorModel

structure Msg where
  origin : Nat
  payload : FitBytes
  deriving Repr

def deadKey (src ticket : Nat) : Option FitBytes :=
  FitBytes.ofList? ([9] ++ beBytes 4 src ++ beBytes 8 ticket)

/--
Skip the oldest unapplied notice from `src` to `dst` and remember its payload.
Used when a handler has already failed `maxAttempts` times.
-/
def deadLetter (s : ShardSet) (src dst : Nat) : IO Bool := do
  let some pk := progKey src | return false
  let mark ← match ← s.localGet dst pk with
    | some v => pure (decodeNat v |>.getD 0)
    | none => pure 0
  let (rows, _) ← s.localPrefix src (outPrefix dst) none 16
  for e in rows do
    match ticketOf dst e.1, decodeNotice e.2.bytes with
    | some ticket, some note =>
        if mark < ticket then
          let some dk := deadKey src ticket | return false
          let some body := FitBytes.ofList? (encodeNotice note) | return false
          s.transactOn dst fun tx => do
            tx.putLocal dk body
            tx.putLocal pk (encodeNat ticket)
          return true
    | _, _ => pure ()
  return false

structure Running where
  shard : Nat
  stop : IO.Ref Bool
  task : Task (Except IO.Error Unit)
  deadCount : IO.Ref Nat

namespace Actor

private def drain (s : ShardSet) (shard : Nat) (handle : FitBytes → Tx → IO Unit) : IO Nat := do
  let mut n := 0
  for src in [0:s.shardCount] do
    n := n + (← propagate s src shard handle)
  return n

/--
Start the shard loop. It drains the durable inbox first, then waits on the
bounded mailbox. `cap` is that mailbox. A full mailbox blocks `ShardSet.send`.
-/
def spawn (s : ShardSet) (shard : Nat) (handle : FitBytes → Tx → IO Unit)
    (cap : Nat := 32) (maxAttempts : Nat := 3) : IO Running := do
  if s.shardCount ≤ shard then
    throw (IO.userError "shard id is out of range")
  let box ← Std.Channel.Sync.new (some (max cap 1))
  let wakes ← s.wakes.get
  s.wakes.set (wakes.set! shard (some box))
  let stop ← IO.mkRef false
  let deadCount ← IO.mkRef 0
  let task ← IO.asTask (prio := .dedicated) do
    let mut fails := 0
    let mut force := true
    while !(← stop.get) do
      try
        if !force then
          let _ ← box.recv
          if ← stop.get then
            break
        force := false
        let n ← drain s shard handle
        fails := 0
        if n > 0 then
          force := true
          let _ ← box.tryRecv
      catch e =>
        IO.eprintln s!"cairn actor {shard}: {e}"
        fails := fails + 1
        if maxAttempts ≤ fails then
          let mut skipped := false
          for src in [0:s.shardCount] do
            if ← deadLetter s src shard then
              skipped := true
              deadCount.modify (· + 1)
          fails := 0
          force := true
          if !skipped then
            force := false
        else
          IO.sleep (fails.toUInt32 * 2)
          force := true
  return { shard, stop, task, deadCount }

def stop (a : Running) (s : ShardSet) : IO Unit := do
  a.stop.set true
  let wakes ← s.wakes.get
  match wakes[a.shard]? with
  | some (some box) => box.send ()
  | _ => pure ()
  match ← IO.wait a.task with
  | .ok () => pure ()
  | .error e => throw e

end Actor

/--
Asynchronous, at-least-once. The notice is durable on `msg.origin` before
this returns. The destination actor is woken if it has been spawned. A full
mailbox blocks the caller. The reply, if any, is a later `send` the other way.
-/
def ShardSet.send (s : ShardSet) (dst : Nat) (msg : Msg) : IO Unit := do
  s.transactOn msg.origin fun tx =>
    tx.enqueue dst (.msg msg.payload) 0
  let wakes ← s.wakes.get
  match wakes[dst]? with
  | some (some box) => box.send ()
  | _ => pure ()

end Cairn
