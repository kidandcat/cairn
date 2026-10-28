/-
Persistent jobs on the key order `03 / inverted priority / runAt / id`.

`enqueueWith` writes the caller's ops and the job in one batch. `commit`
rejects that batch when the keys are not in one shard, and nothing is
published. With a single shard the keys always agree. With bounds, a job
key that falls on the other side of a bound is refused.

Claim is compare-and-set on the job value. A live lease does not match, so
the loser retries. The pure statement is `Job.claim_blocks`.
-/

import Cairn.Coll
import Cairn.Job
import Cairn.ShardSet
import Cairn.Ulid

namespace Cairn

namespace Queue

def jobPrefix : Bytes := [3]

def jobKey? (priority : Nat) (runAt : Nat) (id : Ulid) : Option FitBytes :=
  let inv := 255 - min priority 255
  FitBytes.ofList? (jobPrefix ++ [UInt8.ofNat inv] ++ beBytes 8 runAt ++ Ulid.encode id)

def encode (leaseUntil attempts runAt : Nat) (dead : Bool) (payload : Bytes) : Bytes :=
  beBytes 8 leaseUntil ++ beBytes 8 attempts ++ beBytes 8 runAt ++
    [if dead then 1 else 0] ++ payload

def decode (bs : Bytes) : Option (Nat × Nat × Nat × Bool × Bytes) :=
  match readBe 8 bs with
  | some (lease, rest) =>
      match readBe 8 rest with
      | some (attempts, rest) =>
          match readBe 8 rest with
          | some (runAt, rest) =>
              match rest with
              | flag :: payload => some (lease, attempts, runAt, flag == 1, payload)
              | [] => none
          | none => none
      | none => none
  | none => none

private def pack (lease attempts runAt : Nat) (dead : Bool) (payload : Bytes) : Option FitBytes :=
  FitBytes.ofList? (encode lease attempts runAt dead payload)

def enqueueWith (s : ShardSet) (anchor : FitBytes) (ops : List Op)
    (priority runAt : Nat) (id : Ulid) (payload : Bytes) : IO Unit := do
  let some k := jobKey? priority runAt id | throw (IO.userError "job key does not fit")
  let some v := pack 0 0 runAt false payload | throw (IO.userError "job value does not fit")
  let batch := ops ++ [.put k v]
  let epoch ← s.epoch.get
  if sameShard epoch.bounds batch = false then
    throw (IO.userError "outbox crossed a shard")
  s.transact anchor fun tx => do
    for op in batch do
      match op with
      | .put k v => tx.put k v
      | .del k => tx.delete k

def enqueue (s : ShardSet) (priority runAt : Nat) (id : Ulid) (payload : Bytes) : IO Unit := do
  let some k := jobKey? priority runAt id | throw (IO.userError "job key does not fit")
  enqueueWith s k [] priority runAt id payload

private def eligible (now lease _attempts runAt : Nat) (dead : Bool) : Bool :=
  !dead && decide (runAt ≤ now) && decide (lease ≤ now)

def claim (s : ShardSet) (now leaseFor : Nat) : IO (Option (Ulid × Bytes)) := do
  let mut after : Option FitBytes := none
  for _ in [0:32] do
    let (rows, cur) ← s.prefix jobPrefix after 32
    for e in rows do
      let suf := e.1.bytes.drop jobPrefix.length
      if suf.length ≥ 1 + 8 + 16 then
        let idBytes := suf.drop (suf.length - 16)
        match Ulid.decode? idBytes, decode e.2.bytes with
        | some id, some (lease, attempts, runAt, dead, payload) =>
            if eligible now lease attempts runAt dead then
              let some nv := pack (now + leaseFor) attempts runAt dead payload
                | throw (IO.userError "job value does not fit")
              let won ← s.transact e.1 fun tx => do
                match ← tx.get e.1 with
                | some cur =>
                    match decode cur.bytes with
                    | some (lease2, _, runAt2, dead2, _) =>
                        if eligible now lease2 0 runAt2 dead2 && cur == e.2 then
                          tx.put e.1 nv
                          return true
                        else
                          return false
                    | none => return false
                | none => return false
              if won then
                return some (id, payload)
        | _, _ => pure ()
    match cur with
    | none => return none
    | some k => after := some k
  return none

def ack (s : ShardSet) (priority runAt : Nat) (id : Ulid) : IO Unit := do
  let some k := jobKey? priority runAt id | throw (IO.userError "job key does not fit")
  s.transact k fun tx => do
    match ← tx.get k with
    | some _ => tx.delete k
    | none => pure ()

def nack (s : ShardSet) (priority runAt : Nat) (id : Ulid) (now maxAttempts : Nat) : IO Unit := do
  let some k := jobKey? priority runAt id | throw (IO.userError "job key does not fit")
  s.transact k fun tx => do
    match ← tx.get k with
    | some cur =>
        match decode cur.bytes with
        | some (_lease, attempts, _run, dead, payload) =>
            let attempts' := attempts + 1
            if dead || maxAttempts ≤ attempts' then
              match pack 0 attempts' runAt true payload with
              | some nv => tx.put k nv
              | none => pure ()
            else
              let run' := now + Job.backoff attempts'
              match pack 0 attempts' run' false payload, jobKey? priority run' id with
              | some nv, some k2 =>
                  if shardOf tx.bounds k2.bytes == tx.home then
                    tx.delete k
                    tx.put k2 nv
                  else
                    match pack 0 attempts' run' false payload with
                    | some stay => tx.put k stay
                    | none => pure ()
              | _, _ => pure ()
        | none => pure ()
    | none => pure ()

end Queue

namespace Ttl

def ttlPrefix : Bytes := [4]

def key? (expiry : Nat) (id : Ulid) : Option FitBytes :=
  FitBytes.ofList? (ttlPrefix ++ beBytes 8 expiry ++ Ulid.encode id)

def put (s : ShardSet) (expiry : Nat) (id : Ulid) (payload : Bytes) : IO Unit := do
  let some k := key? expiry id | throw (IO.userError "ttl key does not fit")
  let some v := FitBytes.ofList? payload | throw (IO.userError "ttl value does not fit")
  s.put k v

/-- Delete index entries whose expiry is `≤ now`. The key order is the index. -/
def sweep (s : ShardSet) (now : Nat) : IO Nat := do
  let mut after : Option FitBytes := none
  let mut n := 0
  for _ in [0:64] do
    let (rows, cur) ← s.prefix ttlPrefix after 32
    for e in rows do
      let suf := e.1.bytes.drop ttlPrefix.length
      match readBe 8 suf with
      | some (expiry, _) =>
          if expiry ≤ now then
            s.transact e.1 fun tx => tx.delete e.1
            n := n + 1
          else
            return n
      | none => pure ()
    match cur with
    | none => return n
    | some k => after := some k
  return n

end Ttl

end Cairn
