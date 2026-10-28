/-
Copies and messages across shards. Not a cross-shard transaction.

A write on the home shard is one `transact`: the home keys, plus one outbox
notice per destination. A propagator on the destination reads that outbox
in key order and applies each notice once. The idempotency key is the
outbox ticket (source LSN and index). The destination stores the last
ticket it applied, in the same batch as the effect, so a crash resumes
without duplicating or dropping a notice that was committed on the home.

Consistency is eventual. Inside the home, `transact` is serial. A reader
can use `ShardSet.get` (the home, current for that shard) or `readCopy`
(the destination file, which can lag). `readCopy` returns the applied
ticket and the home tip.

`commit` still rejects a batch that spans shards. `commitCross` splits it
into the home batch plus notices. The result says it is not atomic.
`strict := true` keeps the rejection.

Outbox and progress keys are stored with `Tx.putLocal` in the file of the
shard that holds the batch. `shardOf` does not route them. Propagators
read that file with `localPrefix` / `localGet`.
-/

import Cairn.Coll
import Cairn.ShardSet
import Cairn.Ulid

namespace Cairn

namespace CopyModel

def applyTicket (mark : Nat) (data : Map) (ticket : Nat) (op : Op) : Nat × Map :=
  if ticket ≤ mark then (mark, data) else (ticket, applyOp data op)

theorem applyTicket_skip (mark : Nat) (data : Map) (ticket : Nat) (op : Op)
    (h : ticket ≤ mark) : applyTicket mark data ticket op = (mark, data) := by
  simp [applyTicket, h]

theorem applyTicket_idem (mark : Nat) (data : Map) (ticket : Nat) (op : Op) :
    (applyTicket (applyTicket mark data ticket op).1 (applyTicket mark data ticket op).2 ticket op) =
      applyTicket mark data ticket op := by
  by_cases h : ticket ≤ mark
  · simp [applyTicket, h]
  · simp [applyTicket, h, Nat.le_refl]

def applyTickets (mark : Nat) (data : Map) (ms : List (Nat × Op)) : Nat × Map :=
  ms.foldl (fun s m => applyTicket s.1 s.2 m.1 m.2) (mark, data)

def numbered (start : Nat) : List Op → List (Nat × Op)
  | [] => []
  | op :: ops => (start, op) :: numbered (start + 1) ops

/-- Tickets `start, start+1, …` replay the ops in order, and the mark ends on the last ticket. -/
theorem numbered_fold (data : Map) (ops : List Op) (start : Nat) (hs : 1 ≤ start) :
    applyTickets (start - 1) data (numbered start ops) =
      (start + ops.length - 1, applyBatch data ops) := by
  induction ops generalizing data start with
  | nil =>
      simp [numbered, applyTickets]
  | cons op ops ih =>
      have hnot : ¬ start ≤ start - 1 := by omega
      have ih' := ih (applyOp data op) (start + 1) (by omega)
      simp only [Nat.add_sub_cancel] at ih'
      have hstep :
          applyTickets (start - 1) data (numbered start (op :: ops)) =
            applyTickets start (applyOp data op) (numbered (start + 1) ops) := by
        simp [numbered, applyTickets, List.foldl_cons, applyTicket, hnot]
      rw [hstep, ih']
      simp [applyBatch, applyOp]

/-- After every notice, the copy matches the home that started empty and logged those ops. -/
theorem converge (ops : List Op) :
    (applyTickets 0 Map.empty (numbered 1 ops)).2 = applyBatch Map.empty ops := by
  have h := numbered_fold Map.empty ops 1 (by decide)
  simp [h]

end CopyModel

inductive Notice where
  | put (k v : FitBytes)
  | del (k : FitBytes)
  | msg (payload : FitBytes)
  deriving Repr

def encodeNotice : Notice → Bytes
  | .put k v => [1] ++ writeFit k ++ writeFit v
  | .del k => [2] ++ writeFit k
  | .msg p => [3] ++ writeFit p

def decodeNotice (bs : Bytes) : Option Notice :=
  match bs with
  | 1 :: rest =>
      match readFit rest with
      | some (k, rest) =>
          match readFit rest with
          | some (v, []) => some (.put k v)
          | _ => none
      | none => none
  | 2 :: rest =>
      match readFit rest with
      | some (k, []) => some (.del k)
      | _ => none
  | 3 :: rest =>
      match readFit rest with
      | some (p, []) => some (.msg p)
      | _ => none
  | _ => none

def outPrefix (dest : Nat) : Bytes :=
  [7] ++ beBytes 4 dest

def outKey (dest ticket : Nat) : Option FitBytes :=
  FitBytes.ofList? (outPrefix dest ++ beBytes 8 ticket)

def progKey (src : Nat) : Option FitBytes :=
  FitBytes.ofList? ([8] ++ beBytes 4 src)

def encodeNat (n : Nat) : FitBytes :=
  ⟨beBytes 8 n, by simpa [beBytes_length] using (by decide : 8 < UInt32.size)⟩

def decodeNat (f : FitBytes) : Option Nat :=
  match readBe 8 f.bytes with
  | some (n, []) => some n
  | _ => none

def noticeTicket (lsn : UInt64) (idx : Nat) : Nat :=
  (lsn.toNat + 1) * 65536 + idx

def Tx.enqueue (tx : Tx) (dest : Nat) (note : Notice) (idx : Nat) : IO Unit := do
  if 65536 ≤ idx then
    throw (IO.userError "too many notices in one batch")
  let ticket := noticeTicket tx.nextLsn idx
  let some k := outKey dest ticket | throw (IO.userError "outbox key does not fit")
  let some v := FitBytes.ofList? (encodeNotice note) | throw (IO.userError "notice does not fit")
  tx.putLocal k v

private def ticketOf (dest : Nat) (k : FitBytes) : Option Nat :=
  let pre := outPrefix dest
  if pre.isPrefixOf k.bytes then
    match readBe 8 (k.bytes.drop pre.length) with
    | some (n, []) => some n
    | _ => none
  else
    none

structure CopyView where
  value : Option FitBytes
  applied : Nat
  homeTip : UInt64
  deriving Repr

def readCopy (s : ShardSet) (home dest : Nat) (k : FitBytes) : IO CopyView := do
  let value ← s.localGet dest k
  let applied ←
    match progKey home with
    | none => pure 0
    | some pk =>
        match ← s.localGet dest pk with
        | some v => pure (decodeNat v |>.getD 0)
        | none => pure 0
  let tip ← s.tip home
  return { value, applied, homeTip := tip }

/--
Apply notices from `src` addressed to `dst`, in ticket order.
Each notice is one transaction on `dst` together with the progress key.
A ticket already applied is skipped.
-/
def propagate (s : ShardSet) (src dst : Nat) (handle : FitBytes → Tx → IO Unit) : IO Nat := do
  let some pk := progKey src | throw (IO.userError "progress key does not fit")
  let mut after : Option FitBytes := none
  let mut n := 0
  for _ in [0:128] do
    let (rows, cur) ← s.localPrefix src (outPrefix dst) after 32
    for e in rows do
      match ticketOf dst e.1, decodeNotice e.2.bytes with
      | some ticket, some note =>
          let did ← s.transactOn dst fun tx => do
            let mark ←
              match ← tx.get pk with
              | some v => pure (decodeNat v |>.getD 0)
              | none => pure 0
            if ticket ≤ mark then
              return false
            match note with
            | .put k v => tx.putLocal k v
            | .del k => tx.deleteLocal k
            | .msg p => handle p tx
            tx.putLocal pk (encodeNat ticket)
            return true
          if did then
            n := n + 1
      | _, _ => pure ()
    match cur with
    | none => return n
    | some k => after := some k
  return n

inductive CrossResult where
  | local
  | eventual (home : Nat) (destinations : List Nat)
  deriving Repr, BEq

def commitCross (s : ShardSet) (ops : List Op) (strict : Bool := false) : IO CrossResult := do
  match ops with
  | [] => throw (IO.userError "empty batch")
  | op :: _ =>
      let e ← s.epoch.get
      let home := shardOf e.bounds op.key.bytes
      let mut dests : List Nat := []
      for o in ops do
        let d := shardOf e.bounds o.key.bytes
        if d ≠ home && !dests.contains d then
          dests := d :: dests
      if dests.isEmpty then
        s.commit ops
        return .local
      if strict then
        throw (IO.userError "cross-shard batch")
      s.transactOn home fun tx => do
        let mut i := 0
        for o in ops do
          let d := shardOf tx.bounds o.key.bytes
          if d == home then
            match o with
            | .put k v => tx.put k v
            | .del k => tx.delete k
          else
            let note :=
              match o with
              | .put k v => Notice.put k v
              | .del k => Notice.del k
            tx.enqueue d note i
            i := i + 1
      return .eventual home dests.reverse

end Cairn
