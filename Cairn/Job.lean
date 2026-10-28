/-
Pure job queue. `claim` is a function of the list, the clock, and the lease,
so the same state always yields the same job. A job whose lease is still in
the future is not free, so the next claim does not return it.

`enqueue` with an idempotency key that is already present does not add a
second job. An outbox is one batch of two puts: both keys are visible after
the batch, and a missing batch has neither (the log record is atomic).
-/

import Cairn.Log

namespace Cairn

namespace Job

structure Row where
  id : Nat
  priority : Nat
  runAt : Nat
  leaseUntil : Nat
  attempts : Nat
  idem : Option Nat
  dead : Bool
  deriving Repr, BEq, DecidableEq

def Row.free (j : Row) (now : Nat) : Bool :=
  !j.dead && decide (j.runAt ≤ now) && decide (j.leaseUntil ≤ now)

def Row.better (a b : Row) : Bool :=
  if a.priority != b.priority then decide (b.priority < a.priority)
  else if a.runAt != b.runAt then decide (a.runAt < b.runAt)
  else decide (a.id < b.id)

def pick (now : Nat) : List Row → Option Row
  | [] => none
  | j :: rest =>
      match pick now rest with
      | none => if j.free now then some j else none
      | some best => if j.free now && j.better best then some j else some best

def setLease (rows : List Row) (id leaseAt : Nat) : List Row :=
  rows.map fun j => if j.id == id then { j with leaseUntil := leaseAt } else j

def claim (rows : List Row) (now leaseFor : Nat) : Option Nat × List Row :=
  match pick now rows with
  | none => (none, rows)
  | some j => (some j.id, setLease rows j.id (now + leaseFor))

theorem pick_free (now : Nat) (rows : List Row) (j : Row) (h : pick now rows = some j) :
    j.free now = true := by
  induction rows generalizing j with
  | nil => simp [pick] at h
  | cons head rest ih =>
      simp only [pick] at h
      cases hpick : pick now rest with
      | none =>
          simp only [hpick] at h
          by_cases hf : head.free now = true
          · simp [hf] at h
            cases h
            exact hf
          · simp [hf] at h
      | some best =>
          simp only [hpick] at h
          by_cases hf : head.free now = true
          · by_cases hb : head.better best = true
            · simp [hf, hb] at h
              cases h
              exact hf
            · simp [hf, hb] at h
              cases h
              exact ih j hpick
          · simp [hf] at h
            cases h
            exact ih j hpick

def findId (rows : List Row) (id : Nat) : Option Row :=
  rows.find? fun j => j.id == id

theorem pick_mem (now : Nat) (rows : List Row) (j : Row) (h : pick now rows = some j) :
    j ∈ rows := by
  induction rows generalizing j with
  | nil => simp [pick] at h
  | cons head rest ih =>
      simp only [pick] at h
      cases hpick : pick now rest with
      | none =>
          simp only [hpick] at h
          by_cases hf : head.free now = true
          · simp [hf] at h
            cases h
            exact List.mem_cons_self ..
          · simp [hf] at h
      | some best =>
          simp only [hpick] at h
          by_cases hf : head.free now = true
          · by_cases hb : head.better best = true
            · simp [hf, hb] at h
              cases h
              exact List.mem_cons_self ..
            · simp [hf, hb] at h
              cases h
              exact List.mem_cons_of_mem _ (ih j hpick)
          · simp [hf] at h
            cases h
            exact List.mem_cons_of_mem _ (ih j hpick)

theorem setLease_busy (rows : List Row) (id leaseAt now : Nat) (j : Row)
    (hj : j ∈ setLease rows id leaseAt) (hid : j.id = id) (hnow : now < leaseAt) :
    j.free now = false := by
  simp only [setLease, List.mem_map] at hj
  obtain ⟨row, _, rfl⟩ := hj
  by_cases h : row.id == id
  · simp [h, Row.free, hid, hnow]
  · simp [h] at hid
    have : (row.id == id) = true := by simp [hid]
    exact absurd this h

theorem pick_ne_busy (rows : List Row) (now id : Nat)
    (h : ∀ j ∈ rows, j.id = id → j.free now = false) (j : Row)
    (hp : pick now rows = some j) : j.id ≠ id := by
  intro heq
  have hmem := pick_mem now rows j hp
  have hfree := pick_free now rows j hp
  have hnot := h j hmem heq
  simp [hnot] at hfree

theorem claim_spec (rows : List Row) (now leaseFor : Nat) (j : Row)
    (hp : pick now rows = some j) :
    claim rows now leaseFor = (some j.id, setLease rows j.id (now + leaseFor)) := by
  simp [claim, hp]

/-- A second claim before the lease ends does not return the same id. -/
theorem claim_blocks (rows : List Row) (now leaseFor now' : Nat) (j : Row)
    (_hp : pick now rows = some j) (hnow : now' < now + leaseFor) :
    match pick now' (setLease rows j.id (now + leaseFor)) with
    | none => True
    | some k => k.id ≠ j.id := by
  cases hpick : pick now' (setLease rows j.id (now + leaseFor)) with
  | none => trivial
  | some k =>
      exact pick_ne_busy _ _ j.id
        (fun row hmem hid => setLease_busy rows j.id (now + leaseFor) now' row hmem hid hnow)
        k hpick

def hasIdem (rows : List Row) (key : Nat) : Bool :=
  rows.any fun j => j.idem == some key && !j.dead

def enqueue (rows : List Row) (j : Row) : List Row :=
  match j.idem with
  | none => j :: rows
  | some key => if hasIdem rows key then rows else j :: rows

theorem enqueue_idem (rows : List Row) (j : Row) (key : Nat)
    (hid : j.idem = some key) (hex : hasIdem rows key = true) :
    enqueue rows j = rows := by
  simp [enqueue, hid, hex]

def backoff (attempts : Nat) : Nat :=
  min (2 ^ min attempts 16) 65536

def nack (rows : List Row) (id now maxAttempts : Nat) : List Row :=
  rows.map fun j =>
    if j.id != id then
      j
    else if decide (maxAttempts ≤ j.attempts + 1) then
      { j with dead := true, leaseUntil := 0, attempts := j.attempts + 1 }
    else
      { j with leaseUntil := 0, attempts := j.attempts + 1, runAt := now + backoff (j.attempts + 1) }

def ack (rows : List Row) (id : Nat) : List Row :=
  rows.filter fun j => j.id != id

theorem ack_gone (rows : List Row) (id : Nat) :
    findId (ack rows id) id = none := by
  induction rows with
  | nil => rfl
  | cons head rest ih =>
      simp only [ack, findId, List.filter_cons] at ih ⊢
      split
      · rename_i hkeep
        have hne : (head.id == id) = false := by
          simpa [bne] using hkeep
        simp [hne, ih]
      · exact ih

def due (now : Nat) (rows : List (Nat × Nat)) : List (Nat × Nat) :=
  rows.filter fun r => decide (r.2 ≤ now)

theorem due_mem (now : Nat) (rows : List (Nat × Nat)) (k t : Nat) :
    (k, t) ∈ due now rows ↔ (k, t) ∈ rows ∧ t ≤ now := by
  simp [due, List.mem_filter, decide_eq_true_eq]

end Job

theorem outbox_both (m : Map) (k jk v jv : FitBytes) (h : k.bytes ≠ jk.bytes) :
    get (applyBatch m [.put k v, .put jk jv]) k = some v ∧
      get (applyBatch m [.put k v, .put jk jv]) jk = some jv := by
  have hkeep := get_insert_ne (insert m k v) jk k jv (Ne.symm h)
  have hput := get_insert m k v
  refine ⟨?_, get_insert (insert m k v) jk jv⟩
  simpa [applyBatch, applyOp] using hkeep.trans hput

theorem outbox_second (m : Map) (k jk v jv : FitBytes) (h : k.bytes ≠ jk.bytes) :
    get (applyBatch m [.put jk jv, .put k v]) jk = some jv := by
  simp [applyBatch, applyOp, get_insert_ne, h, get_insert]

end Cairn
