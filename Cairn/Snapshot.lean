/-
Single-writer history.

`Hist` is the model the runtime mutex is meant to realize: commits are a
sequence, and a snapshot is the map value at the moment it was taken. Later
`write`s build a new history; they do not update an old `Snapshot`.

This file does not formalize the C++ memory model behind `IO.Ref` or
`Std.Mutex`. Those are cited in the README and covered by the task stress test.
-/

import Cairn.Log

namespace Cairn

inductive Hist where
  | empty
  | write (prev : Hist) (ops : List Op)
  | look (prev : Hist)

def Hist.state : Hist → Map
  | .empty => []
  | .write prev ops => applyBatch prev.state ops
  | .look prev => prev.state

def Hist.commits : Hist → List (List Op)
  | .empty => []
  | .write prev ops => prev.commits ++ [ops]
  | .look prev => prev.commits

/-- Fold the committed batches in admission order. -/
def serial (commits : List (List Op)) : Map :=
  commits.foldl applyBatch []

theorem state_eq_serial (h : Hist) : h.state = serial h.commits := by
  induction h with
  | empty => simp [Hist.state, Hist.commits, serial]
  | write prev ops ih =>
      simp [Hist.state, Hist.commits, serial, List.foldl_append, ih]
  | look prev ih =>
      simp [Hist.state, Hist.commits, ih]

/-- Captured map. A value, not a pointer into the history. -/
structure Snapshot where
  view : Map

def snap (h : Hist) : Snapshot :=
  { view := h.state }

theorem snap_view (h : Hist) : (snap h).view = h.state := rfl

theorem look_preserves (h : Hist) : (Hist.look h).state = h.state := rfl

def Hist.extend (h : Hist) : List (List Op) → Hist
  | [] => h
  | ops :: more => (Hist.write h ops).extend more

theorem extend_foldl (h : Hist) (more : List (List Op)) :
    (h.extend more).state = more.foldl applyBatch h.state := by
  induction more generalizing h with
  | nil => simp [Hist.extend]
  | cons ops more ih =>
      simp [Hist.extend, Hist.state, ih]

/--
The view taken at `h` is `h.state`. Extending the history with more commits
folds those batches onto that same view; the snapshot value is not rewritten.
-/
theorem snapshot_stable (h : Hist) (more : List (List Op)) :
    (snap h).view = h.state ∧
      (h.extend more).state = more.foldl applyBatch (snap h).view :=
  ⟨rfl, extend_foldl h more⟩

end Cairn
