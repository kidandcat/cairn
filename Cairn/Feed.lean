/-
Change feed over one shard's log. Order is that shard's admission order.
There is no merge across shards: two shards have no shared sequence.
-/

import Cairn.Log
import Cairn.Range

namespace Cairn

namespace Feed

def keep (fromLsn : UInt64) (pre : Bytes) (lsn : UInt64) (op : Op) : Bool :=
  decide (fromLsn ≤ lsn) && hasPrefix pre op.key

def visible (fromLsn : UInt64) (pre : Bytes) : List Record → List (UInt64 × Op)
  | [] => []
  | r :: rs =>
      (r.ops.filterMap fun op =>
        if keep fromLsn pre r.lsn op then some (r.lsn, op) else none) ++
        visible fromLsn pre rs

theorem visible_mem (fromLsn : UInt64) (pre : Bytes) (rs : List Record) (lsn : UInt64) (op : Op) :
    (lsn, op) ∈ visible fromLsn pre rs ↔
      ∃ r, r ∈ rs ∧ r.lsn = lsn ∧ op ∈ r.ops ∧ keep fromLsn pre lsn op = true := by
  induction rs with
  | nil => simp [visible]
  | cons r rs ih =>
      simp only [visible, List.mem_append, List.mem_cons, ih]
      constructor
      · intro h
        cases h with
        | inl hmem =>
            simp only [List.mem_filterMap] at hmem
            obtain ⟨op', hop, hsome⟩ := hmem
            cases hkeep : keep fromLsn pre r.lsn op' with
            | false => simp [hkeep] at hsome
            | true =>
                simp [hkeep, Prod.mk.injEq] at hsome
                rcases hsome with ⟨rfl, rfl⟩
                exact ⟨r, Or.inl rfl, rfl, hop, hkeep⟩
        | inr hmem =>
            obtain ⟨r', hr, hlsn, hop, hk⟩ := hmem
            exact ⟨r', Or.inr hr, hlsn, hop, hk⟩
      · intro h
        obtain ⟨r', hr, hlsn, hop, hk⟩ := h
        cases hr with
        | inl heq =>
            cases heq
            refine Or.inl ?_
            simp [List.mem_filterMap]
            exact ⟨op, hop, by simp [hk, hlsn]⟩
        | inr hr =>
            exact Or.inr ⟨r', hr, hlsn, hop, hk⟩

theorem visible_since (fromLsn : UInt64) (pre : Bytes) (rs : List Record)
    (lsn : UInt64) (op : Op) (h : (lsn, op) ∈ visible fromLsn pre rs) :
    fromLsn ≤ lsn := by
  obtain ⟨_, _, hlsn, _, hk⟩ := (visible_mem fromLsn pre rs lsn op).mp h
  simp [keep, decide_eq_true_eq] at hk
  exact hlsn ▸ hk.1

theorem visible_prefix (fromLsn : UInt64) (pre : Bytes) (rs : List Record)
    (lsn : UInt64) (op : Op) (h : (lsn, op) ∈ visible fromLsn pre rs) :
    hasPrefix pre op.key = true := by
  obtain ⟨_, _, _, _, hk⟩ := (visible_mem fromLsn pre rs lsn op).mp h
  simp [keep] at hk
  exact hk.2

end Feed

end Cairn
