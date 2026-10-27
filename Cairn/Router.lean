/-
Key to shard.

`shardOf` counts range bounds that are `≤` the key. Empty bounds means one
shard, so a single node is the same router with no split points. The result is
a plain function of the bounds and the key: total, and the same inputs always
yield the same shard.

Bounds should be strictly increasing if the ranges are meant to be contiguous
and non-empty. Uniqueness does not depend on that. `shardHash` is a separate
static partition; it is not what `sameShard` uses.

An epoch is a generation plus the bounds. Rebalance replaces the bounds and
bumps the generation. It does not move bytes by itself.
-/

import Cairn.Log

namespace Cairn

def shardOf (bounds : List Bytes) (k : Bytes) : Nat :=
  (bounds.filter (fun b => decide (b ≤ k))).length

theorem shardOf_le (bounds : List Bytes) (k : Bytes) : shardOf bounds k ≤ bounds.length := by
  simpa [shardOf] using List.length_filter_le (fun b => decide (b ≤ k)) bounds

theorem shardOf_range (bounds : List Bytes) (k : Bytes) : shardOf bounds k < bounds.length + 1 :=
  Nat.lt_succ_of_le (shardOf_le bounds k)

/-- `s` is the shard id of `k` for these bounds. -/
def IsShard (bounds : List Bytes) (k : Bytes) (s : Nat) : Prop :=
  s = shardOf bounds k ∧ s ≤ bounds.length

/-- Every key belongs to exactly one shard id in `0 .. bounds.length`. -/
theorem key_one_shard (bounds : List Bytes) (k : Bytes) :
    (∃ s, IsShard bounds k s) ∧ ∀ s t, IsShard bounds k s → IsShard bounds k t → s = t := by
  refine ⟨⟨shardOf bounds k, rfl, shardOf_le bounds k⟩, ?_⟩
  intro s t hs ht
  exact hs.1.trans ht.1.symm

theorem shardOf_deterministic {b1 b2 : List Bytes} {k1 k2 : Bytes}
    (hb : b1 = b2) (hk : k1 = k2) : shardOf b1 k1 = shardOf b2 k2 := by
  subst hb
  subst hk
  rfl

theorem shardOf_empty (k : Bytes) : shardOf [] k = 0 := by
  simp [shardOf]

/-- Static hash partition. `n = 0` yields shard 0, matching the empty range router. -/
def shardHash (n : Nat) (k : Bytes) : Nat :=
  if n = 0 then 0 else (crc32 k).toNat % n

theorem shardHash_range (n : Nat) (k : Bytes) (hn : 0 < n) : shardHash n k < n := by
  have hne : ¬ n = 0 := Nat.ne_of_gt hn
  simp [shardHash, hne]
  exact Nat.mod_lt _ hn

def sameShard (bounds : List Bytes) (ops : List Op) : Bool :=
  match ops with
  | [] => false
  | op :: rest => rest.all fun o => shardOf bounds o.key.bytes == shardOf bounds op.key.bytes

theorem sameShard_single (bounds : List Bytes) (op : Op) : sameShard bounds [op] = true := by
  simp [sameShard]

structure Epoch where
  gen : Nat
  bounds : List Bytes
  deriving Repr, DecidableEq

def Epoch.single : Epoch where
  gen := 0
  bounds := []

def Epoch.rebalance (e : Epoch) (bounds : List Bytes) : Epoch where
  gen := e.gen + 1
  bounds := bounds

theorem rebalance_gen (e : Epoch) (bounds : List Bytes) :
    (e.rebalance bounds).gen = e.gen + 1 ∧ (e.rebalance bounds).bounds = bounds := by
  simp [Epoch.rebalance]

def inShard (bounds : List Bytes) (s : Nat) (m : Map) : Map :=
  m.filter fun e => decide (shardOf bounds e.1.bytes = s)

theorem mem_inShard (bounds : List Bytes) (s : Nat) (m : Map) (e : FitBytes × FitBytes) :
    e ∈ inShard bounds s m ↔ e ∈ m ∧ shardOf bounds e.1.bytes = s := by
  simp [inShard, List.mem_filter]

theorem mem_home (bounds : List Bytes) (m : Map) (e : FitBytes × FitBytes) (h : e ∈ m) :
    e ∈ inShard bounds (shardOf bounds e.1.bytes) m := by
  simp [mem_inShard, h]

theorem inShard_disjoint (bounds : List Bytes) (s t : Nat) (m : Map) (e : FitBytes × FitBytes)
    (hs : e ∈ inShard bounds s m) (ht : e ∈ inShard bounds t m) : s = t := by
  simp [mem_inShard] at hs ht
  exact hs.2.symm.trans ht.2

/-- An entry is in the map iff it sits in its home shard. Rebalance reassigns; it does not drop keys. -/
theorem rebalance_partition (bounds : List Bytes) (m : Map) (e : FitBytes × FitBytes) :
    e ∈ m ↔ e ∈ inShard bounds (shardOf bounds e.1.bytes) m := by
  constructor
  · exact mem_home bounds m e
  · intro h
    exact (mem_inShard bounds _ m e).mp h |>.1

theorem nodup_inShard (bounds : List Bytes) (s : Nat) (m : Map) (h : NodupKeys m) :
    NodupKeys (inShard bounds s m) := by
  simpa [NodupKeys, inShard] using List.Pairwise.filter (fun e => decide (shardOf bounds e.1.bytes = s)) h

/-- Snapshot of one shard: compact its entries and replay. The list comes back unchanged. -/
theorem move_replays (bounds : List Bytes) (s : Nat) (m : Map) (h : NodupKeys m) (start : UInt64) :
    replay (compactRecords (inShard bounds s m) start) = inShard bounds s m :=
  compact_eq _ (nodup_inShard bounds s m h) start

end Cairn
