/-
Ordered pages over a map.

`rangeHits` and `prefixHits` are the entries inside an interval, in key order,
each key once. A page is a prefix of that list. The cursor is the last key of
a full page; the next page is the same query with `after` set to that key.

On one map this is exact. Across shards the caller merges one snapshot per
shard (`mergeAll`) and then takes the page. That merge is not a global snapshot.
-/

import Cairn.Map
import Cairn.ShardModel

open Std

namespace Cairn

def strictlyAfter (cursor k : FitBytes) : Bool :=
  cmpKey cursor k == .lt

/-- Inclusive `lo`, exclusive `hi`. `after` is a strict cursor. -/
def inRange (lo hi after : Option FitBytes) (k : FitBytes) : Bool :=
  let loOk := match lo with
    | none => true
    | some a => (cmpKey a k).isLE
  let hiOk := match hi with
    | none => true
    | some b => cmpKey k b == .lt
  let afterOk := match after with
    | none => true
    | some c => strictlyAfter c k
  loOk && hiOk && afterOk

def hasPrefix (p : Bytes) (k : FitBytes) : Bool :=
  p.isPrefixOf k.bytes

def inPrefix (p : Bytes) (after : Option FitBytes) (k : FitBytes) : Bool :=
  hasPrefix p k &&
    match after with
    | none => true
    | some c => strictlyAfter c k

def hits (rows : List (FitBytes × FitBytes)) (keep : FitBytes → Bool) :
    List (FitBytes × FitBytes) :=
  rows.filter fun e => keep e.1

def rangeHits (m : Map) (lo hi after : Option FitBytes) : List (FitBytes × FitBytes) :=
  hits (entries m) (inRange lo hi after)

def prefixHits (m : Map) (p : Bytes) (after : Option FitBytes) : List (FitBytes × FitBytes) :=
  hits (entries m) (inPrefix p after)

def takePage (rows : List (FitBytes × FitBytes)) (limit : Nat) : List (FitBytes × FitBytes) :=
  rows.take limit

def rangePage (m : Map) (lo hi after : Option FitBytes) (limit : Nat) :
    List (FitBytes × FitBytes) :=
  takePage (rangeHits m lo hi after) limit

def prefixPage (m : Map) (p : Bytes) (after : Option FitBytes) (limit : Nat) :
    List (FitBytes × FitBytes) :=
  takePage (prefixHits m p after) limit

/-- `none` when the page is shorter than `limit` (nothing left). Otherwise the last key. -/
def pageCursor (limit : Nat) (rows : List (FitBytes × FitBytes)) : Option FitBytes :=
  let took := rows.take limit
  if took.length < limit then none else took.getLast?.map (·.1)

theorem hits_mem (rows : List (FitBytes × FitBytes)) (keep : FitBytes → Bool)
    (e : FitBytes × FitBytes) :
    e ∈ hits rows keep ↔ e ∈ rows ∧ keep e.1 = true := by
  simp [hits, List.mem_filter]

theorem hits_lt (rows : List (FitBytes × FitBytes)) (keep : FitBytes → Bool)
    (h : rows.Pairwise (fun a b => cmpKey a.1 b.1 = .lt)) :
    (hits rows keep).Pairwise (fun a b => cmpKey a.1 b.1 = .lt) := by
  simpa [hits] using List.Pairwise.filter (fun e => keep e.1) h

theorem entries_lt (m : Map) :
    (entries m).Pairwise (fun a b => cmpKey a.1 b.1 = .lt) :=
  Std.TreeMap.ordered_keys_toList (t := m)

theorem rangeHits_mem (m : Map) (lo hi after : Option FitBytes) (e : FitBytes × FitBytes) :
    e ∈ rangeHits m lo hi after ↔ e ∈ m ∧ inRange lo hi after e.1 = true := by
  simp [rangeHits, hits_mem, entries_mem]

theorem prefixHits_mem (m : Map) (p : Bytes) (after : Option FitBytes) (e : FitBytes × FitBytes) :
    e ∈ prefixHits m p after ↔ e ∈ m ∧ inPrefix p after e.1 = true := by
  simp [prefixHits, hits_mem, entries_mem]

theorem rangeHits_sorted (m : Map) (lo hi after : Option FitBytes) :
    (rangeHits m lo hi after).Pairwise (fun a b => keyLe a b = true) := by
  have h := hits_lt (entries m) (inRange lo hi after) (entries_lt m)
  refine List.Pairwise.imp (fun {a b} (hlt : cmpKey a.1 b.1 = .lt) => ?_) h
  simp [keyLe, hlt]

theorem prefixHits_sorted (m : Map) (p : Bytes) (after : Option FitBytes) :
    (prefixHits m p after).Pairwise (fun a b => keyLe a b = true) := by
  have h := hits_lt (entries m) (inPrefix p after) (entries_lt m)
  refine List.Pairwise.imp (fun {a b} (hlt : cmpKey a.1 b.1 = .lt) => ?_) h
  simp [keyLe, hlt]

private theorem cmp_ne_of_lt {a b : FitBytes} (h : cmpKey a b = .lt) : a.bytes ≠ b.bytes := by
  intro heq
  have hab : a = b := FitBytes.eq_of_bytes heq
  rw [hab] at h
  have he : cmpKey b b = .eq := ReflCmp.compare_self (cmp := cmpKey)
  rw [he] at h
  cases h

theorem rangeHits_nodup (m : Map) (lo hi after : Option FitBytes) :
    (rangeHits m lo hi after).Pairwise (fun a b => a.1.bytes ≠ b.1.bytes) := by
  refine List.Pairwise.imp (fun {a b} (hlt : cmpKey a.1 b.1 = .lt) => ?_)
    (hits_lt (entries m) (inRange lo hi after) (entries_lt m))
  exact cmp_ne_of_lt hlt

theorem prefixHits_nodup (m : Map) (p : Bytes) (after : Option FitBytes) :
    (prefixHits m p after).Pairwise (fun a b => a.1.bytes ≠ b.1.bytes) := by
  refine List.Pairwise.imp (fun {a b} (hlt : cmpKey a.1 b.1 = .lt) => ?_)
    (hits_lt (entries m) (inPrefix p after) (entries_lt m))
  exact cmp_ne_of_lt hlt

theorem rangePage_sorted (m : Map) (lo hi after : Option FitBytes) (limit : Nat) :
    (rangePage m lo hi after limit).Pairwise (fun a b => keyLe a b = true) :=
  List.Pairwise.take (rangeHits_sorted m lo hi after)

theorem prefixPage_sorted (m : Map) (p : Bytes) (after : Option FitBytes) (limit : Nat) :
    (prefixPage m p after limit).Pairwise (fun a b => keyLe a b = true) :=
  List.Pairwise.take (prefixHits_sorted m p after)

theorem rangePage_nodup (m : Map) (lo hi after : Option FitBytes) (limit : Nat) :
    (rangePage m lo hi after limit).Pairwise (fun a b => a.1.bytes ≠ b.1.bytes) :=
  List.Pairwise.take (rangeHits_nodup m lo hi after)

theorem prefixPage_nodup (m : Map) (p : Bytes) (after : Option FitBytes) (limit : Nat) :
    (prefixPage m p after limit).Pairwise (fun a b => a.1.bytes ≠ b.1.bytes) :=
  List.Pairwise.take (prefixHits_nodup m p after)

theorem rangePage_sub (m : Map) (lo hi after : Option FitBytes) (limit : Nat)
    (e : FitBytes × FitBytes) :
    e ∈ rangePage m lo hi after limit → e ∈ m ∧ inRange lo hi after e.1 = true := by
  intro he
  have hmem : e ∈ rangeHits m lo hi after := List.mem_of_mem_take he
  exact (rangeHits_mem m lo hi after e).mp hmem

theorem prefixPage_sub (m : Map) (p : Bytes) (after : Option FitBytes) (limit : Nat)
    (e : FitBytes × FitBytes) :
    e ∈ prefixPage m p after limit → e ∈ m ∧ inPrefix p after e.1 = true := by
  intro he
  have hmem : e ∈ prefixHits m p after := List.mem_of_mem_take he
  exact (prefixHits_mem m p after e).mp hmem

/-! ## The next page is the tail of the same hit list -/

private theorem cmp_irrefl (k : FitBytes) : (cmpKey k k == .lt) = false := by
  have he : cmpKey k k = .eq := ReflCmp.compare_self (cmp := cmpKey)
  simp [he]

private theorem filter_drop_head (y : FitBytes × FitBytes) (ys : List (FitBytes × FitBytes))
    (h : (y :: ys).Pairwise (fun a b => cmpKey a.1 b.1 = .lt)) :
    (y :: ys).filter (fun e => cmpKey y.1 e.1 == .lt) = ys := by
  have hself : (cmpKey y.1 y.1 == .lt) = false := cmp_irrefl y.1
  simp only [List.filter_cons, hself]
  refine (List.filter_eq_self).mpr ?_
  intro e he
  have hlt : cmpKey y.1 e.1 = .lt := (List.pairwise_cons.mp h).1 e he
  simp [hlt]

private theorem not_lt_of_lt {a b : FitBytes} (h : cmpKey a b = .lt) :
    (cmpKey b a == .lt) = false := by
  have hs := OrientedCmp.eq_swap (cmp := cmpKey) (a := a) (b := b)
  rw [h] at hs
  cases hba : cmpKey b a with
  | lt =>
      rw [hba] at hs
      simp [Ordering.swap] at hs
  | eq =>
      rw [hba] at hs
      simp [Ordering.swap] at hs
  | gt =>
      simp [hba]

/-- Dropping `n` from a strictly ordered list is filtering past the last kept key. -/
theorem drop_eq_after (ys : List (FitBytes × FitBytes)) (n : Nat)
    (h : ys.Pairwise (fun a b => cmpKey a.1 b.1 = .lt)) (hn : n ≤ ys.length) :
    ys.drop n = ys.filter (fun e =>
      match (ys.take n).getLast? with
      | none => true
      | some z => cmpKey z.1 e.1 == .lt) := by
  induction n generalizing ys with
  | zero =>
      simp only [List.take_zero, List.drop_zero, List.getLast?_nil]
      exact ((List.filter_eq_self).mpr (fun _ _ => rfl)).symm
  | succ n ih =>
      cases ys with
      | nil => simp at hn
      | cons y ys =>
          have hn' : n ≤ ys.length := by exact Nat.le_of_succ_le_succ hn
          have ht : ys.Pairwise (fun a b => cmpKey a.1 b.1 = .lt) :=
            (List.pairwise_cons.mp h).2
          have hhead : ∀ e ∈ ys, cmpKey y.1 e.1 = .lt :=
            (List.pairwise_cons.mp h).1
          cases n with
          | zero =>
              have htake : ((y :: ys).take 1).getLast? = some y := by
                simp [List.take_succ_cons, List.take_zero, List.getLast?_singleton]
              have hdrop : (y :: ys).drop 1 = ys := by simp
              rw [htake, hdrop]
              change ys = (y :: ys).filter (fun e => cmpKey y.1 e.1 == .lt)
              exact (filter_drop_head y ys h).symm
          | succ n =>
              have ih' := ih ys ht hn'
              simp only [List.drop_succ_cons]
              rw [ih']
              have hlen : (ys.take (n + 1)).length = n + 1 :=
                List.length_take_of_le hn'
              have hne : ys.take (n + 1) ≠ [] := by
                intro hempty
                have : (ys.take (n + 1)).length = 0 := by simp [hempty]
                rw [hlen] at this
                exact Nat.succ_ne_zero n this
              have hlast :
                  ((y :: ys).take (n + 2)).getLast? = (ys.take (n + 1)).getLast? := by
                simp [List.take_succ_cons, List.getLast?_cons_of_ne_nil hne]
              rw [hlast]
              cases hz : (ys.take (n + 1)).getLast? with
              | none =>
                  exact False.elim (hne ((List.getLast?_eq_none_iff).1 hz))
              | some z =>
                  have hzys : z ∈ ys := List.mem_of_mem_take (List.mem_of_getLast? hz)
                  have hyz : cmpKey y.1 z.1 = .lt := hhead z hzys
                  have hyfilt : (cmpKey z.1 y.1 == .lt) = false := not_lt_of_lt hyz
                  simp [hyfilt]

private theorem filter_and (rows : List (FitBytes × FitBytes))
    (p q : FitBytes → Bool) :
    rows.filter (fun e => p e.1 && q e.1) =
      (rows.filter (fun e => p e.1)).filter (fun e => q e.1) := by
  induction rows with
  | nil => rfl
  | cons e es ih =>
      simp only [List.filter_cons, ih]
      cases hp : p e.1 <;> cases hq : q e.1 <;> simp [*]

private theorem inRange_after (lo hi : Option FitBytes) (c k : FitBytes) :
    inRange lo hi (some c) k = (inRange lo hi none k && strictlyAfter c k) := by
  simp [inRange, strictlyAfter, Bool.and_assoc]

theorem resume_hits (m : Map) (lo hi : Option FitBytes) (limit : Nat)
    (hlim : limit ≤ (rangeHits m lo hi none).length) :
    rangeHits m lo hi (pageCursor limit (rangeHits m lo hi none)) =
      (rangeHits m lo hi none).drop limit := by
  have hs := hits_lt (entries m) (inRange lo hi none) (entries_lt m)
  have hd := drop_eq_after (rangeHits m lo hi none) limit hs hlim
  have hlen : ((rangeHits m lo hi none).take limit).length = limit :=
    List.length_take_of_le hlim
  simp only [pageCursor, hlen, Nat.lt_irrefl, ite_false]
  cases hlast : ((rangeHits m lo hi none).take limit).getLast? with
  | none =>
      have hempty : (rangeHits m lo hi none).take limit = [] :=
        (List.getLast?_eq_none_iff).1 hlast
      have hz : limit = 0 := by
        have h0 : ((rangeHits m lo hi none).take limit).length = 0 := by simp [hempty]
        rw [hlen] at h0
        exact h0
      simp [hz, List.drop_zero] at hd ⊢
  | some z =>
      have hpred :
          (rangeHits m lo hi none).filter (fun e => cmpKey z.1 e.1 == .lt) =
            (rangeHits m lo hi none).drop limit := by
        simpa [hlast] using hd.symm
      rw [← hpred]
      simp only [rangeHits, hits, Option.map_some]
      have hiff :
          ∀ e : FitBytes × FitBytes,
            inRange lo hi (some z.1) e.1 =
              (inRange lo hi none e.1 && strictlyAfter z.1 e.1) :=
        fun e => inRange_after lo hi z.1 e.1
      simp only [hiff, strictlyAfter]
      exact filter_and (entries m) (inRange lo hi none) (fun k => cmpKey z.1 k == .lt)

theorem resume_prefix (m : Map) (p : Bytes) (limit : Nat)
    (hlim : limit ≤ (prefixHits m p none).length) :
    prefixHits m p (pageCursor limit (prefixHits m p none)) =
      (prefixHits m p none).drop limit := by
  have hs := hits_lt (entries m) (inPrefix p none) (entries_lt m)
  have hd := drop_eq_after (prefixHits m p none) limit hs hlim
  have hlen : ((prefixHits m p none).take limit).length = limit :=
    List.length_take_of_le hlim
  simp only [pageCursor, hlen, Nat.lt_irrefl, ite_false]
  cases hlast : ((prefixHits m p none).take limit).getLast? with
  | none =>
      have hempty : (prefixHits m p none).take limit = [] :=
        (List.getLast?_eq_none_iff).1 hlast
      have hz : limit = 0 := by
        have h0 : ((prefixHits m p none).take limit).length = 0 := by simp [hempty]
        rw [hlen] at h0
        exact h0
      simp [hz, List.drop_zero] at hd ⊢
  | some z =>
      have hpred :
          (prefixHits m p none).filter (fun e => cmpKey z.1 e.1 == .lt) =
            (prefixHits m p none).drop limit := by
        simpa [hlast] using hd.symm
      rw [← hpred]
      simp only [prefixHits, hits, Option.map_some, inPrefix, strictlyAfter, Bool.and_true]
      exact filter_and (entries m) (hasPrefix p) (fun k => cmpKey z.1 k == .lt)

/-- Merged shard snapshots: an entry is in the merged hits iff some part has it and it matches. -/
theorem mergedHits_mem (parts : List (List (FitBytes × FitBytes))) (keep : FitBytes → Bool)
    (e : FitBytes × FitBytes) :
    e ∈ mergeAll (parts.map fun p => hits p keep) ↔
      ∃ p, p ∈ parts ∧ e ∈ p ∧ keep e.1 = true := by
  rw [mem_mergeAll]
  constructor
  · intro h
    obtain ⟨rows, hrows, he⟩ := h
    simp only [List.mem_map] at hrows
    obtain ⟨p, hp, rfl⟩ := hrows
    have hhit := (hits_mem p keep e).mp he
    exact ⟨p, hp, hhit.1, hhit.2⟩
  · intro h
    obtain ⟨p, hp, he, hk⟩ := h
    refine ⟨hits p keep, List.mem_map_of_mem hp, ?_⟩
    exact (hits_mem p keep e).mpr ⟨he, hk⟩

end Cairn
