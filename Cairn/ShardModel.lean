/-
What one-writer-per-shard means, without a runtime.

`routeOf` sends a batch to `shardOf` of its keys, or to nowhere when the
batch is empty or crosses a shard. `Worlds` keeps a `Hist` per shard id.
A step writes that history and no other. Two steps on different shards
commute: there is no global serial order to recover.

`clusterEntries` is the sorted merge of per-shard snapshots. It contains
exactly the entries of those snapshots. Splitting one map with `inShard`
and merging gives those entries back. The runtime merge reads each shard
at its own moment, so the theorem is about the merge of the views that
were actually read, not about one global snapshot.

`afterCrash` replaces one shard's record list and leaves every other id
alone. The replaced list is a prefix when the bytes were a prefix of a
well-formed encoding (`decodeFile_prefix`).
-/

import Cairn.Router
import Cairn.Snapshot

namespace Cairn

def routeOf (bounds : List Bytes) (ops : List Op) : Option Nat :=
  match ops with
  | [] => none
  | op :: rest =>
      if rest.all (fun o => shardOf bounds o.key.bytes == shardOf bounds op.key.bytes) then
        some (shardOf bounds op.key.bytes)
      else
        none

theorem route_is_shardOf (bounds : List Bytes) (op : Op) (rest : List Op) (s : Nat)
    (h : routeOf bounds (op :: rest) = some s) :
    s = shardOf bounds op.key.bytes ∧ sameShard bounds (op :: rest) = true := by
  match hcond : rest.all (fun o => shardOf bounds o.key.bytes == shardOf bounds op.key.bytes) with
  | true =>
      simp only [routeOf, hcond, sameShard] at h ⊢
      cases h
      simp
  | false =>
      simp only [routeOf, hcond, Bool.false_eq_true, ite_false] at h
      cases h

/-- One history per shard id. Absent ids are whatever the caller stored, usually `Hist.empty`. -/
@[ext] structure Worlds where
  bounds : List Bytes
  shardHist : Nat → Hist

def writeAt (h : Nat → Hist) (s : Nat) (ops : List Op) : Nat → Hist :=
  fun i => if i = s then Hist.write (h i) ops else h i

theorem writeAt_eq (h : Nat → Hist) (s : Nat) (ops : List Op) (i : Nat) (hi : i = s) :
    writeAt h s ops i = Hist.write (h i) ops := by
  simp [writeAt, hi]

theorem writeAt_ne (h : Nat → Hist) (s : Nat) (ops : List Op) (i : Nat) (hi : i ≠ s) :
    writeAt h s ops i = h i := by
  simp [writeAt, hi]

theorem writeAt_comm (h : Nat → Hist) (s t : Nat) (ops1 ops2 : List Op) (hne : s ≠ t) :
    writeAt (writeAt h s ops1) t ops2 = writeAt (writeAt h t ops2) s ops1 := by
  funext i
  by_cases ht : i = t
  · have hts : ¬ t = s := fun hts => hne hts.symm
    simp [writeAt, ht, hts]
  · by_cases hs : i = s
    · simp [writeAt, hs, hne]
    · simp [writeAt, hs, ht]

def Worlds.step (w : Worlds) (ops : List Op) : Worlds :=
  match routeOf w.bounds ops with
  | none => w
  | some s => { w with shardHist := writeAt w.shardHist s ops }

theorem step_bounds (w : Worlds) (ops : List Op) : (w.step ops).bounds = w.bounds := by
  unfold Worlds.step
  split <;> rfl

theorem step_reject (w : Worlds) (ops : List Op) (h : routeOf w.bounds ops = none) :
    w.step ops = w := by
  simp [Worlds.step, h]

theorem step_home (w : Worlds) (ops : List Op) (s : Nat)
    (h : routeOf w.bounds ops = some s) :
    (w.step ops).shardHist s = Hist.write (w.shardHist s) ops := by
  simp [Worlds.step, h, writeAt]

theorem step_other (w : Worlds) (ops : List Op) (s i : Nat)
    (h : routeOf w.bounds ops = some s) (hne : i ≠ s) :
    (w.step ops).shardHist i = w.shardHist i := by
  simp [Worlds.step, h, writeAt, hne]

/-- Each shard's state is the serial fold of that shard's own commits. There is no second history. -/
theorem shard_hist_serial (w : Worlds) (s : Nat) :
    (w.shardHist s).state = serial (w.shardHist s).commits :=
  state_eq_serial (w.shardHist s)

theorem step_hist (w : Worlds) (ops : List Op) (s : Nat)
    (h : routeOf w.bounds ops = some s) :
    (w.step ops).shardHist = writeAt w.shardHist s ops := by
  simp [Worlds.step, h]

/--
Writes to different shards commute. Either order is the same `Worlds`.
That is the absence of a global serial order: the two interleavings are equal
because the histories do not share a map.
-/
theorem steps_commute (w : Worlds) (ops1 ops2 : List Op) (s t : Nat)
    (h1 : routeOf w.bounds ops1 = some s) (h2 : routeOf w.bounds ops2 = some t)
    (hne : s ≠ t) :
    (w.step ops1).step ops2 = (w.step ops2).step ops1 := by
  have hb1 : (w.step ops1).bounds = w.bounds := step_bounds w ops1
  have hb2 : (w.step ops2).bounds = w.bounds := step_bounds w ops2
  have hr2 : routeOf (w.step ops1).bounds ops2 = some t := by simpa [hb1] using h2
  have hr1 : routeOf (w.step ops2).bounds ops1 = some s := by simpa [hb2] using h1
  have hA : ((w.step ops1).step ops2).shardHist =
      writeAt (writeAt w.shardHist s ops1) t ops2 := by
    rw [step_hist (w.step ops1) ops2 t hr2, step_hist w ops1 s h1]
  have hB : ((w.step ops2).step ops1).shardHist =
      writeAt (writeAt w.shardHist t ops2) s ops1 := by
    rw [step_hist (w.step ops2) ops1 s hr1, step_hist w ops2 t h2]
  apply Worlds.ext
  · exact (step_bounds (w.step ops1) ops2).trans hb1 |>.trans
      (hb2.symm.trans (step_bounds (w.step ops2) ops1).symm)
  · rw [hA, hB]
    exact writeAt_comm w.shardHist s t ops1 ops2 hne

/-! ## Merge of per-shard snapshots -/

def mergeTwo (xs ys : List (FitBytes × FitBytes)) : List (FitBytes × FitBytes) :=
  List.merge xs ys keyLe

def mergeAll : List (List (FitBytes × FitBytes)) → List (FitBytes × FitBytes)
  | [] => []
  | p :: ps => mergeTwo p (mergeAll ps)

theorem mem_mergeTwo (xs ys : List (FitBytes × FitBytes)) (e : FitBytes × FitBytes) :
    e ∈ mergeTwo xs ys ↔ e ∈ xs ∨ e ∈ ys := by
  have hp : List.Perm (mergeTwo xs ys) (xs ++ ys) := by
    simpa [mergeTwo] using (List.merge_perm_append (le := keyLe) (xs := xs) (ys := ys))
  have hm := List.Perm.mem_iff (a := e) hp
  simpa [List.mem_append] using hm

theorem mem_mergeAll (ps : List (List (FitBytes × FitBytes))) (e : FitBytes × FitBytes) :
    e ∈ mergeAll ps ↔ ∃ p, p ∈ ps ∧ e ∈ p := by
  induction ps with
  | nil => simp [mergeAll]
  | cons p ps ih =>
      simp only [mergeAll, mem_mergeTwo, ih, List.mem_cons]
      constructor
      · rintro (he | ⟨q, hq, he⟩)
        · exact ⟨p, Or.inl rfl, he⟩
        · exact ⟨q, Or.inr hq, he⟩
      · rintro ⟨q, (rfl | hq), he⟩
        · exact Or.inl he
        · exact Or.inr ⟨q, hq, he⟩

theorem mergeTwo_sorted (xs ys : List (FitBytes × FitBytes))
    (hx : xs.Pairwise (fun a b => keyLe a b = true))
    (hy : ys.Pairwise (fun a b => keyLe a b = true)) :
    (mergeTwo xs ys).Pairwise (fun a b => keyLe a b = true) := by
  simpa [mergeTwo] using
    List.pairwise_merge (le := keyLe) keyLe_trans keyLe_total xs ys hx hy

theorem mergeAll_sorted (ps : List (List (FitBytes × FitBytes)))
    (h : ∀ p, p ∈ ps → p.Pairwise (fun a b => keyLe a b = true)) :
    (mergeAll ps).Pairwise (fun a b => keyLe a b = true) := by
  induction ps with
  | nil => simp [mergeAll]
  | cons p ps ih =>
      simp only [mergeAll]
      exact mergeTwo_sorted p (mergeAll ps) (h p (List.mem_cons_self ..))
        (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

/-!
A merged page only needs the first `limit` rows of each part. Anything past that
already has `limit` predecessors in its own part, and `List.merge` keeps that
order, so it cannot land in the merged page.
-/

private theorem merge_cons_cons {α : Type} (le : α → α → Bool) (x y : α) (xs ys : List α) :
    List.merge (x :: xs) (y :: ys) le =
      if le x y then x :: List.merge xs (y :: ys) le
      else y :: List.merge (x :: xs) ys le := by
  conv =>
    lhs
    unfold List.merge

private theorem take_merge_append_right {α : Type} (le : α → α → Bool) (n : Nat)
    (bs as : List α) (z : α) (h : n ≤ as.length) :
    (List.merge bs (as ++ [z]) le).take n = (List.merge bs as le).take n := by
  induction n generalizing bs as with
  | zero => simp
  | succ n ih =>
      match as with
      | [] => simp at h
      | a :: as =>
          have h' : n ≤ as.length := Nat.le_of_succ_le_succ h
          match bs with
          | [] =>
              simp [List.take_append_of_le_length h', List.take_succ_cons]
          | b :: bs =>
              have happend : (a :: as) ++ [z] = a :: (as ++ [z]) := rfl
              rw [happend]
              have hL := merge_cons_cons le b a bs (as ++ [z])
              have hR := merge_cons_cons le b a bs as
              rw [hL, hR]
              split
              · next hcond =>
                  simp only [hcond, List.take_succ_cons]
                  exact congrArg (b :: ·) (ih bs (a :: as) (Nat.le_succ_of_le h'))
              · next hcond =>
                  simp only [hcond, List.take_succ_cons]
                  exact congrArg (a :: ·) (ih (b :: bs) as h')

private theorem take_merge_append_left {α : Type} (le : α → α → Bool) (n : Nat)
    (as bs : List α) (z : α) (h : n ≤ as.length) :
    (List.merge (as ++ [z]) bs le).take n = (List.merge as bs le).take n := by
  induction n generalizing as bs with
  | zero => simp
  | succ n ih =>
      match as with
      | [] => simp at h
      | a :: as =>
          have h' : n ≤ as.length := Nat.le_of_succ_le_succ h
          match bs with
          | [] =>
              simp [List.take_append_of_le_length h', List.take_succ_cons]
          | b :: bs =>
              have happend : (a :: as) ++ [z] = a :: (as ++ [z]) := rfl
              rw [happend]
              have hL := merge_cons_cons le a b (as ++ [z]) bs
              have hR := merge_cons_cons le a b as bs
              rw [hL, hR]
              split
              · next hcond =>
                  simp only [hcond, List.take_succ_cons]
                  exact congrArg (a :: ·) (ih as (b :: bs) h')
              · next hcond =>
                  simp only [hcond, List.take_succ_cons]
                  exact congrArg (b :: ·) (ih (a :: as) bs (Nat.le_trans h' (Nat.le_succ as.length)))

private theorem take_merge_lists {α : Type} (le : α → α → Bool) (n : Nat) (xs ys : List α) :
    (List.merge xs ys le).take n = (List.merge (xs.take n) (ys.take n) le).take n := by
  induction n generalizing xs ys with
  | zero => simp
  | succ n ih =>
      match xs, ys with
      | [], ys =>
          simp [List.take_take, Nat.min_self]
      | x :: xs, [] =>
          simp [List.take_take, Nat.min_self, List.take_succ_cons]
      | x :: xs, y :: ys =>
          simp only [List.take_succ_cons]
          have hL := merge_cons_cons le x y xs ys
          have hR := merge_cons_cons le x y (xs.take n) (ys.take n)
          rw [hL, hR]
          cases hle : le x y with
          | true =>
              simp only [ite_true, List.take_succ_cons]
              congr 1
              rw [ih xs (y :: ys)]
              cases n with
              | zero => simp
              | succ m =>
                  simp only [List.take_succ_cons]
                  by_cases hlen : m < ys.length
                  · have hget := List.take_append_getElem (l := ys) (i := m) hlen
                    have happ := take_merge_append_right le (m + 1) (xs.take (m + 1))
                      (y :: ys.take m) ys[m] (by simp; omega)
                    simpa [hget, List.cons_append] using happ.symm
                  · have hle' : ys.length ≤ m := Nat.le_of_not_gt hlen
                    simp [List.take_of_length_le hle', List.take_of_length_le (Nat.le_succ_of_le hle')]
          | false =>
              simp only [Bool.false_eq_true, ite_false, List.take_succ_cons]
              congr 1
              rw [ih (x :: xs) ys]
              cases n with
              | zero => simp
              | succ m =>
                  simp only [List.take_succ_cons]
                  by_cases hlen : m < xs.length
                  · have hget := List.take_append_getElem (l := xs) (i := m) hlen
                    have happ := take_merge_append_left le (m + 1) (x :: xs.take m)
                      (ys.take (m + 1)) xs[m] (by simp; omega)
                    simpa [hget, List.cons_append] using happ.symm
                  · have hle' : xs.length ≤ m := Nat.le_of_not_gt hlen
                    simp [List.take_of_length_le hle', List.take_of_length_le (Nat.le_succ_of_le hle')]

theorem take_mergeTwo (n : Nat) (xs ys : List (FitBytes × FitBytes)) :
    (mergeTwo xs ys).take n = (mergeTwo (xs.take n) (ys.take n)).take n := by
  simpa [mergeTwo] using take_merge_lists keyLe n xs ys

theorem take_mergeAll (n : Nat) (ps : List (List (FitBytes × FitBytes))) :
    (mergeAll ps).take n = (mergeAll (ps.map (·.take n))).take n := by
  induction ps with
  | nil => simp [mergeAll]
  | cons p ps ih =>
      simp only [List.map_cons, mergeAll]
      rw [take_mergeTwo n p (mergeAll ps), ih]
      have h := take_mergeTwo n (p.take n) (mergeAll (ps.map (·.take n)))
      simp only [List.take_take, Nat.min_self] at h
      exact h.symm

/-- Sorted merge of one snapshot per part. This is the global iterate. -/
def clusterEntries (parts : List Map) : List (FitBytes × FitBytes) :=
  mergeAll (parts.map entries)

theorem clusterEntries_mem (parts : List Map) (e : FitBytes × FitBytes) :
    e ∈ clusterEntries parts ↔ ∃ p, p ∈ parts ∧ e ∈ p := by
  unfold clusterEntries
  rw [mem_mergeAll]
  constructor
  · intro h
    obtain ⟨rows, hrows, he⟩ := h
    simp only [List.mem_map] at hrows
    obtain ⟨p, hp, rfl⟩ := hrows
    exact ⟨p, hp, (entries_mem p e).mp he⟩
  · intro h
    obtain ⟨p, hp, he⟩ := h
    exact ⟨entries p, List.mem_map_of_mem hp, (entries_mem p e).mpr he⟩

theorem clusterEntries_sorted (parts : List Map) :
    (clusterEntries parts).Pairwise (fun a b => keyLe a b = true) := by
  unfold clusterEntries
  refine mergeAll_sorted _ ?_
  intro rows hrows
  simp only [List.mem_map] at hrows
  obtain ⟨m, _, rfl⟩ := hrows
  exact entries_sorted m

def shardViews (bounds : List Bytes) (m : Map) : List Map :=
  (List.range (bounds.length + 1)).map fun s => inShard bounds s m

/-- The ordered merge of the home shards has exactly the entries of the map. -/
theorem cluster_partition (bounds : List Bytes) (m : Map) (e : FitBytes × FitBytes) :
    e ∈ clusterEntries (shardViews bounds m) ↔ e ∈ m := by
  rw [clusterEntries_mem]
  constructor
  · intro h
    obtain ⟨p, hp, he⟩ := h
    simp only [shardViews, List.mem_map, List.mem_range] at hp
    obtain ⟨s, _, rfl⟩ := hp
    exact (mem_inShard bounds s m e).mp he |>.1
  · intro he
    let s := shardOf bounds e.1.bytes
    refine ⟨inShard bounds s m, ?_, mem_home bounds m e he⟩
    simp only [shardViews, List.mem_map, List.mem_range]
    exact ⟨s, shardOf_range bounds e.1.bytes, rfl⟩

/-! ## A crash on one shard leaves the others -/

/-- Replace shard `i` and keep every other id. -/
def afterCrash (logs : Nat → List Record) (i : Nat) (kept : List Record) : Nat → List Record :=
  fun j => if j = i then kept else logs j

theorem crash_others (logs : Nat → List Record) (i j : Nat) (kept : List Record)
    (hj : j ≠ i) : afterCrash logs i kept j = logs j := by
  simp [afterCrash, hj]

/-- The shard that crashed comes back as a record prefix. Other ids are `crash_others`. -/
theorem crash_shard_independent (logs : Nat → List Record) (i n : Nat)
    (h : RecordsFit (logs i)) :
    ∃ k, decodeFile ((encodeFile (logs i)).take n) = .ok ((logs i).take k) :=
  decodeFile_prefix (logs i) n h

end Cairn
