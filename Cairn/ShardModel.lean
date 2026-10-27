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
