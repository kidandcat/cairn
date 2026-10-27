/-
In-memory index. The head of the list is the visible value. `insert` drops
any previous entry for the key and conses, so `get` is first-match.

Iteration sorts a copy. The map itself stays in commit order so replay and
compaction have an obvious oldest-to-newest direction (the reverse of this list).
-/

import Cairn.Bytes

namespace Cairn

abbrev Map := List (FitBytes × FitBytes)

/-- No two entries carry the same key bytes. -/
def NodupKeys (m : Map) : Prop :=
  m.Pairwise (fun a b => a.1.bytes ≠ b.1.bytes)

def keyEq (k : FitBytes) (e : FitBytes × FitBytes) : Bool :=
  decide (e.1.bytes = k.bytes)

def get (m : Map) (k : FitBytes) : Option FitBytes :=
  match m.find? (keyEq k) with
  | some e => some e.2
  | none => none

def remove (m : Map) (k : FitBytes) : Map :=
  m.filter (fun e => !keyEq k e)

def insert (m : Map) (k v : FitBytes) : Map :=
  (k, v) :: remove m k

theorem keyEq_self (k v : FitBytes) : keyEq k (k, v) = true := by
  simp [keyEq]

theorem get_insert (m : Map) (k v : FitBytes) :
    get (insert m k v) k = some v := by
  simp [get, insert, keyEq_self, List.find?_cons_of_pos]

theorem get_remove (m : Map) (k : FitBytes) : get (remove m k) k = none := by
  have hnone : (remove m k).find? (keyEq k) = none := by
    rw [remove, List.find?_filter, List.find?_eq_none]
    intro e _
    cases keyEq k e <;> simp
  simp [get, hnone]

theorem find_remove_ne (m : Map) (k k' : FitBytes) (h : k.bytes ≠ k'.bytes) :
    (remove m k).find? (keyEq k') = m.find? (keyEq k') := by
  induction m with
  | nil => simp [remove]
  | cons e m ih =>
      simp only [remove, List.filter_cons] at ih ⊢
      by_cases he : keyEq k e = true
      · have hnot : ¬ keyEq k' e := by
          intro hk'
          simp only [keyEq, decide_eq_true_eq] at he hk'
          exact h (he.symm.trans hk')
        simp [he, hnot, ih]
      · have hpos : (!keyEq k e) = true := by
          cases hb : keyEq k e <;> simp_all
        cases hk' : keyEq k' e <;> simp [hpos, hk', ih]

theorem get_insert_ne (m : Map) (k k' v : FitBytes) (h : k.bytes ≠ k'.bytes) :
    get (insert m k v) k' = get m k' := by
  have hnot : ¬ keyEq k' (k, v) := by
    simp [keyEq, h]
  simp only [get, insert, List.find?_cons_of_neg hnot, find_remove_ne m k k' h]

theorem nodup_nil : NodupKeys [] := by
  simp [NodupKeys]

theorem nodup_remove (m : Map) (k : FitBytes) (h : NodupKeys m) :
    NodupKeys (remove m k) := by
  simpa [NodupKeys, remove] using List.Pairwise.filter (fun e => !keyEq k e) h

theorem nodup_insert (m : Map) (k v : FitBytes) (h : NodupKeys m) :
    NodupKeys (insert m k v) := by
  refine List.Pairwise.cons ?_ (nodup_remove m k h)
  intro e he
  simp only [remove, List.mem_filter] at he
  have hne : keyEq k e = false := by
    cases hb : keyEq k e <;> simp_all
  simp only [keyEq, decide_eq_false_iff_not] at hne
  exact Ne.symm hne

/-- Lexicographic key order. `≤` on byte lists is the standard library order. -/
def keyLe (a b : FitBytes × FitBytes) : Bool :=
  decide (a.1.bytes ≤ b.1.bytes)

/-- Entries in lexicographic key order. A permutation of the map (proved). -/
def entries (m : Map) : List (FitBytes × FitBytes) :=
  m.mergeSort keyLe

theorem entries_perm (m : Map) : List.Perm (entries m) m := by
  simp [entries, List.mergeSort_perm]

theorem entries_mem (m : Map) (e : FitBytes × FitBytes) :
    e ∈ entries m ↔ e ∈ m := by
  simp [entries, List.mem_mergeSort]

/-
Sortedness is `List.pairwise_mergeSort` once `keyLe` is transitive and total.
Those two facts are `List.le_trans` / `List.le_total` on byte lists, which need
a linear order on `UInt8`. They are proved below when the instances resolve;
if they do not, the permutation theorem above is the one the library relies on.
-/

theorem keyLe_trans (a b c : FitBytes × FitBytes)
    (h1 : keyLe a b) (h2 : keyLe b c) : keyLe a c := by
  simp only [keyLe, decide_eq_true_eq] at h1 h2 ⊢
  exact List.le_trans h1 h2

theorem keyLe_total (a b : FitBytes × FitBytes) : keyLe a b || keyLe b a := by
  have h := List.le_total a.1.bytes b.1.bytes
  cases h with
  | inl h =>
      simp [keyLe, h]
  | inr h =>
      simp [keyLe, h]

theorem entries_sorted (m : Map) :
    (entries m).Pairwise (fun a b => keyLe a b = true) := by
  simpa [entries] using
    List.pairwise_mergeSort (le := keyLe) keyLe_trans keyLe_total m

end Cairn
