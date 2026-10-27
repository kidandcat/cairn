/-
In-memory index. One persistent size-balanced tree (`Std.TreeMap`, delta 3,
ratio 2). `get` walks that tree. `insert` and `remove` return a new root and
share the untouched branches, so a reader holding an older `View` still sees
the tree it loaded with `IO.Ref.get`.

`entries` is the inorder list: lexicographic on key bytes, each key once.
Compaction replays those bindings. Two trees with the same bindings need not
have the same shape, so the compaction lemmas equate `entries`, not the roots.
-/

import Std.Data.TreeMap
import Std.Data.TreeMap.Lemmas
import Cairn.Bytes

open Std

namespace Cairn

/-- Bytewise order. Equal bytes compare equal, and those are the same `FitBytes`. -/
def cmpKey (a b : FitBytes) : Ordering :=
  compare a.bytes b.bytes

instance : LawfulBEq FitBytes where
  rfl {a} := by
    show (a.bytes == a.bytes) = true
    simp
  eq_of_beq {a b} h := by
    apply FitBytes.eq_of_bytes
    exact eq_of_beq h

instance : TransCmp cmpKey where
  eq_swap {a b} := by
    simpa [cmpKey] using
      (OrientedCmp.eq_swap (cmp := compare (α := List UInt8)) (a := a.bytes) (b := b.bytes))
  isLE_trans {a b c} h1 h2 := by
    simpa [cmpKey] using
      (TransCmp.isLE_trans (cmp := compare (α := List UInt8)) (a := a.bytes) (b := b.bytes)
        (c := c.bytes) h1 h2)

instance : LawfulEqCmp cmpKey where
  compare_self {a} := by
    simp [cmpKey, ReflCmp.compare_self]
  eq_of_compare {a b} h := by
    apply FitBytes.eq_of_bytes
    exact LawfulEqCmp.eq_of_compare (cmp := compare (α := List UInt8)) (by simpa [cmpKey] using h)

abbrev Map := Std.TreeMap FitBytes FitBytes cmpKey

def Map.empty : Map :=
  Std.TreeMap.empty

/-- No two entries carry the same key bytes. The tree keeps this on its own. -/
def NodupKeys (m : Map) : Prop :=
  (Std.TreeMap.toList m).Pairwise (fun a b => a.1.bytes ≠ b.1.bytes)

def get (m : Map) (k : FitBytes) : Option FitBytes :=
  Std.TreeMap.get? m k

def remove (m : Map) (k : FitBytes) : Map :=
  Std.TreeMap.erase m k

def insert (m : Map) (k v : FitBytes) : Map :=
  Std.TreeMap.insert m k v

theorem get_insert (m : Map) (k v : FitBytes) :
    get (insert m k v) k = some v := by
  simp [get, insert]

theorem get_remove (m : Map) (k : FitBytes) : get (remove m k) k = none := by
  simp [get, remove]

theorem get_insert_ne (m : Map) (k k' v : FitBytes) (h : k.bytes ≠ k'.bytes) :
    get (insert m k v) k' = get m k' := by
  have hcmp : ¬ cmpKey k k' = .eq := by
    intro heq
    exact h (congrArg FitBytes.bytes (LawfulEqCmp.eq_of_compare (cmp := cmpKey) heq))
  simp only [get, insert, Std.TreeMap.get?_eq_getElem?]
  rw [Std.TreeMap.getElem?_insert]
  simp [hcmp]

theorem get_remove_ne (m : Map) (k k' : FitBytes) (h : k.bytes ≠ k'.bytes) :
    get (remove m k) k' = get m k' := by
  have hcmp : ¬ cmpKey k k' = .eq := by
    intro heq
    exact h (congrArg FitBytes.bytes (LawfulEqCmp.eq_of_compare (cmp := cmpKey) heq))
  simp only [get, remove, Std.TreeMap.get?_eq_getElem?]
  rw [Std.TreeMap.getElem?_erase]
  simp [hcmp]

theorem nodup_all (m : Map) : NodupKeys m := by
  refine List.Pairwise.imp (fun {a b} (hne : ¬ cmpKey a.1 b.1 = .eq) hbytes => ?_)
    (Std.TreeMap.distinct_keys_toList (t := m))
  apply hne
  have hab : a.1 = b.1 := FitBytes.eq_of_bytes hbytes
  rw [hab]
  exact ReflCmp.compare_self (cmp := cmpKey) (a := b.1)

theorem nodup_nil : NodupKeys Map.empty :=
  nodup_all Map.empty

theorem nodup_remove (m : Map) (k : FitBytes) (h : NodupKeys m) :
    NodupKeys (remove m k) := by
  have _kept : NodupKeys m := h
  exact nodup_all (remove m k)

theorem nodup_insert (m : Map) (k v : FitBytes) (h : NodupKeys m) :
    NodupKeys (insert m k v) := by
  have _kept : NodupKeys m := h
  exact nodup_all (insert m k v)

/-- `Ordering.isLE` of the bytewise order. Total and transitive (`keyLe_total`, `keyLe_trans`). -/
def keyLe (a b : FitBytes × FitBytes) : Bool :=
  (cmpKey a.1 b.1).isLE

theorem keyLe_trans (a b c : FitBytes × FitBytes)
    (h1 : keyLe a b) (h2 : keyLe b c) : keyLe a c := by
  simpa [keyLe] using
    (TransCmp.isLE_trans (cmp := cmpKey) (a := a.1) (b := b.1) (c := c.1) h1 h2)

theorem keyLe_total (a b : FitBytes × FitBytes) : keyLe a b || keyLe b a := by
  cases h : cmpKey a.1 b.1 with
  | lt => simp [keyLe, h]
  | eq => simp [keyLe, h]
  | gt =>
      have hswap : cmpKey b.1 a.1 = .lt := by
        have hs := OrientedCmp.eq_swap (cmp := cmpKey) (a := b.1) (b := a.1)
        simpa [h, Ordering.swap] using hs
      simp [keyLe, hswap]

/-- Entries in lexicographic key order. -/
def entries (m : Map) : List (FitBytes × FitBytes) :=
  Std.TreeMap.toList m

instance : Membership (FitBytes × FitBytes) Map where
  mem m e := e ∈ entries m

theorem mem_iff_entries (m : Map) (e : FitBytes × FitBytes) :
    e ∈ m ↔ e ∈ entries m :=
  Iff.rfl

theorem entries_mem (m : Map) (e : FitBytes × FitBytes) :
    e ∈ entries m ↔ e ∈ m :=
  (mem_iff_entries m e).symm

theorem entries_of_get (m : Map) (k v : FitBytes) :
    (k, v) ∈ entries m ↔ get m k = some v := by
  simp [entries, get, Std.TreeMap.mem_toList_iff_getElem?_eq_some, Std.TreeMap.get?_eq_getElem?]

theorem entries_sorted (m : Map) :
    (entries m).Pairwise (fun a b => keyLe a b = true) := by
  refine List.Pairwise.imp (fun {a b} (hlt : cmpKey a.1 b.1 = .lt) => ?_)
    (Std.TreeMap.ordered_keys_toList (t := m))
  simp [keyLe, hlt]

/-- Each key once. This is what `entries_perm` was for the old list. -/
theorem entries_nodup (m : Map) :
    (entries m).Pairwise (fun a b => a.1.bytes ≠ b.1.bytes) :=
  nodup_all m

theorem entries_agree_of_get (m₁ m₂ : Map) (h : ∀ k, get m₁ k = get m₂ k) :
    entries m₁ = entries m₂ := by
  have heqv : Std.TreeMap.Equiv m₁ m₂ :=
    Std.TreeMap.Equiv.of_forall_constGet?_eq (fun k => by
      simpa [get, Std.TreeMap.get?_eq_getElem?] using h k)
  simpa [entries] using (Std.TreeMap.equiv_iff_toList_eq (t₁ := m₁) (t₂ := m₂)).mp heqv

def ofPairs (es : List (FitBytes × FitBytes)) : Map :=
  es.foldl (fun acc p => insert acc p.1 p.2) Map.empty

theorem foldl_insertMany (m : Map) (es : List (FitBytes × FitBytes)) :
    es.foldl (fun acc p => insert acc p.1 p.2) m = Std.TreeMap.insertMany m es := by
  induction es generalizing m with
  | nil => simp [Std.TreeMap.insertMany_nil]
  | cons p es ih =>
      cases p with
      | mk k v =>
          rw [List.foldl_cons, ih, Std.TreeMap.insertMany_cons]
          rfl

theorem ofPairs_insertMany (es : List (FitBytes × FitBytes)) :
    ofPairs es = Std.TreeMap.insertMany Map.empty es := by
  simpa [ofPairs] using foldl_insertMany Map.empty es

theorem get_ofPairs_entries (m : Map) (k : FitBytes) :
    get (ofPairs (entries m)) k = get m k := by
  rw [ofPairs_insertMany]
  cases hget : get m k with
  | some v =>
      have hmem : (k, v) ∈ entries m := (entries_of_get m k v).mpr hget
      have hdist : (entries m).Pairwise (fun a b => ¬ cmpKey a.1 b.1 = .eq) :=
        Std.TreeMap.distinct_keys_toList (t := m)
      have hgot :=
        Std.TreeMap.getElem?_insertMany_list_of_mem
          (t := Map.empty) (l := entries m) (k := k) (k' := k) (v := v)
          (ReflCmp.compare_self (cmp := cmpKey) (a := k)) hdist hmem
      simpa [get, hget, Std.TreeMap.get?_eq_getElem?] using hgot
  | none =>
      have hnot : ((entries m).map Prod.fst).contains k = false := by
        rw [Bool.eq_false_iff]
        intro hc
        obtain ⟨k', hk', hbeq⟩ := (List.contains_iff_exists_mem_beq).mp hc
        simp only [List.mem_map] at hk'
        obtain ⟨p, hp, hk'eq⟩ := hk'
        cases p with
        | mk k0 v =>
            have hk0 : k0 = k' := hk'eq
            rw [hk0] at hp
            have heqk : k = k' := eq_of_beq hbeq
            rw [heqk] at hget
            have hsome : get m k' = some v := (entries_of_get m k' v).mp hp
            simp [hsome] at hget
      have hgot :=
        Std.TreeMap.getElem?_insertMany_list_of_contains_eq_false
          (t := Map.empty) (l := entries m) (k := k) hnot
      simp only [get, Std.TreeMap.get?_eq_getElem?]
      rw [hgot]
      simp [Map.empty, Std.TreeMap.empty_eq_emptyc]

theorem entries_rebuilt (m : Map) :
    entries (ofPairs (entries m)) = entries m :=
  entries_agree_of_get _ _ (get_ofPairs_entries m)

end Cairn
