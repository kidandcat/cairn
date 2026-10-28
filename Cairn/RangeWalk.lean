/-
Pages read from the tree, not from a filtered `entries` list.

`rangeWalk` / `prefixWalk` start at the lower bound (`Std.TreeMap` slice) and
stop after `limit` entries. They are proved equal to `rangePage` / `prefixPage`,
so `rangeHits_mem`, `prefixHits_mem`, and `resume_hits` still describe the page.
The zipper walk is what the library does; a big-O bound is not a cairn theorem.
-/

import Cairn.Range

open Std

namespace Cairn

private theorem isLE_swap (a b : FitBytes) :
    (cmpKey a b).isLE = (cmpKey b a).isGE := by
  have hs := OrientedCmp.eq_swap (cmp := cmpKey) (a := a) (b := b)
  cases hab : cmpKey a b <;> rw [hab] at hs <;> cases hba : cmpKey b a <;>
    simp_all [Ordering.swap, Ordering.isLE, Ordering.isGE]

private theorem eq_lt_isGT (a b : FitBytes) :
    (cmpKey a b == .lt) = (cmpKey b a).isGT := by
  have hs := OrientedCmp.eq_swap (cmp := cmpKey) (a := a) (b := b)
  cases hab : cmpKey a b <;> rw [hab] at hs <;> cases hba : cmpKey b a <;>
    simp_all [Ordering.swap, Ordering.isGT]

private theorem beq_lt_isLT (a b : FitBytes) :
    (cmpKey a b == .lt) = (cmpKey a b).isLT := by
  cases h : cmpKey a b <;> simp [h, Ordering.isLT]

private theorem cmp_lt_trans {a b c : FitBytes}
    (hab : cmpKey a b = .lt) (hbc : cmpKey b c = .lt) : cmpKey a c = .lt := by
  have hle := TransCmp.isLE_trans (cmp := cmpKey) (a := a) (b := b) (c := c)
    (by simp [hab, Ordering.isLE]) (by simp [hbc, Ordering.isLE])
  cases hac : cmpKey a c with
  | lt => rfl
  | eq =>
      have heq : a = c := LawfulEqCmp.eq_of_compare (cmp := cmpKey) hac
      have hab' : cmpKey c b = .lt := by simpa [heq] using hab
      have hs := OrientedCmp.eq_swap (cmp := cmpKey) (a := c) (b := b)
      rw [hab', hbc] at hs
      simp [Ordering.swap] at hs
  | gt =>
      simp [Ordering.isLE, hac] at hle

private theorem after_follows {c a k : FitBytes}
    (hca : cmpKey c a = .lt) (hle : (cmpKey a k).isLE = true) : cmpKey c k = .lt := by
  cases hak : cmpKey a k with
  | lt => exact cmp_lt_trans hca hak
  | eq =>
      have heq : a = k := LawfulEqCmp.eq_of_compare (cmp := cmpKey) hak
      simpa [heq] using hca
  | gt => simp [Ordering.isLE, hak] at hle

private theorem lo_follows {c a k : FitBytes}
    (hnot : (cmpKey c a == .lt) = false) (hgt : cmpKey c k = .lt) :
    (cmpKey a k).isLE = true := by
  cases hca : cmpKey c a with
  | lt => simp [hca] at hnot
  | eq =>
      have heq : c = a := LawfulEqCmp.eq_of_compare (cmp := cmpKey) hca
      have hgt' : cmpKey a k = .lt := by simpa [heq] using hgt
      simp [hgt', Ordering.isLE]
  | gt =>
      have hs := OrientedCmp.eq_swap (cmp := cmpKey) (a := c) (b := a)
      rw [hca] at hs
      have hac : cmpKey a c = .lt := by
        cases h : cmpKey a c <;> simp [h, Ordering.swap] at hs
        rfl
      simp [cmp_lt_trans hac hgt, Ordering.isLE]

/-- Inclusive `lo` and a strict cursor: the tighter of the two lower bounds. -/
private theorem lower_eq (a c k : FitBytes) :
    ((cmpKey a k).isLE && strictlyAfter c k) =
      (if cmpKey c a == .lt then (cmpKey k a).isGE else (cmpKey k c).isGT) := by
  simp only [strictlyAfter, isLE_swap a k, eq_lt_isGT c k]
  cases hca : cmpKey c a == .lt with
  | true =>
      simp only [hca, ite_true]
      cases hge : (cmpKey k a).isGE with
      | false => simp [hge]
      | true =>
          cases hgt : (cmpKey k c).isGT with
          | true => simp [hge, hgt]
          | false =>
              have hle : (cmpKey a k).isLE = true := by simpa [isLE_swap a k] using hge
              have hlt : cmpKey c a = .lt := (beq_iff_eq).mp hca
              have hck : cmpKey c k = .lt := after_follows hlt hle
              have hgt' : (cmpKey k c).isGT = true := by
                simpa [eq_lt_isGT c k] using (by simp [hck] : (cmpKey c k == .lt) = true)
              simp [hgt'] at hgt
  | false =>
      simp only [Bool.false_eq_true]
      cases hge : (cmpKey k a).isGE <;> cases hgt : (cmpKey k c).isGT
      · simp [hge, hgt]
      · have hck : cmpKey c k = .lt := by
          have : (cmpKey c k == .lt) = true := by simpa [eq_lt_isGT c k] using hgt
          exact (beq_iff_eq).mp this
        have hle : (cmpKey a k).isLE = true := lo_follows hca hck
        have hge' : (cmpKey k a).isGE = true := by simpa [isLE_swap a k] using hle
        simp [hge'] at hge
      · simp [hge, hgt]
      · simp [hge, hgt]

private theorem and_right_comm (a b c : Bool) : ((a && b) && c) = ((a && c) && b) := by
  cases a with
  | false => simp [Bool.false_and]
  | true =>
      cases b <;> cases c <;> simp [Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false]

private theorem ite_and (p a b c : Bool) :
    (if p then (a && c) else (b && c)) = ((if p then a else b) && c) := by
  cases p <;> rfl

/-- Same predicate as `inRange`, written as one tree interval. -/
def walkPred (lo hi after : Option FitBytes) (k : FitBytes) : Bool :=
  match lo, after with
  | none, none =>
      match hi with
      | none => true
      | some b => (cmpKey k b).isLT
  | none, some c =>
      match hi with
      | none => (cmpKey k c).isGT
      | some b => (cmpKey k c).isGT && (cmpKey k b).isLT
  | some a, none =>
      match hi with
      | none => (cmpKey k a).isGE
      | some b => (cmpKey k a).isGE && (cmpKey k b).isLT
  | some a, some c =>
      if cmpKey c a == .lt then
        match hi with
        | none => (cmpKey k a).isGE
        | some b => (cmpKey k a).isGE && (cmpKey k b).isLT
      else
        match hi with
        | none => (cmpKey k c).isGT
        | some b => (cmpKey k c).isGT && (cmpKey k b).isLT

def rangeWalk (m : Map) (lo hi after : Option FitBytes) (limit : Nat) :
    List (FitBytes × FitBytes) :=
  match lo, after with
  | none, none =>
      match hi with
      | none => treeHead m limit
      | some b => treeLT m b limit
  | none, some c =>
      match hi with
      | none => treeGT m c limit
      | some b => treeGT_LT m c b limit
  | some a, none =>
      match hi with
      | none => treeGE m a limit
      | some b => treeGE_LT m a b limit
  | some a, some c =>
      if cmpKey c a == .lt then
        match hi with
        | none => treeGE m a limit
        | some b => treeGE_LT m a b limit
      else
        match hi with
        | none => treeGT m c limit
        | some b => treeGT_LT m c b limit

theorem inRange_eq_walkPred (lo hi after : Option FitBytes) (k : FitBytes) :
    inRange lo hi after k = walkPred lo hi after k := by
  cases lo with
  | none =>
      cases after with
      | none =>
          cases hi with
          | none => simp [inRange, walkPred]
          | some b => simp [inRange, walkPred, beq_lt_isLT k b]
      | some c =>
          cases hi with
          | none => simp [inRange, walkPred, strictlyAfter, eq_lt_isGT c k]
          | some b =>
              simp [inRange, walkPred, strictlyAfter, eq_lt_isGT c k, beq_lt_isLT k b, Bool.and_comm]
  | some a =>
      cases after with
      | none =>
          cases hi with
          | none => simp [inRange, walkPred, isLE_swap a k]
          | some b =>
              simp [inRange, walkPred, isLE_swap a k, beq_lt_isLT k b]
      | some c =>
          cases hi with
          | none =>
              simp only [inRange, walkPred, Bool.and_true]
              exact lower_eq a c k
          | some b =>
              simp only [inRange, walkPred]
              rw [and_right_comm (cmpKey a k).isLE (cmpKey k b == .lt) (strictlyAfter c k)]
              rw [lower_eq a c k, ite_and (cmpKey c a == .lt)]
              simp [beq_lt_isLT k b]

private theorem filter_true (rows : List (FitBytes × FitBytes)) :
    rows.filter (fun _ => true) = rows :=
  List.filter_eq_self.mpr (fun _ _ => rfl)

private theorem rangeWalk_pred (m : Map) (lo hi after : Option FitBytes) (limit : Nat) :
    rangeWalk m lo hi after limit =
      ((entries m).filter (fun e => walkPred lo hi after e.1)).take limit := by
  cases lo <;> cases after <;> cases hi <;>
    simp [rangeWalk, walkPred, treeHead_eq, treeLT_eq, treeGT_eq, treeGE_eq, treeGE_LT_eq,
      treeGT_LT_eq, filter_true, Bool.and_true, Bool.true_and]
  all_goals
    split <;>
      simp [treeGE_eq, treeGT_eq, treeGE_LT_eq, treeGT_LT_eq, Bool.and_true]

theorem rangeWalk_eq (m : Map) (lo hi after : Option FitBytes) (limit : Nat) :
    rangeWalk m lo hi after limit = rangePage m lo hi after limit := by
  rw [rangeWalk_pred]
  simp only [rangePage, takePage, rangeHits, hits]
  refine congrArg (List.take limit) ?_
  refine List.filter_congr ?_
  intro e _
  exact (inRange_eq_walkPred lo hi after e.1).symm

theorem rangeWalk_cursor (m : Map) (lo hi after : Option FitBytes) (limit : Nat) :
    pageCursor limit (rangeWalk m lo hi after limit) =
      pageCursor limit (rangeHits m lo hi after) := by
  rw [rangeWalk_eq, rangePage, takePage, pageCursor_page]

/-! ## Prefixes are one byte interval -/

def prefixSucc : Bytes → Option Bytes
  | [] => none
  | b :: bs =>
      match prefixSucc bs with
      | some t => some (b :: t)
      | none => if b == 255 then none else some [b + 1]

private theorem prefixSucc_cons (b : UInt8) (bs : Bytes) :
    prefixSucc (b :: bs) =
      match prefixSucc bs with
      | some t => some (b :: t)
      | none => if b == 255 then none else some [b + 1] := by
  conv =>
    lhs
    unfold prefixSucc

theorem prefixSucc_length_le {p s : Bytes} (h : prefixSucc p = some s) :
    s.length ≤ p.length := by
  induction p generalizing s with
  | nil => simp [prefixSucc] at h
  | cons b bs ih =>
      cases ht : prefixSucc bs with
      | some t =>
          have hstep : prefixSucc (b :: bs) = some (b :: t) := by
            simp [prefixSucc_cons, ht]
          rw [hstep] at h
          cases h
          have := ih ht
          simp
          omega
      | none =>
          cases hb : b == 255 with
          | true =>
              have hstep : prefixSucc (b :: bs) = none := by
                simp [prefixSucc_cons, ht, hb]
              simp [hstep] at h
          | false =>
              have hstep : prefixSucc (b :: bs) = some [b + 1] := by
                simp [prefixSucc_cons, ht, hb]
              rw [hstep] at h
              cases h
              simp

private theorem u8_toNat_255 : (255 : UInt8).toNat = 255 := by decide

private theorem u8_toNat_one : (1 : UInt8).toNat = 1 := by decide

private theorem u8_ne_255_toNat {b : UInt8} (h : b ≠ 255) : b.toNat ≠ 255 := by
  intro he
  exact h (UInt8.toNat_inj.mp (he.trans u8_toNat_255.symm))

private theorem u8_below_size (b : UInt8) : b.toNat < 256 := by
  have h := UInt8.toNat_lt_size b
  simp [UInt8.size] at h
  exact h

private theorem u8_lt_succ {b : UInt8} (h : b ≠ 255) : b < b + 1 := by
  rw [UInt8.lt_iff_toNat_lt, UInt8.toNat_add, u8_toNat_one]
  have hmod : b.toNat + 1 < 256 := by
    have hne := u8_ne_255_toNat h
    have := u8_below_size b
    omega
  rw [Nat.mod_eq_of_lt hmod]
  omega

private theorem u8_not_lt_max {c : UInt8} : ¬ (255 : UInt8) < c := by
  intro hlt
  rw [UInt8.lt_iff_toNat_lt, u8_toNat_255] at hlt
  have hc := u8_below_size c
  omega

private theorem u8_compare_lt {a b : UInt8} (h : compare a b = .lt) : a < b := by
  have hcmp : compare a b = compareOfLessAndEq a b := rfl
  exact (compareOfLessAndEq_eq_lt).mp (hcmp ▸ h)

private theorem u8_lt_compare {a b : UInt8} (h : a < b) : compare a b = .lt := by
  simp [compare, compareOfLessAndEq, h]

private theorem u8_succ_le {b c : UInt8} (hmax : b ≠ 255) (hlt : b < c) : b + 1 ≤ c := by
  rw [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt] at *
  rw [UInt8.toNat_add, u8_toNat_one]
  have hmod : b.toNat + 1 < 256 := by
    have hne := u8_ne_255_toNat hmax
    have := u8_below_size b
    omega
  rw [Nat.mod_eq_of_lt hmod]
  omega

private theorem u8_swap (b c : UInt8) : compare c b = (compare b c).swap := by
  simpa using (OrientedCmp.eq_swap (cmp := compare (α := UInt8)) (a := c) (b := b))

private theorem compare_nil_right_not_lt (ks : Bytes) :
    (compare ks ([] : Bytes)).isLT = false := by
  cases ks <;> simp [List.compare_cons_nil, List.compare_nil_nil, Ordering.isLT]

private theorem ord_isLT_beq (o : Ordering) : o.isLT = (o == .lt) := by
  cases o <;> simp [Ordering.isLT]

theorem isPrefixOf_iff_bounds (p k : Bytes) :
    p.isPrefixOf k =
      ((compare p k).isLE &&
        match prefixSucc p with
        | none => true
        | some s => (compare k s).isLT) := by
  induction p generalizing k with
  | nil =>
      simp [prefixSucc, List.isPrefixOf_nil_left, List.isLE_compare_nil_left]
  | cons b bs ih =>
      cases k with
      | nil =>
          simp [List.isPrefixOf_cons_nil, List.compare_cons_nil, Ordering.isLE, Bool.false_and]
      | cons c ks =>
          rw [List.isPrefixOf_cons_cons, List.compare_cons_cons]
          have ihk := ih ks
          cases hbs : prefixSucc bs with
          | some t =>
              have hstep : prefixSucc (b :: bs) = some (b :: t) := by
                simp [prefixSucc_cons, hbs]
              rw [hstep, ihk, hbs]
              simp only [List.compare_cons_cons]
              cases hbc : compare b c with
              | eq =>
                  have hcb : compare c b = .eq := by
                    have hs := u8_swap b c
                    rw [hbc] at hs
                    simpa [Ordering.swap] using hs
                  have hbeq : (b == c) = true := (LawfulBEqOrd.compare_eq_iff_beq).mp hbc
                  simp [hbc, hcb, hbeq, Ordering.then, Ordering.isLE, Ordering.isLT]
              | lt =>
                  have hcb : compare c b = .gt := by
                    have hs := u8_swap b c
                    rw [hbc] at hs
                    simpa [Ordering.swap] using hs
                  have hbeq : (b == c) = false :=
                    (LawfulBEqOrd.not_compare_eq_iff_beq_eq_false).mp (by simp [hbc])
                  simp [hbc, hcb, hbeq, Ordering.then, Ordering.isLE, Ordering.isLT]
              | gt =>
                  have hcb : compare c b = .lt := by
                    have hs := u8_swap b c
                    rw [hbc] at hs
                    simpa [Ordering.swap] using hs
                  have hbeq : (b == c) = false :=
                    (LawfulBEqOrd.not_compare_eq_iff_beq_eq_false).mp (by simp [hbc])
                  simp [hbc, hcb, hbeq, Ordering.then, Ordering.isLE, Ordering.isLT]
          | none =>
              cases hb : b == 255 with
              | true =>
                  have hstep : prefixSucc (b :: bs) = none := by
                    simp [prefixSucc_cons, hbs, hb]
                  rw [hstep, ihk, hbs]
                  have hbv : b = 255 := (beq_iff_eq).mp hb
                  cases hbc : compare b c with
                  | eq =>
                      have hbeq : (b == c) = true := (LawfulBEqOrd.compare_eq_iff_beq).mp hbc
                      have hcb : compare c b = .eq := by
                        have hs := u8_swap b c
                        rw [hbc] at hs
                        simpa [Ordering.swap] using hs
                      simp [hbc, hcb, hbeq, Ordering.then, Ordering.isLE, Bool.and_true]
                  | lt =>
                      exact False.elim (u8_not_lt_max (by simpa [hbv] using u8_compare_lt hbc))
                  | gt =>
                      have hbeq : (b == c) = false :=
                        (LawfulBEqOrd.not_compare_eq_iff_beq_eq_false).mp (by simp [hbc])
                      simp [hbc, hbeq, Ordering.then, Ordering.isLE, Bool.false_and]
              | false =>
                  have hstep : prefixSucc (b :: bs) = some [b + 1] := by
                    simp [prefixSucc_cons, hbs, hb]
                  rw [hstep, ihk, hbs]
                  have hmax : b ≠ 255 := by
                    intro heq
                    have : (b == 255) = true := (beq_iff_eq).mpr heq
                    simp [this] at hb
                  have hsucc : compare b (b + 1) = .lt := u8_lt_compare (u8_lt_succ hmax)
                  cases hbc : compare b c with
                  | eq =>
                      have hbeq : (b == c) = true := (LawfulBEqOrd.compare_eq_iff_beq).mp hbc
                      have hc : c = b := (LawfulEqOrd.eq_of_compare hbc).symm
                      have hup : compare (c :: ks) ((b + 1) :: []) = .lt := by
                        rw [List.compare_cons_cons, hc, hsucc]
                        simp [Ordering.then]
                      simp [hbc, hbeq, hup, Ordering.then, Ordering.isLE, Ordering.isLT, Bool.and_true]
                  | lt =>
                      have hbeq : (b == c) = false :=
                        (LawfulBEqOrd.not_compare_eq_iff_beq_eq_false).mp (by simp [hbc])
                      have hle : b + 1 ≤ c := u8_succ_le hmax (u8_compare_lt hbc)
                      have hnot : compare c (b + 1) ≠ .lt := by
                        intro hlt
                        exact lt_irrefl (lt_of_lt_of_le (u8_compare_lt hlt) hle)
                      cases hcb : compare c (b + 1) with
                      | lt => exact absurd hcb hnot
                      | eq =>
                          simp [hbc, hbeq, hcb, List.compare_cons_cons, Ordering.then, Ordering.isLE,
                            compare_nil_right_not_lt ks, Bool.false_and]
                      | gt =>
                          simp [hbc, hbeq, hcb, List.compare_cons_cons, Ordering.then, Ordering.isLE,
                            Ordering.isLT, Bool.false_and]
                  | gt =>
                      have hbeq : (b == c) = false :=
                        (LawfulBEqOrd.not_compare_eq_iff_beq_eq_false).mp (by simp [hbc])
                      simp [hbc, hbeq, Ordering.then, Ordering.isLE, Bool.false_and]

def prefixHi (p : Bytes) (h : p.length < UInt32.size) : Option FitBytes :=
  match prefixSucc p with
  | none => none
  | some s =>
      if hs : s.length < UInt32.size then
        some ⟨s, hs⟩
      else
        none

def prefixBound (p : Bytes) : Option (FitBytes × Option FitBytes) :=
  if h : p.length < UInt32.size then
    some (⟨p, h⟩, prefixHi p h)
  else
    none

theorem hasPrefix_eq_bounds (p : Bytes) (h : p.length < UInt32.size) (k : FitBytes) :
    hasPrefix p k = inRange (some ⟨p, h⟩) (prefixHi p h) none k := by
  simp only [hasPrefix, inRange, Bool.and_true, cmpKey]
  rw [isPrefixOf_iff_bounds]
  cases hsucc : prefixSucc p with
  | none =>
      have hhi : prefixHi p h = none := by simp [prefixHi, hsucc]
      simp [hhi]
  | some s =>
      have hlen : s.length < UInt32.size := Nat.lt_of_le_of_lt (prefixSucc_length_le hsucc) h
      have hhi : prefixHi p h = some ⟨s, hlen⟩ := by simp [prefixHi, hsucc, hlen]
      simp [hhi, cmpKey, ord_isLT_beq]

theorem inPrefix_eq_inRange (p : Bytes) (h : p.length < UInt32.size)
    (after : Option FitBytes) (k : FitBytes) :
    inPrefix p after k = inRange (some ⟨p, h⟩) (prefixHi p h) after k := by
  cases after with
  | none =>
      simpa [inPrefix, inRange, Bool.and_true] using hasPrefix_eq_bounds p h k
  | some c =>
      simp only [inPrefix, inRange, strictlyAfter, Bool.and_assoc]
      rw [hasPrefix_eq_bounds p h k]
      simp [inRange, Bool.and_assoc]

def prefixWalk (m : Map) (p : Bytes) (after : Option FitBytes) (limit : Nat) :
    List (FitBytes × FitBytes) :=
  match prefixBound p with
  | none => []
  | some (lo, hi) => rangeWalk m (some lo) hi after limit

private theorem isPrefixOf_length_le {p k : Bytes} (h : p.isPrefixOf k = true) :
    p.length ≤ k.length := by
  induction p generalizing k with
  | nil => simp
  | cons b bs ih =>
      cases k with
      | nil => simp [List.isPrefixOf] at h
      | cons c ks =>
          rw [List.isPrefixOf_cons_cons] at h
          rcases Bool.and_eq_true_iff.mp h with ⟨_, htail⟩
          have := ih htail
          simp
          omega

private theorem not_hasPrefix_long (p : Bytes) (k : FitBytes) (h : ¬ p.length < UInt32.size) :
    hasPrefix p k = false := by
  cases hpre : hasPrefix p k with
  | false => rfl
  | true =>
      have hle := isPrefixOf_length_le (by simpa [hasPrefix] using hpre)
      have hk : k.bytes.length < UInt32.size := k.hlen
      omega

theorem prefixWalk_eq (m : Map) (p : Bytes) (after : Option FitBytes) (limit : Nat) :
    prefixWalk m p after limit = prefixPage m p after limit := by
  unfold prefixWalk prefixBound
  by_cases hlen : p.length < UInt32.size
  · simp only [hlen, dite_true, rangeWalk_eq, rangePage, prefixPage, takePage, rangeHits,
      prefixHits, hits]
    refine congrArg (List.take limit) ?_
    refine List.filter_congr ?_
    intro e _
    exact (inPrefix_eq_inRange p hlen after e.1).symm
  · have hempty : (entries m).filter (fun e => inPrefix p after e.1) = [] := by
      refine List.filter_eq_nil_iff.mpr ?_
      intro e _
      simp [inPrefix, not_hasPrefix_long p e.1 hlen, Bool.false_and]
    simp [hlen, prefixPage, takePage, prefixHits, hits, hempty]

theorem prefixWalk_cursor (m : Map) (p : Bytes) (after : Option FitBytes) (limit : Nat) :
    pageCursor limit (prefixWalk m p after limit) =
      pageCursor limit (prefixHits m p after) := by
  rw [prefixWalk_eq, prefixPage, takePage, pageCursor_page]

end Cairn
