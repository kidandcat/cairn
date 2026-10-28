/-
Time-ordered identifiers. 48 bits of milliseconds, then 80 bits of entropy,
both big-endian, so lexicographic byte order is time order.

`fresh` is the pure step. A test passes a counter as the clock. If the clock
does not move past the previous id, the random part increments, and on
overflow the time does. The generator refuses past 2^48.
-/

import Cairn.Bytes

namespace Cairn

def beBytes : Nat → Nat → Bytes
  | 0, _ => []
  | n + 1, x =>
      let base := 256 ^ n
      UInt8.ofNat (x / base) :: beBytes n (x % base)

theorem beBytes_length (n x : Nat) : (beBytes n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [beBytes, ih]

private theorem byte_lt {a b : Nat} (ha : a < 256) (hb : b < 256) (h : a < b) :
    UInt8.ofNat a < UInt8.ofNat b := by
  rw [UInt8.lt_iff_toNat_lt]
  have ha' : (UInt8.ofNat a).toNat = a := by
    simpa [UInt8.toNat_ofNat] using Nat.mod_eq_of_lt ha
  have hb' : (UInt8.ofNat b).toNat = b := by
    simpa [UInt8.toNat_ofNat] using Nat.mod_eq_of_lt hb
  rw [ha', hb']
  exact h

private theorem pow_succ (n : Nat) : 256 ^ (n + 1) = 256 ^ n * 256 := by
  rw [Nat.pow_succ, Nat.mul_comm]

/-- Fixed-width big-endian order agrees with numeric order. -/
theorem beBytes_lt (n a b : Nat) (ha : a < 256 ^ n) (hb : b < 256 ^ n) (h : a < b) :
    beBytes n a < beBytes n b := by
  induction n generalizing a b with
  | zero =>
      simp [Nat.pow_zero] at ha hb
      omega
  | succ n ih =>
      rw [pow_succ] at ha hb
      have hbase : 0 < 256 ^ n := Nat.pow_pos (by decide : 0 < 256)
      have hqa : a / 256 ^ n < 256 := by
        have hmul := Nat.mul_div_le a (256 ^ n)
        have halt : a < 256 ^ n * 256 := by simpa [Nat.mul_comm] using ha
        have hstep : 256 ^ n * (a / 256 ^ n) < 256 ^ n * 256 := Nat.lt_of_le_of_lt hmul halt
        exact (Nat.mul_lt_mul_left hbase).mp hstep
      have hqb : b / 256 ^ n < 256 := by
        have hmul := Nat.mul_div_le b (256 ^ n)
        have halt : b < 256 ^ n * 256 := by simpa [Nat.mul_comm] using hb
        have hstep : 256 ^ n * (b / 256 ^ n) < 256 ^ n * 256 := Nat.lt_of_le_of_lt hmul halt
        exact (Nat.mul_lt_mul_left hbase).mp hstep
      have hra : a % 256 ^ n < 256 ^ n := Nat.mod_lt _ hbase
      have hrb : b % 256 ^ n < 256 ^ n := Nat.mod_lt _ hbase
      simp only [beBytes]
      by_cases hq : a / 256 ^ n = b / 256 ^ n
      · have hrest : a % 256 ^ n < b % 256 ^ n := by
          have ha' : 256 ^ n * (a / 256 ^ n) + a % 256 ^ n = a := Nat.div_add_mod a (256 ^ n)
          have hb' : 256 ^ n * (b / 256 ^ n) + b % 256 ^ n = b := Nat.div_add_mod b (256 ^ n)
          rw [← ha', ← hb', hq] at h
          exact Nat.lt_of_add_lt_add_left h
        rw [hq]
        exact List.Lex.cons (ih _ _ hra hrb hrest)
      · have hlt : a / 256 ^ n < b / 256 ^ n := by
          have hle : a / 256 ^ n ≤ b / 256 ^ n := Nat.div_le_div_right (Nat.le_of_lt h)
          omega
        exact List.Lex.rel (byte_lt hqa hqb hlt)

structure Ulid where
  time : Nat
  rand : Nat
  htime : time < 2 ^ 48
  hrand : rand < 2 ^ 80
  deriving Repr

def Ulid.encode (u : Ulid) : Bytes :=
  beBytes 6 u.time ++ beBytes 10 u.rand

theorem Ulid.encode_length (u : Ulid) : (Ulid.encode u).length = 16 := by
  simp [Ulid.encode, beBytes_length]

def Ulid.lt (a b : Ulid) : Prop :=
  a.time < b.time ∨ (a.time = b.time ∧ a.rand < b.rand)

private theorem lex_prefix {α} {r : α → α → Prop} {a b s t : List α}
    (h : List.Lex r a b) (hlen : a.length = b.length) :
    List.Lex r (a ++ s) (b ++ t) := by
  induction h with
  | nil =>
      simp at hlen
  | @rel a1 l1 a2 l2 hr =>
      exact List.Lex.rel hr
  | @cons a l1 l2 ht ih =>
      have htail : l1.length = l2.length := by simpa using hlen
      exact List.Lex.cons (ih htail)

private theorem lex_same_prefix {α} {r : α → α → Prop} {p s t : List α}
    (h : List.Lex r s t) : List.Lex r (p ++ s) (p ++ t) := by
  induction p with
  | nil => exact h
  | cons x xs ih => exact List.Lex.cons ih

theorem Ulid.encode_lt_of_lt {a b : Ulid} (h : Ulid.lt a b) :
    Ulid.encode a < Ulid.encode b := by
  rcases h with htime | ⟨heq, hrand⟩
  · have hpre : beBytes 6 a.time < beBytes 6 b.time :=
      beBytes_lt 6 a.time b.time a.htime b.htime htime
    have hlen : (beBytes 6 a.time).length = (beBytes 6 b.time).length := by
      simp [beBytes_length]
    simpa [Ulid.encode] using lex_prefix hpre hlen
  · have hpre : beBytes 10 a.rand < beBytes 10 b.rand :=
      beBytes_lt 10 a.rand b.rand a.hrand b.hrand hrand
    simpa [Ulid.encode, heq] using lex_same_prefix (p := beBytes 6 a.time) hpre

def Ulid.bump (u : Ulid) : Option Ulid :=
  if h : u.rand + 1 < 2 ^ 80 then
    some ⟨u.time, u.rand + 1, u.htime, h⟩
  else if h : u.time + 1 < 2 ^ 48 then
    some ⟨u.time + 1, 0, h, by decide⟩
  else
    none

theorem Ulid.bump_lt (u v : Ulid) (h : Ulid.bump u = some v) : Ulid.lt u v := by
  unfold Ulid.bump at h
  split at h
  · cases h
    exact Or.inr ⟨rfl, Nat.lt_succ_self _⟩
  · split at h
    · cases h
      exact Or.inl (Nat.lt_succ_self _)
    · cases h

/-- Next id. A later millisecond wins. Otherwise the previous id is bumped. -/
def Ulid.fresh (prev : Option Ulid) (now entropy : Nat) : Option Ulid :=
  let ent := entropy % 2 ^ 80
  if hnow : now < 2 ^ 48 then
    have hent : ent < 2 ^ 80 := Nat.mod_lt _ (by decide)
    match prev with
    | none => some ⟨now, ent, hnow, hent⟩
    | some p =>
        if p.time < now then
          some ⟨now, ent, hnow, hent⟩
        else
          p.bump
  else
    match prev with
    | none => none
    | some p => p.bump

theorem Ulid.fresh_increases (p q : Ulid) (now entropy : Nat)
    (h : Ulid.fresh (some p) now entropy = some q) : Ulid.lt p q := by
  unfold Ulid.fresh at h
  by_cases hnow : now < 2 ^ 48
  · simp only [hnow, dite_true] at h
    by_cases ht : p.time < now
    · simp only [ht, ite_true] at h
      cases h
      exact Or.inl ht
    · simp only [ht, ite_false] at h
      exact bump_lt p q h
  · simp only [hnow, dite_false] at h
    exact bump_lt p q h

structure Clock where
  millis : IO Nat
  entropy : IO Nat

def Clock.counter (r : IO.Ref Nat) : Clock where
  millis := do
    let n ← r.get
    r.set (n + 1)
    return n
  entropy := pure 0

def Clock.fixed (ms : Nat) (ent : Nat) : Clock where
  millis := pure ms
  entropy := pure ent

structure IdGen where
  clock : Clock
  prev : IO.Ref (Option Ulid)

def IdGen.new (clock : Clock) : IO IdGen := do
  let prev ← IO.mkRef none
  return { clock, prev }

def IdGen.next (g : IdGen) : IO Ulid := do
  let now ← g.clock.millis
  let ent ← g.clock.entropy
  let p ← g.prev.get
  match Ulid.fresh p now ent with
  | some id =>
      g.prev.set (some id)
      return id
  | none => throw (IO.userError "ulid space exhausted")

end Cairn
