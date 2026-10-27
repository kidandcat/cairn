/-
What CRC-32 (`sum32`) actually detects.

`sum32` is the non-reflected CRC, init 0, no final xor, polynomial
`x^32 + 0x04C11DB7`. A fixed-width checksum cannot reject every altered
string: `sum32 [1, 4, 0xC1, 0x1D, 0xB7] = 0`, and that string has odd
Hamming weight, so this polynomial does not detect every odd-weight error.

It does detect every error whose bits lie in some window of 32 consecutive
positions (a burst of width ≤ 32), at every message length. The bound is the
window, not the length of the record. A one-bit error is that burst with
width 1. Two bits at distance ≤ 31 are the same burst. Two bits farther
apart are not claimed: that needs the order of `x` modulo the polynomial,
which is not proved.
-/

import Cairn.Sum32

namespace Cairn

def bitSumFuel : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, n => bitSumFuel fuel (n / 2) + n % 2

def bitSum (n : Nat) : Nat :=
  bitSumFuel 40 n

def weight (bs : List UInt8) : Nat :=
  bs.foldl (fun acc b => acc + bitSum b.toNat) 0

/-- An odd-weight input with CRC 0. Fixed-width CRC does not detect every change. -/
theorem sum32_odd_zero : sum32 [1, 4, 0xC1, 0x1D, 0xB7] = 0 := by
  decide

theorem weight_odd_zero : weight [1, 4, 0xC1, 0x1D, 0xB7] % 2 = 1 := by
  decide

theorem not_all_odd_weight : ∃ bs, sum32 bs = 0 ∧ weight bs % 2 = 1 :=
  ⟨[1, 4, 0xC1, 0x1D, 0xB7], sum32_odd_zero, weight_odd_zero⟩

/-! ## Polynomial model -/

def polyLow : Nat := 0x04C11DB7

def polyNat : Nat := 2 ^ 32 + polyLow

def natShl1 (c : Nat) : Nat :=
  if c / 2 ^ 31 = 1 then
    (c % 2 ^ 31) * 2 ^^^ polyLow
  else
    c * 2

/-- Carryless product. Bit i of the result is the GF(2) coefficient of `x^i`. -/
def clmul (a b : Nat) : Nat :=
  if b = 0 then
    0
  else
    let r := clmul a (b / 2) * 2
    if b % 2 = 1 then r ^^^ a else r
termination_by b

/-- Message polynomial, first byte in the high place. -/
def polyOf (bs : List UInt8) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

def feedBit (c bit : Nat) : Nat :=
  natShl1 (c ^^^ ((bit % 2) * 2 ^ 31))

/-- Feed the top `n` bits of `extra`, one bit at a time. -/
def feedTop : Nat → Nat → Nat → Nat
  | 0, c, _ => c
  | n + 1, c, extra =>
    feedTop n (feedBit c (extra / 2 ^ 31)) ((extra % 2 ^ 31) * 2)

def feedByte (c b : Nat) : Nat :=
  feedTop 8 c ((b % 256) * 2 ^ 24)

def natSum (bs : List UInt8) : Nat :=
  bs.foldl (fun c b => feedByte c b.toNat) 0

def shlFrom : Nat → Nat → Nat
  | 0, c => c
  | n + 1, c => shlFrom n (natShl1 c)

def xorBytes : List UInt8 → List UInt8 → List UInt8
  | a :: as, b :: bs => (a ^^^ b) :: xorBytes as bs
  | _, _ => []

theorem clmul_zero_right (a : Nat) : clmul a 0 = 0 := by
  simp [clmul]

theorem polyNat_odd : polyNat % 2 = 1 := by
  decide

theorem polyLow_lt_32 : polyLow < 2 ^ 32 := by
  decide

theorem polyLow_lt_27 : polyLow < 2 ^ 27 := by
  decide

theorem polyNat_eq_xor : polyNat = 2 ^ 32 ^^^ polyLow := by
  decide

theorem clmul_succ_div (a b : Nat) (hb : b ≠ 0) :
    clmul a b = (clmul a (b / 2) * 2) ^^^ (if b % 2 = 1 then a else 0) := by
  rw [clmul.eq_def]
  simp [hb]
  split
  · rfl
  · simp

theorem mul2_xor (a b : Nat) : (a ^^^ b) * 2 = a * 2 ^^^ b * 2 := by
  simpa [Nat.shiftLeft_eq] using (Nat.shiftLeft_xor_distrib (a := a) (b := b) (i := 1))

theorem xor_cancel_left (a b c : Nat) (h : a ^^^ b = a ^^^ c) : b = c := by
  have h' := congrArg (fun x => a ^^^ x) h
  rw [← Nat.xor_assoc, ← Nat.xor_assoc, Nat.xor_self] at h'
  have hb : b = 0 ^^^ b := (Nat.zero_xor b).symm
  have hc : c = 0 ^^^ c := (Nat.zero_xor c).symm
  rw [← hb, ← hc] at h'
  exact h'

theorem xor_eq_zero_iff (a b : Nat) : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    have h' := congrArg (fun x => x ^^^ b) h
    simp [Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_zero] at h'
    exact h'
  · intro h
    simp [h, Nat.xor_self]

theorem clmul_two_mul (a b : Nat) : clmul a (b * 2) = clmul a b * 2 := by
  by_cases hb : b * 2 = 0
  · have : b = 0 := by omega
    simp [this, clmul_zero_right]
  · rw [clmul_succ_div a (b * 2) hb]
    have hdiv : b * 2 / 2 = b := Nat.mul_div_left b (by decide)
    have hmod : b * 2 % 2 = 0 := by
      rw [Nat.mul_comm]
      exact Nat.mul_mod_right 2 b
    simp [hdiv, hmod]

theorem clmul_one (a : Nat) : clmul a 1 = a := by
  rw [clmul_succ_div a 1 (by decide)]
  simp [clmul_zero_right]

theorem xor_left_comm (a b c : Nat) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  calc
    a ^^^ (b ^^^ c) = (a ^^^ b) ^^^ c := (Nat.xor_assoc a b c).symm
    _ = (b ^^^ a) ^^^ c := by rw [Nat.xor_comm a b]
    _ = b ^^^ (a ^^^ c) := Nat.xor_assoc b a c

theorem xor_both (x y a : Nat) : (x ^^^ a) ^^^ (y ^^^ a) = x ^^^ y := by
  calc
    (x ^^^ a) ^^^ (y ^^^ a) = x ^^^ (a ^^^ (y ^^^ a)) := Nat.xor_assoc x a (y ^^^ a)
    _ = x ^^^ (y ^^^ (a ^^^ a)) := by rw [xor_left_comm a y a]
    _ = x ^^^ (y ^^^ 0) := by rw [Nat.xor_self]
    _ = x ^^^ y := by rw [Nat.xor_zero]

theorem xor_four (w x y z : Nat) : (w ^^^ x) ^^^ (y ^^^ z) = (w ^^^ y) ^^^ (x ^^^ z) := by
  calc
    (w ^^^ x) ^^^ (y ^^^ z) = w ^^^ (x ^^^ (y ^^^ z)) := Nat.xor_assoc w x (y ^^^ z)
    _ = w ^^^ (y ^^^ (x ^^^ z)) := by rw [xor_left_comm x y z]
    _ = (w ^^^ y) ^^^ (x ^^^ z) := (Nat.xor_assoc w y (x ^^^ z)).symm

theorem clmul_xor_right (a : Nat) : ∀ b c, clmul a (b ^^^ c) = clmul a b ^^^ clmul a c := by
  intro b
  induction b using Nat.strongRecOn with | ind b ih
  intro c
  by_cases hb : b = 0
  · simp [hb, clmul_zero_right, Nat.zero_xor]
  · by_cases hc : c = 0
    · simp [hc, clmul_zero_right]
    · by_cases hbc : b = c
      · simp [hbc, Nat.xor_self, clmul_zero_right]
      · have hxor : b ^^^ c ≠ 0 := by
          intro h
          exact hbc ((xor_eq_zero_iff b c).mp h)
        rw [clmul_succ_div a b hb, clmul_succ_div a c hc, clmul_succ_div a (b ^^^ c) hxor]
        have hlt : b / 2 < b := Nat.div_lt_self (Nat.pos_of_ne_zero hb) (by decide)
        have hdiv : (b ^^^ c) / 2 = b / 2 ^^^ c / 2 := Nat.xor_div_two
        have hmod : (b ^^^ c) % 2 = b % 2 ^^^ c % 2 := by
          simpa using (Nat.xor_mod_two_pow (a := b) (b := c) (n := 1))
        rw [hdiv, ih (b / 2) hlt (c / 2)]
        have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
        have hc2 : c % 2 = 0 ∨ c % 2 = 1 := by omega
        rcases hb2 with hb0 | hb1 <;> rcases hc2 with hc0 | hc1
        · simp [hb0, hc0, hmod, mul2_xor]
        · simp [hb0, hc1, hmod, mul2_xor]
          exact Nat.xor_assoc (clmul a (b / 2) * 2) (clmul a (c / 2) * 2) a
        · simp [hb1, hc0, hmod, mul2_xor]
          rw [Nat.xor_comm (clmul a (b / 2) * 2) (clmul a (c / 2) * 2)]
          calc
            (clmul a (c / 2) * 2 ^^^ clmul a (b / 2) * 2) ^^^ a
                = clmul a (c / 2) * 2 ^^^ (clmul a (b / 2) * 2 ^^^ a) :=
                  Nat.xor_assoc _ _ _
            _ = clmul a (b / 2) * 2 ^^^ (clmul a (c / 2) * 2 ^^^ a) :=
                  xor_left_comm _ _ _
            _ = clmul a (b / 2) * 2 ^^^ (a ^^^ clmul a (c / 2) * 2) := by
                  rw [Nat.xor_comm (clmul a (c / 2) * 2) a]
            _ = (clmul a (b / 2) * 2 ^^^ a) ^^^ clmul a (c / 2) * 2 :=
                  (Nat.xor_assoc _ _ _).symm
        · simp [hb1, hc1, hmod, mul2_xor]
          calc
            clmul a (b / 2) * 2 ^^^ clmul a (c / 2) * 2
                = a ^^^ (a ^^^ (clmul a (b / 2) * 2 ^^^ clmul a (c / 2) * 2)) := by
                  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
            _ = a ^^^ (clmul a (b / 2) * 2 ^^^ (a ^^^ clmul a (c / 2) * 2)) :=
                  congrArg (a ^^^ ·) (xor_left_comm a _ _)
            _ = (a ^^^ clmul a (b / 2) * 2) ^^^ (a ^^^ clmul a (c / 2) * 2) :=
                  (Nat.xor_assoc _ _ _).symm
            _ = (clmul a (b / 2) * 2 ^^^ a) ^^^ (clmul a (c / 2) * 2 ^^^ a) := by
                  rw [Nat.xor_comm a (clmul a (b / 2) * 2), Nat.xor_comm a (clmul a (c / 2) * 2)]

theorem clmul_xor_left (a b c : Nat) : clmul (a ^^^ b) c = clmul a c ^^^ clmul b c := by
  induction c using Nat.strongRecOn with | ind c ih
  by_cases hc : c = 0
  · simp [hc, clmul_zero_right]
  · rw [clmul_succ_div (a ^^^ b) c hc, clmul_succ_div a c hc, clmul_succ_div b c hc]
    have hlt : c / 2 < c := Nat.div_lt_self (Nat.pos_of_ne_zero hc) (by decide)
    rw [ih (c / 2) hlt]
    by_cases hod : c % 2 = 1
    · simp [hod, mul2_xor]
      exact xor_four (clmul a (c / 2) * 2) (clmul b (c / 2) * 2) a b
    · simp [hod, mul2_xor]

theorem and_pow_mul_zero (x p k : Nat) (hp : p < 2 ^ k) : (x * 2 ^ k) &&& p = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_mul_two_pow]
  by_cases hik : k ≤ i
  · have hp' : p < 2 ^ i := Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (Nat.zero_lt_two) hik)
    simp [hik, Nat.testBit_lt_two_pow hp']
  · simp [hik]

theorem or_eq_xor_and_zero (a b : Nat) (h : a &&& b = 0) : a ||| b = a ^^^ b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have ht : (a &&& b).testBit i = false := by simp [h]
  simp only [Nat.testBit_and] at ht
  simp only [Nat.testBit_or, Nat.testBit_xor]
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

theorem shift_add_xor (x p k : Nat) (hp : p < 2 ^ k) : x * 2 ^ k + p = x * 2 ^ k ^^^ p := by
  rw [← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt hp]
  apply or_eq_xor_and_zero
  rw [Nat.shiftLeft_eq]
  exact and_pow_mul_zero x p k hp

theorem clmul_two_pow_left (n s : Nat) : clmul (2 ^ n) s = s <<< n := by
  induction s using Nat.strongRecOn with | ind s ih
  by_cases hs : s = 0
  · simp [hs, clmul_zero_right]
  · rw [clmul_succ_div (2 ^ n) s hs]
    have hlt : s / 2 < s := Nat.div_lt_self (Nat.pos_of_ne_zero hs) (by decide)
    rw [ih (s / 2) hlt]
    have hs2 : s % 2 = 0 ∨ s % 2 = 1 := by omega
    rcases hs2 with he | ho
    · have hmul : s = s / 2 * 2 := by
        have := Nat.div_add_mod s 2
        simp [he] at this
        simpa [Nat.mul_comm] using this.symm
      simp [he]
      have hr : s <<< n = (s / 2 * 2) <<< n := congrArg (· <<< n) hmul
      rw [hr, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
      simp [Nat.mul_assoc, Nat.mul_comm]
    · have hmul : s = s / 2 * 2 + 1 := by
        have := Nat.div_add_mod s 2
        simp [ho] at this
        simpa [Nat.mul_comm] using this.symm
      simp [ho]
      have hr : s <<< n = (s / 2 * 2 + 1) <<< n := congrArg (· <<< n) hmul
      rw [hr, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
      have hlt : 2 ^ n < 2 ^ (n + 1) := by
        have h := Nat.lt_add_of_pos_right (n := 2 ^ n) (Nat.two_pow_pos n)
        simpa [Nat.pow_succ, Nat.two_mul, Nat.mul_comm] using h
      have hsum : (s / 2 * 2 + 1) * 2 ^ n = s / 2 * 2 ^ (n + 1) + 2 ^ n := by
        rw [Nat.add_mul, Nat.one_mul, Nat.pow_succ, Nat.mul_assoc]
        simp [Nat.mul_comm, Nat.mul_left_comm]
      rw [hsum, shift_add_xor (s / 2) (2 ^ n) (n + 1) hlt]
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]

theorem clmul_lt (a b m k : Nat) (ha : a < 2 ^ m) (hb : b < 2 ^ k) : clmul a b < 2 ^ (m + k) := by
  induction b using Nat.strongRecOn generalizing k with | ind b ih
  by_cases hb0 : b = 0
  · simp [hb0, clmul_zero_right, Nat.two_pow_pos]
  · have hk : k ≠ 0 := by
      intro hk0
      simp [hk0] at hb
      omega
    have hk1 : k = (k - 1) + 1 := by omega
    rw [clmul_succ_div a b hb0]
    have hb2 : b / 2 < 2 ^ (k - 1) := by
      have hb' : b < 2 ^ (k - 1) * 2 := by
        rw [hk1, Nat.pow_succ] at hb
        exact hb
      exact (Nat.div_lt_iff_lt_mul (by decide)).mpr hb'
    have hrec := ih (b / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hb0) (by decide)) (k - 1) hb2
    have hsum : m + k = m + (k - 1) + 1 := by omega
    have hrec2 : clmul a (b / 2) * 2 < 2 ^ (m + k) := by
      rw [hsum, Nat.pow_succ]
      exact Nat.mul_lt_mul_of_pos_right hrec (by decide)
    have ha' : (if b % 2 = 1 then a else 0) < 2 ^ (m + k) := by
      by_cases h : b % 2 = 1
      · simp [h]
        exact Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (Nat.le_add_right m k))
      · simp [h, Nat.two_pow_pos]
    exact Nat.xor_lt_two_pow hrec2 ha'

theorem clmul_poly (s : Nat) : clmul polyNat s = (s <<< 32) ^^^ clmul polyLow s := by
  rw [polyNat_eq_xor, clmul_xor_left, clmul_two_pow_left]

theorem clmul_poly_high (s : Nat) (hs : s ≠ 0) : (clmul polyNat s).testBit (32 + s.log2) = true := by
  rw [clmul_poly, Nat.testBit_xor]
  have h1 : (s <<< 32).testBit (32 + s.log2) = true := by
    simp [Nat.testBit_shiftLeft, Nat.testBit_log2 hs]
  have hbound : clmul polyLow s < 2 ^ (32 + s.log2) := by
    have hlt := clmul_lt polyLow s 27 (s.log2 + 1) polyLow_lt_27 Nat.lt_log2_self
    exact Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))
  have h2 : (clmul polyLow s).testBit (32 + s.log2) = false := Nat.testBit_lt_two_pow hbound
  simp [h1, h2]

theorem clmul_poly_mod2 (q : Nat) : clmul polyNat q % 2 = q % 2 := by
  by_cases hq : q = 0
  · simp [hq, clmul_zero_right]
  · rw [clmul_succ_div polyNat q hq]
    have heven : clmul polyNat (q / 2) * 2 % 2 = 0 := by
      rw [Nat.mul_comm, Nat.mul_mod_right]
    by_cases ho : q % 2 = 1
    · have hxor : (clmul polyNat (q / 2) * 2 ^^^ polyNat) % 2 = polyNat % 2 := by
        rw [Nat.xor_mod_two_pow (n := 1)]
        simp [heven]
      simp [ho, hxor, polyNat_odd]
    · have hz : q % 2 = 0 := by omega
      simp [hz, heven]

theorem clmul_div2 (q : Nat) (h : clmul polyNat q % 2 = 0) :
    clmul polyNat (q / 2) = clmul polyNat q / 2 := by
  have hq : q % 2 = 0 := by rw [← clmul_poly_mod2]; exact h
  by_cases hz : q = 0
  · simp [hz, clmul_zero_right]
  · have hq2 : q = q / 2 * 2 := by omega
    have hrhs : clmul polyNat q / 2 = clmul polyNat (q / 2) * 2 / 2 := by
      have h := congrArg (fun x => clmul polyNat x / 2) hq2
      simpa [clmul_two_mul] using h
    rw [hrhs]
    exact (Nat.mul_div_left (clmul polyNat (q / 2)) (by decide : 0 < 2)).symm

theorem pow_mul_div (B k : Nat) : B * 2 ^ (k + 1) / 2 = B * 2 ^ k := by
  rw [Nat.pow_succ, ← Nat.mul_assoc]
  exact Nat.mul_div_left (B * 2 ^ k) (by decide)

theorem clmul_strip : ∀ k B q, clmul polyNat q = B * 2 ^ k → ∃ q', clmul polyNat q' = B := by
  intro k
  induction k with
  | zero =>
    intro B q h
    exact ⟨q, by simpa using h⟩
  | succ k ih =>
    intro B q h
    have he : clmul polyNat q % 2 = 0 := by
      rw [h, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm, Nat.mul_mod_right]
    have hdiv := clmul_div2 q he
    have hpow := pow_mul_div B k
    have : clmul polyNat (q / 2) = B * 2 ^ k := by
      rw [hdiv, h, hpow]
    exact ih B (q / 2) this

/-! ## The register stays a remainder -/

def Reduces (c m : Nat) : Prop :=
  c < 2 ^ 32 ∧ ∃ q, clmul polyNat q ^^^ c = m

theorem natShl1_lt (c : Nat) (hc : c < 2 ^ 32) : natShl1 c < 2 ^ 32 := by
  have hdivlt : c / 2 ^ 31 < 2 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 31)).mpr (by simpa [Nat.pow_succ, Nat.mul_comm] using hc)
  by_cases htop : c / 2 ^ 31 = 1
  · have hlow : (c % 2 ^ 31) * 2 < 2 ^ 32 := by
      have hmod : c % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
      omega
    simp [natShl1, htop]
    exact Nat.xor_lt_two_pow hlow polyLow_lt_32
  · have hzero : c / 2 ^ 31 = 0 := by omega
    have hc31 : c < 2 ^ 31 := by
      have := Nat.div_add_mod c (2 ^ 31)
      simp [hzero] at this
      simp [this]
    simp [natShl1, htop]
    omega

theorem natShl1_spec (c : Nat) (hc : c < 2 ^ 32) :
    natShl1 c = c * 2 ^^^ (if c / 2 ^ 31 = 1 then polyNat else 0) := by
  by_cases htop : c / 2 ^ 31 = 1
  · have hmod : c % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
    have hc' : c = 2 ^ 31 + c % 2 ^ 31 := by
      have := Nat.div_add_mod c (2 ^ 31)
      simp [htop] at this
      exact this.symm
    have hmul : c * 2 = 2 ^ 32 + (c % 2 ^ 31) * 2 := by
      rw [hc', Nat.add_mul, Nat.pow_succ]
      simp [Nat.mul_comm]
    have hlow : (c % 2 ^ 31) * 2 < 2 ^ 32 := by omega
    have hdis : 2 ^ 32 + (c % 2 ^ 31) * 2 = 2 ^ 32 ^^^ ((c % 2 ^ 31) * 2) := by
      simpa using (shift_add_xor 1 ((c % 2 ^ 31) * 2) 32 hlow)
    simp only [natShl1, htop, ite_true, hmul, hdis, polyNat_eq_xor]
    have hx := (xor_both ((c % 2 ^ 31) * 2) polyLow (2 ^ 32)).symm
    rw [Nat.xor_comm ((c % 2 ^ 31) * 2) (2 ^ 32), Nat.xor_comm polyLow (2 ^ 32)] at hx
    exact hx
  · have hzero : c / 2 ^ 31 = 0 := by
      have hdivlt : c / 2 ^ 31 < 2 :=
        (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 31)).mpr (by simpa [Nat.pow_succ, Nat.mul_comm] using hc)
      omega
    simp [natShl1, hzero]

theorem natShl1_xor_low (c e : Nat) (hc : c < 2 ^ 32) (he : e < 2 ^ 31) :
    natShl1 (c ^^^ e) = natShl1 c ^^^ (e * 2) := by
  have hdiv : (c ^^^ e) / 2 ^ 31 = c / 2 ^ 31 := by
    rw [Nat.xor_div_two_pow]
    simp [Nat.div_eq_of_lt he]
  have hc1 : c ^^^ e < 2 ^ 32 := Nat.xor_lt_two_pow hc (Nat.lt_trans he (by decide))
  rw [natShl1_spec (c ^^^ e) hc1, natShl1_spec c hc, hdiv, mul2_xor]
  by_cases htop : c / 2 ^ 31 = 1
  · simp only [htop, ite_true]
    calc
      c * 2 ^^^ e * 2 ^^^ polyNat
          = c * 2 ^^^ (e * 2 ^^^ polyNat) := Nat.xor_assoc _ _ _
      _ = c * 2 ^^^ (polyNat ^^^ e * 2) := by rw [Nat.xor_comm (e * 2) polyNat]
      _ = c * 2 ^^^ polyNat ^^^ e * 2 := (Nat.xor_assoc _ _ _).symm
  · simp only [htop, ite_false, Nat.xor_zero]

theorem feedBit_reduces {c m bit : Nat} (hr : Reduces c m) :
    Reduces (feedBit c bit) (m * 2 ^^^ ((bit % 2) * 2 ^ 32)) := by
  rcases hr with ⟨hc, q, hq⟩
  let bit1 := bit % 2
  have hbit1 : bit1 < 2 := Nat.mod_lt _ (by decide)
  let c1 := c ^^^ (bit1 * 2 ^ 31)
  have hc1 : c1 < 2 ^ 32 := by
    apply Nat.xor_lt_two_pow hc
    have : bit1 * 2 ^ 31 < 2 ^ 32 := by
      have : bit1 ≤ 1 := by omega
      omega
    omega
  have hfeed : feedBit c bit = natShl1 c1 := by simp [feedBit, c1, bit1]
  rw [hfeed]
  refine ⟨natShl1_lt c1 hc1, ?_⟩
  have hsh := natShl1_spec c1 hc1
  have hlin : (clmul polyNat q ^^^ c) * 2 ^^^ (bit1 * 2 ^ 32) =
      clmul polyNat (q * 2) ^^^ (c1 * 2) := by
    rw [mul2_xor, clmul_two_mul]
    have : c * 2 ^^^ (bit1 * 2 ^ 32) = (c ^^^ (bit1 * 2 ^ 31)) * 2 := by
      rw [mul2_xor]
      have hpow : bit1 * 2 ^ 32 = bit1 * 2 ^ 31 * 2 := by
        rw [Nat.pow_succ, Nat.mul_assoc]
      rw [hpow, Nat.mul_comm (bit1 * 2 ^ 31) 2]
    simp [c1, this, Nat.xor_assoc]
  by_cases htop : c1 / 2 ^ 31 = 1
  · refine ⟨q * 2 ^^^ 1, ?_⟩
    simp [htop] at hsh
    have hnew : m * 2 ^^^ (bit1 * 2 ^ 32) = clmul polyNat (q * 2) ^^^ (c1 * 2) := by
      rw [← hq, hlin]
    rw [hnew, hsh, clmul_xor_right, clmul_one, Nat.xor_assoc,
      xor_left_comm polyNat (c1 * 2) polyNat, Nat.xor_self, Nat.xor_zero]
  · refine ⟨q * 2, ?_⟩
    simp [htop] at hsh
    rw [hsh, ← hq, hlin]

theorem pow_sub_succ (n : Nat) (hn : n < 32) : 32 - n = (31 - n) + 1 := by omega

theorem rest_div (rest n : Nat) (hn : n < 32) :
    (rest * 2) / 2 ^ (32 - n) = rest / 2 ^ (31 - n) := by
  rw [pow_sub_succ n hn, Nat.pow_succ]
  exact Nat.mul_div_mul_right (m := 2) rest (2 ^ (31 - n)) (by decide)

theorem extra_split (extra n : Nat) (hn : n < 32) :
    extra / 2 ^ (31 - n) = extra / 2 ^ 31 * 2 ^ n + extra % 2 ^ 31 / 2 ^ (31 - n) := by
  have hk : (31 - n) + n = 31 := by omega
  have hpow : 2 ^ ((31 - n) + n) = 2 ^ (31 - n) * 2 ^ n := Nat.pow_add 2 (31 - n) n
  have hpow' : 2 ^ 31 = 2 ^ (31 - n) * 2 ^ n := by
    simpa [hk] using hpow
  have hdm : extra = 2 ^ 31 * (extra / 2 ^ 31) + extra % 2 ^ 31 := (Nat.div_add_mod extra (2 ^ 31)).symm
  have hmul : 2 ^ 31 * (extra / 2 ^ 31) = 2 ^ (31 - n) * (extra / 2 ^ 31 * 2 ^ n) := by
    have h := congrArg (· * (extra / 2 ^ 31)) hpow'
    rw [Nat.mul_assoc, Nat.mul_comm (2 ^ n) (extra / 2 ^ 31)] at h
    exact h
  have hleft := congrArg (fun x => x / 2 ^ (31 - n)) hdm
  rw [hleft, hmul, Nat.add_comm (2 ^ (31 - n) * (extra / 2 ^ 31 * 2 ^ n)),
    Nat.add_mul_div_left (extra % 2 ^ 31) (extra / 2 ^ 31 * 2 ^ n) (Nat.two_pow_pos _), Nat.add_comm]

theorem message_step (m extra n : Nat) (hn : n < 32) (he : extra < 2 ^ 32) :
    (m * 2 ^^^ ((extra / 2 ^ 31) * 2 ^ 32)) * 2 ^ n ^^^
        ((((extra % 2 ^ 31) * 2) / 2 ^ (32 - n)) * 2 ^ 32) =
      m * 2 ^ (n + 1) ^^^ ((extra / 2 ^ (31 - n)) * 2 ^ 32) := by
  let bit := extra / 2 ^ 31
  let rest := extra % 2 ^ 31
  have hbit : bit < 2 := by
    have hc2 : extra < 2 ^ 31 * 2 := by
      rw [Nat.pow_succ, Nat.mul_comm] at he
      exact he
    exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 31)).mpr hc2
  have hrest : rest < 2 ^ 31 := Nat.mod_lt extra (by decide : 0 < 2 ^ 31)
  have hdiv : (rest * 2) / 2 ^ (32 - n) = rest / 2 ^ (31 - n) := rest_div rest n hn
  have hdist : (m * 2 ^^^ (bit * 2 ^ 32)) * 2 ^ n = m * 2 ^ (n + 1) ^^^ bit * 2 ^ (32 + n) := by
    rw [← Nat.shiftLeft_eq, Nat.shiftLeft_xor_distrib]
    simp only [Nat.shiftLeft_eq]
    have h1 : m * 2 * 2 ^ n = m * 2 ^ (n + 1) := by
      rw [Nat.mul_assoc, Nat.mul_comm 2 (2 ^ n), ← Nat.pow_succ]
    have h2 : bit * 2 ^ 32 * 2 ^ n = bit * 2 ^ (32 + n) := by
      rw [Nat.mul_assoc, Nat.pow_add]
    rw [h1, h2]
  rw [hdist, hdiv]
  have hrlt : rest / 2 ^ (31 - n) < 2 ^ n := by
    have hexp : n + (31 - n) = 31 := by omega
    have hpow : 2 ^ n * 2 ^ (31 - n) = 2 ^ 31 := by
      rw [← Nat.pow_add, hexp]
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by rw [hpow]; exact hrest)
  have hsplit := extra_split extra n hn
  have hpack : (bit * 2 ^ n + rest / 2 ^ (31 - n)) * 2 ^ 32 =
      bit * 2 ^ (32 + n) ^^^ (rest / 2 ^ (31 - n)) * 2 ^ 32 := by
    have hxor : bit * 2 ^ n + rest / 2 ^ (31 - n) = bit * 2 ^ n ^^^ rest / 2 ^ (31 - n) :=
      shift_add_xor bit _ n hrlt
    rw [hxor, ← Nat.shiftLeft_eq, Nat.shiftLeft_xor_distrib]
    simp only [Nat.shiftLeft_eq]
    rw [Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm n 32]
  have hsum : (extra / 2 ^ (31 - n)) * 2 ^ 32 =
      bit * 2 ^ (32 + n) ^^^ (rest / 2 ^ (31 - n)) * 2 ^ 32 := by
    rw [← hpack, hsplit]
  rw [hsum, Nat.xor_assoc]

theorem feedTop_reduces (n : Nat) :
    ∀ c m extra, n ≤ 32 → Reduces c m → extra < 2 ^ 32 →
      Reduces (feedTop n c extra) (m * 2 ^ n ^^^ ((extra / 2 ^ (32 - n)) * 2 ^ 32)) := by
  induction n with
  | zero =>
    intro c m extra hn hr he
    have : extra / 2 ^ 32 = 0 := Nat.div_eq_of_lt he
    simpa [feedTop, this, Nat.pow_zero] using hr
  | succ n ih =>
    intro c m extra hn hr he
    have hn' : n < 32 := by omega
    have hbit : extra / 2 ^ 31 < 2 :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 31)).mpr (by simpa [Nat.pow_succ, Nat.mul_comm] using he)
    have hr' := feedBit_reduces (bit := extra / 2 ^ 31) hr
    have hbitmod : (extra / 2 ^ 31) % 2 = extra / 2 ^ 31 := Nat.mod_eq_of_lt hbit
    rw [hbitmod] at hr'
    have hrest : (extra % 2 ^ 31) * 2 < 2 ^ 32 := by
      have : extra % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
      omega
    have ih' := ih (feedBit c (extra / 2 ^ 31)) (m * 2 ^^^ ((extra / 2 ^ 31) * 2 ^ 32))
      ((extra % 2 ^ 31) * 2) (by omega) hr' hrest
    have hm := message_step m extra n hn' he
    simpa [feedTop, hm, Nat.pow_succ] using ih'

theorem feedByte_reduces {c m b : Nat} (hr : Reduces c m) (hb : b < 256) :
    Reduces (feedByte c b) (m * 256 ^^^ (b * 2 ^ 32)) := by
  have h8 : (8 : Nat) ≤ 32 := by decide
  have he : (b % 256) * 2 ^ 24 < 2 ^ 32 := by
    have hmod : b % 256 < 256 := Nat.mod_lt _ (by decide)
    have : 256 = 2 ^ 8 := by decide
    omega
  have h := feedTop_reduces 8 c m ((b % 256) * 2 ^ 24) h8 hr he
  have hdiv : (b % 256) * 2 ^ 24 / 2 ^ 24 = b % 256 := Nat.mul_div_left _ (by decide : 0 < 2 ^ 24)
  have hbmod : b % 256 = b := Nat.mod_eq_of_lt hb
  have h256 : (256 : Nat) = 2 ^ 8 := by decide
  simpa [feedByte, hdiv, hbmod, h256] using h

theorem fold_crc (p : Nat) (bs : List UInt8) :
    bs.foldl (fun acc b => acc * 256 ^^^ (b.toNat * 2 ^ 32)) (p * 2 ^ 32) =
      bs.foldl (fun acc b => acc * 256 + b.toNat) p * 2 ^ 32 := by
  induction bs generalizing p with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl]
    have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
    have h40 : b.toNat * 2 ^ 32 < 2 ^ 40 := by
      have h := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos 32)
      have h256 : (256 : Nat) = 2 ^ 8 := by decide
      have hpow : 2 ^ 8 * 2 ^ 32 = 2 ^ 40 := by rw [← Nat.pow_add]
      rw [h256, hpow] at h
      exact h
    have hshift : p * 2 ^ 32 * 256 = p * 2 ^ 40 := by
      have h256 : (256 : Nat) = 2 ^ 8 := by decide
      rw [h256, Nat.mul_assoc, ← Nat.pow_add]
    have hdis : p * 2 ^ 40 ^^^ (b.toNat * 2 ^ 32) = p * 2 ^ 40 + b.toNat * 2 ^ 32 :=
      (shift_add_xor p (b.toNat * 2 ^ 32) 40 h40).symm
    have hsum : p * 2 ^ 40 + b.toNat * 2 ^ 32 = (p * 256 + b.toNat) * 2 ^ 32 := by
      have h256 : (256 : Nat) = 2 ^ 8 := by decide
      rw [h256, Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add]
    have hstep : p * 2 ^ 32 * 256 ^^^ (b.toNat * 2 ^ 32) = (p * 256 + b.toNat) * 2 ^ 32 := by
      rw [hshift, hdis, hsum]
    rw [hstep]
    exact ih (p * 256 + b.toNat)

theorem fold_reduces (acc m : Nat) (bs : List UInt8) (hr : Reduces acc m) :
    Reduces (bs.foldl (fun c b => feedByte c b.toNat) acc)
      (bs.foldl (fun acc b => acc * 256 ^^^ (b.toNat * 2 ^ 32)) m) := by
  induction bs generalizing acc m with
  | nil => simpa using hr
  | cons b bs ih =>
    simp only [List.foldl]
    exact ih _ _ (feedByte_reduces hr (by simpa using UInt8.toNat_lt b))

theorem natSum_reduces (bs : List UInt8) : Reduces (natSum bs) (polyOf bs * 2 ^ 32) := by
  have h0 : Reduces 0 0 := ⟨by decide, 0, by simp [clmul_zero_right]⟩
  have h := fold_reduces 0 0 bs h0
  have hf := fold_crc 0 bs
  rcases h with ⟨hc, q, hq⟩
  refine ⟨hc, q, ?_⟩
  simpa [natSum, polyOf, hf] using hq

theorem reduces_unique {c1 c2 m : Nat} (h1 : Reduces c1 m) (h2 : Reduces c2 m) : c1 = c2 := by
  rcases h1 with ⟨hc1, q1, hq1⟩
  rcases h2 with ⟨hc2, q2, hq2⟩
  have hxor : clmul polyNat (q1 ^^^ q2) = c1 ^^^ c2 := by
    rw [clmul_xor_right]
    have heq : clmul polyNat q1 ^^^ c1 = clmul polyNat q2 ^^^ c2 := hq1.trans hq2.symm
    have hL : (clmul polyNat q1 ^^^ c1) ^^^ c1 = clmul polyNat q1 := by
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    have hstep := congrArg (fun x => x ^^^ c1) heq
    rw [hL] at hstep
    have hR : (clmul polyNat q2 ^^^ c2) ^^^ c1 = clmul polyNat q2 ^^^ (c2 ^^^ c1) :=
      Nat.xor_assoc _ _ _
    rw [hR] at hstep
    have hstep2 := congrArg (fun x => x ^^^ clmul polyNat q2) hstep
    have hR2 : (clmul polyNat q2 ^^^ (c2 ^^^ c1)) ^^^ clmul polyNat q2 = c1 ^^^ c2 := by
      rw [Nat.xor_assoc, xor_left_comm (clmul polyNat q2) (c2 ^^^ c1) (clmul polyNat q2),
        Nat.xor_self, Nat.xor_zero, Nat.xor_comm]
    exact hstep2.trans hR2
  have hlt : c1 ^^^ c2 < 2 ^ 32 := Nat.xor_lt_two_pow hc1 hc2
  by_cases hz : q1 ^^^ q2 = 0
  · have hq : q1 = q2 := (xor_eq_zero_iff q1 q2).mp hz
    rw [hq] at hq1
    exact xor_cancel_left (clmul polyNat q2) c1 c2 (hq1.trans hq2.symm)
  · have ht := clmul_poly_high (q1 ^^^ q2) hz
    rw [hxor] at ht
    have hlt' : c1 ^^^ c2 < 2 ^ (32 + (q1 ^^^ q2).log2) :=
      Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
    have hf := Nat.testBit_lt_two_pow hlt'
    simp [ht] at hf

/--
A byte string whose set bits lie in some window of 32 consecutive positions
has nonzero `natSum`, at every length. `B < 2 ^ 32` is that window.
-/
theorem natSum_burst (bs : List UInt8) {B t : Nat} (hB : 0 < B) (hlt : B < 2 ^ 32)
    (hp : polyOf bs = B * 2 ^ t) : natSum bs ≠ 0 := by
  intro h0
  have hr := natSum_reduces bs
  have hm : polyOf bs * 2 ^ 32 = B * 2 ^ (t + 32) := by
    rw [hp, Nat.pow_add, Nat.mul_assoc]
  rw [h0, hm] at hr
  rcases hr with ⟨_, q, hq⟩
  have hq0 : clmul polyNat q = B * 2 ^ (t + 32) := by simpa [Nat.xor_zero] using hq
  obtain ⟨q', hq'⟩ := clmul_strip (t + 32) B q hq0
  have hB : Reduces B B := ⟨hlt, 0, by simp [clmul_zero_right]⟩
  have hZ : Reduces 0 B := ⟨by decide, q', by simpa [Nat.xor_zero] using hq'⟩
  have := reduces_unique hZ hB
  omega

/-! ## The on-disk register is `natSum` -/

def extraShift : Nat → Nat → Nat
  | 0, extra => extra
  | n + 1, extra => extraShift n ((extra % 2 ^ 31) * 2)

theorem extraShift_eq (n extra : Nat) (hn : n ≤ 32) (he : extra < 2 ^ 32) :
    extraShift n extra = extra * 2 ^ n % 2 ^ 32 := by
  induction n generalizing extra with
  | zero =>
    simp [extraShift, Nat.pow_zero, Nat.mod_eq_of_lt he]
  | succ n ih =>
    have hn32 : n ≤ 32 := by omega
    have hlow : extra % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
    have hlow2 : (extra % 2 ^ 31) * 2 < 2 ^ 32 := by omega
    have ih' := ih ((extra % 2 ^ 31) * 2) hn32 hlow2
    have hdef : extraShift (n + 1) extra = extraShift n ((extra % 2 ^ 31) * 2) := by
      simp [extraShift]
    have hmul : (extra % 2 ^ 31) * 2 * 2 ^ n = (extra % 2 ^ 31) * 2 ^ (n + 1) := by
      rw [Nat.mul_assoc, Nat.mul_comm 2 (2 ^ n), ← Nat.pow_succ]
    have hrepr : extra * 2 ^ (n + 1) =
        extra / 2 ^ 31 * 2 ^ (n + 32) + (extra % 2 ^ 31) * 2 ^ (n + 1) := by
      have hdm : extra = extra / 2 ^ 31 * 2 ^ 31 + extra % 2 ^ 31 := by
        have h := (Nat.div_add_mod extra (2 ^ 31)).symm
        rwa [Nat.mul_comm (2 ^ 31) (extra / 2 ^ 31)] at h
      have hmul := congrArg (· * 2 ^ (n + 1)) hdm
      rw [Nat.add_mul, Nat.mul_assoc] at hmul
      have hexp : 2 ^ 31 * 2 ^ (n + 1) = 2 ^ (n + 32) := by
        rw [← Nat.pow_add]
        have : 31 + (n + 1) = n + 32 := by omega
        rw [this]
      rwa [hexp] at hmul
    have hdiv : extra / 2 ^ 31 * 2 ^ (n + 32) = extra / 2 ^ 31 * 2 ^ n * 2 ^ 32 := by
      rw [Nat.pow_add, ← Nat.mul_assoc]
    calc
      extraShift (n + 1) extra = extraShift n ((extra % 2 ^ 31) * 2) := hdef
      _ = (extra % 2 ^ 31) * 2 * 2 ^ n % 2 ^ 32 := ih'
      _ = (extra % 2 ^ 31) * 2 ^ (n + 1) % 2 ^ 32 := by rw [hmul]
      _ = extra * 2 ^ (n + 1) % 2 ^ 32 := by
        rw [hrepr, hdiv, Nat.mul_add_mod_self_right]

theorem shl_feed (n c extra : Nat) (hn : n ≤ 32) (hc : c < 2 ^ 32) (he : extra < 2 ^ 32) :
    shlFrom n (c ^^^ extra) = feedTop n c extra ^^^ extraShift n extra := by
  induction n generalizing c extra with
  | zero => simp [shlFrom, feedTop, extraShift]
  | succ n ih =>
    have hn' : n ≤ 32 := by omega
    have hbitlt : extra / 2 ^ 31 < 2 :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 31)).mpr
        (by simpa [Nat.pow_succ, Nat.mul_comm] using he)
    have hbit : extra / 2 ^ 31 = 0 ∨ extra / 2 ^ 31 = 1 := by omega
    have hlow : extra % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
    have hsplit : extra = extra / 2 ^ 31 * 2 ^ 31 ^^^ extra % 2 ^ 31 := by
      have hdis : extra / 2 ^ 31 * 2 ^ 31 + extra % 2 ^ 31 =
          extra / 2 ^ 31 * 2 ^ 31 ^^^ extra % 2 ^ 31 :=
        shift_add_xor (extra / 2 ^ 31) (extra % 2 ^ 31) 31 hlow
      have hdm : extra = extra / 2 ^ 31 * 2 ^ 31 + extra % 2 ^ 31 := by
        have h := (Nat.div_add_mod extra (2 ^ 31)).symm
        rwa [Nat.mul_comm (2 ^ 31) (extra / 2 ^ 31)] at h
      exact hdm.trans hdis
    have hc1 : c ^^^ (extra / 2 ^ 31 * 2 ^ 31) < 2 ^ 32 := by
      have hpow : extra / 2 ^ 31 * 2 ^ 31 < 2 ^ 32 := by
        rcases hbit with h0 | h1
        · simp [h0]
        · simp [h1, Nat.pow_succ]
      exact Nat.xor_lt_two_pow hc hpow
    have hsh := natShl1_xor_low (c ^^^ (extra / 2 ^ 31 * 2 ^ 31)) (extra % 2 ^ 31) hc1 hlow
    have hjoin : (c ^^^ (extra / 2 ^ 31 * 2 ^ 31)) ^^^ extra % 2 ^ 31 = c ^^^ extra := by
      rw [Nat.xor_assoc, ← hsplit]
    have hfeed : natShl1 (c ^^^ extra) =
        feedBit c (extra / 2 ^ 31) ^^^ ((extra % 2 ^ 31) * 2) := by
      rw [← hjoin, hsh]
      simp [feedBit, Nat.mod_eq_of_lt hbitlt]
    have hbit2 : (extra % 2 ^ 31) * 2 < 2 ^ 32 := by omega
    have hreg : feedBit c (extra / 2 ^ 31) < 2 ^ 32 := by
      simpa [feedBit] using natShl1_lt (c ^^^ ((extra / 2 ^ 31) % 2 * 2 ^ 31))
        (Nat.xor_lt_two_pow hc (by
          have : (extra / 2 ^ 31) % 2 < 2 := Nat.mod_lt _ (by decide)
          omega))
    have ih' := ih (feedBit c (extra / 2 ^ 31)) ((extra % 2 ^ 31) * 2) hn' hreg hbit2
    calc
      shlFrom (n + 1) (c ^^^ extra) = shlFrom n (natShl1 (c ^^^ extra)) := by simp [shlFrom]
      _ = shlFrom n (feedBit c (extra / 2 ^ 31) ^^^ ((extra % 2 ^ 31) * 2)) := by rw [hfeed]
      _ = feedTop n (feedBit c (extra / 2 ^ 31)) ((extra % 2 ^ 31) * 2) ^^^
            extraShift n ((extra % 2 ^ 31) * 2) := ih'
      _ = feedTop (n + 1) c extra ^^^ extraShift (n + 1) extra := by simp [feedTop, extraShift]

theorem feedByte_shl (c b : Nat) (hc : c < 2 ^ 32) (hb : b < 256) :
    feedByte c b = shlFrom 8 (c ^^^ (b * 2 ^ 24)) := by
  have he : b * 2 ^ 24 < 2 ^ 32 := by
    have h256 : (256 : Nat) = 2 ^ 8 := by decide
    have h := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos 24)
    rw [h256, ← Nat.pow_add] at h
    exact h
  have hmod : b % 256 = b := Nat.mod_eq_of_lt hb
  have hshift : extraShift 8 ((b % 256) * 2 ^ 24) = 0 := by
    rw [hmod, extraShift_eq 8 (b * 2 ^ 24) (by decide) he]
    have h256 : (256 : Nat) = 2 ^ 8 := by decide
    rw [Nat.mul_assoc, ← Nat.pow_add, Nat.mul_comm b (2 ^ 32)]
    exact Nat.mul_mod_right (2 ^ 32) b
  have hs := shl_feed 8 c ((b % 256) * 2 ^ 24) (by decide) hc (by simpa [hmod] using he)
  have hzero : feedTop 8 c ((b % 256) * 2 ^ 24) = shlFrom 8 (c ^^^ ((b % 256) * 2 ^ 24)) := by
    have hs' := hs.symm
    rw [hshift, Nat.xor_zero] at hs'
    exact hs'
  simpa [feedByte, hmod] using hzero

theorem mod_mul2_top (c : Nat) (_hc : c < 2 ^ 32) (ht : c / 2 ^ 31 = 1) :
    c * 2 % 2 ^ 32 = (c % 2 ^ 31) * 2 := by
  have hc' : c = 2 ^ 31 + c % 2 ^ 31 := by
    have h := (Nat.div_add_mod c (2 ^ 31)).symm
    rw [ht, Nat.mul_one] at h
    exact h
  have hlow : (c % 2 ^ 31) * 2 < 2 ^ 32 := by omega
  have hstep : (2 ^ 31 + c % 2 ^ 31) * 2 = 2 ^ 32 + (c % 2 ^ 31) * 2 := by
    rw [Nat.add_mul, ← Nat.pow_succ]
  calc
    c * 2 % 2 ^ 32 = (2 ^ 31 + c % 2 ^ 31) * 2 % 2 ^ 32 :=
      congrArg (fun x => x * 2 % 2 ^ 32) hc'
    _ = (2 ^ 32 + (c % 2 ^ 31) * 2) % 2 ^ 32 := by rw [hstep]
    _ = (c % 2 ^ 31) * 2 % 2 ^ 32 := by
      rw [Nat.add_comm, ← Nat.mul_one (2 ^ 32), Nat.add_mul_mod_self_left]
    _ = (c % 2 ^ 31) * 2 := Nat.mod_eq_of_lt hlow

theorem uint32_top (c : UInt32) : (c >>> 31).toNat = c.toNat / 2 ^ 31 := by
  rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  simp

theorem uint32_shl1 (c : UInt32) : (c <<< 1).toNat = c.toNat * 2 % 2 ^ 32 := by
  rw [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp

theorem natShl1_uint (c : UInt32) :
    natShl1 c.toNat =
      (if c >>> 31 == 1 then (c <<< 1) ^^^ polySum else c <<< 1).toNat := by
  have hc : c.toNat < 2 ^ 32 := UInt32.toNat_lt_size c
  by_cases htop : c >>> 31 == 1
  · have hdiv : c.toNat / 2 ^ 31 = 1 := by
      have hbeq : c >>> 31 = 1 := by simpa [beq_iff_eq] using htop
      have hnat : c.toNat >>> 31 = 1 := by
        simpa [UInt32.toNat_shiftRight] using congrArg UInt32.toNat hbeq
      rwa [Nat.shiftRight_eq_div_pow] at hnat
    unfold natShl1
    simp [hdiv, htop]
    rw [Nat.shiftLeft_eq, mod_mul2_top c.toNat hc hdiv]
    have hp : polySum.toNat = polyLow := by decide
    rw [hp]
  · have hdiv : c.toNat / 2 ^ 31 = 0 := by
      have hlt : c.toNat / 2 ^ 31 < 2 :=
        (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 31)).mpr
          (by simpa [Nat.pow_succ, Nat.mul_comm] using hc)
      have hne : c.toNat / 2 ^ 31 ≠ 1 := by
        intro h
        have hbeq : c >>> 31 = 1 := UInt32.toNat_inj.mp (by
          have hnat : c.toNat >>> 31 = 1 := by rwa [Nat.shiftRight_eq_div_pow]
          simpa [UInt32.toNat_shiftRight] using hnat)
        exact htop (by simpa [beq_iff_eq] using hbeq)
      omega
    have hsmall : c.toNat * 2 < 2 ^ 32 := by
      have hc31 : c.toNat < 2 ^ 31 := by
        have h := Nat.div_add_mod c.toNat (2 ^ 31)
        rw [hdiv, Nat.mul_zero, Nat.zero_add] at h
        simpa [h] using Nat.mod_lt c.toNat (by decide : 0 < 2 ^ 31)
      omega
    unfold natShl1
    simp [hdiv, htop]
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hsmall]

theorem sumStep_go_nat : ∀ (n : Nat) (c : UInt32), (sumStep.go n c).toNat = shlFrom n c.toNat := by
  intro n
  induction n with
  | zero =>
    intro c
    rw [sumStep.go.eq_1]
    simp [shlFrom]
  | succ n ih =>
    intro c
    rw [sumStep.go.eq_2, shlFrom]
    by_cases htop : c >>> 31 == 1
    · rw [ite_eq_left htop, ih]
      have h := natShl1_uint c
      rw [ite_eq_left htop] at h
      exact congrArg (shlFrom n) h.symm
    · rw [ite_eq_right htop, ih]
      have h := natShl1_uint c
      rw [ite_eq_right htop] at h
      exact congrArg (shlFrom n) h.symm

theorem sumStep_nat (crc : UInt32) (b : UInt8) :
    (sumStep crc b).toNat = feedByte crc.toNat b.toNat := by
  have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
  have hc : crc.toNat < 2 ^ 32 := UInt32.toNat_lt_size crc
  have hxor : (crc ^^^ (b.toUInt32 <<< 24)).toNat = crc.toNat ^^^ (b.toNat * 2 ^ 24) := by
    rw [UInt32.toNat_xor, UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]
    have hb24 : b.toNat * 2 ^ 24 < 2 ^ 32 := by
      have h := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos 24)
      have h256 : (256 : Nat) = 2 ^ 8 := by decide
      rw [h256, ← Nat.pow_add] at h
      exact h
    simp [UInt8.toNat_toUInt32, Nat.mod_eq_of_lt hb24]
  rw [sumStep, sumStep_go_nat, hxor, feedByte_shl crc.toNat b.toNat hc hb]

theorem sum32_toNat (bs : List UInt8) : (sum32 bs).toNat = natSum bs := by
  have h : ∀ (acc : UInt32) (bs : List UInt8),
      (bs.foldl sumStep acc).toNat =
        bs.foldl (fun c b => feedByte c b.toNat) acc.toNat := by
    intro acc bs
    induction bs generalizing acc with
    | nil => simp
    | cons b bs ih =>
      simp only [List.foldl]
      rw [ih, sumStep_nat]
  simpa [sum32, natSum] using h 0 bs

theorem sum32_burst (bs : List UInt8) {B t : Nat} (hB : 0 < B) (hlt : B < 2 ^ 32)
    (hp : polyOf bs = B * 2 ^ t) : sum32 bs ≠ 0 := by
  intro h0
  have hnat := natSum_burst bs hB hlt hp
  have ht := sum32_toNat bs
  rw [h0] at ht
  exact hnat (by simpa using ht.symm)

/-- A single set bit, anywhere in a byte string of any length. -/
theorem sum32_one_bit (bs : List UInt8) {k : Nat} (hp : polyOf bs = 2 ^ k) : sum32 bs ≠ 0 := by
  have hpow : polyOf bs = 1 * 2 ^ k := by simpa [Nat.one_mul] using hp
  exact sum32_burst bs (Nat.one_pos) (by decide) hpow

/-- Two set bits at distance `d` with `1 ≤ d ≤ 31`. Farther pairs are not claimed. -/
theorem sum32_two_close (bs : List UInt8) {k d : Nat} (hd0 : 0 < d) (hd : d ≤ 31)
    (hp : polyOf bs = 2 ^ k + 2 ^ (k + d)) : sum32 bs ≠ 0 := by
  have hle : 2 ^ d ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) hd
  have h31 : 1 + 2 ^ 31 < 2 ^ 32 := by
    rw [Nat.pow_succ 2 31]
    omega
  have hB : 1 + 2 ^ d < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.add_le_add_left hle 1) h31
  have hpos : 0 < 1 + 2 ^ d := by
    rw [Nat.add_comm]
    exact Nat.succ_pos _
  have _hd0 := hd0
  have hpoly : polyOf bs = (1 + 2 ^ d) * 2 ^ k := by
    calc
      polyOf bs = 2 ^ k + 2 ^ (k + d) := hp
      _ = 2 ^ k + 2 ^ k * 2 ^ d := by rw [Nat.pow_add]
      _ = 2 ^ k * 1 + 2 ^ k * 2 ^ d := by rw [Nat.mul_one]
      _ = 2 ^ k * (1 + 2 ^ d) := by rw [← Nat.mul_add]
      _ = (1 + 2 ^ d) * 2 ^ k := by rw [Nat.mul_comm]
  exact sum32_burst bs hpos hB hpoly

theorem natShl1_xor (c e : Nat) (hc : c < 2 ^ 32) (he : e < 2 ^ 32) :
    natShl1 (c ^^^ e) = natShl1 c ^^^ natShl1 e := by
  have htop (x : Nat) (hx : x < 2 ^ 32) : x / 2 ^ 31 = 0 ∨ x / 2 ^ 31 = 1 := by
    have : x / 2 ^ 31 < 2 :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 31)).mpr
        (by simpa [Nat.pow_succ, Nat.mul_comm] using hx)
    omega
  have hc2 := htop c hc
  have he2 := htop e he
  have hxor : c ^^^ e < 2 ^ 32 := Nat.xor_lt_two_pow hc he
  have hdiv : (c ^^^ e) / 2 ^ 31 = c / 2 ^ 31 ^^^ e / 2 ^ 31 := Nat.xor_div_two_pow
  rw [natShl1_spec (c ^^^ e) hxor, natShl1_spec c hc, natShl1_spec e he, mul2_xor, hdiv]
  rcases hc2 with hc0 | hc1 <;> rcases he2 with he0 | he1
  · simp [hc0, he0, Nat.xor_zero]
  · simp [hc0, he1, Nat.xor_zero, Nat.xor_assoc]
  · simp [hc1, he0]
    calc
      c * 2 ^^^ e * 2 ^^^ polyNat
          = c * 2 ^^^ (e * 2 ^^^ polyNat) := Nat.xor_assoc _ _ _
      _ = c * 2 ^^^ (polyNat ^^^ e * 2) := by rw [Nat.xor_comm (e * 2) polyNat]
      _ = (c * 2 ^^^ polyNat) ^^^ e * 2 := (Nat.xor_assoc _ _ _).symm
      _ = (polyNat ^^^ c * 2) ^^^ e * 2 := by rw [Nat.xor_comm (c * 2) polyNat]
      _ = c * 2 ^^^ polyNat ^^^ e * 2 := by rw [Nat.xor_comm polyNat (c * 2)]
  · simp [hc1, he1]
    rw [Nat.xor_assoc, xor_left_comm polyNat (e * 2) polyNat, Nat.xor_self, Nat.xor_zero]

theorem shlFrom_xor (n c e : Nat) (hc : c < 2 ^ 32) (he : e < 2 ^ 32) :
    shlFrom n (c ^^^ e) = shlFrom n c ^^^ shlFrom n e := by
  induction n generalizing c e with
  | zero => simp [shlFrom]
  | succ n ih =>
    simp only [shlFrom]
    rw [natShl1_xor c e hc he]
    exact ih (natShl1 c) (natShl1 e) (natShl1_lt c hc) (natShl1_lt e he)

theorem feedByte_xor (c1 c2 b1 b2 : Nat) (hc1 : c1 < 2 ^ 32) (hc2 : c2 < 2 ^ 32)
    (hb1 : b1 < 256) (hb2 : b2 < 256) :
    feedByte (c1 ^^^ c2) (b1 ^^^ b2) = feedByte c1 b1 ^^^ feedByte c2 b2 := by
  have hc : c1 ^^^ c2 < 2 ^ 32 := Nat.xor_lt_two_pow hc1 hc2
  have h256 : (256 : Nat) = 2 ^ 8 := by decide
  have hb1e : b1 < 2 ^ 8 := by simpa [h256] using hb1
  have hb2e : b2 < 2 ^ 8 := by simpa [h256] using hb2
  have hb : b1 ^^^ b2 < 256 := by
    simpa [h256] using (Nat.xor_lt_two_pow hb1e hb2e)
  have hmul : (b1 ^^^ b2) * 2 ^ 24 = b1 * 2 ^ 24 ^^^ b2 * 2 ^ 24 := by
    simpa [Nat.shiftLeft_eq] using (Nat.shiftLeft_xor_distrib (a := b1) (b := b2) (i := 24))
  have hleft : c1 ^^^ (b1 * 2 ^ 24) < 2 ^ 32 := by
    have hb1' : b1 * 2 ^ 24 < 2 ^ 32 := by
      have h := Nat.mul_lt_mul_of_pos_right hb1 (Nat.two_pow_pos 24)
      have h256 : (256 : Nat) = 2 ^ 8 := by decide
      rw [h256, ← Nat.pow_add] at h
      exact h
    exact Nat.xor_lt_two_pow hc1 hb1'
  have hright : c2 ^^^ (b2 * 2 ^ 24) < 2 ^ 32 := by
    have hb2' : b2 * 2 ^ 24 < 2 ^ 32 := by
      have h := Nat.mul_lt_mul_of_pos_right hb2 (Nat.two_pow_pos 24)
      have h256 : (256 : Nat) = 2 ^ 8 := by decide
      rw [h256, ← Nat.pow_add] at h
      exact h
    exact Nat.xor_lt_two_pow hc2 hb2'
  rw [feedByte_shl (c1 ^^^ c2) (b1 ^^^ b2) hc hb, feedByte_shl c1 b1 hc1 hb1,
    feedByte_shl c2 b2 hc2 hb2, hmul, xor_four c1 c2 (b1 * 2 ^ 24) (b2 * 2 ^ 24)]
  exact shlFrom_xor 8 (c1 ^^^ (b1 * 2 ^ 24)) (c2 ^^^ (b2 * 2 ^ 24)) hleft hright

theorem fold_feed_xor (as bs : List UInt8) (c1 c2 : Nat) (hc1 : c1 < 2 ^ 32) (hc2 : c2 < 2 ^ 32)
    (hlen : as.length = bs.length) :
    (xorBytes as bs).foldl (fun c b => feedByte c b.toNat) (c1 ^^^ c2) =
      as.foldl (fun c b => feedByte c b.toNat) c1 ^^^
        bs.foldl (fun c b => feedByte c b.toNat) c2 := by
  induction as generalizing bs c1 c2 with
  | nil =>
    cases bs with
    | nil => simp [xorBytes]
    | cons _ _ => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [xorBytes, List.foldl, List.length_cons, Nat.succ.injEq] at hlen ⊢
      have ha : a.toNat < 256 := by simpa using UInt8.toNat_lt a
      have hb : b.toNat < 256 := by simpa using UInt8.toNat_lt b
      have hbyte : (a ^^^ b).toNat = a.toNat ^^^ b.toNat := UInt8.toNat_xor a b
      have hfeed := feedByte_xor c1 c2 a.toNat b.toNat hc1 hc2 ha hb
      have hlt1 : feedByte c1 a.toNat < 2 ^ 32 := by
        rw [feedByte_shl c1 a.toNat hc1 ha]
        -- shlFrom stays below 2^32
        have hbound : ∀ n x, x < 2 ^ 32 → shlFrom n x < 2 ^ 32 := by
          intro n x hx
          induction n generalizing x with
          | zero => simpa [shlFrom] using hx
          | succ n ihx =>
            simp only [shlFrom]
            exact ihx _ (natShl1_lt x hx)
        exact hbound 8 _ (Nat.xor_lt_two_pow hc1 (by
          have h := Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos 24)
          have h256 : (256 : Nat) = 2 ^ 8 := by decide
          rw [h256, ← Nat.pow_add] at h
          exact h))
      have hlt2 : feedByte c2 b.toNat < 2 ^ 32 := by
        rw [feedByte_shl c2 b.toNat hc2 hb]
        have hbound : ∀ n x, x < 2 ^ 32 → shlFrom n x < 2 ^ 32 := by
          intro n x hx
          induction n generalizing x with
          | zero => simpa [shlFrom] using hx
          | succ n ihx =>
            simp only [shlFrom]
            exact ihx _ (natShl1_lt x hx)
        exact hbound 8 _ (Nat.xor_lt_two_pow hc2 (by
          have h := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos 24)
          have h256 : (256 : Nat) = 2 ^ 8 := by decide
          rw [h256, ← Nat.pow_add] at h
          exact h))
      rw [hbyte, hfeed]
      exact ih bs (feedByte c1 a.toNat) (feedByte c2 b.toNat) hlt1 hlt2 hlen

theorem natSum_xor (a b : List UInt8) (hlen : a.length = b.length) :
    natSum (xorBytes a b) = natSum a ^^^ natSum b := by
  simpa [natSum] using fold_feed_xor a b 0 0 (by decide) (by decide) hlen

theorem sum32_xor (a b : List UInt8) (hlen : a.length = b.length) :
    sum32 (xorBytes a b) = sum32 a ^^^ sum32 b := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_xor, sum32_toNat, sum32_toNat, sum32_toNat, natSum_xor a b hlen]

/--
A burst in `err` changes the checksum of an equal-length message.
`polyOf err = B * 2 ^ t` with `B < 2 ^ 32` means every flipped bit sits in one
window of 32 consecutive positions.
-/
theorem sum32_detects_burst (data err : List UInt8) (hlen : data.length = err.length)
    {B t : Nat} (hB : 0 < B) (hlt : B < 2 ^ 32) (hp : polyOf err = B * 2 ^ t) :
    sum32 (xorBytes data err) ≠ sum32 data := by
  intro hsame
  have h0 := sum32_burst err hB hlt hp
  have hnat := congrArg UInt32.toNat hsame
  rw [sum32_xor data err hlen, UInt32.toNat_xor, sum32_toNat, sum32_toNat] at hnat
  have h' := congrArg (fun x => natSum data ^^^ x) hnat
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h'
  exact h0 (UInt32.toNat_inj.mp (by simpa [h'] using sum32_toNat err))

/-! ## One set bit is a power of two -/

theorem bitSumFuel_step (k n : Nat) (hn : n < 2 ^ k) :
    bitSumFuel (k + 1) n = bitSumFuel k n := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by omega
    simp [this, bitSumFuel]
  | succ k ih =>
    cases n with
    | zero => simp [bitSumFuel]
    | succ n =>
      simp [bitSumFuel]
      have hn' : (n + 1) / 2 < 2 ^ k := by
        have hmul : n + 1 < 2 ^ k * 2 := by
          simpa [Nat.pow_succ, Nat.mul_comm] using hn
        exact (Nat.div_lt_iff_lt_mul (by decide)).mpr hmul
      exact ih ((n + 1) / 2) hn'

theorem bitSumFuel_extra (t k n : Nat) (hn : n < 2 ^ k) :
    bitSumFuel (k + t) n = bitSumFuel k n := by
  induction t generalizing k n with
  | zero => simp
  | succ t ih =>
    have hn' : n < 2 ^ (k + t) :=
      Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (Nat.le_add_right k t))
    rw [← Nat.add_assoc, bitSumFuel_step (k + t) n hn']
    exact ih k n hn

theorem bitSum_byte (b : Nat) (hb : b < 2 ^ 8) : bitSum b = bitSumFuel 8 b := by
  simpa [bitSum, show (40 : Nat) = 8 + 32 by decide] using bitSumFuel_extra 32 8 b hb

theorem bitSumFuel_zero {fuel n : Nat} (hn : n < 2 ^ fuel) (hz : bitSumFuel fuel n = 0) : n = 0 := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp [bitSumFuel] at hz
      have hn' : (n + 1) / 2 < 2 ^ fuel := by
        have hmul : n + 1 < 2 ^ fuel * 2 := by
          simpa [Nat.pow_succ, Nat.mul_comm] using hn
        exact (Nat.div_lt_iff_lt_mul (by decide)).mpr hmul
      have hmod : (n + 1) % 2 = 0 := by omega
      have hrest : bitSumFuel fuel ((n + 1) / 2) = 0 := by omega
      have := ih hn' hrest
      omega

theorem bitSumFuel_one {fuel n : Nat} (hn : n < 2 ^ fuel) (hw : bitSumFuel fuel n = 1) :
    ∃ k, k < fuel ∧ n = 2 ^ k := by
  induction fuel generalizing n with
  | zero =>
    have : n = 0 := by omega
    simp [bitSumFuel] at hw
  | succ fuel ih =>
    cases n with
    | zero => simp [bitSumFuel] at hw
    | succ n =>
      simp [bitSumFuel] at hw
      have hn' : (n + 1) / 2 < 2 ^ fuel := by
        have hmul : n + 1 < 2 ^ fuel * 2 := by
          simpa [Nat.pow_succ, Nat.mul_comm] using hn
        exact (Nat.div_lt_iff_lt_mul (by decide)).mpr hmul
      by_cases hbit : (n + 1) % 2 = 1
      · have h0 : bitSumFuel fuel ((n + 1) / 2) = 0 := by omega
        have hz := bitSumFuel_zero hn' h0
        refine ⟨0, Nat.succ_pos _, ?_⟩
        omega
      · have hbit0 : (n + 1) % 2 = 0 := by omega
        have h1 : bitSumFuel fuel ((n + 1) / 2) = 1 := by omega
        obtain ⟨k, hk, heq⟩ := ih hn' h1
        refine ⟨k + 1, Nat.succ_lt_succ hk, ?_⟩
        have hdouble : n + 1 = (n + 1) / 2 * 2 := by omega
        rw [hdouble, heq, Nat.pow_succ, Nat.mul_comm]

theorem weight_add (bs : List UInt8) (s : Nat) :
    bs.foldl (fun acc b => acc + bitSum b.toNat) s =
      s + bs.foldl (fun acc b => acc + bitSum b.toNat) 0 := by
  induction bs generalizing s with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl]
    rw [ih (s + bitSum b.toNat)]
    simp only [Nat.zero_add]
    rw [ih (bitSum b.toNat)]
    omega

theorem weight_cons (b : UInt8) (bs : List UInt8) :
    weight (b :: bs) = bitSum b.toNat + weight bs := by
  simp only [weight, List.foldl]
  rw [weight_add]
  simp

theorem weight_zero_bytes (bs : List UInt8) (h : weight bs = 0) : ∀ b ∈ bs, b = 0 := by
  induction bs with
  | nil => intro b hb; cases hb
  | cons b bs ih =>
    intro x hx
    have hsplit := weight_cons b bs
    rw [h] at hsplit
    have hb0 : bitSum b.toNat = 0 := by omega
    have hbs : weight bs = 0 := by omega
    have h8 : b.toNat < 2 ^ 8 := by simpa using UInt8.toNat_lt b
    have hnat : b.toNat = 0 :=
      bitSumFuel_zero h8 (by simpa [bitSum_byte b.toNat h8] using hb0)
    cases hx with
    | head => exact UInt8.toNat_inj.mp (by simpa using hnat)
    | tail _ hmem => exact ih hbs _ hmem

theorem poly_zeros_shift (s : Nat) (bs : List UInt8) (hz : ∀ x ∈ bs, x = 0) :
    bs.foldl (fun acc x => acc * 256 + x.toNat) s = s * 256 ^ bs.length := by
  induction bs generalizing s with
  | nil => simp
  | cons b bs ih =>
    have hb : b = 0 := hz b (List.Mem.head _)
    have htail : ∀ x ∈ bs, x = 0 := fun x hx => hz x (List.Mem.tail _ hx)
    simp only [List.foldl, hb, UInt8.toNat_zero, Nat.add_zero]
    rw [ih (s * 256) htail, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ bs.length), ← Nat.pow_succ]
    simp [List.length_cons]

/-- A byte string of Hamming weight 1 has polynomial `2 ^ k`. -/
theorem weight_one_pow (bs : List UInt8) (hw : weight bs = 1) : ∃ k, polyOf bs = 2 ^ k := by
  induction bs with
  | nil => simp [weight] at hw
  | cons b bs ih =>
    have hsplit := weight_cons b bs
    by_cases h0 : bitSum b.toNat = 0
    · have htail : weight bs = 1 := by
        rw [hw] at hsplit
        simp [h0] at hsplit
        exact hsplit.symm
      have h8 : b.toNat < 2 ^ 8 := by simpa using UInt8.toNat_lt b
      have hnat : b.toNat = 0 :=
        bitSumFuel_zero h8 (by simpa [bitSum_byte b.toNat h8] using h0)
      have hb : b = 0 := UInt8.toNat_inj.mp (by simpa using hnat)
      obtain ⟨k, hk⟩ := ih htail
      refine ⟨k, ?_⟩
      simpa [polyOf, hb, hk]
    · have hsum : bitSum b.toNat + weight bs = 1 := by
        rw [hw] at hsplit
        exact hsplit.symm
      have h1 : bitSum b.toNat = 1 := by omega
      have htail0 : weight bs = 0 := by omega
      have hall := weight_zero_bytes bs htail0
      have h8 : b.toNat < 2 ^ 8 := by simpa using UInt8.toNat_lt b
      have hfuel : bitSumFuel 8 b.toNat = 1 := by
        simpa [bitSum_byte b.toNat h8] using h1
      obtain ⟨j, _, heq⟩ := bitSumFuel_one h8 hfuel
      refine ⟨j + 8 * bs.length, ?_⟩
      have hfold := poly_zeros_shift b.toNat bs hall
      have h256 : (256 : Nat) = 2 ^ 8 := by decide
      simp only [polyOf, List.foldl, Nat.zero_mul, Nat.zero_add]
      rw [hfold, heq, h256, ← Nat.pow_mul, ← Nat.pow_add]

theorem sum32_weight_one (bs : List UInt8) (hw : weight bs = 1) : sum32 bs ≠ 0 := by
  obtain ⟨k, hk⟩ := weight_one_pow bs hw
  exact sum32_one_bit bs hk


end Cairn
