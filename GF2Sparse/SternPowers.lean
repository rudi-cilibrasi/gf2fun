import GF2Sparse.Certificate
import GF2Sparse.ShiftWeight

/-! Trace polynomials for the sum of the two positive trinomial exponents. -/

namespace GF2Sparse.SternPowers
open Polynomial

noncomputable section

/-- If `u+v=1` and `Y=u*v`, this polynomial evaluates to `u^m+v^m`. -/
def tracePoly : ℕ → BinaryPoly
  | 0 => 0
  | 1 => 1
  | m+2 => tracePoly (m+1) + X * tracePoly m

theorem tracePoly_eval {R : Type*} [CommRing R] [Algebra (ZMod 2) R] [CharP R 2]
    {u v : R} (huv : u+v = 1) (m : ℕ) :
    aeval (u*v) (tracePoly m) = u^m + v^m := by
  induction m using Nat.twoStepInduction with
  | zero => simp [tracePoly, CharTwo.add_self_eq_zero]
  | one => simp [tracePoly, huv]
  | more m hm hn =>
    rw [tracePoly, map_add, map_mul, aeval_X, hn, hm]
    calc
      _ = (u+v)*(u^(m+1)+v^(m+1)) + u*v*(u^m+v^m) := by rw [huv, one_mul]
      _ = _ := by simp only [pow_succ]; ring_nf; simp [CharTwo.two_eq_zero]

/-- A divisor of the sum of the taps gives a polynomial for the powered root. -/
theorem trinomial_midpoint_power {R : Type*} [CommRing R] [Algebra (ZMod 2) R] [CharP R 2]
    {r : R} {n a m h : ℕ} (hr : r^n+r^a = 1) (hm : m*h = n+a) :
    aeval (r^m) (X^n + X^a + (tracePoly m).comp (X^h)) = 0 := by
  simp only [map_add, map_pow, aeval_X, aeval_comp]
  rw [show (r^m)^h = r^(n+a) by rw [← pow_mul, hm]]
  have ht := tracePoly_eval hr m
  rw [← pow_add] at ht
  rw [ht, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul,
    Nat.mul_comm n m, Nat.mul_comm a m, CharTwo.add_self_eq_zero]

/-- Squaring doubles the index. The odd index interleaves two squared polynomials. -/
theorem tracePoly_double (k : ℕ) : tracePoly (2*k) = (tracePoly k)^2 ∧
    tracePoly (2*k+1) = (tracePoly (k+1))^2 + X*(tracePoly k)^2 := by
  induction k with
  | zero => simp [tracePoly]
  | succ k ih =>
    obtain ⟨he, ho⟩ := ih
    have h : tracePoly (2*k+2) = (tracePoly (k+1))^2 := by
      rw [tracePoly, ho, he, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    constructor
    · simpa only [Nat.mul_succ] using h
    · rw [Nat.mul_succ, show 2*k+2+1 = (2*k+1)+2 by omega, tracePoly, h, ho,
        show tracePoly (k+1+1) = tracePoly (k+1) + X*tracePoly k from rfl, CharTwo.add_sq]
      ring

/-- Together with initial weights `0,1`, these are Stern's diatomic recurrences. -/
theorem tracePoly_weights (k : ℕ) :
    (tracePoly (2*k)).support.card = (tracePoly k).support.card ∧
    (tracePoly (2*k+1)).support.card = (tracePoly k).support.card + (tracePoly (k+1)).support.card := by
  obtain ⟨he, ho⟩ := tracePoly_double k
  rw [he, ho, ShiftWeight.card_support_sq_add_X_mul_sq, Nat.add_comm]
  exact ⟨by simpa using ShiftWeight.card_support_sq_add_X_mul_sq (tracePoly k) 0, rfl⟩

/-- The degree-eleven source and its thirteenth-power pentanomial both have full order. -/
theorem primitive_midpoint_pair_11 : Primitive (decode 0x805) ∧ Primitive (decode 0x863) := by
  have h : ∀ p ∈ [23,89], Nat.Prime p := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl <;> decide
  exact ⟨(check_sound h (by decide +kernel : check 11 0x805 [23,89] = true)).2.2,
         (check_sound h (by decide +kernel : check 11 0x863 [23,89] = true)).2.2⟩

/-- The degree-28 source and its 31st-power pentanomial both have full order. -/
theorem primitive_midpoint_pair_28 : Primitive (decode 0x10000009) ∧ Primitive (decode 0x10008083) := by
  have h : ∀ p ∈ [3,5,29,43,113,127], Nat.Prime p := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact ⟨(check_sound h (by decide +kernel : check 28 0x10000009 [3,5,29,43,113,127] = true)).2.2,
         (check_sound h (by decide +kernel : check 28 0x10008083 [3,5,29,43,113,127] = true)).2.2⟩

end
end GF2Sparse.SternPowers
