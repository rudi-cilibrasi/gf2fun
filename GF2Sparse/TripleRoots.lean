import GF2Sparse.Progressions
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Product-one triples of roots on the binary line u + v = 1. -/

namespace GF2Sparse

open Polynomial

/-- The three roots may coincide. This condition also passes to f(X^m). -/
def NoRootTriple (f : BinaryPoly) : Prop :=
  ∀ x y z : AlgebraicClosure (ZMod 2), aeval x f = 0 → aeval y f = 0 →
    aeval z f = 0 → x * y * z ≠ 1

section Field

variable {K : Type*} [Field K] [CharP K 2]

/-- Among three points with product one whose translates also have product
one, one of the other two points must be 1/(u+1). -/
theorem triple_translate_orbit {u v w : K}
    (h : u * v * w = 1) (ht : (u + 1) * (v + 1) * (w + 1) = 1) :
    v * (u + 1) = 1 ∨ w * (u + 1) = 1 := by
  have hz : (v * (u + 1) + 1) * (w * (u + 1) + 1) = 0 := by
    linear_combination ht + (u + 1) * h + CharTwo.add_self_eq_zero (1 : K)
  exact (mul_eq_zero.1 hz).imp CharTwo.add_eq_zero.1 CharTwo.add_eq_zero.1

private theorem orbit_translate {u v : K} (h : v * (u + 1) = 1) :
    (v + 1) * (u + 1) = u := by
  rw [add_mul, h, one_mul, add_comm u 1, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

private theorem orbit_frobenius {u v : K} (h : v * (u + 1) = 1) (s : ℕ) :
    v ^ (2 ^ s) * (u ^ (2 ^ s) + 1) = 1 := by
  calc
    _ = (v * (u + 1)) ^ (2 ^ s) := by rw [mul_pow, add_pow_expChar_pow, one_pow]
    _ = _ := by rw [h, one_pow]

omit [CharP K 2] in
private theorem product_powers {x y z : K} (h : x * y * z = 1) (i : ℕ) :
    x ^ i * y ^ i * z ^ i = 1 := by rw [← mul_pow, ← mul_pow, h, one_pow]

variable [Algebra (ZMod 2) K]

private theorem trinomial_root_power {x : K} {n a : ℕ} (h : aeval x (trinomial n a) = 0) :
    x ^ n = x ^ a + 1 := by
  simpa only [trinomial, map_add, map_pow, aeval_X, map_one, CharTwo.add_eq_zero] using h

omit [Algebra (ZMod 2) K] in
private theorem order_from_trinomial_orbit {x y : K} {n a : ℕ} (ha : a ≤ n) (hx : x ≠ 0)
    (hxn : x ^ n = x ^ a + 1) (hyn : y ^ n = y ^ a + 1) (horb : y ^ a * (x ^ a + 1) = 1) :
    orderOf x ∣ n * (n - a) + a * a := by
  have hfirst : x ^ n * y ^ a = 1 := by rwa [hxn, mul_comm]
  have hsecond : x ^ n * y ^ n = x ^ a := by
    rw [hxn, hyn, mul_comm]; exact orbit_translate horb
  have h0 : x ^ (n * n) * y ^ (a * n) = 1 := by
    simpa only [mul_pow, ← pow_mul, one_pow] using congrArg (· ^ n) hfirst
  have h1 : x ^ (n * a) * y ^ (a * n) = x ^ (a * a) := by
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm a n] using congrArg (· ^ a) hsecond
  have hpow : x ^ (n * n) * x ^ (a * a) = x ^ (n * a) := by
    calc
      _ = x ^ (n * n) * (x ^ (n * a) * y ^ (a * n)) := by rw [h1]
      _ = (x ^ (n * n) * y ^ (a * n)) * x ^ (n * a) := by ac_rfl
      _ = _ := by rw [h0, one_mul]
  have hsum : n * (n - a) + a * a + n * a = n * n + a * a := by
    rw [Nat.mul_sub_left_distrib]
    have := Nat.mul_le_mul_left n ha
    omega
  apply orderOf_dvd_of_pow_eq_one
  apply mul_right_cancel₀ (pow_ne_zero (n * a) hx)
  rw [one_mul, ← pow_add, hsum, pow_add, hpow]

/-- Each root in a product-one triple of a binary trinomial has order dividing
n²-na+a². This direction allows repeated roots and arbitrary exponent gcd. -/
theorem trinomial_triple_order_dvd {x y z : K} {n a : ℕ} (ha : a ≤ n)
    (hx : aeval x (trinomial n a) = 0) (hy : aeval y (trinomial n a) = 0)
    (hz : aeval z (trinomial n a) = 0) (h : x * y * z = 1) :
    orderOf x ∣ n * (n - a) + a * a := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at h
  have hxn := trinomial_root_power hx
  have hyn := trinomial_root_power hy
  have hzn := trinomial_root_power hz
  have ht := product_powers h n
  rw [hxn, hyn, hzn] at ht
  rcases triple_translate_orbit (product_powers h a) ht with horb | horb
  · exact order_from_trinomial_orbit ha hx0 hxn hyn horb
  · exact order_from_trinomial_orbit ha hx0 hxn hzn horb

end Field

/-- Substituting a power preserves the exclusion, including when several
roots upstairs have the same image under the power map. -/
theorem NoRootTriple.expand {f : BinaryPoly} (hf : NoRootTriple f) (m : ℕ) :
    NoRootTriple (Polynomial.expand (ZMod 2) m f) := by
  intro x y z hx hy hz h
  rw [expand_aeval] at hx hy hz
  exact hf _ _ _ hx hy hz (product_powers h m)

end GF2Sparse
