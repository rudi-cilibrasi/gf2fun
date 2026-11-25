import GF2Sparse.Table

/-! Product pentanomials with no pair of mutually inverse roots. -/

namespace GF2Sparse

open Polynomial

private theorem eval_product_root {K : Type*} [Field K] [Algebra (ZMod 2) K] [CharP K 2]
    {n u v : ℕ} {x : K} (hz : aeval x (productCandidate n u v) = 0) :
    x ^ n = (x ^ u + 1) * (x ^ v + 1) := by
  apply CharTwo.add_eq_zero.1
  simpa only [productCandidate, map_add, map_mul, map_pow, aeval_X, map_one] using hz

/-- A root and its inverse force x^(2n)=x^(u+v). If the gap is a
dyadic multiple of a divisor of u, no such pair can occur. -/
theorem product_no_inverse_root {K : Type*} [Field K] [Algebra (ZMod 2) K] [CharP K 2]
    {n u v s w : ℕ} (hgap : n + n = (u + v) + w * 2 ^ s) (hd : w ∣ u)
    {x : K} (hx : x ≠ 0) (hz : aeval x (productCandidate n u v) = 0) :
    aeval x⁻¹ (productCandidate n u v) ≠ 0 := by
  intro hi
  have h := eval_product_root hz
  have hi' := eval_product_root hi
  simp only [inv_pow] at hi'
  have hprod : x ^ n * ((x ^ u + 1) * (x ^ v + 1)) = x ^ u * x ^ v := by
    field_simp [hx] at hi'
    linear_combination -hi'
  have he : x ^ (u + v) * x ^ (w * 2 ^ s) = x ^ (u + v) * 1 := by
    calc
      _ = x ^ (n + n) := by rw [← pow_add, hgap]
      _ = x ^ n * ((x ^ u + 1) * (x ^ v + 1)) := by rw [pow_add, ← h]
      _ = _ := by rw [hprod, pow_add, mul_one]
  have he' := mul_left_cancel₀ (pow_ne_zero (u + v) hx) he
  rw [pow_mul] at he'
  have hw : x ^ w = 1 := by
    apply (iterateFrobenius_inj K 2 s)
    simpa only [iterateFrobenius_def, one_pow] using he'
  obtain ⟨j, rfl⟩ := hd
  rw [pow_mul, hw, one_pow, CharTwo.add_self_eq_zero, zero_mul] at h
  exact pow_ne_zero n hx h

/-- The B = 3 construction with L = 21, P = 32 and w = 1 is primitive
in degree 55. -/
theorem reciprocal_sieve_example_55 :
    Primitive (X ^ 55 + X ^ 46 + X ^ 25 + X ^ 21 + 1) := by
  exact certify_five_terms 55 46 25 21 [23, 31, 89, 881, 3191, 201961] (by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1) (by decide +kernel)

end GF2Sparse
