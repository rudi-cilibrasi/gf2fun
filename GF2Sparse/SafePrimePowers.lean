import GF2Sparse.SeventhPowerDegree

/-! The two order-33 base polynomials and the exact orders of their dilations. -/

namespace GF2Sparse

/-- Every element of order 33 in characteristic two satisfies one of these pentanomials. -/
theorem order_33_pentanomials {K : Type*} [Field K] [CharP K 2] {z : K}
    (h : z^33 = 1) (h₃ : z^3 ≠ 1) (h₁₁ : z^11 ≠ 1) :
    z^10 + z^9 + z^5 + z + 1 = 0 ∨ z^10 + z^7 + z^5 + z^3 + 1 = 0 := by
  have hc : z^2 + z + 1 ≠ 0 := by
    intro hc
    apply h₃
    apply sub_eq_zero.mp
    calc
      z^3 - 1 = (z-1) * (z^2+z+1) := by ring
      _ = 0 := by rw [hc, mul_zero]
  have hf : ((z^11-1) * (z^2+z+1)) *
      ((z^10+z^9+z^5+z+1) * (z^10+z^7+z^5+z^3+1)) = 0 := by
    calc
      _ = z^33-1 := by ring_nf; reduce_mod_char!
      _ = 0 := by rw [h, sub_self]
  exact mul_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left
    (mul_ne_zero (sub_ne_zero.mpr h₁₁) hc))

/-- If the base order contains d, every successive d-th root gains the full factor d. -/
theorem order_of_iterated_root {M : Type*} [Monoid M] {d m : ℕ}
    (hd : d ≠ 0) (hm : d ∣ m) (i : ℕ) (z : M) (h : orderOf (z^(d^i)) = m) :
    orderOf z = m * d^i := by
  induction i generalizing z with
  | zero => simpa using h
  | succ i ih =>
    have hstep : orderOf ((z^d)^(d^i)) = m := by rwa [← pow_mul, ← pow_succ']
    have hz := ih (z^d) hstep
    have hdiv : d ∣ orderOf (z^d) := hz ▸ dvd_mul_of_dvd_left hm _
    have hroot : d ∣ orderOf z := hdiv.trans (orderOf_pow_dvd d)
    rw [orderOf_pow_of_dvd hd hroot] at hz
    calc
      orderOf z = (orderOf z / d) * d := (Nat.div_mul_cancel hroot).symm
      _ = m * d^(i+1) := by rw [hz, pow_succ, mul_assoc]

end GF2Sparse
