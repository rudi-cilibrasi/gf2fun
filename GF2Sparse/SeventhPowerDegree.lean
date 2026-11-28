import GF2Sparse.Dilation
import Mathlib.Tactic.ReduceModChar

/-! The full degree drop under powering, and the vanishing traces of a cubic scalar. -/

namespace GF2Sparse

open Polynomial

/-- The largest possible degree drop under d-th powering characterizes substitution by X^d. -/
theorem expand_iff_full_power_degree_drop {K : Type*} [Field K] [Algebra (ZMod 2) K]
    {f : BinaryPoly} (hf : Irreducible f) {z : K} (hz : aeval z f = 0)
    {d : ℕ} (hd : 0 < d) :
    f = expand (ZMod 2) d (minpoly (ZMod 2) (z^d)) ↔
      f.natDegree = (minpoly (ZMod 2) (z^d)).natDegree * d := by
  have hi : IsIntegral (ZMod 2) z := ⟨f, binary_monic hf.ne_zero, hz⟩
  have hm := minpoly.monic (hi.pow d)
  constructor
  · intro h
    rw [h, natDegree_expand]
  · intro h
    have hdiv : f ∣ expand (ZMod 2) d (minpoly (ZMod 2) (z^d)) := by
      rw [minpoly.eq_of_irreducible_of_monic hf hz (binary_monic hf.ne_zero)]
      apply minpoly.dvd
      rw [expand_aeval]
      exact minpoly.aeval _ _
    exact (eq_of_monic_of_dvd_of_natDegree_le (binary_monic hf.ne_zero)
      (hm.expand hd) hdiv (by rw [natDegree_expand, h])).symm

/-- One of the two nonidentity Frobenius orbits of seventh roots has trace zero. -/
theorem seventh_root_trace_or {K : Type*} [Field K] [CharP K 2] {a : K}
    (ha : a^7 = 1) (hne : a ≠ 1) : a + a^2 + a^4 = 0 ∨ a^3 + a^5 + a^6 = 0 := by
  have h : (a-1) * ((a^3+a+1) * (a^3+a^2+1)) = 0 := by
    calc
      _ = a^7-1 := by ring_nf; reduce_mod_char!
      _ = 0 := by rw [ha, sub_self]
  rcases mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)) with h | h
  · left
    calc
      _ = a * (a^3+a+1) := by ring
      _ = 0 := by rw [h, mul_zero]
  · right
    calc
      _ = a^3 * (a^3+a^2+1) := by ring
      _ = 0 := by rw [h, mul_zero]

/-- A vanishing scalar power sum forces the same vanishing in an entire residue class
for the three scaled conjugates. The scalar multiplier can lie in any binary extension. -/
theorem seventh_root_trace_class {K : Type*} [Field K] {a : K} (ha : a^7 = 1)
    (b : K) (r j : ℕ) (h : a^r + (a^2)^r + (a^4)^r = 0) :
    (a*b)^(7*j+r) + (a^2*b)^(7*j+r) + (a^4*b)^(7*j+r) = 0 := by
  have h₂ : (a^2)^7 = 1 := by rw [pow_right_comm, ha, one_pow]
  have h₄ : (a^4)^7 = 1 := by rw [pow_right_comm, ha, one_pow]
  simp only [mul_pow, ← add_mul]
  rw [pow_add a, pow_add (a^2), pow_add (a^4), pow_mul, pow_mul, pow_mul, ha, h₂, h₄]
  simp [h]

end GF2Sparse
