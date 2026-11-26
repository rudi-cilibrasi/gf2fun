import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring

namespace GF2Sparse.HermitianDescent

/-- Substituting the rational model in each monomial of a pencil. -/
theorem clear_monomial {R : Type*} [CommRing R] (x h₀ h₁ : R) (i j m q : ℕ)
    (hi : i ≤ m) (h : h₀ = x*h₁) :
    h₀^i * h₁^(m-i) * (x^q)^j = h₁^m * x^(i+q*j) := by
  rw [h, mul_pow, pow_add, pow_mul]
  calc
    _ = (h₁^i * h₁^(m-i)) * (x^i * (x^q)^j) := by ring
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le hi]

/-- Clearing a principal two-by-two determinant expresses a rank-two ternary
form through the two corresponding columns and rows. The barred entries can
be specialized to Frobenius conjugates. -/
theorem rank_two_pencil {R : Type*} [CommRing R]
    (a b c u v w ub vb wb x₀ x₁ x₂ y₀ y₁ y₂ : R)
    (hdet : a*b*c + u*w*vb + v*ub*wb - v*b*vb - u*ub*c - a*w*wb = 0) :
    (a*b-u*ub) * (x₀*(a*y₀+u*y₁+v*y₂) + x₁*(ub*y₀+b*y₁+w*y₂) +
        x₂*(vb*y₀+wb*y₁+c*y₂)) =
      (a*x₀+ub*x₁+vb*x₂) * (b*(a*y₀+u*y₁+v*y₂)-u*(ub*y₀+b*y₁+w*y₂)) +
      (u*x₀+b*x₁+wb*x₂) * (a*(ub*y₀+b*y₁+w*y₂)-ub*(a*y₀+u*y₁+v*y₂)) := by
  calc
    _ = (a*x₀+ub*x₁+vb*x₂) * (b*(a*y₀+u*y₁+v*y₂)-u*(ub*y₀+b*y₁+w*y₂)) +
        (u*x₀+b*x₁+wb*x₂) * (a*(ub*y₀+b*y₁+w*y₂)-ub*(a*y₀+u*y₁+v*y₂)) +
        (a*b*c + u*w*vb + v*ub*wb - v*b*vb - u*ub*c - a*w*wb)*x₂*y₂ := by ring
    _ = _ := by rw [hdet]; ring

/-- Completing the norm in a binary Hermitian form, with denominators cleared. -/
theorem norm_circle {K : Type*} [Field K] (a c u ub f fb g gb : K) (hc : c ≠ 0) :
    c*f*fb + u*f*gb + ub*g*fb + a*g*gb = 0 ↔
      (c*f+ub*g)*(c*fb+u*gb) = (u*ub-a*c)*g*gb := by
  have ident : (c*f+ub*g)*(c*fb+u*gb) - (u*ub-a*c)*g*gb =
      c*(c*f*fb + u*f*gb + ub*g*fb + a*g*gb) := by ring
  calc
    _ ↔ c*(c*f*fb + u*f*gb + ub*g*fb + a*g*gb) = 0 := by simp [hc]
    _ ↔ _ := by rw [← ident, sub_eq_zero]

/-- The Artin--Schreier inverse image of a split horizontal line factors into two lines. -/
theorem artinSchreier_lines {K : Type*} [CommRing K] [CharP K 2] (x y v : K) :
    (x^2+x) + (y^2+y) + (v^2+v) = (x+y+v) * (x+y+v+1) := by
  calc
    _ = (x+y+v)^2 + (x+y+v) := by simp only [CharTwo.add_sq]; ring
    _ = _ := by ring

open Polynomial

/-- A trace sum cannot be constant on a torus when only its first exponent
reduces to one. Its representing polynomial has degree below the size of the
torus and a nonzero linear coefficient. -/
theorem trace_sum_nonconstant {K : Type*} [Field K] {m h : ℕ}
    (hm : 1 < m) (hh : 0 < h)
    (exponents : ∀ i < h, 2^i % m = 1 → i = 0)
    (s : Finset K) (card : s.card = m) (torus : ∀ x ∈ s, x^m = 1)
    {a : K} (ha : a ≠ 0) (b : K) :
    ¬ ∀ x ∈ s, (∑ i ∈ Finset.range h, (a*x)^(2^i)) = b := by
  classical
  let term (i : ℕ) : K[X] := monomial (2^i % m) (a^(2^i))
  let p := ∑ i ∈ Finset.range h, term i
  have bound : p.natDegree ≤ m-1 := by
    apply natDegree_sum_le_of_forall_le
    intro i _
    exact (natDegree_monomial_le _).trans (by have := Nat.mod_lt (2^i) (by omega : 0 < m); omega)
  have linear : p.coeff 1 = a := by
    simp only [p, finset_sum_coeff]
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hh)]
    · simp [term, Nat.mod_eq_of_lt hm]
    · intro i hi hne
      have ne : 2^i % m ≠ 1 := fun he => hne (exponents i (Finset.mem_range.mp hi) he)
      simp [term, coeff_monomial, ne]
  intro all
  have equal : p = C b := by
    apply eq_of_natDegree_lt_card_of_eval_eq' _ _ s
    · intro x hx
      calc
        p.eval x = ∑ i ∈ Finset.range h, a^(2^i) * x^(2^i % m) := by
          simp [p, term, eval_finset_sum]
        _ = ∑ i ∈ Finset.range h, (a*x)^(2^i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [mul_pow, pow_eq_pow_mod (2^i) (torus x hx)]
        _ = (C b).eval x := by simpa using all x hx
    · rw [card, natDegree_C]
      omega
  exact ha (by simpa [equal] using linear.symm)

/-- The absolute-trace exponents have residue one only at the first term, for every
binary norm torus of order (2^h+1). -/
theorem torus_trace_exponents (h i : ℕ) (hi : i < 2*h)
    (one : 2^i % (2^h+1) = 1) : i = 0 := by
  by_cases lo : i < h
  · have small := Nat.pow_lt_pow_right (by decide : 1 < 2) lo
    rw [Nat.mod_eq_of_lt (by omega)] at one
    by_contra nonzero
    have big := Nat.pow_lt_pow_right (by decide : 1 < 2) (show 0 < i by omega)
    simp [one] at big
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt lo)
    have small := Nat.pow_lt_pow_right (by decide : 1 < 2) (show j < h by omega)
    have multiple : 2^h+1 ∣ 2^(h+j)+2^j := ⟨2^j, by rw [pow_add]; ring⟩
    have nonzero : (2^(h+j)+2^j) % (2^h+1) = 1+2^j := by
      have rem := Nat.mod_eq_of_lt (show 2^j < 2^h+1 by omega)
      rw [Nat.add_mod, one, rem, Nat.mod_eq_of_lt (show 1+2^j < 2^h+1 by omega)]
    have impossible : 0 = 1+2^j := (Nat.mod_eq_zero_of_dvd multiple).symm.trans nonzero
    exact (Nat.succ_ne_zero (2^j) (by simpa [Nat.add_comm] using impossible.symm)).elim

end GF2Sparse.HermitianDescent
