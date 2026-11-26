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

end GF2Sparse.HermitianDescent
