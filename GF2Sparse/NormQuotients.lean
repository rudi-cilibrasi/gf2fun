import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Tactic.Ring

/-! Lower bounds for the degrees of two polynomials representing a residue as a quotient. -/

namespace GF2Sparse.NormQuotients

open Polynomial

variable {K : Type*} [Field K]

def pairDegree (p b : K[X]) : ℕ := max p.natDegree b.natDegree

/-- Modular representations agree as rational functions when both cross products
have degree below the modulus. The numerator and denominator may have different sizes. -/
theorem same_ratio_of_cross_degrees {f ρ p b A B : K[X]}
    (hp : f ∣ p - ρ * b) (hA : f ∣ A - ρ * B)
    (hpB : p.natDegree + B.natDegree < f.natDegree)
    (hbA : b.natDegree + A.natDegree < f.natDegree) : p * B = b * A := by
  have hd : f ∣ p * B - b * A := by
    obtain ⟨u, hu⟩ := hp
    obtain ⟨v, hv⟩ := hA
    refine ⟨u * B - b * v, ?_⟩
    calc
      p * B - b * A = (p - ρ * b) * B - b * (A - ρ * B) := by ring
      _ = f * (u * B - b * v) := by rw [hu, hv]; ring
  have bound : (p * B - b * A).natDegree < f.natDegree :=
    (natDegree_sub_le _ _).trans_lt (max_lt
      ((natDegree_mul_le).trans_lt hpB) ((natDegree_mul_le).trans_lt hbA))
  by_contra h
  exact (not_lt_of_ge (natDegree_le_of_dvd hd (sub_ne_zero.mpr h))) bound

/-- At the first Euclidean numerator of degree at most the proposed numerator's degree,
the preceding remainder's degree determines the denominator degree. Any fraction of
total degree below the modulus must agree with this convergent. -/
theorem same_ratio_at_degree_crossing {f ρ p b A B : K[X]} {previousDegree : ℕ}
    (hp : f ∣ p - ρ * b) (hA : f ∣ A - ρ * B)
    (hden : previousDegree + b.natDegree = f.natDegree)
    (hcross : p.natDegree ≤ A.natDegree) (hprev : A.natDegree < previousDegree)
    (htotal : A.natDegree + B.natDegree < f.natDegree) : p * B = b * A :=
  same_ratio_of_cross_degrees hp hA (by omega) (by omega)

private theorem same_ratio_of_small_degree {f ρ p b A B : K[X]}
    (hp : f ∣ p - ρ * b) (hA : f ∣ A - ρ * B)
    (small : pairDegree p b + pairDegree A B < f.natDegree) : p * B = b * A :=
  same_ratio_of_cross_degrees hp hA
    ((Nat.add_le_add (le_max_left _ _) (le_max_right _ _)).trans_lt small)
    ((Nat.add_le_add (le_max_right _ _) (le_max_left _ _)).trans_lt small)

/-- Two independent modular representations force every other representation with
a nonzero denominator to have degree at least the modulus degree minus their maximum degree. -/
theorem modulus_degree_le {f ρ p₀ b₀ p₁ b₁ A B : K[X]}
    (h₀ : f ∣ p₀ - ρ * b₀) (h₁ : f ∣ p₁ - ρ * b₁) (hA : f ∣ A - ρ * B)
    (independent : p₀ * b₁ ≠ p₁ * b₀) (hB : B ≠ 0) :
    f.natDegree ≤ max (pairDegree p₀ b₀) (pairDegree p₁ b₁) + pairDegree A B := by
  by_contra! small
  have e₀ := same_ratio_of_small_degree h₀ hA
    ((Nat.add_le_add_right (le_max_left _ _) _).trans_lt small)
  have e₁ := same_ratio_of_small_degree h₁ hA
    ((Nat.add_le_add_right (le_max_right _ _) _).trans_lt small)
  apply independent
  apply mul_right_cancel₀ hB
  calc
    (p₀ * b₁) * B = b₁ * (p₀ * B) := by ring
    _ = b₁ * (b₀ * A) := by rw [e₀]
    _ = b₀ * (p₁ * B) := by rw [e₁]; ring
    _ = (p₁ * b₀) * B := by ring

/-- Rounding the degree bounds to a multiple of the degree-13 Frobenius parameter. -/
theorem frobenius_degree_bounds {D : ℕ} (hq : 13 ∣ D) :
    (614 ≤ D → 624 ≤ D) ∧ (1228 ≤ D → 1235 ≤ D) := by
  omega

/-- An even polynomial degree makes the norm degree a multiple of 26. -/
theorem even_single_degree_bound {D : ℕ} (hq : 26 ∣ D) (degree : 1228 ≤ D) :
    1248 ≤ D := by
  omega

end GF2Sparse.NormQuotients
