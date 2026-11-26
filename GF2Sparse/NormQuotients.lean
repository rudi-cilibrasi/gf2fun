import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Tactic.Ring

/-! Lower bounds for the degrees of two polynomials representing a residue as a quotient. -/

namespace GF2Sparse.NormQuotients

open Polynomial

variable {K : Type*} [Field K]

def pairDegree (p b : K[X]) : ℕ := max p.natDegree b.natDegree

private theorem same_ratio_of_small_degree {f ρ p b A B : K[X]}
    (hp : f ∣ p - ρ * b) (hA : f ∣ A - ρ * B)
    (small : pairDegree p b + pairDegree A B < f.natDegree) : p * B = b * A := by
  have hd : f ∣ p * B - b * A := by
    obtain ⟨u, hu⟩ := hp
    obtain ⟨v, hv⟩ := hA
    refine ⟨u * B - b * v, ?_⟩
    calc
      p * B - b * A = (p - ρ * b) * B - b * (A - ρ * B) := by ring
      _ = f * (u * B - b * v) := by rw [hu, hv]; ring
  have bound : (p * B - b * A).natDegree ≤ pairDegree p b + pairDegree A B :=
    (natDegree_sub_le _ _).trans (max_le
      (natDegree_mul_le_of_le (le_max_left _ _) (le_max_right _ _))
      (natDegree_mul_le_of_le (le_max_right _ _) (le_max_left _ _)))
  by_contra h
  exact (not_lt_of_ge (natDegree_le_of_dvd hd (sub_ne_zero.mpr h))) (bound.trans_lt small)

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

end GF2Sparse.NormQuotients
