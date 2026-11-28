import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-! The area bound for a power substitution supported in a Frobenius rectangle. -/

namespace GF2Sparse.FrobeniusBoxes

/-- Twice the signed area of the triangle with vertices (xᵢ,yᵢ). -/
def determinant (x₀ y₀ x₁ y₁ x₂ y₂ : ℤ) : ℤ :=
  (x₁ - x₀)*(y₂ - y₀) - (x₂ - x₀)*(y₁ - y₀)

/-- The three vertices can be numbered with nondecreasing first coordinate. -/
theorem determinant_bounds {h d x₀ y₀ x₁ y₁ x₂ y₂ : ℤ}
    (hx₀ : 0 ≤ x₀) (hx₁ : x₀ ≤ x₁) (hx₂ : x₁ ≤ x₂) (hxh : x₂ ≤ h)
    (hy₀ : 0 ≤ y₀ ∧ y₀ ≤ d) (hy₁ : 0 ≤ y₁ ∧ y₁ ≤ d) (hy₂ : 0 ≤ y₂ ∧ y₂ ≤ d) :
    -(h*d) ≤ determinant x₀ y₀ x₁ y₁ x₂ y₂ ∧ determinant x₀ y₀ x₁ y₁ x₂ y₂ ≤ h*d := by
  have h₀₁ : 0 ≤ x₁ - x₀ := sub_nonneg.mpr hx₁
  have h₁₂ : 0 ≤ x₂ - x₁ := sub_nonneg.mpr hx₂
  have h₀₂ : 0 ≤ x₂ - x₀ := sub_nonneg.mpr (hx₁.trans hx₂)
  have hd : 0 ≤ d := hy₀.1.trans hy₀.2
  have hspan : (x₂ - x₀)*d ≤ h*d := mul_le_mul_of_nonneg_right (by omega) hd
  unfold determinant
  constructor
  · nlinarith [mul_nonneg h₀₁ hy₂.1, mul_nonneg h₁₂ hy₀.1,
      mul_nonneg h₀₂ (sub_nonneg.mpr hy₁.2)]
  · nlinarith [mul_nonneg h₀₂ hy₁.1, mul_nonneg h₀₁ (sub_nonneg.mpr hy₂.2),
      mul_nonneg h₁₂ (sub_nonneg.mpr hy₀.2)]

/-- A noncollinear triple whose flattened exponents belong to t + kℤ forces k ≤ h*d. -/
theorem step_le_area {h d q k t e₀ e₁ e₂ x₀ y₀ x₁ y₁ x₂ y₂ : ℤ}
    (hk : 0 < k) (hx₀ : 0 ≤ x₀) (hx₁ : x₀ ≤ x₁) (hx₂ : x₁ ≤ x₂) (hxh : x₂ ≤ h)
    (hy₀ : 0 ≤ y₀ ∧ y₀ ≤ d) (hy₁ : 0 ≤ y₁ ∧ y₁ ≤ d) (hy₂ : 0 ≤ y₂ ∧ y₂ ≤ d)
    (he₀ : x₀ + q*y₀ = t + k*e₀) (he₁ : x₁ + q*y₁ = t + k*e₁)
    (he₂ : x₂ + q*y₂ = t + k*e₂) (hn : determinant x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) :
    k ≤ h*d := by
  let l := (e₁ - e₀)*(y₂ - y₀) - (e₂ - e₀)*(y₁ - y₀)
  have he : determinant x₀ y₀ x₁ y₁ x₂ y₂ = k*l := by
    unfold determinant l
    linear_combination (y₂ - y₀)*(he₁ - he₀) - (y₁ - y₀)*(he₂ - he₀)
  have hl : l ≠ 0 := by
    intro hz
    exact hn (by rw [he, hz, mul_zero])
  obtain ⟨lower, upper⟩ := determinant_bounds hx₀ hx₁ hx₂ hxh hy₀ hy₁ hy₂
  rw [he] at lower upper
  rcases lt_or_gt_of_ne hl with neg | pos
  · nlinarith [mul_nonneg hk.le (show 0 ≤ -l - 1 by omega)]
  · nlinarith [mul_nonneg hk.le (show 0 ≤ l - 1 by omega)]

end GF2Sparse.FrobeniusBoxes
