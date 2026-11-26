import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Coordinate identities and finite fiber calculations for the degree-five map
used by the degree-1229 Frobenius model. -/

namespace GF2Sparse.QuinticIsogeny

section Field

variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem denominator (z : K) : z^2 + z = z*(z+1) := by ring

theorem cubic (z : K) : z^3 + z = (z*(z+1))*(z+1) := by
  rw [mul_assoc, ← sq, CharTwo.add_sq]
  ring

/-- The elliptic-curve addition slopes for Frobenius plus and minus the point. -/
theorem frobenius_x_coordinates (z w : K) (hz : z ≠ 0) (hz' : z+1 ≠ 0)
    (curve : w^2+w = z^3+z) :
    ((w^2+w)/(z^2+z))^2 + z^2+z = z+1 ∧
    ((w^2+w+1)/(z^2+z))^2 + z^2+z = z+1+(1/(z*(z+1)))^2 := by
  have hn : z*(z+1) ≠ 0 := mul_ne_zero hz hz'
  have slope : (w^2+w)/(z^2+z) = z+1 := by
    rw [curve, cubic, denominator]
    exact (mul_div_cancel_left₀ _ hn)
  have first : ((w^2+w)/(z^2+z))^2 + z^2+z = z+1 := by
    rw [slope, CharTwo.add_sq]
    calc
      _ = (z^2+z^2) + (z+1) := by ring
      _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]
  refine ⟨first, ?_⟩
  rw [add_div, CharTwo.add_sq]
  calc
    _ = (((w^2+w)/(z^2+z))^2+z^2+z) + (1/(z^2+z))^2 := by ring
    _ = _ := by rw [first, denominator]

/-- The same rational map in the inverse coordinate of the binary model. -/
theorem rational_model (t : K) (ht : t ≠ 0) (ht' : t+1 ≠ 0) :
    (t^5+t^2+1)/(t^3+t) = 1/t + (t^2/(t+1))^2 := by
  have hnum : t^5+t^2+1 = t^5+(t+1)^2 := by rw [CharTwo.add_sq]; ring
  rw [hnum, cubic]
  field_simp
  ring

end Field

/-- The three Frobenius cycle types on the five points of a fiber. -/
theorem fiber_permutations :
    (∀ (s : ZMod 5), s ≠ 0 → Function.Bijective (fun i : ZMod 5 => i*s)) ∧
    (∀ (s : ZMod 5), (Finset.univ.filter (fun i : ZMod 5 => s-i=i)).card = 1 ∧
      ∀ i : ZMod 5, s-(s-i)=i) := by decide +kernel

def frobeniusTrace : ℕ → ℤ
  | 0 => 2
  | 1 => -2
  | n+2 => -2*frobeniusTrace (n+1)-2*frobeniusTrace n

def curveOrder (m : ℕ) : ℤ := 2^m+1-frobeniusTrace m

theorem fiber_counts :
    2*curveOrder 1 = 5*2 ∧
    2*(curveOrder 2-curveOrder 1) = 0 ∧
    2*(curveOrder 4-curveOrder 2) = 20*2 ∧
    2*curveOrder 5 = 25*2 ∧
    2*(curveOrder 10-curveOrder 5) = 50*40 ∧
    2*(curveOrder 20-curveOrder 10) = 100*20992 := by decide +kernel

end GF2Sparse.QuinticIsogeny
