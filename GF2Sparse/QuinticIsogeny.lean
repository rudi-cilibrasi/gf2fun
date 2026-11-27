import GF2Sparse.Certificate
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

private def maskPower (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => maskProduct (maskPower p n) p

private theorem decodePower (p n : ℕ) : decode (maskPower p n) = (decode p)^n := by
  induction n with
  | zero => simp [maskPower]
  | succ n ih => simp [maskPower, ih, pow_succ]

private theorem decodeProduct (ps : List ℕ) :
    decode (ps.foldr maskProduct 1) = (ps.map decode).prod := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [ih]

private theorem decodeSum (ps : List ℕ) :
    decode (ps.foldr (· ^^^ ·) 0) = (ps.map decode).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [ih]

/-- The five octics in the homogeneous pullback of the binary mask 0x1e7. -/
theorem octicPullback :
    ([0x15f, 0x19f, 0x1b1, 0x1cf, 0x1f5].map decode).prod =
      ([0, 1, 2, 5, 6, 7, 8].map fun (i : ℕ) => (decode 37)^i * (decode 10)^(8-i)).sum := by
  let ps : List ℕ := [0x15f, 0x19f, 0x1b1, 0x1cf, 0x1f5]
  let exps : List ℕ := [0, 1, 2, 5, 6, 7, 8]
  have eq : ps.foldr maskProduct 1 =
      (exps.map fun i => maskProduct (maskPower 37 i) (maskPower 10 (8-i))).foldr (· ^^^ ·) 0 := by
    decide +kernel
  simpa only [decodeProduct, decodeSum, List.map_map, Function.comp_def, decode_maskProduct, decodePower]
    using congrArg decode eq

/-- Clearing the denominator when the Frobenius exponent is lowered from 1024 to 256. -/
theorem octicCircle {A : Type*} [CommRing A] (x y u v b d : A)
    (hy : x^256 = y) (hr : x*v^4 = u^4) :
    (x^257 + b*(x^256+x) + d)*v^4 = (y+b)*u^4 + (b*y+d)*v^4 := by
  rw [show x^257 = x^256*x from pow_succ x 256, hy, ← hr]
  ring

/-- Multiplying the four conjugate circle equations contributes the sixteenth denominator power. -/
theorem octicCircleNorm {A : Type*} [CommRing A] (x y u v : A) (b d : Fin 4 → A)
    (hy : x^256 = y) (hr : x*v^4 = u^4) :
    (∏ i, (x^257 + b i*(x^256+x) + d i))*v^16 =
      ∏ i, ((y+b i)*u^4 + (b i*y+d i)*v^4) := by
  simp_rw [← octicCircle x y u v _ _ hy hr]
  rw [Finset.prod_mul_distrib]
  simp [← pow_mul]

/-- Each monomial of a bivariate Frobenius relation has the same cleared denominator. -/
theorem bivariateTerm {A : Type*} [CommMonoid A] (x y u v : A) (s q a i j : ℕ)
    (hi : i ≤ a) (hy : x^q = y) (hx : x*v^s = u^s) :
    x^(i+q*j)*v^(s*a) = u^(s*i)*v^(s*(a-i))*y^j := by
  have he : s*a = s*i+s*(a-i) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [pow_add, pow_mul x q j, hy, he, pow_add, pow_mul v s i, pow_mul u s i, ← hx, mul_pow]
  ac_rfl

/-- Distributing mass in proportion to child degrees preserves the homogeneous pullback equation. -/
theorem degreeTailStep {ι A : Type*} [CommRing A] (children : Finset ι) (d : ι → A)
    (q inverse mass parent : A) (h : 5*q*inverse = 1)
    (hdeg : ∑ i ∈ children, d i = 5*parent) :
    q*(∑ i ∈ children, (mass*inverse)*d i) = mass*parent := by
  rw [← Finset.mul_sum, hdeg]
  calc
    _ = mass*parent*(5*q*inverse) := by ring
    _ = mass*parent := by rw [h, mul_one]

/-- A homogeneous solution with value one at a target makes every target value compatible
with the prescribed linear equations, also over a composite residue ring. -/
theorem freeLogValue {ι κ A : Type*} [CommRing A] (support : κ → Finset ι)
    (coeff : κ → ι → A) (rhs : κ → A) (logs delta : ι → A) (p : ι)
    (hl : ∀ k, ∑ i ∈ support k, coeff k i * logs i = rhs k)
    (hd : ∀ k, ∑ i ∈ support k, coeff k i * delta i = 0)
    (hp : delta p = 1) (value : A) :
    ∃ f : ι → A, (∀ k, ∑ i ∈ support k, coeff k i * f i = rhs k) ∧ f p = value := by
  refine ⟨fun i => logs i + (value-logs p)*delta i, ?_, ?_⟩
  · intro k
    calc
      _ = ∑ i ∈ support k, (coeff k i * logs i + (value-logs p)*(coeff k i * delta i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = rhs k := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hl k, hd k, mul_zero, add_zero]
  · change logs p + (value-logs p)*delta p = value
    rw [hp, mul_one]
    ring

end GF2Sparse.QuinticIsogeny
