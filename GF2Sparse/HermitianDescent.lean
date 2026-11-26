import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FieldSimp
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

/-- The two-by-two bracket controlling the cross-ratio is scaled by the determinant. -/
theorem mobius_bracket {K : Type*} [CommRing K] (a b c d x y : K) :
    (a*x+b)*(c*y+d) - (a*y+b)*(c*x+d) = (a*d-b*c)*(x-y) := by ring

/-- Writing the two conjugates as θ and θ+1 turns their norm into an Artin--Schreier
equation. This also covers a nonunit scaling δ without division. -/
theorem scaled_quadratic_norm {K : Type*} [CommRing K] [CharP K 2] (θ w δ : K) :
    (δ*(θ+w)) * (δ*(θ+1+w)) = δ^2 * (θ^2+θ+(w^2+w)) := by
  calc
    _ = δ^2 * ((θ+w)^2 + (θ+w)) := by ring
    _ = _ := by rw [CharTwo.add_sq]; ring

/-- The two linear equations used by the pencil finder give the prescribed difference
of t = vθ+u and its Frobenius image. -/
theorem frobenius_difference {K : Type*} [CommRing K] [CharP K 2]
    (σ : K →+* K) (v θ u w δ ξ : K) (hv : v+σ v = δ) (hθ : σ θ = θ+ξ)
    (hu : σ u+u = δ*w+σ v*ξ) :
    σ (v*θ+u) + (v*θ+u) = δ*(θ+w) := by
  rw [map_add, map_mul, hθ]
  calc
    _ = (v+σ v)*θ + (σ u+u) + σ v*ξ := by ring
    _ = δ*θ + δ*w + (σ v*ξ+σ v*ξ) := by rw [hv, hu]; ring
    _ = _ := by rw [CharTwo.add_self_eq_zero]; ring

/-- Translating v by a fixed-field scalar s keeps v+σ(v) constant and gives a
binary-linear perturbation of vσ(v). -/
theorem translate_norm_on_line {K : Type*} [CommRing K] [CharP K 2]
    (σ : K →+* K) (v s : K) (hs : σ s = s) :
    (v+s) + σ (v+s) = v+σ v ∧
    (v+s)*σ (v+s) = v*σ v + (s^2 + (v+σ v)*s) := by
  rw [map_add, hs]
  constructor
  · calc
      _ = (v+σ v)+(s+s) := by ring
      _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
  · ring

/-- The sum of the constant terms in any quadratic partition is a root of the
cubic resolvent. In characteristic two the terms with a factor four vanish. -/
theorem quartic_partition_resolvent {K : Type*} [CommRing K] (p s r t : K) :
    let a := p+s
    let b := r+t+p*s
    let c := p*t+s*r
    let d := r*t
    let y := r+t
    y^3-b*y^2+(a*c-4*d)*y+(4*b*d-a^2*d-c^2) = 0 := by
  dsimp
  ring

/-- Translation by the quadratic coefficient depresses the binary resolvent. -/
theorem translate_cubic_resolvent {K : Type*} [CommRing K] [CharP K 2] (a b c d z : K) :
    (z+b)^3+b*(z+b)^2+a*c*(z+b)+a^2*d+c^2 =
      z^3+(b^2+a*c)*z+(a^2*d+c^2+a*b*c) := by
  have cancel : z+b+b = z := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  calc
    _ = (z+b)^2*(z+b+b)+a*c*(z+b)+a^2*d+c^2 := by ring
    _ = _ := by rw [cancel, CharTwo.add_sq]; ring

/-- A cube root and its complementary factor reconstruct a root of the depressed cubic. -/
theorem binary_cubic_sum {K : Type*} [CommRing K] [CharP K 2] (u v : K) :
    (u+v)^3+u*v*(u+v) = u^3+v^3 := by
  calc
    _ = (u+v)^2*(u+v)+u*v*(u+v) := by ring
    _ = (u^3+v^3)+((u^2*v+u*v^2)+(u^2*v+u*v^2)) := by rw [CharTwo.add_sq]; ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

/-- The relative trace of the product of the outer coefficients of the equation
for a common pencil point. The primed entries denote Frobenius conjugates. -/
theorem common_pencil_trace {K : Type*} [CommRing K] [CharP K 2]
    (a₁ a₂ d₁ d₂ b₁ b₁' b₂ b₂' : K) :
    (a₂*b₁'+a₁*b₂')*(d₁*b₂+d₂*b₁) + (a₂*b₁+a₁*b₂)*(d₁*b₂'+d₂*b₁') =
      (a₂*d₁+a₁*d₂)*(b₁'*b₂+b₁*b₂') := by
  let z := a₂*d₂*b₁*b₁' + a₁*d₁*b₂*b₂'
  calc
    _ = (z+z) + (a₂*d₁+a₁*d₂)*(b₁'*b₂+b₁*b₂') := by dsimp [z]; ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

/-- After division by (v+w)^2 this is the Artin--Schreier value of v/(v+w). -/
theorem common_pencil_artinSchreier {K : Type*} [CommRing K] [CharP K 2] (v w : K) :
    v^2+v*(v+w) = v*w := by
  calc
    _ = (v^2+v^2)+v*w := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

/-- If the relative trace of z²+z is the Artin--Schreier value of a fixed scalar,
then z belongs to the quadratic fixed field of the endomorphism. -/
theorem fixed_after_two_of_artinSchreier_trace {K : Type*} [Field K] [CharP K 2]
    (σ : K →+* K) (z t : K) (ht : σ t = t)
    (h : σ (z^2+z)+(z^2+z) = t^2+t) : σ (σ z) = z := by
  let y := σ z+z+t
  have hy : y*(y+1) = 0 := by
    calc
      y*(y+1) = y^2+y := by ring
      _ = (σ (z^2+z)+(z^2+z))+(t^2+t) := by
        simp only [y, CharTwo.add_sq, map_add, map_pow]; ring
      _ = 0 := by rw [h, CharTwo.add_self_eq_zero]
  have fixed : σ y = y := by
    rcases mul_eq_zero.mp hy with he | he
    · simp [he]
    · have one : y = 1 := by
        calc
          y = (y+1)+1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
          _ = 1 := by rw [he, zero_add]
      simp [one]
  have hsum : (σ (σ z)+σ z)+t = (σ z+z)+t := by
    simpa only [y, map_add, ht] using fixed
  have hpair := add_right_cancel hsum
  rw [add_comm (σ z) z] at hpair
  exact add_right_cancel hpair

/-- A quadratic whose normalized constant has Artin--Schreier relative trace
has all its roots in the quadratic fixed field. -/
theorem fixed_quadratic_root_of_trace {K : Type*} [Field K] [CharP K 2]
    (σ : K →+* K) (a b c z t : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfa : σ (σ a) = a) (hfb : σ (σ b) = b) (ht : σ t = t)
    (hz : a*z^2+b*z+c = 0)
    (h : σ (a*c/b^2)+(a*c/b^2) = t^2+t) : σ (σ z) = z := by
  have polynomial_value : a*z^2+b*z = c := by
    calc
      _ = (a*z^2+b*z+c)+c := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = c := by rw [hz, zero_add]
  have value : (a*z/b)^2+(a*z/b) = a*c/b^2 := by
    calc
      _ = a*(a*z^2+b*z)/b^2 := by field_simp
      _ = _ := by rw [polynomial_value]
  have fixed := fixed_after_two_of_artinSchreier_trace σ (a*z/b) t ht (by rw [value]; exact h)
  have equal : a*σ (σ z)/b = a*z/b := by simpa only [map_div₀, map_mul, hfa, hfb] using fixed
  field_simp at equal
  exact equal

/-- A quadratic with middle coefficient v+w and outer-coefficient trace v*w
cannot have a root outside the quadratic fixed field. These are the coefficients
obtained by cross-multiplying two distinct binary Hermitian projectivities. -/
theorem fixed_common_pencil_root {K : Type*} [Field K] [CharP K 2]
    (σ : K →+* K) (a c v w z : K) (hfa : σ (σ a) = a) (hfc : σ (σ c) = c)
    (hv : σ v = v) (hw : σ w = w) (nonzero : a ≠ 0 ∨ v+w ≠ 0)
    (hz : a*z^2+(v+w)*z+c = 0) (htrace : σ (a*c)+a*c = v*w) :
    σ (σ z) = z := by
  have conjugate := congrArg (fun x => σ (σ x)) hz
  simp only [map_add, map_mul, map_pow, map_zero, hfa, hfc, hv, hw] at conjugate
  by_cases ha : a = 0
  · have hb := nonzero.resolve_left (by simp [ha])
    simp only [ha, zero_mul, zero_add] at hz conjugate
    exact mul_left_cancel₀ hb (add_right_cancel (conjugate.trans hz.symm))
  by_cases hb : v+w = 0
  · simp only [hb, zero_mul, add_zero] at hz conjugate
    have hs := mul_left_cancel₀ ha (add_right_cancel (conjugate.trans hz.symm))
    have zero : (σ (σ z)+z)^2 = 0 := by
      rw [CharTwo.add_sq, hs, CharTwo.add_self_eq_zero]
    have diff : σ (σ z)+z = 0 := eq_zero_of_pow_eq_zero zero
    calc
      _ = (σ (σ z)+z)+z := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = z := by rw [diff, zero_add]
  have mid : σ (v+w) = v+w := by rw [map_add, hv, hw]
  apply fixed_quadratic_root_of_trace σ a (v+w) c z (v/(v+w)) ha hb hfa
      (by rw [mid, mid]) (by rw [map_div₀, hv, mid]) hz
  calc
    _ = (σ (a*c)+a*c)/(v+w)^2 := by rw [map_div₀, map_pow, mid, add_div]
    _ = (v^2+v*(v+w))/(v+w)^2 := by rw [htrace, common_pencil_artinSchreier]
    _ = _ := by field_simp

/-- A linear rational expression in the q-th power cannot contain a factor
of degree strictly greater than q+1 unless its cleared polynomial vanishes. -/
theorem height_one_factor_bound {K : Type*} [Field K] (q : ℕ) (a b c d : K)
    (P : K[X]) (hp : q+1 < P.natDegree)
    (hdiv : P ∣ C a*X^q+C b + X*(C c*X^q+C d)) :
    C a*X^q+C b + X*(C c*X^q+C d) = 0 := by
  have lin (u v : K) : (C u*X^q+C v).natDegree ≤ q := by
    apply (natDegree_add_le _ _).trans
    exact max_le ((natDegree_mul_le).trans (by simp)) (by simp)
  have bound : (C a*X^q+C b + X*(C c*X^q+C d)).natDegree ≤ q+1 := by
    apply (natDegree_add_le _ _).trans
    apply max_le ((lin a b).trans (by omega))
    have mulBound := @natDegree_mul_le K _ X (C c*X^q+C d)
    rw [natDegree_X] at mulBound
    have := lin c d
    omega
  by_contra nonzero
  exact (not_le_of_gt hp) ((natDegree_le_of_dvd hdiv nonzero).trans bound)

/-- In a nonzero cubic pencil a designated quadratic can leave at most a linear cofactor. -/
theorem height_two_cofactor {K : Type*} [Field K] (Q B : K[X])
    (nonzero : Q*B ≠ 0) (target : Q.natDegree = 2) (bound : (Q*B).natDegree ≤ 3) :
    B.natDegree ≤ 1 := by
  rw [natDegree_mul (left_ne_zero_of_mul nonzero) (right_ne_zero_of_mul nonzero), target] at bound
  omega

/-- Squaring a norm circle clears one denominator in the doubled Frobenius model. -/
theorem doubled_circle {R : Type*} [CommRing R] [CharP R 2]
    (x y b bbar d h₀ h₁ : R) (model : h₀ = x^2*h₁) :
    h₁*(x*(y+b)+(bbar*y+d))^2 = (y+b)^2*h₀+(bbar*y+d)^2*h₁ := by
  rw [CharTwo.add_sq, mul_pow, model]
  ring

/-- Translating all logarithms by the same scalar removes the common pole term. -/
theorem shift_pullback {R : Type*} [CommRing R] (q p h c a b : R)
    (row : c = q*(a+b-p)) (shift : (1-2*q)*h = q*p) :
    c+h = q*((a+h)+(b+h)) := by
  calc
    c+h = q*((a+h)+(b+h)) + ((1-2*q)*h-q*p) := by rw [row]; ring
    _ = _ := by rw [shift, sub_self, add_zero]

/-- Closing an affine recurrence around a cycle only requires the inverse of
one minus the cycle multiplier, also over a composite modulus. -/
theorem close_pullback_cycle {R : Type*} [CommRing R] (m u v b : R)
    (unit : u*(1-m) = 1) (cycle : v = m*v+b) : v = u*b := by
  have fixed : (1-m)*v = b := by
    calc
      (1-m)*v = v-m*v := by ring
      _ = b := by conv_lhs => lhs; rw [cycle]
                  ring
  calc
    v = (u*(1-m))*v := by rw [unit, one_mul]
    _ = u*b := by rw [mul_assoc, fixed]

end GF2Sparse.HermitianDescent
