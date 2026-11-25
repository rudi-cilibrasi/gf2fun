import GF2Sparse.DyadicTap
import GF2Sparse.SignedTriples

/-! Binary derivatives at the Gold and Kasami exponents and at 2^j+3
confine the roots in a product-one triple to explicit small fields. -/

namespace GF2Sparse

open Polynomial

section Derivatives

variable {K : Type*} [Field K] [CharP K 2]

private noncomputable abbrev F (j : ℕ) := iterateFrobenius K 2 j

/-- The Kasami identity after clearing its two possible denominators. -/
theorem kasami_derivative_product {j m : ℕ} (hm : m+2^j = 2^j*2^j+1) (x : K) :
    ((x+1)^m+x^m+1)*x^(2^j)*(x^(2^j)+1) =
      (x+x^(2^j))*(x^(2^j)+(x^(2^j))^(2^j)) := by
  have hp (v : K) : v^m*F j v = F j (F j v)*v := by
    change v^m*v^(2^j) = (v^(2^j))^(2^j)*v
    rw [← pow_add, ← pow_mul, hm, pow_succ]
  have h0 := hp x
  have h1 := hp (x+1)
  simp only [map_add, map_one] at h1
  change ((x+1)^m+x^m+1)*F j x*(F j x+1) = (x+F j x)*(F j x+F j (F j x))
  grind only

/-- Away from 0 and 1 the binary derivative of a Kasami monomial takes the
value 1 precisely in the base field of size 2^j. -/
theorem kasami_derivative_iff {j m : ℕ} (hm : m+2^j = 2^j*2^j+1) {x : K}
    (hx : x ≠ 0) (hx1 : x ≠ 1) : (x+1)^m = x^m+1 ↔ x^(2^j) = x := by
  have hp := kasami_derivative_product hm x
  have h0 : F j x ≠ 0 := (_root_.map_ne_zero (F j)).2 hx
  have h1 : F j x+1 ≠ 0 := by
    intro h
    exact hx1 ((F j).injective ((CharTwo.add_eq_zero.1 h).trans (map_one _).symm))
  change ((x+1)^m+x^m+1)*F j x*(F j x+1) = (x+F j x)*(F j x+F j (F j x)) at hp
  constructor
  · intro hd
    have hz : (x+F j x)*(F j x+F j (F j x)) = 0 := by rw [← hp, hd]; grind only
    rcases mul_eq_zero.1 hz with h | h
    · exact (CharTwo.add_eq_zero.1 h).symm
    · exact ((F j).injective (CharTwo.add_eq_zero.1 h)).symm
  · intro hd
    change F j x = x at hd
    have hz : ((x+1)^m+x^m+1)*F j x*(F j x+1) = 0 := by
      rw [hp, hd, CharTwo.add_self_eq_zero, zero_mul]
    have he := (mul_eq_zero.1 ((mul_eq_zero.1 hz).resolve_right h1)).resolve_right h0
    grind only

omit [CharP K 2] in
private theorem kasami_power_of_fixed {j m : ℕ} (hm : m+2^j = 2^j*2^j+1) {x : K}
    (hx : x ≠ 0) (hfix : x^(2^j) = x) : x^m = x := by
  apply mul_right_cancel₀ (pow_ne_zero (2^j) hx)
  rw [← pow_add, hm, pow_succ, pow_mul, hfix, hfix]

/-- The additional roots of the derivative for 2^j+3 are the primitive
cube roots of unity. -/
theorem dyadic_add_three_derivative (j : ℕ) (x : K) :
    (x+1)^(2^j+3)+x^(2^j+3)+1 = (x^(2^j)+x)*(x^2+x+1) := by
  rw [pow_add, pow_add, add_pow_expChar_pow, one_pow]
  grind only

end Derivatives

private abbrev K := AlgebraicClosure (ZMod 2)

private theorem triple_nontrivial {x y z : K} {n a : ℕ}
    (hx : aeval x (trinomial n a) = 0) (h : x*y*z = 1) : x ≠ 0 ∧ x ≠ 1 := by
  constructor
  · rintro rfl; simp at h
  · rintro rfl; simp [trinomial, CharTwo.add_self_eq_zero] at hx

/-- For n = 2^i + 2^b (2^(2j)-2^j+1), an integer gcd test excludes every
product-one triple, including repeated roots. -/
theorem kasami_no_root_triple {j m i b : ℕ} (hm : m+2^j = 2^j*2^j+1)
    (he : excludesTwistedPeriod j (i.dist b)) :
    NoRootTriple (trinomial (2^i+2^b*m) (2^i)) := by
  intro x y z hx hy hz h
  obtain ⟨hd,hp⟩ := (dyadic_tap_scaled_triple_iff x i b m).1 ⟨hx,y,z,hy,hz,h⟩
  obtain ⟨hx0,hx1⟩ := triple_nontrivial hx h
  have hfix := (kasami_derivative_iff hm hx0 hx1).1 hd
  rw [kasami_power_of_fixed hm hx0 hfix, add_pow_expChar_pow, one_pow] at hp
  exact he.no_shifted_product hx0 hx1 hfix hp

/-- At the Gold exponent the derivative already cuts out the degree-j field. -/
theorem gold_no_root_triple {j i b : ℕ} (he : excludesTwistedPeriod j (i.dist (b+1))) :
    NoRootTriple (trinomial (2^i+2^b*(2^j+1)) (2^i)) := by
  intro x y z hx hy hz h
  obtain ⟨hd,hp⟩ := (dyadic_tap_scaled_triple_iff x i b _).1 ⟨hx,y,z,hy,hz,h⟩
  obtain ⟨hx0,hx1⟩ := triple_nontrivial hx h
  simp only [pow_succ, add_pow_expChar_pow, one_pow] at hd
  have hfix : x^(2^j) = x := by grind only
  have hxpow : x^(2^j+1) = x^(2^1) := by rw [pow_succ, hfix]; ring
  rw [hxpow, add_pow_expChar_pow, one_pow, ← pow_mul, ← pow_add, Nat.add_comm 1 b] at hp
  exact he.no_shifted_product hx0 hx1 hfix hp

/-- At exponent 2^j+3 the shifted products in the degree-j field and in
the degree-two field control all product-one triples. -/
theorem dyadic_add_three_no_root_triple {j i b : ℕ}
    (he : excludesTwistedPeriod j (i.dist (b+2)))
    (hc : excludesTwistedPeriod 2 (i.dist (j+b))) :
    NoRootTriple (trinomial (2^i+2^b*(2^j+3)) (2^i)) := by
  intro x y z hx hy hz h
  obtain ⟨hd,hp⟩ := (dyadic_tap_scaled_triple_iff x i b _).1 ⟨hx,y,z,hy,hz,h⟩
  obtain ⟨hx0,hx1⟩ := triple_nontrivial hx h
  have hzprod := dyadic_add_three_derivative j x
  rw [hd] at hzprod
  have hz' : (x^(2^j)+x)*(x^2+x+1) = 0 := by rw [← hzprod]; grind only
  rcases mul_eq_zero.1 hz' with hf | hw
  · have hfix := CharTwo.add_eq_zero.1 hf
    have hxpow : x^(2^j+3) = x^(2^2) := by rw [pow_add, hfix]; ring
    rw [hxpow, add_pow_expChar_pow, one_pow, ← pow_mul, ← pow_add, Nat.add_comm 2 b] at hp
    exact he.no_shifted_product hx0 hx1 hfix hp
  · have hx3 : x^3 = 1 := by linear_combination (x-1)*hw
    have hfix : x^(2^2) = x := by change x^(3+1)=x; rw [pow_succ, hx3, one_mul]
    rw [pow_add, hx3, mul_one, add_pow_expChar_pow, one_pow, ← pow_mul, ← pow_add] at hp
    exact hc.no_shifted_product hx0 hx1 hfix hp

/-- Every Frobenius shift is excluded when the field degree is coprime to six. -/
theorem excludesTwistedPeriod_of_coprime_six {j : ℕ} (hj : j.Coprime 6) (h : ℕ) :
    excludesTwistedPeriod j h := by
  have h3 : Nat.Coprime 3 j := (hj.of_dvd_right (by decide : 3 ∣ 6)).symm
  have h2 : j.Coprime 2 := hj.of_dvd_right (by decide)
  exact ⟨by rw [h3.gcd_mul_left_cancel_right]; exact Nat.gcd_dvd_right j h,
    h2.of_dvd_left (Nat.gcd_dvd_left j h)⟩

/-- Both free dyadic shifts are allowed for every Kasami parameter j coprime to six. -/
theorem kasami_coprime_six_no_root_triple {j m : ℕ} (hj : j.Coprime 6)
    (hm : m+2^j = 2^j*2^j+1) (i b : ℕ) :
    NoRootTriple (trinomial (2^i+2^b*m) (2^i)) :=
  kasami_no_root_triple hm (excludesTwistedPeriod_of_coprime_six hj _)

end GF2Sparse
