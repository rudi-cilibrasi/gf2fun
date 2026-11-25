import GF2Sparse.TripleRoots

/-! Product-one triples for trinomials whose inner exponent is a power of two. -/

namespace GF2Sparse

open Polynomial

variable {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]

private theorem tap_root_iff (x : K) (i m : ℕ) :
    aeval x (trinomial (2^i+m) (2^i)) = 0 ↔ x^(2^i) * (x^m+1) = 1 := by
  simp only [trinomial, map_add, map_pow, aeval_X, map_one, pow_add, map_mul, mul_add, mul_one,
    CharTwo.add_eq_zero]
  grind only

private theorem tap_orbit_root_iff {x y : K} (i m : ℕ) (ho : y*(x+1) = 1) :
    aeval y (trinomial (2^i+m) (2^i)) = 0 ↔ x^(2^i)*(x+1)^m = 1 := by
  have hd : x+1 ≠ 0 := by rintro h; simp [h] at ho
  have hp (j : ℕ) : y^j*(x+1)^j = 1 := by rw [← mul_pow, ho, one_pow]
  have hterm : (y^(2^i) + 1)*(x+1)^(2^i+m) = x^(2^i)*(x+1)^m := by
    rw [pow_add, ← mul_assoc, add_mul, hp, one_mul, add_pow_expChar_pow, one_pow,
      add_comm (x^(2^i)) 1, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  simp only [trinomial, map_add, map_pow, aeval_X, map_one, CharTwo.add_eq_zero]
  rw [← mul_left_inj' (pow_ne_zero (2^i+m) hd), hp, hterm, eq_comm]

/-- A root x belongs to a product-one triple, allowing repetitions, exactly
when the monomial of degree m = n-2^i has binary derivative 1 at x. -/
theorem dyadic_tap_triple_iff {x : K} {i m : ℕ}
    (hx : aeval x (trinomial (2^i+m) (2^i)) = 0) :
    (∃ y z : K, aeval y (trinomial (2^i+m) (2^i)) = 0 ∧
      aeval z (trinomial (2^i+m) (2^i)) = 0 ∧ x*y*z = 1) ↔ (x+1)^m = x^m+1 := by
  let a := 2^i
  let n := a+m
  have root_eq (v : K) :
      aeval v (trinomial n a) = 0 ↔ v^n = v^a+1 := by
    simp only [trinomial, map_add, map_pow, aeval_X, map_one, CharTwo.add_eq_zero]
  have hxv := (tap_root_iff x i m).1 hx
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxv
  have hx1 : x+1 ≠ 0 := by
    intro hz
    have he := CharTwo.add_eq_zero.1 hz
    simp [he, CharTwo.add_self_eq_zero] at hxv
  constructor
  · rintro ⟨y,z,hy,hz,h⟩
    have hp (k : ℕ) : x^k*y^k*z^k = 1 := by rw [← mul_pow, ← mul_pow, h, one_pow]
    have ht := hp n
    rw [(root_eq _).1 hx, (root_eq _).1 hy, (root_eq _).1 hz] at ht
    have lift_pair (v : K) (hv : v^a*(x^a+1)=1) : v*(x+1)=1 := by
      apply iterateFrobenius_inj K 2 i
      simpa [iterateFrobenius_def, a, mul_pow, add_pow_expChar_pow] using hv
    apply mul_left_cancel₀ (pow_ne_zero (2^i) hx0)
    rcases triple_translate_orbit (hp a) ht with ho | ho
    · exact ((tap_orbit_root_iff i m (lift_pair _ ho)).1 hy).trans hxv.symm
    · exact ((tap_orbit_root_iff i m (lift_pair _ ho)).1 hz).trans hxv.symm
  · intro hd
    let y := (x+1)⁻¹
    let z := (x+1)/x
    have hyx : y*(x+1) = 1 := inv_mul_cancel₀ hx1
    have hy := (tap_orbit_root_iff i m hyx).2 (hd ▸ hxv)
    have hp : x*y*z = 1 := by dsimp [y,z]; field_simp
    have ht : (x+1)*(y+1)*(z+1) = 1 := by
      dsimp [y,z]
      field_simp
      grind only
    have hp' := congrArg (· ^ n) hp
    have ht' := congrArg (· ^ a) ht
    simp only [mul_pow, one_pow] at hp'
    simp only [a, mul_pow, add_pow_expChar_pow, one_pow] at ht'
    refine ⟨y,z,hy,(root_eq _).2 ?_,hp⟩
    have hxy : y ≠ 0 := by rintro he; simp [he] at hp
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero n hx0) (pow_ne_zero n hxy))
    rw [hp', (root_eq _).1 hx, (root_eq _).1 hy]
    exact ht'.symm

end GF2Sparse
