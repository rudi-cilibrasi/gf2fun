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

/-- Removing a common Frobenius power from the exponent difference leaves
one binary derivative and one product equation. -/
theorem dyadic_tap_scaled_triple_iff (x : K) (i b m : ℕ) :
    let f := trinomial (2^i+2^b*m) (2^i)
    (aeval x f = 0 ∧ ∃ y z : K, aeval y f = 0 ∧ aeval z f = 0 ∧ x*y*z = 1) ↔
      (x+1)^m = x^m+1 ∧ x^(2^i)*(x^m+1)^(2^b) = 1 := by
  dsimp only
  have eval_iff := tap_root_iff x i (2^b*m)
  have powers (v : K) : v^(2^b*m) = (v^m)^(2^b) := by rw [Nat.mul_comm, pow_mul]
  have shift (v : K) : (v+1)^(2^b) = v^(2^b)+1 := by rw [add_pow_expChar_pow, one_pow]
  rw [powers, ← shift] at eval_iff
  have diff : (x+1)^(2^b*m) = x^(2^b*m)+1 ↔ (x+1)^m = x^m+1 := by
    rw [powers, powers, ← shift]
    exact (iterateFrobenius_inj K 2 b).eq_iff
  exact ⟨fun ⟨hx,h⟩ => ⟨diff.1 ((dyadic_tap_triple_iff hx).1 h), eval_iff.1 hx⟩,
    fun ⟨hd,hv⟩ => ⟨eval_iff.2 hv,(dyadic_tap_triple_iff (eval_iff.2 hv)).2 (diff.2 hd)⟩⟩

/-- An irreducible dyadic-tap trinomial passes the three-root test whenever
the exponent difference has an odd factor greater than one. -/
theorem irreducible_dyadic_tap_no_root_triple {i b m : ℕ} (hm : Odd m) (hm1 : 1 < m)
    (hf : Irreducible (trinomial (2^i+2^b*m) (2^i))) :
    NoRootTriple (trinomial (2^i+2^b*m) (2^i)) := by
  intro x y z hx hy hz h
  have hd := ((dyadic_tap_scaled_triple_iff x i b m).1 ⟨hx,y,z,hy,hz,h⟩).1
  let d : BinaryPoly := (X+1)^m+(X^m+1)
  have heval : aeval x d = 0 := by
    simpa only [d, map_add, map_pow, aeval_X, map_one, CharTwo.add_eq_zero] using hd
  have hdvd := minpoly.dvd (ZMod 2) x heval
  rw [← minpoly.eq_of_irreducible_of_monic hf hx (binary_monic hf.ne_zero)] at hdvd
  have hcoeff : d.coeff 1 = 1 := by
    simp [d, coeff_X_add_one_pow, coeff_X_pow, hm1.ne, coeff_one, hm.natCast_zmod_two]
  have hne : d ≠ 0 := by rintro he; simp [he] at hcoeff
  have hdeg : d.natDegree ≤ m := by
    apply natDegree_add_le_of_degree_le
    · have hc : (X+1 : BinaryPoly).natDegree = 1 := by
        simpa only [C_1] using natDegree_X_add_C (1 : ZMod 2)
      exact natDegree_pow_le.trans (by rw [hc, mul_one])
    · exact natDegree_add_le_of_degree_le (by simp) (by simp)
  have hmle : m ≤ 2^b*m := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have hlt : 2^i < 2^i+2^b*m := Nat.lt_add_of_pos_right (by positivity)
  have hle := (natDegree_le_of_dvd hdvd hne).trans hdeg
  rw [trinomial_degree (Nat.two_pow_pos _) hlt] at hle
  have := Nat.two_pow_pos i
  omega

end GF2Sparse
