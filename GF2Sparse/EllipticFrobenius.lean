import GF2Sparse.Table
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Ring

/-! A single elliptic curve gives Frobenius models for five-term polynomials
of degree 9t+5 whenever 15t+8 is a power of two. -/

namespace GF2Sparse.EllipticFrobenius

variable {K : Type*} [Field K] [CharP K 2]

/-- Clear the torus coordinates u = r^t and v = r^(2t+1) in the pentanomial. -/
theorem curve_equation (r : K) (t : ℕ)
    (hf : r^(9*t+5) + r^(6*t+3) + r^(5*t+3) + r^t + 1 = 0) :
    let u := r^t
    let v := r^(2*t+1)
    u^2 + (v^3+1)*u + v^3*(v+1)^2 = 0 := by
  dsimp only
  simp only [Nat.mul_comm 9 t, Nat.mul_comm 6 t, Nat.mul_comm 5 t,
    Nat.mul_comm 2 t, pow_add, pow_mul, pow_one] at *
  linear_combination (norm := (try ring_nf; reduce_mod_char!)) (r^t)*hf

/-- The quadratic torus equation reduces to the Artin–Schreier elliptic equation. -/
theorem artin_schreier_factor (v z : K) :
    let u := (v^3+1)*z + v + 1
    u^2 + (v^3+1)*u + v^3*(v+1)^2 =
      (v+1)^2 * (v^2+v+1) * ((v^2+v+1)*(z^2+z) + v) := by
  dsimp only
  ring_nf
  reduce_mod_char!

omit [CharP K 2] in
/-- Both coordinate functions specialize to the claimed powers without any order hypothesis. -/
theorem coordinate_powers {r : K} (hr : r ≠ 0) (t : ℕ) :
    let u := r^t
    let v := r^(2*t+1)
    v/u^2 = r ∧ v^8/u = r^(15*t+8) := by
  dsimp only
  constructor
  · apply (div_eq_iff (pow_ne_zero _ (pow_ne_zero _ hr))).2
    rw [← pow_mul, mul_comm r, ← pow_succ]
    congr 1
    omega
  · apply (div_eq_iff (pow_ne_zero _ hr)).2
    rw [← pow_add, ← pow_mul]
    congr 1
    omega

private def small (n : ℕ) (h : n.Prime := by norm_num1) : ProvenPrime := ⟨n, h⟩
private def p1861 := lucasPrime 1861 2 [small 2, small 2, small 3, small 5, small 31] (by decide +kernel)
private def p18199 := lucasPrime 18199 11 [small 2, small 3, small 3, small 3, small 337] (by decide +kernel)
private def p1310329 :=
  lucasPrime 1310329 7 [small 2, small 2, small 2, small 3, small 3, p18199] (by decide +kernel)
private def p13528921548413 :=
  lucasPrime 13528921548413 2 [small 2, small 2, small 19, small 73, p1861, p1310329] (by decide +kernel)
private def p581283643249112959 := lucasPrime 581283643249112959 6
  [small 2, small 3, small 3, small 7, small 11, small 31, p13528921548413] (by decide +kernel)
private def factors77 := [small 23, small 89, small 127, p581283643249112959]

/-- The first member of the dyadic sequence is primitive. -/
theorem primitive_77 : Primitive (productCandidate 77 8 43) := by
  rw [← decode_productMask]
  have h : check 77 (productMask 77 8 43) (factors77.map Subtype.val) = true := by decide +kernel
  apply (check_sound ?_ h).2.2
  intro p hp
  obtain ⟨v, _, rfl⟩ := List.mem_map.1 hp
  exact v.property

end GF2Sparse.EllipticFrobenius
