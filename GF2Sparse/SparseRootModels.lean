import GF2Sparse.Degree1229
import GF2Sparse.PackedOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Ring

/-! Changes of coordinate for five-term binary equations of degree 1229. -/

namespace GF2Sparse.SparseRootModels

variable {K : Type*} [Field K] [CharP K 2]

/-- A quadratic value and a linear ratio in the coordinate a = 1/(1+x). -/
theorem quadratic_values {x y : K} (hx : 1 + x ≠ 0)
    (h : y * (1 + x)^2 = 1 + x + x^2) :
    let a := (1 + x)⁻¹
    a^2 + a + 1 = y ∧ (a + 1) / a = x := by
  dsimp only
  have hquad : ((1 + x)⁻¹)^2 - (1 + x)⁻¹ + 1 = y := by
    field_simp [hx]
    linear_combination -h
  have hratio : (1 - (1 + x)⁻¹) / (1 + x)⁻¹ = x := by
    field_simp [hx]
    ring
  exact ⟨by simpa only [CharTwo.sub_eq_add] using hquad,
    by simpa only [CharTwo.sub_eq_add, add_comm (1 : K) ((1 + x)⁻¹)] using hratio⟩

/-- The degree-1229 pentanomial supplies both powers and the nonzero denominator. -/
theorem sparse_quadratic_values {r : K}
    (hf : r^1229 + r^1066 + r^533 + r^163 + 1 = 0) :
    let a := (1 + r^533)⁻¹
    a^2 + a + 1 = r^163 ∧ (a + 1) / a = r^533 := by
  have h : r^163 * (1 + r^533)^2 = 1 + r^533 + (r^533)^2 := by
    rw [CharTwo.add_sq, one_pow]
    apply CharTwo.add_eq_zero.mp
    linear_combination hf
  apply quadratic_values _ h
  intro hx
  have hr : r^533 = 1 := (CharTwo.add_eq_zero.mp hx).symm
  rw [hx, hr] at h
  simp at h

omit [CharP K 2] in

/-- The two powers recover the original root by Bézout's identity. -/
theorem recover_root {r : K} (hr : r ≠ 0) : (r^533)^63 / (r^163)^206 = r := by
  apply (div_eq_iff (pow_ne_zero _ (pow_ne_zero _ hr))).2
  simp only [← pow_mul]
  change r^(33578+1) = r*r^33578
  rw [pow_succ, mul_comm]

omit [CharP K 2] in
/-- Substituting the fifth power in the second pentanomial gives a quadratic
equation in z over its 256th Frobenius power. -/
theorem quadratic_frobenius (z : K) :
    (z^5)^1229 + (z^5)^922 + (z^5)^461 + (z^5)^256 + 1 =
      (z^256)^18*z^2 + ((z^256)^9 + (z^256)^24)*z + 1 + (z^256)^5 := by
  ring

omit [CharP K 2] in
/-- The five terms of the minimum-sum model have bidegree (15,3). -/
theorem cubic_frobenius (z : K) :
    (z^5)^1229 + (z^5)^822 + (z^5)^410 + (z^5)^3 + 1 =
      z*(z^2048)^3 + z^14*(z^2048)^2 + z^2*(z^2048) + z^15 + 1 := by
  ring

omit [CharP K 2] in
/-- A monomial shift of seven places the five terms in a box of bidegree (8,12). -/
theorem balanced_frobenius (z : K) :
    z^7*((z^5)^1229 + (z^5)^818 + (z^5)^614 + (z^5)^101 + 1) =
      z^8*(z^512)^12 + z*(z^512)^8 + z^5*(z^512)^6 + z^512 + z^7 := by
  ring

/-- A rational parameter expresses the two powers on a pentanomial curve as a cubic
and a quadratic ratio. -/
theorem rational_cubic_coordinate {b t : K} (hd : t^2+t+1 ≠ 0)
    (curve : b^2+(t^3+1)*b+t+1 = 0) :
    let w := (b+t)/(t^2+t+1)
    w^2*(w+1) = b ∧ t*w = w^2+w+1 := by
  let w := (b+t)/(t^2+t+1)
  change w^2*(w+1) = b ∧ t*w = w^2+w+1
  have lin : (t^2+t+1)*w = b+t := by
    dsimp only [w]
    rw [mul_comm, div_mul_cancel₀ _ hd]
  have quadratic : w^2+(t+1)*w+1 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right (pow_ne_zero 2 hd)
    calc
      _ * (t^2+t+1)^2 = ((t^2+t+1)*w)^2 + (t+1)*((t^2+t+1)*w)*(t^2+t+1) + (t^2+t+1)^2 := by ring
      _ = 0 := by
        rw [lin]
        linear_combination (norm := (try ring_nf; reduce_mod_char!)) curve
  constructor
  · linear_combination (norm := (try ring_nf; reduce_mod_char!)) (w+t)*quadratic + lin
  · linear_combination (norm := (try ring_nf; reduce_mod_char!)) -quadratic

/-- The only quadratic factors needed in this sparse-root equation are the linear
translate and the third cyclotomic polynomial. -/
theorem sparse_quadratic_product {r : K}
    (hf : r^1229 + r^1101 + r^4 + r^2 + 1 = 0) :
    r^1101 * (1+r)^128 = (1+r+r^2)^2 := by
  have hfrob : (1+r)^128 = 1+r^128 := by
    simpa only [one_pow] using add_pow_expChar_pow (1 : K) r 2 7
  rw [hfrob, CharTwo.add_sq, CharTwo.add_sq]
  apply CharTwo.add_eq_zero.mp
  linear_combination (norm := ring_nf) hf

/-- Three products of translates obtained from one five-term equation. -/
theorem translate_products {x y : K} (h : 1+x+y+x*y+x^2*y = 0) :
    (1+x)*(1+y) = x^2*y ∧ (1+x)*(1+x*y) = y ∧
      1+y = x^2*(1+x*y) ∧ y*(1+x^3) = (1+x)^2 := by
  have h₁ : (1+x)*(1+y) = x^2*y := by
    apply CharTwo.add_eq_zero.mp
    linear_combination h
  have h₂ : (1+x)*(1+x*y) = y := by
    apply CharTwo.add_eq_zero.mp
    linear_combination h
  refine ⟨h₁, h₂, ?_, ?_⟩
  · apply CharTwo.add_eq_zero.mp
    linear_combination (norm := (try ring_nf; reduce_mod_char!)) (1+x)*h
  · apply CharTwo.add_eq_zero.mp
    linear_combination (norm := (try ring_nf; reduce_mod_char!)) (1+x)*h

open Polynomial PackedSquare
open GF2Sparse.Degree1229 (knownPart cofactor)

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

noncomputable def pentanomial (a b c : ℕ) : BinaryPoly :=
  X^1229 + (X^c + (X^b + (X^a + 1)))

private def primes : List ℕ :=
  [36871, 46703, 10543179280661916121033, 9536289355314392579996071515160583098298616686033085857]

private def certified (js : List ℕ) (fuel : ℕ) : Bool :=
  let stages := stagesFor 11
  let e := 2^1229-1
  (xorShifts js 1).log2 == 1229 && powerBits 1229 1229 fuel stages js (e.log2+1) e == some 1 &&
    nontrivialPower 1229 fuel stages js knownPart &&
    primes.all (fun p => nontrivialPower 1229 fuel stages js (cofactor*(knownPart/p)))

private theorem basis : checkBasis 1229 (stagesFor 11) = true := by decide +kernel

private theorem of_certified (a b c fuel : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : certified [1229,c,b,a,0] fuel = true) :
    Irreducible (pentanomial a b c) ∧
      ∃ t : ℕ, 1 < t ∧ t ∣ cofactor ∧ orderOf (AdjoinRoot.root (pentanomial a b c)) = knownPart*t := by
  let js := [1229,c,b,a,0]
  let mask := xorShifts js 1
  have heq : decode mask = pentanomial a b c := by
    simp only [mask, js, xorShifts, decode_xor, decode_shift_by, decode_one, decode_zero,
      pow_zero, mul_one, add_zero, pentanomial]
  change certified js fuel = true at h
  simp only [certified, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hd,hfull⟩,hextra⟩,hp⟩ := h
  have hdeg : (decode mask).natDegree = 1229 := (natDegree_decode _).trans hd
  have full : AdjoinRoot.root (decode mask)^(2^1229-1) = 1 := by
    have he := powerBits_sound basis (show xorShifts js 1 = mask from rfl) Nat.lt_log2_self hfull
    simpa using he.symm
  have proper {e : ℕ} (ht : nontrivialPower 1229 fuel (stagesFor 11) js e = true) :
      AdjoinRoot.root (decode mask)^e ≠ 1 :=
    nontrivialPower_sound basis rfl hd (by decide) ht
  rw [← heq]
  constructor
  · apply irreducible_of_prime_degree_power (f := decode mask) (by rw [hdeg]; norm_num)
    · intro z
      rw [heq]
      have hz : z = 0 ∨ z = 1 := by
        fin_cases z
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hz with rfl | rfl
      · simp [pentanomial, zero_pow ha, zero_pow hb, zero_pow hc]
      · simp only [pentanomial, eval_add, eval_pow, eval_X, eval_one, one_pow]
        decide
    · simpa only [hdeg] using full
  · exact Degree1229.order_split_of_powers _ full (proper hextra) (fun p hm => proper (hp p hm))

/-- Irreducibility and the four known prime projections for the quadratic-value model. -/
theorem quadratic_value_order :
    Irreducible (pentanomial 163 533 1066) ∧
      ∃ t : ℕ, 1 < t ∧ t ∣ cofactor ∧
        orderOf (AdjoinRoot.root (pentanomial 163 533 1066)) = knownPart*t :=
  of_certified 163 533 1066 10 (by decide) (by decide) (by decide) (by decide +kernel)

/-- Irreducibility and the same order projections for the quadratic Frobenius model. -/
theorem frobenius_model_order :
    Irreducible (pentanomial 256 461 922) ∧
      ∃ t : ℕ, 1 < t ∧ t ∣ cofactor ∧
        orderOf (AdjoinRoot.root (pentanomial 256 461 922)) = knownPart*t :=
  of_certified 256 461 922 6 (by decide) (by decide) (by decide) (by decide +kernel)

/-- Irreducibility and the four known prime projections for the second rational cubic model. -/
theorem rational_cubic_order :
    Irreducible (pentanomial 29 58 400) ∧
      ∃ t : ℕ, 1 < t ∧ t ∣ cofactor ∧
        orderOf (AdjoinRoot.root (pentanomial 29 58 400)) = knownPart*t :=
  of_certified 29 58 400 4 (by decide) (by decide) (by decide) (by decide +kernel)

/-- The sparse quadratic product passes all four known prime tests and the cofactor test. -/
theorem quadratic_product_order :
    Irreducible (pentanomial 2 4 1101) ∧
      ∃ t : ℕ, 1 < t ∧ t ∣ cofactor ∧
        orderOf (AdjoinRoot.root (pentanomial 2 4 1101)) = knownPart*t :=
  of_certified 2 4 1101 12 (by decide) (by decide) (by decide) (by decide +kernel)

/-- The three-translate model passes the same order tests. -/
theorem translate_product_order :
    Irreducible (pentanomial 310 609 919) ∧
      ∃ t : ℕ, 1 < t ∧ t ∣ cofactor ∧
        orderOf (AdjoinRoot.root (pentanomial 310 609 919)) = knownPart*t :=
  of_certified 310 609 919 6 (by decide) (by decide) (by decide) (by decide +kernel)

/-- The cubic model has all four known prime factors and a nontrivial cofactor part. -/
theorem cubic_frobenius_order :
    Irreducible (pentanomial 3 410 822) ∧
      ∃ t : ℕ, 1 < t ∧ t ∣ cofactor ∧
        orderOf (AdjoinRoot.root (pentanomial 3 410 822)) = knownPart*t :=
  of_certified 3 410 822 5 (by decide) (by decide) (by decide) (by decide +kernel)

/-- The (8,12) example also passes the four known prime and cofactor tests. -/
theorem balanced_frobenius_order :
    Irreducible (pentanomial 101 614 818) ∧
      ∃ t : ℕ, 1 < t ∧ t ∣ cofactor ∧
        orderOf (AdjoinRoot.root (pentanomial 101 614 818)) = knownPart*t :=
  of_certified 101 614 818 5 (by decide) (by decide) (by decide) (by decide +kernel)

end GF2Sparse.SparseRootModels
