import GF2Sparse.Table
import GF2Sparse.Roots
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Product pentanomials with no pair of mutually inverse roots. -/

namespace GF2Sparse

open Polynomial

private theorem eval_product_root {K : Type*} [Field K] [Algebra (ZMod 2) K] [CharP K 2]
    {n u v : ℕ} {x : K} (hz : aeval x (productCandidate n u v) = 0) :
    x ^ n = (x ^ u + 1) * (x ^ v + 1) := by
  apply CharTwo.add_eq_zero.1
  simpa only [productCandidate, map_add, map_mul, map_pow, aeval_X, map_one] using hz

/-- On a product-pentanomial root, reciprocity is exactly a power condition. -/
theorem product_inverse_root_iff {K : Type*} [Field K] [Algebra (ZMod 2) K] [CharP K 2]
    {n u v g : ℕ} (hgap : n + n = (u + v) + g)
    {x : K} (hx : x ≠ 0) (hz : aeval x (productCandidate n u v) = 0) :
    aeval x⁻¹ (productCandidate n u v) = 0 ↔ x ^ g = 1 := by
  have h := eval_product_root hz
  have hi : aeval x⁻¹ (productCandidate n u v) = 0 ↔
      x ^ u * x ^ v = x ^ n * ((x ^ u + 1) * (x ^ v + 1)) := by
    simp only [productCandidate, map_add, map_mul, map_pow, aeval_X, map_one,
      CharTwo.add_eq_zero, inv_pow]
    constructor <;> intro hi
    · field_simp [hx] at hi
      linear_combination hi
    · field_simp [hx]
      linear_combination hi
  rw [hi, ← h, ← pow_add x u v, ← pow_add x n n, hgap, pow_add x (u+v) g]
  constructor
  · intro he
    exact (mul_left_cancel₀ (pow_ne_zero (u+v) hx) (he.symm.trans (mul_one _).symm))
  · intro he
    rw [he, mul_one]

/-- Reciprocal pairs on the slice n = v + (s+2)w give roots of a fixed polynomial. -/
noncomputable def productSliceAux (s : ℕ) : BinaryPoly :=
  X ^ (s+2) + (X ^ s + 1) * (1 + X ^ (s+4))

theorem product_slice_aux_of_inverse_root {K : Type*} [Field K]
    [Algebra (ZMod 2) K] [CharP K 2] {n s v w : ℕ} (hn : n = v + (s+2)*w)
    {x : K} (hx : x ≠ 0) (hz : aeval x (productCandidate n (s*w) v) = 0)
    (hi : aeval x⁻¹ (productCandidate n (s*w) v) = 0) :
    aeval (x ^ w) (productSliceAux s) = 0 := by
  have hd : n+n = (s*w+v) + (n+2*w) := by rw [hn]; ring
  have hc := (product_inverse_root_iff hd hx hz).mp hi
  let t := x ^ w
  have hc₁ : x ^ n * t ^ 2 = 1 := by
    simpa only [t, ← pow_mul, Nat.mul_comm w 2, ← pow_add] using hc
  have hc₂ : x ^ v * t ^ (s+4) = 1 := by
    change x ^ v * (x ^ w) ^ (s+4) = 1
    rw [← pow_mul, ← pow_add, show v+w*(s+4) = n+2*w by rw [hn]; ring]
    exact hc
  have hr : x ^ n = (t ^ s + 1) * (x ^ v + 1) := by
    simpa only [t, ← pow_mul, Nat.mul_comm w s] using eval_product_root hz
  have hshift : t ^ (s+4) = t ^ 2 * t ^ (s+2) := by
    rw [← pow_add, show 2+(s+2) = s+4 by omega]
  have he : t ^ (s+2) = (t ^ s + 1) * (1 + t ^ (s+4)) := calc
    _ = (x ^ n * t ^ 2) * t ^ (s+2) := by rw [hc₁, one_mul]
    _ = x ^ n * t ^ (s+4) := by rw [hshift, mul_assoc]
    _ = (t ^ s + 1) * (x ^ v * t ^ (s+4) + t ^ (s+4)) := by rw [hr]; ring
    _ = _ := by rw [hc₂]
  simpa only [productSliceAux, map_add, map_mul, map_pow, aeval_X, map_one] using
    (CharTwo.add_eq_zero.2 he)

theorem product_slice_aux_nonzero_of_period {K : Type*} [Field K]
    [Algebra (ZMod 2) K] [CharP K 2] {s : ℕ} {t : K} (ht : t ≠ 0) (h : t ^ s = 1) :
    aeval t (productSliceAux s) ≠ 0 := by
  simp only [productSliceAux, map_add, map_mul, map_pow, aeval_X, map_one, h,
    CharTwo.add_self_eq_zero, zero_mul, add_zero]
  exact pow_ne_zero _ ht

/-- A root and its inverse force x^(2n)=x^(u+v). If the gap is a
dyadic multiple of a divisor of u, no such pair can occur. -/
theorem product_no_inverse_root {K : Type*} [Field K] [Algebra (ZMod 2) K] [CharP K 2]
    {n u v s w : ℕ} (hgap : n + n = (u + v) + w * 2 ^ s) (hd : w ∣ u)
    {x : K} (hx : x ≠ 0) (hz : aeval x (productCandidate n u v) = 0) :
    aeval x⁻¹ (productCandidate n u v) ≠ 0 := by
  intro hi
  have h := eval_product_root hz
  have he' := (product_inverse_root_iff hgap hx hz).mp hi
  rw [pow_mul] at he'
  have hw : x ^ w = 1 := by
    apply (iterateFrobenius_inj K 2 s)
    simpa only [iterateFrobenius_def, one_pow] using he'
  obtain ⟨j, rfl⟩ := hd
  rw [pow_mul, hw, one_pow, CharTwo.add_self_eq_zero, zero_mul] at h
  exact pow_ne_zero n hx h

section Squarefreeness

variable {K : Type*} [Field K] [Algebra (ZMod 2) K]

noncomputable def reciprocalSieveAux (P L : ℕ) : BinaryPoly := X ^ (P + L) + X ^ (2 * L) + 1

private theorem eval_product (x : K) (n u v : ℕ) :
    aeval x (productCandidate n u v) = x ^ n + (x ^ u + 1) * (x ^ v + 1) := by
  simp [productCandidate]

private theorem eval_aux (x : K) (P L : ℕ) :
    aeval x (reciprocalSieveAux P L) = x ^ P * x ^ L + (x ^ L) ^ 2 + 1 := by
  simp [reciprocalSieveAux, pow_add, pow_mul']

variable [CharP K 2]

private theorem log_derivative_product (x : K) {n u v : ℕ} (hn : 0 < n) (hu : Odd u) (hv : Odd v) :
    x * aeval x (productCandidate n u v).derivative =
      (n : K) * x ^ n + x ^ u + x ^ v := by
  have hshift (k : ℕ) (hk : 0 < k) : x * x ^ (k - 1) = x ^ k := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  calc
    _ = (n : K) * (x * x ^ (n - 1)) + (x * x ^ (u - 1)) * (x ^ v + 1) +
          (x ^ u + 1) * (x * x ^ (v - 1)) := by
      simp only [productCandidate, derivative_mul, derivative_X_pow, derivative_one,
        add_zero, hu.natCast_zmod_two, hv.natCast_zmod_two, one_mul, map_add, map_mul, map_pow,
        aeval_X, map_natCast, map_one]
      ring
    _ = _ := by
      rw [hshift n hn, hshift u hu.pos, hshift v hv.pos]
      linear_combination CharTwo.add_self_eq_zero (x ^ u * x ^ v)

omit [Algebra (ZMod 2) K] in
private theorem sq_one {z : K} (h : z ^ 2 = 1) : z = 1 := by
  apply frobenius_inj K 2
  simpa only [frobenius_def, one_pow] using h

private theorem repeat_even {n u v : ℕ} (hn : Even n) (hn0 : 0 < n) (hu : Odd u) (hv : Odd v)
    {x : K} (hx : x ≠ 0) :
    aeval x (productCandidate n u v).derivative = 0 ↔ x ^ u = x ^ v := by
  have h := log_derivative_product x hn0 hu hv
  rw [natCast_eq_zero_of_even_of_two_eq_zero hn (CharP.cast_eq_zero K 2), zero_mul, zero_add] at h
  rw [← CharTwo.add_eq_zero (a := x ^ u) (b := x ^ v), ← h, mul_eq_zero]
  simp [hx]

private theorem repeat_odd {n u v : ℕ} (hn : Odd n) (hu : Odd u) (hv : Odd v)
    {x : K} (hx : x ≠ 0) (hz : aeval x (productCandidate n u v) = 0) :
    aeval x (productCandidate n u v).derivative = 0 ↔ x ^ (u + v) = 1 := by
  have h := log_derivative_product x hn.pos hu hv
  rw [natCast_eq_one_of_odd_of_two_eq_zero hn (CharP.cast_eq_zero K 2), one_mul,
    eval_product_root hz] at h
  have he : x * aeval x (productCandidate n u v).derivative = x ^ (u + v) + 1 := by
    rw [h, pow_add]
    linear_combination (CharTwo.add_self_eq_zero (x ^ u)) + (CharTwo.add_self_eq_zero (x ^ v))
  rw [← CharTwo.add_eq_zero (a := x ^ (u + v)) (b := 1), ← he, mul_eq_zero]
  simp [hx]

private theorem common_root_even {n v P L w t : ℕ}
    (hn : Even n) (hn0 : 0 < n) (hu : Odd (w * L)) (hv : Odd v)
    (hdeg : n = t + w * (P + L)) (hvform : v = w * L + t * 2) {x : K} (hx : x ≠ 0) :
    let F := productCandidate n (w * L) v
    aeval x F = 0 ∧ aeval x F.derivative = 0 ↔
      x ^ t = 1 ∧ aeval (x ^ w) (reciprocalSieveAux P L) = 0 := by
  dsimp only
  have hfix : x ^ (w * L) = x ^ v ↔ x ^ t = 1 := by
    rw [hvform, pow_add, pow_mul x t 2]
    constructor
    · intro h
      exact sq_one (mul_left_cancel₀ (pow_ne_zero _ hx) (h.symm.trans (mul_one _).symm))
    · intro ht
      rw [ht, one_pow, mul_one]
  have hder := (repeat_even hn hn0 hu hv hx).trans hfix
  have hval (ht : x ^ t = 1) :
      aeval x (productCandidate n (w * L) v) = aeval (x ^ w) (reciprocalSieveAux P L) := by
    have hxn : x ^ n = (x ^ w) ^ P * (x ^ w) ^ L := by
      rw [hdeg, pow_add, ht, one_mul, pow_mul, pow_add]
    rw [eval_product, eval_aux, hxn, ← hfix.2 ht, pow_mul, ← sq, CharTwo.add_sq, one_pow, add_assoc]
  constructor
  · rintro ⟨hz, hd⟩
    exact ⟨hder.1 hd, (hval (hder.1 hd)).symm.trans hz⟩
  · rintro ⟨ht, hb⟩
    exact ⟨(hval ht).trans hb, hder.2 ht⟩

private theorem common_root_odd {n v P L w t : ℕ}
    (hn : Odd n) (hu : Odd (w * L)) (hv : Odd v)
    (hdeg : n = t + w * P) (hsum : w * L + v = t * 2) {x : K} (hx : x ≠ 0) :
    let F := productCandidate n (w * L) v
    aeval x F = 0 ∧ aeval x F.derivative = 0 ↔
      x ^ t = 1 ∧ aeval (x ^ w) (reciprocalSieveAux P L) = 0 := by
  dsimp only
  have hfix : x ^ (w * L + v) = 1 ↔ x ^ t = 1 := by
    rw [hsum, pow_mul]
    exact ⟨sq_one, fun ht => by rw [ht, one_pow]⟩
  have hval (ht : x ^ t = 1) :
      aeval x (productCandidate n (w * L) v) = 0 ↔ aeval (x ^ w) (reciprocalSieveAux P L) = 0 := by
    let a := (x ^ w) ^ L
    have ha : a ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hx)
    have hab : a * x ^ v = 1 := by simpa only [pow_add, pow_mul, a] using hfix.2 ht
    have hxn : x ^ n = (x ^ w) ^ P := by rw [hdeg, pow_add, ht, one_mul, pow_mul]
    have hprod : a * aeval x (productCandidate n (w * L) v) =
        aeval (x ^ w) (reciprocalSieveAux P L) := by
      rw [eval_product, eval_aux, hxn, pow_mul]
      calc
        _ = (x ^ w) ^ P * a + (a + 1) * (a * x ^ v) + a * (a + 1) := by dsimp [a]; ring
        _ = _ := by rw [hab, mul_one]; linear_combination CharTwo.add_self_eq_zero a
    rw [← hprod, mul_eq_zero]
    simp [ha]
  constructor
  · rintro ⟨hz, hd⟩
    have ht := hfix.1 ((repeat_odd hn hu hv hx hz).1 hd)
    exact ⟨ht, (hval ht).1 hz⟩
  · rintro ⟨ht, hb⟩
    have hz := (hval ht).2 hb
    exact ⟨hz, (repeat_odd hn hu hv hx hz).2 (hfix.2 ht)⟩

end Squarefreeness

private theorem coprime_iff_aux {K : Type*} [Field K] [IsAlgClosed K] [Algebra (ZMod 2) K]
    {F G H : BinaryPoly} {w t : ℕ} (ht : 0 < t) (hwt : w.Coprime t) (hzero : aeval (0 : K) F ≠ 0)
    (hcommon : ∀ x : K, x ≠ 0 → (aeval x F = 0 ∧ aeval x G = 0 ↔
      x ^ t = 1 ∧ aeval (x ^ w) H = 0)) : IsCoprime F G ↔ IsCoprime H (X ^ t - 1) := by
  classical
  rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed (ZMod 2) K F G,
    isCoprime_iff_aeval_ne_zero_of_isAlgClosed (ZMod 2) K H (X ^ t - 1)]
  have hcycl (z : K) : aeval z (X ^ t - 1 : BinaryPoly) = 0 ↔ z ^ t = 1 := by simp [sub_eq_zero]
  constructor
  · intro hf β
    by_contra! hb
    have hβ := (hcycl β).1 hb.2
    have hne : β ≠ 0 := by rintro rfl; simp [zero_pow ht.ne'] at hβ
    obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime (x := β)
      (hwt.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hβ))
    have hxw : (β ^ j) ^ w = β := by rw [← pow_mul, Nat.mul_comm j w, pow_mul, hj]
    have hxt : (β ^ j) ^ t = 1 := by rw [← pow_mul, Nat.mul_comm j t, pow_mul, hβ, one_pow]
    have hp := (hcommon _ (pow_ne_zero j hne)).2 ⟨hxt, by rw [hxw]; exact hb.1⟩
    exact (hf _).elim (· hp.1) (· hp.2)
  · intro hh x
    by_contra! hp
    have hx : x ≠ 0 := fun he => hzero (he ▸ hp.1)
    obtain ⟨htx, hH⟩ := (hcommon x hx).1 hp
    have hxt : (x ^ w) ^ t = 1 := by rw [← pow_mul, Nat.mul_comm w t, pow_mul, htx, one_pow]
    exact (hh _).elim (· hH) (· ((hcycl _).2 hxt))

/-- In the inverse-root sieve, one fixed polynomial determines squarefreeness.
The residual exponent t is n-(P+L)w for even n and n-Pw for odd n. -/
theorem reciprocalSieve_separable_iff {n v P L w t : ℕ}
    (hn : 0 < n) (hu : Odd (w * L)) (hv : Odd v) (ht : 0 < t) (hc : w.Coprime n)
    (hgap : w * L + v + 2 * (w * P) = n + n)
    (hdeg : n = t + w * (if Even n then P + L else P)) :
    (productCandidate n (w * L) v).Separable ↔ IsCoprime (reciprocalSieveAux P L) (X ^ t - 1) := by
  let K := AlgebraicClosure (ZMod 2)
  have hwt : w.Coprime t := (Nat.coprime_add_mul_left_right _ _ _).1 (hdeg ▸ hc)
  apply coprime_iff_aux (K := K) ht hwt
  · simp [eval_product, zero_pow hn.ne', zero_pow hu.pos.ne', zero_pow hv.pos.ne']
  · intro x hx
    by_cases he : Even n
    · rw [if_pos he] at hdeg
      have hvform : v = w * L + t * 2 := by rw [Nat.mul_add] at hdeg; omega
      exact common_root_even he hn hu hv hdeg hvform hx
    · rw [if_neg he] at hdeg
      have hsum : w * L + v = t * 2 := by omega
      exact common_root_odd (Nat.not_even_iff_odd.1 he) hu hv hdeg hsum hx

/-- On the n-th roots of unity, the entire family restricts, up to multiplication
by a unit and the substitution Y = X^w, to this fixed polynomial. -/
noncomputable def reciprocalSieveObstruction (P L : ℕ) : BinaryPoly :=
  X ^ (2 * (P + L)) + X ^ L + 1

theorem reciprocalSieve_coprime_roots_of_unity_iff {n v P L w : ℕ}
    (hn : 0 < n) (hu : 0 < w * L) (hv : 0 < v) (hc : w.Coprime n)
    (hgap : w * L + v + 2 * (w * P) = n + n) :
    IsCoprime (productCandidate n (w * L) v) (X ^ n - 1) ↔
    IsCoprime (reciprocalSieveObstruction P L) (X ^ n - 1) := by
  let K := AlgebraicClosure (ZMod 2)
  apply coprime_iff_aux (K := K) hn hc
  · simp [eval_product, zero_pow hn.ne', zero_pow hu.ne', zero_pow hv.ne']
  · intro x hx
    have hz : aeval x (X ^ n - 1 : BinaryPoly) = 0 ↔ x ^ n = 1 := by simp [sub_eq_zero]
    rw [hz, and_comm]
    apply and_congr_right
    intro hxn
    let β := x ^ w
    let a := β ^ L
    let b := β ^ (2 * P + L)
    have hb : b ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hx)
    have hsum : w * (2 * P + L) + v = n + n := by
      rw [Nat.mul_add, Nat.mul_left_comm w 2 P]
      omega
    have hby : b * x ^ v = 1 := by
      change (x ^ w) ^ (2 * P + L) * x ^ v = 1
      rw [← pow_mul, ← pow_add, hsum, pow_add, hxn, one_mul]
    have hG : aeval β (reciprocalSieveObstruction P L) = a * b + a + 1 := by
      simp only [reciprocalSieveObstruction, map_add, map_pow, aeval_X, map_one]
      rw [show 2 * (P + L) = L + (2 * P + L) by omega, pow_add β L (2 * P + L)]
    have hprod : b * aeval x (productCandidate n (w * L) v) =
        aeval β (reciprocalSieveObstruction P L) := by
      rw [eval_product, hxn, pow_mul, hG]
      calc
        _ = b + (a + 1) * (b * x ^ v) + (a + 1) * b := by dsimp [a, β]; ring
        _ = _ := by rw [hby, mul_one]; linear_combination CharTwo.add_self_eq_zero b
    change _ ↔ aeval β _ = 0
    rw [← hprod, mul_eq_zero]
    simp [hb]

private theorem natDegree_sieveObstruction {P L : ℕ} (hL : 0 < L) :
    (reciprocalSieveObstruction P L).natDegree = 2 * (P + L) := by
  have htail : (X ^ L + 1 : BinaryPoly).natDegree = L := by
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
    simpa using hL
  rw [reciprocalSieveObstruction, add_assoc, natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
  rw [htail, natDegree_X_pow]
  omega

/-- For fixed L and P a common period forces reducibility for every admissible
w coprime to the degree, however large that degree is. -/
theorem reciprocalSieve_reducible_on_multiples {n v P L w : ℕ} (hL : 0 < L)
    (hu : 0 < w * L) (huv : w * L < v) (htop : w * L + v < n) (hc : w.Coprime n)
    (hgap : w * L + v + 2 * (w * P) = n + n) (hperiod : period (2 * (P + L)) ∣ n) :
    ¬ Irreducible (productCandidate n (w * L) v) := by
  let G := reciprocalSieveObstruction P L
  have hdeg : G.natDegree = 2 * (P + L) := natDegree_sieveObstruction hL
  have hpos : 0 < G.natDegree := by omega
  obtain ⟨p, hp, hpg⟩ := WfDvdMonoid.exists_irreducible_factor (not_isUnit_of_natDegree_pos G hpos)
    (show G ≠ 0 by intro h; simp [h] at hpos)
  have hpd : p.natDegree ≤ 2 * (P + L) :=
    (natDegree_le_of_dvd hpg (fun h => by simp [h] at hpos)).trans hdeg.le
  have hgc : G.coeff 0 = 1 := by
    simp [G, reciprocalSieveObstruction, coeff_X_pow, hL.ne, hL.ne']
  have hr := root_pow_period hp hpd (root_ne_zero_of_factor hp hpg hgc)
  have hpn : p ∣ (X ^ n - 1 : BinaryPoly) := AdjoinRoot.mk_eq_zero.1 (by
    obtain ⟨k, hk⟩ := hperiod
    simp only [map_sub, map_pow, AdjoinRoot.mk_X, map_one, hk, pow_mul, hr, one_pow, sub_self])
  intro hi
  have hn : 0 < n := by omega
  have hv := hu.trans huv
  have hcop : IsCoprime (productCandidate n (w * L) v) (X ^ n - 1) := hi.coprime_iff_not_dvd.2 (by
    intro hd
    have hn' : (X ^ n - 1 : BinaryPoly).natDegree = n := by
      simpa using (natDegree_X_pow_sub_C (r := (1 : ZMod 2)) (n := n))
    have hmon : (X ^ n - 1 : BinaryPoly).Monic := by simpa using monic_X_pow_sub_C (1 : ZMod 2) hn.ne'
    have he := eq_of_monic_of_dvd_of_natDegree_le (binary_monic hi.ne_zero) hmon hd
      (le_of_eq (hn'.trans (product_shape hu hv huv.ne htop).1.symm))
    have he1 := congrArg (eval (1 : ZMod 2)) he
    simp [productCandidate, CharTwo.add_self_eq_zero] at he1)
  have hbad := (reciprocalSieve_coprime_roots_of_unity_iff hn hu hv hc hgap).1 hcop
  exact hp.not_isUnit (hbad.isUnit_of_dvd' hpg hpn)

/-- The B = 3 construction with L = 21, P = 32 and w = 1 is primitive
in degree 55. -/
theorem reciprocal_sieve_example_55 :
    Primitive (X ^ 55 + X ^ 46 + X ^ 25 + X ^ 21 + 1) := by
  exact certify_five_terms 55 46 25 21 [23, 31, 89, 881, 3191, 201961] (by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1) (by decide +kernel)

/-- A primitive member of the q = 8 slice with w = 1. -/
theorem product_slice_primitive_56 :
    Primitive (X ^ 56 + X ^ 54 + X ^ 47 + X ^ 7 + 1) := by
  apply certify_five_terms 56 54 47 7 [3, 5, 17, 29, 43, 113, 127, 15790321]
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1
  · decide +kernel

/-- With q = 64 the lower tap 63 also excludes all factors of degree at most three. -/
theorem product_slice_primitive_152 :
    Primitive (X ^ 152 + X ^ 150 + X ^ 87 + X ^ 63 + 1) := by
  have h : Nat.Prime 24517014940753 := by
    let two : ProvenPrime := ⟨2, by decide⟩
    exact (lucasPrime 24517014940753 15 [two, two, two, two, ⟨3, by decide⟩,
      ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨2309, by norm_num1⟩, ⟨684857, by norm_num1⟩]
      (by decide +kernel)).property
  apply certify_five_terms 152 150 87 63
    [3, 5, 17, 229, 457, 1217, 148961, 174763, 524287, 525313, 24517014940753]
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact h | norm_num1
  · decide +kernel

end GF2Sparse
