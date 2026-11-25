import GF2Sparse.TripleRoots
import GF2Sparse.Table
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.RingTheory.Polynomial.Basic

/-! Ordinary polynomials in the binary Frobenius detect possible factor
degrees of X^(2^s-1) + X + 1. -/

namespace GF2Sparse

open Polynomial FiniteField

variable {K : Type*} [Field K] [Algebra (ZMod 2) K] [CharP K 2]

omit [CharP K 2] in
private theorem frobenius_pow_apply (k : ℕ) (x : K) :
    ((frobeniusAlgHom (ZMod 2) K).toLinearMap ^ k) x = x ^ (2 ^ k) := by
  rw [Module.End.pow_apply]
  change (fun y : K => y ^ Fintype.card (ZMod 2))^[k] x = _
  simp [pow_iterate]

/-- A nonzero root of the linearized trinomial fixed by degree-d
Frobenius forces an ordinary common factor in degrees s and d. -/
theorem frobenius_trinomial_not_coprime {s d : ℕ} {x : K} (hx : x ≠ 0)
    (hs : x ^ (2 ^ s) = x ^ 2 + x) (hd : x ^ (2 ^ d) = x) :
    ¬ IsCoprime (trinomial s 1) ((X : BinaryPoly) ^ d - 1) := by
  let F := (frobeniusAlgHom (ZMod 2) K).toLinearMap
  have hF (k : ℕ) : (F ^ k) x = x ^ (2 ^ k) := frobenius_pow_apply k x
  have h1 : F x = x ^ 2 := by simpa using hF 1
  have hp : x ∈ LinearMap.ker (aeval F (trinomial s 1)) := by
    simp only [LinearMap.mem_ker, trinomial, pow_one, map_add, map_pow, aeval_X, map_one,
      LinearMap.add_apply, Module.End.one_apply, hF, h1, hs, CharTwo.add_self_eq_zero]
  have hq : x ∈ LinearMap.ker (aeval F ((X : BinaryPoly) ^ d - 1)) := by
    simp [hF, hd]
  intro hc
  exact hx (Submodule.disjoint_def.1 (disjoint_ker_aeval_of_isCoprime F hc) x hp hq)

/-- Test the possible degree of an irreducible divisor with polynomials
of ordinary degrees s and d. -/
theorem additive_trinomial_factor_obstruction {p : BinaryPoly} (hp : Irreducible p)
    {s : ℕ} (hs : 0 < s) (hdiv : p ∣ trinomial (2 ^ s - 1) 1) :
    ¬ IsCoprime (trinomial s 1) ((X : BinaryPoly) ^ p.natDegree - 1) := by
  letI : Fact (Irreducible p) := ⟨hp⟩
  letI : CharP (AdjoinRoot p) 2 := charP_of_injective_ringHom (AdjoinRoot.of p).injective 2
  let x := AdjoinRoot.root p
  have hx : aeval x p = 0 := by rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_self
  have hT : aeval x (trinomial (2 ^ s - 1) 1) = 0 := by
    obtain ⟨q, hq⟩ := hdiv
    rw [hq, map_mul, hx, zero_mul]
  have hpow : x ^ (2 ^ s - 1) = x + 1 := by
    simpa only [trinomial, pow_one, map_add, map_pow, aeval_X, map_one,
      CharTwo.add_eq_zero] using hT
  have hpos := Nat.one_lt_two_pow hs.ne'
  have hx0 : x ≠ 0 := by
    rintro hzero
    simp [hzero, zero_pow (by omega : 2 ^ s - 1 ≠ 0)] at hpow
  apply frobenius_trinomial_not_coprime hx0 _ ((degree_dvd_iff_frobenius hp hx _).1 dvd_rfl)
  conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ 2 ^ s), pow_succ, hpow]
  ring

/-- Ore's irreducibility construction for a primitive X^s + X + 1. -/
theorem irreducible_trinomial_of_primitive_associate {s : ℕ} (hs : 1 < s)
    (hprim : Primitive (trinomial s 1)) : Irreducible (trinomial (2 ^ s - 1) 1) := by
  let n := 2 ^ s - 1
  have hfour : 2 ^ 2 ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hs
  have hn : 1 < n := by dsimp [n]; omega
  have hd := trinomial_degree (by decide : 0 < 1) hn
  have hpos : 0 < (trinomial n 1).natDegree := by rw [hd]; omega
  have hne : trinomial n 1 ≠ 0 := by intro h; simp [h] at hpos
  obtain ⟨p, hp, hdiv⟩ := WfDvdMonoid.exists_irreducible_factor
    (not_isUnit_of_natDegree_pos _ hpos) hne
  have hcommon := hprim.2.1.dvd_iff_not_isCoprime.2
    (additive_trinomial_factor_obstruction hp (by omega : 0 < s) hdiv)
  have hpow := AdjoinRoot.mk_eq_zero.2 hcommon
  simp only [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at hpow
  have horder := orderOf_dvd_of_pow_eq_one hpow
  rw [hprim.2.2, trinomial_degree (by decide) hs] at horder
  have hle : n ≤ p.natDegree := Nat.le_of_dvd hp.natDegree_pos horder
  have heq := eq_of_monic_of_dvd_of_natDegree_le (binary_monic hp.ne_zero) (binary_monic hne)
    hdiv (hd.trans_le hle)
  change Irreducible (trinomial n 1)
  rwa [heq]

/-- Recover the trinomial root from a root of the cubic sampling polynomial. -/
private theorem recover_trinomial_root {u : ℕ} {z : K}
    (hz : aeval z (sampledBlock 0 1 u 3) = 0) :
    ∃ r : K, r ^ 3 = z ∧ aeval r (trinomial (3 * u + 1) 1) = 0 := by
  have hmul : z * (z ^ u + 1) ^ 3 = 1 := by
    symm
    simpa only [sampledBlock, pow_zero, pow_one, map_add, map_mul, map_pow,
      aeval_X, map_one, CharTwo.add_eq_zero] using hz
  have hne : z ^ u + 1 ≠ 0 := by intro h; simp [h] at hmul
  let r := (z ^ u + 1)⁻¹
  have hc : r ^ 3 = z := by
    change ((z ^ u + 1)⁻¹) ^ 3 = z
    rw [inv_pow]
    calc
      _ = (z * (z ^ u + 1) ^ 3) * ((z ^ u + 1) ^ 3)⁻¹ := by rw [hmul, one_mul]
      _ = z := by rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hne), mul_one]
  refine ⟨r, hc, ?_⟩
  have hr : (z ^ u + 1) * r = 1 := mul_inv_cancel₀ hne
  simp only [trinomial, pow_one, map_add, map_pow, aeval_X, map_one]
  rw [pow_succ, pow_mul, hc]
  linear_combination hr + CharTwo.add_self_eq_zero (1 : K)

/-- Cubic sampling preserves irreducibility for these trinomials because
each sampled root recovers a trinomial root in its own field. -/
theorem irreducible_sampled_of_trinomial {u : ℕ} (hu : 0 < u)
    (ht : Irreducible (trinomial (3 * u + 1) 1)) : Irreducible (sampledBlock 0 1 u 3) := by
  let f := sampledBlock 0 1 u 3
  have hbin : ((X : BinaryPoly) ^ u + 1).natDegree = u := by
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
    simpa using hu
  have hne : (X : BinaryPoly) ^ u + 1 ≠ 0 := by intro h; simp [h] at hbin; omega
  have htop : (X * ((X : BinaryPoly) ^ u + 1) ^ 3).natDegree = 3 * u + 1 := by
    rw [natDegree_mul X_ne_zero (pow_ne_zero _ hne), natDegree_pow, hbin, natDegree_X]; omega
  have hdeg : f.natDegree = 3 * u + 1 := by
    simp only [f, sampledBlock, pow_zero, pow_one]
    rw [natDegree_add_eq_right_of_natDegree_lt, htop]
    simp [htop]
  have hf : f ≠ 0 := by intro h; simp [h] at hdeg
  obtain ⟨p, hp, hdiv⟩ := WfDvdMonoid.exists_irreducible_factor
    (not_isUnit_of_natDegree_pos f (by omega)) hf
  letI : Fact (Irreducible p) := ⟨hp⟩
  letI : CharP (AdjoinRoot p) 2 := charP_of_injective_ringHom (AdjoinRoot.of p).injective 2
  letI : Fintype (AdjoinRoot p) := Fintype.ofEquiv _ (AdjoinRoot.powerBasisAux hp.ne_zero).equivFun.toEquiv.symm
  have hroot : aeval (AdjoinRoot.root p) f = 0 := by
    rw [AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_eq_zero.2 hdiv
  obtain ⟨r, _, hr⟩ := recover_trinomial_root hroot
  have hfix := FiniteField.pow_card r
  rw [card_adjoinRoot hp.ne_zero] at hfix
  have hd := (degree_dvd_iff_frobenius ht hr _).2 hfix
  rw [trinomial_degree (by decide) (by omega)] at hd
  have heq : f = p := eq_of_monic_of_dvd_of_natDegree_le (binary_monic hp.ne_zero)
    (binary_monic hf) hdiv (hdeg.trans_le (Nat.le_of_dvd hp.natDegree_pos hd))
  change Irreducible f
  rwa [heq]

theorem primitive_trinomial_127 : Primitive (trinomial 127 1) := by
  let mask := 2 ^ 127 ^^^ (2 ^ 1 ^^^ 1)
  have hm : decode mask = trinomial 127 1 := by
    simp only [mask, trinomial, decode_xor, decode_pow_two, decode_one]
  rw [← hm]
  apply (check_sound (n := 127) (factors := [2 ^ 127 - 1]) ?_ (by decide +kernel)).2.2
  intro p hp
  obtain rfl := List.mem_singleton.1 hp
  exact lucas_lehmer_sufficiency 127 (by decide) (by norm_num)

theorem irreducible_trinomial_mersenne_127 : Irreducible (trinomial (2 ^ 127 - 1) 1) :=
  irreducible_trinomial_of_primitive_associate (by decide) primitive_trinomial_127

theorem irreducible_pentanomial_mersenne_127 :
    Irreducible (sampledBlock 0 1 ((2 ^ 127 - 2) / 3) 3) := by
  apply irreducible_sampled_of_trinomial (by decide)
  exact irreducible_trinomial_mersenne_127

end GF2Sparse
