import GF2Sparse.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Ring.GeomSum

/-! The relative norm of the root of an irreducible composition H(h). -/

namespace GF2Sparse

open Polynomial

/-- The exponent of the norm from a field of size q^m to its subfield of size q. -/
def normExponent (q m : ℕ) : ℕ := ∑ j ∈ Finset.range m, q ^ j

theorem normExponent_mul {q : ℕ} (hq : 1 ≤ q) (m : ℕ) :
    normExponent q m * (q - 1) = q ^ m - 1 := geom_sum_mul_of_one_le hq m

/-- Every irreducible factor of H(h) contains a root of H in its residue field. -/
theorem outer_degree_dvd_factor {H h p : BinaryPoly} (hH : Irreducible H)
    (hp : Irreducible p) (hd : p ∣ H.comp h) : H.natDegree ∣ p.natDegree := by
  letI : Fact (Irreducible p) := ⟨hp⟩
  let E := AdjoinRoot p
  letI : CharP E 2 := charP_of_injective_ringHom (AdjoinRoot.of p).injective 2
  let z := AdjoinRoot.root p
  have hz : aeval z p = 0 := (AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self
  have hHz : aeval (aeval z h) H = 0 := by
    rw [← aeval_comp, AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_eq_zero.2 hd
  exact (degree_dvd_iff_frobenius hH hHz _).2 (by
    rw [← aeval_dyadic, (degree_dvd_iff_frobenius hp hz _).1 dvd_rfl])

private theorem conjugates_injective {K : Type*} [Field K] [Algebra (ZMod 2) K] [CharP K 2]
    {f : BinaryPoly} (hf : Irreducible f) {z : K} (hz : aeval z f = 0)
    {r m : ℕ} (hr : 0 < r) (hd : f.natDegree = r * m) :
    Function.Injective (fun j : Fin m => z ^ (2 ^ (r * j.val))) := by
  have hne (i j : Fin m) (hij : i < j) :
      z ^ (2 ^ (r * i.val)) ≠ z ^ (2 ^ (r * j.val)) := by
    let k := j.val - i.val
    have hk : 0 < k := Nat.sub_pos_of_lt hij
    have hsum : k + i.val = j.val := Nat.sub_add_cancel (Fin.le_iff_val_le_val.1 hij.le)
    intro he
    have hfix : z ^ (2 ^ (r * k)) = z := by
      apply (iterateFrobenius K 2 (r * i.val)).injective
      simpa only [iterateFrobenius_def, ← pow_mul, ← pow_add, ← Nat.mul_add, hsum] using he.symm
    have hdiv := (degree_dvd_iff_frobenius hf hz _).2 hfix
    rw [hd] at hdiv
    have hle := Nat.le_of_dvd hk (Nat.dvd_of_mul_dvd_mul_left hr hdiv)
    have := j.isLt
    dsimp [k] at hle
    omega
  intro i j he
  exact le_antisymm (le_of_not_gt (fun hij => hne j i hij he.symm))
    (le_of_not_gt (fun hij => hne i j hij he))

/-- In an irreducible composition, the relative conjugates of X multiply to h(X)
when h(0) = 0. The outer polynomial need only be irreducible here. -/
theorem norm_congruence_of_irreducible_comp {H h : BinaryPoly} (hH : Irreducible H)
    (hm : 0 < h.natDegree) (hc : h.coeff 0 = 0) (hf : Irreducible (H.comp h)) :
    H.comp h ∣ X ^ normExponent (2 ^ H.natDegree) h.natDegree - h := by
  classical
  let f := H.comp h
  let r := H.natDegree
  let m := h.natDegree
  let E := AdjoinRoot f
  letI : Fact (Irreducible f) := ⟨hf⟩
  letI : CharP E 2 := charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  let x := AdjoinRoot.root f
  let β := aeval x h
  let z (j : Fin m) := x ^ (2 ^ (r * j.val))
  have hx : aeval x f = 0 := (AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self
  have hβ : aeval β H = 0 := (aeval_comp x).symm.trans hx
  have hinj : Function.Injective z := conjugates_injective hf hx hH.natDegree_pos natDegree_comp
  let P := h.map (algebraMap (ZMod 2) E) - C β
  have hh : h.Monic := binary_monic (fun he => by simp [he] at hm)
  have hm' : (h.map (algebraMap (ZMod 2) E)).natDegree = m := natDegree_map _
  have hP : P.Monic := (hh.map _).sub_of_left ((degree_C_le).trans_lt
    (natDegree_pos_iff_degree_pos.mp (hm' ▸ hm)))
  have hdvd : (∏ j, (X - C (z j))) ∣ P := by
    apply Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C hinj)
    intro j
    rw [dvd_iff_isRoot, IsRoot.def, eval_sub, eval_C, eval_map, ← aeval_def,
      sub_eq_zero, aeval_dyadic]
    exact (degree_dvd_iff_frobenius hH hβ _).1 (dvd_mul_right _ _)
  have he : P = ∏ j, (X - C (z j)) := eq_of_monic_of_dvd_of_natDegree_le
    (monic_prod_X_sub_C z Finset.univ) hP hdvd (by simp [P, hm'])
  have hzero : (h.map (algebraMap (ZMod 2) E)).eval 0 = 0 := by
    rw [eval_zero_map, ← coeff_zero_eq_eval_zero, hc, map_zero]
  have hval := congrArg (eval (0 : E)) he
  simp only [P, eval_sub, hzero, eval_C, zero_sub, CharTwo.neg_eq, eval_prod, eval_X, z,
    Finset.prod_pow_eq_pow_sum] at hval
  apply AdjoinRoot.mk_eq_zero.1
  rw [map_sub, map_pow, sub_eq_zero]
  change x ^ normExponent (2 ^ r) m = AdjoinRoot.mk f h
  rw [← AdjoinRoot.aeval_eq]
  simpa only [normExponent, pow_mul, Fin.sum_univ_eq_sum_range] using hval.symm

private theorem norm_at_factor {f p h : BinaryPoly} {D : ℕ} (hp : p ∣ f)
    (hnorm : f ∣ X ^ D - h) : AdjoinRoot.root p ^ D = aeval (AdjoinRoot.root p) h := by
  have he := AdjoinRoot.mk_eq_zero.2 (hp.trans hnorm)
  simpa only [map_sub, map_pow, AdjoinRoot.mk_X, sub_eq_zero, AdjoinRoot.aeval_eq] using he

private theorem inner_order_at_factor {H h p : BinaryPoly} [Nontrivial (AdjoinRoot p)]
    (hH : Primitive H) (hd : p ∣ H.comp h) :
    orderOf (aeval (AdjoinRoot.root p) h) = 2 ^ H.natDegree - 1 := by
  have he : aeval (aeval (AdjoinRoot.root p) h) H = 0 := by
    rw [← aeval_comp, AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_eq_zero.2 hd
  exact (orderOf_root_at hH.2.1 he).trans hH.2.2

private theorem root_pow_of_norm {H h p : BinaryPoly} [Nontrivial (AdjoinRoot p)]
    (hH : Primitive H) (hd : p ∣ H.comp h)
    (hnorm : H.comp h ∣ X ^ normExponent (2 ^ H.natDegree) h.natDegree - h) :
    AdjoinRoot.root p ^ ((2 ^ H.natDegree) ^ h.natDegree - 1) = 1 := by
  rw [← normExponent_mul (Nat.two_pow_pos H.natDegree), pow_mul, norm_at_factor hd hnorm,
    ← inner_order_at_factor hH hd, pow_orderOf_eq_one]

private theorem pow_ne_one_div_prime {M : Type*} [Monoid M] {x : M} {N p : ℕ}
    (ho : orderOf x = N) (hN : 0 < N) (hp : p.Prime) (hd : p ∣ N) : x ^ (N / p) ≠ 1 := by
  intro he
  have h := orderOf_dvd_of_pow_eq_one he
  rw [ho] at h
  exact (Nat.div_lt_self hN hp.one_lt).not_ge
    (Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hN hd) hp.pos) h)

/-- A single norm congruence supplies the maximal order at all primes of
the outer field's multiplicative group, even before irreducibility is known. -/
theorem primitive_comp_iff_norm_and_prime_checks {H h : BinaryPoly} (hH : Primitive H)
    (hm : 0 < h.natDegree) (hc : h.coeff 0 = 0) :
    let q := 2 ^ H.natDegree
    let N := q ^ h.natDegree - 1
    Primitive (H.comp h) ↔
      H.comp h ∣ X ^ normExponent q h.natDegree - h ∧
      ∀ p : ℕ, p.Prime → p ∣ N → ¬ p ∣ q - 1 →
        AdjoinRoot.root (H.comp h) ^ (N / p) ≠ 1 := by
  let f := H.comp h
  let q := 2 ^ H.natDegree
  let R := q - 1
  let D := normExponent q h.natDegree
  let N := q ^ h.natDegree - 1
  let x := AdjoinRoot.root f
  have hn : 0 < f.natDegree := by
    rw [show f = H.comp h from rfl, natDegree_comp]
    exact Nat.mul_pos hH.2.1.natDegree_pos hm
  have hsize : 2 ^ f.natDegree - 1 = N := by simp only [f, natDegree_comp, pow_mul, N, q]
  have hN : 0 < N := hsize ▸ Nat.sub_pos_of_lt (Nat.one_lt_two_pow hn.ne')
  have hq : 1 < q := Nat.one_lt_two_pow hH.2.1.natDegree_pos.ne'
  have hR : 0 < R := Nat.sub_pos_of_lt hq
  have hDR : D * R = N := normExponent_mul hq.le _
  change Primitive f ↔ f ∣ X ^ D - h ∧ ∀ p : ℕ, p.Prime → p ∣ N → ¬p ∣ R → x ^ (N / p) ≠ 1
  constructor
  · intro hf
    exact ⟨norm_congruence_of_irreducible_comp hH.2.1 hm hc hf.2.1,
      fun _ hp hd _ => pow_ne_one_div_prime (hf.2.2.trans hsize) hN hp hd⟩
  · rintro ⟨hnorm, hrest⟩
    letI := AdjoinRoot.nontrivial f (degree_ne_of_natDegree_ne hn.ne')
    have ho := inner_order_at_factor hH (dvd_refl f)
    have he := norm_at_factor (dvd_refl f) hnorm
    apply primitive_of_prime_checks (binary_monic (fun hzero => by simp [hzero] at hn)) hn
    · rw [hsize]
      exact root_pow_of_norm hH (dvd_refl f) hnorm
    · rw [hsize]
      intro p hp hd
      by_cases hbase : p ∣ R
      · change x ^ (N / p) ≠ 1
        rw [← hDR, Nat.mul_div_assoc _ hbase, pow_mul, he]
        exact pow_ne_one_div_prime ho hR hp hbase
      · exact hrest p hp hd hbase

end GF2Sparse
