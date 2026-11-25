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

end GF2Sparse
