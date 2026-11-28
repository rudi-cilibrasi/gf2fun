import GF2Sparse.AdditiveOrbit
import GF2Sparse.OrderBound
import GF2Sparse.PolynomialSupport

/-! Ore's binary linearized associate divided by X. Replacing every support
index i by 2^i-1 preserves weight and turns primitivity into irreducibility. -/

namespace GF2Sparse

open Polynomial FiniteField

private theorem oreIndex_strict : StrictMono (fun i : ℕ => 2^i-1) := by
  intro i j hij
  have h := Nat.pow_lt_pow_right (by decide : 1 < 2) hij
  have := Nat.two_pow_pos i
  dsimp
  omega

def oreIndex : ℕ ↪ ℕ := ⟨_, oreIndex_strict.injective⟩

/-- The quotient by X of the binary linearized polynomial associated to p. -/
noncomputable def oreLift (p : BinaryPoly) : BinaryPoly :=
  ⟨Finsupp.embDomain oreIndex p.toFinsupp⟩

theorem oreLift_support (p : BinaryPoly) : (oreLift p).support = p.support.map oreIndex :=
  Finsupp.support_embDomain _ _

@[simp] theorem oreLift_weight (p : BinaryPoly) : (oreLift p).support.card = p.support.card := by
  rw [oreLift_support, Finset.card_map]

theorem oreLift_coeff (p : BinaryPoly) (i : ℕ) : (oreLift p).coeff (2^i-1) = p.coeff i :=
  Finsupp.embDomain_apply_self oreIndex _ i

@[simp] theorem oreLift_constant (p : BinaryPoly) : (oreLift p).coeff 0 = p.coeff 0 :=
  oreLift_coeff p 0

theorem oreLift_ne_zero {p : BinaryPoly} (hp : p ≠ 0) : oreLift p ≠ 0 := by
  have h := oreLift_coeff p p.natDegree
  rw [coeff_natDegree] at h
  intro e
  exact leadingCoeff_ne_zero.2 hp (by simpa [e] using h.symm)

@[simp] theorem oreLift_add (p q : BinaryPoly) : oreLift (p+q) = oreLift p + oreLift q :=
  toFinsupp_injective (Finsupp.embDomain_add _ _ _)

@[simp] theorem oreLift_X_pow (a : ℕ) : oreLift ((X : BinaryPoly)^a) = X^(2^a-1) := by
  apply toFinsupp_injective
  change Finsupp.embDomain oreIndex _ = _
  rw [toFinsupp_X_pow, Finsupp.embDomain_single, toFinsupp_X_pow]
  rfl

@[simp] theorem oreLift_one : oreLift 1 = 1 := by simpa using oreLift_X_pow 0

theorem oreLift_degree {p : BinaryPoly} (hp : p ≠ 0) :
    (oreLift p).natDegree = 2^p.natDegree-1 := by
  have top := natDegree_mem_support_of_nonzero hp
  have ht : oreIndex p.natDegree ∈ (oreLift p).support := by
    rw [oreLift_support]; exact Finset.mem_map_of_mem _ top
  apply eq_natDegree_of_le_mem_support _ ht
  apply natDegree_le_iff_coeff_eq_zero.2
  intro k hk
  by_contra h
  have hm := mem_support_iff.2 h
  rw [oreLift_support] at hm
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hm
  exact (not_lt_of_ge (oreIndex_strict.monotone (le_natDegree_of_mem_supp _ hi))) hk

/-- Evaluation at Frobenius is ordinary evaluation of the linearized polynomial. -/
theorem oreLift_frobenius {K : Type*} [Field K] [Algebra (ZMod 2) K] (p : BinaryPoly) (z : K) :
    aeval (frobeniusAlgHom (ZMod 2) K).toLinearMap p z = z * aeval z (oreLift p) := by
  simp only [aeval_binary_support, oreLift_support, Finset.sum_map,
    Finset.mul_sum, LinearMap.sum_apply, binary_frobenius_pow_apply]
  apply Finset.sum_congr rfl
  intro i _
  change z^(2^i) = z * z^(2^i-1)
  rw [← pow_succ', Nat.sub_add_cancel (Nat.two_pow_pos i)]

theorem Primitive.coeff_zero_eq_one {p : BinaryPoly} (hp : Primitive p) : p.coeff 0 = 1 := by
  have h : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  apply h
  intro hc
  have hx : aeval (0 : ZMod 2) p = 0 := by rw [← coeff_zero_eq_aeval_zero', hc, map_zero]
  have ho := (orderOf_root_at hp.2.1 hx).trans hp.2.2
  rw [orderOf_zero] at ho
  have := Nat.one_lt_two_pow hp.2.1.natDegree_pos.ne'
  omega

/-- For a constant-one seed, irreducibility of its Ore lift is equivalent to
the seed having full multiplicative order, even when the seed starts reducible. -/
theorem irreducible_oreLift_iff {p : BinaryPoly} (hs : 0 < p.natDegree) (hc : p.coeff 0 = 1) :
    Irreducible (oreLift p) ↔ Primitive p := by
  classical
  have hp : p ≠ 0 := by intro he; simp [he] at hc
  let q := oreLift p
  have hqdeg : q.natDegree = 2^p.natDegree-1 := oreLift_degree hp
  have hn := Nat.one_lt_two_pow hs.ne'
  have hqpos : 0 < q.natDegree := by omega
  have hq : q ≠ 0 := by intro e; simp [e] at hqpos
  let K := AlgebraicClosure (ZMod 2)
  let F := (frobeniusAlgHom (ZMod 2) K).toLinearMap
  constructor
  · intro h
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero K q (ne_of_gt h.degree_pos)
    have hzL : (aeval F p) z = 0 := by rw [oreLift_frobenius, hz, mul_zero]
    let y := AdjoinRoot.root p
    letI : Fintype (AdjoinRoot p) := Fintype.ofEquiv _ (AdjoinRoot.powerBasisAux hp).equivFun.toEquiv.symm
    letI := AdjoinRoot.nontrivial p (degree_ne_of_natDegree_ne hs.ne')
    have hy : IsUnit y := root_unit hc
    have hm := hy.isOfFinOrder.orderOf_pos
    have hdiv : p ∣ (X : BinaryPoly)^(orderOf y)-1 := AdjoinRoot.mk_eq_zero.1 (by
      simp only [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero]; exact pow_orderOf_eq_one y)
    obtain ⟨a, ha⟩ := hdiv
    have hk : (aeval F ((X : BinaryPoly)^(orderOf y)-1)) z = 0 := by
      rw [ha, mul_comm, map_mul, Module.End.mul_apply, hzL, map_zero]
    have hfix : z^(2^orderOf y) = z := by
      simpa [F, binary_frobenius_pow_apply, sub_eq_zero] using hk
    have hle := Nat.le_of_dvd hm ((degree_dvd_iff_frobenius h hz _).2 hfix)
    let inj (i : Fin (orderOf y)) : {t : AdjoinRoot p // t ≠ 0} := ⟨y^i.val, (hy.pow _).ne_zero⟩
    have hi : Function.Injective inj := fun i j e =>
      Fin.ext (pow_injOn_Iio_orderOf i.isLt j.isLt (congrArg Subtype.val e))
    have hub := Fintype.card_le_of_injective inj hi
    rw [Fintype.card_fin, Fintype.card_subtype_compl] at hub
    simp only [Fintype.card_unique, card_adjoinRoot hp] at hub
    change q.natDegree ≤ orderOf y at hle
    rw [hqdeg] at hle
    exact primitive_of_order (binary_monic hp) hs (le_antisymm hub hle)
  · intro h
    obtain ⟨u, hu, huq⟩ := WfDvdMonoid.exists_irreducible_factor (not_isUnit_of_natDegree_pos q hqpos) hq
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero K u (ne_of_gt hu.degree_pos)
    have hzq : aeval z q = 0 := by obtain ⟨w, hw⟩ := huq; rw [hw, map_mul, hz, zero_mul]
    have hnz : z ≠ 0 := by
      rintro rfl
      rw [← coeff_zero_eq_aeval_zero', oreLift_constant, hc, map_one] at hzq
      exact one_ne_zero hzq
    have hpz : z ∈ LinearMap.ker (aeval F p) := by
      rw [LinearMap.mem_ker, oreLift_frobenius, hzq, mul_zero]
    have huz : z ∈ LinearMap.ker (aeval F ((X : BinaryPoly)^u.natDegree-1)) := by
      simp [F, binary_frobenius_pow_apply, (degree_dvd_iff_frobenius hu hz _).1 dvd_rfl]
    have hd := h.2.1.dvd_iff_not_isCoprime.2 (fun e =>
      hnz (Submodule.disjoint_def.1 (disjoint_ker_aeval_of_isCoprime F e) z hpz huz))
    have ho := AdjoinRoot.mk_eq_zero.2 hd
    simp only [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at ho
    have hle := Nat.le_of_dvd hu.natDegree_pos (orderOf_dvd_of_pow_eq_one ho)
    rw [h.2.2, ← hqdeg] at hle
    have he := eq_of_monic_of_dvd_of_natDegree_le (binary_monic hu.ne_zero) (binary_monic hq) huq hle
    change Irreducible q
    rwa [he]

theorem Primitive.irreducible_oreLift {p : BinaryPoly} (hp : Primitive p) : Irreducible (oreLift p) :=
  (irreducible_oreLift_iff hp.2.1.natDegree_pos hp.coeff_zero_eq_one).2 hp

/-- The lifted roots are the nonzero points of a binary cube. This excludes
every product of fewer than the seed degree many roots, including repetition. -/
theorem Primitive.oreLift_short_products {p : BinaryPoly} (hp : Primitive p) {k : ℕ}
    (hk : k < p.natDegree) : NoShortRootProducts k (oreLift p) := by
  classical
  by_cases hs : 1 < p.natDegree
  · let s := p.natDegree
    let K := AlgebraicClosure (ZMod 2)
    let F := (frobeniusAlgHom (ZMod 2) K).toLinearMap
    have hf := hp.irreducible_oreLift
    have hdeg := oreLift_degree hp.2.1.ne_zero
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero K (oreLift p) (ne_of_gt hf.degree_pos)
    have hd : (minpoly (ZMod 2) r).natDegree = 2^s-1 := by
      rw [← minpoly.eq_of_irreducible_of_monic hf hr (binary_monic hf.ne_zero), hdeg]
    let v (j : Fin s) := r^(2^j.val)
    have htwo : 2^(s-1)*2 = 2^s := by rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ s by omega)]
    have hgt := Nat.one_lt_two_pow (show s-1 ≠ 0 by change p.natDegree-1 ≠ 0; omega)
    let ix (j : Fin s) : Fin (minpoly (ZMod 2) r).natDegree := ⟨2^j.val, by
      rw [hd]
      have hj := Nat.pow_le_pow_right (by decide : 0 < 2) (show j.val ≤ s-1 by omega)
      omega⟩
    have hi : LinearIndependent (ZMod 2) v := (linearIndependent_pow r).comp ix
      (fun i j e => Fin.ext (Nat.pow_right_injective (by decide : 2 ≤ 2) (congrArg Fin.val e)))
    have hv (j : Fin s) : (aeval F p) (v j) = 0 := by
      rw [oreLift_frobenius]
      simp only [v, aeval_dyadic, hr, zero_pow (Nat.two_pow_pos _).ne', mul_zero]
    apply no_short_products_of_binary_cube hf v _ hk
    intro c hc
    have hne : ∑ j, c j • v j ≠ 0 := fun e => hc (funext (Fintype.linearIndependent_iff.1 hi c e))
    have hz : (aeval F p) (∑ j, c j • v j) = 0 := by simp [map_sum, map_smul, hv]
    exact (mul_eq_zero.1 ((oreLift_frobenius p _).symm.trans hz)).resolve_left hne
  · intro j hj hjk
    omega

end GF2Sparse
