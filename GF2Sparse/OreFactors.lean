import GF2Sparse.OreOrder

/-! The largest irreducible factor degree of an Ore lift is the exact order
of the seed. For an irreducible seed, every factor attains that degree. -/

namespace GF2Sparse

open Polynomial FiniteField

private abbrev K := AlgebraicClosure (ZMod 2)
private noncomputable abbrev F := (frobeniusAlgHom (ZMod 2) K).toLinearMap

theorem derivative_linearized_associate (p : BinaryPoly) :
    derivative (X * oreLift p) = C (p.coeff 0) := by
  ext i
  rw [coeff_derivative, coeff_X_mul]
  by_cases h : i = 0
  · subst i; simp
  · rw [coeff_C, if_neg h]
    by_cases hi : i ∈ (oreLift p).support
    · rw [oreLift_support] at hi
      obtain ⟨j, _, hj⟩ := Finset.mem_map.1 hi
      change 2^j-1 = i at hj
      have hj0 : j ≠ 0 := by rintro rfl; exact h hj.symm
      have he : i+1 = 2^j := by rw [← hj, Nat.sub_add_cancel (Nat.two_pow_pos j)]
      have hcast : (i : ZMod 2)+1 = 0 := by
        rw [← Nat.cast_one, ← Nat.cast_add, he, Nat.cast_pow]
        simp [hj0, CharTwo.two_eq_zero]
      rw [hcast, mul_zero]
    · rw [notMem_support_iff.1 hi, zero_mul]

theorem separable_oreLift {p : BinaryPoly} (hc : p.coeff 0 = 1) : (oreLift p).Separable := by
  have h : (X * oreLift p).Separable := by
    rw [separable_def, derivative_linearized_associate, hc, C_1]
    exact isCoprime_one_right
  exact h.of_dvd (dvd_mul_left _ _)

private theorem fixed_of_seed_dvd {p : BinaryPoly} {d : ℕ} {z : K}
    (hz : aeval z (oreLift p) = 0) (h : p ∣ (X : BinaryPoly)^d-1) : z^(2^d) = z := by
  have hz' : (aeval F p) z = 0 := by rw [oreLift_frobenius, hz, mul_zero]
  obtain ⟨u, hu⟩ := h
  have he : (aeval F ((X : BinaryPoly)^d-1)) z = 0 := by
    rw [hu, mul_comm, map_mul, Module.End.mul_apply, hz', map_zero]
  simpa [F, binary_frobenius_pow_apply, sub_eq_zero] using he

/-- Every factor degree of the lift divides the seed order. -/
theorem oreLift_factor_degree_dvd {p u : BinaryPoly} (hu : Irreducible u) (h : u ∣ oreLift p) :
    u.natDegree ∣ orderOf (AdjoinRoot.root p) := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero K u (ne_of_gt hu.degree_pos)
  apply (degree_dvd_iff_frobenius hu hz _).2
  apply fixed_of_seed_dvd (aeval_eq_zero_of_dvd_aeval_eq_zero h hz)
  exact AdjoinRoot.mk_eq_zero.1 (by simp)

/-- Some irreducible factor realizes the full order as its degree for
every positive-degree seed with constant term one, including reducible seeds. -/
theorem oreLift_attains_seed_order {p : BinaryPoly} (hd : 0 < p.natDegree) (hc : p.coeff 0 = 1) :
    ∃ u : BinaryPoly, Irreducible u ∧ u ∣ oreLift p ∧ u.natDegree = orderOf (AdjoinRoot.root p) := by
  obtain ⟨z, hz⟩ := exists_exact_frobenius_annihilator p hc
  have hz0 : z ≠ 0 := by
    rintro rfl
    have hle := natDegree_le_of_dvd ((hz 1).1 (map_zero _)) (one_ne_zero : (1 : BinaryPoly) ≠ 0)
    rw [natDegree_one] at hle
    omega
  have hr : aeval z (oreLift p) = 0 :=
    (mul_eq_zero.1 ((oreLift_frobenius p z).symm.trans ((hz p).2 dvd_rfl))).resolve_left hz0
  let u := minpoly (ZMod 2) z
  have hu : Irreducible u := minpoly.irreducible (Algebra.IsIntegral.isIntegral z)
  have hdiv : u ∣ oreLift p := minpoly.dvd _ z hr
  refine ⟨u, hu, hdiv, Nat.dvd_antisymm (oreLift_factor_degree_dvd hu hdiv) ?_⟩
  have hf := (degree_dvd_iff_frobenius hu (minpoly.aeval _ z) _).1 dvd_rfl
  have hz' := (hz ((X : BinaryPoly)^u.natDegree-1)).1 (by
    simpa [binary_frobenius_pow_apply, sub_eq_zero] using hf)
  apply orderOf_dvd_of_pow_eq_one
  have := AdjoinRoot.mk_eq_zero.2 hz'
  simpa only [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] using this

theorem oreLift_factor_degree_of_irreducible {p u : BinaryPoly} (hp : Irreducible p) (hc : p.coeff 0 = 1)
    (hu : Irreducible u) (h : u ∣ oreLift p) : u.natDegree = orderOf (AdjoinRoot.root p) := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero K u (ne_of_gt hu.degree_pos)
  have hr := aeval_eq_zero_of_dvd_aeval_eq_zero h hz
  have hnz : z ≠ 0 := by
    rintro rfl
    rw [← coeff_zero_eq_aeval_zero', oreLift_constant, hc, map_one] at hr
    exact one_ne_zero hr
  have hpz : z ∈ LinearMap.ker (aeval F p) := by
    rw [LinearMap.mem_ker, oreLift_frobenius, hr, mul_zero]
  have huz : z ∈ LinearMap.ker (aeval F ((X : BinaryPoly)^u.natDegree-1)) := by
    simp [F, binary_frobenius_pow_apply, (degree_dvd_iff_frobenius hu hz _).1 dvd_rfl]
  have hd := hp.dvd_iff_not_isCoprime.2 fun e =>
    hnz (Submodule.disjoint_def.1 (disjoint_ker_aeval_of_isCoprime F e) z hpz huz)
  apply Nat.dvd_antisymm (oreLift_factor_degree_dvd hu h) (orderOf_dvd_of_pow_eq_one ?_)
  simpa only [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] using AdjoinRoot.mk_eq_zero.2 hd

/-- The number of distinct irreducible factors equals the multiplicative
index of the seed root whenever the seed is irreducible. -/
theorem oreLift_factor_count {p : BinaryPoly} (hp : Irreducible p) (hc : p.coeff 0 = 1) :
    (UniqueFactorizationMonoid.normalizedFactors (oreLift p)).card * orderOf (AdjoinRoot.root p) =
      2^p.natDegree-1 := by
  classical
  let g := oreLift p
  let fs := UniqueFactorizationMonoid.normalizedFactors g
  have hn := oreLift_ne_zero hp.ne_zero
  have hm : g.Monic := binary_monic hn
  have hprod : fs.prod = g := by simpa [fs, hm.leadingCoeff] using leadingCoeff_mul_prod_normalizedFactors g
  have hmem {u} (h : u ∈ fs) := (Polynomial.mem_normalizedFactors_iff hm.ne_zero).1 h
  have heq (u) (hu : u ∈ fs) := oreLift_factor_degree_of_irreducible hp hc (hmem hu).1 (hmem hu).2.2
  have he := natDegree_multiset_prod_of_monic fs (fun _ hu => (hmem hu).2.1)
  rw [hprod, Multiset.map_congr rfl heq, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul] at he
  exact he.symm.trans (oreLift_degree hp.ne_zero)

end GF2Sparse
