import GF2Sparse.FibreBound
import GF2Sparse.Linearized
import Mathlib.Data.Set.Finite.Lattice

/-! Short root products in the additive trinomial family. -/

namespace GF2Sparse

open Polynomial

private abbrev K := AlgebraicClosure (ZMod 2)

private noncomputable def iteratePoly : ℕ → K[X]
  | 0 => X
  | j + 1 => iteratePoly j * (iteratePoly j + 1)

private noncomputable def layer : ℕ → K[X]
  | 0 => X
  | j + 1 => iteratePoly j + 1

private theorem iterate_monic_degree (j : ℕ) :
    (iteratePoly j).Monic ∧ (iteratePoly j).natDegree = 2 ^ j := by
  induction j with
  | zero => simp [iteratePoly]
  | succ j ih =>
    have hlt : (1 : K[X]).natDegree < (iteratePoly j).natDegree := by simp [ih.2]
    have hm := ih.1.add_of_left (degree_lt_degree hlt)
    refine ⟨ih.1.mul hm, ?_⟩
    rw [iteratePoly, ih.1.natDegree_mul hm, natDegree_add_eq_left_of_natDegree_lt hlt, ih.2, pow_succ]
    omega

private theorem layer_monic_degree (j : ℕ) : (layer j).Monic ∧ 0 < (layer j).natDegree := by
  cases j with
  | zero => simp [layer]
  | succ j =>
    obtain ⟨hm, hd⟩ := iterate_monic_degree j
    have hlt : (1 : K[X]).natDegree < (iteratePoly j).natDegree := by simp [hd]
    exact ⟨hm.add_of_left (degree_lt_degree hlt), by
      rw [layer, natDegree_add_eq_left_of_natDegree_lt hlt, hd]; positivity⟩

private theorem layer_root_later {i j : ℕ} {x : K} (h : (layer i).eval x = 0) (hlt : i < j) :
    (layer j).eval x = 1 := by
  have hi : (iteratePoly i).eval x = 0 := by
    cases i with
    | zero => exact h
    | succ i =>
      change (iteratePoly i + 1).eval x = 0 at h
      simp [iteratePoly, h]
  obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le hlt
  have hz (b : ℕ) : (iteratePoly (i + b)).eval x = 0 := by
    induction b with
    | zero => simpa using hi
    | succ b ih => simp [iteratePoly, ih]
  have he : j = (i + l) + 1 := by omega
  simp [he, layer, hz l]

private def candidatePolys (k : ℕ) : Set K[X] :=
  {H | H.Monic ∧ H.natDegree = k ∧
    ∀ j : Fin k, (((layer j).roots.map (fun x => H.eval x)).prod) ^ 3 = 1}

private theorem finite_candidatePolys (k : ℕ) : (candidatePolys k).Finite := by
  classical
  let U := ((X ^ 3 - 1 : K[X]).roots).toFinset
  let nodes (j : Fin k) := (layer j).roots
  have hpos (j : Fin k) : 0 < (nodes j).card := by
    rw [show (nodes j).card = (layer j).natDegree from (IsAlgClosed.splits _).natDegree_eq_card_roots.symm]
    exact (layer_monic_degree j).2
  have hdis (i j : Fin k) (x : K) (hi : x ∈ nodes i) (hj : x ∈ nodes j) : i = j := by
    have hi' := (mem_roots (layer_monic_degree i).1.ne_zero).1 hi
    have hj' := (mem_roots (layer_monic_degree j).1.ne_zero).1 hj
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact (zero_ne_one (hj'.symm.trans (layer_root_later hi' h))).elim
    · exact Fin.ext h
    · exact (zero_ne_one (hi'.symm.trans (layer_root_later hj' h))).elim
  let S (t : Fin k → U) := {H : K[X] | H.Monic ∧ H.natDegree = k ∧
    ∀ j, ((nodes j).map (fun x => H.eval x)).prod = (t j).val}
  have hfin (t : Fin k → U) : (S t).Finite :=
    finite_prescribed_multiset_products nodes _ hpos hdis
  apply (Set.finite_iUnion hfin).subset
  rintro H ⟨hm, hd, ht⟩
  let t (j : Fin k) := ((nodes j).map (fun x => H.eval x)).prod
  have hmem (j : Fin k) : t j ∈ U := by
    apply Multiset.mem_toFinset.2
    apply (mem_roots (X_pow_sub_C_ne_zero (R := K) (by decide : 0 < 3) 1)).2
    simpa [IsRoot, t, nodes] using sub_eq_zero.2 (ht j)
  exact Set.mem_iUnion.2 ⟨(fun j => ⟨t j, hmem j⟩), hm, hd, fun _ => rfl⟩

private def candidateRoots (k : ℕ) : Set K := ⋃ H ∈ candidatePolys k, {x | H.IsRoot x}

private theorem finite_candidateRoots (k : ℕ) : (candidateRoots k).Finite :=
  (finite_candidatePolys k).biUnion (fun _ h => finite_setOf_isRoot h.1.ne_zero)

private theorem iterate_next {s : ℕ} {x : K} (hx : x ^ (2 ^ s) = x * (x + 1)) (j : ℕ) :
    (iteratePoly (j + 1)).eval x = ((iteratePoly j).eval x) ^ (2 ^ s) := by
  induction j with
  | zero => simpa [iteratePoly] using hx.symm
  | succ j ih =>
    calc
      _ = (iteratePoly (j+1)).eval x * ((iteratePoly (j+1)).eval x + 1) := by
        simp only [iteratePoly, eval_mul, eval_add, eval_one]
      _ = ((iteratePoly j).eval x * ((iteratePoly j).eval x + 1)) ^ (2 ^ s) := by
        rw [ih, mul_pow, add_pow_expChar_pow, one_pow]
      _ = _ := by simp only [iteratePoly, eval_mul, eval_add, eval_one]

private theorem layer_products {k s : ℕ} (r : Fin k → K)
    (hr : ∀ i, r i ^ (2 ^ s) = r i * (r i + 1)) (hz : (∏ i, r i) ^ 3 = 1) (j : ℕ) :
    (∏ i, (layer j).eval (r i)) ^ 3 = 1 := by
  have hi (a : ℕ) : (∏ i, (iteratePoly a).eval (r i)) ^ 3 = 1 := by
    induction a with
    | zero => simpa [iteratePoly] using hz
    | succ a ih =>
      simp_rw [iterate_next (hr _) a]
      rw [Finset.prod_pow, pow_right_comm, ih, one_pow]
  cases j with
  | zero => simpa [layer] using hz
  | succ j =>
    have h := hi (j+1)
    simpa only [iteratePoly, eval_mul, Finset.prod_mul_distrib, mul_pow, hi j, one_mul,
      layer] using h

private theorem eval_root_products (g : K[X]) (hg : g.Monic) {k : ℕ} (r : Fin k → K) :
    (g.roots.map (fun a => (∏ i, (X - C (r i))).eval a)).prod = ∏ i, g.eval (r i) := by
  have swap (m : Multiset K) : (m.map (fun a => ∏ i, (r i - a))).prod =
      ∏ i, (m.map (r i - ·)).prod := by
    induction m using Multiset.induction with
    | empty => simp
    | cons x m ih => simp [ih, Finset.prod_mul_distrib]
  have he (a : K) : (∏ i, (X - C (r i))).eval a = ∏ i, (r i - a) := by
    simp [eval_prod, sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  simp only [he, swap, ← (IsAlgClosed.splits g).eval_eq_prod_roots_of_monic hg]

private theorem mem_candidateRoots {k s : ℕ} (r : Fin k → K)
    (hr : ∀ i, r i ^ (2 ^ s) = r i * (r i + 1)) (hz : (∏ i, r i) ^ 3 = 1) (t : Fin k) :
    r t ∈ candidateRoots k := by
  let H : K[X] := ∏ i, (X - C (r i))
  have hm : H.Monic := monic_prod_X_sub_C r _
  have hd : H.natDegree = k := by simp [H]
  have hH : H ∈ candidatePolys k := by
    refine ⟨hm, hd, fun j => ?_⟩
    rw [show ((layer j).roots.map (fun x => H.eval x)).prod = ∏ i, (layer j).eval (r i) from
      eval_root_products _ (layer_monic_degree j).1 r]
    exact layer_products r hr hz j
  change r t ∈ ⋃ H ∈ candidatePolys k, {x | H.IsRoot x}
  refine Set.mem_iUnion.2 ⟨H, Set.mem_iUnion.2 ⟨hH, ?_⟩⟩
  change H.eval (r t) = 0
  simp only [H, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ t) (sub_self _)

private theorem common_frobenius_period (S : Set K) (hS : S.Finite) :
    ∃ M : ℕ, 0 < M ∧ ∀ x ∈ S, x ^ (2 ^ M) = x := by
  classical
  let d (x : K) := (minpoly (ZMod 2) x).natDegree
  have hi (x : K) : Irreducible (minpoly (ZMod 2) x) := minpoly.irreducible (Algebra.IsIntegral.isIntegral x)
  let M := ∏ x ∈ hS.toFinset, d x
  refine ⟨M, Finset.prod_pos (fun x _ => (hi x).natDegree_pos), fun x hx => ?_⟩
  apply (degree_dvd_iff_frobenius (hi x) (minpoly.aeval _ _) M).1
  exact Finset.dvd_prod_of_mem d (hS.mem_toFinset.2 hx)

private theorem fixed_at_multiple {x : K} {M : ℕ} (h : x ^ (2 ^ M) = x) (l : ℕ) :
    x ^ (2 ^ (M * l)) = x := by
  induction l with
  | zero => simp
  | succ l ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

/-- A single progression of odd Frobenius exponents rules out products
of up to k trinomial roots in the cube roots of unity. Repetitions are allowed. -/
theorem short_trinomial_products (k : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ l : ℕ, let s := M * (2 * l) + 1
      ∀ j : ℕ, 0 < j → j ≤ k → ∀ r : Fin j → AlgebraicClosure (ZMod 2),
        (∀ i, aeval (r i) (trinomial (2 ^ s - 1) 1) = 0) → (∏ i, r i) ^ 3 ≠ 1 := by
  let S := ⋃ j : Fin (k+1), candidateRoots j
  obtain ⟨M, hM, hfix⟩ := common_frobenius_period S (Set.finite_iUnion fun j => finite_candidateRoots j)
  refine ⟨M, hM, fun l j hj hk r hr hz => ?_⟩
  let s := M * (2 * l) + 1
  have hs : 0 < s := by dsimp [s]; omega
  have ht (i : Fin j) : r i ^ (2 ^ s - 1) = r i + 1 := by
    simpa only [trinomial, pow_one, map_add, map_pow, aeval_X, map_one, CharTwo.add_eq_zero] using hr i
  have hpos := Nat.one_lt_two_pow hs.ne'
  have hf (i : Fin j) : r i ^ (2 ^ s) = r i * (r i + 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ 2 ^ s), pow_succ, ht i]
    ring
  let i : Fin j := ⟨0, hj⟩
  have hm : r i ∈ S := Set.mem_iUnion.2 ⟨⟨j, by omega⟩, mem_candidateRoots r hf hz i⟩
  have he : r i ^ (2 ^ s) = r i ^ 2 := by
    rw [show s = M * (2 * l) + 1 from rfl, pow_succ 2, pow_mul, fixed_at_multiple (hfix _ hm)]
  have hzero : r i = 0 := by linear_combination he - hf i
  have hb := ht i
  simp [hzero, zero_pow (by omega : 2 ^ s - 1 ≠ 0)] at hb

private theorem even_thirds (w : ℕ) : ∃ b : ℕ, 2 ^ (2 * w + 1) = 6 * b + 2 := by
  induction w with
  | zero => exact ⟨0, rfl⟩
  | succ w ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨4 * b + 1, ?_⟩
    rw [show 2 * (w+1) + 1 = (2*w+1)+2 by omega, pow_add, hb]
    omega

private theorem inverse_cubic_sample {u : ℕ} (hu : 0 < u) {z : K}
    (hz : aeval z (productCandidate (3*u+1) u (2*u)) = 0) :
    aeval z⁻¹ (sampledBlock 0 1 u 3) = 0 := by
  have hp : z ^ (3*u+1) = (z ^ u + 1) * (z ^ (2*u) + 1) := by
    simpa only [productCandidate, map_add, map_mul, map_pow, aeval_X, map_one,
      CharTwo.add_eq_zero] using hz
  have hzero : z ≠ 0 := by rintro rfl; simp [zero_pow hu.ne', zero_pow (by omega : 2*u ≠ 0)] at hp
  have hpow : z * (z ^ u) ^ 3 = (z ^ u + 1) ^ 3 := by
    rw [pow_succ (z^u + 1) 2, CharTwo.add_sq, one_pow]
    rw [pow_succ z (3*u), pow_mul' z 3 u, pow_mul' z 2 u] at hp
    linear_combination hp
  have hval : z⁻¹ * ((z⁻¹) ^ u + 1) ^ 3 = 1 := by
    rw [inv_pow]
    field_simp [hzero, pow_ne_zero u hzero]
    linear_combination -hpow
  simp only [sampledBlock, pow_zero, pow_one, map_add, map_mul, map_pow, aeval_X, map_one, hval,
    CharTwo.add_self_eq_zero]

private theorem cubic_product_squarefree {u : ℕ} (hu : 0 < u) (he : Even u) :
    Squarefree (productCandidate (3*u+1) u (2*u)) := by
  have h2 : Even (2*u) := ⟨u, by omega⟩
  have hc : (productCandidate (3*u+1) u (2*u)).coeff 0 = 1 := by
    simp [coeff_zero_eq_eval_zero, productCandidate, zero_pow hu.ne', zero_pow (by omega : 2*u ≠ 0)]
  apply Polynomial.Separable.squarefree
  refine isCoprime_of_irreducible_dvd (fun h => by simp [h.1] at hc) ?_
  intro p hp hpf hpd
  letI : Fact (Irreducible p) := ⟨hp⟩
  have hroot := root_ne_zero_of_factor hp hpf hc
  have hder := AdjoinRoot.mk_eq_zero.2 hpd
  simp [productCandidate, derivative_mul, derivative_X_pow, he.natCast_zmod_two,
    h2.natCast_zmod_two, hroot] at hder

/-- Selections with repetition of one through k binary roots. -/
def NoShortRootProducts (k : ℕ) (f : BinaryPoly) : Prop :=
  ∀ j : ℕ, 0 < j → j ≤ k → ∀ z : Fin j → AlgebraicClosure (ZMod 2),
    (∀ i, aeval (z i) f = 0) → ∏ i, z i ≠ 1

/-- For each k, an arithmetic progression of exponents s gives normalized
squarefree pentanomials of degree 2^s-1 with no product-one selection of
one through k roots, including selections with repetitions. -/
theorem arbitrarily_many_pentanomial_tests (k : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ l : ℕ, let s := M * (2 * (l + 1)) + 1
      ∃ u : ℕ, 0 < u ∧ 3*u+1 = 2^s-1 ∧ (3*u+1).Coprime u ∧
        let f := productCandidate (3*u+1) u (2*u)
        f.natDegree = 2^s-1 ∧ f.support.card = 5 ∧ Squarefree f ∧ NoShortRootProducts k f := by
  obtain ⟨M, hM, htests⟩ := short_trinomial_products k
  refine ⟨M, hM, fun l => ?_⟩
  let s := M * (2 * (l + 1)) + 1
  have hs : s = 2 * (M * (l+1)) + 1 := by dsimp [s]; ring
  have hpos : 0 < M * (l+1) := Nat.mul_pos hM (by omega)
  obtain ⟨b, hb⟩ := even_thirds (M * (l+1))
  rw [← hs] at hb
  have hlarge : 2^3 ≤ 2^s := Nat.pow_le_pow_right (by decide) (by omega)
  let u := 2*b
  have hu : 0 < u := by dsimp [u]; omega
  have hn : 3*u+1 = 2^s-1 := by dsimp [u]; omega
  have he : Even u := ⟨b, by dsimp [u]; omega⟩
  have hc : (3*u+1).Coprime u := by simp [Nat.coprime_comm]
  obtain ⟨hdeg, hcard⟩ := product_shape (n := 3*u+1) hu (by omega : 0 < 2*u) (by omega) (by omega)
  refine ⟨u, hu, hn, hc, hdeg.trans hn, hcard, cubic_product_squarefree hu he, ?_⟩
  intro j hj hk z hz hzprod
  choose r hcub ht using fun i => trinomial_root_of_cubic_sample (inverse_cubic_sample hu (hz i))
  apply htests (l+1) j hj hk r (fun i => hn ▸ ht i)
  rw [← Finset.prod_pow]
  simp_rw [hcub]
  rw [Finset.prod_inv_distrib, hzprod, inv_one]

/-- A single explicit sequence works eventually for every fixed number of tests. -/
theorem factorial_pentanomial_tests (k : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      let n := 2 ^ (j.factorial + 1) - 1
      let u := (n-1)/3
      let f := productCandidate n u (2*u)
      n.Coprime u ∧ f.natDegree = n ∧ f.support.card = 5 ∧ Squarefree f ∧
        NoShortRootProducts k f := by
  obtain ⟨M, hM, hpass⟩ := arbitrarily_many_pentanomial_tests k
  refine ⟨2*M, fun j hj => ?_⟩
  obtain ⟨t, ht⟩ := Nat.dvd_factorial (by omega : 0 < 2*M) hj
  have htn : t ≠ 0 := by rintro rfl; simp [Nat.factorial_ne_zero] at ht
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero htn
  have hs : M * (2 * (l+1)) = j.factorial := by rw [ht, Nat.succ_eq_add_one]; ring
  obtain ⟨u, _, hn, hc, hd, hw, hsep, hp⟩ := hpass l
  rw [hs] at hn hd
  dsimp only
  rw [← hn, show (3*u+1-1)/3 = u by omega]
  exact ⟨hc, hd.trans hn.symm, hw, hsep, hp⟩

end GF2Sparse
