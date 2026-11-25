import GF2Sparse.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Separable

/-! The relative norm of the root of an irreducible composition H(h). -/

namespace GF2Sparse

open Polynomial

/-- The exponent of the norm from a field of size q^m to its subfield of size q. -/
def normExponent (q m : ℕ) : ℕ := ∑ j ∈ Finset.range m, q ^ j

theorem normExponent_mul {q : ℕ} (hq : 1 ≤ q) (m : ℕ) :
    normExponent q m * (q - 1) = q ^ m - 1 := geom_sum_mul_of_one_le hq m

theorem normExponent_eq_div {q : ℕ} (hq : 1 < q) (m : ℕ) :
    normExponent q m = (q ^ m - 1) / (q - 1) := by
  rw [← normExponent_mul hq.le, Nat.mul_div_cancel _ (Nat.sub_pos_of_lt hq)]

private theorem comp_degree_pos {H h : BinaryPoly} (hH : Irreducible H) (hm : 0 < h.natDegree) :
    0 < (H.comp h).natDegree := by
  rw [natDegree_comp]
  exact Nat.mul_pos hH.natDegree_pos hm

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
  have hn : 0 < f.natDegree := comp_degree_pos hH.2.1 hm
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

private theorem normExponent_add (q t u : ℕ) :
    normExponent q (t + u) = normExponent q t + q ^ t * normExponent q u := by
  simp only [normExponent, Finset.sum_range_add, pow_add, Finset.mul_sum]

private theorem repeat_norm {M : Type*} [Monoid M] {x : M} {q t : ℕ}
    (hfix : x ^ (q ^ t) = x) (k : ℕ) :
    x ^ normExponent q (t * k) = (x ^ normExponent q t) ^ k := by
  induction k with
  | zero => simp [normExponent]
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm (t * k) t, normExponent_add, pow_add,
      pow_mul, hfix, ih, pow_succ']

/-- Under the norm congruence, a factor of relative degree t has relative
index k coprime to the order of the outer field's multiplicative group. -/
theorem factor_degree_of_norm_congruence {H h p : BinaryPoly} (hH : Primitive H)
    (hm : 0 < h.natDegree) (hp : Irreducible p) (hd : p ∣ H.comp h)
    (hnorm : H.comp h ∣ X ^ normExponent (2 ^ H.natDegree) h.natDegree - h) :
    ∃ t k : ℕ, p.natDegree = H.natDegree * t ∧ h.natDegree = t * k ∧
      k.Coprime (2 ^ H.natDegree - 1) := by
  let r := H.natDegree
  let m := h.natDegree
  let q := 2 ^ r
  let R := q - 1
  let x := AdjoinRoot.root p
  letI : Fact (Irreducible p) := ⟨hp⟩
  have hr : 0 < r := hH.2.1.natDegree_pos
  have hq : 1 < q := Nat.one_lt_two_pow hr.ne'
  have hR : 0 < R := Nat.sub_pos_of_lt hq
  have hN : 0 < q ^ m - 1 := Nat.sub_pos_of_lt (one_lt_pow₀ hq hm.ne')
  have hfull : x ^ (q ^ m - 1) = 1 := root_pow_of_norm hH hd hnorm
  have hx0 : x ≠ 0 := by
    intro hx
    exact zero_ne_one ((zero_pow hN.ne').symm.trans (hx ▸ hfull))
  have hx : aeval x p = 0 := (AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self
  have hfixed : x ^ (q ^ m) = x := by
    calc
      x ^ (q ^ m) = x ^ ((q ^ m - 1) + 1) := by rw [Nat.sub_add_cancel (by omega)]
      _ = x := by rw [pow_succ, hfull, one_mul]
  obtain ⟨t, ht⟩ := outer_degree_dvd_factor hH.2.1 hp hd
  have htm : t ∣ m := by
    apply Nat.dvd_of_mul_dvd_mul_left hr
    rw [← ht]
    apply (degree_dvd_iff_frobenius hp hx _).2
    simpa only [pow_mul] using hfixed
  obtain ⟨k, hk⟩ := htm
  refine ⟨t, k, ht, hk, ?_⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp [m] at hk
    omega
  have hxt : x ^ (q ^ t) = x := by
    have he := (degree_dvd_iff_frobenius hp hx _).1 (dvd_refl p.natDegree)
    simpa only [ht, pow_mul] using he
  let y := x ^ normExponent q t
  have hy : y ^ R = 1 := by
    change (x ^ normExponent q t) ^ (q - 1) = 1
    rw [← pow_mul, normExponent_mul hq.le]
    apply mul_right_cancel₀ hx0
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hq.le), hxt]
  have hyk : y ^ k = aeval x h := by
    rw [show y ^ k = x ^ normExponent q (t * k) from (repeat_norm hxt k).symm, ← hk]
    exact norm_at_factor hd hnorm
  have hok : orderOf (y ^ k) = R := (congrArg orderOf hyk).trans (inner_order_at_factor hH hd)
  have hoy : orderOf y = R := Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hy)
    (hok ▸ orderOf_pow_dvd (x := y) k)
  have he := orderOf_pow' y hk0
  rw [hok, hoy] at he
  apply Nat.Coprime.symm
  change R.gcd k = 1
  have hg := Nat.gcd_pos_of_pos_left k hR
  by_contra! h
  exact (Nat.div_lt_self hR (by omega : 1 < R.gcd k)).ne he.symm

/-- If every prime of the relative degree divides the order of the outer
field's multiplicative group, a single modular power decides irreducibility. -/
theorem irreducible_comp_iff_norm_of_smooth {H h : BinaryPoly} (hH : Primitive H)
    (hm : 0 < h.natDegree) (hc : h.coeff 0 = 0)
    (hs : ∀ p : ℕ, p.Prime → p ∣ h.natDegree → p ∣ 2 ^ H.natDegree - 1) :
    Irreducible (H.comp h) ↔ H.comp h ∣ X ^ normExponent (2 ^ H.natDegree) h.natDegree - h := by
  refine ⟨norm_congruence_of_irreducible_comp hH.2.1 hm hc, fun hnorm => ?_⟩
  let f := H.comp h
  have hn : 0 < f.natDegree := comp_degree_pos hH.2.1 hm
  have hf : f.Monic := binary_monic (fun he => by simp [he] at hn)
  obtain ⟨p, hp, hd⟩ := WfDvdMonoid.exists_irreducible_factor (not_isUnit_of_natDegree_pos f hn)
    hf.ne_zero
  obtain ⟨t, k, ht, hk, hcop⟩ := factor_degree_of_norm_congruence hH hm hp hd hnorm
  have hk1 : k = 1 := by
    by_contra he
    obtain ⟨l, hl, hlk⟩ := Nat.exists_prime_and_dvd he
    have hld : l ∣ h.natDegree := hk ▸ hlk.trans (dvd_mul_left _ _)
    exact hl.ne_one (Nat.eq_one_of_dvd_coprimes hcop hlk (hs l hl hld))
  have heq : f = p := eq_of_monic_of_dvd_of_natDegree_le (binary_monic hp.ne_zero) hf hd
    (by simp only [f, natDegree_comp, ht, hk, hk1, mul_one, le_refl])
  change Irreducible f
  rwa [heq]

/-- The norm congruence rules out repeated factors for every relative degree. -/
theorem squarefree_comp_of_norm {H h : BinaryPoly} (hH : Primitive H) (hm : 0 < h.natDegree)
    (hnorm : H.comp h ∣ X ^ normExponent (2 ^ H.natDegree) h.natDegree - h) :
    Squarefree (H.comp h) := by
  let f := H.comp h
  let n := f.natDegree
  have hn : 0 < n := comp_degree_pos hH.2.1 hm
  letI := AdjoinRoot.nontrivial f (degree_ne_of_natDegree_ne hn.ne')
  have hd : f ∣ X ^ (2 ^ n - 1) - 1 := AdjoinRoot.mk_eq_zero.1 (by
    simp only [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero, n, f, natDegree_comp, pow_mul]
    exact root_pow_of_norm hH (dvd_refl f) hnorm)
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [hj, pow_succ]
    exact ⟨2 ^ j - 1, by have := Nat.two_pow_pos j; omega⟩
  have hs := separable_X_pow_sub_C' 2 (2 ^ n - 1) (1 : ZMod 2) hodd.not_two_dvd_nat one_ne_zero
  rw [map_one] at hs
  exact (hs.of_dvd hd).squarefree

end GF2Sparse
