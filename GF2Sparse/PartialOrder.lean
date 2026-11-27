import GF2Sparse.Roots

/-! Prime-degree irreducibility and the exact part of an order recovered from
a partial factorization of the group size. -/

namespace GF2Sparse

open Polynomial

/-- At prime degree the Frobenius identity and absence of linear factors suffice. -/
theorem irreducible_of_prime_degree_power {f : BinaryPoly} (hn : f.natDegree.Prime)
    (hbase : ∀ x : ZMod 2, f.eval x ≠ 0)
    (hpow : AdjoinRoot.root f ^ (2^f.natDegree-1) = 1) : Irreducible f := by
  have hf : f ≠ 0 := by rintro rfl; exact Nat.not_prime_zero hn
  obtain ⟨p,hp,hpf⟩ := WfDvdMonoid.exists_irreducible_factor (not_isUnit_of_natDegree_pos f hn.pos) hf
  letI : Fact (Irreducible p) := ⟨hp⟩
  let x := AdjoinRoot.root p
  have hx : aeval x p = 0 := (AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self
  have hmod : f ∣ X^(2^f.natDegree)-(X : BinaryPoly) := by
    apply AdjoinRoot.mk_eq_zero.1
    rw [map_sub, map_pow, AdjoinRoot.mk_X, sub_eq_zero]
    have he : 2^f.natDegree = (2^f.natDegree-1)+1 := by have := Nat.two_pow_pos f.natDegree; omega
    conv_lhs => rw [he, pow_succ, hpow, one_mul]
  have he := AdjoinRoot.mk_eq_zero.2 (hpf.trans hmod)
  simp only [map_sub, map_pow, AdjoinRoot.mk_X, sub_eq_zero] at he
  have hdiv := (degree_dvd_iff_frobenius hp hx _).2 he
  have h1 : p.natDegree ≠ 1 := by
    intro h
    obtain ⟨z,hz⟩ := exists_root_of_degree_eq_one ((degree_eq_iff_natDegree_eq hp.ne_zero).2 h)
    exact hbase z (hz.dvd hpf)
  have heq := (Nat.dvd_prime hn).1 hdiv |>.resolve_left h1
  rwa [eq_of_monic_of_dvd_of_natDegree_le (binary_monic hp.ne_zero) (binary_monic hf) hpf heq.ge]

/-- A known order for a projected element extracts an exact factor of the
original order. A second nonidentity test forces an additional divisor. -/
theorem order_split_of_projection {G : Type*} [Monoid G] {r : G} {k c : ℕ}
    (hk : 0 < k) (hc : 0 < c) (hfull : r^(k*c) = 1)
    (hknown : orderOf (r^c) = k) (hextra : r^k ≠ 1) :
    ∃ t : ℕ, 1 < t ∧ t ∣ c ∧ orderOf r = k*t := by
  have hd : k ∣ orderOf r := hknown ▸ orderOf_pow_dvd (x := r) c
  obtain ⟨t,ht⟩ := hd
  have htc : t ∣ c := Nat.dvd_of_mul_dvd_mul_left hk (ht ▸ orderOf_dvd_of_pow_eq_one hfull)
  have ht0 := Nat.pos_of_dvd_of_pos htc hc
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [mul_one] at ht
    exact hextra (ht ▸ pow_orderOf_eq_one r)
  exact ⟨t, by omega, htc, ht⟩

/-- When the quotient of the two field group orders is prime, the order of
every root of full degree is recovered from its norm to the smaller field. -/
theorem orderOf_root_of_prime_norm_quotient {K : Type*} [Field K] [Algebra (ZMod 2) K]
    {f : BinaryPoly} (hf : Irreducible f) {z : K} (hz : aeval z f = 0)
    {d q : ℕ} (hd : 0 < d) (hsmall : d < f.natDegree) (hq : q.Prime)
    (hsize : 2 ^ f.natDegree - 1 = q * (2 ^ d - 1)) :
    orderOf z = q * orderOf (z ^ q) := by
  have frob := degree_dvd_iff_frobenius hf hz
  have hproper : z ^ (2 ^ d) ≠ z :=
    fun h => (not_le_of_gt hsmall) (Nat.le_of_dvd hd ((frob d).2 h))
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hproper (by simp)
  have hfull : z ^ (2 ^ f.natDegree - 1) = 1 := by
    apply mul_right_cancel₀ hz0
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel (Nat.two_pow_pos _), (frob _).1 dvd_rfl]
  have hmiss : ¬ orderOf z ∣ 2 ^ d - 1 := by
    intro h
    apply hproper
    have hfix : z ^ (2 ^ d - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp h
    conv_lhs => rw [← Nat.sub_add_cancel (Nat.two_pow_pos d : 1 ≤ 2 ^ d), pow_succ, hfix, one_mul]
  have hdiv : q ∣ orderOf z := by
    by_contra h
    have cop := (hq.coprime_iff_not_dvd.mpr h).symm
    exact hmiss (cop.dvd_mul_left.mp (hsize ▸ orderOf_dvd_of_pow_eq_one hfull))
  rw [orderOf_pow_of_dvd hq.ne_zero hdiv, Nat.mul_div_cancel' hdiv]

/-- For a finite field extension of prime norm exponent, a polynomial of full
degree is primitive exactly when the norm of a root generates the smaller field's units. -/
theorem primitive_iff_norm_order_of_prime_quotient {F E : Type*} [Field F] [Field E]
    [Algebra F E] [Algebra (ZMod 2) E] [Finite E]
    {f : BinaryPoly} (hf : Irreducible f) {z : E} (hz : aeval z f = 0)
    {d q : ℕ} (hd : 0 < d) (hsmall : d < f.natDegree) (hq : q.Prime)
    (hF : Nat.card F = 2 ^ d) (hE : Nat.card E = 2 ^ f.natDegree)
    (hsize : 2 ^ f.natDegree - 1 = q * (2 ^ d - 1)) :
    Primitive f ↔ orderOf (Algebra.norm F z) = 2 ^ d - 1 := by
  have he := orderOf_root_of_prime_norm_quotient hf hz hd hsmall hq hsize
  have hpos := Nat.sub_pos_of_lt (Nat.one_lt_two_pow hd.ne')
  have hnorm := FiniteField.algebraMap_norm_eq_pow (K := F) (x := z)
  rw [hE, hF, hsize, Nat.mul_div_cancel _ hpos] at hnorm
  have hmap : orderOf (algebraMap F E (Algebra.norm F z)) = orderOf (Algebra.norm F z) :=
    orderOf_injective (algebraMap F E).toMonoidHom (algebraMap F E).injective _
  rw [← hnorm, hmap] at he
  have hzord := orderOf_root_at hf hz
  constructor
  · intro hp
    exact Nat.eq_of_mul_eq_mul_left hq.pos (he.symm.trans (hzord.trans (hp.2.2.trans hsize)))
  · intro hn
    refine ⟨binary_monic hf.ne_zero, hf, hzord.symm.trans ?_⟩
    exact he.trans ((congrArg (q * ·) hn).trans hsize.symm)

end GF2Sparse
