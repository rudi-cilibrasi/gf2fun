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

end GF2Sparse
