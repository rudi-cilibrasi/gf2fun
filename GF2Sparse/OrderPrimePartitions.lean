import GF2Sparse.SparseOrderBounds

/-! Prime-index tests for sparse witnesses whose root-order primes come from a proper subfield. -/

namespace GF2Sparse

open Polynomial

private theorem root_pow_field_order {f : BinaryPoly} (hf : Irreducible f)
    (hc : f.coeff 0 = 1) : AdjoinRoot.root f ^ (2 ^ f.natDegree - 1) = 1 := by
  letI : Fact (Irreducible f) := ⟨hf⟩
  have hz : aeval (AdjoinRoot.root f) f = 0 :=
    (AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self
  have h₀ : AdjoinRoot.root f ≠ 0 := by
    intro h
    rw [h, ← coeff_zero_eq_aeval_zero', hc, map_one] at hz
    exact one_ne_zero hz
  apply mul_right_cancel₀ h₀
  rw [one_mul, ← pow_succ, Nat.sub_add_cancel (Nat.two_pow_pos _)]
  exact (degree_dvd_iff_frobenius hf hz _).1 dvd_rfl

/-- When a prime divides the base field order, one power decides whether
substitution by that prime preserves irreducibility. -/
theorem irreducible_prime_expand_iff_index_test {f : BinaryPoly} (hf : Irreducible f)
    (hc : f.coeff 0 = 1) {r : ℕ} (hr : r.Prime) (hd : r ∣ 2 ^ f.natDegree - 1) :
    Irreducible (expand (ZMod 2) r f) ↔
      AdjoinRoot.root f ^ ((2 ^ f.natDegree - 1) / r) ≠ 1 := by
  let F := expand (ZMod 2) r f
  let b := AdjoinRoot.root f ^ ((2 ^ f.natDegree - 1) / r)
  have hdeg : F.natDegree = f.natDegree * r := natDegree_expand _ _
  have hmon : F.Monic := (binary_monic hf.ne_zero).expand hr.pos
  have hb : b ^ r = 1 := by
    dsimp only [b]
    rw [← pow_mul, Nat.div_mul_cancel hd]
    exact root_pow_field_order hf hc
  change Irreducible F ↔ b ≠ 1
  constructor
  · intro h hb₁
    have he := factor_degree_of_expand hf hc h hd (dvd_refl F)
    change F.natDegree = f.natDegree * orderOf b at he
    rw [hdeg, hb₁, orderOf_one] at he
    exact hr.ne_one (Nat.eq_of_mul_eq_mul_left hf.natDegree_pos he)
  · intro hb₁
    have ho : orderOf b = r :=
      ((Nat.dvd_prime hr).1 (orderOf_dvd_of_pow_eq_one hb)).resolve_left
        (fun h => hb₁ (orderOf_eq_one_iff.1 h))
    obtain ⟨p, hp, hpf⟩ := WfDvdMonoid.exists_irreducible_factor
      (not_isUnit_of_natDegree_pos F (hdeg ▸ Nat.mul_pos hf.natDegree_pos hr.pos)) hmon.ne_zero
    have he := factor_degree_of_expand hf hc hp hd hpf
    change p.natDegree = f.natDegree * orderOf b at he
    have heq : F = p := eq_of_monic_of_dvd_of_natDegree_le (binary_monic hp.ne_zero) hmon hpf
      (by rw [hdeg, he, ho])
    rwa [heq]

/-- All order primes of an irreducible dilation by a divisor of the base
field order already divide that field order. -/
theorem prime_dvd_base_order_of_expand {f : BinaryPoly} (hf : Irreducible f)
    (hc : f.coeff 0 = 1) {r ℓ : ℕ} (hr : 0 < r) (hd : r ∣ 2 ^ f.natDegree - 1)
    (hi : Irreducible (expand (ZMod 2) r f)) (hℓ : ℓ.Prime)
    (h : ℓ ∣ orderOf (AdjoinRoot.root (expand (ZMod 2) r f))) :
    ℓ ∣ 2 ^ f.natDegree - 1 := by
  rw [root_order_irreducible_dilation hf hr hi] at h
  exact (hℓ.dvd_mul.mp h).elim (·.trans hd)
    (·.trans (orderOf_dvd_of_pow_eq_one (root_pow_field_order hf hc)))

end GF2Sparse
