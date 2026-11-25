import GF2Sparse.DyadicTriples

/-! Factor degrees impose exact periods on the Frobenius exponent.
The five-term family has a quintic factor in three classes modulo five. -/

namespace GF2Sparse

open Polynomial

/-- For a fixed irreducible factor, the divisibility test for X^(2^s)+h only
needs the residue of s modulo the factor degree. -/
theorem dvd_dyadic_tail_iff_mod {p : BinaryPoly} (hp : Irreducible p) (h : BinaryPoly) (s : ℕ) :
    p ∣ X ^ (2 ^ s) + h ↔ p ∣ X ^ (2 ^ (s % p.natDegree)) + h := by
  letI : Fact (Irreducible p) := ⟨hp⟩
  let x := AdjoinRoot.root p
  have hx : aeval x p = 0 := by rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_self
  have hfix := (degree_dvd_iff_frobenius hp hx (p.natDegree * (s / p.natDegree))).1 (dvd_mul_right ..)
  have he : x ^ (2 ^ s) = x ^ (2 ^ (s % p.natDegree)) := by
    conv_lhs => rw [← Nat.mod_add_div s p.natDegree, Nat.add_comm, pow_add, pow_mul, hfix]
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.mk_eq_zero]
  simp only [map_add, map_pow, AdjoinRoot.mk_X]
  change x ^ (2 ^ s) + _ = 0 ↔ x ^ (2 ^ (s % p.natDegree)) + _ = 0
  rw [he]

private theorem quintic_seed {j : ℕ} (hj : j < 3) :
    (productCandidate (2 ^ j) 3 2).natDegree = 5 ∧ Primitive (productCandidate (2 ^ j) 3 2) := by
  have hcheck : ∀ i : Fin 3, check 5 (productMask (2 ^ i.val) 3 2) [31] = true := by decide +kernel
  have h := check_sound (fun p (hp : p ∈ [31]) => by simp only [List.mem_singleton] at hp; subst p; decide)
    (hcheck ⟨j, hj⟩)
  rw [decode_productMask] at h
  exact ⟨h.1, h.2.2⟩

/-- Exactly three residue classes of Frobenius exponents admit a quintic factor. -/
theorem dyadic_quintic_factor_iff (s : ℕ) :
    (∃ p : BinaryPoly, Irreducible p ∧ p.natDegree = 5 ∧ p ∣ productCandidate (2 ^ s) 3 2) ↔
      s % 5 < 3 := by
  constructor
  · rintro ⟨p, hp, hd, hdiv⟩
    have hsmall := (dvd_dyadic_tail_iff_mod hp ((X ^ 3 + 1) * (X ^ 2 + 1)) s).1 hdiv
    rw [hd] at hsmall
    change p ∣ productCandidate (2 ^ (s % 5)) 3 2 at hsmall
    by_contra! h
    have exclude (k : ℕ) (hk : 5 < k) (hf : Primitive (productCandidate k 3 2))
        (hv : p ∣ productCandidate k 3 2) : False := by
      have hle := natDegree_le_of_dvd (hp.dvd_symm hf.2.1 hv) hp.ne_zero
      have hshape := product_shape (n := k) (u := 3) (v := 2) (by decide) (by decide) (by decide) hk
      omega
    have hr : s % 5 = 3 ∨ s % 5 = 4 := by omega
    rcases hr with hr | hr <;> rw [hr] at hsmall
    · exact exclude 8 (by decide) dyadic_triple_example_eight hsmall
    · exact exclude 16 (by decide) dyadic_triple_example_sixteen hsmall
  · intro h
    obtain ⟨hd, hp⟩ := quintic_seed h
    refine ⟨_, hp.2.1, hd, (dvd_dyadic_tail_iff_mod hp.2.1 _ s).2 ?_⟩
    rw [hd]
    exact dvd_rfl

end GF2Sparse
