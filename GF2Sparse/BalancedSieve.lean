import GF2Sparse.OrderBound

/-! Distribute the orders of the small binary fields between the two exponents of a product pentanomial. -/

namespace GF2Sparse

open Polynomial

/-- Each small degree may use either exponent to make a binomial vanish. -/
theorem product_no_small_factor_split {B n u v : ℕ} (hn : 0 < n) (hu : 0 < u) (hv : 0 < v)
    (cover : ∀ d, 0 < d → d ≤ B → (2^d-1 ∣ u) ∨ (2^d-1 ∣ v))
    {p : BinaryPoly} (hp : Irreducible p) (hd : p.natDegree ≤ B) :
    ¬ p ∣ productCandidate n u v := by
  letI : Fact (Irreducible p) := ⟨hp⟩
  intro h
  have hc : (productCandidate n u v).coeff 0 = 1 := by
    simp [productCandidate, coeff_X_pow, hn.ne, hu.ne, hv.ne]
  have hx := root_ne_zero_of_factor hp h hc
  letI : Fintype (AdjoinRoot p) := Fintype.ofEquiv _ (AdjoinRoot.powerBasisAux hp.ne_zero).equivFun.toEquiv.symm
  have hpw := FiniteField.pow_card_sub_one_eq_one _ hx
  rw [card_adjoinRoot hp.ne_zero] at hpw
  have htwo : (1 : AdjoinRoot p)+1 = 0 := by
    simpa using congrArg (AdjoinRoot.of p) (show (1 : ZMod 2)+1 = 0 by decide)
  have he := AdjoinRoot.mk_eq_zero.2 h
  rcases cover p.natDegree hp.natDegree_pos hd with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;>
    simp [productCandidate, pow_mul, hpw, htwo, hx] at he

/-- The same polynomial realizes the stated factor-degree and multiplicative-order bounds. -/
theorem split_sieve_candidate {B n u v : ℕ} (hu : Odd u) (hv : Even v) (hv0 : 0 < v)
    (htop : u+v < n) (cover : ∀ d, 0 < d → d ≤ B → (2^d-1 ∣ u) ∨ (2^d-1 ∣ v)) :
    let f := productCandidate n u v
    f.natDegree = n ∧ f.support.card = 5 ∧ Squarefree f ∧
    (∀ p : BinaryPoly, Irreducible p → p ∣ f → B < p.natDegree) ∧
    n^2 ≤ 2*(u+v)*orderOf (AdjoinRoot.root f) := by
  have hu0 : 0 < u := by obtain ⟨k,hk⟩ := hu; omega
  have huv : u ≠ v := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hu) hv
  obtain ⟨hd, hw⟩ := product_shape hu0 hv0 huv htop
  refine ⟨hd, hw, (product_separable (by omega) hu hv hv0).squarefree, ?_,
    product_order_quadratic hu0 hv0 huv htop⟩
  intro p hp hpf
  exact lt_of_not_ge fun hle => product_no_small_factor_split (by omega) hu0 hv0 cover hp hle hpf

/-- For every degree from 168, these two fixed taps exclude all factors through degree five. -/
theorem split_sieve_five {n : ℕ} (hn : 168 ≤ n) :
    let f := productCandidate n 105 62
    f.natDegree = n ∧ f.support.card = 5 ∧ Squarefree f ∧
    (∀ p : BinaryPoly, Irreducible p → p ∣ f → 5 < p.natDegree) ∧
    n^2 ≤ 334*orderOf (AdjoinRoot.root f) := by
  apply split_sieve_candidate (by decide) (by decide) (by decide) (by omega)
  intro d hpos hle
  interval_cases d <;> decide

end GF2Sparse
