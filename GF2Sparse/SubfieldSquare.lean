import GF2Sparse.SubfieldProducts

/-! A square obtained by applying the same family of scalar translations twice. -/

namespace GF2Sparse

open scoped BigOperators

/-- Off-diagonal factors pair up, leaving the product on the diagonal times a square. -/
theorem translated_pair_product {A R : Type*} [CommMonoid A] [CommMonoid R]
    (s : Finset A) (b : A → R) :
    ∃ c : R, (∏ i ∈ s, ∏ j ∈ s, b (i*j)) = (∏ i ∈ s, b (i^2)) * c^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨(∏ i ∈ s, b (a*i)) * c, ?_⟩
    simp only [Finset.prod_insert ha, Finset.prod_mul_distrib, hc]
    have hswap : (∏ i ∈ s, b (i*a)) = ∏ i ∈ s, b (a*i) :=
      Finset.prod_congr rfl fun i _ => by rw [mul_comm i a]
    rw [hswap]
    simp only [pow_two]
    ac_rfl

/-- If squaring permutes the scalar labels, one additional untwisted product makes
the whole double product a square. This applies to a binary Frobenius orbit. -/
theorem square_of_translated_products {A R : Type*} [CommMonoid A] [CommMonoid R]
    (s : Finset A) (b : A → R) (hs : (∏ i ∈ s, b (i^2)) = ∏ i ∈ s, b i) :
    IsSquare ((∏ i ∈ s, b i) * ∏ i ∈ s, ∏ j ∈ s, b (i*j)) := by
  obtain ⟨c, hc⟩ := translated_pair_product s b
  refine ⟨(∏ i ∈ s, b i) * c, ?_⟩
  rw [hc, hs, pow_two]
  ac_rfl

end GF2Sparse
