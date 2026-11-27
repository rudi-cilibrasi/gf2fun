import GF2Sparse.ConjugateProducts
import GF2Sparse.RootProducts

/-! Conjugate products after adjoining a root of unity, and binary words with
complementary halves. -/

namespace GF2Sparse.MiddleRank

open scoped Pointwise

/-- For independent coordinates, adjoining a set containing u, 1/u and 1/u²
preserves the product-one test at every length at least two. -/
theorem product_one_after_twist {M G : Type*} [Monoid M] [Group G]
    (s : Set M) (t : Set G) {u : G} (hu : u ∈ t) (hi : u⁻¹ ∈ t)
    (hii : (u*u)⁻¹ ∈ t) {k : ℕ} (hk : 2 ≤ k) :
    (1 : M × G) ∈ (s ×ˢ t)^k ↔ (1 : M) ∈ s^k := by
  have pair : (1 : G) ∈ t^2 := by
    simpa [pow_two] using Set.mul_mem_mul hu hi
  have triple : (1 : G) ∈ t^3 := by
    simpa [pow_succ, pow_two, mul_assoc] using
      Set.mul_mem_mul (Set.mul_mem_mul hu hu) hii
  have all (j : ℕ) : (1 : G) ∈ t^(j+2) := by
    induction j using Nat.twoStepInduction with
    | zero => exact pair
    | one => exact triple
    | more j ih _ =>
      simpa only [pow_add, one_mul] using
        (Set.mul_mem_mul ih pair : (1 : G)*1 ∈ t^(j+2) * t^2)
  have ht : (1 : G) ∈ t^k := by simpa [Nat.sub_add_cancel hk] using all (k-2)
  rw [Set.prod_pow]
  exact ⟨fun h => h.1, fun h => ⟨h, ht⟩⟩

/-- Every nonzero multiple of 2^m−1 below 2^(2m)−1 has m ones. The high half of
the word is the binary complement of the low half. -/
theorem weight_of_complementary_halves {m a : ℕ} (ha : a < 2^m) :
    ((a+1)*(2^m-1)).bitIndices.toFinset.card = m := by
  classical
  let high := a.bitIndices.toFinset
  have sub : high ⊆ Finset.range m := by
    intro i hi
    have h := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hi)
    exact Finset.mem_range.mpr ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (h.trans_lt ha))
  let shift : ℕ ↪ ℕ := ⟨fun i => m+i, fun _ _ h => Nat.add_left_cancel h⟩
  let low := Finset.range m \ high
  have separate : Disjoint low (high.map shift) := by
    refine Finset.disjoint_left.mpr ?_
    intro i hi hm
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hm
    have := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
    change m+j < m at this
    omega
  have fieldsum : ∑ i ∈ Finset.range m, 2^i = 2^m-1 := by
    simpa using Nat.geomSum_eq (show 2 ≤ 2 by decide) m
  have highsum : ∑ i ∈ high, 2^i = a := Finset.twoPowSum_toFinset_bitIndices _
  have lowsum : (∑ i ∈ low, 2^i) + a = 2^m-1 := by
    change (∑ i ∈ Finset.range m \ high, 2^i) + a = 2^m-1
    rw [← highsum, ← fieldsum]
    exact Finset.sum_sdiff sub
  have shifted : ∑ i ∈ high.map shift, 2^i = 2^m*a := by
    simp [shift, pow_add, ← Finset.mul_sum, highsum]
  have word : ∑ i ∈ low ∪ high.map shift, 2^i = (a+1)*(2^m-1) := by
    rw [Finset.sum_union separate, shifted]
    have pos := Nat.two_pow_pos m
    have step : 2^m-1+1 = 2^m := by omega
    calc
      _ = (∑ i ∈ low, 2^i) + (2^m-1+1)*a := by rw [step]
      _ = _ := by rw [Nat.add_mul, Nat.one_mul]; nlinarith only [lowsum]
  rw [← word, Finset.toFinset_bitIndices_twoPowSum, Finset.card_union_of_disjoint separate,
    Finset.card_map, Finset.card_sdiff_of_subset sub, Finset.card_range]
  have := Finset.card_le_card sub
  simp only [Finset.card_range] at this
  omega

end GF2Sparse.MiddleRank
