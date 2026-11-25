import GF2Sparse.Roots
import Mathlib.Combinatorics.Colex

/-! Detect full multiplicative order by products of binary Frobenius powers. -/

namespace GF2Sparse

variable {M : Type*} [CommMonoid M]

def frobeniusProduct (x : M) (s : Finset ℕ) : M := ∏ i ∈ s, x ^ (2 ^ i)

private theorem range_sum_bits (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
  simpa using Nat.geomSum_eq (show 2 ≤ 2 by decide) n

theorem frobeniusProduct_range (x : M) (n : ℕ) :
    frobeniusProduct x (Finset.range n) = x ^ (2 ^ n - 1) := by
  rw [frobeniusProduct, Finset.prod_pow_eq_pow_sum, range_sum_bits]

private theorem bits_lt_of_ssubset {s : Finset ℕ} {n : ℕ} (hs : s ⊂ Finset.range n) :
    ∑ i ∈ s, 2 ^ i < 2 ^ n - 1 := by
  obtain ⟨j, hj, hjs⟩ := Finset.exists_of_ssubset hs
  rw [← range_sum_bits]
  exact Finset.sum_lt_sum_of_subset hs.subset hj hjs (Nat.two_pow_pos j) (fun _ _ _ => Nat.zero_le _)

/-- No nonempty proper selection of conjugates of a full-order root has product one. -/
theorem frobeniusProduct_ne_one_of_full_order {x : M} {n : ℕ}
    (ho : orderOf x = 2 ^ n - 1) {s : Finset ℕ} (hs : s ⊂ Finset.range n)
    (hne : s.Nonempty) : frobeniusProduct x s ≠ 1 := by
  intro h
  rw [frobeniusProduct, Finset.prod_pow_eq_pow_sum] at h
  have hd := orderOf_dvd_of_pow_eq_one h
  have hpos : 0 < ∑ i ∈ s, 2 ^ i := Finset.sum_pos (fun i _ => Nat.two_pow_pos i) hne
  exact (not_lt_of_ge (Nat.le_of_dvd hpos (ho ▸ hd))) (bits_lt_of_ssubset hs)

/-- Checking products up to half the degree suffices. If a proper subgroup
contains the root, the binary digits of its order or their complement give
a nonempty selection of at most half the indices with product one. -/
theorem order_iff_half_frobeniusProducts {x : M} {n : ℕ} (hn : 0 < n) :
    orderOf x = 2 ^ n - 1 ↔ frobeniusProduct x (Finset.range n) = 1 ∧
    ∀ s ⊆ Finset.range n, s.Nonempty → 2 * s.card ≤ n → frobeniusProduct x s ≠ 1 := by
  have hsize : 0 < 2 ^ n - 1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow hn.ne')
  constructor
  · intro ho
    refine ⟨by rw [frobeniusProduct_range, ← ho, pow_orderOf_eq_one], ?_⟩
    intro s hs hne hhalf
    apply frobeniusProduct_ne_one_of_full_order ho _ hne
    apply (Finset.ssubset_iff_subset_ne).2 ⟨hs, ?_⟩
    rintro rfl
    simp only [Finset.card_range] at hhalf
    omega
  · rintro ⟨hfull, hshort⟩
    have hd := orderOf_dvd_of_pow_eq_one ((frobeniusProduct_range x n).symm.trans hfull)
    have hpos := Nat.pos_of_dvd_of_pos hd hsize
    refine (Nat.le_of_dvd hsize hd).eq_of_not_lt (fun hlt => ?_)
    let s := (orderOf x).bitIndices.toFinset
    have hsum : ∑ i ∈ s, 2 ^ i = orderOf x := Finset.twoPowSum_toFinset_bitIndices _
    have hs : s ⊆ Finset.range n := by
      intro i hi
      have hbit := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.1 hi)
      exact Finset.mem_range.2 ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 (by omega))
    have hne : s.Nonempty := by
      by_contra! he
      simp [he] at hsum
      omega
    have he : frobeniusProduct x s = 1 := by
      rw [frobeniusProduct, Finset.prod_pow_eq_pow_sum, hsum, pow_orderOf_eq_one]
    by_cases hsmall : 2 * s.card ≤ n
    · exact hshort s hs hne hsmall he
    · have hproper : s ≠ Finset.range n := by
        intro heq
        rw [heq, range_sum_bits] at hsum
        omega
      have hcomp := Finset.sdiff_nonempty.2 (fun hc => hproper (Finset.Subset.antisymm hs hc))
      apply hshort _ Finset.sdiff_subset hcomp
      · rw [Finset.card_sdiff_of_subset hs, Finset.card_range]
        omega
      · have hprod := Finset.prod_sdiff (f := fun i => x ^ (2 ^ i)) hs
        change frobeniusProduct x _ * frobeniusProduct x s = frobeniusProduct x _ at hprod
        simpa only [he, hfull, mul_one] using hprod

theorem primitive_iff_half_frobeniusProducts {f : BinaryPoly} (hf : f.Monic) (hn : 0 < f.natDegree) :
    let x := AdjoinRoot.root f
    let n := f.natDegree
    Primitive f ↔ frobeniusProduct x (Finset.range n) = 1 ∧
      ∀ s ⊆ Finset.range n, s.Nonempty → 2 * s.card ≤ n → frobeniusProduct x s ≠ 1 :=
  (show Primitive f ↔ orderOf (AdjoinRoot.root f) = 2 ^ f.natDegree - 1 from
    ⟨fun h => h.2.2, primitive_of_order hf hn⟩).trans (order_iff_half_frobeniusProducts hn)

/-- With r = 0 or 1, these are the even or odd positions below 2m. -/
def alternatingPositions (m r : ℕ) : Finset ℕ :=
  (Finset.range m).map ⟨fun i => 2 * i + r, fun _ _ h => by dsimp at h; omega⟩

@[simp] theorem card_alternatingPositions (m r : ℕ) : (alternatingPositions m r).card = m := by
  simp [alternatingPositions]

private theorem sum_alternatingPositions (m r : ℕ) :
    ∑ i ∈ alternatingPositions m r, 2 ^ i = (∑ i ∈ Finset.range m, 4 ^ i) * 2 ^ r := by
  rw [alternatingPositions, Finset.sum_map, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  change 2 ^ (2 * i + r) = _
  rw [pow_add, pow_mul]
  rfl

private theorem three_sum_four (m : ℕ) : 3 * (∑ i ∈ Finset.range m, 4 ^ i) + 1 = 4 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- At index three, the only nonempty proper products equal to one are the
even-index and odd-index products. Both involve exactly half the indices. -/
theorem frobeniusProduct_eq_one_iff_index_three {x : M} {m : ℕ}
    (ho : 3 * orderOf x = 2 ^ (2 * m) - 1)
    {s : Finset ℕ} (hs : s ⊂ Finset.range (2 * m)) (hne : s.Nonempty) :
    frobeniusProduct x s = 1 ↔ s = alternatingPositions m 0 ∨ s = alternatingPositions m 1 := by
  have hgeom := three_sum_four m
  have ho' : 3 * orderOf x = 4 ^ m - 1 := by simpa only [pow_mul] using ho
  have hsum : ∑ i ∈ Finset.range m, 4 ^ i = orderOf x := by omega
  have hpos : 0 < ∑ i ∈ s, 2 ^ i := Finset.sum_pos (fun i _ => Nat.two_pow_pos i) hne
  rw [frobeniusProduct, Finset.prod_pow_eq_pow_sum, ← orderOf_dvd_iff_pow_eq_one]
  constructor
  · rintro ⟨j, hj⟩
    have hjlt : j < 3 := Nat.lt_of_mul_lt_mul_left (a := orderOf x) (by
      rw [← hj, Nat.mul_comm (orderOf x) 3, ho]
      exact bits_lt_of_ssubset hs)
    have hjne : j ≠ 0 := fun he => hpos.ne' (by simpa only [he, Nat.mul_zero] using hj)
    rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
    · exact Or.inl (Finset.geomSum_injective (by decide : 2 ≤ 2) (by
        simp [sum_alternatingPositions, hj, hsum]))
    · exact Or.inr (Finset.geomSum_injective (by decide : 2 ≤ 2) (by
        simp [sum_alternatingPositions, hj, hsum]))
  · rintro (rfl | rfl) <;> simp [sum_alternatingPositions, hsum]

/-- In every even degree 2m ≥ 4 there is an irreducible polynomial whose
root generates the subgroup of index three. Its first failed product test
therefore uses exactly m conjugates. -/
theorem exists_irreducible_index_three (m : ℕ) (hm : 2 ≤ m) :
    ∃ f : BinaryPoly, f.natDegree = 2 * m ∧ Irreducible f ∧
      3 * orderOf (AdjoinRoot.root f) = 2 ^ (2 * m) - 1 := by
  classical
  let K := GaloisField 2 (2 * m)
  letI : Fintype K := Fintype.ofFinite K
  have hn : 2 * m ≠ 0 := by omega
  have hcard : Nat.card K = 2 ^ (2 * m) := GaloisField.card 2 _ hn
  obtain ⟨u, hu⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α := Kˣ)).1 inferInstance
  have hgen : orderOf (u : K) = 2 ^ (2 * m) - 1 := by
    rw [orderOf_units, hu, Nat.card_units, hcard]
  have h3 : 3 ∣ orderOf (u : K) := by
    rw [hgen, pow_mul]
    exact ⟨∑ i ∈ Finset.range m, 4 ^ i, by change 4 ^ m - 1 = _; have := three_sum_four m; omega⟩
  let x := (u : K) ^ 3
  have ho : 3 * orderOf x = 2 ^ (2 * m) - 1 := by
    rw [show orderOf x = orderOf (u : K) / 3 from orderOf_pow_of_dvd (by decide) h3,
      Nat.mul_div_cancel' h3, hgen]
  have hlarge : 2 ^ m - 1 < orderOf x := by
    have hq : 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide : 0 < 2) hm
    have hmulg := Nat.mul_le_mul_right (2 ^ m) hq
    rw [pow_mul', sq] at ho
    omega
  let f := minpoly (ZMod 2) x
  have hi : Irreducible f := minpoly.irreducible (IsIntegral.of_finite (ZMod 2) x)
  have hz : Polynomial.aeval x f = 0 := minpoly.aeval _ _
  have hd : f.natDegree ∣ 2 * m := (degree_dvd_iff_frobenius hi hz _).2 (by
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x)
  have hgt : m < f.natDegree := by
    by_contra! hsmall
    have hle := order_le_of_aeval (pow_ne_zero 3 u.ne_zero) hi.ne_zero hz
    have hbound := Nat.pow_le_pow_right (by decide : 0 < 2) hsmall
    change orderOf x ≤ _ at hle
    omega
  refine ⟨f, (Nat.eq_of_dvd_of_lt_two_mul hn hd (by omega)).symm, hi, ?_⟩
  rwa [← orderOf_root_at hi hz]

theorem exists_irreducible_first_failure_at_half (m : ℕ) (hm : 2 ≤ m) :
    ∃ f : BinaryPoly, f.natDegree = 2 * m ∧ Irreducible f ∧ ¬ Primitive f ∧
      (∀ s ⊆ Finset.range (2 * m), s.Nonempty → s.card < m →
        frobeniusProduct (AdjoinRoot.root f) s ≠ 1) ∧
      ∃ s ⊆ Finset.range (2 * m), s.card = m ∧ frobeniusProduct (AdjoinRoot.root f) s = 1 := by
  obtain ⟨f, hn, hi, ho⟩ := exists_irreducible_index_three m hm
  refine ⟨f, hn, hi, ?_, ?_, ?_⟩
  · intro hp
    rw [hp.2.2, hn] at ho
    have := Nat.one_lt_two_pow (show 2 * m ≠ 0 by omega)
    omega
  · intro s hs hne hlen hprod
    have hproper : s ⊂ Finset.range (2 * m) := Finset.ssubset_iff_subset_ne.2 ⟨hs, by
      rintro rfl; simp only [Finset.card_range] at hlen; omega⟩
    rcases (frobeniusProduct_eq_one_iff_index_three ho hproper hne).1 hprod with rfl | rfl <;>
      simp at hlen
  · let s := alternatingPositions m 0
    have hcard : s.card = m := card_alternatingPositions _ _
    have hs : s ⊆ Finset.range (2 * m) := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
      have hj' := Finset.mem_range.1 hj
      exact Finset.mem_range.2 (show 2 * j + 0 < 2 * m by omega)
    have hproper : s ⊂ Finset.range (2 * m) := Finset.ssubset_iff_subset_ne.2 ⟨hs, by
      intro he; rw [he, Finset.card_range] at hcard; omega⟩
    exact ⟨s, hs, hcard, (frobeniusProduct_eq_one_iff_index_three ho hproper
      (Finset.card_pos.1 (by omega))).2 (Or.inl rfl)⟩

end GF2Sparse
