import GF2Sparse.ShortProducts
import GF2Sparse.CompositionNorm

/-! Products of fewer than s binary linear functions sum to zero on the s-cube.
Apply this to the nonzero roots of an irreducible linearized quotient. -/

namespace GF2Sparse

open Polynomial FiniteField

private abbrev K := AlgebraicClosure (ZMod 2)

/-- Each monomial in a product of k linear forms misses a binary coordinate when k < s. -/
theorem sum_cube_linear_products {E : Type*} [Field E] [Algebra (ZMod 2) E] [CharP E 2]
    {s k : ℕ} (hk : k < s) (A : Fin k → Fin s → E) :
    ∑ c : Fin s → ZMod 2, ∏ i, ∑ j, c j • A i j = 0 := by
  classical
  simp_rw [Fintype.prod_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro f _
  obtain ⟨j, hj⟩ : ∃ j : Fin s, ∀ i, f i ≠ j := by
    by_contra! hf
    have hh := Fintype.card_le_of_surjective f hf
    simp only [Fintype.card_fin] at hh
    omega
  apply Finset.sum_ninvolution (fun c : Fin s → ZMod 2 => c + Pi.single j 1)
  · intro c
    have he (i : Fin k) : (c + Pi.single j 1 : Fin s → ZMod 2) (f i) = c (f i) := by
      simp [Pi.single_eq_of_ne (hj i)]
    simp only [he, CharTwo.add_self_eq_zero]
  · intro c _ h
    have hh := congrFun h j
    simp at hh
  · simp
  · intro c
    ext i
    by_cases hi : i = j <;> simp [hi, add_assoc, CharTwo.add_self_eq_zero]

/-- All roots of an irreducible binary polynomial are Frobenius powers of any one root. -/
theorem exists_frobenius_root {f : BinaryPoly} (hf : Irreducible f) {r z : K}
    (hr : aeval r f = 0) (hz : aeval z f = 0) : ∃ a : ℕ, z = r ^ (2^a) := by
  classical
  let orb (a : Fin f.natDegree) : f.rootSet K := ⟨r ^ (2^a.val), (mem_rootSet_of_ne hf.ne_zero).2
    (by rw [aeval_dyadic, hr, zero_pow (Nat.two_pow_pos _).ne'])⟩
  have hi : Function.Injective orb := by
    intro a b h
    apply relative_frobenius_conjugates_injective hf hr (r := 1) (m := f.natDegree) (by decide) (by simp)
    simpa only [one_mul] using congrArg Subtype.val h
  have hc : Fintype.card (Fin f.natDegree) = Fintype.card (f.rootSet K) := by
    rw [Fintype.card_fin, card_rootSet_eq_natDegree (PerfectField.separable_of_irreducible hf)
      (IsAlgClosed.splits _)]
  obtain ⟨i, hi⟩ := ((Fintype.bijective_iff_injective_and_card orb).2 ⟨hi, hc⟩).2
    ⟨z, (mem_rootSet_of_ne hf.ne_zero).2 hz⟩
  exact ⟨i.val, (congrArg Subtype.val hi).symm⟩

/-- A binary s-cube whose nonzero points are roots rules out all products shorter than s. -/
theorem no_short_products_of_binary_cube {f : BinaryPoly} (hf : Irreducible f) {s k : ℕ}
    (v : Fin s → K) (hv : ∀ c : Fin s → ZMod 2, c ≠ 0 → aeval (∑ j, c j • v j) f = 0)
    (hk : k < s) : NoShortRootProducts k f := by
  classical
  intro d hd hdk z hz he
  let i₀ : Fin d := ⟨0, hd⟩
  let r := z i₀
  choose a ha using fun i => exists_frobenius_root hf (hz i₀) (hz i)
  let F := (frobeniusAlgHom (ZMod 2) K).toLinearMap
  let H (y : K) := ∏ i, (F ^ a i) y
  have hH (y : K) : H y = ∏ i, y ^ (2 ^ a i) := by simp only [H, F, binary_frobenius_pow_apply]
  have hbase : H r = 1 := by simpa only [hH, r, ← ha] using he
  have hval (c : Fin s → ZMod 2) : H (∑ j, c j • v j) = if c = 0 then 0 else 1 := by
    split_ifs with hc
    · subst c
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, H, map_zero]
      exact Finset.prod_eq_zero (Finset.mem_univ i₀) rfl
    · obtain ⟨t, ht⟩ := exists_frobenius_root hf (hz i₀) (hv c hc)
      change (∑ j, c j • v j) = r ^ (2^t) at ht
      rw [ht, hH]
      simp_rw [pow_right_comm r (2^t)]
      rw [Finset.prod_pow, ← hH, hbase, one_pow]
  have hsum : ∑ c : Fin s → ZMod 2, H (∑ j, c j • v j) = 0 := by
    simpa only [H, map_sum, map_smul] using
      sum_cube_linear_products (lt_of_le_of_lt hdk hk) (fun i j => (F ^ a i) (v j))
  have hs : 0 < s := by omega
  have hite (c : Fin s → ZMod 2) : (if c = 0 then (0 : K) else 1) =
      1 - (if c = 0 then 1 else 0) := by split <;> simp [*]
  simp_rw [hval, hite] at hsum
  simp [Finset.sum_sub_distrib, Fintype.card_pi, ZMod.card, CharTwo.two_eq_zero,
    zero_pow hs.ne'] at hsum

private theorem root_iff_linearized {s a : ℕ} {x : K} (hx : x ≠ 0) :
    aeval x (trinomial (2^s-1) (2^a-1)) = 0 ↔ x^(2^s) = x^(2^a) + x := by
  simp only [trinomial, map_add, map_pow, aeval_X, map_one, CharTwo.add_eq_zero]
  have hm (t : ℕ) : x^(2^t-1) * x = x^(2^t) := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.two_pow_pos t)]
  constructor
  · intro h
    simpa only [add_mul, one_mul, hm] using congrArg (· * x) h
  · intro h
    apply mul_right_cancel₀ hx
    rwa [add_mul, one_mul, hm, hm]

/-- For any irreducible Ore lift of a trinomial, the first s-1 root-product tests pass. -/
theorem irreducible_linearized_trinomial_tests {s a k : ℕ} (ha : 0 < a) (has : a < s)
    (hf : Irreducible (trinomial (2^s-1) (2^a-1))) (hk : k < s) :
    NoShortRootProducts k (trinomial (2^s-1) (2^a-1)) := by
  classical
  let f := trinomial (2^s-1) (2^a-1)
  have hpa := Nat.one_lt_two_pow ha.ne'
  have hlt := Nat.pow_lt_pow_right (by decide : 1 < 2) has
  have hdeg : f.natDegree = 2^s-1 := trinomial_degree (by omega) (by omega)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero K f (ne_of_gt hf.degree_pos)
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp [f, trinomial, zero_pow (by omega : 2^a-1 ≠ 0), zero_pow (by omega : 2^s-1 ≠ 0)] at hr
  have hmin : (minpoly (ZMod 2) r).natDegree = 2^s-1 := by
    rw [← minpoly.eq_of_irreducible_of_monic hf hr (binary_monic hf.ne_zero)]; exact hdeg
  let v (j : Fin s) := r ^ (2 ^ j.val)
  have hdeg2 : 2 ^ (s-1) * 2 = 2^s := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hlarge := Nat.one_lt_two_pow (show s-1 ≠ 0 by omega)
  let ix (j : Fin s) : Fin (minpoly (ZMod 2) r).natDegree := ⟨2^j.val, by
    rw [hmin]
    have hj := Nat.pow_le_pow_right (by decide : 0 < 2) (show j.val ≤ s-1 by omega)
    omega⟩
  have hv : LinearIndependent (ZMod 2) v := (linearIndependent_pow r).comp ix
    (fun i j h => Fin.ext (Nat.pow_right_injective (by decide : 2 ≤ 2) (congrArg Fin.val h)))
  let F := (frobeniusAlgHom (ZMod 2) K).toLinearMap
  let L := F ^ s - F ^ a - 1
  have hker (x : K) : L x = 0 ↔ x^(2^s) = x^(2^a) + x := by
    simp only [L, F, LinearMap.sub_apply, binary_frobenius_pow_apply, Module.End.one_apply,
      sub_eq_iff_eq_add, add_zero, add_comm]
  have hvL (j : Fin s) : L (v j) = 0 := by
    apply (hker _).2
    apply (root_iff_linearized (pow_ne_zero _ hr0)).1
    change aeval (r ^ (2 ^ j.val)) f = 0
    rw [aeval_dyadic, hr, zero_pow (Nat.two_pow_pos _).ne']
  apply no_short_products_of_binary_cube hf v _ hk
  intro c hc
  have hnz : ∑ j, c j • v j ≠ 0 := fun h => hc (funext (Fintype.linearIndependent_iff.1 hv c h))
  apply (root_iff_linearized hnz).2
  apply (hker _).1
  simp only [map_sum, map_smul, hvL, smul_zero, Finset.sum_const_zero]

theorem trinomial_mersenne_127_tests : NoShortRootProducts 126 (trinomial (2^127-1) 1) :=
  irreducible_linearized_trinomial_tests (s := 127) (a := 1) (by decide) (by decide)
    irreducible_trinomial_mersenne_127 (by decide)

/-- Cubing the roots preserves the short-product bound in an odd degree. -/
theorem sampled_block_tests_of_irreducible {u k : ℕ} (hu : 0 < u) (ho : Odd (3*u+1))
    (hf : Irreducible (trinomial (3*u+1) 1)) (hpass : NoShortRootProducts k (trinomial (3*u+1) 1)) :
    NoShortRootProducts k (sampledBlock 0 1 u 3) := by
  classical
  intro d hd hdk z hz hunit
  choose r hc hr using fun i => trinomial_root_of_cubic_sample (hz i)
  let n := 3*u+1
  have hdeg : (trinomial (3*u+1) 1).natDegree = n := trinomial_degree (by decide) (by omega)
  have hfix (i : Fin d) : (r i) ^ (2^n) = r i :=
    (degree_dvd_iff_frobenius hf (hr i) n).1 (hdeg ▸ dvd_rfl)
  let q := ∏ i, r i
  have hc3 : q^3 = 1 := by simp only [q, ← Finset.prod_pow, hc, hunit]
  have hq : q ≠ 0 := by rintro he; simp [he] at hc3
  have hqn : q ^ (2^n-1) = 1 := by
    apply mul_right_cancel₀ hq
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel (Nat.two_pow_pos n)]
    simp only [q, ← Finset.prod_pow, hfix]
  have hdiv := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hqn) (orderOf_dvd_of_pow_eq_one hc3)
  rw [((mersenne_coprime_three_iff_odd n).2 ho).gcd_eq_one] at hdiv
  exact hpass d hd hdk r hr (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_one hdiv))

theorem pentanomial_mersenne_127_tests :
    NoShortRootProducts 126 (sampledBlock 0 1 ((2^127-2)/3) 3) :=
  sampled_block_tests_of_irreducible (by decide) (by decide) irreducible_trinomial_mersenne_127
    trinomial_mersenne_127_tests

end GF2Sparse
