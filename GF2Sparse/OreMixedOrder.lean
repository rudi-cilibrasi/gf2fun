import GF2Sparse.OreOrder

/-! Products of linearized quotients from different seed degrees remain independent.
An exact Frobenius annihilator distinguishes a generator of maximal degree in
any proposed product relation. -/

namespace GF2Sparse

open Polynomial FiniteField

private abbrev K := AlgebraicClosure (ZMod 2)
private noncomputable abbrev F := (frobeniusAlgHom (ZMod 2) K).toLinearMap

private theorem product_vanishes {ι : Type*} (G : ι → BinaryPoly) (z : K) (s : Multiset ι) :
    aeval z ((s.map G).prod) = 0 ↔ ∃ i ∈ s, aeval z (G i) = 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons i s ih => simp [ih, mul_eq_zero]

private theorem products_equal {ι : Type*} (G : ι → BinaryPoly) (rank : ι → ℕ)
    (hn : ∀ i, G i ≠ 0)
    (mark : ∀ i, ∃ z : K, aeval z (G i) = 0 ∧
      ∀ j, aeval z (G j) = 0 → i = j ∨ rank i < rank j)
    (s t : Multiset ι) (he : (s.map G).prod = (t.map G).prod) : s = t := by
  classical
  by_cases hst : s+t = 0
  · have h := congrArg Multiset.card hst
    simp only [Multiset.card_add, Multiset.card_zero] at h
    exact (Multiset.card_eq_zero.1 (by omega : s.card = 0)).trans
      (Multiset.card_eq_zero.1 (by omega : t.card = 0)).symm
  obtain ⟨i, hi, hmax⟩ := (s+t).toFinset.exists_max_image rank (Multiset.toFinset_nonempty.2 hst)
  obtain ⟨z, hz, hmark⟩ := mark i
  have detect (u : Multiset ι) (hu : ∀ j ∈ u, j ∈ s+t) :
      aeval z ((u.map G).prod) = 0 ↔ i ∈ u := by
    rw [product_vanishes]
    constructor
    · rintro ⟨j,hj,hzj⟩
      have hij := (hmark j hzj).resolve_right (not_lt_of_ge (hmax j (Multiset.mem_toFinset.2 (hu j hj))))
      simpa [hij] using hj
    · exact fun h => ⟨i,h,hz⟩
  have iffmem : i ∈ s ↔ i ∈ t := by
    rw [← detect s (fun _ h => Multiset.mem_add.2 (Or.inl h)), he,
      detect t (fun _ h => Multiset.mem_add.2 (Or.inr h))]
  have hs : i ∈ s := (Multiset.mem_add.1 (Multiset.mem_toFinset.1 hi)).elim id iffmem.mpr
  have ht := iffmem.mp hs
  have hc : ((s.erase i).map G).prod = ((t.erase i).map G).prod := by
    rw [← Multiset.cons_erase hs, ← Multiset.cons_erase ht] at he
    simp only [Multiset.map_cons, Multiset.prod_cons] at he
    exact mul_left_cancel₀ (hn i) he
  have hst' := products_equal G rank hn mark (s.erase i) (t.erase i) hc
  rw [← Multiset.cons_erase hs, ← Multiset.cons_erase ht, hst']
termination_by s.card + t.card
decreasing_by
  classical
  rw [Multiset.card_erase_of_mem hs, Multiset.card_erase_of_mem ht]
  have h₁ := (Multiset.card_pos.2 (by rintro e; simp [e] at hs) : 0 < s.card)
  have h₂ := (Multiset.card_pos.2 (by rintro e; simp [e] at ht) : 0 < t.card)
  simp only [Nat.pred_eq_sub_one]
  omega

/-- Adjoin X to the linearized quotients of distinct, positive-degree,
constant-one seeds. The resulting family is multiplicatively independent. -/
theorem oreLift_multiset_injective {ι : Type*} (g : ι → BinaryPoly) (gi : Function.Injective g)
    (gc : ∀ i, (g i).coeff 0 = 1) (gd : ∀ i, 0 < (g i).natDegree) :
    Function.Injective (fun u : Multiset (Option ι) =>
      (u.map (fun j => j.elim X (fun i => oreLift (g i)))).prod) := by
  let G : Option ι → BinaryPoly := fun j => j.elim X (fun i => oreLift (g i))
  let rank : Option ι → ℕ := fun j => j.elim 0 (fun i => (g i).natDegree)
  have gn (i : ι) : g i ≠ 0 := fun e => by have := gc i; simp [e] at this
  apply products_equal G rank
  · intro i
    cases i with
    | none => exact X_ne_zero
    | some i => exact oreLift_ne_zero (gn i)
  intro i
  cases i with
  | none =>
    refine ⟨0, by simp [G], ?_⟩
    intro j hj
    cases j with
    | none => exact Or.inl rfl
    | some j => exact Or.inr (gd j)
  | some i =>
    obtain ⟨z, hz⟩ := exists_exact_frobenius_annihilator (g i) (gc i)
    have hz0 : z ≠ 0 := by
      rintro rfl
      have hl := natDegree_le_of_dvd ((hz 1).1 (map_zero _)) (one_ne_zero : (1:BinaryPoly) ≠ 0)
      rw [natDegree_one] at hl
      exact (not_lt_of_ge hl) (gd i)
    have root (j : ι) : aeval z (oreLift (g j)) = 0 ↔ g i ∣ g j := by
      rw [← mul_eq_zero_iff_left hz0, ← oreLift_frobenius, hz]
    refine ⟨z, (root i).2 dvd_rfl, ?_⟩
    intro j hj
    cases j with
    | none => exact (hz0 (by simpa [G] using hj)).elim
    | some j =>
      have hd := (root j).1 hj
      by_cases h : (g i).natDegree < (g j).natDegree
      · exact Or.inr h
      · exact Or.inl (congrArg some (gi (eq_of_monic_of_dvd_of_natDegree_le
          (binary_monic (gn _)) (binary_monic (gn _)) hd (Nat.le_of_not_gt h)).symm))

/-- Every injective family of multisets whose polynomial products have
degree below the lifted degree gives that many distinct root powers. -/
theorem Primitive.oreLift_order_multisets {p : BinaryPoly} (hp : Primitive p)
    {ι σ : Type*} [Fintype σ] (g : ι → BinaryPoly) (gi : Function.Injective g)
    (gc : ∀ i, (g i).coeff 0 = 1) (gd : ∀ i, 0 < (g i).natDegree) (hv : ∀ i, ¬ p ∣ g i)
    (m : σ → Multiset (Option ι)) (hm : Function.Injective m)
    (hd : ∀ a, ((m a).map (fun j => j.elim 1 (fun i => 2^(g i).natDegree-1))).sum <
      2^p.natDegree-1) : Fintype.card σ ≤ orderOf (AdjoinRoot.root (oreLift p)) := by
  let G : Option ι → BinaryPoly := fun j => j.elim X (fun i => oreLift (g i))
  have gp : ∀ j, ∃ e : ℕ, AdjoinRoot.mk (oreLift p) (G j) = AdjoinRoot.root (oreLift p)^e
    | none => ⟨1, by simp [G]⟩
    | some i => hp.oreLift_value_is_power (hv i)
  choose e he using gp
  apply order_ge_of_representatives ((oreLift_constant p).trans hp.coeff_zero_eq_one)
    (fun a => ((m a).map G).prod) (fun a => ((m a).map e).sum)
    ((oreLift_multiset_injective g gi gc gd).comp hm)
  · intro a
    apply (natDegree_multiset_prod_le _).trans_lt
    rw [oreLift_degree hp.2.1.ne_zero, Multiset.map_map]
    have weights : natDegree ∘ G = (fun j : Option ι => j.elim 1 (fun i => 2^(g i).natDegree-1)) := by
      funext j
      cases j with
      | none => exact natDegree_X
      | some i => exact oreLift_degree (fun e => by have := gc i; simp [e] at this)
    rw [weights]
    exact hd a
  · intro a
    generalize m a = u
    induction u using Multiset.induction_on with
    | empty => simp
    | cons j u ih => simp [he, ih, pow_add]

end GF2Sparse
