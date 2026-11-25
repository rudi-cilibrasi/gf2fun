import GF2Sparse.OreMixedOrder
import Mathlib.Combinatorics.Colex

/-! Distinct sets of binary shifts of linearized polynomials give distinct
products before specialization at an Ore root. -/

namespace GF2Sparse

open Polynomial FiniteField

private abbrev K := AlgebraicClosure (ZMod 2)
private noncomputable abbrev F := (frobeniusAlgHom (ZMod 2) K).toLinearMap

/-- The linearized polynomials belonging to constant-one seeds, including
the polynomial X from the unit seed, are multiplicatively independent. -/
theorem linearized_multiset_injective {ι : Type*} (g : ι → BinaryPoly)
    (gi : Function.Injective g) (gc : ∀ i, (g i).coeff 0 = 1) :
    Function.Injective (fun u : Multiset ι => (u.map (fun i => X * oreLift (g i))).prod) := by
  have gn (i : ι) : g i ≠ 0 := fun e => by have := gc i; simp [e] at this
  apply multiset_eq_of_ranked_root_products _ (fun i => (g i).natDegree)
    (fun i => mul_ne_zero X_ne_zero (oreLift_ne_zero (gn i)))
  intro i
  by_cases h : (g i).natDegree = 0
  · refine ⟨0, by simp, fun j _ => ?_⟩
    by_cases hj : (g j).natDegree = 0
    · exact Or.inl (gi (by rw [eq_C_of_natDegree_eq_zero h, eq_C_of_natDegree_eq_zero hj, gc, gc]))
    · exact Or.inr (h ▸ Nat.pos_of_ne_zero hj)
  · obtain ⟨z,hz⟩ := exists_exact_frobenius_annihilator (g i) (gc i)
    have test (j : ι) : aeval z (X * oreLift (g j)) = 0 ↔ g i ∣ g j := by
      rw [map_mul, aeval_X, ← oreLift_frobenius, hz]
    refine ⟨z, (test i).2 dvd_rfl, fun j hroot => ?_⟩
    by_cases hj : (g i).natDegree < (g j).natDegree
    · exact Or.inr hj
    · exact Or.inl (gi (eq_of_monic_of_dvd_of_natDegree_le
        (binary_monic (gn _)) (binary_monic (gn _)) ((test j).1 hroot) (Nat.le_of_not_gt hj)).symm)

private def shiftPositions {ι : Type*} [DecidableEq ι] (s : Finset (ι × ℕ)) (i : ι) : Finset ℕ :=
  (s.filter (fun x => x.1 = i)).image Prod.snd

private theorem mem_shiftPositions {ι : Type*} [DecidableEq ι] (s : Finset (ι × ℕ)) (i : ι) (j : ℕ) :
    j ∈ shiftPositions s i ↔ (i,j) ∈ s := by
  simp only [shiftPositions, Finset.mem_image, Finset.mem_filter, Prod.exists]
  constructor
  · rintro ⟨a,b,⟨hab,rfl⟩,rfl⟩; exact hab
  · exact fun h => ⟨i,j,⟨h,rfl⟩,rfl⟩

/-- Powers indexed by distinct binary digits preserve the ability to recover
a finite set from its product in a multiplicatively independent family. -/
private theorem binary_powers_injective {ι : Type*} (G : ι → BinaryPoly)
    (hi : Function.Injective (fun u : Multiset ι => (u.map G).prod)) :
    Function.Injective (fun s : Finset (ι × ℕ) => ∏ a ∈ s, (G a.1)^(2^a.2)) := by
  classical
  let mult (s : Finset (ι × ℕ)) := ∑ a ∈ s, Multiset.replicate (2^a.2) a.1
  have prod_eq (s : Finset (ι × ℕ)) : ((mult s).map G).prod = ∏ a ∈ s, (G a.1)^(2^a.2) := by
    induction s using Finset.induction_on with
    | empty => simp [mult]
    | insert a s ha ih =>
      rw [show mult (insert a s) = Multiset.replicate (2^a.2) a.1 + mult s from Finset.sum_insert ha,
        Multiset.map_add, Multiset.prod_add, Finset.prod_insert ha, ih]
      simp
  have count_eq (s : Finset (ι × ℕ)) (i : ι) :
      (mult s).count i = ∑ j ∈ shiftPositions s i, 2^j := by
    induction s using Finset.induction_on with
    | empty => simp [mult, shiftPositions]
    | insert a s ha ih =>
      obtain ⟨b,j⟩ := a
      rw [show mult (insert (b,j) s) = Multiset.replicate (2^j) b + mult s from Finset.sum_insert ha,
        Multiset.count_add, ih]
      by_cases h : b = i
      · subst b
        have hp : shiftPositions (insert (i,j) s) i = insert j (shiftPositions s i) := by
          ext l; simp [mem_shiftPositions]
        rw [hp, Finset.sum_insert (fun h => ha ((mem_shiftPositions s i j).1 h))]
        simp
      · have hp : shiftPositions (insert (b,j) s) i = shiftPositions s i := by
          ext l; simp [mem_shiftPositions, Ne.symm h]
        simp [hp, Multiset.count_replicate, h]
  intro s t he
  have same := hi ((prod_eq s).trans (he.trans (prod_eq t).symm))
  ext a
  obtain ⟨i,j⟩ := a
  have hc := congrArg (Multiset.count i) same
  rw [count_eq, count_eq] at hc
  have hp := Finset.geomSum_injective (by decide : 2 ≤ 2) hc
  rw [← mem_shiftPositions s i j, hp, mem_shiftPositions]

/-- A seed of the form Y^j b, with b(0)=1, has linearized polynomial
(X O_b)^(2^j). Products of distinct such pairs determine the complete set
of seed labels and shifts. -/
theorem linearized_shift_products_injective {ι : Type*} (g : ι → BinaryPoly)
    (gi : Function.Injective g) (gc : ∀ i, (g i).coeff 0 = 1) :
    Function.Injective (fun s : Finset (ι × ℕ) =>
      ∏ a ∈ s, (X * oreLift (g a.1))^(2^a.2)) :=
  binary_powers_injective _ (linearized_multiset_injective g gi gc)

/-- Multiplication by a Frobenius shift on the seed raises its linearized
polynomial to the corresponding power of two. -/
theorem linearized_X_pow_mul (j : ℕ) (b : BinaryPoly) :
    X * oreLift (X^j * b) = (X * oreLift b)^(2^j) := by
  apply Polynomial.map_injective (algebraMap (ZMod 2) K) (algebraMap (ZMod 2) K).injective
  apply Polynomial.funext
  intro z
  simp only [eval_map_algebraMap, map_pow, map_mul, aeval_X, ← oreLift_frobenius,
    Module.End.mul_apply, binary_frobenius_pow_apply]

/-- Every finite set of nonzero binary seeds is determined by the product
of the associated linearized polynomials. -/
theorem linearized_set_products_injective :
    Function.Injective (fun s : Finset {g : BinaryPoly // g ≠ 0} =>
      ∏ g ∈ s, X * oreLift g.val) := by
  classical
  let B := {b : BinaryPoly // b.coeff 0 = 1}
  let A := {g : BinaryPoly // g ≠ 0}
  have factors (g : A) : ∃ u : B × ℕ, g.val = X^u.2 * u.1.val := by
    have hf := finiteMultiplicity_of_degree_pos_of_monic (by simp : 0 < (X : BinaryPoly).degree) monic_X g.property
    obtain ⟨b,hg,hb⟩ := hf.exists_eq_pow_mul_and_not_dvd
    have bit : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact ⟨(⟨b,bit _ (fun h => hb (X_dvd_iff.2 h))⟩,_), hg⟩
  choose factor spec using factors
  let label : A ↪ B × ℕ := ⟨factor, fun x y h => Subtype.ext (by rw [spec x, spec y, h])⟩
  have prod_eq (s : Finset A) :
      (∏ a ∈ s.map label, (X * oreLift a.1.val)^(2^a.2)) = ∏ g ∈ s, X * oreLift g.val := by
    rw [Finset.prod_map]
    apply Finset.prod_congr rfl
    intro g _
    change (X * oreLift (factor g).1.val)^(2^(factor g).2) = _
    rw [spec g, linearized_X_pow_mul]
  intro s t h
  apply Finset.map_injective label
  apply linearized_shift_products_injective (fun b : B => b.val) Subtype.val_injective (fun b => b.property)
  exact (prod_eq s).trans (h.trans (prod_eq t).symm)

/-- After cancelling the common power of X, total degree below the
modulus makes specialization faithful on equal-size sets of seeds. -/
theorem seed_sets_eq_of_small_quotient_products {f : BinaryPoly}
    (s t : Finset {g : BinaryPoly // g ≠ 0}) (hcard : s.card = t.card)
    (hs : (∑ g ∈ s, (2^g.val.natDegree-1)) < f.natDegree)
    (ht : (∑ g ∈ t, (2^g.val.natDegree-1)) < f.natDegree)
    (he : (∏ g ∈ s, AdjoinRoot.mk f (oreLift g.val)) = ∏ g ∈ t, AdjoinRoot.mk f (oreLift g.val)) :
    s = t := by
  classical
  let rep (u : Finset {g : BinaryPoly // g ≠ 0}) := ∏ g ∈ u, oreLift g.val
  have deg (u : Finset {g : BinaryPoly // g ≠ 0}) : (rep u).natDegree = ∑ g ∈ u, (2^g.val.natDegree-1) := by
    dsimp only [rep]
    rw [natDegree_prod _ _ (fun g _ => oreLift_ne_zero g.property)]
    exact Finset.sum_congr rfl fun g _ => oreLift_degree g.property
  have he' : AdjoinRoot.mk f (rep s) = AdjoinRoot.mk f (rep t) := by simpa only [rep, map_prod] using he
  have hr : rep s = rep t := by
    by_contra hn
    have hlow := (natDegree_sub_le (rep s) (rep t)).trans_lt (max_lt ((deg s).trans_lt hs) ((deg t).trans_lt ht))
    exact (not_lt_of_ge (natDegree_le_of_dvd (AdjoinRoot.mk_eq_mk.1 he') (sub_ne_zero.2 hn))) hlow
  apply linearized_set_products_injective
  change (∏ g ∈ s, X * oreLift g.val) = ∏ g ∈ t, X * oreLift g.val
  simp only [Finset.prod_mul_distrib, Finset.prod_const]
  change X^s.card * rep s = X^t.card * rep t
  rw [hcard, hr]

end GF2Sparse
