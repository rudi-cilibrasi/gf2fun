import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.List.GetD

/-! A sharp bound for prescribed products of polynomial evaluations on
disjoint groups of nodes. The nodes in an individual group may repeat. -/

namespace GF2Sparse

open Polynomial

variable {K : Type*} [Field K] {k : ℕ}

private theorem separating_evaluation [Infinite K] {I : Type*} [Fintype I]
    (H : I → K[X]) (hH : Function.Injective H) :
    ∃ x : K, Function.Injective (fun i => (H i).eval x) := by
  classical
  let forbidden := (Finset.univ : Finset (I × I)).biUnion
    (fun ij => (H ij.1 - H ij.2).roots.toFinset)
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset forbidden
  refine ⟨x, fun i j hij => ?_⟩
  by_contra hne
  apply hx
  apply Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, ?_⟩
  apply Multiset.mem_toFinset.2
  apply (mem_roots (sub_ne_zero.2 (hH.ne hne))).2
  simpa [IsRoot, eval_sub] using sub_eq_zero.2 hij

private theorem eval_monic_interpolate {H : K[X]} (hH : H.Monic) (hd : H.natDegree = k)
    (v : Fin k → K) (hv : Function.Injective v) (x : K) :
    H.eval x = x ^ k + ∑ j, ((H.eval (v j) - v j ^ k) *
      (Lagrange.basis Finset.univ v j).eval x) := by
  classical
  have hdeg : H.degree = (k : ℕ) := by rw [degree_eq_natDegree hH.ne_zero, hd]
  have hlt : (H - X ^ k).degree < ((Finset.univ : Finset (Fin k)).card : WithBot ℕ) := by
    simpa only [Finset.card_univ, Fintype.card_fin, ← hdeg] using
      (degree_sub_lt (p := H) (q := X ^ k) (by simpa using hdeg)
        hH.ne_zero (by simp [hH.leadingCoeff]))
  have e := congrArg (eval x) (Lagrange.eq_interpolate hv.injOn hlt)
  simp only [Lagrange.interpolate_apply, eval_sub, eval_pow, eval_X, eval_finset_sum,
    eval_mul, eval_C] at e
  linear_combination e

private abbrev PrefixIndex (d : Fin k → ℕ) := (j : Fin k) → Fin (d j + 1)

private def prefixWeight (a : Fin k → ℕ → K) (H : K[X]) {d : Fin k → ℕ}
    (b : PrefixIndex d) : K :=
  ∏ j, ∏ i ∈ Finset.range (b j).val, H.eval (a j i)

private def nextPrefix {d : Fin k → ℕ} (b : PrefixIndex d) (j : Fin k) : PrefixIndex d :=
  Function.update b j (if h : (b j).val < d j then ⟨(b j).val + 1, by omega⟩ else 0)

private def prefixMultiplier {d : Fin k → ℕ} (b : PrefixIndex d) (j : Fin k)
    (target : Fin k → K) : K := if (b j).val < d j then 1 else target j

private theorem prefix_advance (a : Fin k → ℕ → K) (H : K[X]) {d : Fin k → ℕ}
    (target : Fin k → K) (hprod : ∀ j, ∏ i ∈ Finset.range (d j + 1), H.eval (a j i) = target j)
    (b : PrefixIndex d) (j : Fin k) :
    H.eval (a j (b j)) * prefixWeight a H b =
      prefixMultiplier b j target * prefixWeight a H (nextPrefix b j) := by
  classical
  let w (i : Fin k) (n : ℕ) := ∏ l ∈ Finset.range n, H.eval (a i l)
  have hout : (∏ i ∈ Finset.univ.erase j, w i ((nextPrefix b j) i)) =
      ∏ i ∈ Finset.univ.erase j, w i (b i) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [nextPrefix, Function.update_of_ne (Finset.mem_erase.1 hi).1]
  have hlocal : H.eval (a j (b j)) * w j (b j) =
      prefixMultiplier b j target * w j ((nextPrefix b j) j) := by
    by_cases h : (b j).val < d j
    · simp [nextPrefix, prefixMultiplier, h, w, Finset.prod_range_succ, mul_comm]
    · have he : (b j).val = d j := by have := (b j).isLt; omega
      simp [nextPrefix, prefixMultiplier, he, w]
      rw [← hprod j, Finset.prod_range_succ, mul_comm]
  change _ * (∏ i, w i (b i)) = _ * ∏ i, w i ((nextPrefix b j) i)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ (fun i => w i ((nextPrefix b j) i)) (Finset.mem_univ j),
    hout, ← mul_assoc, hlocal, mul_assoc]

/-- If every group j of d(j)+1 evaluation nodes prescribes the product
of the evaluations, at most ∏ j, (d(j)+1) distinct monic degree-k
polynomials realize the prescriptions. Different groups have disjoint nodes. -/
theorem card_prescribed_evaluation_products [Infinite K] {I : Type*} [Fintype I]
    (d : Fin k → ℕ) (a : Fin k → ℕ → K) (target : Fin k → K)
    (hsep : ∀ (b : (j : Fin k) → Fin (d j + 1)), Function.Injective (fun j => a j (b j)))
    (H : I → K[X]) (hinj : Function.Injective H) (hm : ∀ t, (H t).Monic)
    (hd : ∀ t, (H t).natDegree = k)
    (hprod : ∀ t j, ∏ i ∈ Finset.range (d j + 1), (H t).eval (a j i) = target j) :
    Fintype.card I ≤ ∏ j, (d j + 1) := by
  classical
  obtain ⟨x, hx⟩ := separating_evaluation H hinj
  let node (b : PrefixIndex d) (j : Fin k) := a j (b j)
  let L (b : PrefixIndex d) (j : Fin k) := (Lagrange.basis Finset.univ (node b) j).eval x
  let W (t : I) (b : PrefixIndex d) := prefixWeight a (H t) b
  let M : Module.End K (PrefixIndex d → K) := LinearMap.pi fun b =>
    (x ^ k - ∑ j, L b j * node b j ^ k) • LinearMap.proj b +
      ∑ j, (L b j * prefixMultiplier b j target) • LinearMap.proj (nextPrefix b j)
  have heig (t : I) : M.HasEigenvector ((H t).eval x) (W t) := by
    refine ⟨Module.End.mem_eigenspace_iff.2 ?_, ?_⟩
    · ext b
      change (M (W t)) b = (H t).eval x * W t b
      simp only [M, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.proj_apply, LinearMap.sum_apply, smul_eq_mul]
      have hav (j : Fin k) := prefix_advance a (H t) target (hprod t) b j
      change ∀ j, (H t).eval (node b j) * W t b =
        prefixMultiplier b j target * W t (nextPrefix b j) at hav
      rw [eval_monic_interpolate (hm t) (hd t) (node b) (hsep b) x]
      change (x^k - ∑ j, L b j * node b j ^ k) * W t b +
        ∑ j, L b j * prefixMultiplier b j target * W t (nextPrefix b j) =
        (x^k + ∑ j, ((H t).eval (node b j) - node b j ^ k) * L b j) * W t b
      simp only [add_mul, sub_mul, Finset.sum_mul, mul_assoc, ← hav, Finset.sum_sub_distrib]
      ring_nf
      simp only [mul_assoc, mul_comm]
      ring
    · intro hz
      have hh := congrFun hz (fun _ => 0)
      simp [W, prefixWeight] at hh
  have hbound := (M.eigenvectors_linearIndependent' _ hx _ heig).fintype_card_le_finrank
  simpa [PrefixIndex, Module.finrank_pi, Fintype.card_pi] using hbound

/-- The full solution set is finite, even when the coefficients and the
evaluation nodes range over an infinite field. -/
theorem finite_prescribed_evaluation_products [Infinite K]
    (d : Fin k → ℕ) (a : Fin k → ℕ → K) (target : Fin k → K)
    (hsep : ∀ (b : (j : Fin k) → Fin (d j + 1)), Function.Injective (fun j => a j (b j))) :
    {H : K[X] | H.Monic ∧ H.natDegree = k ∧
      ∀ j, ∏ i ∈ Finset.range (d j + 1), H.eval (a j i) = target j}.Finite := by
  classical
  by_contra hf
  obtain ⟨S, hS, hc⟩ := Set.Infinite.exists_subset_card_eq hf ((∏ j, (d j + 1)) + 1)
  have hh (t : S) := hS t.property
  have hle := card_prescribed_evaluation_products d a target hsep (fun t : S => t.val)
    Subtype.coe_injective (fun t => (hh t).1) (fun t => (hh t).2.1) (fun t => (hh t).2.2)
  rw [Fintype.card_coe, hc] at hle
  omega

private theorem prod_list_evaluations (l : List K) (f : K → K) :
    ∏ i ∈ Finset.range l.length, f (l.getD i 0) = (l.map f).prod := by
  rw [← Fin.prod_univ_eq_prod_range (fun i => f (l.getD i 0)) l.length, ← Fin.prod_ofFn]
  simp only [List.getD_eq_getElem l 0 (Fin.isLt _)]
  rw [List.ofFn_getElem_eq_map]

/-- Group membership alone is needed. Repetitions within any one multiset
represent the multiplicities of roots in a resultant. -/
theorem finite_prescribed_multiset_products [Infinite K] (nodes : Fin k → Multiset K)
    (target : Fin k → K) (hpos : ∀ j, 0 < (nodes j).card)
    (hdis : ∀ i j x, x ∈ nodes i → x ∈ nodes j → i = j) :
    {H : K[X] | H.Monic ∧ H.natDegree = k ∧
      ∀ j, ((nodes j).map (fun x => H.eval x)).prod = target j}.Finite := by
  classical
  let d (j : Fin k) := (nodes j).card - 1
  let a (j : Fin k) (i : ℕ) := (nodes j).toList.getD i 0
  have hd (j : Fin k) : d j + 1 = (nodes j).toList.length := by
    simp [d, Nat.sub_add_cancel (hpos j)]
  have hsep (b : (j : Fin k) → Fin (d j + 1)) : Function.Injective (fun j => a j (b j)) := by
    have hm (j : Fin k) : a j (b j) ∈ nodes j := by
      have hj : (b j).val < (nodes j).toList.length := (hd j) ▸ (b j).isLt
      apply Multiset.mem_toList.1
      change (nodes j).toList.getD (b j).val 0 ∈ (nodes j).toList
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem _
    intro i j he
    change a i (b i) = a j (b j) at he
    exact hdis i j _ (hm i) (he.symm ▸ hm j)
  apply (finite_prescribed_evaluation_products d a target hsep).subset
  rintro H ⟨hm, hn, ht⟩
  refine ⟨hm, hn, fun j => ?_⟩
  simp only [hd, a, prod_list_evaluations (nodes j).toList (fun x => H.eval x),
    Multiset.prod_map_toList]
  exact ht j

end GF2Sparse
