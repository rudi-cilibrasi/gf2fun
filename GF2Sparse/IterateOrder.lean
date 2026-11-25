import GF2Sparse.OrderBound
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.BigOperators

/-! Gao's iterate method for the order of X when X^(2^t) = g(X).
The proof applies to a quotient by the whole polynomial or any of its factors. -/

namespace GF2Sparse

open Polynomial

private abbrev K := AlgebraicClosure (ZMod 2)

private noncomputable def iteratePoly (g : BinaryPoly) : ℕ → BinaryPoly
  | 0 => X
  | j + 1 => (iteratePoly g j).comp g

private theorem iterate_degree (g : BinaryPoly) (j : ℕ) :
    (iteratePoly g j).natDegree = g.natDegree ^ j := by
  induction j with
  | zero => simp [iteratePoly]
  | succ j ih => simp [iteratePoly, natDegree_comp, ih, pow_succ]

/-- A nonzero preimage at each step constructs a point first reaching zero
after exactly j iterations. -/
private theorem iterate_fresh_root (g : BinaryPoly)
    (hpre : ∀ y : K, ∃ z : K, z ≠ 0 ∧ aeval z g = y) (j : ℕ) :
    ∃ z : K, aeval z (iteratePoly g j) = 0 ∧ ∀ k < j, aeval z (iteratePoly g k) ≠ 0 := by
  induction j with
  | zero => exact ⟨0, by simp [iteratePoly], by omega⟩
  | succ j ih =>
    obtain ⟨y, hy, hprev⟩ := ih
    obtain ⟨z, hz, hzy⟩ := hpre y
    refine ⟨z, by simpa [iteratePoly, aeval_comp, hzy] using hy, ?_⟩
    intro k hk
    cases k with
    | zero => simpa [iteratePoly] using hz
    | succ k => simpa [iteratePoly, aeval_comp, hzy] using hprev k (by omega)

private theorem product_preimages {u v : ℕ} (hu : 0 < u) (huv : u < v) :
    ∀ y : K, ∃ z : K, z ≠ 0 ∧ aeval z (((X : BinaryPoly) ^ u + 1) * (X ^ v + 1)) = y := by
  let g : BinaryPoly := (X ^ u + 1) * (X ^ v + 1)
  have hv := hu.trans huv
  have leftdeg (k : ℕ) (hk : 0 < k) : ((X : BinaryPoly) ^ k + 1).natDegree = k := by
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
    simpa using hk
  have hg : g.natDegree = u + v := product_tail_degree hu hv
  intro y
  by_cases hy : y = 1
  · subst y
    let q : BinaryPoly := X ^ v + (X ^ (v - u) + 1)
    have hw : 0 < v - u := by omega
    have hq : q.natDegree = v := by
      rw [show q = _ from rfl, natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
      rw [leftdeg _ hw, natDegree_X_pow]
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero K q
      (degree_ne_of_natDegree_ne (hq ▸ hv.ne'))
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp [q, hv.ne', hw.ne'] at hz
    refine ⟨z, hz0, ?_⟩
    have hform : g = X ^ u * q + 1 := by
      have hpow : (X : BinaryPoly) ^ u * X ^ (v - u) = X ^ v := by
        rw [← pow_add, Nat.add_sub_of_le huv.le]
      dsimp [g, q]
      linear_combination -hpow
    change aeval z g = 1
    simp [hform, hz]
  · have hs := IsAlgClosed.eval_surjective (p := g.map (algebraMap (ZMod 2) K))
      (by rw [natDegree_map, hg]; omega)
    obtain ⟨z, hz⟩ := hs y
    change (g.map (algebraMap (ZMod 2) K)).eval z = y at hz
    rw [eval_map_algebraMap] at hz
    refine ⟨z, ?_, hz⟩
    rintro rfl
    exact hy (by simpa [g, hu.ne', hv.ne'] using hz.symm)

private noncomputable def iterateProduct (g : BinaryPoly) {s : ℕ} (e : Fin s → ℕ) : BinaryPoly :=
  ∏ j, iteratePoly g j.val ^ e j

private theorem index_le_of_eval_ne_zero {A B G : BinaryPoly} {a b : ℕ} {z : K}
    (hG : G ≠ 0) (hz : aeval z G = 0) (hB : aeval z B ≠ 0)
    (he : A * G ^ a = B * G ^ b) : a ≤ b := by
  by_contra! h
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
  rw [hk, pow_succ, pow_add] at he
  have hc : (A * G ^ k * G) * G ^ b = B * G ^ b := by
    convert he using 1
    ring
  have hv := congrArg (aeval z) (mul_right_cancel₀ (pow_ne_zero b hG) hc)
  exact hB (by simpa [hz] using hv.symm)

private theorem iterateProduct_injective {g : BinaryPoly} (hd : 0 < g.natDegree)
    (hpre : ∀ y : K, ∃ z : K, z ≠ 0 ∧ aeval z g = y) (s : ℕ) :
    Function.Injective (iterateProduct g (s := s)) := by
  induction s with
  | zero => intro a b _; exact Subsingleton.elim a b
  | succ s ih =>
    intro a b heq
    obtain ⟨z, hz, hprev⟩ := iterate_fresh_root g hpre s
    let G := iteratePoly g s
    have hG : G ≠ 0 := by
      intro he
      have := iterate_degree g s
      change G.natDegree = _ at this
      exact (pow_pos hd s).ne (by simpa [he] using this)
    let head (e : Fin (s + 1) → ℕ) := iterateProduct g (fun j : Fin s => e j.castSucc)
    have hn (e : Fin (s + 1) → ℕ) : aeval z (head e) ≠ 0 := by
      simp only [head, iterateProduct, map_prod, map_pow]
      exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hprev i.val i.isLt)
    have hsplit (e : Fin (s + 1) → ℕ) :
        iterateProduct g e = head e * G ^ e (Fin.last s) := Fin.prod_univ_castSucc _
    rw [hsplit, hsplit] at heq
    have hl : a (Fin.last s) = b (Fin.last s) := le_antisymm
      (index_le_of_eval_ne_zero hG hz (hn b) heq) (index_le_of_eval_ne_zero hG hz (hn a) heq.symm)
    rw [hl] at heq
    have hh := ih (mul_right_cancel₀ (pow_ne_zero _ hG) heq)
    funext j
    exact Fin.lastCases hl (fun i => congrFun hh i) j

private theorem aeval_dyadic {R : Type*} [CommRing R] [Algebra (ZMod 2) R] [CharP R 2]
    (p : BinaryPoly) (r : R) (t : ℕ) : aeval (r ^ (2 ^ t)) p = (aeval r p) ^ (2 ^ t) := by
  have h := map_aeval_eq_aeval_map (φ := RingHom.id (ZMod 2)) (ψ := iterateFrobenius R 2 t)
    (Subsingleton.elim _ _) p r
  simpa [iterateFrobenius_def] using h.symm

private theorem triangle (s : ℕ) : (∑ j : Fin s, (s - j.val)) * 2 = s * (s + 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.succ_sub_succ_eq_sub, Nat.add_mul, ih]
    ring

/-- Count products of iterates as powers of the residue of X. The box of
exponents has d^(s(s+1)/2) elements and every product has degree < s*d^s. -/
private theorem iterate_order {f g : BinaryPoly} {t s : ℕ} (hc : f.coeff 0 = 1)
    (hd : 0 < g.natDegree) (hpre : ∀ y : K, ∃ z : K, z ≠ 0 ∧ aeval z g = y)
    (hrel : AdjoinRoot.root f ^ (2 ^ t) = AdjoinRoot.mk f g)
    (hs : 0 < s) (hm : s * g.natDegree ^ s ≤ f.natDegree) :
    g.natDegree ^ (s * (s + 1) / 2) ≤ orderOf (AdjoinRoot.root f) := by
  classical
  let d := g.natDegree
  have hdeg := (Nat.mul_pos hs (pow_pos hd s)).trans_le hm
  letI := AdjoinRoot.nontrivial f (degree_ne_of_natDegree_ne hdeg.ne')
  letI : CharP (AdjoinRoot f) 2 := charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  let r := AdjoinRoot.root f
  have hpow (j : ℕ) : AdjoinRoot.mk f (iteratePoly g j) = r ^ ((2 ^ t) ^ j) := by
    induction j with
    | zero => simp [iteratePoly, r]
    | succ j ih =>
      rw [iteratePoly, ← AdjoinRoot.aeval_eq, aeval_comp, AdjoinRoot.aeval_eq, ← hrel,
        aeval_dyadic, AdjoinRoot.aeval_eq, ih, ← pow_mul, pow_succ]
  let Box := (j : Fin s) → Fin (d ^ (s - j.val))
  let p (e : Box) := iterateProduct g (fun j => (e j).val)
  let index (e : Box) := ∑ j : Fin s, ((2 ^ t) ^ j.val) * (e j).val
  have hrep (e : Box) : AdjoinRoot.mk f (p e) = r ^ index e := by
    simp only [p, iterateProduct, map_prod, map_pow, hpow, index, Finset.prod_pow_eq_pow_sum,
      ← pow_mul]
  have hi : Function.Injective p := by
    intro a b he
    have h := iterateProduct_injective hd hpre s he
    exact funext (fun j => Fin.ext (congrFun h j))
  have hlt (e : Box) : (p e).natDegree < f.natDegree := by
    letI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
    apply (natDegree_prod_le _ _).trans_lt
    apply lt_of_lt_of_le _ hm
    calc
      _ < ∑ _j : Fin s, d ^ s := by
        apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        intro j _
        rw [natDegree_pow, iterate_degree]
        calc
          _ < d ^ (s - j.val) * d ^ j.val := Nat.mul_lt_mul_of_pos_right (e j).isLt (pow_pos hd _)
          _ = d ^ s := by rw [← pow_add, Nat.sub_add_cancel j.isLt.le]
      _ = s * d ^ s := by simp
  have hcount : Fintype.card Box = d ^ (s * (s + 1) / 2) := by
    simp only [Box, Fintype.card_pi, Fintype.card_fin, Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [← triangle, Nat.mul_div_cancel _ (by decide : 0 < 2)]
  rw [← hcount]
  exact order_ge_of_representatives hc p index hi hlt hrep

/-- At dyadic degrees, Gao's iterate bound holds modulo every sufficiently
large divisor of the pentanomial, including the pentanomial itself. -/
theorem dyadic_factor_order {t u v s : ℕ} {f : BinaryPoly}
    (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v) (hf : f ∣ productCandidate (2 ^ t) u v)
    (hs : 0 < s) (hm : s * (u + v) ^ s ≤ f.natDegree) :
    (u + v) ^ (s * (s + 1) / 2) ≤ orderOf (AdjoinRoot.root f) := by
  let g : BinaryPoly := (X ^ u + 1) * (X ^ v + 1)
  have hd : g.natDegree = u + v := product_tail_degree hu hv
  have hpre : ∀ y : K, ∃ z : K, z ≠ 0 ∧ aeval z g = y := by
    rcases lt_or_gt_of_ne huv with h | h
    · exact product_preimages hu h
    · simpa only [g, mul_comm] using product_preimages hv h
  have hrel : AdjoinRoot.root f ^ (2 ^ t) = AdjoinRoot.mk f g := by
    apply sub_eq_zero.1
    have he := AdjoinRoot.mk_eq_zero.2 hf
    change AdjoinRoot.mk f (X ^ (2 ^ t) + g) = 0 at he
    have he' : AdjoinRoot.mk f (X ^ (2 ^ t) - g) = 0 := by
      rwa [sub_eq_add_neg, CharTwo.neg_eq]
    simpa only [map_sub, map_pow, AdjoinRoot.mk_X] using he'
  have hc : f.coeff 0 = 1 := by
    obtain ⟨q, hq⟩ := hf
    have h := congrArg (fun h : BinaryPoly => h.coeff 0) hq
    simp [productCandidate, coeff_X_pow, hu.ne, hv.ne, (Nat.two_pow_pos t).ne] at h
    have options : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    exact (options _).resolve_left (fun hz => by simp [hz] at h)
  rw [← hd] at hm ⊢
  exact iterate_order hc (by omega) hpre hrel hs hm

end GF2Sparse
