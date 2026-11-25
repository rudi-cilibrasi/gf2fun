import GF2Sparse.CompositionNorm
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-! Multiplicities of quotients of roots of a two-block polynomial. -/

namespace GF2Sparse

open Polynomial

variable {K : Type*} [Field K]

/-- A power is injective on roots satisfying a rational equation in that power. -/
theorem twoBlock_power_injOn {d m : ℕ} (hc : d.Coprime m) (A B : K[X]) (R : Finset K)
    (hn : ∀ x ∈ R, x ≠ 0) (ha : ∀ x ∈ R, A.eval (x^d) ≠ 0)
    (hr : ∀ x ∈ R, x^m * A.eval (x^d) = B.eval (x^d)) :
    Set.InjOn (fun x : K => x^d) (R : Set K) := by
  intro x hx y hy he
  change x^d = y^d at he
  have hm : x^m = y^m := by
    apply mul_right_cancel₀ (ha y hy)
    rw [hr y hy, ← he, hr x hx]
  apply (div_eq_one_iff_eq (hn y hy)).1
  apply (pow_eq_one_iff_of_coprime hc).1
  simp [div_pow, he, hm, hn y hy]

/-- If multiplication by z moves some root outside the equation, at most
deg A + deg B ordered pairs of roots have quotient z. -/
theorem twoBlock_quotient_card_le [DecidableEq K] {d m : ℕ} (hc : d.Coprime m)
    (A B : K[X]) (R : Finset K) (hn : ∀ x ∈ R, x ≠ 0)
    (ha : ∀ x ∈ R, A.eval (x^d) ≠ 0)
    (hr : ∀ x ∈ R, x^m * A.eval (x^d) = B.eval (x^d))
    (z : K) (hmove : ∃ x ∈ R, (z*x)^m * A.eval ((z*x)^d) ≠ B.eval ((z*x)^d)) :
    (R.filter (fun x => z*x ∈ R)).card ≤ A.natDegree + B.natDegree := by
  let t : K[X] := C (z^d) * X
  let H : K[X] := B.comp t * A - C (z^m) * (A.comp t * B)
  have identity (x : K) (hx : x ∈ R) :
      H.eval (x^d) = A.eval (x^d) * (B.eval ((z*x)^d) - (z*x)^m * A.eval ((z*x)^d)) := by
    simp only [H, t, eval_sub, eval_mul, eval_comp, eval_C, eval_X, mul_pow]
    rw [← hr x hx]
    ring
  have hH : H ≠ 0 := by
    intro he
    obtain ⟨x,hx,hmove⟩ := hmove
    have hv := identity x hx
    rw [he, eval_zero] at hv
    exact hmove (sub_eq_zero.mp ((mul_eq_zero.mp hv.symm).resolve_left (ha x hx))).symm
  have ltdeg (P : K[X]) : (P.comp t).natDegree ≤ P.natDegree := by
    rw [natDegree_comp]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left P.natDegree
      ((natDegree_C_mul_le (z^d) (X : K[X])).trans natDegree_X_le)
  have degH : H.natDegree ≤ A.natDegree + B.natDegree := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simpa only [add_comm B.natDegree A.natDegree] using
        (natDegree_mul_le_of_le (ltdeg B) (le_refl A.natDegree))
    · exact (natDegree_C_mul_le _ _).trans (natDegree_mul_le_of_le (ltdeg A) le_rfl)
  let S := R.filter (fun x => z*x ∈ R)
  have hs : Set.InjOn (fun x : K => x^d) (S : Set K) :=
    (twoBlock_power_injOn hc A B R hn ha hr).mono (fun _ hx => (Finset.mem_filter.1 hx).1)
  rw [← Finset.card_image_of_injOn hs]
  apply le_trans (card_le_degree_of_subset_roots (p := H) ?_) degH
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hx,hzx⟩ := Finset.mem_filter.1 hx
  exact (mem_roots hH).2 (by simp [IsRoot, identity x hx, hr _ hzx])

/-- An upper bound on each quotient multiplicity gives a lower bound on every
common exponent of the roots. The ambient field can be infinite. -/
theorem common_exponent_of_quotient_card_le [DecidableEq K]
    (R : Finset K) {h D : ℕ} (hh : 0 < h)
    (hn : ∀ x ∈ R, x ≠ 0) (he : ∀ x ∈ R, x^h = 1)
    (hc : ∀ z : K, z ≠ 1 → (R.filter (fun x => z*x ∈ R)).card ≤ D) :
    R.card * R.card - R.card ≤ D * (h-1) := by
  let U := (nthRootsFinset h (1 : K)).erase 1
  let q (p : K × K) := p.1 / p.2
  have maps (p : K × K) (hp : p ∈ R.offDiag) : q p ∈ U := by
    obtain ⟨hp1,hp2,hne⟩ := Finset.mem_offDiag.1 hp
    refine Finset.mem_erase.2 ⟨fun e => hne ((div_eq_one_iff_eq (hn _ hp2)).1 e), ?_⟩
    exact (mem_nthRootsFinset hh 1).2 (by simp [q, div_pow, he _ hp1, he _ hp2])
  have hbound := Finset.card_le_mul_card_image_of_maps_to maps D (by
    intro z hz
    refine le_trans (Finset.card_le_card_of_injOn Prod.snd ?_ ?_) (hc z (Finset.mem_erase.1 hz).1)
    · rintro ⟨x,y⟩ hp
      obtain ⟨hp,heq⟩ := Finset.mem_filter.1 hp
      obtain ⟨hx,hy,_⟩ := Finset.mem_offDiag.1 hp
      exact Finset.mem_filter.2 ⟨hy, (div_eq_iff (hn _ hy)).1 heq ▸ hx⟩
    · rintro ⟨x,y⟩ hp ⟨v,w⟩ ht eq
      change y = w at eq
      subst w
      obtain ⟨hp,eh⟩ := Finset.mem_filter.1 hp
      have hy := hn y (Finset.mem_offDiag.1 hp).2.1
      have ex : x = z*y := (div_eq_iff hy).1 eh
      have ev : v = z*y := (div_eq_iff hy).1 (Finset.mem_filter.1 ht).2
      exact Prod.ext (ex.trans ev.symm) rfl)
  have one_mem : 1 ∈ nthRootsFinset h (1 : K) := (mem_nthRootsFinset hh 1).2 (one_pow h)
  have hu : U.card ≤ h-1 := by
    rw [Finset.card_erase_of_mem one_mem]
    letI := Classical.decEq K
    exact Nat.sub_le_sub_right ((Multiset.toFinset_card_le _).trans (card_nthRoots h (1 : K))) 1
  simpa only [Finset.offDiag_card] using hbound.trans (Nat.mul_le_mul_left D hu)

/-- A quotient fixed by the degree-b Frobenius occurs for at least n/b different
denominators among the conjugate roots of its irreducible polynomial. -/
theorem quotient_subfield_fiber [Algebra (ZMod 2) K] [CharP K 2] [DecidableEq K]
    {f : BinaryPoly} (hf : Irreducible f) {y z : K}
    (hy : aeval y f = 0) (hzy : aeval (z*y) f = 0)
    {b k : ℕ} (hb : 0 < b) (hd : f.natDegree = b*k) (hz : z^(2^b) = z) :
    k ≤ ((f.rootSet K).toFinset.filter (fun x => z*x ∈ (f.rootSet K).toFinset)).card := by
  classical
  let v (i : Fin k) := y^(2^(b*i.val))
  have hi : Function.Injective v := relative_frobenius_conjugates_injective hf hy hb hd
  have fix (j : ℕ) : z^(2^(b*j)) = z := by
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hz]
  have root {x : K} (hx : aeval x f = 0) (i : ℕ) : x^(2^i) ∈ f.rootSet K :=
    (mem_rootSet_of_ne hf.ne_zero).2 (by rw [aeval_dyadic, hx, zero_pow (Nat.two_pow_pos _).ne'])
  have hmem (i : Fin k) : v i ∈ (f.rootSet K).toFinset.filter (fun x => z*x ∈ (f.rootSet K).toFinset) := by
    refine Finset.mem_filter.2 ⟨Set.mem_toFinset.2 (root hy _), Set.mem_toFinset.2 ?_⟩
    have h := root hzy (b*i.val)
    simpa only [v, mul_pow, fix] using h
  simpa only [Finset.card_univ, Fintype.card_fin] using
    (Finset.card_le_card_of_injOn v (fun i _ => hmem i) hi.injOn : Finset.univ.card ≤ _)

end GF2Sparse
