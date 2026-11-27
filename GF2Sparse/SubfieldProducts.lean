import GF2Sparse.Certificate
import GF2Sparse.Roots
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Tactic

/-! Rank and binary subgroup certificates for products from two proper subfields. -/

namespace GF2Sparse.SubfieldProducts

open Polynomial
open scoped TensorProduct

/-- A relation on products from linearly disjoint coordinate systems bounds the
sum of the ranks of the two coordinate matrices by the number of terms. -/
theorem coordinate_rank_sum {F K I J E : Type*} [Field F] [Field K] [Algebra F K]
    [Fintype I] [Fintype J] [Fintype E]
    (a : I → K) (b : J → K) (U : Matrix I E F) (V : Matrix J E F)
    (hi : LinearIndependent F (fun ij : I × J => a ij.1 * b ij.2))
    (hr : ∑ e, (∑ i, U i e • a i) * (∑ j, V j e • b j) = 0) :
    U.rank + V.rank ≤ Fintype.card E := by
  classical
  have hz : ∑ ij : I × J, (U * V.transpose) ij.1 ij.2 • (a ij.1 * b ij.2) = 0 := by
    rw [← hr, Fintype.sum_prod_type]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_smul,
      Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
    simp_rw [mul_comm (V _ _) (U _ _)]
    let w (i : I) (j : J) (e : E) := (U i e * V j e) • (a i * b j)
    calc
      ∑ i, ∑ j, ∑ e, w i j e = ∑ i, ∑ e, ∑ j, w i j e :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ e, ∑ i, ∑ j, w i j e := Finset.sum_comm
      _ = ∑ e, ∑ j, ∑ i, w i j e := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have hm : U * V.transpose = 0 := by
    ext i j
    exact Fintype.linearIndependent_iff.1 hi _ hz (i,j)
  simpa only [Matrix.rank_transpose] using Matrix.rank_add_rank_le_card_of_mul_eq_zero hm

private def binomialMask : ℕ → ℕ
  | 0 => 1
  | n+1 => maskProduct 3 (binomialMask n)

private theorem decode_binomial (n : ℕ) : decode (binomialMask n) = (X+1)^n := by
  have hx : decode 3 = X+1 := by
    change decode ((1 <<< 1) ^^^ 1) = _
    simp only [decode_xor, decode_shift, decode_one, mul_one]
  induction n with
  | zero => simp [binomialMask]
  | succ n ih => rw [binomialMask, decode_maskProduct, hx, ih, pow_succ']

private theorem binomial_coprime (h a b : ℕ)
    (hc : maskProduct a ((1 <<< h) ^^^ 1) ^^^ maskProduct b (binomialMask h ^^^ 1) = 1) :
    IsCoprime ((X : BinaryPoly)^h+1) ((X+1)^h+1) := by
  refine ⟨decode a, decode b, ?_⟩
  simpa only [decode_xor, decode_maskProduct, decode_shift_by, decode_one, mul_one,
    decode_binomial] using congrArg decode hc

set_option maxRecDepth 16384 in
/-- No point x and its translate x+1 both lie in the subgroup of order 23 or 89. -/
theorem no_binary_plane_23_89 :
    IsCoprime ((X : BinaryPoly)^23+1) ((X+1)^23+1) ∧
    IsCoprime ((X : BinaryPoly)^89+1) ((X+1)^89+1) :=
  ⟨binomial_coprime 23 0xfeff 0x8101 (by decide),
   binomial_coprime 89 0x355f8a2bfd500aa0202023 0x264c993ebd7af5f264c991 (by decide)⟩

set_option maxRecDepth 16384 in
/-- Exhaustion of small multiplicative orders from the two proper subfields of degree 1243. -/
theorem small_orders_1243 :
    ∀ h : Fin 1244, 1 < h.val →
      (h.val ∣ 2^11-1 → h.val = 23 ∨ h.val = 89) ∧ ¬ h.val ∣ 2^113-1 := by
  decide

/-- Project a binary tensor relation to a proper odd subrelation in the second factor. -/
theorem odd_subrelation {ι A B : Type*} [Fintype ι] [AddCommGroup A] [AddCommGroup B]
    [Module (ZMod 2) A] [Module (ZMod 2) B] (a : ι → A) (b : ι → B)
    (ha : ∑ i, a i ≠ 0) (hb : ∑ i, b i ≠ 0)
    (hab : ∑ i, a i ⊗ₜ[ZMod 2] b i = 0) :
    ∃ t : Finset ι, Odd t.card ∧ t.card < Fintype.card ι ∧ ∑ i ∈ t, b i = 0 := by
  classical
  obtain ⟨L, hL⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) ha
  let t := Finset.univ.filter (fun i => L (a i) = 1)
  have binary : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have select (i : ι) : L (a i) = if L (a i) = 1 then 1 else 0 := by
    rcases binary (L (a i)) with h | h <;> simp [h]
  have hcard : (t.card : ZMod 2) = 1 := by
    calc
      _ = ∑ i, (if L (a i) = 1 then 1 else 0 : ZMod 2) := by simp [t]
      _ = 1 := by simpa only [← select, ← map_sum] using hL
  have hodd : Odd t.card :=
    Nat.odd_iff.mpr ((ZMod.natCast_eq_natCast_iff t.card 1 2).1 (by simpa using hcard))
  let proj := (TensorProduct.lid (ZMod 2) B).toLinearMap.comp (L.rTensor B)
  have hp (i : ι) : proj (a i ⊗ₜ[ZMod 2] b i) = if L (a i) = 1 then b i else 0 := by
    change L (a i) • b i = _
    rcases binary (L (a i)) with h | h <;> simp [h]
  have ht : ∑ i ∈ t, b i = 0 := by
    simpa only [map_sum, hp, map_zero, t, Finset.sum_filter] using congrArg proj hab
  refine ⟨t, hodd, ?_, ht⟩
  apply Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ t, ?_⟩)
  intro h
  exact hb (h ▸ ht)

/-- A relation on at most five terms between two proper binary factors
forces a three-term additive relation among nonzero elements of the second. -/
theorem triple_of_five_tensors {ι A B : Type*} [Fintype ι] [AddCommGroup A] [AddCommGroup B]
    [Module (ZMod 2) A] [Module (ZMod 2) B] (a : ι → A) (b : ι → B)
    (hw : Fintype.card ι ≤ 5) (ha : ∑ i, a i ≠ 0) (hb : ∑ i, b i ≠ 0)
    (hnz : ∀ i, b i ≠ 0) (hab : ∑ i, a i ⊗ₜ[ZMod 2] b i = 0) :
    ∃ t : Finset ι, t.card = 3 ∧ ∑ i ∈ t, b i = 0 := by
  obtain ⟨t, ⟨k, hk⟩, hlt, ht⟩ := odd_subrelation a b ha hb hab
  refine ⟨t, ?_, ht⟩
  have h1 : t.card ≠ 1 := by
    intro h
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 h
    exact hnz i (by simpa using ht)
  omega

private theorem sum_powers_ne_zero {K : Type*} [Field K] [Algebra (ZMod 2) K]
    [FiniteDimensional (ZMod 2) K] {f : BinaryPoly} (hf : Irreducible f)
    (hd : Module.finrank (ZMod 2) K < f.natDegree) (a : K) :
    ∑ i : f.support, a^(i : ℕ) ≠ 0 := by
  intro h
  have he : aeval a f = 0 := by
    rw [aeval_binary_support, ← Finset.sum_coe_sort]; exact h
  have hmin := minpoly.eq_of_irreducible_of_monic hf he (binary_monic hf.ne_zero)
  rw [hmin] at hd
  exact hd.not_ge (minpoly.natDegree_le a)

/-- In a proper binary subfield, the support powers of an irreducible cannot
all have odd multiplicity when their distinct values sum to zero. This rules
out the multiplicity pattern 3,1,1 on a binary plane. -/
theorem no_odd_plane_profile {K : Type*} [Field K] [Algebra (ZMod 2) K] [CharP K 2]
    [FiniteDimensional (ZMod 2) K] [DecidableEq K] {f : BinaryPoly} (hf : Irreducible f)
    (hd : Module.finrank (ZMod 2) K < f.natDegree) (a : K)
    (ht : ∑ v ∈ f.support.image (fun e => a^e), v = 0) :
    ¬ ∀ v ∈ f.support.image (fun e => a^e), Odd (f.support.filter (fun e => a^e = v)).card := by
  intro h
  apply sum_powers_ne_zero hf hd a
  rw [Finset.sum_coe_sort]
  calc
    _ = ∑ v ∈ f.support.image (fun e => a^e),
        (f.support.filter (fun e => a^e = v)).card • v :=
      Finset.sum_comp (fun v : K => v) (fun e => a^e)
    _ = ∑ v ∈ f.support.image (fun e => a^e), v := by
      apply Finset.sum_congr rfl
      intro v hv
      obtain ⟨k, hk⟩ := h v hv
      rw [hk, nsmul_eq_mul]
      have htwo : (2 : K) = 0 := by simpa only [Nat.cast_ofNat] using CharP.cast_eq_zero K 2
      simp [htwo]
    _ = 0 := ht

/-- A root split over coprime proper subfields forces three powers of its second
component to sum to zero, at three distinct exponents from the sparse support. -/
theorem triple_of_subfield_product {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (A B : IntermediateField (ZMod 2) K)
    [FiniteDimensional (ZMod 2) A] [FiniteDimensional (ZMod 2) B]
    (hc : (Module.finrank (ZMod 2) A).Coprime (Module.finrank (ZMod 2) B))
    {f : BinaryPoly} (hf : Irreducible f) (hw : f.support.card ≤ 5)
    (ha : Module.finrank (ZMod 2) A < f.natDegree)
    (hb : Module.finrank (ZMod 2) B < f.natDegree)
    (a : A) (b : B) (hb0 : b ≠ 0) (hr : aeval ((a : K) * b) f = 0) :
    ∃ t : Finset (↑f.support), t.card = 3 ∧ ∑ i ∈ t, b^(i : ℕ) = 0 := by
  classical
  apply triple_of_five_tensors (fun i : f.support => a^(i : ℕ)) (fun i => b^(i : ℕ))
    (by simpa) (sum_powers_ne_zero hf ha a) (sum_powers_ne_zero hf hb b)
    (fun _ => pow_ne_zero _ hb0)
  have disj : A.LinearDisjoint B := IntermediateField.LinearDisjoint.of_finrank_coprime hc
  apply (Subalgebra.linearDisjoint_iff_injective.1 (IntermediateField.linearDisjoint_iff'.1 disj))
  rw [map_zero, map_sum]
  change ∑ i : f.support, (a : K)^(i : ℕ) * (b : K)^(i : ℕ) = 0
  rw [aeval_binary_support, ← Finset.sum_coe_sort] at hr
  simpa only [mul_pow] using hr

end GF2Sparse.SubfieldProducts
