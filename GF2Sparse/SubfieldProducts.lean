import GF2Sparse.Certificate
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-! Rank and binary subgroup certificates for products from two proper subfields. -/

namespace GF2Sparse.SubfieldProducts

open Polynomial

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

end GF2Sparse.SubfieldProducts
