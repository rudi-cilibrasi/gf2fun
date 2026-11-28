import GF2Sparse.Basic

/-! Evaluation of a binary polynomial on its support. -/

namespace GF2Sparse

open Polynomial

/-- Evaluate a binary polynomial by summing the powers on its support. -/
theorem aeval_binary_support {A : Type*} [Semiring A] [Algebra (ZMod 2) A]
    (p : BinaryPoly) (x : A) : aeval x p = ∑ i ∈ p.support, x^i := by
  rw [aeval_def, eval₂_eq_sum, sum_def]
  apply Finset.sum_congr rfl
  intro i hi
  have h : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  rw [h _ (mem_support_iff.1 hi), map_one, one_mul]

end GF2Sparse
