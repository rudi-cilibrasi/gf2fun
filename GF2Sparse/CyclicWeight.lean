import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-! Bounds on the loss of binary coefficients when projecting a finite set onto a line. -/

namespace GF2Sparse
namespace CyclicWeight

open Finset

private theorem count_le_parity_add_pairs (k : ℕ) : k ≤ k % 2 + (k * k - k) := by
  by_cases h : k ≤ 1
  · interval_cases k <;> decide
  · have hm := Nat.mul_le_mul_right k (show 2 ≤ k by omega)
    omega

/-- Over a finite target, each coefficient lost by reduction modulo two is charged to an ordered collision. -/
theorem card_le_odd_fibers_add_collisions {ι K : Type*} [DecidableEq ι]
    [Fintype K] [DecidableEq K] (T : Finset ι) (f : ι → K) :
    T.card ≤ (∑ y : K, (T.filter fun x => f x = y).card % 2) +
      (T.offDiag.filter fun z => f z.1 = f z.2).card := by
  classical
  let C := T.offDiag.filter fun z => f z.1 = f z.2
  have hf (y : K) : (T.filter fun x => f x = y).offDiag = C.filter (fun z => f z.1 = y) := by
    ext z
    simp only [C, mem_offDiag, mem_filter]
    aesop
  have ht : (∑ y : K, (T.filter fun x => f x = y).card) = T.card := by
    simpa using sum_card_fiberwise_eq_card_filter T univ f
  have hc : (∑ y : K, (C.filter fun z => f z.1 = y).card) = C.card := by
    simpa using sum_card_fiberwise_eq_card_filter C univ (fun z => f z.1)
  change T.card ≤ _ + C.card
  rw [← ht, ← hc, ← Finset.sum_add_distrib]
  apply sum_le_sum
  intro y _
  rw [← hf, offDiag_card]
  exact count_le_parity_add_pairs _

private theorem unique_slope {K : Type*} [Field K] {z w : K × K} (hne : z ≠ w)
    {a b : K} (ha : z.1 + a*z.2 = w.1 + a*w.2) (hb : z.1 + b*z.2 = w.1 + b*w.2) :
    a = b := by
  have h : (a-b)*(z.2-w.2) = 0 := by linear_combination ha - hb
  rcases mul_eq_zero.mp h with hab | hzw
  · exact sub_eq_zero.mp hab
  · have hy := sub_eq_zero.mp hzw
    rw [hy] at ha
    exact (hne (Prod.ext (add_right_cancel ha) hy)).elim

/-- Every ordered pair of distinct points collides under at most one slope. -/
theorem sum_collisions_le {K : Type*} [Field K] [Fintype K] [DecidableEq K] (T : Finset (K × K)) :
    (∑ a : K, (T.offDiag.filter fun z => z.1.1 + a*z.1.2 = z.2.1 + a*z.2.2).card) ≤
      T.offDiag.card := by
  classical
  let P (a : K) (z : (K × K) × (K × K)) := z.1.1 + a*z.1.2 = z.2.1 + a*z.2.2
  change (∑ a : K, (T.offDiag.filter (P a)).card) ≤ _
  have swap : (∑ a : K, (T.offDiag.filter (P a)).card) =
      ∑ z ∈ T.offDiag, (univ.filter fun a => P a z).card := by
    simp only [Finset.card_filter]
    rw [sum_comm]
  rw [swap, card_eq_sum_ones T.offDiag]
  apply sum_le_sum
  intro z hz
  apply card_le_one_iff.mpr
  intro a b ha hb
  exact unique_slope (mem_offDiag.mp hz).2.2 (mem_filter.mp ha).2 (mem_filter.mp hb).2

/-- Total binary projection weight over all field slopes, with its quadratic error term. -/
theorem projection_weight_bound {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (T : Finset (K × K)) :
    Fintype.card K * T.card ≤
      (∑ a : K, ∑ y : K, (T.filter fun z => z.1 + a*z.2 = y).card % 2) +
        (T.card * T.card - T.card) := by
  classical
  have h := sum_le_sum (s := (univ : Finset K)) (fun a _ =>
    card_le_odd_fibers_add_collisions T (fun z => z.1 + a*z.2))
  simp only [sum_const, card_univ, smul_eq_mul, sum_add_distrib] at h
  exact h.trans (Nat.add_le_add_left (offDiag_card T ▸ sum_collisions_le T) _)

end CyclicWeight
end GF2Sparse
