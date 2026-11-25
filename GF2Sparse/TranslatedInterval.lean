import GF2Sparse.Coverage
import GF2Sparse.OrderBound
import GF2Sparse.ShiftedPeriods

/-! Keep all 380 certified pentanomial tails fixed and translate their leading exponents together. -/

namespace GF2Sparse

open Polynomial

theorem translated_product_interval_upto_384 :
    ∃ u v : Finset.Icc 5 384 → ℕ,
      (∀ j, Primitive (productCandidate j.val (u j) (v j))) ∧
      ∀ B : ℕ, ∃ T > B, ∀ j, let f := productCandidate (T+j.val) (u j) (v j)
        f.natDegree = T+j.val ∧ f.support.card = 5 ∧ productCandidate j.val (u j) (v j) ∣ f ∧
        NoShortRootProducts (j.val-1) f ∧ ¬ NoRootProductOfLength j.val f := by
  classical
  have seeds (j : Finset.Icc 5 384) :=
    primitiveProduct_upto_384 j.val (Finset.mem_Icc.1 j.property).1 (Finset.mem_Icc.1 j.property).2
  choose u v hu hv huv htop hp using seeds
  let h (j : Finset.Icc 5 384) := ((X : BinaryPoly)^(u j)+1)*(X^(v j)+1)
  have deg (j) : (h j).natDegree = u j+v j := product_tail_degree (hu j) (hv j)
  refine ⟨u, v, hp, fun B => ?_⟩
  obtain ⟨T, hT, hall⟩ := simultaneous_seed_translations (fun j : Finset.Icc 5 384 => j.val) h
    (fun j => by rw [deg]; have := hu j; omega)
    (fun j => (deg j).trans_lt (htop j))
    (fun j => by simp [h, coeff_X_pow, (hu j).ne, (hv j).ne]) hp B
  refine ⟨T, hT, fun j => ?_⟩
  have shape := product_shape (hu j) (hv j) (huv j) ((htop j).trans_le (Nat.le_add_left j.val T))
  exact ⟨shape.1, shape.2, hall j⟩

end GF2Sparse
