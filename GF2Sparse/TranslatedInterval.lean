import GF2Sparse.Coverage
import GF2Sparse.OrderBound
import GF2Sparse.ShiftedPeriods

/-! Keep a finite interval of certified pentanomial tails fixed and translate their leading exponents together. -/

namespace GF2Sparse

open Polynomial

/-- A common shift preserves the shortest root-product relation for every source degree. -/
def TranslatedProductInterval (N : ℕ) : Prop :=
    ∃ u v : Finset.Icc 5 N → ℕ,
      (∀ j, Primitive (productCandidate j.val (u j) (v j))) ∧
      ∀ B : ℕ, ∃ T > B, ∀ j, let f := productCandidate (T+j.val) (u j) (v j)
        f.natDegree = T+j.val ∧ f.support.card = 5 ∧ productCandidate j.val (u j) (v j) ∣ f ∧
        NoShortRootProducts (j.val-1) f ∧ ¬ NoRootProductOfLength j.val f

theorem translated_product_interval_of_coverage {N : ℕ}
    (hN : ∀ n, 5 ≤ n → n ≤ N → HasPrimitiveProduct n) : TranslatedProductInterval N := by
  classical
  have seeds (j : Finset.Icc 5 N) :=
    hN j.val (Finset.mem_Icc.1 j.property).1 (Finset.mem_Icc.1 j.property).2
  choose u v hu hv huv htop hp using seeds
  let h (j : Finset.Icc 5 N) := ((X : BinaryPoly)^(u j)+1)*(X^(v j)+1)
  have deg (j) : (h j).natDegree = u j+v j := product_tail_degree (hu j) (hv j)
  refine ⟨u, v, hp, fun B => ?_⟩
  obtain ⟨T, hT, hall⟩ := simultaneous_seed_translations (fun j : Finset.Icc 5 N => j.val) h
    (fun j => by rw [deg]; have := hu j; omega)
    (fun j => (deg j).trans_lt (htop j))
    (fun j => by simp [h, coeff_X_pow, (hu j).ne, (hv j).ne]) hp B
  refine ⟨T, hT, fun j => ?_⟩
  have shape := product_shape (hu j) (hv j) (huv j) ((htop j).trans_le (Nat.le_add_left j.val T))
  exact ⟨shape.1, shape.2, hall j⟩

theorem translated_product_interval_upto_384 : TranslatedProductInterval 384 :=
  translated_product_interval_of_coverage primitiveProduct_upto_384

theorem translated_product_interval_upto_400 : TranslatedProductInterval 400 :=
  translated_product_interval_of_coverage primitiveProduct_upto_400

theorem translated_product_interval_upto_416 : TranslatedProductInterval 416 :=
  translated_product_interval_of_coverage primitiveProduct_upto_416

theorem translated_product_interval_upto_432 : TranslatedProductInterval 432 :=
  translated_product_interval_of_coverage primitiveProduct_upto_432

theorem translated_product_interval_upto_512 : TranslatedProductInterval 512 :=
  translated_product_interval_of_coverage primitiveProduct_upto_512

theorem translated_product_interval_upto_528 : TranslatedProductInterval 528 :=
  translated_product_interval_of_coverage primitiveProduct_upto_528

theorem translated_product_interval_upto_544 : TranslatedProductInterval 544 :=
  translated_product_interval_of_coverage primitiveProduct_upto_544

theorem translated_product_interval_upto_640 : TranslatedProductInterval 640 :=
  translated_product_interval_of_coverage primitiveProduct_upto_640

theorem translated_product_interval_upto_656 : TranslatedProductInterval 656 :=
  translated_product_interval_of_coverage primitiveProduct_upto_656

end GF2Sparse
