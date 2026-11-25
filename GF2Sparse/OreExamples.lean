import GF2Sparse.OreOrder
import GF2Sparse.Coverage
import GF2Sparse.MersenneExamples

/-! Apply the weight-preserving Ore lift to the verified primitive seeds. -/

namespace GF2Sparse

theorem HasSparsePrimitive.oreLift {s : ℕ} (h : HasSparsePrimitive s) :
    ∃ f : BinaryPoly, f.natDegree = 2^s-1 ∧ f.support.card ≤ 5 ∧
      Irreducible f ∧ NoShortRootProducts (s-1) f := by
  obtain ⟨p, rfl, hw, hp⟩ := h
  exact ⟨GF2Sparse.oreLift p, oreLift_degree hp.2.1.ne_zero, (oreLift_weight p).trans_le hw,
    hp.irreducible_oreLift, hp.oreLift_short_products (by have := hp.2.1.natDegree_pos; omega)⟩

theorem oreLift_upto_320 {s : ℕ} (hs : 0 < s) (hle : s ≤ 320) :
    ∃ f : BinaryPoly, f.natDegree = 2^s-1 ∧ f.support.card ≤ 5 ∧
      Irreducible f ∧ NoShortRootProducts (s-1) f :=
  (sparsePrimitive_upto_320 s hs hle).oreLift

theorem oreLift_upto_384 {s : ℕ} (hs : 0 < s) (hle : s ≤ 384) :
    ∃ f : BinaryPoly, f.natDegree = 2^s-1 ∧ f.support.card ≤ 5 ∧
      Irreducible f ∧ NoShortRootProducts (s-1) f :=
  (sparsePrimitive_upto_384 s hs hle).oreLift

theorem oreLift_of_primitive_product {s u v : ℕ} (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v)
    (hlt : u+v < s) (hp : Primitive (productCandidate s u v)) :
    let f := oreLift (productCandidate s u v)
    f.natDegree = 2^s-1 ∧ f.support.card = 5 ∧ Irreducible f ∧ NoShortRootProducts (s-1) f := by
  obtain ⟨hd, hw⟩ := product_shape hu hv huv hlt
  refine ⟨(oreLift_degree hp.2.1.ne_zero).trans (by rw [hd]), (oreLift_weight _).trans hw,
    hp.irreducible_oreLift, hp.oreLift_short_products ?_⟩
  omega

theorem oreLift_2203 : Irreducible (oreLift (productCandidate 2203 62 135)) ∧
    NoShortRootProducts 2202 (oreLift (productCandidate 2203 62 135)) := by
  have h := primitiveProduct_2203_62_135
  refine ⟨h.irreducible_oreLift, h.oreLift_short_products ?_⟩
  rw [(product_shape (u := 62) (v := 135) (n := 2203) (by decide) (by decide) (by decide) (by decide)).1]
  decide

theorem oreLift_2203_order :
    2^(2^(1101+1)-1101) < orderOf (AdjoinRoot.root (oreLift (productCandidate 2203 62 135))) := by
  have hd := (product_shape (u := 62) (v := 135) (n := 2203) (by decide) (by decide) (by decide) (by decide)).1
  exact primitiveProduct_2203_62_135.oreLift_order_exponential (a := 1101) (by decide) (by rw [hd])

end GF2Sparse
