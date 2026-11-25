import GF2Sparse.Witnesses
import GF2Sparse.Witnesses129To192

/-! Combine the independently checkable witness tables into degree intervals. -/

namespace GF2Sparse

theorem primitiveProduct_upto_192 (n : ℕ) (hn : 5 ≤ n) (hmax : n ≤ 192) :
    HasPrimitiveProduct n := by
  by_cases h : n ≤ 128
  · exact primitiveProduct_upto_128 n hn h
  · exact primitiveProduct_129_to_192 n (by omega) hmax

theorem sparsePrimitive_upto_192 (n : ℕ) (hn : 0 < n) (hmax : n ≤ 192) :
    HasSparsePrimitive n := by
  by_cases h : n < 5
  · exact sparsePrimitive_upto_128 n hn (by omega)
  · exact (primitiveProduct_upto_192 n (by omega) hmax).sparse

end GF2Sparse
