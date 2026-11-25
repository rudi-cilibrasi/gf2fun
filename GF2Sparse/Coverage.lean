import GF2Sparse.Witnesses
import GF2Sparse.Witnesses129To192
import GF2Sparse.Witnesses193To256
import GF2Sparse.Witnesses257To272
import GF2Sparse.Witnesses273To288
import GF2Sparse.Witnesses289To304
import GF2Sparse.Witnesses305To320

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

theorem primitiveProduct_upto_256 (n : ℕ) (hn : 5 ≤ n) (hmax : n ≤ 256) :
    HasPrimitiveProduct n := by
  by_cases h : n ≤ 192
  · exact primitiveProduct_upto_192 n hn h
  · exact primitiveProduct_193_to_256 n (by omega) hmax

theorem sparsePrimitive_upto_256 (n : ℕ) (hn : 0 < n) (hmax : n ≤ 256) :
    HasSparsePrimitive n := by
  by_cases h : n < 5
  · exact sparsePrimitive_upto_128 n hn (by omega)
  · exact (primitiveProduct_upto_256 n (by omega) hmax).sparse

theorem primitiveProduct_upto_288 (n : ℕ) (hn : 5 ≤ n) (hmax : n ≤ 288) :
    HasPrimitiveProduct n := by
  by_cases h : n ≤ 256
  · exact primitiveProduct_upto_256 n hn h
  by_cases h' : n ≤ 272
  · exact primitiveProduct_257_to_272 n (by omega) h'
  · exact primitiveProduct_273_to_288 n (by omega) hmax

theorem sparsePrimitive_upto_288 (n : ℕ) (hn : 0 < n) (hmax : n ≤ 288) :
    HasSparsePrimitive n := by
  by_cases h : n < 5
  · exact sparsePrimitive_upto_128 n hn (by omega)
  · exact (primitiveProduct_upto_288 n (by omega) hmax).sparse

theorem primitiveProduct_upto_320 (n : ℕ) (hn : 5 ≤ n) (hmax : n ≤ 320) :
    HasPrimitiveProduct n := by
  by_cases h : n ≤ 288
  · exact primitiveProduct_upto_288 n hn h
  by_cases h' : n ≤ 304
  · exact primitiveProduct_289_to_304 n (by omega) h'
  · exact primitiveProduct_305_to_320 n (by omega) hmax

theorem sparsePrimitive_upto_320 (n : ℕ) (hn : 0 < n) (hmax : n ≤ 320) :
    HasSparsePrimitive n := by
  by_cases h : n < 5
  · exact sparsePrimitive_upto_128 n hn (by omega)
  · exact (primitiveProduct_upto_320 n (by omega) hmax).sparse

end GF2Sparse
