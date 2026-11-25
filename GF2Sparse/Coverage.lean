import GF2Sparse.Witnesses
import GF2Sparse.Witnesses129To192
import GF2Sparse.Witnesses193To256
import GF2Sparse.Witnesses257To272
import GF2Sparse.Witnesses273To288
import GF2Sparse.Witnesses289To304
import GF2Sparse.Witnesses305To320
import GF2Sparse.Witnesses321To336
import GF2Sparse.Witnesses337To352
import GF2Sparse.Witnesses353To368
import GF2Sparse.Witnesses369To384
import GF2Sparse.Witnesses385To400
import GF2Sparse.Witnesses401To416
import GF2Sparse.Witnesses417To432
import GF2Sparse.Witnesses433To448
import GF2Sparse.Witnesses449To464
import GF2Sparse.Witnesses465To480
import GF2Sparse.Witnesses481To496
import GF2Sparse.Witnesses497To512

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

theorem primitiveProduct_upto_352 (n : ℕ) (hn : 5 ≤ n) (hmax : n ≤ 352) :
    HasPrimitiveProduct n := by
  by_cases h : n ≤ 320
  · exact primitiveProduct_upto_320 n hn h
  by_cases h' : n ≤ 336
  · exact primitiveProduct_321_to_336 n (by omega) h'
  · exact primitiveProduct_337_to_352 n (by omega) hmax

theorem primitiveProduct_upto_384 (n : ℕ) (hn : 5 ≤ n) (hmax : n ≤ 384) :
    HasPrimitiveProduct n := by
  by_cases h : n ≤ 352
  · exact primitiveProduct_upto_352 n hn h
  by_cases h' : n ≤ 368
  · exact primitiveProduct_353_to_368 n (by omega) h'
  · exact primitiveProduct_369_to_384 n (by omega) hmax

theorem sparsePrimitive_upto_384 (n : ℕ) (hn : 0 < n) (hmax : n ≤ 384) :
    HasSparsePrimitive n := by
  by_cases h : n < 5
  · exact sparsePrimitive_upto_128 n hn (by omega)
  · exact (primitiveProduct_upto_384 n (by omega) hmax).sparse

theorem primitiveProduct_upto_400 (n : ℕ) (hn : 5 ≤ n) (hmax : n ≤ 400) :
    HasPrimitiveProduct n := by
  by_cases h : n ≤ 384
  · exact primitiveProduct_upto_384 n hn h
  · exact primitiveProduct_385_to_400 n (by omega) hmax

theorem sparsePrimitive_upto_400 (n : ℕ) (hn : 0 < n) (hmax : n ≤ 400) :
    HasSparsePrimitive n := by
  by_cases h : n < 5
  · exact sparsePrimitive_upto_128 n hn (by omega)
  · exact (primitiveProduct_upto_400 n (by omega) hmax).sparse

theorem primitiveProduct_upto_416 (n : ℕ) (hn : 5 ≤ n) (hmax : n ≤ 416) :
    HasPrimitiveProduct n := by
  by_cases h : n ≤ 400
  · exact primitiveProduct_upto_400 n hn h
  · exact primitiveProduct_401_to_416 n (by omega) hmax

theorem sparsePrimitive_upto_416 (n : ℕ) (hn : 0 < n) (hmax : n ≤ 416) :
    HasSparsePrimitive n := by
  by_cases h : n < 5
  · exact sparsePrimitive_upto_128 n hn (by omega)
  · exact (primitiveProduct_upto_416 n (by omega) hmax).sparse

theorem primitiveProduct_upto_432 (n : ℕ) (hn : 5 ≤ n) (hmax : n ≤ 432) :
    HasPrimitiveProduct n := by
  by_cases h : n ≤ 416
  · exact primitiveProduct_upto_416 n hn h
  · exact primitiveProduct_417_to_432 n (by omega) hmax

theorem sparsePrimitive_upto_432 (n : ℕ) (hn : 0 < n) (hmax : n ≤ 432) :
    HasSparsePrimitive n := by
  by_cases h : n < 5
  · exact sparsePrimitive_upto_128 n hn (by omega)
  · exact (primitiveProduct_upto_432 n (by omega) hmax).sparse

theorem primitiveProduct_upto_512 (n : ℕ) (hn : 5 ≤ n) (hmax : n ≤ 512) :
    HasPrimitiveProduct n := by
  by_cases h : n ≤ 432
  · exact primitiveProduct_upto_432 n hn h
  by_cases h : n ≤ 448
  · exact primitiveProduct_433_to_448 n (by omega) h
  by_cases h : n ≤ 464
  · exact primitiveProduct_449_to_464 n (by omega) h
  by_cases h : n ≤ 480
  · exact primitiveProduct_465_to_480 n (by omega) h
  by_cases h : n ≤ 496
  · exact primitiveProduct_481_to_496 n (by omega) h
  exact primitiveProduct_497_to_512 n (by omega) hmax

theorem sparsePrimitive_upto_512 (n : ℕ) (hn : 0 < n) (hmax : n ≤ 512) :
    HasSparsePrimitive n := by
  by_cases h : n < 5
  · exact sparsePrimitive_upto_128 n hn (by omega)
  · exact (primitiveProduct_upto_512 n (by omega) hmax).sparse

end GF2Sparse
