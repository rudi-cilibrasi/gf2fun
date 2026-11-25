import GF2Sparse.PackedSquare

/-! Primitive product pentanomials found by the PARI search in four Mersenne-prime degrees. -/

namespace GF2Sparse

open PackedSquare

set_option maxRecDepth 32000
set_option maxHeartbeats 16000000
set_option exponentiation.threshold 32768

theorem primitiveProduct_2281_2_39 : Primitive (productCandidate 2281 2 39) :=
  primitive_product_of_check (by decide)
    (lucas_lehmer_sufficiency 2281 (by decide) (by norm_num)) (by decide +kernel)

theorem primitiveProduct_3217_41_84 : Primitive (productCandidate 3217 41 84) :=
  primitive_product_of_check (by decide)
    (lucas_lehmer_sufficiency 3217 (by decide) (by norm_num)) (by decide +kernel)

theorem primitiveProduct_4253_210_263 : Primitive (productCandidate 4253 210 263) :=
  primitive_product_of_check (by decide)
    (lucas_lehmer_sufficiency 4253 (by decide) (by norm_num)) (by decide +kernel)

theorem primitiveProduct_4423_17_26 : Primitive (productCandidate 4423 17 26) :=
  primitive_product_of_check (by decide)
    (lucas_lehmer_sufficiency 4423 (by decide) (by norm_num)) (by decide +kernel)

end GF2Sparse
