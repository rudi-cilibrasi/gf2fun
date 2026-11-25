import GF2Sparse.PackedSquare
import GF2Sparse.Progressions

/-! Apply the packed power test to a trinomial using its symbolic degree. -/

namespace GF2Sparse.PackedSquare

theorem primitive_trinomial_of_run {n a width fuel : ℕ} {stages : List (ℕ × ℕ)}
    (ha : 0 < a) (han : a < n) (hp : (mersenne n).Prime)
    (hc : checkBasis width stages = true)
    (hr : PowerBlock width n fuel stages [n,a,0] n 1 1) : Primitive (trinomial n a) := by
  have hdecode : decode (xorShifts [n,a,0] 1) = trinomial n a := decode_trinomial_taps n a
  have hd : (xorShifts [n,a,0] 1).log2 = n := by
    rw [← natDegree_decode, hdecode, trinomial_degree ha han]
  rw [← hdecode]
  exact primitive_of_run (by omega) hd hp hc rfl hr.checked

end GF2Sparse.PackedSquare
