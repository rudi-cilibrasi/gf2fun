import GF2Sparse.Degree1229

/-! Integer inequalities for products of linear and good irreducible norms in the
forward Frobenius presentations. The character estimate is in the research note. -/

namespace GF2Sparse.NormCoverBounds

set_option exponentiation.threshold 8192
set_option maxRecDepth 8192

/-- Positivity after dividing the character estimate by the square root of the
parameter count raised to the number of factors. -/
def cover (groupSize n m q h k : ℕ) : Bool :=
  let removed := if h = 1 then 0 else q + 4
  decide ((groupSize - 1) * (n - 1 + removed) ^ k < (2 ^ (m * h / 2) - removed) ^ k)

def degreeBounds (groupSize n m q : ℕ) (counts : List ℕ) : Bool :=
  counts.length == 5 && (([1, 2, 4, 8, 16] : List ℕ).zip counts).all
    fun (h, k) => cover groupSize n m q h k

theorem binary1229 : degreeBounds (2^1229 - 1) 1229 234 8192 [12, 6, 3, 2, 1] = true := by
  decide +kernel

theorem firstThreeGaps : ([1229, 1231, 1237] : List ℕ).all
    (fun n => degreeBounds (2^n - 1) n 198 2048 [14, 7, 4, 2, 1]) = true := by
  decide +kernel

theorem nextThreeGaps : ([1243, 1249, 1259] : List ℕ).all
    (fun n => degreeBounds (2^n - 1) n 198 2048 [15, 7, 4, 2, 1]) = true := by
  decide +kernel

theorem projected1229 :
    degreeBounds Degree1229.cofactor 1229 234 8192 [9, 5, 3, 2, 1] = true ∧
    degreeBounds Degree1229.cofactor 1229 198 2048 [11, 6, 3, 2, 1] = true := by
  decide +kernel

theorem properSubgroupFraction :
    2^59 * (2^99 + 1228 * 818085338814611458) < 818085338814611458 * 2^99 := by
  decide +kernel

end GF2Sparse.NormCoverBounds
