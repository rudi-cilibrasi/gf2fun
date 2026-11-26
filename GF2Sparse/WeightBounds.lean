import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Sqrt

/-! Exact arithmetic for the character-sum weight bounds in Section 76 of the note. -/

namespace GF2Sparse.WeightBounds

/-- Fix the first subset. Count the choices of the second subset and the free
coefficients that give odd weight strictly greater than the cutoff. -/
def overweightExtensions (d a free cutoff : ℕ) : ℕ :=
  ((List.range (free + 1)).map fun k =>
    if k % 2 = 1 then
      free.choose k * ((List.range (a + 1)).map fun j =>
        if cutoff < 2 + 2 * (a - j) + k then
          a.choose j * (d - a).choose (a - j)
        else 0).sum
    else 0).sum

/-- The integer inequality obtained by clearing the positive denominator of
the prime-degree count and asking for at least the given number of polynomials. -/
def countInequality (n d a cutoff primes count : ℕ) : Prop :=
  (2 * n + 1) * 2 ^ (2 * d) *
      ((primes + 1) * (2 * d) * ((2 ^ n).sqrt + 1) +
        n * (overweightExtensions d a (n - 1 - 2 * d) cutoff + count)) ≤
    (2 * n + 1 - primes) * (2 ^ n - 1) * d.choose a

theorem entropyComparison : 7 ^ 462 < (2 : ℕ) ^ 1297 ∧
    713 * 5000 < 1159 * 3076 := by decide +kernel

theorem orderPrimeCount1229 : (2 : ℕ) ^ 1229 - 1 < 2459 ^ 110 := by decide +kernel

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem count1229Weight329 : countInequality 1229 411 54 329 109 (2 ^ 619 + 1) := by
  unfold countInequality overweightExtensions
  rw [Nat.choose_eq_fast_choose]
  decide +kernel

theorem count1229Weight327 : countInequality 1229 414 55 327 19 (2 ^ 613 + 1) := by
  unfold countInequality overweightExtensions
  rw [Nat.choose_eq_fast_choose]
  decide +kernel

end GF2Sparse.WeightBounds
