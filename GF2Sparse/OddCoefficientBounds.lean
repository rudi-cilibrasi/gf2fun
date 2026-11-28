import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.ReduceModChar

/-! Squaring modulo a squarefree divisor in the odd-coefficient sieve. -/

namespace GF2Sparse.OddCoefficientBounds

open Polynomial

/-- Distinct residue classes of the even part give distinct squared classes.
Adding the fixed odd part does not affect this equivalence. -/
theorem square_residue {K : Type*} [Field K] [CharP K 2]
    (a b odd d : K[X]) (hd : Squarefree d) :
    d ∣ (a ^ 2 + odd) - (b ^ 2 + odd) ↔ d ∣ a - b := by
  have hf : (a ^ 2 + odd) - (b ^ 2 + odd) = (a - b) ^ 2 := by
    ring_nf
    reduce_mod_char!
  rw [hf]
  exact hd.dvd_pow_iff_dvd (by decide)

/-- Clear the positive denominators of the character bound and the level-307
polynomial sieve. The compulsory leading odd term leaves sixteen free bits. -/
theorem degree1229_eleven_odd_terms :
    let heavy := ((List.range 17).filter (11 ≤ ·)).map (Nat.fast_choose 16)
    let error := 20 * 1195 * (Nat.sqrt (2 ^ 1229) + 1)
    20000 * 2 ^ 598 *
        (310 * error + 1229 * (3 * 2 ^ 614 * heavy.sum + 310 * 2 ^ 617)) <
      310 * 19999 * ((2 : ℕ) ^ 1229 - 1) := by
  decide +kernel

/-- The derivative cross-product factors as a square in characteristic two.
Here a² + t b² and c² + t d² are the even-odd decompositions. -/
theorem logarithmic_cross_square {K : Type*} [Field K] [CharP K 2]
    (a b c d t : K) :
    b^2 * (c^2 + t * d^2) + d^2 * (a^2 + t * b^2) = (a*d + b*c)^2 := by
  ring_nf
  reduce_mod_char!

/-- Worst-case union bound for all six projective images, with 598 prescribed bits. -/
theorem degree1229_prescribed_trace_count :
    20000 * 2^598 * (58 * 1197 * (Nat.sqrt (2^1229) + 1) + 1229 * 2^618) <
      19997 * ((2 : ℕ)^1229 - 600) := by
  decide +kernel

/-- Remove the irreducibles with more than twelve odd terms, at 596 prescribed bits. -/
theorem degree1229_twelve_odd_projective :
    let heavy := ((List.range 19).filter (12 ≤ ·)).map (Nat.fast_choose 18)
    let error := 58 * 1193 * (Nat.sqrt (2^1229) + 1)
    20000 * 2^596 * (310 * error + 1229 * (3 * 2^614 * heavy.sum + 310 * 2^619)) <
      310 * 19997 * ((2 : ℕ)^1229 - 598) := by
  decide +kernel

end GF2Sparse.OddCoefficientBounds
