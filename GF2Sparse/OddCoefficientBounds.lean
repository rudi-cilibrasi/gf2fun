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

end GF2Sparse.OddCoefficientBounds
