import GF2Sparse.FrobeniusWitness

/-! The last degree in which a primitive pentanomial has a sparse fifth-power image. -/

namespace GF2Sparse.FifthImage
open Polynomial

noncomputable def source : BinaryPoly := X^25 + (X^13 + (X^9 + (X^8 + 1)))
noncomputable def target : BinaryPoly := X^25 + (X^20 + (X^17 + (X^15 + 1)))

theorem primitive_pair_25 : Primitive source ∧ Primitive target ∧ source ∣ expand (ZMod 2) 5 target := by
  let taps : List ℕ := [25,13,9,8,0]
  let f := xorShifts taps 1
  let g := xorShifts [25,20,17,15,0] 1
  let expanded := xorShifts [125,100,85,75,0] 1
  have hf : decode f = source := by
    simp only [f, taps, xorShifts, decode_xor, decode_shift_by, decode_one, decode_zero,
      pow_zero, mul_one, add_zero, source]
  have hg : decode g = target := by
    simp only [g, xorShifts, decode_xor, decode_shift_by, decode_one, decode_zero,
      pow_zero, mul_one, add_zero, target]
  have he : decode expanded = expand (ZMod 2) 5 target := by
    simp only [expanded, xorShifts, decode_xor, decode_shift_by, decode_one, decode_zero,
      pow_zero, mul_one, add_zero, target, map_add, map_pow, map_one, expand_X, ← pow_mul]
  have hp : ∀ p ∈ [31,601,1801], Nat.Prime p := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl <;> norm_num
  refine ⟨hf ▸ (check_sound (n := 25) hp (by decide +kernel : check 25 f [31,601,1801] = true)).2.2,
    hg ▸ (check_sound (n := 25) hp (by decide +kernel : check 25 g [31,601,1801] = true)).2.2, ?_⟩
  rw [← hf, ← he]
  apply AdjoinRoot.mk_eq_zero.mp
  rw [← mk_reduceHigh 25 f 24 expanded taps rfl,
    show reduceHigh 25 taps 24 expanded = 0 by decide +kernel, decode_zero, map_zero]

end GF2Sparse.FifthImage
