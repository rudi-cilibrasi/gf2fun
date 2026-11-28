import GF2Sparse.CubicImage
import GF2Sparse.PackedOrder
import GF2Sparse.PartialOrder

/-! A primitive cubing pair in degree 27 and an irreducible weight-seven cube in degree 1229. -/

namespace GF2Sparse.CubedExamples
open Polynomial PackedSquare

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

private def taps27 : List ℕ := [27,17,10,7,0]
private def taps1229 : List ℕ := [1229,66,33,11,0]

noncomputable def p27 : BinaryPoly := X^27+(X^17+(X^10+(X^7+1)))
noncomputable def q27 : BinaryPoly := X^27+(X^10+(X^9+(X^7+1)))
noncomputable def p1229 : BinaryPoly := X^1229+(X^66+(X^33+(X^11+1)))
noncomputable def q1229 : BinaryPoly := X^1229+(X^823+(X^417+(X^66+(X^55+(X^33+1)))))

private theorem decode27 : decode (xorShifts taps27 1) = p27 := by
  simp only [taps27, xorShifts, decode_xor, decode_shift_by, decode_one, decode_zero,
    pow_zero, mul_one, add_zero, p27]

theorem primitive_p27 : Primitive p27 := by
  rw [← decode27]
  exact (check_sound (f := xorShifts taps27 1) (n := 27) (factors := [7,73,262657])
    (by intro p hp; simp at hp; rcases hp with rfl | rfl | rfl <;> norm_num)
    (by decide +kernel)).2.2

theorem source27 : CubicImage.source (X^9+1) (X^3+X^2) (X^5) = p27 := by
  simp only [CubicImage.source, map_add, map_pow, map_one, expand_X, p27]
  ring

private theorem three_eq_one : (3 : BinaryPoly) = 1 := by
  calc
    (3 : BinaryPoly) = 2+1 := by norm_num
    _ = 1 := by rw [CharTwo.two_eq_zero (R := BinaryPoly), zero_add]

theorem image27 : CubicImage.image (X^9+1) (X^3+X^2) (X^5) = q27 := by
  simp only [CubicImage.image, q27, pow_succ _ 2, CharTwo.add_sq]
  ring_nf
  simp only [CharTwo.two_eq_zero, three_eq_one, mul_zero, mul_one, add_zero]

theorem primitive_q27 : Primitive q27 := by
  have hn : p27.natDegree = 27 := by rw [← decode27, natDegree_decode]; decide +kernel
  rw [← image27, CubicImage.primitive_image_iff, source27]
  · exact ⟨primitive_p27, hn ▸ (by decide : Odd 27)⟩
  · rw [source27, hn]; decide

private abbrev mask1229 := xorShifts taps1229 1
private theorem decode1229 : decode mask1229 = p1229 := by
  simp only [mask1229, taps1229, xorShifts, decode_xor, decode_shift_by, decode_one, decode_zero,
    pow_zero, mul_one, add_zero, p1229]

private theorem degree1229 : (decode mask1229).natDegree = 1229 :=
  (natDegree_decode _).trans (by decide +kernel)

theorem irreducible_p1229 : Irreducible p1229 := by
  rw [← decode1229]
  apply irreducible_of_prime_degree_power (by rw [degree1229]; norm_num)
  · intro x
    rw [decode1229]
    fin_cases x <;> simp only [p1229, eval_add, eval_pow, eval_X, eval_one] <;> decide +kernel
  · let stages := stagesFor 11
    have h := powerBits_sound (n := 1229) (width := 1229) (fuel := 3) (js := taps1229)
      (stages := stages) (f := mask1229) (e := 2^1229-1) (v := 1)
      (by decide +kernel) rfl Nat.lt_log2_self (by decide +kernel)
    simpa only [degree1229, decode_one, map_one] using h.symm

theorem source1229 : CubicImage.source (X^22+(X^11+1)) 0 (X^409+X^3) = p1229 := by
  simp only [CubicImage.source, map_add, map_pow, map_one, map_zero, expand_X, p1229, mul_zero, add_zero]
  ring

theorem image1229 : CubicImage.image (X^22+(X^11+1)) 0 (X^409+X^3) = q1229 := by
  simp only [CubicImage.image, q1229, pow_succ _ 2, CharTwo.add_sq]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

theorem irreducible_q1229 : Irreducible q1229 := by
  have hd : p1229.natDegree = q1229.natDegree := by
    rw [← source1229, ← image1229, CubicImage.degree_image]
  have hdiv : p1229 ∣ expand (ZMod 2) 3 q1229 := by
    rw [← source1229, ← image1229]
    exact CubicImage.source_dvd_expand_image _ _ _
  have hodd : Odd p1229.natDegree := by rw [← decode1229, degree1229]; decide
  exact (irreducible_iff_of_coprime_sampling hd hdiv ((mersenne_coprime_three_iff_odd _).2 hodd)).2
    irreducible_p1229

end GF2Sparse.CubedExamples
