import GF2Sparse.SeventhImage

/-! Fifth and seventh powers for trinomials with a midpoint modulo the exponent. -/

namespace GF2Sparse.TrinomialPowers
open Polynomial

private def powerSum {R : Type*} [Semiring R] (m d : ℕ) (a b c : R) : R :=
  a^m + b^m + c^m + a*b^(m-2)*c + a^d*b*c^d

private theorem midpoint_identity {R : Type*} [CommRing R] [CharP R 2] (a c : R)
    {m d : ℕ} (h : (m = 5 ∧ d = 2) ∨ (m = 7 ∧ d = 3)) :
    powerSum m d a (a+c) c = 0 := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> unfold powerSum <;> ring_nf <;> reduce_mod_char!

/-- The two interpolated exponents complete a polynomial of the powered root. -/
theorem midpoint_dvd {m d a b c v w : ℕ} (h : (m = 5 ∧ d = 2) ∨ (m = 7 ∧ d = 3))
    (hv : m*v = a+b*(m-2)+c) (hw : m*w = a*d+b+c*d) :
    (X^b + (X^a + X^c) : BinaryPoly) ∣
      expand (ZMod 2) m (X^a + X^b + X^c + X^v + X^w) := by
  let f : BinaryPoly := X^b + (X^a + X^c)
  let φ := AdjoinRoot.mk f
  have he : φ (X^b) = φ (X^a + X^c) := by
    apply sub_eq_zero.mp
    rw [← map_sub, CharTwo.sub_eq_add]
    exact AdjoinRoot.mk_self
  have hexpand : expand (ZMod 2) m (X^a + X^b + X^c + X^v + X^w) =
      powerSum m d ((X : BinaryPoly)^a) (X^b) (X^c) := by
    simp only [map_add, map_pow, expand_X, powerSum, ← pow_mul, ← pow_add, hv, hw]
    ring
  apply AdjoinRoot.mk_eq_zero.mp
  change φ _ = 0
  rw [hexpand]
  unfold powerSum
  simp only [map_add, map_mul, map_pow]
  have he' : φ X ^ b = φ (X^a + X^c) := by simpa only [map_pow] using he
  rw [he']
  simpa only [powerSum, map_zero, map_add, map_mul, map_pow] using
    congrArg φ (midpoint_identity ((X : BinaryPoly)^a) (X^c) h)

/-- A primitive trinomial whose seventh power has nine terms, even at a Mersenne exponent. -/
theorem nine_terms_17 :
    Primitive (trinomial 17 3) ∧ Primitive (sampledBlock 0 3 2 7) ∧
      (sampledBlock 0 3 2 7).support.card = 9 ∧
      trinomial 17 3 ∣ expand (ZMod 2) 7 (sampledBlock 0 3 2 7) := by
  let taps : List ℕ := [17,3,0]
  have he : decode (xorShifts taps 1) = trinomial 17 3 := by
    simp only [taps, xorShifts, decode_xor, decode_shift_by, decode_one, decode_zero,
      pow_zero, mul_one, add_zero, trinomial]
  have hs : Primitive (trinomial 17 3) := by
    rw [← he]
    exact (check_sound (n := 17) (factors := [131071])
      (by intro p hp; simp at hp; subst p; norm_num) (by decide +kernel)).2.2
  have hb : blockEndpoints 0 3 2 7 = trinomial 17 3 := by
    unfold blockEndpoints trinomial
    ring
  refine ⟨hs, (sampledBlock_primitive_iff (by decide) (by decide) (by decide)).2
    ⟨hb ▸ hs, by decide⟩, ?_, hb ▸ endpoints_dvd_expand_block 0 3 2 7⟩
  let terms : List ℕ := [17,15,13,11,9,7,5,3,0]
  have ht : sampledBlock 0 3 2 7 = decode (xorShifts terms 1) := by
    simp only [terms, xorShifts, decode_xor, decode_shift_by, decode_one, decode_zero,
      pow_zero, mul_one, add_zero, sampledBlock]
    rw [show ((X : BinaryPoly)^2+1)^7 = (((X^2+1)^2)^2)*((X^2+1)^2)*(X^2+1) by ring]
    simp only [CharTwo.add_sq, one_pow]
    ring
  rw [ht, support_decode]
  decide +kernel

end GF2Sparse.TrinomialPowers
