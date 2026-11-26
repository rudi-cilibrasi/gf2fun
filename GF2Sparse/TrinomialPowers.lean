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

/-- Every power of the form 2^k+1 acts bijectively on an odd-degree binary field's units. -/
theorem odd_mersenne_coprime {n : ℕ} (hn : Odd n) (k : ℕ) :
    (2^n-1).Coprime (2^k+1) := by
  apply Nat.coprime_of_dvd
  intro p hp hm hd
  have plus : p ∣ 2^(k*n)+1 := hd.trans (by
    simpa only [← pow_mul, one_pow] using hn.nat_add_dvd_pow_add_pow (2^k) 1)
  have minus : p ∣ 2^(k*n)-1 := hm.trans (by
    simpa only [← pow_mul, Nat.mul_comm n k] using Nat.sub_one_dvd_pow_sub_one (2^n) k)
  have pos := Nat.two_pow_pos (k*n)
  have htwo : p ∣ 2 := (show 2^(k*n)+1-(2^(k*n)-1) = 2 by omega) ▸ Nat.dvd_sub plus minus
  have he : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 htwo
  obtain ⟨j, hj⟩ := hn
  have hpos : 0 < n := by omega
  subst p
  have even : 2 ∣ 2^n := dvd_pow_self 2 (by omega)
  have pos' := Nat.two_pow_pos n
  omega

/-- The four terms of the binomial block, with one isolated source term. -/
theorem binary_block_identity (a t u k : ℕ) :
    sampledBlock a t u (2^k+1) =
      X^a + X^t * (X^((2^k+1)*u) + X^(2^k*u) + X^u + 1) := by
  unfold sampledBlock
  rw [pow_succ, add_pow_expChar_pow, one_pow]
  simp only [← pow_mul, Nat.mul_comm u (2^k), add_mul, one_mul]
  ring

/-- If the isolated exponent cancels a block tap, the endpoint trinomial has a short order. -/
theorem root_pow_one_of_block_collision {K : Type*} [CommRing K] [CharP K 2]
    {r : K} {k : ℕ} (hr : r^(2^k+1) = r+1) : r^((2^k+1)*2^k+1) = 1 := by
  rw [pow_succ, pow_mul, hr, add_pow_expChar_pow, one_pow, add_mul, one_mul, ← pow_succ, hr]
  rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]

theorem primitive_binary_block {a t u k : ℕ} (hu : 0 < u)
    (hd : a ≠ t + (2^k+1)*u) (hn : Odd (max a (t+(2^k+1)*u)))
    (hs : Primitive (blockEndpoints a t u (2^k+1))) :
    Primitive (sampledBlock a t u (2^k+1)) :=
  (sampledBlock_primitive_iff hu (Nat.succ_pos _) hd).2 ⟨hs, odd_mersenne_coprime hn k⟩

/-- When the block spans the degree, its two complementary interior positions
and its isolated trinomial tap determine the two parameters uniquely. -/
theorem complementary_taps_injective {n h j a b : ℕ} (hn : Odd n)
    (hh : h+h < n) (hj : j+j < n) (ha : a < n) (hb : b < n)
    (ha₁ : a ≠ h) (ha₂ : a ≠ n-h) (hb₁ : b ≠ j) (hb₂ : b ≠ n-j)
    (he : ({h, n-h, a} : Finset ℕ) = {j, n-j, b}) : h = j ∧ a = b := by
  have mem (i : ℕ) : (i = h ∨ i = n-h ∨ i = a) ↔ (i = j ∨ i = n-j ∨ i = b) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using (Finset.ext_iff.mp he i)
  obtain ⟨k, hk⟩ := hn
  have m₁ := mem h
  have m₂ := mem (n-h)
  have m₃ := mem j
  have m₄ := mem (n-j)
  have m₅ := mem a
  omega

end GF2Sparse.TrinomialPowers
