import GF2Sparse.SparseOrderBounds

/-! Arithmetic consequences of a collision or separation of signed Frobenius powers. -/

namespace GF2Sparse

/-- If two exponents differ by a Frobenius power modulo the order, raising them to the
extension degree gives the same residue. The signed case uses a negative exponent `b`. -/
theorem frobenius_exponents_modEq {R a b : ℤ} {n j : ℕ}
    (hperiod : (2 : ℤ) ^ n ≡ 1 [ZMOD R])
    (hcollision : a ≡ b * (2 : ℤ) ^ j [ZMOD R]) : a ^ n ≡ b ^ n [ZMOD R] := by
  have h : ((2 : ℤ) ^ j) ^ n ≡ 1 [ZMOD R] := by
    rw [← pow_mul, Nat.mul_comm j n, pow_mul]
    simpa using hperiod.pow j
  apply (hcollision.pow n).trans
  simpa only [mul_pow, mul_one] using h.mul_left (b ^ n)

/-- A congruence modulo `s` that separates two powers in the field excludes every root
order dividing `s`. If the ambient order is `s * p`, this test removes `p` from the index. -/
theorem prime_test_of_separated_powers {G : Type*} [Group G] {x : G} {a b : ℤ} {s p : ℕ}
    (hp : 0 < p) (horder : orderOf x ∣ s * p)
    (hmod : a ≡ b [ZMOD (s : ℤ)]) (hne : x ^ a ≠ x ^ b) :
    ¬ p ∣ (s * p) / orderOf x := by
  intro h
  obtain ⟨k, hk⟩ := h
  have hm := Nat.div_mul_cancel horder
  rw [hk] at hm
  have hs : k * orderOf x = s := Nat.eq_of_mul_eq_mul_left hp (by
    simpa only [Nat.mul_assoc, Nat.mul_comm s p] using hm)
  have hd : orderOf x ∣ s := ⟨k, by rw [← hs, Nat.mul_comm]⟩
  apply hne
  exact zpow_eq_zpow_iff_modEq.mpr (hmod.of_dvd (by exact_mod_cast hd))

end GF2Sparse
