import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-! Residue classes used in the search for prime factors of odd Mersenne numbers. -/

namespace GF2Sparse

private theorem pow_two_eq_one_mod_factor {n q : ℕ} (hd : q ∣ 2^n-1) :
    (2 : ZMod q)^n = 1 := by
  have h := (ZMod.natCast_eq_zero_iff (2^n-1) q).2 hd
  rw [Nat.cast_sub (Nat.two_pow_pos n), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
    sub_eq_zero] at h
  exact h

/-- Every prime factor of a Mersenne number with odd exponent is ±1 modulo eight. -/
theorem odd_mersenne_prime_mod_eight {n q : ℕ} (hn : Odd n) (hq : q.Prime)
    (hd : q ∣ 2^n-1) : q % 8 = 1 ∨ q % 8 = 7 := by
  letI : Fact q.Prime := ⟨hq⟩
  have hp := pow_two_eq_one_mod_factor hd
  obtain ⟨k, rfl⟩ := hn
  have hne : q ≠ 2 := by
    rintro rfl
    have hzero : (2 : ZMod 2) = 0 := by exact_mod_cast ZMod.natCast_self 2
    rw [hzero, zero_pow (by omega)] at hp
    exact zero_ne_one hp
  apply (ZMod.exists_sq_eq_two_iff hne).1
  refine ⟨(2 : ZMod q)^(k+1), ?_⟩
  rw [← pow_add, show k+1+(k+1) = (2*k+1)+1 by omega, pow_succ, hp, one_mul]

/-- For an odd prime exponent p, the residue progression has step 2p. -/
theorem prime_mersenne_factor_progression {p q : ℕ} (hp : p.Prime) (ho : Odd p)
    (hq : q.Prime) (hd : q ∣ 2^p-1) : 2*p ∣ q-1 := by
  letI : Fact q.Prime := ⟨hq⟩
  have hpow := pow_two_eq_one_mod_factor hd
  have h8 := odd_mersenne_prime_mod_eight ho hq hd
  have hq2 : q ≠ 2 := by omega
  have htwo : (2 : ZMod q) ≠ 0 := by
    intro h
    have hn : (2 : ZMod q) = ((2 : ℕ) : ZMod q) := by norm_num
    have hdiv := (ZMod.natCast_eq_zero_iff 2 q).1 (hn ▸ h)
    have := Nat.le_of_dvd (by decide : 0 < 2) hdiv
    have := hq.two_le
    omega
  have he : orderOf (2 : ZMod q) = p := by
    apply ((Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hpow)).resolve_left
    intro he
    have hh := orderOf_eq_one_iff.1 he
    have : (1 : ZMod q) = 0 := by linear_combination hh
    exact one_ne_zero this
  have hdq := orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one (2 : ZMod q) htwo)
  rw [he, ZMod.card] at hdq
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_two_left.mpr ho)
    (by omega) hdq

end GF2Sparse
