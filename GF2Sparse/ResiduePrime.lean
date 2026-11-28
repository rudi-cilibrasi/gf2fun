import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Excluding a factorization when every prime divisor is one modulo F. -/

namespace GF2Sparse

/-- A small-multiplier exclusion and a bounded two-factor exclusion together
certify primality. The modulus F need not reach the cube root of n. -/
theorem prime_of_residue_exclusions {n F : ℕ} (hn : 2 ≤ n)
    (hnF : n % F = 1) (hprime : ∀ p : ℕ, p.Prime → p ∣ n → p % F = 1)
    (small : ∀ a : ℕ, 0 < a → a * F^3 ≤ n → ¬ (1 + F*a) ∣ n)
    (balanced : ∀ a b : ℕ, 0 < a → a ≤ b → b ≤ F → (1 + F*a)*(1 + F*b) ≠ n) :
    n.Prime := by
  by_contra h
  let p := n.minFac
  let q := n / p
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hpq : p*q = n := Nat.mul_div_cancel' hpn
  have hle : p ≤ q := by
    have hs : p^2 ≤ n := Nat.minFac_sq_le_self (by omega) h
    have hp0 := hp.pos
    rw [← hpq, pow_two] at hs
    exact Nat.le_of_mul_le_mul_left hs hp0
  have hpr := hprime p hp hpn
  have hqr : q % F = 1 := by
    have he := congrArg (· % F) hpq
    simpa only [Nat.mul_mod p q F, hpr, one_mul, Nat.mod_mod, hnF] using he
  let a := p / F
  let b := q / F
  have ha : p = 1 + F*a := by simpa [a, hpr] using (Nat.mod_add_div p F).symm
  have hb : q = 1 + F*b := by simpa [b, hqr] using (Nat.mod_add_div q F).symm
  have ha0 : 0 < a := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hp.ne_one (by simpa only [hz, Nat.mul_zero, Nat.add_zero] using ha)
  have hab : a ≤ b := Nat.div_le_div_right hle
  have eqn : (1 + F*a)*(1 + F*b) = n := by simpa only [← ha, ← hb] using hpq
  by_cases hbound : b ≤ F
  · exact balanced a b ha0 hab hbound eqn
  · apply small a ha0 _ (ha ▸ hpn)
    calc
      a * F^3 = (F*a)*(F*F) := by ring
      _ ≤ (1 + F*a)*(1 + F*b) :=
        Nat.mul_le_mul (by omega) ((Nat.mul_le_mul_left F (by omega : F ≤ b)).trans (by omega))
      _ = n := eqn

theorem multiplier_discriminant (a b : ℤ) : (a+b)^2 - 4*(a*b) = (a-b)^2 := by ring

theorem two_not_square_mod_five : ∀ x : ZMod 5, x^2 ≠ 2 := by decide

end GF2Sparse
