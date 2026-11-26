import GF2Sparse.MersenneDivisors

/-! Integer estimates and the prime sieve for generation by two constant fields. -/

namespace GF2Sparse.FactorFieldIndex

/-- Cleared form of the decreasing tail bound for the three character-weight blocks. -/
theorem tail_bound {y : ℕ} (hy : 2048 ≤ y) :
    (7076*y^2 + 17487*y + 16672)^2 < 64*83*9452*y^4 := by
  have h₁ : 17487*y + 16672 ≤ 18432*y := by omega
  have h₂ : 18432*y ≤ 9*y^2 := by nlinarith [Nat.mul_le_mul_right y hy]
  have h₃ : 7076*y^2 + 17487*y + 16672 ≤ 7085*y^2 := by omega
  calc
    _ ≤ (7085*y^2)^2 := Nat.pow_le_pow_left h₃ 2
    _ = 7085^2*y^4 := by ring
    _ < _ := Nat.mul_lt_mul_of_pos_right (by decide) (by positivity)

/-- In prime extension degree every possible small factor has one of twenty multipliers. -/
theorem prime_multiplier {n q p : ℕ} (hn : n.Prime) (ho : Odd n) (hp : p.Prime)
    (hd : p ∣ 2^n - 1) (hcap : p ≤ 83*q) (hq : 2*q < n) :
    ∃ k, 1 ≤ k ∧ k ≤ 20 ∧ p = 2*n*k+1 ∧ (p % 8 = 1 ∨ p % 8 = 7) := by
  obtain ⟨k, hk⟩ := prime_mersenne_factor_progression hn ho hp hd
  have hpos := hp.two_le
  have heq : p = 2*n*k+1 := by omega
  refine ⟨k, ?_, ?_, heq, odd_mersenne_prime_mod_eight ho hp hd⟩
  · by_contra! h
    have : k = 0 := by omega
    simp [this] at heq
    omega
  · by_contra! h
    have hl := Nat.mul_le_mul_left (2*n) (show 21 ≤ k by omega)
    nlinarith

def allowed (a k : ℕ) : Bool :=
  let p := 2*a*k+1
  (p % 8 == 1 || p % 8 == 7) && p % 3 != 0 && p % 5 != 0

def multipliers (a : ℕ) : List ℕ :=
  ((List.range 20).map (· + 1)).filter (allowed a)

/-- The sieve on the unit residue classes modulo 60 leaves at most six multipliers. -/
theorem residue_sieve : (List.range 60).all (fun a =>
    decide (a.Coprime 60 → (multipliers a).length ≤ 6)) = true := by decide +kernel

/-- The degree-1229 linear cutoff leaves just 36871. Testing divisibility also
removes composite progression entries, using the fact that the list has one survivor. -/
theorem degree1229_sieve :
    (((multipliers 1229).map (fun k => 2458*k+1)).filter (fun p =>
      decide (p ≤ 42496 ∧ p ∣ 2^1229-1))) = [36871] := by decide +kernel

end GF2Sparse.FactorFieldIndex
