import GF2Sparse.FrobeniusWitness
import GF2Sparse.OreNorms

/-! Logarithms of polynomial quotients of products of linearized seed residues. -/

namespace GF2Sparse.OreClassLogs

open Polynomial

private def positions (g : ℕ) := (List.range (g.log2 + 1)).filter g.testBit

private theorem linearized_decode (js : List ℕ) :
    decode (xorShifts (js.map (fun j => 2^j)) 1) = X * oreLift (decode (xorShifts js 1)) := by
  induction js with
  | nil =>
    have hz : oreLift 0 = 0 := toFinsupp_injective (Finsupp.embDomain_zero oreIndex)
    simp [xorShifts, hz]
  | cons j js ih =>
    simp only [List.map_cons, xorShifts, decode_xor, decode_shift_by, decode_one,
      mul_one, oreLift_add, oreLift_X_pow, mul_add, ih]
    rw [← pow_succ', Nat.sub_add_cancel (Nat.two_pow_pos j)]

/-- Multiply a mask by the linearized polynomials for a list of binary seed labels. -/
def multiplyLabels : List ℕ → ℕ → ℕ
  | [], w => w
  | g :: gs, w => xorShifts ((positions g).map (fun j => 2^j)) (multiplyLabels gs w)

/-- The sum of Frobenius exponents associated with the seed labels. -/
def exponent (log : ℕ → ℕ) (gs : List ℕ) := (gs.map (fun g => 2^(log g))).sum

private def residueCheck (degree seed : ℕ) (log : ℕ → ℕ) (g : ℕ) : Bool :=
  xPow degree seed (log g) == xorShifts (positions g) 1

variable {K : Type*} [Field K] [Algebra (ZMod 2) K]

private theorem multiplyLabels_eval {n p : ℕ} {z : K}
    (hz : aeval z (oreLift (decode p)) = 0) (log : ℕ → ℕ) (gs : List ℕ) (w : ℕ)
    (h : ∀ g ∈ gs, residueCheck n p log g = true) :
    aeval z (decode (multiplyLabels gs w)) = z^(exponent log gs) * aeval z (decode w) := by
  induction gs with
  | nil => simp [multiplyLabels, exponent]
  | cons g gs ih =>
    have hg := dvd_X_pow_sub_decode (beq_iff_eq.1 (h g List.mem_cons_self))
    have hv := ore_conjugate_of_seed_remainder hz hg
    rw [multiplyLabels, decode_xorShifts, linearized_decode, map_mul, map_mul, aeval_X,
      ← hv, ih (fun u hu => h u (List.mem_cons_of_mem _ hu))]
    simp [exponent, pow_add, mul_assoc]

/-- Numerator and denominator factorization identities are checked in the polynomial ring.
Only the individual Frobenius exponents are checked in the smaller seed quotient. -/
def check (degree seed : ℕ) (log : ℕ → ℕ) (mask : ℕ) (pos neg : List ℕ) : Bool :=
  multiplyLabels neg mask == multiplyLabels pos 1 &&
    (pos ++ neg).all (residueCheck degree seed log)

theorem check_sound {degree seed mask : ℕ} {log : ℕ → ℕ} {pos neg : List ℕ}
    {z : K} (hz : aeval z (oreLift (decode seed)) = 0) (hne : z ≠ 0)
    (h : check degree seed log mask pos neg = true) :
    aeval z (decode mask) = z^(exponent log pos) / z^(exponent log neg) := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hm, ha⟩ := h
  have hp := multiplyLabels_eval hz log pos 1 (fun g hg => ha g (List.mem_append_left neg hg))
  have hn := multiplyLabels_eval hz log neg mask (fun g hg => ha g (List.mem_append_right pos hg))
  rw [hm, hp, decode_one, map_one, mul_one] at hn
  exact (eq_div_iff (pow_ne_zero _ hne)).2 (by rw [mul_comm]; exact hn.symm)

end GF2Sparse.OreClassLogs
