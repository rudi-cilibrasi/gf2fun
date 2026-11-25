import GF2Sparse.CompositionNorm
import GF2Sparse.Table

/-! Five-term compositions from pairs of exponents on Frobenius orbits. -/

namespace GF2Sparse

open Polynomial

/-- The polynomial T^(2^s) + T + 1 whose composition cancels intermediate terms. -/
noncomputable def frobeniusOuter (s : ℕ) : BinaryPoly := X ^ (2 ^ s) + X + 1

/-- The monomials between two exponents under repeated multiplication by 2^s. -/
noncomputable def frobeniusChain (s a k : ℕ) : BinaryPoly :=
  ∑ j ∈ Finset.range k, X ^ (a * (2 ^ s) ^ j)

private theorem chain_boundary (s a k : ℕ) :
    frobeniusChain s a k ^ (2 ^ s) + frobeniusChain s a k =
      X ^ a + X ^ (a * (2 ^ s) ^ k) := by
  induction k with
  | zero => simp [frobeniusChain, zero_pow (Nat.two_pow_pos s).ne', CharTwo.add_self_eq_zero]
  | succ k ih =>
    let q := 2 ^ s
    let u : BinaryPoly := X ^ (a * q ^ k)
    let v : BinaryPoly := X ^ (a * q ^ (k + 1))
    have hs : frobeniusChain s a (k + 1) = frobeniusChain s a k + u := Finset.sum_range_succ _ _
    have hu : u ^ q = v := by simp only [u, v, ← pow_mul, pow_succ, Nat.mul_assoc]
    rw [hs, add_pow_expChar_pow, hu]
    calc
      _ = (frobeniusChain s a k ^ q + frobeniusChain s a k) + u + v := by ac_rfl
      _ = X ^ a + v := by rw [ih, CharTwo.add_cancel_right]

/-- Two chains yield precisely the four endpoints and the constant term. -/
theorem frobenius_pair_composition (s a i b j : ℕ) :
    (frobeniusOuter s).comp (frobeniusChain s a i + frobeniusChain s b j) =
      X ^ a + X ^ (a * (2 ^ s) ^ i) + X ^ b + X ^ (b * (2 ^ s) ^ j) + 1 := by
  simp only [frobeniusOuter, add_comp, pow_comp, X_comp, one_comp, add_pow_expChar_pow]
  calc
    _ = (frobeniusChain s a i ^ (2 ^ s) + frobeniusChain s a i) +
        (frobeniusChain s b j ^ (2 ^ s) + frobeniusChain s b j) + 1 := by ac_rfl
    _ = _ := by rw [chain_boundary, chain_boundary]; ac_rfl

theorem frobeniusOuter_natDegree {s : ℕ} (hs : 0 < s) :
    (frobeniusOuter s).natDegree = 2 ^ s := by
  have hd : ((X + 1 : BinaryPoly)).natDegree = 1 := by
    simpa only [map_one] using natDegree_X_add_C (1 : ZMod 2)
  rw [frobeniusOuter, add_assoc, natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
  rw [hd, natDegree_X_pow]
  exact Nat.one_lt_two_pow hs.ne'

private theorem primitive_outer_certificate (s : ℕ) (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (h : check (2 ^ s) (2 ^ (2 ^ s) ^^^ 2 ^ 1 ^^^ 1) ps = true) :
    Primitive (frobeniusOuter s) := by
  have hx : decode 2 = X := by simpa using decode_pow_two 1
  simpa only [decode_xor, decode_pow_two, decode_one, pow_one, hx, frobeniusOuter] using
    (check_sound hp h).2.2

theorem primitive_frobeniusOuter_one : Primitive (frobeniusOuter 1) := by
  apply primitive_outer_certificate 1 [3]
  · intro p hp
    simp only [List.mem_singleton] at hp
    rw [hp]
    decide
  · decide +kernel

theorem primitive_frobeniusOuter_two : Primitive (frobeniusOuter 2) := by
  apply primitive_outer_certificate 2 [3, 5]
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl <;> decide
  · decide +kernel

private theorem double_lt_two_pow {s : ℕ} (hs : 3 ≤ s) : s + s < 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [pow_succ]; omega

/-- Only the quadratic and quartic outer polynomials can be used for irreducibility.
Every root satisfies z^(2^(2s)) = z. -/
theorem not_irreducible_frobeniusOuter {s : ℕ} (hs : 3 ≤ s) :
    ¬ Irreducible (frobeniusOuter s) := by
  intro hi
  let f := frobeniusOuter s
  letI : Fact (Irreducible f) := ⟨hi⟩
  letI : CharP (AdjoinRoot f) 2 := charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  let z := AdjoinRoot.root f
  have hz : aeval z f = 0 := (AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self
  have hrel : z ^ (2 ^ s) = z + 1 := by
    have he : z ^ (2 ^ s) + (z + 1) = 0 := by
      have hz' : aeval z (X ^ (2 ^ s) + X + 1 : BinaryPoly) = 0 := hz
      rwa [map_add, map_add, map_pow, aeval_X, map_one, add_assoc] at hz'
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left he
  have hfix : z ^ (2 ^ (s + s)) = z := by
    rw [pow_add, pow_mul, hrel, add_pow_expChar_pow, one_pow, hrel, CharTwo.add_cancel_right]
  have hd := (degree_dvd_iff_frobenius hi hz _).2 hfix
  rw [frobeniusOuter_natDegree (by omega)] at hd
  exact (double_lt_two_pow hs).not_ge (Nat.le_of_dvd (by omega) hd)

/-- A common Frobenius step of size s ≥ 3 rules out the entire composition. -/
theorem not_irreducible_frobeniusOuter_comp {s : ℕ} (hs : 3 ≤ s) (h : BinaryPoly) :
    ¬ Irreducible ((frobeniusOuter s).comp h) := by
  intro hi
  have hm : 0 < h.natDegree := by
    have hd := hi.natDegree_pos
    rw [natDegree_comp] at hd
    by_contra! hz
    simp [Nat.eq_zero_of_le_zero hz] at hd
  letI : IsLocalHom (compRingHom h) := ⟨by
    intro g hu
    change IsUnit (g.comp h) at hu
    have hg : g ≠ 0 := fun he => by simp [he] at hu
    by_contra hn
    apply not_isUnit_of_natDegree_pos _ _ hu
    rw [natDegree_comp]
    exact Nat.mul_pos ((binary_monic hg).natDegree_pos_of_not_isUnit hn) hm⟩
  exact not_irreducible_frobeniusOuter hs (Irreducible.of_map (f := compRingHom h) hi)

end GF2Sparse
