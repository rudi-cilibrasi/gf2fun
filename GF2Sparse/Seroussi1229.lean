import GF2Sparse.Degree1229
import GF2Sparse.PackedOrder

/-! The degree-1229 polynomial in Seroussi's minimum-weight irreducible table. -/

namespace GF2Sparse.Seroussi1229

open Polynomial PackedSquare
open GF2Sparse.Degree1229 (knownPart cofactor)

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

noncomputable def candidate : BinaryPoly := X^1229 + (X^15 + (X^6 + (X^2 + 1)))

private def taps : List ℕ := [1229,15,6,2,0]
private abbrev mask := xorShifts taps 1
private noncomputable abbrev r := AdjoinRoot.root (decode mask)
private def stages := stagesFor 11

private theorem decoded : decode mask = candidate := by
  simp only [mask, taps, xorShifts, decode_xor, decode_shift_by, decode_one, decode_zero,
    pow_zero, mul_one, add_zero, candidate]

private theorem degree_eq : (decode mask).natDegree = 1229 :=
  (natDegree_decode _).trans (by decide +kernel)

private theorem basis : checkBasis 1229 stages = true := by decide +kernel

private def power (e : ℕ) := powerBits 1229 1229 3 stages taps (e.log2+1) e

private theorem power_sound {e v : ℕ} (h : power e = some v) :
    AdjoinRoot.mk (decode mask) (decode v) = r^e :=
  powerBits_sound basis rfl Nat.lt_log2_self h

private theorem full : r^(2^1229-1) = 1 := by
  have h := power_sound (e := 2^1229-1) (v := 1) (by decide +kernel)
  simpa using h.symm

private def nontrivial (e : ℕ) : Bool :=
  match power e with
  | none => false
  | some v => v != 1 && v < 2^1229

private theorem power_ne_one {e : ℕ} (hc : nontrivial e = true) : r^e ≠ 1 := by
  unfold nontrivial at hc
  split at hc
  · contradiction
  · rename_i v hv
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at hc
    intro h
    have hv1 := (power_sound hv).trans h
    have hne : decode v - 1 ≠ 0 := fun he => hc.1
      (decode_injective ((sub_eq_zero.1 he).trans decode_one.symm))
    have hd : (decode v).natDegree < 1229 := by
      rw [natDegree_decode]
      by_cases hz : v = 0
      · simp [hz]
      · exact (Nat.log2_lt hz).2 hc.2
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_decode (by decide +kernel : mask ≠ 0)) hne
      ((natDegree_sub_le _ _).trans_lt (degree_eq ▸ max_lt hd (by simp)))
    simp [hv1]

theorem irreducible_candidate : Irreducible candidate := by
  rw [← decoded]
  apply irreducible_of_prime_degree_power (f := decode mask) (by rw [degree_eq]; norm_num)
  · intro x
    rw [decoded]
    fin_cases x <;> simp only [candidate, eval_add, eval_pow, eval_X, eval_one] <;> decide +kernel
  · simpa only [degree_eq] using full

/-- Two low-degree expressions used to recover missing factor-base logarithms. -/
theorem tail_relations :
    let z := AdjoinRoot.root candidate
    let g := z^15 + (z^6 + (z^2 + 1))
    z^1229 = g ∧ (z^39+1)^32 = z^19*g+1 := by
  letI : Fact (Irreducible candidate) := ⟨irreducible_candidate⟩
  letI : CharP (AdjoinRoot candidate) 2 := charP_of_injective_ringHom (AdjoinRoot.of candidate).injective 2
  dsimp only
  have h : AdjoinRoot.mk candidate candidate = 0 := AdjoinRoot.mk_self
  change AdjoinRoot.mk candidate ((X : BinaryPoly)^1229 + (X^15 + (X^6 + (X^2+1)))) = 0 at h
  simp only [map_add, map_pow, AdjoinRoot.mk_X, map_one, CharTwo.add_eq_zero] at h
  refine ⟨h, ?_⟩
  let z := AdjoinRoot.root candidate
  change (z^39+1)^(2^5) = z^19*(z^15+(z^6+(z^2+1)))+1
  rw [add_pow_expChar_pow, one_pow, ← pow_mul, ← h, ← pow_add, show 39 * 2^5 = 19 + 1229 by decide]

private theorem fold_power {A : Type*} [CommRing A] [CharP A 2] (z : A)
    (d m s : ℕ) : z^d * (z^m + 1)^(2^s) = z^(d + m * 2^s) + z^d := by
  rw [add_pow_expChar_pow, one_pow, mul_add, mul_one, ← pow_mul, ← pow_add]

/-- Three binomial factorizations used in the degree-1229 direct order certificate. -/
theorem folded_relations :
    let z := AdjoinRoot.root candidate
    let g := z^15 + (z^6 + (z^2 + 1))
    z^21 * (z^151 + 1)^8 = g + z^21 ∧
      z^13 * (z^19 + 1)^64 = g + z^13 ∧
      z^3 * (z^613 + 1)^2 = g + z^3 := by
  letI : Fact (Irreducible candidate) := ⟨irreducible_candidate⟩
  letI : CharP (AdjoinRoot candidate) 2 := charP_of_injective_ringHom (AdjoinRoot.of candidate).injective 2
  dsimp only
  rw [← tail_relations.1]
  exact ⟨fold_power _ 21 151 3, fold_power _ 13 19 6, fold_power _ 3 613 1⟩

theorem order_split :
    ∃ t : ℕ, 1 < t ∧ t ∣ cofactor ∧ orderOf (AdjoinRoot.root candidate) = knownPart*t := by
  rw [← decoded]
  apply GF2Sparse.Degree1229.order_split_of_powers r full (power_ne_one (by decide +kernel))
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> exact power_ne_one (by decide +kernel)

end GF2Sparse.Seroussi1229
