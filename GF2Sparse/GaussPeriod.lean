import GF2Sparse.Roots
import Mathlib.RingTheory.Polynomial.Dickson

/-! Frobenius substitutions and subgroup membership for Gauss period relations. -/

namespace GF2Sparse

open Polynomial

/-- Signed congruence of exponents gives the Frobenius action on a reciprocal pair. -/
theorem dickson_period_frobenius {K : Type*} [Field K] [CharP K 2]
    (z : Kˣ) {p m k : ℕ} (hz : z ^ p = 1)
    (hm : m ≡ 2^k [MOD p] ∨ p ∣ m + 2^k) :
    (dickson 1 (1 : K) m).eval ((z : K) + (z : K)⁻¹) =
      ((z : K) + (z : K)⁻¹) ^ (2^k) := by
  have hs : z ^ m = z ^ (2^k) ∨ z ^ m = (z ^ (2^k))⁻¹ := by
    rcases hm with h | ⟨j, hj⟩
    · exact Or.inl (pow_eq_pow_iff_modEq.mpr (h.of_dvd (orderOf_dvd_of_pow_eq_one hz)))
    · apply Or.inr
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_add, hj, pow_mul, hz, one_pow]
  rw [dickson_one_one_eval_add_inv _ _ (mul_inv_cancel₀ z.ne_zero), add_pow_char_pow,
    inv_pow, inv_pow]
  rcases hs with h | h
  · have hv := congrArg (fun u : Kˣ => (u : K)) h
    simpa only [Units.val_pow_eq_pow_val] using congrArg (fun t : K => t + t⁻¹) hv
  · have hv : (z : K)^m = ((z : K)^(2^k))⁻¹ := by
      simpa using congrArg (fun u : Kˣ => (u : K)) h
    rw [hv, inv_inv, add_comm]

/-- A trace from the norm-one torus determines its argument up to inversion. -/
theorem period_eq_iff {K : Type*} [Field K] (u v : Kˣ) :
    (u : K) + (u : K)⁻¹ = (v : K) + (v : K)⁻¹ ↔ u = v ∨ u = v⁻¹ := by
  constructor
  · intro h
    have hr : ((u : K) - (v : K)) * ((u : K) - (v : K)⁻¹) = 0 := by
      calc
        _ = (u : K) * (((u : K) + (u : K)⁻¹) - ((v : K) + (v : K)⁻¹)) := by
          field_simp
          ring
        _ = 0 := by rw [h, sub_self, mul_zero]
    rcases mul_eq_zero.mp hr with h | h
    · exact Or.inl (Units.ext (sub_eq_zero.mp h))
    · exact Or.inr (Units.ext (by simpa using sub_eq_zero.mp h))
  · rintro (rfl | rfl)
    · rfl
    · simp [add_comm]

/-- Frobenius fixes the period exactly at the signed order of two. -/
theorem period_fixed_iff {K : Type*} [Field K] [CharP K 2] (z : Kˣ) (k : ℕ) :
    ((z : K) + (z : K)⁻¹)^(2^k) = (z : K) + (z : K)⁻¹ ↔
      2^k ≡ 1 [MOD orderOf z] ∨ orderOf z ∣ 2^k + 1 := by
  rw [add_pow_char_pow, inv_pow]
  change ((z^(2^k) : Kˣ) : K) + ((z^(2^k) : Kˣ) : K)⁻¹ = _ ↔ _
  rw [period_eq_iff]
  apply or_congr
  · simpa using (pow_eq_pow_iff_modEq (x := z) (n := 2^k) (m := 1))
  · constructor
    · intro h
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_succ, h, inv_mul_cancel]
    · intro h
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, pow_eq_one_iff_modEq]
      exact Nat.modEq_zero_iff_dvd.mpr h

set_option maxRecDepth 4096 in
set_option exponentiation.threshold 2048 in
/-- Every order-2459 reciprocal pair gives a coordinate of degree 1229. -/
theorem degree_period_1229 {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    (z : Kˣ) (hz : orderOf z = 2459) :
    (minpoly (ZMod 2) ((z : K) + (z : K)⁻¹)).natDegree = 1229 := by
  let a := (z : K) + (z : K)⁻¹
  have hbig : a^(2^1229) = a := (period_fixed_iff z 1229).2 (by
    rw [hz]
    exact Or.inr (by decide +kernel))
  have hi : IsIntegral (ZMod 2) a := by
    refine ⟨X^(2^1229) - X, monic_X_pow_sub (by rw [degree_X]; exact_mod_cast (by decide : 1 < 2^1229)), ?_⟩
    change aeval a (X^(2^1229) - X : BinaryPoly) = 0
    simpa only [map_sub, map_pow, aeval_X, sub_eq_zero] using hbig
  have hd := degree_dvd_iff_frobenius (minpoly.irreducible hi) (minpoly.aeval (ZMod 2) a)
  apply ((Nat.dvd_prime (by decide +kernel : Nat.Prime 1229)).mp ((hd 1229).2 hbig)).resolve_left
  intro hone
  have hsmall := (period_fixed_iff z 1).1 ((hd 1).1 (hone ▸ dvd_rfl))
  rw [hz] at hsmall
  exact (by decide : ¬(2^1 ≡ 1 [MOD 2459] ∨ 2459 ∣ 2^1+1)) hsmall

/-- Binary polynomial values at the Dickson conjugate inherit the same Frobenius power. -/
theorem aeval_period_dickson {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    (P : BinaryPoly) (z : Kˣ) {p m k : ℕ} (hz : z ^ p = 1)
    (hm : m ≡ 2^k [MOD p] ∨ p ∣ m + 2^k) :
    aeval ((dickson 1 (1 : K) m).eval ((z : K) + (z : K)⁻¹)) P =
      (aeval ((z : K) + (z : K)⁻¹) P) ^ (2^k) := by
  rw [dickson_period_frobenius z hz hm, aeval_dyadic]

/-- A coefficient invertible modulo a group exponent allows recovery of subgroup membership. -/
theorem mem_of_unit_pivot {G : Type*} [Monoid G] (H : Submonoid G)
    {x : G} {c M : ℕ} (hM : x^M = 1) (hc : c.Coprime M) (h : x^c ∈ H) : x ∈ H := by
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime
    (hc.of_dvd_right (orderOf_dvd_of_pow_eq_one hM))
  exact hj ▸ H.pow_mem h j

/-- A power coprime to the subgroup index detects membership in a normal subgroup. -/
theorem mem_of_pow_coprime_index {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    {x : G} {k : ℕ} (hk : k.Coprime H.index) (hx : x ^ k ∈ H) : x ∈ H := by
  apply (QuotientGroup.eq_one_iff x).mp
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes hk _ (orderOf_dvd_natCard _)
  apply orderOf_dvd_of_pow_eq_one
  exact (QuotientGroup.mk_pow H x k).symm.trans ((QuotientGroup.eq_one_iff _).mpr hx)

/-- A logarithm after raising to the known part of the order proves membership
in the original cyclic subgroup. -/
theorem mem_zpowers_of_projected_log {G : Type*} [CommGroup G] {r x : G} {k c e : ℕ}
    (hk : 0 < k) (hkc : k.Coprime c) (hcard : Nat.card G = k * c)
    (hr : k ∣ orderOf r) (hx : x ^ k = (r ^ k) ^ e) : x ∈ Subgroup.zpowers r := by
  let H := Subgroup.zpowers r
  obtain ⟨t, ht⟩ := hr
  have hsize : Nat.card H = k * t := (Nat.card_zpowers r).trans ht
  have hid : t * H.index = c := Nat.eq_of_mul_eq_mul_left hk (by
    rw [← Nat.mul_assoc, ← hsize, H.card_mul_index, hcard])
  apply mem_of_pow_coprime_index H (hkc.of_dvd_right (hid ▸ dvd_mul_left _ _))
  exact hx ▸ H.pow_mem (H.pow_mem (Subgroup.mem_zpowers r) k) e

end GF2Sparse
