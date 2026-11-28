import GF2Sparse.CompositionNorm
import GF2Sparse.Table
import GF2Sparse.Progressions
import GF2Sparse.ShiftWeight

/-! Relative norms of primitive compositions and translates of dyadic pentanomials. -/

namespace GF2Sparse

open Polynomial

/-- A primitive composition with zero inner constant term has a primitive outer
root. The outer root is the relative norm of the primitive root. -/
theorem primitive_outer_of_primitive_composition {H h : BinaryPoly}
    (hH : Irreducible H) (hm : 0 < h.natDegree) (hc : h.coeff 0 = 0)
    (hf : Primitive (H.comp h)) : Primitive H := by
  let f := H.comp h
  letI : Fact (Irreducible f) := ⟨hf.2.1⟩
  let x := AdjoinRoot.root f
  let q := 2 ^ H.natDegree
  let D := normExponent q h.natDegree
  have hq : 1 < q := Nat.one_lt_two_pow hH.natDegree_pos.ne'
  have hN : 0 < q ^ h.natDegree - 1 := Nat.sub_pos_of_lt (one_lt_pow₀ hq hm.ne')
  have hsize : D * (q - 1) = q ^ h.natDegree - 1 := normExponent_mul hq.le _
  have hD : 0 < D := Nat.pos_of_ne_zero (fun hz => by simp [hz] at hsize; omega)
  have ho : orderOf x = D * (q - 1) := by
    rw [hsize]
    simpa only [x, f, q, natDegree_comp, pow_mul] using hf.2.2
  have hnorm := AdjoinRoot.mk_eq_zero.2 (norm_congruence_of_irreducible_comp hH hm hc hf.2.1)
  have he : x ^ D = aeval x h := by
    simpa only [x, f, D, q, map_sub, map_pow, AdjoinRoot.mk_X, sub_eq_zero, AdjoinRoot.aeval_eq]
      using hnorm
  have hy : aeval (aeval x h) H = 0 := by
    rw [← aeval_comp, AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_self
  refine ⟨binary_monic hH.ne_zero, hH, (orderOf_root_at hH hy).symm.trans ?_⟩
  rw [← he, orderOf_pow_of_dvd hD.ne' (ho ▸ dvd_mul_right D (q-1)), ho,
    Nat.mul_div_cancel_left _ hD]

namespace CubicComponents

/-- The five-term shape whose translate can be a proper monomial dilation. -/
noncomputable def dyadicPath (j k : ℕ) : BinaryPoly :=
  1 + (X + X ^ (2^k)) * (1 + X ^ (2^j))

theorem shift_dyadicPath (j k : ℕ) :
    ShiftWeight.shift (dyadicPath j k) = trinomial (2^j + 2^k) (2^j + 1) := by
  have cancel_pair (a b : BinaryPoly) : (a + 1) + (b + 1) = a + b := by
    rw [add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]
  have cancel_one (a : BinaryPoly) : 1 + (a + 1) = a := by
    rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
  simp only [ShiftWeight.shift, dyadicPath, add_comp, mul_comp, pow_comp, X_comp,
    one_comp, add_pow_expChar_pow, one_pow, cancel_pair, cancel_one, trinomial, pow_add, pow_one]
  ring

/-- For any common divisor, the translated polynomial is the dilation
of the trinomial of the correspondingly smaller degree. -/
theorem shift_dyadicPath_eq_expand {j k d : ℕ} (ht : d ∣ 2^j + 1) (hn : d ∣ 2^j + 2^k) :
    ShiftWeight.shift (dyadicPath j k) =
      expand (ZMod 2) d (trinomial ((2^j + 2^k) / d) ((2^j + 1) / d)) := by
  rw [shift_dyadicPath]
  simp only [trinomial, map_add, map_pow, expand_X, map_one, ← pow_mul, Nat.mul_div_cancel' hn,
    Nat.mul_div_cancel' ht]

/-- Degree, binary coefficient mask, and full factorization of the group order
for the four cubic cases and the three primitive translated dilations through 4097. -/
def primitiveCases : List (ℕ × ℕ × List ℕ) :=
  [(3, 0xb, [7]), (3, 0xd, [7]), (9, 0x2a3, [7, 73]),
   (12, 0x12c1, [3, 3, 5, 7, 13]), (6, 0x5b, [3, 3, 7]),
   (20, 0x110023, [3, 5, 5, 11, 31, 41]),
   (66, 0x5000000000000000b, [3, 3, 7, 23, 67, 89, 683, 20857, 599479])]

private def factorsUsed : List ℕ := [3, 5, 7, 11, 13, 23, 31, 41, 67, 73, 89, 683, 20857, 599479]

private theorem prime_of_mem_factorsUsed {p : ℕ} (hp : p ∈ factorsUsed) : Nat.Prime p := by
  simp only [factorsUsed, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> norm_num1

set_option maxRecDepth 8192 in
private theorem checked_cases : ∀ row ∈ primitiveCases,
    check row.1 row.2.1 row.2.2 = true ∧ ∀ p ∈ row.2.2, p ∈ factorsUsed := by
  decide +kernel

theorem primitive_of_mem_cases {n f : ℕ} {factors : List ℕ}
    (hr : (n, f, factors) ∈ primitiveCases) :
    (decode f).natDegree = n ∧ (decode f).support.card ≤ 5 ∧ Primitive (decode f) :=
  check_sound (fun p hp => prime_of_mem_factorsUsed ((checked_cases _ hr).2 p hp))
    (checked_cases _ hr).1

end CubicComponents
end GF2Sparse
