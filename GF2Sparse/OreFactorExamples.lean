import GF2Sparse.OreFactors
import GF2Sparse.OreIndexSeven

/-! Lift the two index-seven examples once more to get an exact factorization
pattern for two pentanomials of degree 2^63-1. -/

namespace GF2Sparse

open Polynomial

theorem oreLift_twice_index_seven (b : ℕ) (hb : b = 2 ∨ b = 4) :
    let P := decode (fiveTermMask 6 5 b 1)
    let g := oreLift (oreLift P)
    g.natDegree = 2^63-1 ∧ g.support.card = 5 ∧ Squarefree g ∧
      (UniqueFactorizationMonoid.normalizedFactors g).card = 7 ∧
      ∀ u : BinaryPoly, Irreducible u → u ∣ g → u.natDegree = (2^63-1)/7 := by
  let P := decode (fiveTermMask 6 5 b 1)
  obtain ⟨hp, hi, ho⟩ := oreLift_degree_six_index_seven b hb
  have hs : P.natDegree = 6 := by rw [show P = _ from rfl, natDegree_decode]; rcases hb with rfl | rfl <;> decide
  have hw : P.support.card = 5 := by
    rw [show P = _ from rfl, support_decode]; rcases hb with rfl | rfl <;> decide
  have hd : (oreLift P).natDegree = 63 := (oreLift_degree hp.2.1.ne_zero).trans (by rw [hs]; decide)
  have hc : (oreLift P).coeff 0 = 1 := (oreLift_constant P).trans hp.coeff_zero_eq_one
  refine ⟨(oreLift_degree hi.ne_zero).trans (by rw [hd]), (oreLift_weight _).trans ((oreLift_weight _).trans hw),
    (separable_oreLift hc).squarefree, ?_, fun u hu h => (oreLift_factor_degree_of_irreducible hi hc hu h).trans ho⟩
  have hn := oreLift_factor_count hi hc
  change (UniqueFactorizationMonoid.normalizedFactors (oreLift (oreLift P))).card * _ = 2^(oreLift P).natDegree-1 at hn
  change (UniqueFactorizationMonoid.normalizedFactors (oreLift (oreLift P))).card = 7
  rw [ho, hd] at hn
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < (2^63-1)/7)
    (hn.trans (by decide : 2^63-1 = 7*((2^63-1)/7)))

end GF2Sparse
