import GF2Sparse.OreLift

/-! The two degree-six pentanomial seeds whose irreducible lifts have index seven. -/

namespace GF2Sparse

open Polynomial

private abbrev e := (2^63-1)/7

private def factors : List ProvenPrime :=
  [⟨7, by norm_num1⟩, ⟨73, by norm_num1⟩, ⟨127, by norm_num1⟩, ⟨337, by norm_num1⟩,
   ⟨92737, by norm_num1⟩, ⟨649657, by norm_num1⟩]

private def indexChecks (f : ℕ) : Bool :=
  powerBlocks 63 f 64 e 1 [1] && factors.all fun p =>
    let k := e / p.val
    let r := xPow 63 f k
    powerBlocks 63 f 64 k r [1] && r != 1 && r < 2^63

private theorem order63 (f : ℕ) (hf : f ≠ 0) (hd : f.log2 = 63) (checks : indexChecks f = true) :
    orderOf (AdjoinRoot.root (decode f)) = e := by
  obtain ⟨hfull, hall⟩ := Bool.and_eq_true_iff.1 checks
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide : 0 < e) (root_pow_one_of_blocks _ _ _ _ _ hfull)
  intro p hp hdiv
  have hfac : (factors.map Subtype.val).prod = e := by decide
  have hpr : ∀ q ∈ factors.map Subtype.val, Prime q := by
    intro q hq
    obtain ⟨v, _, rfl⟩ := List.mem_map.1 hq
    exact v.property.prime
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 (mem_list_primes_of_dvd_prod hp.prime hpr (hfac.symm ▸ hdiv))
  have h := List.all_eq_true.1 hall v hv
  simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at h
  exact root_pow_ne_one_of_blocks 63 f 64 _ _ [1] h.1.1 hf h.1.2 (hd ▸ h.2) (hd ▸ by decide)

theorem oreLift_degree_six_index_seven (b : ℕ) (hb : b = 2 ∨ b = 4) :
    let P := decode (fiveTermMask 6 5 b 1)
    Primitive P ∧ Irreducible (oreLift P) ∧ orderOf (AdjoinRoot.root (oreLift P)) = (2^63-1)/7 := by
  have hp : Primitive (decode (fiveTermMask 6 5 b 1)) := by
    apply (check_sound (n := 6) (factors := [3,3,7]) ?_ ?_).2.2
    · intro p h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> decide
    · rcases hb with rfl | rfl <;> decide +kernel
  refine ⟨hp, hp.irreducible_oreLift, ?_⟩
  have he : oreLift (decode (fiveTermMask 6 5 b 1)) =
      decode (fiveTermMask 63 31 (2^b-1) 1) := by
    simp only [decode_fiveTermMask, oreLift_add, oreLift_X_pow, oreLift_one]
    rfl
  rw [he]
  apply order63
  all_goals rcases hb with rfl | rfl <;> decide +kernel

end GF2Sparse
