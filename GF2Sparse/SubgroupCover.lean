import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-! Finite subgroup covers for the remaining prime-index tests. -/

namespace GF2Sparse.SubgroupCover

variable {G I P J : Type*} [Group G]

/-- Pairwise quotients outside each tested subgroup force a surviving element. -/
theorem exists_outside_of_quotients [Fintype I] [Fintype P]
    (x : I → G) (H : P → Subgroup G) (size : Fintype.card P < Fintype.card I)
    (separate : ∀ i j, i ≠ j → ∀ p, x i / x j ∉ H p) :
    ∃ i, ∀ p, x i ∉ H p := by
  classical
  by_contra! covered
  choose hit mem using covered
  obtain ⟨i, j, hij, equal⟩ := Fintype.exists_ne_map_eq_of_card_lt hit size
  apply separate i j hij (hit i)
  exact (H _).div_mem (mem i) (equal.symm ▸ mem j)

/-- A common multiplier takes every input outside every subgroup. Distinct
multipliers must have distinct cosets modulo each subgroup in the list. -/
theorem exists_common_multiplier [Fintype I] [Fintype P] [Fintype J]
    (x : I → G) (u : J → G) (H : P → Subgroup G)
    (size : Fintype.card I * Fintype.card P < Fintype.card J)
    (separate : ∀ j k, j ≠ k → ∀ p, u j / u k ∉ H p) :
    ∃ j, ∀ i p, u j * x i ∉ H p := by
  classical
  by_contra! covered
  choose input hit mem using covered
  have hc : Fintype.card (I × P) < Fintype.card J := by simpa using size
  obtain ⟨j, k, hjk, equal⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun q => (input q, hit q)) hc
  have hk : u k * x (input j) ∈ H (hit j) := by
    rw [show input j = input k from congrArg Prod.fst equal,
      show hit j = hit k from congrArg Prod.snd equal]
    exact mem k
  apply separate j k hjk (hit j)
  simpa [div_eq_mul_inv, mul_assoc] using (H _).div_mem (mem j) hk

/-- If every surviving reciprocal pair fails a test, one of fifteen tests
must fail for at least 21,305 pairs. Labels for unused primes may be empty. -/
theorem degree1229_common_failure (hit : Fin 319572 → Fin 15) :
    ∃ p, 21305 ≤ (Finset.univ.filter (fun i => hit i = p)).card := by
  obtain ⟨p, _, hp⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (f := hit) (n := 21304)
    (fun _ _ => Finset.mem_univ _) (by simp)
  exact ⟨p, hp⟩

end GF2Sparse.SubgroupCover
