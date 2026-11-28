import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-! Finite subgroup covers for the remaining prime-index tests. -/

namespace GF2Sparse.SubgroupCover

variable {G I P J : Type*} [Group G]

/-- A cover by the listed subgroups labels each input by a failing test.
Each pair with a verified quotient outside every subgroup has different labels. -/
theorem coloring_of_cover (x : I → G) (H : P → Subgroup G) (edge : I → I → Prop)
    (separate : ∀ i j, edge i j → ∀ p, x i / x j ∉ H p)
    (covered : ∀ i, ∃ p, x i ∈ H p) :
    ∃ color : I → P, ∀ i j, edge i j → color i ≠ color j := by
  choose hit mem using covered
  refine ⟨hit, fun i j hij equal => ?_⟩
  exact separate i j hij (hit i) ((H _).div_mem (mem i) (equal.symm ▸ mem j))

/-- Pairwise quotients outside each tested subgroup force a surviving element. -/
theorem exists_outside_of_quotients [Fintype I] [Fintype P]
    (x : I → G) (H : P → Subgroup G) (size : Fintype.card P < Fintype.card I)
    (separate : ∀ i j, i ≠ j → ∀ p, x i / x j ∉ H p) :
    ∃ i, ∀ p, x i ∉ H p := by
  classical
  by_contra! covered
  obtain ⟨color, proper⟩ := coloring_of_cover x H (· ≠ ·) separate covered
  obtain ⟨i, j, hij, equal⟩ := Fintype.exists_ne_map_eq_of_card_lt color size
  exact proper i j hij equal

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

private theorem large_failure_class {inputs labels limit : ℕ} (hit : Fin inputs → Fin labels)
    (size : labels * limit < inputs) :
    ∃ p, limit + 1 ≤ (Finset.univ.filter (fun i => hit i = p)).card := by
  obtain ⟨p, _, hp⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (f := hit) (n := limit)
    (fun _ _ => Finset.mem_univ _) (by simpa using size)
  exact ⟨p, hp⟩

/-- A cover by fifteen tests must assign at least 21,305 surviving pairs to one test. -/
theorem degree1229_common_failure (hit : Fin 319572 → Fin 15) :
    ∃ p, 21305 ≤ (Finset.univ.filter (fun i => hit i = p)).card :=
  large_failure_class (limit := 21304) hit (by decide)

/-- The reduced cofactor budget raises the necessary class size to 22,827 pairs. -/
theorem degree1229_fourteen_prime_cover (hit : Fin 319572 → Fin 14) :
    ∃ p, 22827 ≤ (Finset.univ.filter (fun i => hit i = p)).card :=
  large_failure_class (limit := 22826) hit (by decide)

/-- An injective code for the supports failing each test bounds their union,
even when a support can fail several tests and the code lengths differ. -/
theorem outside_card_of_failure_codes {I P : Type*} [Fintype I] [Fintype P] [DecidableEq I]
    (bad : P → Finset I) (capacity : P → ℕ)
    (code : ∀ p, ↥(bad p) ↪ Fin (capacity p)) :
    Fintype.card I - ∑ p, capacity p ≤ (Finset.univ \ Finset.univ.biUnion bad).card := by
  have hcard (p : P) : (bad p).card ≤ capacity p := by
    simpa using Fintype.card_le_of_embedding (code p)
  have h : (Finset.univ.biUnion bad).card ≤ ∑ p, capacity p :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun p _ => hcard p)
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  omega

private theorem degree1229_uniform_failure_codes {I : Type*} [Fintype I] [DecidableEq I]
    {primes : ℕ} (size : Fintype.card I = 319572) (bad : Fin primes → Finset I)
    (code : ∀ p, ↥(bad p) ↪ Fin (2^14)) :
    319572 - primes * 2^14 ≤ (Finset.univ \ Finset.univ.biUnion bad).card := by
  simpa only [size, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    using outside_card_of_failure_codes bad (fun _ => 2^14) code

/-- The earlier fifteen-prime budget gives 73,812 primitive pairs under the rank hypothesis. -/
theorem degree1229_of_fourteen_bit_codes {I : Type*} [Fintype I] [DecidableEq I]
    (size : Fintype.card I = 319572) (bad : Fin 15 → Finset I)
    (code : ∀ p, ↥(bad p) ↪ Fin (2^14)) :
    73812 ≤ (Finset.univ \ Finset.univ.biUnion bad).card :=
  degree1229_uniform_failure_codes size bad code

/-- A fourteen-bit rank at each of fourteen primes would give 90,196 primitive pairs. -/
theorem degree1229_codes_at_fourteen_primes {I : Type*} [Fintype I] [DecidableEq I]
    (size : Fintype.card I = 319572) (bad : Fin 14 → Finset I)
    (code : ∀ p, ↥(bad p) ↪ Fin (2^14)) :
    90196 ≤ (Finset.univ \ Finset.univ.biUnion bad).card :=
  degree1229_uniform_failure_codes size bad code

/-- A failed parameter can be encoded by a test and a root of its polynomial.
The test fields may differ. Each parameter map must be injective on the given set. -/
theorem card_polynomial_failures {I P : Type*} [Fintype P] {d : ℕ}
    (s : Finset I) (F : P → Type*) [∀ p, Field (F p)]
    (param : ∀ p, I → F p) (poly : ∀ p, Polynomial (F p))
    (inj : ∀ p, Set.InjOn (param p) (s : Set I))
    (nonzero : ∀ p, poly p ≠ 0) (deg : ∀ p, (poly p).natDegree ≤ d)
    (fails : ∀ i ∈ s, ∃ p, (poly p).eval (param p i) = 0) :
    s.card ≤ Fintype.card P * d := by
  classical
  let fiber (p : P) := s.filter fun i => (poly p).eval (param p i) = 0
  have hsub : s ⊆ Finset.univ.biUnion fiber := by
    intro i hi
    obtain ⟨p, hp⟩ := fails i hi
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hi, hp⟩⟩
  have hcard (p : P) : (fiber p).card ≤ d := by
    by_contra! lt
    apply nonzero p
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (poly p)
      (f := fun i : fiber p => param p i.val)
    · intro i j equal
      exact Subtype.ext (inj p (Finset.mem_filter.mp i.prop).1 (Finset.mem_filter.mp j.prop).1 equal)
    · exact fun i => (Finset.mem_filter.mp i.prop).2
    · simpa using lt_of_le_of_lt (deg p) lt
  calc
    s.card ≤ (Finset.univ.biUnion fiber).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ Finset.univ, (fiber p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p : P, d := Finset.sum_le_sum fun p _ => hcard p
    _ = Fintype.card P * d := by simp


/-- The tangent to twice the pair count at consecutive integer class sizes. -/
private theorem pair_count_tangent (x q : ℤ) :
    2*q*x-q*(q+1) ≤ x*(x-1) := by
  rcases le_or_gt x q with h | h
  · nlinarith [mul_nonneg (show 0 ≤ q-x by omega) (show 0 ≤ q+1-x by omega)]
  · nlinarith [mul_nonneg (show 0 ≤ x-q by omega) (show 0 ≤ x-q-1 by omega)]

private theorem fourteen_pair_tangents (size : Fin 14 → ℤ) (q : ℤ) :
    2*q*(∑ i, size i)-q*(14*(q+1)) ≤ ∑ i, size i*(size i-1) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 14)))
    (fun i _ => pair_count_tangent (size i) q)
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using h

/-- A cover of all survivors forces the stated number of same-label pairs,
even after allowing every shared-tap pair counted by the census. -/
theorem degree1229_joint_cover (size : Fin 14 → ℤ) (total : ∑ i, size i = 319572) :
    2*(2877863093+769343665) ≤ ∑ i, size i*(size i-1) := by
  have h := fourteen_pair_tangents size 22826
  rw [total] at h
  norm_num at h ⊢
  exact h

/-- A 31-bit code for disjoint common failures leaves at least 33,784 primitive pairs. -/
theorem degree1229_joint_code (size : Fin 14 → ℤ)
    (code : ∑ i, size i*(size i-1) ≤ 2*(2^31+769343665)) :
    33784 ≤ 319572-∑ i, size i := by
  have h := fourteen_pair_tangents size 20413
  norm_num at h code
  omega

/-- A disjoint family uses at most 614 folded labels and 307 of the two active residues. -/
theorem degree1229_tap_packing_bound {mixed doubleActive triples : ℕ}
    (cover : mixed ≤ 39) (allTaps : 2*(mixed+doubleActive)+3*triples ≤ 614)
    (active : mixed+2*doubleActive+triples ≤ 307) :
    mixed+doubleActive+triples ≤ 240 := by omega

/-- If every member of the explicit disjoint packing fails, eighteen share a failing test. -/
theorem degree1229_packing_cover (hit : Fin 240 → Fin 14) :
    ∃ p, 18 ≤ (Finset.univ.filter (fun i => hit i = p)).card :=
  large_failure_class (limit := 17) hit (by decide)

/-- A four-bit conditional code on the disjoint packing leaves sixteen primitive members. -/
theorem degree1229_four_bit_packing (bad : Fin 14 → Finset (Fin 240))
    (code : ∀ p, ↥(bad p) ↪ Fin 16) :
    16 ≤ (Finset.univ \ Finset.univ.biUnion bad).card := by
  simpa using outside_card_of_failure_codes bad (fun _ => 16) code

end GF2Sparse.SubgroupCover
