import GF2Sparse.Basic
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.LinearCombination

/-! Two effects of reducing candidate polynomials modulo small irreducibles. -/

namespace GF2Sparse

open Polynomial

/-- Every nonzero element of every binary field of degree at most B has order
dividing this number. -/
def period (B : ℕ) : ℕ := (Finset.Icc 1 B).lcm (fun d => 2 ^ d - 1)

theorem period_pos (B : ℕ) : 0 < period B := by
  apply Nat.pos_of_ne_zero
  apply Finset.lcm_ne_zero_iff.2
  intro d hd
  have := Nat.one_lt_two_pow (show d ≠ 0 by have := (Finset.mem_Icc.mp hd).1; omega)
  omega

theorem period_odd (B : ℕ) : Odd (period B) := by
  apply Odd.of_dvd_nat _ ((Finset.Icc 1 B).lcm_dvd_prod (fun d => 2 ^ d - 1))
  apply Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one
  intro d hd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (show d ≠ 0 by have := (Finset.mem_Icc.mp hd).1; omega)
  rw [pow_succ]
  exact ⟨2 ^ k - 1, by have := Nat.two_pow_pos k; omega⟩

theorem root_pow_period {p : BinaryPoly} (hp : Irreducible p) {B : ℕ}
    (hB : p.natDegree ≤ B) (hx : AdjoinRoot.root p ≠ 0) :
    AdjoinRoot.root p ^ period B = 1 := by
  letI : Fact (Irreducible p) := ⟨hp⟩
  let e := (AdjoinRoot.powerBasisAux hp.ne_zero).equivFun.toEquiv
  letI : Fintype (AdjoinRoot p) := Fintype.ofEquiv _ e.symm
  have hpow := FiniteField.pow_card_sub_one_eq_one _ hx
  rw [card_adjoinRoot hp.ne_zero] at hpow
  have hd : 2 ^ p.natDegree - 1 ∣ period B :=
    Finset.dvd_lcm (Finset.mem_Icc.2 ⟨hp.natDegree_pos, hB⟩)
  obtain ⟨k, hk⟩ := hd
  rw [hk, pow_mul, hpow, one_pow]

theorem root_ne_zero_of_factor {p g : BinaryPoly} (hp : Irreducible p)
    (hpg : p ∣ g) (hconst : g.coeff 0 = 1) : AdjoinRoot.root p ≠ 0 := by
  letI : Fact (Irreducible p) := ⟨hp⟩
  intro heq
  have hg := AdjoinRoot.mk_eq_zero.2 hpg
  rw [← AdjoinRoot.aeval_eq, heq, ← coeff_zero_eq_aeval_zero', hconst, map_one] at hg
  exact one_ne_zero hg

/-- Compressing each exponent modulo the common period preserves any
nonzero root of degree at most B. Collisions in either sum are allowed. -/
theorem factor_of_congruent_exponents {ι : Type*} (s : Finset ι) (a b : ι → ℕ)
    {B : ℕ} (hmod : ∀ i ∈ s, a i ≡ b i [MOD period B])
    (g : BinaryPoly) (hg : g = ∑ i ∈ s, X ^ b i) (hpos : 0 < g.natDegree)
    (hB : g.natDegree ≤ B) (hconst : g.coeff 0 = 1) :
    ∃ p : BinaryPoly, Irreducible p ∧ p.natDegree ≤ B ∧ p ∣ ∑ i ∈ s, X ^ a i := by
  have hg0 : g ≠ 0 := by intro h; simp [h] at hpos
  obtain ⟨p, hp, hpg⟩ := WfDvdMonoid.exists_irreducible_factor
    (not_isUnit_of_natDegree_pos g hpos) hg0
  have hdeg := (natDegree_le_of_dvd hpg hg0).trans hB
  refine ⟨p, hp, hdeg, AdjoinRoot.mk_eq_zero.1 ?_⟩
  have hpow := root_pow_period hp hdeg (root_ne_zero_of_factor hp hpg hconst)
  have hres (i) (hi : i ∈ s) : AdjoinRoot.root p ^ a i = AdjoinRoot.root p ^ b i := by
    have hm := Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hpow) (hmod i hi)
    calc
      _ = _ := (pow_mod_orderOf (AdjoinRoot.root p) (a i)).symm
      _ = _ := congrArg (fun e => AdjoinRoot.root p ^ e) hm
      _ = _ := pow_mod_orderOf _ _
  have hz := AdjoinRoot.mk_eq_zero.2 hpg
  rw [hg, map_sum] at hz
  simpa only [map_sum, map_pow, AdjoinRoot.mk_X,
    Finset.sum_congr rfl hres] using hz

/-- Along an arithmetic progression every affine formula for the exponents
repeats the residues of its base polynomial. The same progression works
for all formulas whose base degree is bounded by B. -/
theorem factor_on_progression {ι : Type*} (s : Finset ι) (slope offset : ι → ℕ)
    {B : ℕ} (g : BinaryPoly) (hg : g = ∑ i ∈ s, X ^ offset i)
    (hpos : 0 < g.natDegree) (hB : g.natDegree ≤ B) (hconst : g.coeff 0 = 1) (k : ℕ) :
    ∃ p : BinaryPoly, Irreducible p ∧ p.natDegree ≤ B ∧
      p ∣ ∑ i ∈ s, X ^ (period B * k * slope i + offset i) := by
  apply factor_of_congruent_exponents s _ offset _ g hg hpos hB hconst
  intro i _
  rw [mul_assoc]
  exact Nat.ModEq.modulus_mul_add

/-- If n is a multiple of the period, an entire translated block of terms
retains a small factor when placed between the endpoints 1 and X^n. -/
theorem factor_of_short_block {B n : ℕ} (hn : period B ∣ n) (a : ℕ) {g : BinaryPoly}
    (hpos : 0 < g.natDegree) (hB : g.natDegree ≤ B) (hconst : g.coeff 0 = 1) :
    ∃ p : BinaryPoly, Irreducible p ∧ p.natDegree ≤ B ∧ p ∣ X ^ n + 1 + X ^ a * g := by
  have hg : g ≠ 0 := by intro h; simp [h] at hpos
  obtain ⟨p, hp, hpg⟩ := WfDvdMonoid.exists_irreducible_factor
    (not_isUnit_of_natDegree_pos g hpos) hg
  have hdeg := (natDegree_le_of_dvd hpg hg).trans hB
  refine ⟨p, hp, hdeg, AdjoinRoot.mk_eq_zero.1 ?_⟩
  letI : Fact (Irreducible p) := ⟨hp⟩
  have hpow := root_pow_period hp hdeg (root_ne_zero_of_factor hp hpg hconst)
  obtain ⟨k, rfl⟩ := hn
  simp only [map_add, map_pow, map_one, map_mul, AdjoinRoot.mk_X,
    AdjoinRoot.mk_eq_zero.2 hpg, mul_zero, add_zero, pow_mul, hpow, one_pow]
  simpa using congrArg (AdjoinRoot.of p) (show (1 : ZMod 2) + 1 = 0 by decide)

/-- For a pentanomial, the relevant width is the difference between the
largest and smallest interior exponents. The shift a is unrestricted. -/
theorem pentanomial_not_irreducible {B n a u v : ℕ} (hperiod : period B ∣ n)
    (hu : 0 < u) (huv : u < v) (hv : v ≤ B) (hB : B < n) (htop : a + v < n) :
    ¬ Irreducible ((X : BinaryPoly) ^ n + 1 + X ^ a * (X ^ v + (X ^ u + 1))) := by
  let g : BinaryPoly := X ^ v + (X ^ u + 1)
  have hdeg : g.natDegree = v := by
    dsimp [g]
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow, natDegree_X_pow]
    · exact huv
    · simpa using hu
  have hc : g.coeff 0 = 1 := by
    simp [g, coeff_X_pow, hu.ne, (hu.trans huv).ne]
  obtain ⟨p, hp, hpb, hpf⟩ := factor_of_short_block hperiod a
    (hdeg ▸ hu.trans huv) (hdeg ▸ hv) hc
  intro hirr
  have hle := natDegree_le_of_dvd (hp.dvd_symm hirr hpf) hp.ne_zero
  have htopdeg : ((X : BinaryPoly) ^ n + 1 + X ^ a * g).natDegree = n := by
    have hn : 0 < n := by omega
    have hlead : ((X : BinaryPoly) ^ n + 1).natDegree = n := by
      rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
      simpa using hn
    rw [natDegree_add_eq_left_of_natDegree_lt, hlead]
    exact (natDegree_mul_le.trans (by simp [hdeg])).trans_lt (hlead ▸ htop)
  change (X ^ n + 1 + X ^ a * g).natDegree ≤ p.natDegree at hle
  omega

/-- A two-parameter family of pentanomials. -/
noncomputable def productCandidate (n u v : ℕ) : BinaryPoly :=
  X ^ n + (X ^ u + 1) * (X ^ v + 1)

private theorem product_coeff_zero {n u v : ℕ} (hn : 0 < n) (hu : 0 < u) (hv : 0 < v) :
    (productCandidate n u v).coeff 0 = 1 := by
  simp [productCandidate, coeff_X_pow, hu.ne, hv.ne, hn.ne]

/-- An entire family avoids all irreducible factors up to the chosen degree. -/
theorem product_no_small_factor {B n u v : ℕ} (hn : 0 < n) (hu : 0 < u) (hv : 0 < v)
    (hperiod : period B ∣ u) {p : BinaryPoly} (hp : Irreducible p) (hdeg : p.natDegree ≤ B) :
    ¬ p ∣ productCandidate n u v := by
  letI : Fact (Irreducible p) := ⟨hp⟩
  intro h
  have hx := root_ne_zero_of_factor hp h (product_coeff_zero hn hu hv)
  have hpow := root_pow_period hp hdeg hx
  obtain ⟨k, rfl⟩ := hperiod
  have htwo : (1 : AdjoinRoot p) + 1 = 0 := by
    simpa using congrArg (AdjoinRoot.of p) (show (1 : ZMod 2) + 1 = 0 by decide)
  have he := AdjoinRoot.mk_eq_zero.2 h
  simp [productCandidate, pow_mul, hpow, htwo, hx] at he

/-- Opposite parities for the two exponents make every candidate separable. -/
theorem product_separable {n u v : ℕ} (hn : 0 < n) (hu : Odd u) (hv : Even v) (hv0 : 0 < v) :
    (productCandidate n u v).Separable := by
  have hu0 : 0 < u := by obtain ⟨k, hk⟩ := hu; omega
  have hc := product_coeff_zero hn hu0 hv0
  refine isCoprime_of_irreducible_dvd (fun h => by simp [h.1] at hc) ?_
  intro p hp hpf hpd
  letI : Fact (Irreducible p) := ⟨hp⟩
  let r := AdjoinRoot.root p
  have hx : r ≠ 0 := root_ne_zero_of_factor hp hpf hc
  have hval : r ^ n + (r ^ u + 1) * (r ^ v + 1) = 0 := by
    simpa [productCandidate, r] using AdjoinRoot.mk_eq_zero.2 hpf
  have hvx : r ^ v + 1 ≠ 0 := by
    intro hz
    simp [hz, hx] at hval
  have hd := AdjoinRoot.mk_eq_zero.2 hpd
  rcases Nat.even_or_odd n with he | ho
  · dsimp [r] at hx hvx
    simp [productCandidate, derivative_mul, derivative_X_pow, he.natCast_zmod_two,
      hu.natCast_zmod_two, hv.natCast_zmod_two, hx, hvx] at hd
  · have heq : r ^ (n - 1) + r ^ (u - 1) * (r ^ v + 1) = 0 := by
      simpa [productCandidate, derivative_mul, derivative_X_pow, ho.natCast_zmod_two,
        hu.natCast_zmod_two, hv.natCast_zmod_two, r] using hd
    have heuler := congrArg (r * ·) heq
    simp only [mul_add, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn,
      Nat.sub_add_cancel hu0, mul_zero] at heuler
    apply hvx
    linear_combination hval - heuler

theorem product_support {n u v : ℕ} (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v)
    (htop : u + v < n) :
    (productCandidate n u v).support = {n, u + v, u, v, 0} := by
  let s : Finset ℕ := {n, u + v, u, v, 0}
  have hform : productCandidate n u v = ∑ i ∈ s, X ^ i := by
    simp [s, Finset.sum_insert, huv, hu.ne', hv.ne', show n ≠ 0 by omega,
      htop.ne', show n ≠ u by omega, show n ≠ v by omega, pow_add, productCandidate]
    ring
  rw [hform]
  ext i
  change i ∈ (∑ j ∈ s, (X : BinaryPoly) ^ j).support ↔ i ∈ s
  simp [mem_support_iff, coeff_X_pow]

theorem product_shape {n u v : ℕ} (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v) (htop : u + v < n) :
    (productCandidate n u v).natDegree = n ∧ (productCandidate n u v).support.card = 5 := by
  have hs := product_support hu hv huv htop
  constructor
  · apply le_antisymm
    · apply natDegree_le_iff_coeff_eq_zero.2
      intro i hi
      apply notMem_support_iff.mp
      rw [hs]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · apply le_natDegree_of_ne_zero
      rw [← mem_support_iff, hs]
      simp
  · rw [hs]
    simp [Finset.card_insert_of_notMem, huv, hu.ne', hv.ne', htop.ne',
      show n ≠ u by omega, show n ≠ v by omega, show n ≠ 0 by omega]

/-- For every fixed factor-degree cutoff B, every sufficiently large degree
has an explicit squarefree five-term candidate surviving that cutoff. -/
theorem exists_locally_irreducible (B n : ℕ) (htop : period B + 2 < n) :
    ∃ f : BinaryPoly, f.natDegree = n ∧ f.support.card = 5 ∧ Squarefree f ∧
      ∀ p : BinaryPoly, Irreducible p → p ∣ f → B < p.natDegree := by
  have hu := period_pos B
  have huodd := period_odd B
  have hne : period B ≠ 2 := by rintro he; have := he ▸ huodd; contradiction
  have hs := product_shape hu (by decide : 0 < 2) hne htop
  have hn : 0 < n := by omega
  refine ⟨productCandidate n (period B) 2, hs.1, hs.2,
    (product_separable hn huodd (by decide) (by decide)).squarefree, ?_⟩
  intro p hp hpf
  exact lt_of_not_ge fun hle => product_no_small_factor hn hu (by decide) dvd_rfl hp hle hpf

end GF2Sparse
