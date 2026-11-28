import GF2Sparse.SparseOrderBounds
import Mathlib.NumberTheory.Multiplicity

/-! Prime-index tests for sparse witnesses whose root-order primes come from a proper subfield. -/

namespace GF2Sparse

open Polynomial

private theorem root_pow_field_order {f : BinaryPoly} (hf : Irreducible f)
    (hc : f.coeff 0 = 1) : AdjoinRoot.root f ^ (2 ^ f.natDegree - 1) = 1 := by
  letI : Fact (Irreducible f) := ⟨hf⟩
  have hz : aeval (AdjoinRoot.root f) f = 0 :=
    (AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self
  have h₀ : AdjoinRoot.root f ≠ 0 := by
    intro h
    rw [h, ← coeff_zero_eq_aeval_zero', hc, map_one] at hz
    exact one_ne_zero hz
  apply mul_right_cancel₀ h₀
  rw [one_mul, ← pow_succ, Nat.sub_add_cancel (Nat.two_pow_pos _)]
  exact (degree_dvd_iff_frobenius hf hz _).1 dvd_rfl

/-- When a prime divides the base field order, one power decides whether
substitution by that prime preserves irreducibility. -/
theorem irreducible_prime_expand_iff_index_test {f : BinaryPoly} (hf : Irreducible f)
    (hc : f.coeff 0 = 1) {r : ℕ} (hr : r.Prime) (hd : r ∣ 2 ^ f.natDegree - 1) :
    Irreducible (expand (ZMod 2) r f) ↔
      AdjoinRoot.root f ^ ((2 ^ f.natDegree - 1) / r) ≠ 1 := by
  let F := expand (ZMod 2) r f
  let b := AdjoinRoot.root f ^ ((2 ^ f.natDegree - 1) / r)
  have hdeg : F.natDegree = f.natDegree * r := natDegree_expand _ _
  have hmon : F.Monic := (binary_monic hf.ne_zero).expand hr.pos
  have hb : b ^ r = 1 := by
    dsimp only [b]
    rw [← pow_mul, Nat.div_mul_cancel hd]
    exact root_pow_field_order hf hc
  change Irreducible F ↔ b ≠ 1
  constructor
  · intro h hb₁
    have he := factor_degree_of_expand hf hc h hd (dvd_refl F)
    change F.natDegree = f.natDegree * orderOf b at he
    rw [hdeg, hb₁, orderOf_one] at he
    exact hr.ne_one (Nat.eq_of_mul_eq_mul_left hf.natDegree_pos he)
  · intro hb₁
    have ho : orderOf b = r :=
      ((Nat.dvd_prime hr).1 (orderOf_dvd_of_pow_eq_one hb)).resolve_left
        (fun h => hb₁ (orderOf_eq_one_iff.1 h))
    obtain ⟨p, hp, hpf⟩ := WfDvdMonoid.exists_irreducible_factor
      (not_isUnit_of_natDegree_pos F (hdeg ▸ Nat.mul_pos hf.natDegree_pos hr.pos)) hmon.ne_zero
    have he := factor_degree_of_expand hf hc hp hd hpf
    change p.natDegree = f.natDegree * orderOf b at he
    have heq : F = p := eq_of_monic_of_dvd_of_natDegree_le (binary_monic hp.ne_zero) hmon hpf
      (by rw [hdeg, he, ho])
    rwa [heq]

/-- All order primes of an irreducible dilation by a divisor of the base
field order already divide that field order. -/
theorem prime_dvd_base_order_of_expand {f : BinaryPoly} (hf : Irreducible f)
    (hc : f.coeff 0 = 1) {r ℓ : ℕ} (hr : 0 < r) (hd : r ∣ 2 ^ f.natDegree - 1)
    (hi : Irreducible (expand (ZMod 2) r f)) (hℓ : ℓ.Prime)
    (h : ℓ ∣ orderOf (AdjoinRoot.root (expand (ZMod 2) r f))) :
    ℓ ∣ 2 ^ f.natDegree - 1 := by
  rw [root_order_irreducible_dilation hf hr hi] at h
  exact (hℓ.dvd_mul.mp h).elim (·.trans hd)
    (·.trans (orderOf_dvd_of_pow_eq_one (root_pow_field_order hf hc)))

/-- The part of a polynomial whose exponents are congruent to `r` modulo `q`. -/
noncomputable def exponentResiduePart (f : BinaryPoly) (q r : ℕ) : BinaryPoly :=
  ofFinsupp (f.toFinsupp.filter fun i => i % q = r)

@[simp] theorem coeff_exponentResiduePart (f : BinaryPoly) (q r i : ℕ) :
    (exponentResiduePart f q r).coeff i = if i % q = r then f.coeff i else 0 := by
  cases f
  rfl

/-- If the top exponent is a multiple of `q` and all other residue parts vanish
at the universal root, the entire polynomial is a substitution by `X^q`. -/
theorem expand_contract_of_residue_parts_vanish {f : BinaryPoly} {q : ℕ} (hq : 0 < q)
    (hf : 0 < f.natDegree) (hd : q ∣ f.natDegree)
    (hv : ∀ r, 0 < r → r < q → AdjoinRoot.mk f (exponentResiduePart f q r) = 0) :
    expand (ZMod 2) q (contract q f) = f := by
  ext j
  rw [coeff_expand hq, coeff_contract hq.ne']
  split_ifs with hj
  · rw [Nat.div_mul_cancel hj]
  · have hr : j % q ≠ 0 := fun h => hj (Nat.dvd_of_mod_eq_zero h)
    let g := exponentResiduePart f q (j % q)
    have hg : g.natDegree ≤ f.natDegree - 1 := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro i hi
      change (exponentResiduePart f q (j % q)).coeff i = 0
      rw [coeff_exponentResiduePart]
      by_cases heq : i = f.natDegree
      · rw [heq, Nat.mod_eq_zero_of_dvd hd, if_neg hr.symm]
      · simp [coeff_eq_zero_of_natDegree_lt (show f.natDegree < i by omega)]
    have hg₀ : g = 0 := by
      by_contra hn
      have hle := natDegree_le_of_dvd (AdjoinRoot.mk_eq_zero.mp
        (hv _ (Nat.pos_of_ne_zero hr) (Nat.mod_lt j hq))) hn
      change f.natDegree ≤ g.natDegree at hle
      omega
    simpa [g, coeff_exponentResiduePart] using
      (congrArg (fun h : BinaryPoly => h.coeff j) hg₀).symm

private theorem not_dvd_index_iff_factorization {q R N : ℕ} (hq : q.Prime)
    (hN : 0 < N) (hR : R ∣ N) (hd : q ∣ N) :
    (¬ R ∣ N / q) ↔ R.factorization q = N.factorization q := by
  have hRpos := Nat.pos_of_dvd_of_pos hR hN
  obtain ⟨k, hk⟩ := hR
  have hk₀ : k ≠ 0 := by rintro rfl; simp [hk] at hN
  rw [Nat.dvd_div_iff_mul_dvd hd, hk, Nat.mul_comm q R,
    Nat.mul_dvd_mul_iff_left hRpos, Nat.factorization_mul hRpos.ne' hk₀, Finsupp.add_apply]
  constructor
  · intro h
    simp [Nat.factorization_eq_zero_of_not_dvd h]
  · intro h
    have hz : k.factorization q = 0 := by omega
    exact ((Nat.factorization_eq_zero_iff k q).mp hz |>.resolve_left (not_not_intro hq)).resolve_right hk₀

/-- Extending a binary field by degree `m` adds the valuation of `m` at each
odd prime that divides the original field order. -/
theorem factorization_mersenne_extension {q n m : ℕ} (hq : q.Prime) (ho : Odd q)
    (hn : 0 < n) (hd : q ∣ 2 ^ n - 1) (hm : 0 < m) :
    (2 ^ (n * m) - 1).factorization q = (2^n - 1).factorization q + m.factorization q := by
  letI : Fact q.Prime := ⟨hq⟩
  have h₂ : ¬q ∣ 2 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
    · exact hq.ne_one h
    · exact (by decide : ¬ Odd (2 : ℕ)) (h ▸ ho)
  have hval := padicValNat.pow_sub_pow ho (Nat.one_lt_two_pow hn.ne') hd
    (fun h => h₂ (hq.dvd_of_dvd_pow h)) hm.ne'
  simpa [pow_mul, Nat.factorization_def _ hq] using hval

/-- An extension of degree `q^a` adds exactly `a` powers of the base prime `q`. -/
theorem factorization_mersenne_prime_extension {q n : ℕ} (hq : q.Prime) (ho : Odd q)
    (hn : 0 < n) (hd : q ∣ 2 ^ n - 1) (a : ℕ) :
    (2 ^ (n * q^a) - 1).factorization q = (2^n - 1).factorization q + a := by
  rw [factorization_mersenne_extension hq ho hn hd (pow_pos hq.pos a),
    hq.factorization_pow, Finsupp.single_eq_same]

/-- One base-field power test decides irreducibility at every positive
height in the tower of odd-prime monomial substitutions. -/
theorem irreducible_prime_power_expand_iff_index_test {f : BinaryPoly} (hf : Irreducible f)
    (hc : f.coeff 0 = 1) {q : ℕ} (hq : q.Prime) (ho : Odd q)
    (hd : q ∣ 2 ^ f.natDegree - 1) (a : ℕ) :
    Irreducible (expand (ZMod 2) (q^(a+1)) f) ↔
      AdjoinRoot.root f ^ ((2 ^ f.natDegree - 1) / q) ≠ 1 := by
  constructor
  · intro h
    rw [pow_succ, expand_mul] at h
    exact (irreducible_prime_expand_iff_index_test hf hc hq hd).mp
      (of_irreducible_expand (pow_ne_zero _ hq.ne_zero) h)
  · intro h
    have hN := Nat.sub_pos_of_lt (Nat.one_lt_two_pow hf.natDegree_pos.ne')
    have hR := orderOf_dvd_of_pow_eq_one (root_pow_field_order hf hc)
    have hRpos := Nat.pos_of_dvd_of_pos hR hN
    have hv := (not_dvd_index_iff_factorization hq hN hR hd).mp
      (fun hdiv => h (orderOf_dvd_iff_pow_eq_one.mp hdiv))
    suffices all : ∀ j : ℕ, Irreducible (expand (ZMod 2) (q^j) f) from all (a+1)
    intro j
    induction j with
    | zero => simpa using hf
    | succ j ih =>
      rw [pow_succ', expand_mul]
      let g := expand (ZMod 2) (q^j) f
      have hdeg : g.natDegree = f.natDegree * q^j := natDegree_expand _ _
      have hdg : q ∣ 2 ^ g.natDegree - 1 := by
        rw [hdeg]
        exact hd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.dvd_mul_right _ _))
      have hcg : g.coeff 0 = 1 := by simp [g, coeff_expand (pow_pos hq.pos j), hc]
      apply (irreducible_prime_expand_iff_index_test ih hcg hq hdg).mpr
      change ¬AdjoinRoot.root g ^ ((2 ^ g.natDegree - 1) / q) = 1
      rw [← orderOf_dvd_iff_pow_eq_one]
      apply (not_dvd_index_iff_factorization hq (Nat.sub_pos_of_lt
        (Nat.one_lt_two_pow ih.natDegree_pos.ne')) (orderOf_dvd_of_pow_eq_one
        (root_pow_field_order ih hcg)) hdg).mpr
      change (orderOf (AdjoinRoot.root g)).factorization q = (2^g.natDegree-1).factorization q
      rw [hdeg, factorization_mersenne_prime_extension hq ho hf.natDegree_pos hd,
        root_order_irreducible_dilation hf (pow_pos hq.pos j) ih,
        Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) hRpos.ne',
        Finsupp.add_apply, hq.factorization_pow, Finsupp.single_eq_same, hv, Nat.add_comm]

/-- An odd substitution whose primes divide the base field order is irreducible
exactly when the base root passes the index test at every prime of the multiplier. -/
theorem irreducible_expand_iff_base_index_tests {f : BinaryPoly} (hf : Irreducible f)
    (hc : f.coeff 0 = 1) {m : ℕ} (hm : 0 < m) (ho : Odd m)
    (hs : ∀ q : ℕ, q.Prime → q ∣ m → q ∣ 2 ^ f.natDegree - 1) :
    Irreducible (expand (ZMod 2) m f) ↔
      ∀ q : ℕ, q.Prime → q ∣ m → AdjoinRoot.root f ^ ((2 ^ f.natDegree - 1) / q) ≠ 1 := by
  constructor
  · intro hi q hq hqm
    apply (irreducible_prime_expand_iff_index_test hf hc hq (hs q hq hqm)).mp
    obtain ⟨k, rfl⟩ := hqm
    rw [Nat.mul_comm, expand_mul] at hi
    exact of_irreducible_expand (by rintro rfl; simp at hm) hi
  · intro tests
    induction m using induction_on_primes with
    | zero => omega
    | one => simpa using hf
    | prime_mul q m hq ih =>
      have hm' : 0 < m := Nat.pos_of_mul_pos_left hm
      have hdq := Nat.dvd_mul_right q m
      have hdm := Nat.dvd_mul_left m q
      have hd := hs q hq hdq
      have hg := ih hm' (Odd.of_dvd_nat ho hdm) (fun l hl h => hs l hl (h.trans hdm))
        (fun l hl h => tests l hl (h.trans hdm))
      let g := expand (ZMod 2) m f
      have hdeg : g.natDegree = f.natDegree * m := natDegree_expand _ _
      have hcg : g.coeff 0 = 1 := by simp [g, coeff_expand hm', hc]
      have hdg : q ∣ 2 ^ g.natDegree - 1 := by
        rw [hdeg]
        exact hd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.dvd_mul_right _ _))
      have hN := Nat.sub_pos_of_lt (Nat.one_lt_two_pow hf.natDegree_pos.ne')
      have hR := orderOf_dvd_of_pow_eq_one (root_pow_field_order hf hc)
      have hv := (not_dvd_index_iff_factorization hq hN hR hd).mp
        (fun hdiv => tests q hq hdq (orderOf_dvd_iff_pow_eq_one.mp hdiv))
      rw [expand_mul]
      apply (irreducible_prime_expand_iff_index_test hg hcg hq hdg).mpr
      change ¬AdjoinRoot.root g ^ ((2 ^ g.natDegree - 1) / q) = 1
      rw [← orderOf_dvd_iff_pow_eq_one]
      apply (not_dvd_index_iff_factorization hq (Nat.sub_pos_of_lt
        (Nat.one_lt_two_pow hg.natDegree_pos.ne')) (orderOf_dvd_of_pow_eq_one
        (root_pow_field_order hg hcg)) hdg).mpr
      change (orderOf (AdjoinRoot.root g)).factorization q = (2 ^ g.natDegree - 1).factorization q
      rw [hdeg, factorization_mersenne_extension hq (Odd.of_dvd_nat ho hdq)
        hf.natDegree_pos hd hm', root_order_irreducible_dilation hf hm' hg,
        Nat.factorization_mul hm'.ne' (Nat.pos_of_dvd_of_pos hR hN).ne',
        Finsupp.add_apply, hv, Nat.add_comm]

end GF2Sparse
