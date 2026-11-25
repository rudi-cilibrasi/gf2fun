import GF2Sparse.LocalFactors

/-! A positive fraction of the degree-n pentanomials with constant term one
can simultaneously pass any fixed small-factor sieve and be squarefree. -/

namespace GF2Sparse

open Polynomial

private noncomputable def pent (n a b c : ℕ) : BinaryPoly :=
  X ^ n + (X ^ c + (X ^ b + (X ^ a + 1)))

private theorem nextDegree {g : BinaryPoly} {e : ℕ} (he : g.natDegree < e) :
    ((X : BinaryPoly) ^ e + g).natDegree = e := by
  rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
  simpa only [natDegree_X_pow] using he

private theorem pent_degrees {a b c : ℕ} (ha : 0 < a) (hb : a < b) (hc : b < c) :
    ((X : BinaryPoly) ^ a + 1).natDegree = a ∧
    ((X : BinaryPoly) ^ b + (X ^ a + 1)).natDegree = b ∧
    ((X : BinaryPoly) ^ c + (X ^ b + (X ^ a + 1))).natDegree = c := by
  have h1 := nextDegree (g := 1) (by simpa only [natDegree_one] using ha)
  have h2 := nextDegree (h1.trans_lt hb)
  exact ⟨h1, h2, nextDegree (h2.trans_lt hc)⟩

private theorem pent_injective {n a b c a' b' c' : ℕ}
    (ha : 0 < a) (hb : a < b) (hc : b < c) (ha' : 0 < a') (hb' : a' < b') (hc' : b' < c')
    (he : pent n a b c = pent n a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  obtain ⟨h1, h2, h3⟩ := pent_degrees ha hb hc
  obtain ⟨h1', h2', h3'⟩ := pent_degrees ha' hb' hc'
  unfold pent at he
  have e3 := add_left_cancel he
  have ec := h3.symm.trans ((congrArg natDegree e3).trans h3')
  subst c'
  have e2 := add_left_cancel e3
  have eb := h2.symm.trans ((congrArg natDegree e2).trans h2')
  subst b'
  exact ⟨h1.symm.trans ((congrArg natDegree (add_left_cancel e2)).trans h1'), rfl, rfl⟩

private theorem pent_sifted {B n a b c : ℕ} (ha : 0 < a) (hb : a < b) (hc : b < c)
    (hn : c < n) (hperiod : period B ∣ a) (hgap : ∃ k, c = b + period B * k)
    (hpar : (Even n ∧ Odd a) ∨ (Odd n ∧ Even a)) (hbe : Even b) (hce : Even c) :
    (pent n a b c).natDegree = n ∧ (pent n a b c).support.card = 5 ∧
    Squarefree (pent n a b c) ∧
    ∀ p : BinaryPoly, Irreducible p → p ∣ pent n a b c → B < p.natDegree := by
  let f := pent n a b c
  have hb0 := ha.trans hb
  have hc0 := hb0.trans hc
  have hn0 := hc0.trans hn
  have hconst : f.coeff 0 = 1 := by simp [f, pent, coeff_X_pow, ha.ne, hb0.ne, hc0.ne, hn0.ne]
  refine ⟨nextDegree ((pent_degrees ha hb hc).2.2.trans_lt hn), ?_, ?_, ?_⟩
  · let s : Finset ℕ := {n, c, b, a, 0}
    have hform : pent n a b c = ∑ i ∈ s, X ^ i := by
      simp [pent, s, Finset.sum_insert, hn.ne', hc.ne', hb.ne', hn0.ne', hc0.ne', hb0.ne',
        ha.ne', (hc.trans hn).ne', (hb.trans hc).ne', (hb.trans (hc.trans hn)).ne']
    have hs : (pent n a b c).support = s := by
      rw [hform]
      ext i
      simp [mem_support_iff, coeff_X_pow]
    rw [hs]
    simp [s, Finset.card_insert_of_notMem, hn.ne', hc.ne', hb.ne', hn0.ne', hc0.ne', hb0.ne',
      ha.ne', (hc.trans hn).ne', (hb.trans hc).ne', (hb.trans (hc.trans hn)).ne']
  · apply Polynomial.Separable.squarefree
    apply isCoprime_of_irreducible_dvd (fun h => by have hf : f = 0 := h.1; simp [hf] at hconst)
    intro p hp hpf hpd
    letI : Fact (Irreducible p) := ⟨hp⟩
    have hroot := root_ne_zero_of_factor hp hpf hconst
    have he := AdjoinRoot.mk_eq_zero.2 hpd
    rcases hpar with ⟨hen, hoa⟩ | ⟨hon, hea⟩
    · simp [pent, derivative_X_pow, hen.natCast_zmod_two, hoa.natCast_zmod_two,
        hbe.natCast_zmod_two, hce.natCast_zmod_two, hroot] at he
    · simp [pent, derivative_X_pow, hon.natCast_zmod_two, hea.natCast_zmod_two,
        hbe.natCast_zmod_two, hce.natCast_zmod_two, hroot] at he
  · intro p hp hpf
    letI : Fact (Irreducible p) := ⟨hp⟩
    by_contra! hsmall
    have hroot := root_ne_zero_of_factor hp hpf hconst
    have hpow := root_pow_period hp hsmall hroot
    obtain ⟨i, hi⟩ := hperiod
    obtain ⟨k, hk⟩ := hgap
    have htwo : (1 : AdjoinRoot p) + 1 = 0 := by
      simpa using congrArg (AdjoinRoot.of p) (show (1 : ZMod 2) + 1 = 0 by decide)
    have twice (x : AdjoinRoot p) : x + x = 0 := by
      calc x + x = (1 + 1) * x := by ring
           _ = 0 := by rw [htwo, zero_mul]
    have he := AdjoinRoot.mk_eq_zero.2 hpf
    simp [pent, hi, hk, pow_add, pow_mul, hpow, twice, hroot] at he

/-- For n > 6*L*M there are at least L*M^3 distinct squarefree
pentanomials with all factors of degree > B, where L = period B. -/
theorem many_sifted_pentanomials (B n M : ℕ) (hn : 6 * period B * M < n) :
    ∃ S : Finset BinaryPoly, S.card = period B * M ^ 3 ∧
      ∀ f ∈ S, f.natDegree = n ∧ f.support.card = 5 ∧ Squarefree f ∧
        ∀ p : BinaryPoly, Irreducible p → p ∣ f → B < p.natDegree := by
  classical
  let L := period B
  have hL : 0 < L := period_pos B
  let I := Fin M × Fin (L * M) × Fin M
  let shift := if Even n then 1 else 2
  let a (z : I) := L * (2 * z.1.val + shift)
  let b (z : I) := 2 * (L * M) + 2 * (z.2.1.val + 1)
  let c (z : I) := b z + L * (2 * (z.2.2.val + 1))
  let poly (z : I) := pent n (a z) (b z) (c z)
  have bounds (z : I) : 0 < a z ∧ a z < b z ∧ b z < c z ∧ c z < n := by
    have hdelta : 0 < shift ∧ shift ≤ 2 := by dsimp [shift]; split <;> decide
    have ha0 := Nat.mul_pos hL (show 0 < 2 * z.1.val + shift by omega)
    have ha1 := Nat.mul_le_mul_left L (show 2 * z.1.val + shift ≤ 2 * M by have := z.1.isLt; omega)
    have hc0 := Nat.mul_pos hL (show 0 < 2 * (z.2.2.val + 1) by omega)
    have hc1 := Nat.mul_le_mul_left L
      (show 2 * (z.2.2.val + 1) ≤ 2 * M by have := z.2.2.isLt; omega)
    have hb1 := z.2.1.isLt
    change 6 * L * M < n at hn
    rw [Nat.mul_assoc] at hn
    rw [Nat.mul_left_comm L 2 M] at ha1 hc1
    dsimp only [a, b, c]
    omega
  have hi : Function.Injective poly := by
    intro z w h
    obtain ⟨hz1, hz2, hz3, _⟩ := bounds z
    obtain ⟨hw1, hw2, hw3, _⟩ := bounds w
    obtain ⟨ea, eb, ec⟩ := pent_injective hz1 hz2 hz3 hw1 hw2 hw3 h
    have h1 := Nat.eq_of_mul_eq_mul_left hL ea
    change b z + _ = b w + _ at ec
    rw [eb] at ec
    have h3 := Nat.eq_of_mul_eq_mul_left hL (Nat.add_left_cancel ec)
    dsimp only [b] at eb
    exact Prod.ext (Fin.ext (by omega)) (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
  refine ⟨Finset.univ.image poly, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hi]
    simp [I, L]
    ring
  · intro f hf
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.1 hf
    obtain ⟨ha, hb, hc, ht⟩ := bounds z
    have heB : Even (b z) := Even.add (even_two.mul_right _) (even_two.mul_right _)
    refine pent_sifted ha hb hc ht (dvd_mul_right L _) ⟨_, rfl⟩ ?_ heB
      (heB.add ((even_two.mul_right _).mul_left _))
    rcases Nat.even_or_odd n with he | ho
    · refine Or.inl ⟨he, ?_⟩
      simpa [a, shift, he] using (period_odd B).mul (show Odd (2 * z.1.val + 1) from ⟨_, rfl⟩)
    · refine Or.inr ⟨ho, ?_⟩
      simpa [a, shift, Nat.not_even_iff_odd.2 ho] using
        (((even_two.mul_right z.1.val).add even_two).mul_left L)

end GF2Sparse
