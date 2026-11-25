import GF2Sparse.Grid
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic.NormNum.Prime

/-! A rational grid of bounded width can be excluded in prime degrees. -/

namespace GF2Sparse

open Polynomial

/-- Only field sizes whose multiplicative groups have order coprime to p enter this period. -/
def primeGridPeriod (p : ℕ) : ℕ :=
  ((Finset.Icc 1 p).filter (fun d => p.Coprime (2^d-1))).lcm (fun d => 2^d-1)

theorem primeGridPeriod_coprime (p : ℕ) : p.Coprime (primeGridPeriod p) := by
  apply Nat.Coprime.of_dvd_right (Finset.lcm_dvd_prod _ _)
  exact Nat.Coprime.prod_right fun d hd => (Finset.mem_filter.1 hd).2

private theorem primeGridPeriod_pos (p : ℕ) : 0 < primeGridPeriod p := by
  apply Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.2 ?_)
  intro d hd
  have hd1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 hd).1).1
  have hpow := Nat.one_lt_two_pow (show d ≠ 0 by omega)
  omega

private theorem factor_degree_not_multiple (g : BinaryPoly) {h : ℕ} (hg : ¬ h ∣ g.natDegree) :
    ∃ f : BinaryPoly, Irreducible f ∧ f ∣ g ∧ ¬ h ∣ f.natDegree := by
  induction g using WfDvdMonoid.induction_on_irreducible with
  | zero => simp at hg
  | unit u hu => simp [natDegree_eq_zero_of_isUnit hu] at hg
  | mul g f hg0 hf ih =>
    by_cases hd : h ∣ f.natDegree
    · obtain ⟨v, hv, hvg, hdeg⟩ := ih fun h => hg (by rw [natDegree_mul hf.ne_zero hg0]; exact dvd_add hd h)
      exact ⟨v, hv, dvd_mul_of_dvd_right hvg f, hdeg⟩
    · exact ⟨f, hf, dvd_mul_right f g, hd⟩

/-- Every polynomial of odd prime degree p and constant term one has a factor
whose root order divides the same period coprime to p. -/
theorem prime_seed_factor {p : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (g : BinaryPoly) (hg : g.natDegree = p) (hc : g.coeff 0 = 1) :
    ∃ f : BinaryPoly, Irreducible f ∧ f ∣ g ∧ AdjoinRoot.root f ^ primeGridPeriod p = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  let h := orderOf (2 : ZMod p)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have := Nat.le_of_dvd (by decide : 0 < 2) ((ZMod.natCast_eq_zero_iff 2 p).1 hzero)
    omega
  have hcard := orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one (2 : ZMod p) htwo)
  rw [ZMod.card] at hcard
  have hne : h ≠ 1 := by
    intro he
    have hh : (2 : ZMod p) = 1 := orderOf_eq_one_iff.1 he
    exact one_ne_zero (α := ZMod p) (by linear_combination hh)
  have hdeg : ¬ h ∣ g.natDegree := by
    rw [hg]
    intro hd
    have h1 := Nat.dvd_sub hd hcard
    rw [show p - (p-1) = 1 by omega] at h1
    exact hne (Nat.dvd_one.1 h1)
  obtain ⟨f, hf, hfg, hbad⟩ := factor_degree_not_multiple g hdeg
  have hcop : p.Coprime (2^f.natDegree-1) := by
    rw [hp.coprime_iff_not_dvd]
    intro hd
    have heq := (Nat.modEq_iff_dvd' (show 1 ≤ 2^f.natDegree from Nat.two_pow_pos _)).2 hd
    have hz := (ZMod.natCast_eq_natCast_iff 1 (2^f.natDegree) p).2 heq
    exact hbad (orderOf_dvd_of_pow_eq_one (by simpa using hz.symm : (2 : ZMod p)^f.natDegree = 1))
  have hg0 : g ≠ 0 := by intro hz; simp [hz] at hc
  have hle : f.natDegree ≤ p := hg ▸ natDegree_le_of_dvd hfg hg0
  have hdiv : 2^f.natDegree-1 ∣ primeGridPeriod p :=
    Finset.dvd_lcm (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hf.natDegree_pos, hle⟩, hcop⟩)
  letI : Fact (Irreducible f) := ⟨hf⟩
  let basis := (AdjoinRoot.powerBasisAux hf.ne_zero).equivFun.toEquiv
  letI : Fintype (AdjoinRoot f) := Fintype.ofEquiv _ basis.symm
  have hpow := FiniteField.pow_card_sub_one_eq_one _ (root_ne_zero_of_factor hf hfg hc)
  rw [card_adjoinRoot hf.ne_zero] at hpow
  obtain ⟨k, hk⟩ := hdiv
  exact ⟨f, hf, hfg, by rw [hk, pow_mul, hpow, one_pow]⟩

private theorem compress_grid_point {D w p L k a j : ℕ} (hw : w < p)
    (ha : 0 < a) (htop : a < p+D*(L*k)) (hj : j ≤ D)
    (hlo : j*(p+D*(L*k)) ≤ D*a+w) (hhi : D*a ≤ j*(p+D*(L*k))+w) :
    ∃ b : ℕ, (0 < b ∧ b < p) ∧ a ≡ b [MOD L] := by
  let v := L*k
  have hdist : j*(p+D*(L*k)) = j*p+D*(j*v) := by dsimp [v]; ring
  rw [hdist] at hlo hhi
  have hstart : j*v < a := by
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simpa using ha
    · by_contra! hsmall
      have hprod := Nat.mul_le_mul_left D hsmall
      have hbase : p ≤ j*p := by simpa using Nat.mul_le_mul_right p hpos
      omega
  have hstop : a < p+j*v := by
    rcases hj.eq_or_lt with rfl | hlt
    · exact htop
    · by_contra! hlarge
      have hprod := Nat.mul_le_mul_left D hlarge
      rw [Nat.mul_add] at hprod
      have hbase := Nat.mul_le_mul_right p hlt
      rw [Nat.succ_mul] at hbase
      omega
  refine ⟨a-j*v, ⟨by omega, by omega⟩, ?_⟩
  symm
  apply (Nat.modEq_iff_dvd' (Nat.sub_le _ _)).2
  rw [Nat.sub_sub_self hstart.le]
  exact dvd_mul_of_dvd_right (dvd_mul_right L k) j

/-- On a progression starting at p, every polynomial supported in fixed-width bands
around the grid j/D has an irreducible factor of degree at most p. -/
theorem prime_grid_factor {D w p : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hw : w < p) (k : ℕ) (s : Finset ℕ) (n : ℕ)
    (hn : n = p+D*(primeGridPeriod p*k)) (ha : ∀ a ∈ s, 0 < a ∧ a < n)
    (hgrid : ∀ a ∈ s, ∃ j ≤ D, j*n ≤ D*a+w ∧ D*a ≤ j*n+w) :
    ∃ f : BinaryPoly, Irreducible f ∧ f.natDegree ≤ p ∧
      f ∣ X^n+(1+∑ a ∈ s, X^a) := by
  subst n
  have hc (i : s) : ∃ b : ℕ, (0 < b ∧ b < p) ∧ (i : ℕ) ≡ b [MOD primeGridPeriod p] := by
    obtain ⟨j, hj, hlo, hhi⟩ := hgrid i i.property
    exact compress_grid_point hw (ha i i.property).1 (ha i i.property).2 hj hlo hhi
  choose b hb hmod using hc
  have htop : p+D*(primeGridPeriod p*k) ≡ p [MOD primeGridPeriod p] := by
    rw [Nat.mul_left_comm, Nat.add_comm]
    exact Nat.ModEq.modulus_mul_add
  have h := factor_of_compressed_interior_with_period hp.pos (fun i : s => (i : ℕ)) b hb
    htop hmod (prime_seed_factor hp hp2)
  simpa [Finset.sum_attach s (fun a => (X : BinaryPoly)^a)] using h

/-- In degree 1307, support within distance two of 0, 1307/2 and 1307
forces a factor of degree at most five, independently of the number of terms. -/
theorem prime_grid_example_1307 : Nat.Prime 1307 ∧ ∀ s : Finset ℕ,
    (∀ a ∈ s, 0 < a ∧ a < 1307) →
    (∀ a ∈ s, ∃ j ≤ 2, j*1307 ≤ 2*a+4 ∧ 2*a ≤ j*1307+4) →
    ∃ f : BinaryPoly, Irreducible f ∧ f.natDegree ≤ 5 ∧ f ∣ X^1307+(1+∑ a ∈ s, X^a) := by
  refine ⟨by norm_num, fun s ha hgrid => ?_⟩
  exact prime_grid_factor (D := 2) (p := 5) (w := 4) (by decide) (by decide)
    (by decide) 1 s 1307 (by decide) ha hgrid

/-- In every prescribed reduced class, arbitrarily large prime degrees force
a proper bounded-degree factor in every polynomial supported on the given grid. -/
theorem exists_prime_grid_obstruction (D w : ℕ) (hD : 0 < D) {M r : ℕ}
    (hM : 0 < M) (hr : r.Coprime M) :
    ∃ p > w, p.Prime ∧ ∀ B : ℕ, ∃ n > max p B, n.Prime ∧ n ≡ r [MOD M] ∧
      ∀ s : Finset ℕ, (∀ a ∈ s, 0 < a ∧ a < n) →
        (∀ a ∈ s, ∃ j ≤ D, j*n ≤ D*a+w ∧ D*a ≤ j*n+w) →
        ∃ f : BinaryPoly, Irreducible f ∧ f.natDegree ≤ p ∧ f ∣ X^n+(1+∑ a ∈ s, X^a) := by
  obtain ⟨p, hbig, hp, hpM⟩ := Nat.forall_exists_prime_gt_and_modEq (max (max w 2) (M*D)) hM.ne' hr
  have hw : w < p := (le_max_left w 2).trans_lt ((le_max_left _ _).trans_lt hbig)
  have hp2 : 2 < p := (le_max_right w 2).trans_lt ((le_max_left _ _).trans_lt hbig)
  have hMD : p.Coprime (M*D) := by
    apply hp.coprime_iff_not_dvd.2
    intro hd
    have := Nat.le_of_dvd (Nat.mul_pos hM hD) hd
    have := (le_max_right _ _).trans_lt hbig
    omega
  let L := primeGridPeriod p
  let K := M*D*L
  have hK : 0 < K := Nat.mul_pos (Nat.mul_pos hM hD) (primeGridPeriod_pos p)
  have hcop : p.Coprime K := hMD.mul_right (primeGridPeriod_coprime p)
  refine ⟨p, hw, hp, fun B => ?_⟩
  obtain ⟨n, hlarge, hprime, hn⟩ := Nat.forall_exists_prime_gt_and_modEq (max p B) hK.ne' hcop
  have hpn := (le_max_left p B).trans_lt hlarge
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hpn.le).1 hn.symm
  have hdeg : n = p+D*(L*(M*k)) := by
    rw [show D*(L*(M*k)) = K*k by dsimp [K]; ring, ← hk, Nat.add_sub_of_le hpn.le]
  have hMn : n ≡ r [MOD M] := (Nat.ModEq.of_dvd
    (dvd_mul_of_dvd_left (dvd_mul_right M D) L) hn).trans hpM
  exact ⟨n, hlarge, hprime, hMn, fun s ha hgrid => prime_grid_factor hp hp2 hw (M*k) s n hdeg ha hgrid⟩

end GF2Sparse
