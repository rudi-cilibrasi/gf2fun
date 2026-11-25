import GF2Sparse.SignedTriples
import GF2Sparse.LocalFactors
import Mathlib.Data.Nat.Factorization.Basic

/-! Choosing a dyadic inner exponent when the degree is 2^s-2^t-1. -/

namespace GF2Sparse

open Polynomial

private theorem excludes_of_three_part {m h : ℕ} (hm : 0 < m) (hd : ordProj[3] m ∣ h)
    (ho : m%2=1 ∨ h%2=1) : excludesTwistedPeriod m h := by
  let A := ordProj[3] m
  let C := ordCompl[3] m
  have hmA : A*C = m := Nat.ordProj_mul_ordCompl_eq_self m 3
  have hcop : Nat.Coprime 3 C := Nat.coprime_ordCompl Nat.prime_three hm.ne'
  obtain ⟨k, hk⟩ := hd
  have hmul : 3*h = A*(3*k) := by rw [hk]; dsimp [A]; ring
  have hgd : m.gcd (3*h) = A*(C.gcd k) := by
    calc
      _ = (A*C).gcd (A*(3*k)) := congrArg₂ Nat.gcd hmA.symm hmul
      _ = _ := by rw [Nat.gcd_mul_left, hcop.gcd_mul_left_cancel_right]
  refine ⟨?_, Nat.coprime_two_right.2 ?_⟩
  · rw [hgd, hk]
    exact Nat.mul_dvd_mul_left A (Nat.gcd_dvd_right C k)
  · exact ho.elim (fun e => Odd.of_dvd_nat (Nat.odd_iff.2 e) (Nat.gcd_dvd_left ..))
      (fun e => Odd.of_dvd_nat (Nat.odd_iff.2 e) (Nat.gcd_dvd_right ..))

private def acceptableParity (s t i : ℕ) : Prop :=
  (s%2=1 ∨ i%2 ≠ t%2) ∧ ((s-t)%2=1 ∨ i%2=1)

private theorem adjust_parity {s t H b : ℕ} (ht : t < s) (hb : b < s) (hodd : H%2=1)
    (hbase : (b=t ∧ H ∣ s) ∨ (b=0 ∧ H ∣ s-t)) :
    ∃ i < s, i ≡ b [MOD H] ∧ acceptableParity s t i := by
  by_cases hgood : acceptableParity s t b
  · exact ⟨b, hb, Nat.ModEq.rfl, hgood⟩
  have hsmall : 2*H ≤ s := by
    by_contra! hlarge
    have eqH {m : ℕ} (hm : 0 < m) (hle : m ≤ s) (hd : H ∣ m) : m=H := by
      obtain ⟨k, hk⟩ := hd
      by_cases hk1 : k=1
      · simpa [hk1] using hk
      · have hk2 : 2 ≤ k := by
          have hne : k ≠ 0 := by intro he; simp [he] at hk; omega
          omega
        have := Nat.mul_le_mul_left H hk2
        omega
    unfold acceptableParity at hgood
    rcases hbase with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · have := eqH (by omega) (le_refl s) h
      omega
    · have := eqH (by omega) (Nat.sub_le s t) h
      omega
  have flip (i : ℕ) (hi : i%2 ≠ b%2) : acceptableParity s t i := by
    unfold acceptableParity at *
    omega
  by_cases hplus : b+H < s
  · exact ⟨b+H, hplus, by simp [Nat.ModEq], flip _ (by omega)⟩
  · have hHb : H ≤ b := by omega
    refine ⟨b-H, by omega, (Nat.modEq_iff_dvd' (Nat.sub_le _ _)).2 ?_, flip _ (by omega)⟩
    rw [Nat.sub_sub_self hHb]

private theorem choose_twisted_periods {s t : ℕ} (ht : 0 < t) (hst : t < s) :
    ∃ i < s, excludesTwistedPeriod s (i.dist t) ∧ excludesTwistedPeriod (s-t) i := by
  let A := ordProj[3] s
  let B := ordProj[3] (s-t)
  have hA : A ∣ s := Nat.ordProj_dvd s 3
  have hB : B ∣ s-t := Nat.ordProj_dvd (s-t) 3
  have hodd (j : ℕ) : (3^j)%2=1 := Nat.odd_iff.1 ((by decide : Odd (3:ℕ)).pow)
  have sub {d : ℕ} (hs : d ∣ s) (hd : d ∣ s-t) : d ∣ t := by
    simpa only [Nat.sub_sub_self hst.le] using Nat.dvd_sub hs hd
  obtain ⟨H, b, hOdd, hb, hbase, hAH, hBH, hbA, hbB⟩ :
      ∃ H b, H%2=1 ∧ b<s ∧ ((b=t ∧ H ∣ s) ∨ (b=0 ∧ H ∣ s-t)) ∧
        A ∣ H ∧ B ∣ H ∧ b ≡ t [MOD A] ∧ b ≡ 0 [MOD B] := by
    rcases le_total ((s-t).factorization 3) (s.factorization 3) with h | h
    · have hBA : B ∣ A := pow_dvd_pow 3 h
      exact ⟨A, t, hodd _, hst, Or.inl ⟨rfl, hA⟩, dvd_rfl, hBA, Nat.ModEq.rfl,
        Nat.modEq_zero_iff_dvd.2 (sub (hBA.trans hA) hB)⟩
    · have hAB : A ∣ B := pow_dvd_pow 3 h
      exact ⟨B, 0, hodd _, by omega, Or.inr ⟨rfl, hB⟩, hAB, dvd_rfl,
        (Nat.modEq_zero_iff_dvd.2 (sub hA (hAB.trans hB))).symm, Nat.ModEq.rfl⟩
  obtain ⟨i, hi, hib, hpar⟩ := adjust_parity hst hb hOdd hbase
  have hiA := (Nat.ModEq.of_dvd hAH hib).trans hbA
  have hiB := Nat.modEq_zero_iff_dvd.1 ((Nat.ModEq.of_dvd hBH hib).trans hbB)
  refine ⟨i, hi, excludes_of_three_part (by omega) ?_ ?_,
    excludes_of_three_part (by omega) hiB hpar.2⟩
  · rcases le_total i t with hle | hle
    · rw [Nat.dist_eq_sub_of_le hle]; exact (Nat.modEq_iff_dvd' hle).1 hiA
    · rw [Nat.dist_eq_sub_of_le_right hle]; exact (Nat.modEq_iff_dvd' hle).1 hiA.symm
  · rcases hpar.1 with ho | hne
    · exact Or.inl ho
    · right
      rcases le_total i t with hle | hle
      · rw [Nat.dist_eq_sub_of_le hle]; omega
      · rw [Nat.dist_eq_sub_of_le_right hle]; omega

private theorem trinomial_three_terms {n a : ℕ} (ha : 0 < a) (han : a < n) :
    (trinomial n a).support.card = 3 := by
  let terms : Finset ℕ := {n,a,0}
  have hn : 0 < n := ha.trans han
  have hform : trinomial n a = ∑ i ∈ terms, X^i := by
    simp [terms, trinomial, Finset.sum_insert, ha.ne', han.ne', hn.ne']
  have hs : (trinomial n a).support = terms := by
    rw [hform]
    ext i
    simp [mem_support_iff, coeff_X_pow]
  simp [hs, terms, ha.ne', han.ne', hn.ne']

private theorem trinomial_separable_odd_degree {n a : ℕ} (hn : Odd n) (ha : 0 < a) :
    (trinomial n a).Separable := by
  have hn0 : 0 < n := by obtain ⟨k,hk⟩ := hn; omega
  have hc : (trinomial n a).coeff 0 = 1 := by simp [trinomial, coeff_X_pow, ha.ne, hn0.ne]
  refine isCoprime_of_irreducible_dvd (fun h => by simp [h.1] at hc) ?_
  intro p hp hpf hpd
  letI : Fact (Irreducible p) := ⟨hp⟩
  let x := AdjoinRoot.root p
  have hx : x ≠ 0 := root_ne_zero_of_factor hp hpf hc
  have hd := AdjoinRoot.mk_eq_zero.2 hpd
  rcases Nat.even_or_odd a with he | ho
  · dsimp [x] at hx
    simp [trinomial, derivative_X_pow, hn.natCast_zmod_two, he.natCast_zmod_two, hx] at hd
  · have heq : x^(n-1)+x^(a-1)=0 := by
      simpa [trinomial, derivative_X_pow, hn.natCast_zmod_two, ho.natCast_zmod_two, x] using hd
    have hder := congrArg (x * ·) heq
    simp only [mul_add, ← pow_succ', Nat.sub_add_cancel hn0, Nat.sub_add_cancel ha, mul_zero] at hder
    have hval : x^n+(x^a+1)=0 := by simpa [x, trinomial] using AdjoinRoot.mk_eq_zero.2 hpf
    exact one_ne_zero (α := AdjoinRoot p) (by linear_combination hval - hder)

/-- Every degree n=2^s-2^t-1 with 1 ≤ t ≤ s-2 admits a passing trinomial
with a power-of-two inner exponent strictly between 0 and n and coprime to n. -/
theorem exists_signed_dyadic_trinomial {s t : ℕ} (ht : 0 < t) (hst : t+2 ≤ s) :
    let n := 2^s-2^t-1
    ∃ i < s, 2^i < n ∧ n.Coprime (2^i) ∧ (trinomial n (2^i)).natDegree = n ∧
      (trinomial n (2^i)).support.card = 3 ∧ Squarefree (trinomial n (2^i)) ∧
      NoRootTriple (trinomial n (2^i)) := by
  obtain ⟨i, hi, hfirst, hsecond⟩ := choose_twisted_periods ht (by omega : t < s)
  have htp := Nat.pow_le_pow_right (by decide : 0 < 2) (show t+1 ≤ s-1 by omega)
  have hip := Nat.pow_le_pow_right (by decide : 0 < 2) (show i ≤ s-1 by omega)
  have hs : 2^s = 2^(s-1)*2 := by conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ s), pow_succ]
  rw [pow_succ] at htp
  have hbt : 1 < 2^t := Nat.one_lt_two_pow ht.ne'
  have htc : 2^t = 2^(t-1)*2 := by conv_lhs => rw [← Nat.sub_add_cancel ht, pow_succ]
  have ha : 2^i < 2^s-2^t-1 := by omega
  have hodd : Odd (2^s-2^t-1) := Nat.odd_iff.2 (by omega)
  exact ⟨i, hi, ha, (Nat.coprime_two_right.2 hodd).pow_right i,
    trinomial_degree (Nat.two_pow_pos _) ha, trinomial_three_terms (Nat.two_pow_pos _) ha,
    (trinomial_separable_odd_degree hodd (Nat.two_pow_pos _)).squarefree,
    signed_dyadic_no_root_triple (by omega) (by omega) hfirst hsecond⟩

end GF2Sparse
