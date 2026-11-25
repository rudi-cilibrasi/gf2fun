import GF2Sparse.KasamiTriples
import GF2Sparse.CompositionNorm
import GF2Sparse.OrderBound
import GF2Sparse.SignedDegreeChoices
import Mathlib.Data.Finset.Prod

/-! Root quotients of a binary trinomial with relatively prime exponents. -/

namespace GF2Sparse

open Polynomial

variable {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]

private theorem trinomial_powers {n a : ℕ} {x : K} (hx : aeval x (trinomial n a) = 0) :
    x^n = x^a + 1 := by
  simpa only [trinomial, map_add, map_pow, aeval_X, map_one, CharTwo.add_eq_zero] using hx

private theorem trinomial_root_ne_zero {n a : ℕ} (ha : 0 < a) (han : a < n) {x : K}
    (hx : aeval x (trinomial n a) = 0) : x ≠ 0 := by
  rintro rfl
  simpa [ha.ne', (ha.trans han).ne'] using trinomial_powers hx

/-- Equality of two root products determines their unordered pair, including repetitions. -/
theorem trinomial_root_pair_unique {n a : ℕ} (ha : 0 < a) (han : a < n)
    (hc : a.Coprime n) {x y u v : K} (hx : aeval x (trinomial n a) = 0)
    (hy : aeval y (trinomial n a) = 0) (hu : aeval u (trinomial n a) = 0)
    (hv : aeval v (trinomial n a) = 0) (he : x*y = u*v) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  have hp : x^a*y^a = u^a*v^a := by simpa only [mul_pow] using congrArg (· ^ a) he
  have hq := congrArg (· ^ n) he
  simp only [mul_pow, trinomial_powers hx, trinomial_powers hy, trinomial_powers hu,
    trinomial_powers hv] at hq
  have hs : x^a+y^a = u^a+v^a := by linear_combination hq - hp
  have hz : (x^a-u^a)*(x^a-v^a) = 0 := by linear_combination x^a * hs - hp
  have same {z : K} (hz : aeval z (trinomial n a) = 0) (heq : x^a = z^a) : x = z := by
    have hn : x^n = z^n := by rw [trinomial_powers hx, trinomial_powers hz, heq]
    have z0 := trinomial_root_ne_zero ha han hz
    apply (div_eq_one_iff_eq z0).1
    apply (pow_eq_one_iff_of_coprime hc).1
    simp [div_pow, heq, hn, z0]
  rcases mul_eq_zero.mp hz with h | h
  · obtain rfl := same hu (sub_eq_zero.mp h)
    exact Or.inl ⟨rfl, mul_left_cancel₀ (trinomial_root_ne_zero ha han hx) he⟩
  · obtain rfl := same hv (sub_eq_zero.mp h)
    rw [mul_comm u x] at he
    exact Or.inr ⟨rfl, mul_left_cancel₀ (trinomial_root_ne_zero ha han hx) he⟩

/-- Distinct roots inside one torsion subgroup give distinct off-diagonal quotients. -/
theorem trinomial_card_le_common_exponent {n a k h : ℕ} (ha : 0 < a) (han : a < n)
    (hc : a.Coprime n) (hh : 0 < h) (z : Fin k → K) (hinj : Function.Injective z)
    (root : ∀ i, aeval (z i) (trinomial n a) = 0) (hpow : ∀ i, (z i)^h = 1) :
    k*k - k + 1 ≤ h := by
  classical
  have nz (i : Fin k) : z i ≠ 0 := trinomial_root_ne_zero ha han (root i)
  let q (p : Fin k × Fin k) := z p.1 / z p.2
  let pairs := (Finset.univ : Finset (Fin k)).offDiag
  have inj : Set.InjOn q (pairs : Set (Fin k × Fin k)) := by
    rintro ⟨i,j⟩ hij ⟨k,l⟩ _ h
    have hprod := (div_eq_div_iff (nz j) (nz l)).1 h
    rcases trinomial_root_pair_unique ha han hc (root i) (root l) (root k) (root j) hprod with h | h
    · exact Prod.ext (hinj h.1) (hinj h.2.symm)
    · exact ((Finset.mem_offDiag.1 hij).2.2 (hinj h.1)).elim
  have none : 1 ∉ pairs.image q := by
    rintro h
    obtain ⟨⟨i,j⟩,hij,he⟩ := Finset.mem_image.1 h
    exact (Finset.mem_offDiag.1 hij).2.2 (hinj ((div_eq_one_iff_eq (nz j)).1 he))
  have inside : insert 1 (pairs.image q) ⊆ nthRootsFinset h (1 : K) := by
    intro t ht'
    apply (mem_nthRootsFinset hh 1).2
    rcases Finset.mem_insert.1 ht' with rfl | hm
    · exact one_pow _
    · obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.1 hm
      simp only [q, div_pow, hpow, div_one]
  have hcard := (Finset.card_le_card inside).trans
    ((Multiset.toFinset_card_le _).trans (card_nthRoots h (1 : K)))
  simpa only [Finset.card_insert_of_notMem none, Finset.card_image_of_injOn inj, pairs,
    Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] using hcard

/-- This bound on the number of roots participating in triples also holds for reducible trinomials. -/
theorem trinomial_triple_root_count_bound {n a k : ℕ} (ha : 0 < a) (han : a < n)
    (hc : a.Coprime n) (x : Fin k → K) (hi : Function.Injective x)
    (hr : ∀ i, aeval (x i) (trinomial n a) = 0)
    (ht : ∀ i, ∃ y z : K, aeval y (trinomial n a) = 0 ∧ aeval z (trinomial n a) = 0 ∧ x i*y*z=1) :
    k*k-k+1 ≤ n*(n-a)+a*a := by
  apply trinomial_card_le_common_exponent ha han hc (by positivity) x hi hr
  intro i
  obtain ⟨y,z,hy,hz,he⟩ := ht i
  exact orderOf_dvd_iff_pow_eq_one.1 (trinomial_triple_order_dvd han.le (hr i) hy hz he)

/-- A binary trinomial with relatively prime positive exponents has simple roots. -/
theorem trinomial_separable_of_coprime {n a : ℕ} (ha : 0 < a) (han : a < n)
    (hc : a.Coprime n) : (trinomial n a).Separable := by
  rcases Nat.even_or_odd n with hn | hn
  · have ho : Odd a := by
      rcases Nat.even_or_odd a with he | ho
      · have hdiv := Nat.dvd_gcd (even_iff_two_dvd.mp he) (even_iff_two_dvd.mp hn)
        rw [hc.gcd_eq_one] at hdiv
        omega
      · exact ho
    have hconst : (trinomial n a).coeff 0 = 1 := by simp [trinomial, coeff_X_pow, ha.ne, (ha.trans han).ne]
    refine isCoprime_of_irreducible_dvd (fun h => by simp [h.1] at hconst) ?_
    intro p hp hpf hpd
    letI : Fact (Irreducible p) := ⟨hp⟩
    have hx := root_ne_zero_of_factor hp hpf hconst
    have he := AdjoinRoot.mk_eq_zero.2 hpd
    simp [trinomial, derivative_X_pow, hn.natCast_zmod_two, ho.natCast_zmod_two, hx] at he
  · exact trinomial_separable_odd_degree hn ha

/-- The whole trinomial has period at least n(n-1)+1, including reducible cases. -/
theorem trinomial_period_lower_bound {n a h : ℕ} (ha : 0 < a) (han : a < n)
    (hc : a.Coprime n) (hh : 0 < h) (hd : trinomial n a ∣ X^h - 1) :
    n*n - n + 1 ≤ h := by
  classical
  let L := AlgebraicClosure (ZMod 2)
  let f := trinomial n a
  have hf0 : f ≠ 0 := by
    intro he
    have hdeg := trinomial_degree ha han
    change f.natDegree = n at hdeg
    simp [he] at hdeg
    omega
  have hcard : Fintype.card (Fin n) = Fintype.card (f.rootSet L) := by
    rw [Fintype.card_fin, card_rootSet_eq_natDegree (trinomial_separable_of_coprime ha han hc)
      (IsAlgClosed.splits _), trinomial_degree ha han]
  let z := Fintype.equivOfCardEq hcard
  have root (i : Fin n) : aeval (z i).val f = 0 := (mem_rootSet_of_ne hf0).1 (z i).property
  apply trinomial_card_le_common_exponent ha han hc hh (fun i => (z i).val)
    (Subtype.val_injective.comp z.injective) root
  intro i
  obtain ⟨g,hg⟩ := hd
  have he := congrArg (aeval (z i).val) hg
  have hi : aeval (z i).val (trinomial n a) = 0 := root i
  simpa only [map_sub, map_pow, aeval_X, map_one, map_mul, hi, zero_mul, sub_eq_zero] using he

/-- The order in the actual quotient ring obeys the lower bound in every degree. -/
theorem trinomial_quotient_order_lower_bound {n a : ℕ} (ha : 0 < a) (han : a < n)
    (hc : a.Coprime n) : n*n - n + 1 ≤ orderOf (AdjoinRoot.root (trinomial n a)) := by
  classical
  let f := trinomial n a
  have hconst : f.coeff 0 = 1 := by simp [f, trinomial, coeff_X_pow, ha.ne, (ha.trans han).ne]
  have hf : f ≠ 0 := by intro he; simp [he] at hconst
  let e := (AdjoinRoot.powerBasisAux hf).equivFun.toEquiv
  letI : Fintype (AdjoinRoot f) := Fintype.ofEquiv _ e.symm
  apply trinomial_period_lower_bound ha han hc (root_unit hconst).isOfFinOrder.orderOf_pos
  apply AdjoinRoot.mk_eq_zero.1
  simp only [map_sub, map_pow, AdjoinRoot.mk_X, map_one]
  exact sub_eq_zero.2 (pow_orderOf_eq_one (AdjoinRoot.root f))

/-- In degree q+1 for a binary power q, the linear tap attains the bound,
even when its quotient is not a field. -/
theorem trinomial_dyadic_plus_one_period (j : ℕ) :
    orderOf (AdjoinRoot.root (trinomial (2^j+1) 1)) = 2^j*2^j+2^j+1 := by
  let f := trinomial (2^j+1) 1
  have hlt : 1 < 2^j+1 := by have := Nat.two_pow_pos j; omega
  have hdeg : 0 < f.natDegree := by rw [trinomial_degree (by decide) hlt]; omega
  letI := AdjoinRoot.nontrivial f (degree_ne_of_natDegree_ne hdeg.ne')
  letI : CharP (AdjoinRoot f) 2 := charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  let r := AdjoinRoot.root f
  have hr := AdjoinRoot.mk_self (f := f)
  change (AdjoinRoot.mk f) (X^(2^j+1)+(X^1+1)) = 0 at hr
  have h1 : r^(2^j+1) = r+1 := by
    simpa only [map_add, map_pow, AdjoinRoot.mk_X, map_one, pow_one, CharTwo.add_eq_zero] using hr
  have h2 := congrArg (fun x => x^(2^j)) h1
  change (r^(2^j+1))^(2^j) = (r+1)^(2^j) at h2
  rw [← pow_mul, Nat.add_mul, Nat.one_mul, add_pow_expChar_pow, one_pow] at h2
  have hp : r^(2^j*2^j+2^j+1) = 1 := by
    rw [pow_succ, h2, add_mul, one_mul, ← pow_succ, h1]
    simp [add_right_comm, CharTwo.add_self_eq_zero]
  have hh : 0 < 2^j*2^j+2^j+1 := by positivity
  have lo := trinomial_quotient_order_lower_bound (by decide : 0 < 1) hlt (Nat.coprime_one_left _)
  have he : (2^j+1)*(2^j+1)-(2^j+1)+1 = 2^j*2^j+2^j+1 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  exact le_antisymm (Nat.le_of_dvd hh (orderOf_dvd_of_pow_eq_one hp)) (he ▸ lo)

/-- The n(n-1) off-diagonal quotients occupy different nonidentity powers of the root. -/
theorem trinomial_root_order_lower_bound {n a : ℕ} (ha : 0 < a) (han : a < n)
    (hc : a.Coprime n) (hf : Irreducible (trinomial n a)) {r : K}
    (hr : aeval r (trinomial n a) = 0) : n*n - n + 1 ≤ orderOf r := by
  have hd := trinomial_degree ha han
  have hfix := (degree_dvd_iff_frobenius hf hr n).1 (by rw [hd])
  have hpower : r^(2^n-1) = 1 := by
    apply mul_right_cancel₀ (trinomial_root_ne_zero ha han hr)
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel (Nat.two_pow_pos _), hfix]
  have ht := (isOfFinOrder_iff_pow_eq_one.2
    ⟨2^n-1, Nat.sub_pos_of_lt (Nat.one_lt_two_pow (ha.trans han).ne'), hpower⟩).orderOf_pos
  apply trinomial_card_le_common_exponent ha han hc ht (fun i : Fin n => r^(2^i.val))
  · simpa only [one_mul] using relative_frobenius_conjugates_injective hf hr
      (r := 1) (m := n) (by decide) (hd.trans (one_mul n).symm)
  · intro i; simp [aeval_dyadic, hr]
  · intro i; rw [pow_right_comm, pow_orderOf_eq_one, one_pow]

/-- No product of two proper subfield group sizes can absorb the whole root order. -/
theorem trinomial_order_not_dvd_subfield_product {n a u v : ℕ} (ha : 0 < a) (han : a < n)
    (hc : a.Coprime n) (hf : Irreducible (trinomial n a)) {r : K}
    (hr : aeval r (trinomial n a) = 0) (hu : ¬n ∣ u) (hv : ¬n ∣ v) :
    ¬orderOf r ∣ (2^u-1)*(2^v-1) := by
  intro h
  have hsum : (2^u-1)*(2^v-1) + (2^u+2^v) = 2^(u+v)+1 := by
    rw [pow_add]
    have h1 := Nat.two_pow_pos u
    have h2 := Nat.two_pow_pos v
    zify [show 1 ≤ 2^u by omega, show 1 ≤ 2^v by omega]
    ring
  have he : r * r^(2^(u+v)) = r^(2^u)*r^(2^v) := by
    rw [← pow_succ', ← hsum, pow_add, (orderOf_dvd_iff_pow_eq_one.1 h), one_mul, pow_add]
  have root (b : ℕ) : aeval (r^(2^b)) (trinomial n a) = 0 := by simp [aeval_dyadic, hr]
  have div {b : ℕ} (hfix : r = r^(2^b)) : n ∣ b := by
    simpa only [trinomial_degree ha han] using (degree_dvd_iff_frobenius hf hr b).2 hfix.symm
  rcases trinomial_root_pair_unique ha han hc hr (root (u+v)) (root u) (root v) he with hp | hp
  · exact hu (div hp.1)
  · exact hv (div hp.1)

/-- Every interior normalized tap strictly between 1 and n-1 precludes a product-one triple
for an irreducible trinomial. -/
theorem trinomial_inner_no_root_triple {n a : ℕ} (ha : 1 < a) (han : a+1 < n)
    (hc : a.Coprime n) (hf : Irreducible (trinomial n a)) : NoRootTriple (trinomial n a) := by
  intro x y z hx hy hz e
  have lo := trinomial_root_order_lower_bound (by omega) (by omega) hc hf hx
  have hi := Nat.le_of_dvd (by positivity : 0 < n*(n-a)+a*a)
    (trinomial_triple_order_dvd (by omega) hx hy hz e)
  have hpos : 0 < (a-1)*(n-a-1) := Nat.mul_pos (by omega) (by omega)
  zify [show a ≤ n by omega, show 1 ≤ a by omega, show 1 ≤ n-a by omega,
    show n ≤ n*n by nlinarith] at lo hi hpos
  nlinarith

/-- Inversion exchanges the two complementary taps. -/
theorem trinomial_inverse_root {n a : ℕ} (ha : 0 < a) (han : a < n) {x : K}
    (hx : aeval x (trinomial n a) = 0) : aeval x⁻¹ (trinomial n (n-a)) = 0 := by
  have hx0 := trinomial_root_ne_zero ha han hx
  have hp : x^(n-a)*x^a = x^n := by rw [← pow_add, Nat.sub_add_cancel han.le]
  have he : (x⁻¹)^(n-a)*x^n = x^a := by
    rw [inv_pow, ← hp, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hx0), one_mul]
  apply mul_right_cancel₀ (pow_ne_zero n hx0)
  simp only [trinomial, map_add, map_pow, aeval_X, map_one, add_mul, one_mul, zero_mul, he]
  rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hx0)]
  simpa only [trinomial, map_add, map_pow, aeval_X, map_one, add_comm, add_left_comm,
    add_assoc] using hx

/-- For all relatively prime exponents above degree nine, irreducibility suffices
for the first three root-product tests. -/
theorem trinomial_no_root_triple_of_nine_lt {n a : ℕ} (hn : 9 < n) (ha : 0 < a)
    (han : a < n) (hc : a.Coprime n) (hf : Irreducible (trinomial n a)) :
    NoRootTriple (trinomial n a) := by
  by_cases ha1 : a = 1
  · subst a
    exact irreducible_dyadic_tap_no_root_triple_of_nine_lt (i := 0) hn han hf
  by_cases he : a+1 = n
  · intro x y z hx hy hz h
    have hi {w : AlgebraicClosure (ZMod 2)} (hw : aeval w (trinomial n a) = 0) :
        aeval w⁻¹ (trinomial n 1) = 0 := by
      simpa only [show n-a=1 by omega] using trinomial_inverse_root ha han hw
    let g := minpoly (ZMod 2) x⁻¹
    have hg : Irreducible g := minpoly.irreducible (Algebra.IsIntegral.isIntegral x⁻¹)
    have hgr : aeval x⁻¹ g = 0 := minpoly.aeval _ _
    have hfix := (degree_dvd_iff_frobenius hg hgr g.natDegree).1 dvd_rfl
    have hd := (degree_dvd_iff_frobenius hf hx g.natDegree).2 (by simpa using congrArg Inv.inv hfix)
    have hdeg := trinomial_degree (show 0 < 1 by decide) (show 1 < n by omega)
    have hg_eq : trinomial n 1 = g := eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic (Algebra.IsIntegral.isIntegral x⁻¹))
      (binary_monic (by intro hzero; simp [hzero] at hdeg; omega)) (minpoly.dvd _ _ (hi hx))
      (by rw [hdeg, ← trinomial_degree ha han]; exact Nat.le_of_dvd hg.natDegree_pos hd)
    have hp : Irreducible (trinomial n 1) := by rwa [hg_eq]
    apply irreducible_dyadic_tap_no_root_triple_of_nine_lt (i := 0) hn (by change 1 < n; omega) hp
      x⁻¹ y⁻¹ z⁻¹ (hi hx) (hi hy) (hi hz)
    simpa only [mul_inv, inv_one] using congrArg Inv.inv h
  · exact trinomial_inner_no_root_triple (by omega) (by omega) hc hf

end GF2Sparse
