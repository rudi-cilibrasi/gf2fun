import GF2Sparse.KasamiTriples
import GF2Sparse.CompositionNorm
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

/-- The n(n-1) off-diagonal quotients occupy different nonidentity powers of the root. -/
theorem trinomial_root_order_lower_bound {n a : ℕ} (ha : 0 < a) (han : a < n)
    (hc : a.Coprime n) (hf : Irreducible (trinomial n a)) {r : K}
    (hr : aeval r (trinomial n a) = 0) : n*n - n + 1 ≤ orderOf r := by
  classical
  let z (i : Fin n) := r^(2^i.val)
  have hd := trinomial_degree ha han
  have hinj : Function.Injective z := by
    simpa only [one_mul] using relative_frobenius_conjugates_injective hf hr
      (r := 1) (m := n) (by decide) (hd.trans (one_mul n).symm)
  have root (i : Fin n) : aeval (z i) (trinomial n a) = 0 := by
    simp [z, aeval_dyadic, hr]
  have nz (i : Fin n) : z i ≠ 0 := trinomial_root_ne_zero ha han (root i)
  let q (p : Fin n × Fin n) := z p.1 / z p.2
  let pairs := (Finset.univ : Finset (Fin n)).offDiag
  have inj : Set.InjOn q (pairs : Set (Fin n × Fin n)) := by
    rintro ⟨i,j⟩ hij ⟨k,l⟩ _ h
    have hprod := (div_eq_div_iff (nz j) (nz l)).1 h
    rcases trinomial_root_pair_unique ha han hc (root i) (root l) (root k) (root j) hprod with h | h
    · exact Prod.ext (hinj h.1) (hinj h.2.symm)
    · exact ((Finset.mem_offDiag.1 hij).2.2 (hinj h.1)).elim
  have none : 1 ∉ pairs.image q := by
    rintro h
    obtain ⟨⟨i,j⟩,hij,he⟩ := Finset.mem_image.1 h
    exact (Finset.mem_offDiag.1 hij).2.2 (hinj ((div_eq_one_iff_eq (nz j)).1 he))
  have hfix := (degree_dvd_iff_frobenius hf hr n).1 (by rw [hd])
  have hpower : r^(2^n-1) = 1 := by
    apply mul_right_cancel₀ (trinomial_root_ne_zero ha han hr)
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel (Nat.two_pow_pos _), hfix]
  have ht : 0 < orderOf r := (isOfFinOrder_iff_pow_eq_one.2
    ⟨2^n-1, Nat.sub_pos_of_lt (Nat.one_lt_two_pow (ha.trans han).ne'), hpower⟩).orderOf_pos
  have inside : insert 1 (pairs.image q) ⊆ nthRootsFinset (orderOf r) (1 : K) := by
    intro t ht'
    apply (mem_nthRootsFinset ht 1).2
    rcases Finset.mem_insert.1 ht' with rfl | hm
    · exact one_pow _
    · obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.1 hm
      have h (i : Fin n) : (z i)^(orderOf r) = 1 := by
        change (r ^ (2 ^ i.val)) ^ orderOf r = 1
        rw [pow_right_comm, pow_orderOf_eq_one, one_pow]
      simp only [q, div_pow, h, div_one]
  have hcard := (Finset.card_le_card inside).trans
    ((Multiset.toFinset_card_le _).trans (card_nthRoots (orderOf r) (1 : K)))
  simpa only [Finset.card_insert_of_notMem none, Finset.card_image_of_injOn inj, pairs,
    Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] using hcard

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
