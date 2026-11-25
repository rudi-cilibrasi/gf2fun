import GF2Sparse.Roots
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.FieldTheory.Separable

/-! Exact root orders under the substitution X ↦ X^m. -/

namespace GF2Sparse

open Polynomial

/-- If g has the same degree as f and divides f(X^m), the root map
z ↦ z^m transfers primitivity in both directions subject to coprimality. -/
theorem primitive_iff_of_dvd_expand {f g : BinaryPoly} {m : ℕ}
    (hf : f.Monic) (hg : g.Monic) (hn : 0 < f.natDegree) (hd : g.natDegree = f.natDegree)
    (hm : 0 < m) (hgf : g ∣ expand (ZMod 2) m f) :
    Primitive f ↔ Primitive g ∧ (2 ^ f.natDegree - 1).Coprime m := by
  let N := 2 ^ f.natDegree - 1
  have hN : 0 < N := Nat.sub_pos_of_lt (Nat.one_lt_two_pow hn.ne')
  constructor
  · intro hprim
    obtain ⟨p, hp, hpg⟩ := WfDvdMonoid.exists_irreducible_factor
      (not_isUnit_of_natDegree_pos g (hd ▸ hn)) hg.ne_zero
    letI : Fact (Irreducible p) := ⟨hp⟩
    let z := AdjoinRoot.root p
    have hz : aeval z g = 0 := by rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_eq_zero.2 hpg
    have hfz : aeval (z ^ m) f = 0 := by
      rw [← expand_aeval, AdjoinRoot.aeval_eq]
      exact AdjoinRoot.mk_eq_zero.2 (hpg.trans hgf)
    have hzm : orderOf (z ^ m) = N := (orderOf_root_at hprim.2.1 hfz).trans hprim.2.2
    have hz0 : z ≠ 0 := by
      intro he
      rw [he, zero_pow hm.ne', orderOf_zero] at hzm
      omega
    let e := (AdjoinRoot.powerBasisAux hp.ne_zero).equivFun.toEquiv
    letI : Fintype (AdjoinRoot p) := Fintype.ofEquiv _ e.symm
    have hpow := FiniteField.pow_card_sub_one_eq_one z hz0
    rw [card_adjoinRoot hp.ne_zero] at hpow
    have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt (Nat.one_lt_two_pow hp.natDegree_pos.ne'))
      (orderOf_dvd_of_pow_eq_one hpow)
    have hpdeg := (natDegree_le_of_dvd hpg hg.ne_zero).trans hd.le
    have hub : orderOf z ≤ N := hle.trans (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) hpdeg) 1)
    have he : orderOf z / (orderOf z).gcd m = N := (orderOf_pow' z hm.ne').symm.trans hzm
    have ho : orderOf z = N := le_antisymm hub (he ▸ Nat.div_le_self _ _)
    refine ⟨primitive_of_root_order hg (hd ▸ hn) hz (ho.trans (by rw [hd])), ?_⟩
    change N.gcd m = 1
    rw [ho] at he
    have hpos := Nat.gcd_pos_of_pos_left m hN
    by_contra! h
    exact (Nat.div_lt_self hN (by omega : 1 < N.gcd m)).ne he
  · rintro ⟨hp, hc⟩
    letI : Fact (Irreducible g) := ⟨hp.2.1⟩
    let z := AdjoinRoot.root g
    have ho : orderOf z = 2 ^ f.natDegree - 1 := hp.2.2.trans (by rw [hd])
    have hfz : aeval (z ^ m) f = 0 := by
      rw [← expand_aeval, AdjoinRoot.aeval_eq]
      exact AdjoinRoot.mk_eq_zero.2 hgf
    exact primitive_of_root_order hf hn hfz ((show (orderOf z).Coprime m from ho ▸ hc).orderOf_pow.trans ho)

private theorem lift_frobenius {K : Type*} [Field K] {x y : K} {n : ℕ}
    (hx : x ^ (2 ^ n) = x * y) (hy : y ^ (2 ^ n) = y) (k : ℕ) :
    x ^ (2 ^ (n * k)) = x * y ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, pow_add, pow_mul, ih, mul_pow, hx, ← pow_mul, Nat.mul_comm k,
      pow_mul, hy, pow_succ', mul_assoc]

/-- Let f be irreducible of degree n with nonzero constant coefficient.
For m dividing N = 2^n-1, every irreducible divisor of f(X^m) has degree
n times the order of alpha^(N/m), where alpha is a root of f. -/
theorem factor_degree_of_expand {f p : BinaryPoly} (hf : Irreducible f)
    (hc : f.coeff 0 = 1) (hp : Irreducible p) {m : ℕ}
    (hm : m ∣ 2 ^ f.natDegree - 1) (hpf : p ∣ expand (ZMod 2) m f) :
    p.natDegree = f.natDegree * orderOf (AdjoinRoot.root f ^ ((2 ^ f.natDegree - 1) / m)) := by
  let n := f.natDegree
  let N := 2 ^ n - 1
  have hN : 0 < N := Nat.sub_pos_of_lt (Nat.one_lt_two_pow hf.natDegree_pos.ne')
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hm hN
  letI : Fact (Irreducible f) := ⟨hf⟩
  letI : Fact (Irreducible p) := ⟨hp⟩
  let β := AdjoinRoot.root p
  let α := β ^ m
  let y := α ^ (N / m)
  have hα : aeval α f = 0 := by
    change aeval (β ^ m) f = 0
    rw [← expand_aeval, AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_eq_zero.2 hpf
  have hβ : aeval β p = 0 := (AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self
  have hβ0 : β ≠ 0 := by
    intro he
    have ha0 : α = 0 := by simp [α, he, hm0.ne']
    rw [ha0, ← coeff_zero_eq_aeval_zero', hc, map_one] at hα
    exact one_ne_zero hα
  have hαfixed := (degree_dvd_iff_frobenius hf hα n).1 dvd_rfl
  have hy : y ^ (2 ^ n) = y := by
    change (α ^ (N / m)) ^ (2 ^ n) = _
    rw [← pow_mul, mul_comm, pow_mul, hαfixed]
  have hx : β ^ (2 ^ n) = β * y := by
    change _ = β * (β ^ m) ^ (N / m)
    rw [← pow_mul, Nat.mul_div_cancel' hm, ← pow_succ', Nat.sub_add_cancel (Nat.two_pow_pos n)]
  have hβfixed := (degree_dvd_iff_frobenius hp hβ p.natDegree).1 dvd_rfl
  have hbase : n ∣ p.natDegree := (degree_dvd_iff_frobenius hf hα _).2 (by
    change (β ^ m) ^ (2 ^ p.natDegree) = _
    rw [← pow_mul, mul_comm, pow_mul, hβfixed])
  obtain ⟨j, hj⟩ := hbase
  have hperiod (k : ℕ) : p.natDegree ∣ n * k ↔ orderOf y ∣ k := by
    rw [degree_dvd_iff_frobenius hp hβ, lift_frobenius hx hy, orderOf_dvd_iff_pow_eq_one]
    exact ⟨fun h => mul_left_cancel₀ hβ0 (h.trans (mul_one β).symm), fun h => by rw [h, mul_one]⟩
  have h₁ := (hperiod j).1 (hj ▸ dvd_rfl)
  have h₂ := (hperiod (orderOf y)).2 dvd_rfl
  rw [hj] at h₂
  have he := Nat.dvd_antisymm (Nat.dvd_of_mul_dvd_mul_left hf.natDegree_pos h₂) h₁
  let φ := AdjoinRoot.liftAlgHom f (Algebra.ofId _ _) α hα
  have horder : orderOf y = orderOf (AdjoinRoot.root f ^ (N / m)) := by
    simpa [φ, y, AdjoinRoot.liftAlgHom_root] using
      orderOf_injective φ.toMonoidHom φ.injective (AdjoinRoot.root f ^ (N / m))
  exact hj.trans (congrArg (n * ·) (he.trans horder))

private theorem scaled_field_size {q m : ℕ} (hq : 1 < q) (hm : 1 < m) :
    m * (q - 1) < q ^ m - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ m by omega)
  suffices h : (2 + k) * (q - 1) + 1 < q ^ (2 + k) by omega
  induction k with
  | zero =>
    simp only [Nat.add_zero, sq]
    have h := Nat.mul_le_mul_right q hq
    omega
  | succ k ih =>
    specialize ih (by omega)
    rw [← Nat.add_assoc, Nat.add_one_mul, pow_succ]
    have hpos : 1 ≤ q ^ (2 + k) := Nat.one_le_pow _ _ (by omega)
    have h := Nat.mul_le_mul_right (q - 1) hpos
    have he : q ^ (2 + k) * q = q ^ (2 + k) * (q - 1) + q ^ (2 + k) := by
      rw [← Nat.mul_succ, show (q - 1).succ = q by omega]
    omega

/-- A primitive polynomial of positive degree cannot be g(X^m) for m>1. -/
theorem not_primitive_expand {g : BinaryPoly} {m : ℕ} (hg : 0 < g.natDegree) (hm : 1 < m) :
    ¬ Primitive (expand (ZMod 2) m g) := by
  intro hp
  let f := expand (ZMod 2) m g
  letI : Fact (Irreducible f) := ⟨hp.2.1⟩
  let e := (AdjoinRoot.powerBasisAux hp.2.1.ne_zero).equivFun.toEquiv
  letI : Fintype (AdjoinRoot f) := Fintype.ofEquiv _ e.symm
  let z := AdjoinRoot.root f
  have ho : orderOf z = 2 ^ (g.natDegree * m) - 1 := hp.2.2.trans (by rw [natDegree_expand])
  have hpos := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.mul_pos hg (by omega : 0 < m)).ne')
  have hz0 : z ≠ 0 := by intro he; rw [he, orderOf_zero] at ho; omega
  have hz : aeval (z ^ m) g = 0 := by
    rw [← expand_aeval, AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_self
  have hle := order_le_of_aeval (pow_ne_zero m hz0) (fun he => by simp [he] at hg) hz
  have hd : orderOf z ∣ m * orderOf (z ^ m) := orderOf_dvd_of_pow_eq_one
    (by rw [pow_mul, pow_orderOf_eq_one])
  have hbound := (Nat.le_of_dvd (Nat.mul_pos (by omega : 0 < m)
    (isUnit_iff_ne_zero.2 (pow_ne_zero m hz0)).isOfFinOrder.orderOf_pos) hd).trans
    (Nat.mul_le_mul_left m hle)
  rw [ho, pow_mul] at hbound
  exact (scaled_field_size (Nat.one_lt_two_pow hg.ne') hm).not_ge hbound

/-- For the full exponent N, all factors of f(X^N) have degree n*h.
Their number, counted with multiplicity, is N/h. -/
theorem factor_count_full_expand {f : BinaryPoly} (hf : Irreducible f) (hc : f.coeff 0 = 1) :
    let N := 2 ^ f.natDegree - 1
    (UniqueFactorizationMonoid.normalizedFactors (expand (ZMod 2) N f)).card *
      orderOf (AdjoinRoot.root f) = N := by
  classical
  let n := f.natDegree
  let N := 2 ^ n - 1
  have hN : 0 < N := Nat.sub_pos_of_lt (Nat.one_lt_two_pow hf.natDegree_pos.ne')
  let F := expand (ZMod 2) N f
  let factors := UniqueFactorizationMonoid.normalizedFactors F
  have hmon : F.Monic := (binary_monic hf.ne_zero).expand hN
  have hprod : factors.prod = F := by
    simpa [factors, hmon.leadingCoeff] using leadingCoeff_mul_prod_normalizedFactors F
  have hmem {p} (h : p ∈ factors) := (Polynomial.mem_normalizedFactors_iff hmon.ne_zero).1 h
  have hdeg (p) (hp : p ∈ factors) : p.natDegree = n * orderOf (AdjoinRoot.root f) := by
    simpa [N, n, Nat.div_self hN] using
      factor_degree_of_expand hf hc (hmem hp).1 (m := N) dvd_rfl (hmem hp).2.2
  have he := natDegree_multiset_prod_of_monic factors (fun _ hp => (hmem hp).2.1)
  rw [hprod, natDegree_expand, Multiset.map_congr rfl hdeg, Multiset.map_const',
    Multiset.sum_replicate, nsmul_eq_mul] at he
  change factors.card * orderOf (AdjoinRoot.root f) = N
  apply Nat.eq_of_mul_eq_mul_left hf.natDegree_pos
  calc
    _ = factors.card * (n * orderOf (AdjoinRoot.root f)) := by rw [Nat.mul_left_comm]
    _ = _ := he.symm

/-- An irreducible f with nonzero constant term is primitive precisely when
its single full dilation stays irreducible. -/
theorem primitive_iff_irreducible_full_expand {f : BinaryPoly} (hf : Irreducible f)
    (hc : f.coeff 0 = 1) :
    Primitive f ↔ Irreducible (expand (ZMod 2) (2 ^ f.natDegree - 1) f) := by
  let N := 2 ^ f.natDegree - 1
  let F := expand (ZMod 2) N f
  have hN : 0 < N := Nat.sub_pos_of_lt (Nat.one_lt_two_pow hf.natDegree_pos.ne')
  have hmon : F.Monic := (binary_monic hf.ne_zero).expand hN
  have hdeg : F.natDegree = f.natDegree * N := natDegree_expand _ _
  have hfactor {p} (hp : Irreducible p) (hpf : p ∣ F) :
      p.natDegree = f.natDegree * orderOf (AdjoinRoot.root f) := by
    have he := factor_degree_of_expand hf hc hp (m := N) dvd_rfl hpf
    change p.natDegree = f.natDegree * orderOf (AdjoinRoot.root f ^ (N / N)) at he
    simpa [Nat.div_self hN] using he
  constructor
  · intro h
    obtain ⟨p, hp, hpf⟩ := WfDvdMonoid.exists_irreducible_factor
      (not_isUnit_of_natDegree_pos F (hdeg ▸ Nat.mul_pos hf.natDegree_pos hN)) hmon.ne_zero
    have heq : F = p := eq_of_monic_of_dvd_of_natDegree_le (binary_monic hp.ne_zero) hmon hpf
      (by rw [hdeg, hfactor hp hpf, h.2.2])
    change Irreducible F
    rw [heq]
    exact hp
  · intro h
    have he := hfactor h (dvd_refl F)
    rw [hdeg] at he
    exact ⟨binary_monic hf.ne_zero, hf, Nat.eq_of_mul_eq_mul_left hf.natDegree_pos he.symm⟩

theorem primitive_iff_full_expand {f : BinaryPoly} (hn : 0 < f.natDegree) (hc : f.coeff 0 = 1) :
    Primitive f ↔ Irreducible (expand (ZMod 2) (2 ^ f.natDegree - 1) f) := by
  refine ⟨fun h => (primitive_iff_irreducible_full_expand h.2.1 hc).1 h, fun h => ?_⟩
  have hf := of_irreducible_expand (Nat.sub_pos_of_lt (Nat.one_lt_two_pow hn.ne')).ne' h
  exact (primitive_iff_irreducible_full_expand hf hc).2 h

/-- The factors counted above are distinct. -/
theorem squarefree_expand_of_dvd {f : BinaryPoly} (hf : Irreducible f) (hc : f.coeff 0 = 1)
    {m : ℕ} (hm : m ∣ 2 ^ f.natDegree - 1) : Squarefree (expand (ZMod 2) m f) := by
  let N := 2 ^ f.natDegree - 1
  have hN : 0 < N := Nat.sub_pos_of_lt (Nat.one_lt_two_pow hf.natDegree_pos.ne')
  have hodd : Odd N := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hf.natDegree_pos.ne'
    dsimp [N]
    rw [hk, pow_succ]
    exact ⟨2 ^ k - 1, by have := Nat.two_pow_pos k; omega⟩
  letI : Fact (Irreducible f) := ⟨hf⟩
  let e := (AdjoinRoot.powerBasisAux hf.ne_zero).equivFun.toEquiv
  letI : Fintype (AdjoinRoot f) := Fintype.ofEquiv _ e.symm
  have hx : AdjoinRoot.root f ≠ 0 := by
    intro h
    have hval := AdjoinRoot.mk_self (f := f)
    rw [← AdjoinRoot.aeval_eq, h, ← coeff_zero_eq_aeval_zero', hc, map_one] at hval
    exact one_ne_zero hval
  have hpow := FiniteField.pow_card_sub_one_eq_one _ hx
  rw [card_adjoinRoot hf.ne_zero] at hpow
  have hd : f ∣ X ^ N - 1 := AdjoinRoot.mk_eq_zero.1 (by simpa [N] using sub_eq_zero.2 hpow)
  have he : expand (ZMod 2) m f ∣ X ^ (m * N) - 1 := by
    simpa only [map_sub, map_pow, map_one, expand_X, ← pow_mul] using map_dvd (expand (ZMod 2) m) hd
  have hcoef : (↑(m * N) : ZMod 2) ≠ 0 := by rw [((hodd.of_dvd_nat hm).mul hodd).natCast_zmod_two]; decide
  have hs := separable_X_pow_sub_C (1 : ZMod 2) hcoef one_ne_zero
  rw [map_one] at hs
  exact (hs.of_dvd he).squarefree

end GF2Sparse
