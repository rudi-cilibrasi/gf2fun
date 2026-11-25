import GF2Sparse.LocalFactors
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

/-! An unconditional lower bound on the order of X for the locally sifted
family. It uses the relation X^n = g and counts distinct low-degree residues. -/

namespace GF2Sparse

open Polynomial

def exponentPairs (n d : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range n) ×ˢ (Finset.range n)).filter (fun ij => ij.1 + d * ij.2 < n)

/-- Record which of two numbers is smaller, their minimum, and the quotient
and remainder of their difference by d. The minimum and quotient form a
pair in the triangle i + d*j < n. -/
theorem exponentPairs_quadratic (n d : ℕ) (hd : 0 < d) :
    n ^ 2 ≤ 2 * d * (exponentPairs n d).card := by
  let gap (z : Fin n × Fin n) := max z.1.val z.2.val - min z.1.val z.2.val
  have rebuild (z : Fin n × Fin n) :
      min z.1.val z.2.val + d * (gap z / d) + gap z % d = max z.1.val z.2.val := by
    have h := Nat.div_add_mod (gap z) d
    unfold gap at *
    omega
  let point (z : Fin n × Fin n) : exponentPairs n d :=
    ⟨(min z.1.val z.2.val, gap z / d), by
      have hmax := max_lt z.1.isLt z.2.isLt
      have hg : gap z < n := (Nat.sub_le _ _).trans_lt hmax
      have hdiv := (Nat.div_le_self (gap z) d).trans_lt hg
      have h := rebuild z
      simp only [exponentPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega⟩
  let encode (z : Fin n × Fin n) : (exponentPairs n d × Fin d) × Bool :=
    ((point z, ⟨gap z % d, Nat.mod_lt _ hd⟩), decide (z.1.val ≤ z.2.val))
  let restore (w : (exponentPairs n d × Fin d) × Bool) : ℕ × ℕ :=
    let low := w.1.1.val.1
    let high := low + d * w.1.1.val.2 + w.1.2.val
    if w.2 then (low, high) else (high, low)
  have inverse (z : Fin n × Fin n) : restore (encode z) = (z.1.val, z.2.val) := by
    dsimp only [restore, encode, point]
    simp only [rebuild z, decide_eq_true_eq]
    by_cases h : z.1.val ≤ z.2.val
    · rw [if_pos h, min_eq_left h, max_eq_right h]
    · have h' := (lt_of_not_ge h).le
      rw [if_neg h, min_eq_right h', max_eq_left h']
  have hi : Function.Injective encode := by
    intro a b h
    have hh := congrArg restore h
    rw [inverse, inverse, Prod.mk.injEq] at hh
    exact Prod.ext (Fin.ext hh.1) (Fin.ext hh.2)
  simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    Fintype.card_le_of_injective encode hi

theorem root_unit {f : BinaryPoly} (hc : f.coeff 0 = 1) :
    IsUnit (AdjoinRoot.root f) := by
  have hd : X ∣ 1 - f := X_dvd_iff.2 (by simp [hc])
  obtain ⟨q, hq⟩ := hd
  have h := congrArg (AdjoinRoot.mk f) hq
  simp only [map_sub, map_one, AdjoinRoot.mk_self, sub_zero, map_mul, AdjoinRoot.mk_X] at h
  exact IsUnit.of_mul_eq_one _ h.symm

private theorem low_degree_injective {f a b : BinaryPoly} (ha : a.natDegree < f.natDegree)
    (hb : b.natDegree < f.natDegree) (h : AdjoinRoot.mk f a = AdjoinRoot.mk f b) : a = b := by
  by_contra hne
  have hd : f ∣ a - b := AdjoinRoot.mk_eq_zero.1 (by rw [map_sub, h, sub_self])
  exact (not_lt_of_ge (natDegree_le_of_dvd hd (sub_ne_zero.2 hne)))
    ((natDegree_sub_le a b).trans_lt (max_lt ha hb))

/-- Count different polynomial representatives of powers before reduction
modulo f can identify two of them. -/
theorem order_ge_of_representatives {ι : Type*} [Fintype ι] {f : BinaryPoly}
    (hc : f.coeff 0 = 1) (p : ι → BinaryPoly) (e : ι → ℕ) (hinj : Function.Injective p)
    (hlt : ∀ i, (p i).natDegree < f.natDegree)
    (hrep : ∀ i, AdjoinRoot.mk f (p i) = AdjoinRoot.root f ^ e i) :
    Fintype.card ι ≤ orderOf (AdjoinRoot.root f) := by
  classical
  have hf0 : f ≠ 0 := by intro h; simp [h] at hc
  let eqv := (AdjoinRoot.powerBasisAux hf0).equivFun.toEquiv
  letI : Fintype (AdjoinRoot f) := Fintype.ofEquiv _ eqv.symm
  let r := AdjoinRoot.root f
  have ho : 0 < orderOf r := (root_unit hc).isOfFinOrder.orderOf_pos
  let pos (i : ι) : Fin (orderOf r) := ⟨e i % orderOf r, Nat.mod_lt _ ho⟩
  have hi : Function.Injective pos := by
    intro i j he
    have heq := congrArg (fun k : Fin (orderOf r) => r ^ (k : ℕ)) he
    change r ^ (e i % orderOf r) = r ^ (e j % orderOf r) at heq
    rw [pow_mod_orderOf, pow_mod_orderOf, ← hrep, ← hrep] at heq
    exact hinj (low_degree_injective (hlt i) (hlt j) heq)
  simpa [r] using Fintype.card_le_of_injective pos hi

/-- If g(0)=1 and X^n = g in a degree-n quotient, the powers X^(i+n*j)
are distinct for i + deg(g)*j < n. -/
theorem order_ge_exponentPairs {f g : BinaryPoly} {n : ℕ} (hdeg : f.natDegree = n)
    (hc : f.coeff 0 = 1) (hgc : g.coeff 0 = 1) (hd : 0 < g.natDegree)
    (hrel : AdjoinRoot.root f ^ n = AdjoinRoot.mk f g) :
    (exponentPairs n g.natDegree).card ≤ orderOf (AdjoinRoot.root f) := by
  classical
  have hg0 : g ≠ 0 := by intro h; simp [h] at hd
  let r := AdjoinRoot.root f
  let index (z : ℕ × ℕ) := z.1 + n * z.2
  let poly (z : ℕ × ℕ) : BinaryPoly := X ^ z.1 * g ^ z.2
  have hrep (z : ℕ × ℕ) : AdjoinRoot.mk f (poly z) = r ^ index z := by
    simp only [poly, index, map_mul, map_pow, AdjoinRoot.mk_X, ← hrel, pow_mul, pow_add, r]
  have htop (z : ℕ × ℕ) : (poly z).natDegree = z.1 + g.natDegree * z.2 := by
    dsimp only [poly]
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hg0), natDegree_X_pow,
      natDegree_pow, Nat.mul_comm]
  have hlow (z : ℕ × ℕ) : (poly z).natTrailingDegree = z.1 := by
    have hval : g.eval 0 = 1 := g.coeff_zero_eq_eval_zero ▸ hgc
    have hzero : (g ^ z.2).natTrailingDegree = 0 :=
      natTrailingDegree_eq_zero.2 (.inr (by simp [coeff_zero_eq_eval_zero, hval]))
    simp [poly, natTrailingDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hg0), hzero]
  have hlt (i : exponentPairs n g.natDegree) : (poly i.val).natDegree < f.natDegree := by
    rw [htop, hdeg]
    exact (Finset.mem_filter.mp i.property).2
  rw [← Fintype.card_coe]
  apply order_ge_of_representatives hc (fun i => poly i.val) (fun i => index i.val) _ hlt
    (fun i => hrep i.val)
  · intro i j heq
    have hi := congrArg natTrailingDegree heq
    have hj := congrArg natDegree heq
    rw [hlow, hlow] at hi
    rw [htop, htop, hi] at hj
    exact Subtype.ext (Prod.ext hi (Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel hj)))

theorem product_tail_degree {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    (((X : BinaryPoly) ^ u + 1) * (X ^ v + 1)).natDegree = u + v := by
  have leftdeg (k : ℕ) (hk : 0 < k) : ((X : BinaryPoly) ^ k + 1).natDegree = k := by
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
    simpa using hk
  rw [natDegree_mul (fun he => hu.ne (by simpa [he] using leftdeg u hu))
    (fun he => hv.ne (by simpa [he] using leftdeg v hv)), leftdeg u hu, leftdeg v hv]

theorem product_order_bound {n u v : ℕ} (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v)
    (htop : u + v < n) :
    (exponentPairs n (u + v)).card ≤ orderOf (AdjoinRoot.root (productCandidate n u v)) := by
  let f := productCandidate n u v
  let g : BinaryPoly := (X ^ u + 1) * (X ^ v + 1)
  have hd : g.natDegree = u + v := product_tail_degree hu hv
  have hg : g.coeff 0 = 1 := by simp [g, coeff_X_pow, hu.ne, hv.ne]
  have hn : 0 < n := by omega
  have hf : f.coeff 0 = 1 := by
    change ((X : BinaryPoly) ^ n + g).coeff 0 = 1
    simp [hg, coeff_X_pow, hn.ne]
  rw [← hd]
  apply order_ge_exponentPairs (product_shape hu hv huv htop).1 hf hg (by omega)
  apply sub_eq_zero.1
  have he := AdjoinRoot.mk_self (f := f)
  change AdjoinRoot.mk f (X ^ n + g) = 0 at he
  have he' : AdjoinRoot.mk f (X ^ n - g) = 0 := by
    rwa [sub_eq_add_neg, CharTwo.neg_eq]
  simpa only [map_sub, map_pow, AdjoinRoot.mk_X] using he'

theorem product_order_quadratic {n u v : ℕ} (hu : 0 < u) (hv : 0 < v) (huv : u ≠ v)
    (htop : u + v < n) :
    n ^ 2 ≤ 2 * (u + v) * orderOf (AdjoinRoot.root (productCandidate n u v)) :=
  (exponentPairs_quadratic n (u + v) (by omega)).trans
    (Nat.mul_le_mul_left _ (product_order_bound hu hv huv htop))

end GF2Sparse
