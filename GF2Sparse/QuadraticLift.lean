import GF2Sparse.CompositionNorm
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.RingTheory.Trace.Basic

/-! The trace and multiplicative order of the roots of H(X² + X). -/

namespace GF2Sparse

open Polynomial

noncomputable def quadraticLift (H : BinaryPoly) : BinaryPoly := H.comp (X ^ 2 + X)

private theorem degree_inner : (X ^ 2 + X : BinaryPoly).natDegree = 2 := by
  rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
  simp

@[simp] theorem natDegree_quadraticLift (H : BinaryPoly) :
    (quadraticLift H).natDegree = H.natDegree * 2 := by
  rw [quadraticLift, natDegree_comp, degree_inner]

/-- Sum of the binary Frobenius conjugates of a root of an irreducible
polynomial, transported to any commutative algebra containing that root. -/
theorem sum_frobenius_root {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    {H : BinaryPoly} (hH : Irreducible H) {β : A} (hz : aeval β H = 0) :
    ∑ i ∈ Finset.range H.natDegree, β ^ (2 ^ i) = algebraMap (ZMod 2) A H.nextCoeff := by
  let K := AdjoinRoot H
  letI : Fact (Irreducible H) := ⟨hH⟩
  let e := (AdjoinRoot.powerBasisAux hH.ne_zero).equivFun.toEquiv
  letI : Fintype K := Fintype.ofEquiv _ e.symm
  let pb := AdjoinRoot.powerBasis hH.ne_zero
  have htrace : Algebra.trace (ZMod 2) K (AdjoinRoot.root H) = H.nextCoeff := by
    change Algebra.trace (ZMod 2) K pb.gen = _
    rw [pb.trace_gen_eq_nextCoeff_minpoly, AdjoinRoot.minpoly_powerBasis_gen_of_monic
      (binary_monic hH.ne_zero), CharTwo.neg_eq]
  have hsum := FiniteField.algebraMap_trace_eq_sum_pow (ZMod 2) K (AdjoinRoot.root H)
  have hdim : Module.finrank (ZMod 2) K = H.natDegree := pb.finrank
  rw [htrace, hdim, Nat.card_zmod] at hsum
  let φ := AdjoinRoot.liftAlgHom H (Algebra.ofId _ _) β hz
  have he := (congrArg φ hsum.symm).trans (φ.commutes H.nextCoeff)
  simpa only [map_sum, map_pow, φ, AdjoinRoot.liftAlgHom_root] using he

private theorem artinSchreier_sum {A : Type*} [CommRing A] [CharP A 2] (x : A) (m : ℕ) :
    ∑ i ∈ Finset.range m, (x ^ 2 + x) ^ (2 ^ i) = x ^ (2 ^ m) + x := by
  induction m with
  | zero => simp [CharTwo.add_self_eq_zero]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, add_pow_expChar_pow, ← pow_mul, pow_succ']
    calc
      _ = (x ^ (2 ^ m) + x ^ (2 ^ m)) + (x ^ (2 * 2 ^ m) + x) := by ac_rfl
      _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

private theorem eval_outer_at_root {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    {H : BinaryPoly} {x : A} (hx : aeval x (quadraticLift H) = 0) :
    aeval (x ^ 2 + x) H = 0 := by
  simpa only [quadraticLift, aeval_comp, map_add, map_pow, aeval_X] using hx

/-- Over any algebra containing a root x of the lift, its outer-degree
Frobenius translates x by the trace of x² + x. -/
theorem quadraticLift_frobenius {A : Type*} [CommRing A] [CharP A 2] [Algebra (ZMod 2) A]
    {H : BinaryPoly} (hH : Irreducible H) {x : A} (hx : aeval x (quadraticLift H) = 0) :
    x ^ (2 ^ H.natDegree) = x + algebraMap (ZMod 2) A H.nextCoeff := by
  have he := sum_frobenius_root hH (eval_outer_at_root hx)
  rw [artinSchreier_sum] at he
  rw [← he, add_comm (x ^ (2 ^ H.natDegree)) x, CharTwo.add_cancel_left]

/-- The quadratic Artin–Schreier lift of an irreducible binary polynomial
is irreducible exactly when its next-to-leading coefficient is one. -/
theorem irreducible_quadraticLift_iff {H : BinaryPoly} (hH : Irreducible H) :
    Irreducible (quadraticLift H) ↔ H.nextCoeff = 1 := by
  let f := quadraticLift H
  let m := H.natDegree
  have hm : 0 < m := hH.natDegree_pos
  have hn : f.natDegree = m * 2 := natDegree_quadraticLift H
  have hpos : 0 < f.natDegree := hn ▸ Nat.mul_pos hm (by decide)
  constructor
  · intro hi
    letI : Fact (Irreducible f) := ⟨hi⟩
    letI : CharP (AdjoinRoot f) 2 := charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
    let x := AdjoinRoot.root f
    have hx : aeval x f = 0 := (AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self
    have he := quadraticLift_frobenius hH hx
    have choices : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    refine (choices _).resolve_left (fun h0 => ?_)
    rw [h0, map_zero, add_zero] at he
    have hd : f.natDegree ∣ m := (degree_dvd_iff_frobenius hi hx m).2 he
    have hle := Nat.le_of_dvd hm hd
    omega
  · intro h1
    have hf : f.Monic := binary_monic (fun he => by simp [he] at hpos)
    obtain ⟨p, hp, hd⟩ := WfDvdMonoid.exists_irreducible_factor (not_isUnit_of_natDegree_pos f hpos)
      hf.ne_zero
    letI : Fact (Irreducible p) := ⟨hp⟩
    letI : CharP (AdjoinRoot p) 2 := charP_of_injective_ringHom (AdjoinRoot.of p).injective 2
    let x := AdjoinRoot.root p
    have hx : aeval x p = 0 := (AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self
    have hxf : aeval x f = 0 := (AdjoinRoot.aeval_eq _).trans (AdjoinRoot.mk_eq_zero.2 hd)
    have he := quadraticLift_frobenius hH hxf
    rw [h1, map_one] at he
    obtain ⟨k, hk⟩ := outer_degree_dvd_factor hH hp hd
    have hne : p.natDegree ≠ m := by
      intro hpm
      have hfix := (degree_dvd_iff_frobenius hp hx m).1 (hpm ▸ dvd_rfl)
      exact one_ne_zero (add_left_cancel (he.symm.trans (hfix.trans (add_zero x).symm)))
    have hk2 : 2 ≤ k := by
      have hpp := hp.natDegree_pos
      by_contra! hsmall
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> simp_all [m]
    have heq : f = p := eq_of_monic_of_dvd_of_natDegree_le (binary_monic hp.ne_zero) hf hd
      (by rw [hn, hk]; exact Nat.mul_le_mul_left m hk2)
    change Irreducible f
    rwa [heq]

private theorem lift_size (H : BinaryPoly) :
    2 ^ (quadraticLift H).natDegree - 1 = (2 ^ H.natDegree - 1) * (2 ^ H.natDegree + 1) := by
  rw [natDegree_quadraticLift, pow_mul, sq, Nat.sub_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
  omega

private theorem orderOf_lift_norm {H : BinaryPoly} (hH : Irreducible H) (ht : H.nextCoeff = 1) :
    orderOf (AdjoinRoot.root (quadraticLift H) ^ (2 ^ H.natDegree + 1)) =
      orderOf (AdjoinRoot.root H) := by
  let f := quadraticLift H
  letI : Fact (Irreducible f) := ⟨(irreducible_quadraticLift_iff hH).2 ht⟩
  letI : CharP (AdjoinRoot f) 2 := charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  let x := AdjoinRoot.root f
  have hx : aeval x f = 0 := (AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self
  have hq := quadraticLift_frobenius hH hx
  rw [ht, map_one] at hq
  have he : x ^ (2 ^ H.natDegree + 1) = x ^ 2 + x := by rw [pow_succ, hq, add_mul, one_mul, sq]
  exact (congrArg orderOf he).trans (orderOf_root_at hH (eval_outer_at_root hx))

/-- For an irreducible outer polynomial, primitivity of the lift requires
a primitive outer root, trace one, and full order in the group of order q+1. -/
theorem primitive_quadraticLift_iff {H : BinaryPoly} (hH : Irreducible H) :
    let q := 2 ^ H.natDegree
    let x := AdjoinRoot.root (quadraticLift H)
    Primitive (quadraticLift H) ↔ Primitive H ∧ H.nextCoeff = 1 ∧ orderOf (x ^ (q - 1)) = q + 1 := by
  let f := quadraticLift H
  let x := AdjoinRoot.root f
  let R := 2 ^ H.natDegree - 1
  let S := 2 ^ H.natDegree + 1
  have hR : 0 < R := Nat.sub_pos_of_lt (Nat.one_lt_two_pow hH.natDegree_pos.ne')
  have hS : 0 < S := Nat.succ_pos _
  have hsize : 2 ^ f.natDegree - 1 = R * S := lift_size H
  change Primitive f ↔ Primitive H ∧ H.nextCoeff = 1 ∧ orderOf (x ^ R) = S
  constructor
  · intro hf
    have ht := (irreducible_quadraticLift_iff hH).1 hf.2.1
    have ho : orderOf x = R * S := hf.2.2.trans hsize
    have hnum : orderOf (x ^ S) = R := by
      rw [orderOf_pow_of_dvd hS.ne' (ho ▸ dvd_mul_left S R), ho, Nat.mul_div_cancel _ hS]
    refine ⟨⟨binary_monic hH.ne_zero, hH, (orderOf_lift_norm hH ht).symm.trans hnum⟩, ht, ?_⟩
    rw [orderOf_pow_of_dvd hR.ne' (ho ▸ dvd_mul_right R S), ho, Nat.mul_div_cancel_left _ hR]
  · rintro ⟨hp, ht, hy⟩
    have hnorm : orderOf (x ^ S) = R := (orderOf_lift_norm hH ht).trans hp.2.2
    have hd : R ∣ orderOf x := hnorm ▸ orderOf_pow_dvd (x := x) S
    have hdiv := (orderOf_pow_of_dvd (x := x) hR.ne' hd).symm.trans hy
    have hi := (irreducible_quadraticLift_iff hH).2 ht
    refine ⟨binary_monic hi.ne_zero, hi, ?_⟩
    change orderOf x = 2 ^ f.natDegree - 1
    rw [hsize, ← hdiv, Nat.mul_div_cancel' hd]

/-- When q+1 is prime, the trace-one condition alone lifts a primitive
outer polynomial to a primitive polynomial of twice the degree. -/
theorem primitive_quadraticLift_iff_of_prime {H : BinaryPoly} (hH : Primitive H)
    (hp : Nat.Prime (2 ^ H.natDegree + 1)) :
    Primitive (quadraticLift H) ↔ H.nextCoeff = 1 := by
  refine ⟨fun hf => (irreducible_quadraticLift_iff hH.2.1).1 hf.2.1, fun ht => ?_⟩
  apply (primitive_quadraticLift_iff hH.2.1).2
  refine ⟨hH, ht, ?_⟩
  let f := quadraticLift H
  letI : Fact (Irreducible f) := ⟨(irreducible_quadraticLift_iff hH.2.1).2 ht⟩
  letI : CharP (AdjoinRoot f) 2 := charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  let x := AdjoinRoot.root f
  let q := 2 ^ H.natDegree
  have hx : aeval x f = 0 := (AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self
  have hrel : x ^ q = x + 1 := by simpa only [ht, map_one] using quadraticLift_frobenius hH.2.1 hx
  have ho : orderOf (x ^ (q + 1)) = q - 1 := (orderOf_lift_norm hH.2.1 ht).trans hH.2.2
  have hy : (x ^ (q - 1)) ^ (q + 1) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, ← ho, pow_orderOf_eq_one]
  refine ((Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hy)).resolve_left (fun he => ?_)
  have hfix : x ^ q = x := by
    calc
      x ^ q = x ^ ((q - 1) + 1) := by rw [Nat.sub_add_cancel (Nat.two_pow_pos _)]
      _ = x := by rw [pow_succ, orderOf_eq_one_iff.1 he, one_mul]
  exact one_ne_zero (add_left_cancel (hrel.symm.trans (hfix.trans (add_zero x).symm)))

end GF2Sparse
