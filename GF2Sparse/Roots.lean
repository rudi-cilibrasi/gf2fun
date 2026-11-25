import GF2Sparse.Basic
import Mathlib.FieldTheory.Finite.Extension

/-! Transport the primitive-root test to any binary extension field. -/

namespace GF2Sparse

open Polynomial

theorem binary_monic {f : BinaryPoly} (hf : f ≠ 0) : f.Monic := by
  have choices : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  exact (choices f.leadingCoeff).resolve_left (leadingCoeff_ne_zero.mpr hf)

variable {K : Type*} [Field K] [Algebra (ZMod 2) K]

theorem orderOf_root_at {f : BinaryPoly} (hf : Irreducible f) {z : K}
    (hz : aeval z f = 0) : orderOf z = orderOf (AdjoinRoot.root f) := by
  letI : Fact (Irreducible f) := ⟨hf⟩
  let φ := AdjoinRoot.liftAlgHom f (Algebra.ofId _ _) z hz
  simpa [φ, AdjoinRoot.liftAlgHom_root] using
    orderOf_injective φ.toMonoidHom φ.injective (AdjoinRoot.root f)

private theorem frobenius_degree {f : BinaryPoly} (hf : Irreducible f) {z : K}
    (hz : aeval z f = 0) : z ^ (2 ^ f.natDegree) = z := by
  letI : Fact (Irreducible f) := ⟨hf⟩
  let e := (AdjoinRoot.powerBasisAux hf.ne_zero).equivFun.toEquiv
  letI : Fintype (AdjoinRoot f) := Fintype.ofEquiv _ e.symm
  let φ := AdjoinRoot.liftAlgHom f (Algebra.ofId _ _) z hz
  have he := FiniteField.pow_card (AdjoinRoot.root f)
  rw [card_adjoinRoot hf.ne_zero] at he
  simpa [φ, AdjoinRoot.liftAlgHom_root] using congrArg φ he

/-- The first binary Frobenius power fixing a root of an irreducible
polynomial is its degree. The statement works in any ambient field. -/
theorem degree_dvd_iff_frobenius {f : BinaryPoly} (hf : Irreducible f) {z : K}
    (hz : aeval z f = 0) (k : ℕ) : f.natDegree ∣ k ↔ z ^ (2 ^ k) = z := by
  constructor
  · rintro ⟨j, rfl⟩
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, frobenius_degree hf hz]
  · intro h
    letI : Fact (Irreducible f) := ⟨hf⟩
    let φ := AdjoinRoot.liftAlgHom f (Algebra.ofId _ _) z hz
    apply hf.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
    apply AdjoinRoot.mk_eq_zero.mp
    apply φ.injective
    simp [φ, h]

theorem order_le_of_aeval {z : K} (hz0 : z ≠ 0) {f : BinaryPoly} (hf : f ≠ 0)
    (hz : aeval z f = 0) : orderOf z ≤ 2 ^ f.natDegree - 1 := by
  have hi : IsIntegral (ZMod 2) z := ⟨f, binary_monic hf, hz⟩
  let p := minpoly (ZMod 2) z
  have hp : Irreducible p := minpoly.irreducible hi
  have hpow := frobenius_degree hp (minpoly.aeval (ZMod 2) z)
  have hpos := Nat.one_lt_two_pow hp.natDegree_pos.ne'
  have hpow' : z ^ (2 ^ p.natDegree - 1) = 1 := by
    apply mul_right_cancel₀ hz0
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 ^ p.natDegree), hpow]
  have hle := Nat.le_of_dvd (by omega : 0 < 2 ^ p.natDegree - 1)
    (orderOf_dvd_of_pow_eq_one hpow')
  exact hle.trans (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide)
    (natDegree_le_of_dvd (minpoly.dvd _ z hz) hf)) 1)

/-- A nonzero root of full multiplicative order cannot satisfy a polynomial
of degree below n. -/
theorem degree_le_of_full_order {n : ℕ} (hn : 0 < n) {z : K}
    (ho : orderOf z = 2 ^ n - 1) {f : BinaryPoly} (hf : f ≠ 0)
    (hz : aeval z f = 0) : n ≤ f.natDegree := by
  have hs := Nat.one_lt_two_pow hn.ne'
  have hz0 : z ≠ 0 := by rintro rfl; simp at ho; omega
  have hle := order_le_of_aeval hz0 hf hz
  rw [ho] at hle
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  omega

/-- A full-order root already proves that a monic degree-n polynomial is
its minimal polynomial and is primitive. -/
theorem primitive_of_root_order {f : BinaryPoly} (hf : f.Monic) (hn : 0 < f.natDegree)
    {z : K} (hz : aeval z f = 0) (ho : orderOf z = 2 ^ f.natDegree - 1) : Primitive f := by
  have hi : IsIntegral (ZMod 2) z := ⟨f, hf, hz⟩
  have heq := eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hi) hf (minpoly.dvd _ z hz)
    (degree_le_of_full_order hn ho (minpoly.ne_zero hi) (minpoly.aeval _ z))
  have hirr : Irreducible f := heq ▸ minpoly.irreducible hi
  exact ⟨hf, hirr, (orderOf_root_at hirr hz).symm.trans ho⟩

end GF2Sparse
