import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.GroupTheory.OrderOfElement

/-! Binary primitive polynomials and the exact-order test in the quotient ring. -/

namespace GF2Sparse

open Polynomial

abbrev BinaryPoly := Polynomial (ZMod 2)

/-- The residue of X generates the multiplicative group of the residue field. -/
def Primitive (f : BinaryPoly) : Prop :=
  f.Monic ∧ Irreducible f ∧ orderOf (AdjoinRoot.root f) = 2 ^ f.natDegree - 1

def HasSparsePrimitive (n : ℕ) : Prop :=
  ∃ f : BinaryPoly, f.natDegree = n ∧ f.support.card ≤ 5 ∧ Primitive f

/-- The all-degree statement being investigated. -/
def Conjecture : Prop := ∀ n : ℕ, 0 < n → HasSparsePrimitive n

theorem card_adjoinRoot {f : BinaryPoly} (hf : f ≠ 0) [Fintype (AdjoinRoot f)] :
    Fintype.card (AdjoinRoot f) = 2 ^ f.natDegree := by
  let e := (AdjoinRoot.powerBasisAux hf).equivFun.toEquiv
  simpa using Fintype.card_congr e

/-- In a degree-n quotient, an element of order 2^n - 1 accounts for every
nonzero residue. Thus the order test itself also proves irreducibility. -/
theorem primitive_of_order {f : BinaryPoly} (hf : f.Monic) (hn : 0 < f.natDegree)
    (ho : orderOf (AdjoinRoot.root f) = 2 ^ f.natDegree - 1) : Primitive f := by
  classical
  let R := AdjoinRoot f
  let r := AdjoinRoot.root f
  let e := (AdjoinRoot.powerBasisAux hf.ne_zero).equivFun.toEquiv
  letI : Fintype R := Fintype.ofEquiv _ e.symm
  have hc : Fintype.card R = 2 ^ f.natDegree := card_adjoinRoot hf.ne_zero
  have hsize := Nat.one_lt_two_pow hn.ne'
  letI : Nontrivial R := Fintype.one_lt_card_iff_nontrivial.mp (hc ▸ hsize)
  have hr : IsUnit r := IsUnit.of_pow_eq_one (pow_orderOf_eq_one r) (by
    change orderOf (AdjoinRoot.root f) ≠ 0
    rw [ho]
    omega)
  let powers (i : Fin (orderOf r)) : {y : R // y ≠ 0} :=
    ⟨r ^ (i : ℕ), (hr.pow _).ne_zero⟩
  have hinj : Function.Injective powers := fun i j h =>
    Fin.ext (pow_injOn_Iio_orderOf i.isLt j.isLt (congrArg Subtype.val h))
  have hcard : Fintype.card (Fin (orderOf r)) = Fintype.card {y : R // y ≠ 0} := by
    rw [Fintype.card_subtype_compl]
    simp [r, ho, hc]
  have hsurj := ((Fintype.bijective_iff_injective_and_card powers).2 ⟨hinj, hcard⟩).2
  have hfield : IsField R := by
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
    intro y hy
    obtain ⟨i, hi⟩ := hsurj ⟨y, hy⟩
    have heq : r ^ (i : ℕ) = y := congrArg Subtype.val hi
    exact heq ▸ (hr.pow (i : ℕ)).exists_right_inv
  have hmax := (Ideal.Quotient.maximal_ideal_iff_isField_quotient
    (Ideal.span ({f} : Set BinaryPoly))).2 hfield
  exact ⟨hf, ((Ideal.span_singleton_prime hf.ne_zero).1 hmax.isPrime).irreducible, ho⟩

theorem primitive_of_prime_checks {f : BinaryPoly} (hf : f.Monic) (hn : 0 < f.natDegree)
    (hfull : AdjoinRoot.root f ^ (2 ^ f.natDegree - 1) = 1)
    (hproper : ∀ p : ℕ, p.Prime → p ∣ 2 ^ f.natDegree - 1 →
      AdjoinRoot.root f ^ ((2 ^ f.natDegree - 1) / p) ≠ 1) : Primitive f :=
  primitive_of_order hf hn (orderOf_eq_of_pow_and_pow_div_prime
    (Nat.sub_pos_of_lt (Nat.one_lt_two_pow hn.ne')) hfull hproper)

end GF2Sparse
