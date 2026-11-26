import GF2Sparse.Certificate
import GF2Sparse.OrderBound
import Mathlib.Tactic.NormNum.Prime

/-! A primitive-root criterion using translates of powers and a seven-term quotient. -/

namespace GF2Sparse.TrinomialMultiples

open Polynomial

def PowerOrZero {R : Type*} [MonoidWithZero R] (r x : R) : Prop :=
  x = 0 ∨ ∃ i : ℕ, x = r^i

private theorem add_closed {R : Type*} [CommRing R] {r x y : R}
    (ht : ∀ i : ℕ, PowerOrZero r (1 + r^i))
    (hx : PowerOrZero r x) (hy : PowerOrZero r y) : PowerOrZero r (x+y) := by
  have step (a b : ℕ) : PowerOrZero r (r^a + r^(a+b)) := by
    rw [pow_add, ← mul_one_add]
    rcases ht b with hz | ⟨j,hj⟩
    · exact Or.inl (by rw [hz, mul_zero])
    · exact Or.inr ⟨a+j, by rw [hj, pow_add]⟩
  rcases hx with rfl | ⟨i,rfl⟩
  · simpa using hy
  rcases hy with rfl | ⟨j,rfl⟩
  · rw [add_zero]
    exact Or.inr ⟨i,rfl⟩
  rcases le_total i j with h | h
  · obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le h
    exact step i b
  · obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le h
    simpa only [add_comm (r^(j+b))] using step j b

private theorem all_residues {f : BinaryPoly}
    (ht : ∀ i : ℕ, PowerOrZero (AdjoinRoot.root f) (1 + AdjoinRoot.root f^i)) :
    ∀ x : AdjoinRoot f, PowerOrZero (AdjoinRoot.root f) x := by
  intro x
  obtain ⟨p,rfl⟩ := AdjoinRoot.mk_surjective x
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact add_closed ht hp hq
  | monomial i c =>
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr ⟨i, by simp [← C_mul_X_pow_eq_monomial]⟩

/-- For a constant-one binary modulus, closure of the powers and zero under
translation by one characterizes primitivity, including irreducibility. -/
theorem primitive_iff_translate {f : BinaryPoly} (hf : f.Monic) (hn : 0 < f.natDegree)
    (hconst : f.coeff 0 = 1) :
    Primitive f ↔ ∀ a : ℕ, a < orderOf (AdjoinRoot.root f) →
      PowerOrZero (AdjoinRoot.root f) (1 + AdjoinRoot.root f^a) := by
  classical
  let R := AdjoinRoot f
  let r := AdjoinRoot.root f
  let eqv := (AdjoinRoot.powerBasisAux hf.ne_zero).equivFun.toEquiv
  letI : Fintype R := Fintype.ofEquiv _ eqv.symm
  have hc : Fintype.card R = 2^f.natDegree := card_adjoinRoot hf.ne_zero
  letI : Nontrivial R := Fintype.one_lt_card_iff_nontrivial.mp (hc ▸ Nat.one_lt_two_pow hn.ne')
  have hr : IsUnit r := root_unit hconst
  have hpos := hr.isOfFinOrder.orderOf_pos
  let powers (i : Fin (orderOf r)) : {y : R // y ≠ 0} :=
    ⟨r^(i : ℕ), (hr.pow _).ne_zero⟩
  have hinj : Function.Injective powers := fun i j h =>
    Fin.ext (pow_injOn_Iio_orderOf i.isLt j.isLt (congrArg Subtype.val h))
  have hcard : Fintype.card {y : R // y ≠ 0} = 2^f.natDegree-1 := by
    rw [Fintype.card_subtype_compl]
    simp [hc]
  constructor
  · intro hp a _
    change PowerOrZero r (1+r^a)
    by_cases hz : 1+r^a = 0
    · exact Or.inl hz
    have hsurj := ((Fintype.bijective_iff_injective_and_card powers).2
      ⟨hinj, by simpa only [Fintype.card_fin, hcard] using hp.2.2⟩).2
    obtain ⟨i,hi⟩ := hsurj ⟨1+r^a,hz⟩
    exact Or.inr ⟨i, (congrArg Subtype.val hi).symm⟩
  · intro ht
    have hall := all_residues (f := f) (fun i => by
      change PowerOrZero r (1+r^i)
      rw [← pow_mod_orderOf r i]
      exact ht _ (Nat.mod_lt _ hpos))
    have hs : Function.Surjective powers := by
      intro y
      obtain ⟨i,hi⟩ := (hall y.val).resolve_left y.property
      exact ⟨⟨i % orderOf r, Nat.mod_lt _ hpos⟩, Subtype.ext ((pow_mod_orderOf r i).trans hi.symm)⟩
    apply primitive_of_order hf hn
    simpa only [Fintype.card_fin, hcard] using
      (Fintype.bijective_iff_injective_and_card powers).1 ⟨hinj,hs⟩ |>.2

/-- An extremal primitive factor in the census with quotient weight seven. -/
theorem degree_thirteen :
    Primitive (decode 10265) ∧ (decode 5465).support.card = 7 ∧
      (decode 10265) * (decode 5465) = decode (2^25 + 2^9 + 1) := by
  refine ⟨(check_sound (n := 13) (factors := [8191]) ?_ (by decide +kernel)).2.2, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    norm_num
  · rw [support_decode]
    decide +kernel
  · rw [← decode_maskProduct]
    exact congrArg decode (by decide +kernel)

end GF2Sparse.TrinomialMultiples
