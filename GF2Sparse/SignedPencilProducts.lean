import GF2Sparse.SubgroupCover
import Mathlib.GroupTheory.OrderOfElement

/-! Signed Frobenius shifts and one prime-component cancellation. -/

namespace GF2Sparse

/-- For an odd-order element, its powers and their negatives are disjoint
whenever the two signs are distinct in the exponent field. -/
theorem signed_powers_injective {F : Type*} [Field F] (a : F)
    (hodd : Odd (orderOf a)) (hsign : (1 : F) ≠ -1) :
    Function.Injective (fun t : Bool × Fin (orderOf a) =>
      if t.1 then -(a ^ t.2.val) else a ^ t.2.val) := by
  have full (j : ℕ) : (a^j)^(orderOf a) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have separate (j k : ℕ) : a^j ≠ -(a^k) := by
    intro equal
    have h := congrArg (fun v : F => v^(orderOf a)) equal
    exact hsign (by simpa only [full, hodd.neg_pow] using h)
  rintro ⟨s, i⟩ ⟨t, j⟩ h
  have same (hij : a^i.val = a^j.val) : i = j :=
    Fin.ext (pow_injOn_Iio_orderOf i.isLt j.isLt hij)
  cases s <;> cases t <;> simp only [Bool.false_eq_true, if_false, if_true,
    neg_inj, Prod.mk.injEq, true_and] at h ⊢
  · exact same h
  · exact (separate i j h).elim
  · exact (separate j i h.symm).elim
  · exact same h

/-- If at least one of two exponents is nonzero in a prime component,
two signed shifts cannot both cancel it. -/
theorem cancellation_determines_shift {F J : Type*} [Field F] {shifts : J → F}
    (hinj : Function.Injective shifts) {u v : F} (hn : u ≠ 0 ∨ v ≠ 0)
    {i j : J} (hi : u + v * shifts i = 0) (hj : u + v * shifts j = 0) : i = j := by
  have hv : v ≠ 0 := by
    intro zero
    exact (hn.resolve_right (by simpa using zero)) (by simpa [zero] using hi)
  apply hinj
  exact mul_left_cancel₀ hv (add_left_cancel (hi.trans hj.symm))

end GF2Sparse
