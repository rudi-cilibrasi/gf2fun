import GF2Sparse.OreReciprocal
import GF2Sparse.OrePrimitiveExamples

/-! Full-order trinomials obtained by lifting reciprocal seeds in degrees 9 and 10. -/

namespace GF2Sparse

open Polynomial

private theorem ore_trinomial (s a : ℕ) :
    oreLift (trinomial s a) = trinomial (2^s-1) (2^a-1) := by
  simp [trinomial]

private theorem reverse_trinomial {s a : ℕ} (ha : 0 < a) (ht : a < s) :
    (trinomial s a).reverse = trinomial s (s-a) := by
  have hx (k : ℕ) (hk : k ≤ s) : reflect s ((X : BinaryPoly)^k) = X^(s-k) := by
    simp [revAt_le hk]
  rw [Polynomial.reverse, trinomial_degree ha ht]
  simp only [trinomial, reflect_add, reflect_one, hx s le_rfl, hx a ht.le, Nat.sub_self, pow_zero]
  ac_rfl

/-- If lifting a trinomial gives a primitive polynomial, lifting its reciprocal does too. -/
theorem primitive_reciprocal_ore_trinomial {s a : ℕ} (ha : 0 < a) (ht : a < s)
    (hf : Primitive (trinomial (2^s-1) (2^a-1))) :
    Primitive (trinomial (2^s-1) (2^(s-a)-1)) := by
  rw [← ore_trinomial] at hf
  have hd : 0 < (trinomial s a).natDegree := (trinomial_degree ha ht).symm ▸ ha.trans ht
  have hc : (trinomial s a).coeff 0 = 1 := by simp [trinomial, coeff_X_pow, ha.ne, (ha.trans ht).ne]
  have hp := (irreducible_oreLift_iff hd hc).1 hf.2.1
  simpa only [reverse_trinomial ha ht, ore_trinomial] using hp.primitive_oreLift_reverse_iff.2 hf

theorem primitive_trinomial_511_31 : Primitive (trinomial 511 31) :=
  primitive_reciprocal_ore_trinomial (s := 9) (a := 4) (by decide) (by decide) Ore9.primitive_trinomial

theorem primitive_trinomial_1023_127 : Primitive (trinomial 1023 127) :=
  primitive_reciprocal_ore_trinomial (s := 10) (a := 3) (by decide) (by decide) Ore10.primitive_trinomial

end GF2Sparse
