import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! Specialization of row determinants and the counting bound for exceptional residues. -/

namespace GF2Sparse

open Polynomial

/-- A common modular root makes the characteristic divide the integer resultant.
In the row calculation the first polynomial is cyclotomic. -/
theorem modulus_dvd_resultant_of_common_root (f g : ℤ[X]) (q : ℕ) (h : ZMod q)
    (hd : f.natDegree ≠ 0) (hf : eval₂ (Int.castRingHom (ZMod q)) h f = 0)
    (hg : eval₂ (Int.castRingHom (ZMod q)) h g = 0) :
    (q : ℤ) ∣ f.resultant g := by
  obtain ⟨a, b, _, _, hab⟩ :=
    exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl (Or.inl hd)
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  have he := congrArg (eval₂ (Int.castRingHom (ZMod q)) h) hab
  rw [eval₂_C] at he
  simpa [eval₂_add, eval₂_mul, hf, hg] using he.symm

/-- Sum the support counts after repeatedly removing a common prime from every tap. -/
theorem cumulative_residue_count (a : ℕ → ℕ) (b c r : ℕ) (base : a 0 ≤ b)
    (step : ∀ j, a (j+1) ≤ a j + c*(r+1)^j) (j : ℕ) :
    r*a j + c ≤ r*b + c*(r+1)^j := by
  induction j with
  | zero => simpa using Nat.add_le_add_right (Nat.mul_le_mul_left r base) c
  | succ j ih =>
    calc
      r*a (j+1) + c ≤ r*(a j + c*(r+1)^j) + c :=
        Nat.add_le_add_right (Nat.mul_le_mul_left r (step j)) c
      _ = (r*a j+c) + r*(c*(r+1)^j) := by ring
      _ ≤ (r*b + c*(r+1)^j) + r*(c*(r+1)^j) := Nat.add_le_add_right ih _
      _ = r*b + c*(r+1)^(j+1) := by rw [pow_succ]; ring

end GF2Sparse
