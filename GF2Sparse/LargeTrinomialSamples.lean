import GF2Sparse.TrinomialPowers
import GF2Sparse.PackedMersenne44497

/-! Five-term power images of large primitive trinomials. -/

namespace GF2Sparse.LargeTrinomialSamples
open Polynomial TrinomialPowers

/-- If the tap of an odd-degree primitive trinomial is a multiple of
`2^k+1`, sampling gives the displayed polynomial. -/
theorem primitive_sample_at_origin {n s v u k : ℕ} (hn : Odd n)
    (hu : 0 < u) (hsn : s < n) (hs : (2^k+1)*u = s) (hv : 2^k*u = v)
    (h : Primitive (trinomial n s)) :
    Primitive ((X : BinaryPoly)^n + (X^s + X^v + X^u + 1)) := by
  subst s
  subst v
  have source : Primitive (blockEndpoints n 0 u (2^k+1)) := by
    simpa only [blockEndpoints, trinomial, pow_zero, one_mul] using h
  have hodd : Odd (max n (0 + (2^k+1)*u)) := by
    simpa only [zero_add, max_eq_left hsn.le] using hn
  have image := primitive_binary_block (a := n) (t := 0) (u := u) (k := k) hu
    (by simpa only [zero_add] using hsn.ne') hodd source
  simpa only [binary_block_identity, pow_zero, one_mul] using image

/-- The seventeenth power of a primitive root of the Brent–Zimmermann
trinomial with tap 9999621 has the displayed five-term minimal polynomial. -/
theorem primitive_74207281_of_trinomial (h : Primitive (trinomial 74207281 9999621)) :
    Primitive ((X : BinaryPoly)^74207281 + (X^9999621 + X^9411408 + X^588213 + 1)) :=
  primitive_sample_at_origin (k := 4) ⟨37103640, by decide⟩ (by decide) (by decide)
    (by decide) (by decide) h

/-- The ninth power of a primitive root with degree 48617 and tap 4275. -/
theorem primitive_48617_of_trinomial (h : Primitive (trinomial 48617 4275)) :
    Primitive ((X : BinaryPoly)^48617 + (X^4275 + X^3800 + X^475 + 1)) :=
  primitive_sample_at_origin (k := 3) ⟨24308, by decide⟩ (by decide) (by decide)
    (by decide) (by decide) h

/-- Sampling a block whose two nonconstant trinomial exponents differ by
a multiple of the sampling power. -/
theorem primitive_sample_at_shift {n t u v w k : ℕ} (ht : 0 < t) (hu : 0 < u)
    (hn : Odd n) (hd : t+(2^k+1)*u = n) (hw : t+2^k*u = w) (hv : t+u = v)
    (h : Primitive (trinomial n t)) :
    Primitive ((X : BinaryPoly)^n + (X^w + X^v + X^t + 1)) := by
  subst n
  subst w
  subst v
  have join (a b : ℕ) : (X : BinaryPoly)^a * X^b = X^(a+b) := (pow_add X a b).symm
  have source : blockEndpoints 0 t u (2^k+1) = trinomial (t+(2^k+1)*u) t := by
    simp only [blockEndpoints, trinomial, pow_zero, mul_add, mul_one, join]
    ac_rfl
  have image := primitive_binary_block (a := 0) (t := t) (u := u) (k := k) hu
    (by omega) (by simpa using hn) (source.symm ▸ h)
  simp only [binary_block_identity, pow_zero, mul_add, mul_one, join] at image
  convert image using 1
  ac_rfl

/-- Cubing the root of the kernel-certified degree-44,497 trinomial. -/
theorem primitive_44497_cube :
    Primitive ((X : BinaryPoly)^44497 + (X^32523 + X^20549 + X^8575 + 1)) :=
  primitive_sample_at_shift (t := 8575) (u := 11974) (k := 1)
    (by decide) (by decide) ⟨22248, by decide⟩ (by decide) (by decide) (by decide)
    primitiveTrinomial_44497_8575

end GF2Sparse.LargeTrinomialSamples
