import GF2Sparse.TrinomialPowers

/-! A degree-74,207,281 pentanomial from a published primitive trinomial. -/

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

end GF2Sparse.LargeTrinomialSamples
