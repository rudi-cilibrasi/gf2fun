import GF2Sparse.Table
import Mathlib.NumberTheory.LucasLehmer

/-! Full-order certificates when the multiplicative group has prime size. -/

namespace GF2Sparse

open Polynomial

/-- For a prime Mersenne group size, the full exponent check suffices
as soon as the modulus has degree greater than one. -/
theorem primitive_product_of_mersenne_blocks {n u v bits : ℕ} (hn : 1 < n)
    (hdeg : (productMask n u v).log2 = n) (hp : (mersenne n).Prime) (blocks : List ℕ)
    (hc : powerBlocks n (productMask n u v) bits (mersenne n) 1 blocks = true) :
    Primitive (productCandidate n u v) := by
  let mask := productMask n u v
  let f := decode mask
  have hf0 : mask ≠ 0 := by
    intro he
    change mask.log2 = n at hdeg
    rw [he] at hdeg
    simp at hdeg
    omega
  have hd : f.natDegree = n := (natDegree_decode mask).trans hdeg
  have hpow := root_pow_one_of_blocks n mask bits (mersenne n) blocks hc
  have hroot : AdjoinRoot.root f ≠ 1 := by
    intro hr
    have hdiv : f ∣ (X-1 : BinaryPoly) := AdjoinRoot.mk_eq_zero.1 (by simp [AdjoinRoot.mk_X, hr])
    have hle := natDegree_le_of_dvd hdiv (X_sub_C_ne_zero (1 : ZMod 2))
    change f.natDegree ≤ (X - C (1 : ZMod 2)).natDegree at hle
    rw [natDegree_X_sub_C, hd] at hle
    omega
  have horder := (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hpow)
  rw [← decode_productMask]
  change Primitive f
  apply primitive_of_order (monic_decode hf0) (hd ▸ by omega)
  rw [hd]
  exact horder.resolve_left (fun h => hroot (orderOf_eq_one_iff.1 h))

end GF2Sparse
