import GF2Sparse.Dilation

/-! Exact reduction of root orders under irreducible dilation. -/

namespace GF2Sparse

open Polynomial

/-- If f(X^d) is irreducible, its root order is d times that of f.
This removes the common divisor of the exponents before applying an order bound. -/
theorem root_order_irreducible_dilation {f : BinaryPoly} (hf : Irreducible f)
    {d : ℕ} (hd : 0 < d) (hi : Irreducible (expand (ZMod 2) d f)) :
    orderOf (AdjoinRoot.root (expand (ZMod 2) d f)) = d * orderOf (AdjoinRoot.root f) := by
  letI : Fact (Irreducible f) := ⟨hf⟩
  letI : Fact (Irreducible (expand (ZMod 2) d f)) := ⟨hi⟩
  let y := AdjoinRoot.root (expand (ZMod 2) d f)
  have hroot : aeval (y ^ d) f = 0 := by
    rw [← expand_aeval, AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_self
  let φ := AdjoinRoot.liftAlgHom f (Algebra.ofId _ _) (y ^ d) hroot
  have horder : orderOf (y ^ d) = orderOf (AdjoinRoot.root f) := by
    simpa [φ, AdjoinRoot.liftAlgHom_root] using
      orderOf_injective φ.toMonoidHom φ.injective (AdjoinRoot.root f)
  let R := orderOf y
  let g := R.gcd d
  have hleft : g ∣ R := Nat.gcd_dvd_left _ _
  have hright : g ∣ d := Nat.gcd_dvd_right _ _
  have hg : 0 < g := (Nat.gcd_ne_zero_right hd.ne').bot_lt
  have hbase : R / g = orderOf (AdjoinRoot.root f) := (orderOf_pow' y hd.ne').symm.trans horder
  have hcop : (R / g).Coprime (d / g) := Nat.coprime_div_gcd_div_gcd hg
  have hone : d / g = 1 := by
    by_contra hn
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn
    have hpr : p ∣ R / g := hbase ▸ prime_dvd_root_order_of_irreducible_expand hf hd hp
      (hpd.trans (Nat.div_dvd_of_dvd hright)) hi
    have h := Nat.dvd_gcd hpr hpd
    rw [hcop.gcd_eq_one] at h
    exact hp.not_dvd_one h
  have heq : g = d := by simpa only [hone, one_mul] using Nat.div_mul_cancel hright
  change R = _
  calc R = R / g * g := (Nat.div_mul_cancel hleft).symm
       _ = d * orderOf (AdjoinRoot.root f) := by rw [hbase, heq, Nat.mul_comm]

end GF2Sparse
