import GF2Sparse.LocalFactors
import GF2Sparse.Progressions
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! A common factor from the three interior exponents modulo the degree. -/

namespace GF2Sparse

open Polynomial

/-- An affine change of the three taps by a unit modulo n transports any
trinomial root of order dividing n into a root of the pentanomial. -/
theorem factor_of_affine_taps {n u t a b c j d : ℕ} {p : BinaryPoly}
    (hp : Irreducible p) (hdiv : p ∣ trinomial d j)
    (hord : AdjoinRoot.root p ^ n = 1) (hu : u.Coprime n)
    (ha : a ≡ t [MOD n]) (hb : b ≡ t + u*j [MOD n]) (hc : c ≡ t + u*d [MOD n]) :
    ∃ g : BinaryPoly, Irreducible g ∧ g.natDegree ≤ p.natDegree ∧
      g ∣ X^n + 1 + X^a + X^b + X^c := by
  letI : Fact (Irreducible p) := ⟨hp⟩
  letI : CharP (AdjoinRoot p) 2 := charP_of_injective_ringHom (AdjoinRoot.of p).injective 2
  let z := AdjoinRoot.root p
  obtain ⟨v, hv⟩ := exists_pow_eq_self_of_coprime
    (x := z) (hu.of_dvd_right (orderOf_dvd_of_pow_eq_one hord))
  let y := z^v
  have hyu : y^u = z := by
    change (z^v)^u = z
    rwa [← pow_mul, Nat.mul_comm, pow_mul]
  have hyn : y^n = 1 := by
    change (z^v)^n = 1
    rw [← pow_mul, Nat.mul_comm, pow_mul, show z^n = 1 from hord, one_pow]
  have hz : z^d + (z^j + 1) = 0 := by
    simpa only [trinomial, map_add, map_pow, AdjoinRoot.mk_X, map_one, z] using
      (AdjoinRoot.mk_eq_zero.mpr hdiv)
  have heval : aeval y (X^n + 1 + X^a + X^b + X^c : BinaryPoly) = 0 := by
    simp only [map_add, map_pow, aeval_X, map_one, hyn, pow_eq_pow_of_modEq ha hyn,
      pow_eq_pow_of_modEq hb hyn, pow_eq_pow_of_modEq hc hyn, pow_add, pow_mul, hyu]
    linear_combination (y^t) * hz + (CharTwo.add_self_eq_zero (1 : AdjoinRoot p))
  have hi : IsIntegral (ZMod 2) y := (AdjoinRoot.isIntegral_root hp.ne_zero).pow v
  have hd : (minpoly (ZMod 2) y).natDegree ∣ p.natDegree := by
    rw [← AdjoinRoot.powerBasis_dim hp.ne_zero, ← PowerBasis.finrank]
    exact minpoly.degree_dvd hi
  exact ⟨minpoly (ZMod 2) y, minpoly.irreducible hi, Nat.le_of_dvd hp.natDegree_pos hd,
    minpoly.dvd _ _ heval⟩

/-- On multiples of the small-field period, every compressed three-tap
shape of span d gives an irreducible factor of degree at most d. -/
theorem factor_of_bounded_affine_taps {n u t a b c j d : ℕ}
    (hj : 0 < j) (hjd : j < d) (hn : period d ∣ n) (hu : u.Coprime n)
    (ha : a ≡ t [MOD n]) (hb : b ≡ t + u*j [MOD n]) (hc : c ≡ t + u*d [MOD n]) :
    ∃ g : BinaryPoly, Irreducible g ∧ g.natDegree ≤ d ∧
      g ∣ X^n + 1 + X^a + X^b + X^c := by
  let f := trinomial d j
  have hdeg : f.natDegree = d := trinomial_degree hj hjd
  have hpos : 0 < f.natDegree := hdeg.symm ▸ hj.trans hjd
  have hf : f ≠ 0 := by intro h; simp [h] at hpos
  obtain ⟨p, hp, hpf⟩ := WfDvdMonoid.exists_irreducible_factor
    (not_isUnit_of_natDegree_pos f hpos) hf
  have hd : p.natDegree ≤ d := (natDegree_le_of_dvd hpf hf).trans_eq hdeg
  have hconst : f.coeff 0 = 1 := by
    simp [f, trinomial, coeff_X_pow, hj.ne, (hj.trans hjd).ne]
  have hper := root_pow_period hp hd (root_ne_zero_of_factor hp hpf hconst)
  obtain ⟨k, hk⟩ := hn
  have hord : AdjoinRoot.root p ^ n = 1 := by rw [hk, pow_mul, hper, one_pow]
  obtain ⟨g, hg, hgd, hgf⟩ := factor_of_affine_taps hp hpf hord hu ha hb hc
  exact ⟨g, hg, hgd.trans hd, hgf⟩

end GF2Sparse
