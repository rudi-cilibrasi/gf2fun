import GF2Sparse.TrinomialOrder
import GF2Sparse.AdditiveOrbit

/-! Multiplicative root tests under sampling in the same extension degree. -/

namespace GF2Sparse

open Polynomial

private abbrev C₂ := AlgebraicClosure (ZMod 2)

private theorem root_pow_of_dvd_expand {g f : BinaryPoly} {m : ℕ}
    (hd : g ∣ expand (ZMod 2) m f) {x : C₂} (hx : aeval x g = 0) :
    aeval (x^m) f = 0 := by
  obtain ⟨p, hp⟩ := hd
  rw [← expand_aeval, hp, map_mul, hx, zero_mul]

/-- If a power of a root has the full target degree, its source polynomial
of that same degree is irreducible. -/
theorem irreducible_of_dvd_expand_same_degree {g f : BinaryPoly} {m : ℕ}
    (hf : Irreducible f) (hg : g.natDegree = f.natDegree)
    (hd : g ∣ expand (ZMod 2) m f) : Irreducible g := by
  have hpos : 0 < g.natDegree := hg ▸ hf.natDegree_pos
  have hg0 : g ≠ 0 := fun he => by simp [he] at hpos
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero C₂ g ((natDegree_pos_iff_degree_pos).1 hpos).ne'
  let p := minpoly (ZMod 2) x
  have hp : Irreducible p := minpoly.irreducible (Algebra.IsIntegral.isIntegral x)
  have hfix := (degree_dvd_iff_frobenius hp (minpoly.aeval (ZMod 2) x) p.natDegree).1 dvd_rfl
  have hdiv := (degree_dvd_iff_frobenius hf (root_pow_of_dvd_expand hd hx) p.natDegree).2
    (by rw [pow_right_comm, hfix])
  have he : g = p := eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (Algebra.IsIntegral.isIntegral x)) (binary_monic hg0) (minpoly.dvd _ _ hx)
    (by rw [hg]; exact Nat.le_of_dvd hp.natDegree_pos hdiv)
  rwa [he]

/-- Coprime sampling in the same degree preserves product-one triples,
including triples with repetitions. -/
theorem no_root_triple_iff_of_coprime_sampling {g f : BinaryPoly} {m : ℕ}
    (hm : 0 < m) (hf : Irreducible f) (hg : g.natDegree = f.natDegree) (hd : g ∣ expand (ZMod 2) m f)
    (hc : (2^g.natDegree-1).Coprime m) : NoRootTriple f ↔ NoRootTriple g := by
  constructor
  · intro h x y z hx hy hz he
    apply h (x^m) (y^m) (z^m) (root_pow_of_dvd_expand hd hx)
      (root_pow_of_dvd_expand hd hy) (root_pow_of_dvd_expand hd hz)
    rw [← mul_pow, ← mul_pow, he, one_pow]
  · intro h x y z hx hy hz he
    have hgi := irreducible_of_dvd_expand_same_degree hf hg hd
    obtain ⟨r,hr⟩ := IsAlgClosed.exists_aeval_eq_zero C₂ g hgi.degree_pos.ne'
    have pre {t : C₂} (ht : aeval t f = 0) : ∃ w : C₂, aeval w g = 0 ∧ w^m = t := by
      obtain ⟨a,ha⟩ := exists_frobenius_root hf (root_pow_of_dvd_expand hd hr) ht
      exact ⟨r^(2^a), by rw [aeval_dyadic, hr, zero_pow (Nat.two_pow_pos _).ne'],
        (pow_right_comm r _ _).trans ha.symm⟩
    obtain ⟨u,hu,rfl⟩ := pre hx
    obtain ⟨v,hv,rfl⟩ := pre hy
    obtain ⟨w,hw,rfl⟩ := pre hz
    apply h u v w hu hv hw
    have fix {a : C₂} (ha : aeval a g = 0) : a^(2^g.natDegree) = a :=
      (degree_dvd_iff_frobenius hgi ha g.natDegree).1 dvd_rfl
    have hpow : (u*v*w)^m = 1 := by simpa only [mul_pow] using he
    have hzero : u*v*w ≠ 0 := by rintro hz; simp [hz, hm.ne'] at hpow
    apply (pow_eq_one_iff_of_coprime hc).1
    refine ⟨?_, hpow⟩
    apply mul_right_cancel₀ hzero
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel (Nat.two_pow_pos _)]
    simp only [mul_pow, fix hu, fix hv, fix hw]

/-- An odd-degree irreducible sampled from a coprime trinomial above degree nine
passes the three-root test. The divisibility applies to every four-term block. -/
theorem no_root_triple_of_cubic_trinomial_sampling {f : BinaryPoly} {n a : ℕ}
    (hn : 9 < n) (ho : Odd n) (ha : 0 < a) (han : a < n) (hc : a.Coprime n)
    (hf : Irreducible f) (hdeg : f.natDegree = n)
    (hd : trinomial n a ∣ expand (ZMod 2) 3 f) : NoRootTriple f := by
  have ht := trinomial_degree ha han
  have he := ht.trans hdeg.symm
  apply (no_root_triple_iff_of_coprime_sampling (by decide : 0 < 3) hf he hd _).2
  · exact trinomial_no_root_triple_of_nine_lt hn ha han hc (irreducible_of_dvd_expand_same_degree hf he hd)
  · rw [ht]
    exact (mersenne_coprime_three_iff_odd n).2 ho

end GF2Sparse
