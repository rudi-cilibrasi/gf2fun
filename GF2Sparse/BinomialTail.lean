import GF2Sparse.Progressions
import GF2Sparse.LocalFactors
import GF2Sparse.ShiftWeight

/-! Primitivity of X^n+(X+1)^k via a trinomial of the same degree. -/

namespace GF2Sparse
open Polynomial

noncomputable def binomialTail (n k : ℕ) : BinaryPoly := X^n + (X+1)^k

theorem binomialTail_degree {n k : ℕ} (hk : k < n) :
    (binomialTail n k).natDegree = n := by
  have h : ((X : BinaryPoly) + 1).natDegree = 1 := by
    simpa using natDegree_X_add_C (1 : ZMod 2)
  unfold binomialTail
  rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
  simpa [natDegree_pow, h] using hk

theorem trinomial_dvd_expand_binomialTail (n k : ℕ) :
    trinomial n k ∣ expand (ZMod 2) k (binomialTail n k) := by
  simpa only [trinomial, binomialTail, map_add, map_pow, map_one, expand_X,
    CharTwo.sub_eq_add, ← pow_mul, Nat.mul_comm k n] using
    sub_dvd_pow_sub_pow ((X : BinaryPoly)^n) (X^k+1) k

theorem primitive_binomialTail_iff {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    Primitive (binomialTail n k) ↔ Primitive (trinomial n k) ∧ (2^n-1).Coprime k := by
  have hd := binomialTail_degree hkn
  have ht := trinomial_degree hk hkn
  have hn : 0 < n := lt_trans hk hkn
  have hf : binomialTail n k ≠ 0 := fun h => by simp [h] at hd; omega
  have hg : trinomial n k ≠ 0 := fun h => by simp [h] at ht; omega
  simpa only [hd] using primitive_iff_of_dvd_expand (binary_monic hf) (binary_monic hg)
    (by simpa only [hd] using hn) (ht.trans hd.symm) hk (trinomial_dvd_expand_binomialTail n k)

theorem shift_binomialTail (n k : ℕ) :
    ShiftWeight.shift (binomialTail n k) = (X+1)^n + X^k := by
  simp only [ShiftWeight.shift, binomialTail, add_comp, pow_comp, X_comp, one_comp,
    add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem primitive_shift_binomialTail_iff {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    Primitive (ShiftWeight.shift (binomialTail n k)) ↔
      Primitive (trinomial n k) ∧ (2^n-1).Coprime n := by
  have hn := hk.trans hkn
  have hlin : ((X : BinaryPoly)+1).natDegree = 1 := by simpa using natDegree_X_add_C (1 : ZMod 2)
  have hd : (ShiftWeight.shift (binomialTail n k)).natDegree = n := by
    rw [ShiftWeight.shift, natDegree_comp, binomialTail_degree hkn, hlin, Nat.mul_one]
  have ht := trinomial_degree hk hkn
  have hf : ShiftWeight.shift (binomialTail n k) ≠ 0 := fun h => by simp [h] at hd; omega
  have hg : trinomial n k ≠ 0 := fun h => by simp [h] at ht; omega
  have hdiv : trinomial n k ∣ expand (ZMod 2) n (ShiftWeight.shift (binomialTail n k)) := by
    have he : (X : BinaryPoly)^n + (X^k+1) = (X^n+1)+X^k := by abel
    rw [shift_binomialTail, trinomial, he]
    simpa only [map_add, map_pow, expand_X, map_one, CharTwo.sub_eq_add, ← pow_mul,
      Nat.mul_comm n k] using sub_dvd_pow_sub_pow ((X : BinaryPoly)^n+1) (X^k) n
  simpa only [hd] using primitive_iff_of_dvd_expand (binary_monic hf) (binary_monic hg)
    (by simpa only [hd] using hn) (ht.trans hd.symm) hn hdiv

theorem binomialTail_two_bits (n a b : ℕ) :
    binomialTail n (2^a + 2^b) = productCandidate n (2^a) (2^b) := by
  simp only [binomialTail, productCandidate, pow_add, add_pow_char_pow, one_pow]

section Roots
variable {K : Type*} [Field K] [Algebra (ZMod 2) K] [CharP K 2]

private theorem trinomial_root {z : K} {n k : ℕ} :
    aeval z (trinomial n k) = 0 ↔ z^n = z^k+1 := by
  simp only [trinomial, map_add, map_pow, aeval_X, map_one, CharTwo.add_eq_zero]

private theorem tail_root {r : K} {n k : ℕ} :
    aeval r (binomialTail n k) = 0 ↔ r^n = (r+1)^k := by
  simp only [binomialTail, map_add, map_pow, aeval_X, map_one, CharTwo.add_eq_zero]

private theorem root_image {n k : ℕ} {z : K} (h : aeval z (trinomial n k) = 0) :
    aeval (z^k) (binomialTail n k) = 0 := by
  apply tail_root.2
  rw [← pow_mul, Nat.mul_comm, pow_mul, trinomial_root.1 h]

omit [Algebra (ZMod 2) K] [CharP K 2] in
private theorem commute_zpow_pow (z : K) (a : ℤ) (n : ℕ) : (z^a)^n = (z^n)^a := by
  calc
    _ = z^(a*(n : ℤ)) := by rw [zpow_mul, zpow_natCast]
    _ = _ := by rw [Int.mul_comm, zpow_mul, zpow_natCast]

omit [Algebra (ZMod 2) K] [CharP K 2] in
private theorem recover_from_two_powers {n k : ℕ} (hc : k.Coprime n) {z : K} (hz : z ≠ 0) :
    (z^k)^(k.gcdA n) * (z^n)^(k.gcdB n) = z := by
  have h : (k : ℤ) * k.gcdA n + (n : ℤ) * k.gcdB n = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hc.gcd_eq_one]; rfl
  calc
    _ = z^((k : ℤ) * k.gcdA n + (n : ℤ) * k.gcdB n) := by
      rw [zpow_add₀ hz, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    _ = _ := by rw [h, zpow_one]

/-- Taking the k-th power is a bijection on the two root sets in every
binary extension field when n and k are coprime. -/
theorem binomialTail_root_iff_unique {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (hc : k.Coprime n) (r : K) :
    aeval r (binomialTail n k) = 0 ↔ ∃! z : K, aeval z (trinomial n k) = 0 ∧ z^k = r := by
  constructor
  · intro hr
    have he := tail_root.1 hr
    have hn := hk.trans hkn
    have hr0 : r ≠ 0 := by rintro rfl; simp [zero_pow hn.ne'] at he
    have hr1 : r+1 ≠ 0 := by
      intro hz
      exact pow_ne_zero n hr0 (by rw [he, hz, zero_pow hk.ne'])
    let z := r^(k.gcdA n) * (r+1)^(k.gcdB n)
    have hzk : z^k = r := by
      dsimp [z]
      rw [mul_pow, commute_zpow_pow, commute_zpow_pow, ← he]
      exact recover_from_two_powers hc hr0
    have hzn : z^n = r+1 := by
      dsimp [z]
      rw [mul_pow, commute_zpow_pow, commute_zpow_pow, he]
      exact recover_from_two_powers hc hr1
    refine ⟨z, ⟨trinomial_root.2 (hzn.trans (by rw [hzk])), hzk⟩, ?_⟩
    rintro t ⟨ht, htk⟩
    have ht0 : t ≠ 0 := fun h => hr0 (by rw [← htk, h, zero_pow hk.ne'])
    have htn := trinomial_root.1 ht
    rw [htk] at htn
    exact (recover_from_two_powers hc ht0).symm.trans (by rw [htk, htn])
  · rintro ⟨z, ⟨hz, rfl⟩, _⟩
    exact root_image hz

end Roots

private theorem irreducible_of_root_in_factor_fields {f g : BinaryPoly} (hf : Irreducible f)
    (hd : f.natDegree = g.natDegree)
    (hroot : ∀ p : BinaryPoly, Irreducible p → p ∣ g → ∃ r : AdjoinRoot p, aeval r f = 0) :
    Irreducible g := by
  have hn : 0 < g.natDegree := hd ▸ hf.natDegree_pos
  have hg : g ≠ 0 := fun h => by simp [h] at hn
  obtain ⟨p, hp, hpg⟩ := WfDvdMonoid.exists_irreducible_factor
    (not_isUnit_of_natDegree_pos g hn) hg
  letI : Fact (Irreducible p) := ⟨hp⟩
  let e := (AdjoinRoot.powerBasisAux hp.ne_zero).equivFun.toEquiv
  letI : Fintype (AdjoinRoot p) := Fintype.ofEquiv _ e.symm
  obtain ⟨r, hr⟩ := hroot p hp hpg
  have hfixed := FiniteField.pow_card r
  rw [card_adjoinRoot hp.ne_zero] at hfixed
  have hdiv := (degree_dvd_iff_frobenius hf hr _).2 hfixed
  rw [hd] at hdiv
  have heq := eq_of_monic_of_dvd_of_natDegree_le (binary_monic hp.ne_zero) (binary_monic hg)
    hpg (Nat.le_of_dvd hp.natDegree_pos hdiv)
  exact heq ▸ hp

private theorem irreducible_iff_of_coprime {n k : ℕ} (hk : 0 < k) (hkn : k < n) (hc : k.Coprime n) :
    Irreducible (binomialTail n k) ↔ Irreducible (trinomial n k) := by
  have hd := (binomialTail_degree hkn).trans (trinomial_degree hk hkn).symm
  constructor
  · intro hf
    apply irreducible_of_root_in_factor_fields hf hd
    intro p hp hpg
    letI : Fact (Irreducible p) := ⟨hp⟩
    letI : CharP (AdjoinRoot p) 2 := charP_of_injective_ringHom (AdjoinRoot.of p).injective 2
    exact ⟨AdjoinRoot.root p ^ k, root_image (by rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_eq_zero.2 hpg)⟩
  · intro hg
    apply irreducible_of_root_in_factor_fields hg hd.symm
    intro p hp hpf
    letI : Fact (Irreducible p) := ⟨hp⟩
    letI : CharP (AdjoinRoot p) 2 := charP_of_injective_ringHom (AdjoinRoot.of p).injective 2
    have hr : aeval (AdjoinRoot.root p) (binomialTail n k) = 0 := by
      rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_eq_zero.2 hpf
    obtain ⟨z, ⟨hz, _⟩, _⟩ := (binomialTail_root_iff_unique hk hkn hc _).1 hr
    exact ⟨z, hz⟩

private theorem coprime_of_irreducible_binomialTail {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (hf : Irreducible (binomialTail n k)) : k.Coprime n := by
  let d := k.gcd n
  have hd : 0 < d := Nat.gcd_pos_of_pos_left n hk
  by_contra h
  have hd1 : 1 < d := by
    have hne : d ≠ 1 := h
    omega
  obtain ⟨a, ha⟩ := Nat.gcd_dvd_left k n
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_right k n
  change k = d*a at ha
  change n = d*b at hb
  have hab : a < b := Nat.lt_of_mul_lt_mul_left (by simpa only [← ha, ← hb] using hkn : d*a < d*b)
  have hdiv : binomialTail b a ∣ binomialTail n k := by
    rw [ha, hb]
    unfold binomialTail
    rw [Nat.mul_comm d b, Nat.mul_comm d a, pow_mul (X : BinaryPoly) b d, pow_mul (X+1) a d]
    simpa only [CharTwo.sub_eq_add] using sub_dvd_pow_sub_pow ((X : BinaryPoly)^b) ((X+1)^a) d
  have hdeg := binomialTail_degree hab
  have hpos : 0 < (binomialTail b a).natDegree := by rw [hdeg]; omega
  have hassoc := (hf.dvd_iff.1 hdiv).resolve_left (not_isUnit_of_natDegree_pos _ hpos)
  have hne : binomialTail b a ≠ 0 := fun h => by simp [h] at hpos
  have hle := natDegree_le_of_dvd hassoc.dvd hne
  rw [hdeg, binomialTail_degree hkn, hb] at hle
  nlinarith

theorem irreducible_binomialTail_iff {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    Irreducible (binomialTail n k) ↔ k.Coprime n ∧ Irreducible (trinomial n k) := by
  constructor
  · intro hf
    have hc := coprime_of_irreducible_binomialTail hk hkn hf
    exact ⟨hc, (irreducible_iff_of_coprime hk hkn hc).1 hf⟩
  · rintro ⟨hc, hg⟩
    exact (irreducible_iff_of_coprime hk hkn hc).2 hg

/-- The index of the translate of a primitive binomial-tail root is gcd(n, 2^n-1). -/
theorem orderOf_add_one_of_primitive_binomialTail {K : Type*} [Field K]
    [Algebra (ZMod 2) K] [CharP K 2] {r : K} {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (hf : Primitive (binomialTail n k)) (hr : aeval r (binomialTail n k) = 0) :
    orderOf (r+1) = (2^n-1) / ((2^n-1).gcd n) := by
  have hc := (irreducible_binomialTail_iff hk hkn).1 hf.2.1
  have hg := ((primitive_binomialTail_iff hk hkn).1 hf).1
  obtain ⟨z, ⟨hz, hzk⟩, _⟩ := (binomialTail_root_iff_unique hk hkn hc.1 r).1 hr
  have ho := (orderOf_root_at hg.2.1 hz).trans hg.2.2
  rw [trinomial_degree hk hkn] at ho
  rw [← hzk, ← trinomial_root.1 hz, orderOf_pow' z (hk.trans hkn).ne', ho]

end GF2Sparse
