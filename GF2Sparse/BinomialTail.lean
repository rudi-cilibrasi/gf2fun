import GF2Sparse.ProgressionTriples
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

/-- An arbitrary polynomial tail can be sampled on the two sides of a power. -/
theorem power_tail_dvd_expand (h : BinaryPoly) (n k : ℕ) :
    X^n + expand (ZMod 2) k h ∣ expand (ZMod 2) k (X^n + h^k) := by
  simp only [map_add, map_pow, expand_X]
  rw [← pow_mul, Nat.mul_comm k n, pow_mul]
  simpa only [CharTwo.sub_eq_add] using
    sub_dvd_pow_sub_pow ((X : BinaryPoly)^n) (expand (ZMod 2) k h) k

private theorem power_tail_degrees (h : BinaryPoly) {n k : ℕ} (hd : h.natDegree*k < n) :
    ((X : BinaryPoly)^n+h^k).natDegree = n ∧
      ((X : BinaryPoly)^n+expand (ZMod 2) k h).natDegree = n := by
  have hF : ((X : BinaryPoly)^n+h^k).natDegree = n := by
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
    simpa only [natDegree_X_pow, natDegree_pow, natDegree_X, Nat.mul_one, Nat.mul_comm k h.natDegree] using hd
  have hG : ((X : BinaryPoly)^n+expand (ZMod 2) k h).natDegree = n := by
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
    simpa only [natDegree_expand, natDegree_X_pow] using hd
  exact ⟨hF, hG⟩

theorem primitive_power_tail_iff (h : BinaryPoly) {n k : ℕ} (hk : 0 < k)
    (hd : h.natDegree*k < n) :
    Primitive (X^n+h^k) ↔ Primitive (X^n+expand (ZMod 2) k h) ∧ (2^n-1).Coprime k := by
  obtain ⟨hF, hG⟩ := power_tail_degrees h hd
  have hn : 0 < n := Nat.zero_le _ |>.trans_lt hd
  have hf : (X : BinaryPoly)^n+h^k ≠ 0 := fun he => by rw [he, natDegree_zero] at hF; omega
  have hg : (X : BinaryPoly)^n+expand (ZMod 2) k h ≠ 0 := fun he => by rw [he, natDegree_zero] at hG; omega
  simpa only [hF] using primitive_iff_of_dvd_expand (binary_monic hf) (binary_monic hg)
    (by simpa only [hF] using hn) (hG.trans hF.symm) hk (power_tail_dvd_expand h n k)

private theorem expand_linear_tail (k : ℕ) :
    expand (ZMod 2) k ((X : BinaryPoly)+1) = X^k+1 := by rw [map_add, expand_X, map_one]

theorem trinomial_dvd_expand_binomialTail (n k : ℕ) :
    trinomial n k ∣ expand (ZMod 2) k (binomialTail n k) := by
  have h := power_tail_dvd_expand ((X : BinaryPoly)+1) n k
  rw [map_add, expand_X, map_one] at h
  exact h

theorem primitive_binomialTail_iff {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    Primitive (binomialTail n k) ↔ Primitive (trinomial n k) ∧ (2^n-1).Coprime k := by
  have hlin : ((X : BinaryPoly)+1).natDegree = 1 := by simpa using natDegree_X_add_C (1 : ZMod 2)
  have h := primitive_power_tail_iff ((X : BinaryPoly)+1) hk (by simpa only [hlin, Nat.one_mul] using hkn)
  rw [map_add, expand_X, map_one] at h
  exact h

theorem primitive_product_pow_two_ratio_iff {n u s : ℕ} (hu : 0 < u) (hn : u*(1+2^s) < n) :
    Primitive (productCandidate n u (u*2^s)) ↔
      Primitive (trinomial n (u*(1+2^s))) ∧ (2^n-1).Coprime (1+2^s) := by
  have hd : ((X : BinaryPoly)^u+1).natDegree = u := by
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]; simpa using hu
  have hk : 0 < (1+2^s : ℕ) := by positivity
  have h := primitive_power_tail_iff ((X : BinaryPoly)^u+1) hk (by simpa only [hd] using hn)
  rw [map_add, map_pow, expand_X, map_one, ← pow_mul, Nat.mul_comm (1+2^s) u,
    pow_add, pow_one, add_pow_char_pow, one_pow, ← pow_mul] at h
  exact h

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

private theorem power_tail_root (h : BinaryPoly) {r : K} {n k : ℕ} :
    aeval r (X^n+h^k) = 0 ↔ r^n = (aeval r h)^k := by
  simp only [map_add, map_pow, aeval_X, CharTwo.add_eq_zero]

private theorem power_source_root (h : BinaryPoly) {z : K} {n k : ℕ} :
    aeval z (X^n+expand (ZMod 2) k h) = 0 ↔ z^n = aeval (z^k) h := by
  simp only [map_add, map_pow, aeval_X, expand_aeval, CharTwo.add_eq_zero]

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
theorem power_tail_root_iff_unique (h : BinaryPoly) {n k : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hc : k.Coprime n) (r : K) :
    aeval r (X^n+h^k) = 0 ↔ ∃! z : K, aeval z (X^n+expand (ZMod 2) k h) = 0 ∧ z^k = r := by
  constructor
  · intro hr
    have he := (power_tail_root h).1 hr
    by_cases hr0 : r = 0
    · subst r
      have hv : aeval (0 : K) h = 0 := by
        by_contra hne
        exact pow_ne_zero k hne (he.symm.trans (zero_pow hn.ne'))
      refine ⟨0, ⟨(power_source_root h).2 (by rw [zero_pow hn.ne', zero_pow hk.ne', hv]), zero_pow hk.ne'⟩, ?_⟩
      rintro z ⟨_, hz⟩
      by_contra hne
      exact pow_ne_zero k hne hz
    have hr1 : aeval r h ≠ 0 := by
      intro hz
      exact pow_ne_zero n hr0 (by rw [he, hz, zero_pow hk.ne'])
    let z := r^(k.gcdA n) * (aeval r h)^(k.gcdB n)
    have hzk : z^k = r := by
      dsimp [z]
      rw [mul_pow, commute_zpow_pow, commute_zpow_pow, ← he]
      exact recover_from_two_powers hc hr0
    have hzn : z^n = aeval r h := by
      dsimp [z]
      rw [mul_pow, commute_zpow_pow, commute_zpow_pow, he]
      exact recover_from_two_powers hc hr1
    refine ⟨z, ⟨(power_source_root h).2 (hzn.trans (by rw [hzk])), hzk⟩, ?_⟩
    rintro t ⟨ht, htk⟩
    have ht0 : t ≠ 0 := fun h => hr0 (by rw [← htk, h, zero_pow hk.ne'])
    have htn := (power_source_root h).1 ht
    rw [htk] at htn
    exact (recover_from_two_powers hc ht0).symm.trans (by rw [htk, htn])
  · rintro ⟨z, ⟨hz, rfl⟩, _⟩
    apply (power_tail_root h).2
    rw [← pow_mul, Nat.mul_comm, pow_mul, (power_source_root h).1 hz]

theorem binomialTail_root_iff_unique {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (hc : k.Coprime n) (r : K) :
    aeval r (binomialTail n k) = 0 ↔ ∃! z : K, aeval z (trinomial n k) = 0 ∧ z^k = r := by
  unfold binomialTail trinomial
  rw [← expand_linear_tail k]
  exact power_tail_root_iff_unique ((X : BinaryPoly)+1) hk (hk.trans hkn) hc r

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

private theorem irreducible_iff_of_coprime (h : BinaryPoly) {n k : ℕ}
    (hk : 0 < k) (hd : h.natDegree*k < n) (hc : k.Coprime n) :
    Irreducible (X^n+h^k) ↔ Irreducible (X^n+expand (ZMod 2) k h) := by
  obtain ⟨hF, hG⟩ := power_tail_degrees h hd
  constructor
  · intro hf
    exact irreducible_of_dvd_expand_same_degree hf (hG.trans hF.symm) (power_tail_dvd_expand h n k)
  · intro hg
    apply irreducible_of_root_in_factor_fields hg (hG.trans hF.symm)
    intro p hp hpf
    letI : Fact (Irreducible p) := ⟨hp⟩
    letI : CharP (AdjoinRoot p) 2 := charP_of_injective_ringHom (AdjoinRoot.of p).injective 2
    have hr : aeval (AdjoinRoot.root p) (X^n+h^k) = 0 := by
      rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_eq_zero.2 hpf
    obtain ⟨z, ⟨hz, _⟩, _⟩ := (power_tail_root_iff_unique h hk (Nat.zero_le _ |>.trans_lt hd) hc _).1 hr
    exact ⟨z, hz⟩

private theorem coprime_of_irreducible_power_tail (h : BinaryPoly) {n k : ℕ}
    (hk : 0 < k) (hkn : h.natDegree*k < n) (hf : Irreducible (X^n+h^k)) : k.Coprime n := by
  let d := k.gcd n
  have hd : 0 < d := Nat.gcd_pos_of_pos_left n hk
  by_contra hnc
  have hd1 : 1 < d := by
    have hne : d ≠ 1 := hnc
    omega
  obtain ⟨a, ha⟩ := Nat.gcd_dvd_left k n
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_right k n
  change k = d*a at ha
  change n = d*b at hb
  have hab : h.natDegree*a < b := by
    apply Nat.lt_of_mul_lt_mul_left (a := d)
    calc
      d*(h.natDegree*a) = h.natDegree*k := by rw [ha]; ac_rfl
      _ < n := hkn
      _ = d*b := hb
  have hdiv : (X : BinaryPoly)^b+h^a ∣ X^n+h^k := by
    rw [ha, hb, Nat.mul_comm d b, Nat.mul_comm d a, pow_mul (X : BinaryPoly) b d, pow_mul h a d]
    simpa only [CharTwo.sub_eq_add] using sub_dvd_pow_sub_pow ((X : BinaryPoly)^b) (h^a) d
  have hdeg := (power_tail_degrees h hab).1
  have hpos : 0 < ((X : BinaryPoly)^b+h^a).natDegree := by rw [hdeg]; omega
  have hassoc := (hf.dvd_iff.1 hdiv).resolve_left (not_isUnit_of_natDegree_pos _ hpos)
  have hne : (X : BinaryPoly)^b+h^a ≠ 0 := fun h => by simp [h] at hpos
  have hle := natDegree_le_of_dvd hassoc.dvd hne
  rw [hdeg, (power_tail_degrees h hkn).1, hb] at hle
  nlinarith

theorem irreducible_power_tail_iff (h : BinaryPoly) {n k : ℕ} (hk : 0 < k) (hd : h.natDegree*k < n) :
    Irreducible (X^n+h^k) ↔ k.Coprime n ∧ Irreducible (X^n+expand (ZMod 2) k h) := by
  constructor
  · intro hf
    have hc := coprime_of_irreducible_power_tail h hk hd hf
    exact ⟨hc, (irreducible_iff_of_coprime h hk hd hc).1 hf⟩
  · rintro ⟨hc, hg⟩
    exact (irreducible_iff_of_coprime h hk hd hc).2 hg

theorem irreducible_binomialTail_iff {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    Irreducible (binomialTail n k) ↔ k.Coprime n ∧ Irreducible (trinomial n k) := by
  have hlin : ((X : BinaryPoly)+1).natDegree = 1 := by simpa using natDegree_X_add_C (1 : ZMod 2)
  unfold binomialTail trinomial
  rw [← expand_linear_tail k]
  exact irreducible_power_tail_iff ((X : BinaryPoly)+1) hk (by simpa only [hlin, Nat.one_mul] using hkn)

/-- The value of the tail at a primitive root has index gcd(n, 2^n-1). -/
theorem orderOf_tail_of_primitive_power_tail {K : Type*} [Field K] [Algebra (ZMod 2) K] [CharP K 2]
    (h : BinaryPoly) {r : K} {n k : ℕ} (hk : 0 < k) (hd : h.natDegree*k < n)
    (hf : Primitive (X^n+h^k)) (hr : aeval r (X^n+h^k) = 0) :
    orderOf (aeval r h) = (2^n-1) / ((2^n-1).gcd n) := by
  have hn : 0 < n := Nat.zero_le _ |>.trans_lt hd
  have hc := (irreducible_power_tail_iff h hk hd).1 hf.2.1
  have hg := ((primitive_power_tail_iff h hk hd).1 hf).1
  obtain ⟨z, ⟨hz, hzk⟩, _⟩ := (power_tail_root_iff_unique h hk hn hc.1 r).1 hr
  have ho := (orderOf_root_at hg.2.1 hz).trans hg.2.2
  rw [(power_tail_degrees h hd).2] at ho
  rw [← hzk, ← (power_source_root h).1 hz, orderOf_pow' z hn.ne', ho]

theorem orderOf_add_one_of_primitive_binomialTail {K : Type*} [Field K]
    [Algebra (ZMod 2) K] [CharP K 2] {r : K} {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (hf : Primitive (binomialTail n k)) (hr : aeval r (binomialTail n k) = 0) :
    orderOf (r+1) = (2^n-1) / ((2^n-1).gcd n) := by
  have hlin : ((X : BinaryPoly)+1).natDegree = 1 := by simpa using natDegree_X_add_C (1 : ZMod 2)
  simpa only [map_add, aeval_X, map_one] using orderOf_tail_of_primitive_power_tail
    ((X : BinaryPoly)+1) hk (by simpa only [hlin, Nat.one_mul] using hkn) hf hr

end GF2Sparse
