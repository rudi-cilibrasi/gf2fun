import GF2Sparse.Dilation
import Mathlib.Algebra.Ring.GeomSum

/-! Primitive trinomials and pentanomials containing a four-term arithmetic
progression. The forward construction is a special case of sampling a
primitive trinomial, as in Kashiwagi and Uchimura (1982). -/

namespace GF2Sparse

open Polynomial

noncomputable def sampledBlock (a t u m : ℕ) : BinaryPoly :=
  X ^ a + X ^ t * (X ^ u + 1) ^ m

noncomputable def blockEndpoints (a t u m : ℕ) : BinaryPoly :=
  X ^ a + X ^ t * (X ^ (m * u) + 1)

noncomputable def trinomial (n k : ℕ) : BinaryPoly := X ^ n + (X ^ k + 1)

theorem trinomial_degree {n k : ℕ} (hk : 0 < k) (hn : k < n) :
    (trinomial n k).natDegree = n := by
  have h : ((X : BinaryPoly) ^ k + 1).natDegree = k := by
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]; simpa using hk
  unfold trinomial
  rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
  simpa [h] using hn

private theorem block_degrees {a t u m : ℕ} (hu : 0 < u) (hm : 0 < m)
    (hd : a ≠ t + m * u) :
    (sampledBlock a t u m).natDegree = max a (t + m * u) ∧
    (blockEndpoints a t u m).natDegree = max a (t + m * u) := by
  have hbin {j : ℕ} (hj : 0 < j) : ((X : BinaryPoly) ^ j + 1).natDegree = j := by
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]; simpa using hj
  have hmul (q : BinaryPoly) (hq : q.natDegree = m * u) :
      ((X : BinaryPoly) ^ a + X ^ t * q).natDegree = max a (t + m * u) := by
    have hmdeg : ((X : BinaryPoly) ^ t * q).natDegree = t + m * u := by
      rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (by
        intro he; have := Nat.mul_pos hm hu; simp [he] at hq; omega), natDegree_X_pow, hq]
    rcases lt_or_gt_of_ne hd with h | h
    · rw [max_eq_right h.le, natDegree_add_eq_right_of_natDegree_lt, hmdeg]
      simpa [hmdeg] using h
    · rw [max_eq_left h.le, natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
      simpa [hmdeg] using h
  exact ⟨hmul _ (by rw [natDegree_pow, hbin hu]), hmul _ (hbin (Nat.mul_pos hm hu))⟩

theorem endpoints_dvd_expand_block (a t u m : ℕ) :
    blockEndpoints a t u m ∣ expand (ZMod 2) m (sampledBlock a t u m) := by
  have h := sub_dvd_pow_sub_pow ((X : BinaryPoly) ^ a) (X ^ t * (X ^ (m * u) + 1)) m
  simpa only [sampledBlock, blockEndpoints, map_add, map_mul, map_pow, map_one, expand_X,
    sub_eq_add_neg, CharTwo.neg_eq, mul_pow, ← pow_mul, Nat.mul_comm a m, Nat.mul_comm t m] using h

/-- The exact order condition for a trinomial expanded by the sampling
construction. For m=1+2^k the binomial power has four terms. -/
theorem sampledBlock_primitive_iff {a t u m : ℕ} (hu : 0 < u) (hm : 0 < m)
    (hd : a ≠ t + m * u) :
    Primitive (sampledBlock a t u m) ↔ Primitive (blockEndpoints a t u m) ∧
      (2 ^ (max a (t + m * u)) - 1).Coprime m := by
  obtain ⟨hF, hT⟩ := block_degrees hu hm hd
  have hpos : 0 < max a (t + m * u) := by have := Nat.mul_pos hm hu; omega
  rw [← hF]
  apply primitive_iff_of_dvd_expand
  · apply binary_monic; intro he; simp [he] at hF; omega
  · apply binary_monic; intro he; simp [he] at hT; omega
  · exact hF ▸ hpos
  · exact hT.trans hF.symm
  · exact hm
  · exact endpoints_dvd_expand_block _ _ _ _

private theorem coprime_three_iff_odd (n : ℕ) :
    (2 ^ n - 1).Coprime 3 ↔ Odd n := by
  have hpow (k : ℕ) : 2 ^ (2 * k) ≡ 1 [MOD 3] := by
    rw [pow_mul]; simpa using (show 2 ^ 2 ≡ 1 [MOD 3] by decide).pow k
  rw [Nat.coprime_comm, Nat.prime_three.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero]
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, hk⟩ := he
    have hd : n = 2 * k := by omega
    have hm := hpow k
    change 2 ^ (2 * k) % 3 = 1 at hm
    rw [← hd] at hm
    have hpos := Nat.two_pow_pos n
    simp only [Nat.odd_iff]
    omega
  · obtain ⟨k, hk⟩ := ho
    have hd : n = 2 * k + 1 := by omega
    have hm := (hpow k).mul_right 2
    change 2 ^ (2 * k) * 2 % 3 = 1 * 2 % 3 at hm
    rw [← pow_succ, ← hd] at hm
    change 2 ^ n % 3 = 2 at hm
    have hpos := Nat.two_pow_pos n
    simp only [Nat.odd_iff]
    omega

/-- The three exponents of a normalized trinomial. -/
def IsTrinomial (n : ℕ) (f : BinaryPoly) : Prop :=
  ∃ k, 0 < k ∧ k < n ∧ f = trinomial n k

/-- Endpoints 0 and n and exactly four positions t,t+u,t+2u,t+3u,
with one further exponent a. -/
def IsProgressionPentanomial (n : ℕ) (f : BinaryPoly) : Prop :=
  ∃ a t u, 0 < u ∧ (a = 0 ∨ t = 0) ∧ a ≠ t ∧ a ≠ t + u ∧ a ≠ t + 2 * u ∧
    a ≠ t + 3 * u ∧ max a (t + 3 * u) = n ∧ f = sampledBlock a t u 3

theorem cubic_block_expansion (a t u : ℕ) :
    sampledBlock a t u 3 =
      X ^ a + (X ^ (t + 3 * u) + (X ^ (t + 2 * u) + (X ^ (t + u) + X ^ t))) := by
  rw [sampledBlock, pow_succ (X ^ u + 1) 2, CharTwo.add_sq]
  simp only [pow_add, pow_mul, pow_two]
  ring

private theorem endpoints_are_trinomial {a t u n : ℕ} (hu : 0 < u) (h0 : a = 0 ∨ t = 0)
    (ha : a ≠ t) (hd : a ≠ t + 3 * u) (hn : max a (t + 3 * u) = n) :
    IsTrinomial n (blockEndpoints a t u 3) := by
  rcases h0 with rfl | rfl
  · refine ⟨t, by omega, by omega, ?_⟩
    have ht : n = t + 3 * u := by omega
    simp [ht, blockEndpoints, trinomial, pow_add]; ring
  · rcases lt_or_gt_of_ne hd with h | h
    · refine ⟨a, by omega, by omega, ?_⟩
      have ht : n = 3 * u := by omega
      simp [ht, blockEndpoints, trinomial]; ring
    · refine ⟨3 * u, by omega, by omega, ?_⟩
      have ht : n = a := by omega
      simp [ht, blockEndpoints, trinomial]

theorem progression_ancestors {n : ℕ} {f : BinaryPoly} (hshape : IsProgressionPentanomial n f)
    (hp : Primitive f) :
    Odd n ∧ ∃ g : BinaryPoly, IsTrinomial n g ∧ Primitive g ∧ g ∣ expand (ZMod 2) 3 f := by
  obtain ⟨a, t, u, hu, h0, ha, _, _, hd, hn, rfl⟩ := hshape
  obtain ⟨hT, hcop⟩ := (sampledBlock_primitive_iff hu (by decide) hd).1 hp
  rw [hn, coprime_three_iff_odd] at hcop
  exact ⟨hcop, _, endpoints_are_trinomial hu h0 ha hd hn, hT, endpoints_dvd_expand_block ..⟩

theorem IsProgressionPentanomial.shape {n : ℕ} {f : BinaryPoly} (h : IsProgressionPentanomial n f) :
    f.natDegree = n ∧ f.support.card = 5 := by
  obtain ⟨a, t, u, hu, _, ha, h1, h2, h3, hn, rfl⟩ := h
  refine ⟨(block_degrees hu (by decide) h3).1.trans hn, ?_⟩
  let s : Finset ℕ := {a, t + 3 * u, t + 2 * u, t + u, t}
  have hfirst : t + u ∉ ({t} : Finset ℕ) := by simp only [Finset.mem_singleton]; omega
  have hsecond : t + 2 * u ∉ ({t + u, t} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hthird : t + 3 * u ∉ ({t + 2 * u, t + u, t} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hlast : a ∉ ({t + 3 * u, t + 2 * u, t + u, t} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have he : sampledBlock a t u 3 = ∑ j ∈ s, X ^ j := by
    simp only [s, cubic_block_expansion, Finset.sum_insert hlast, Finset.sum_insert hthird,
      Finset.sum_insert hsecond, Finset.sum_insert hfirst, Finset.sum_singleton]
  have hs : (sampledBlock a t u 3).support = s := by
    rw [he]; ext i; simp [mem_support_iff, coeff_X_pow]
  rw [hs]
  simp only [s, Finset.card_insert_of_notMem hlast, Finset.card_insert_of_notMem hthird,
    Finset.card_insert_of_notMem hsecond, Finset.card_insert_of_notMem hfirst, Finset.card_singleton]

private theorem trinomial_pair {n k : ℕ} (hn : 2 < n) (hk : 0 < k) (hkn : k < n)
    (hp : Irreducible (trinomial n k)) : 3 ∣ k ∨ 3 ∣ n-k ∨ 3 ∣ n := by
  by_contra! h
  let q := trinomial 2 1
  let z := AdjoinRoot.root q
  have hqd : q.natDegree = 2 := trinomial_degree (by decide) (by decide)
  have hq0 : q ≠ 0 := fun he => by simp [he] at hqd
  have hd : q ∣ X^3-1 := ⟨X-1, by simp [q,trinomial]; ring⟩
  have hz : z ^ 3 = 1 := sub_eq_zero.1 (by simpa [z] using AdjoinRoot.mk_eq_zero.2 hd)
  have he (j : ℕ) : z ^ j = z ^ (j % 3) :=
    pow_eq_pow_of_modEq (Nat.mod_modEq j 3).symm hz
  have hrel : z ^ 2 + (z + 1) = 0 := by
    have hh := AdjoinRoot.mk_self (f := q)
    change AdjoinRoot.mk q (trinomial 2 1) = 0 at hh
    simpa [z,trinomial] using hh
  have hdiv : q ∣ trinomial n k := by
    apply AdjoinRoot.mk_eq_zero.mp
    change AdjoinRoot.mk q (X ^ n + (X ^ k + 1)) = 0
    simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X]
    change z ^ n + (z ^ k + 1) = 0
    rw [he n, he k]
    have hm : (n % 3 = 2 ∧ k % 3 = 1) ∨ (n % 3 = 1 ∧ k % 3 = 2) := by omega
    rcases hm with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · simpa [h₁,h₂] using hrel
    · simpa [h₁,h₂,add_left_comm] using hrel
  have hassoc := (hp.dvd_iff.mp hdiv).resolve_left (not_isUnit_of_natDegree_pos q (by omega))
  have hle := natDegree_le_of_dvd hassoc.dvd hq0
  rw [trinomial_degree hk hkn, hqd] at hle
  omega

private theorem trinomial_parameters {n k : ℕ} (h5 : 5 ≤ n) (hk : 0 < k) (hkn : k < n)
    (hp : Primitive (trinomial n k)) :
    ∃ a t u, 0 < u ∧ (a = 0 ∨ t = 0) ∧ a ≠ t ∧ a ≠ t+u ∧ a ≠ t+2*u ∧
      a ≠ t+3*u ∧ max a (t+3*u) = n ∧ blockEndpoints a t u 3 = trinomial n k := by
  rcases trinomial_pair (by omega) hk hkn hp.2.1 with ⟨u, he⟩ | ⟨u, he⟩ | ⟨u, he⟩
  · refine ⟨n,0,u,by omega,Or.inr rfl,by omega,by omega,by omega,by omega,by omega,?_⟩
    simp [blockEndpoints,trinomial,he]
  · have hd : n = k + 3*u := by omega
    refine ⟨0,k,u,by omega,Or.inl rfl,by omega,by omega,by omega,by omega,by omega,?_⟩
    simp [blockEndpoints,trinomial,hd,pow_add]; ring
  · have hu : 1 < u := by omega
    have no (i : ℕ) (hi : 0 < i) (hi' : i < 3) : k ≠ u*i := by
      intro hki
      have heq : trinomial n k = expand (ZMod 2) u (trinomial 3 i) := by
        simp only [trinomial, map_add, map_pow, map_one, expand_X, ← pow_mul, he, hki, Nat.mul_comm 3 u]
      rw [heq] at hp
      exact not_primitive_expand (g := trinomial 3 i) (m := u)
        (by rw [trinomial_degree hi hi']; decide) hu hp
    have h₁ := no 1 (by decide) (by decide)
    have h₂ := no 2 (by decide) (by decide)
    refine ⟨k,0,u,by omega,Or.inr rfl,by omega,by omega,by omega,by omega,by omega,?_⟩
    simp [blockEndpoints,trinomial,he]; ring

theorem trinomial_has_progression {n : ℕ} (hn : 5 ≤ n) (ho : Odd n) {g : BinaryPoly}
    (hshape : IsTrinomial n g) (hp : Primitive g) :
    ∃ f : BinaryPoly, IsProgressionPentanomial n f ∧ Primitive f ∧ g ∣ expand (ZMod 2) 3 f := by
  obtain ⟨k,hk,hkn,rfl⟩ := hshape
  obtain ⟨a,t,u,hu,h0,ha,h1,h2,h3,hdeg,he⟩ := trinomial_parameters hn hk hkn hp
  refine ⟨sampledBlock a t u 3, ⟨a,t,u,hu,h0,ha,h1,h2,h3,hdeg,rfl⟩, ?_, ?_⟩
  · apply (sampledBlock_primitive_iff hu (by decide) h3).2
    exact ⟨he ▸ hp, hdeg ▸ (coprime_three_iff_odd n).2 ho⟩
  · rw [← he]
    exact endpoints_dvd_expand_block ..

theorem IsTrinomial.degree {n : ℕ} {g : BinaryPoly} (h : IsTrinomial n g) :
    g.natDegree = n := by
  obtain ⟨k, hk, hkn, rfl⟩ := h
  exact trinomial_degree hk hkn

theorem no_primitive_progression_of_even {n : ℕ} (hn : Even n) {f : BinaryPoly}
    (hs : IsProgressionPentanomial n f) : ¬ Primitive f := by
  intro hp
  exact (Nat.not_odd_iff_even.2 hn) (progression_ancestors hs hp).1

private theorem image_unique {g f₁ f₂ : BinaryPoly} {m : ℕ} (hg : Irreducible g)
    (hf₁ : Primitive f₁) (hf₂ : Primitive f₂)
    (hd₁ : g ∣ expand (ZMod 2) m f₁) (hd₂ : g ∣ expand (ZMod 2) m f₂) : f₁ = f₂ := by
  letI : Fact (Irreducible g) := ⟨hg⟩
  let z := AdjoinRoot.root g ^ m
  have image_eq {f : BinaryPoly} (hp : Primitive f) (hd : g ∣ expand (ZMod 2) m f) :
      f = minpoly (ZMod 2) z := by
    apply minpoly.eq_of_irreducible_of_monic hp.2.1 _ hp.1
    rw [show z = AdjoinRoot.root g ^ m from rfl, ← expand_aeval, AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_eq_zero.2 hd
  exact (image_eq hf₁ hd₁).trans (image_eq hf₂ hd₂).symm

private theorem reverse_sampling {g f : BinaryPoly} {m r : ℕ} (hg : Primitive g)
    (hf : Primitive f) (hinv : m * r % (2 ^ g.natDegree - 1) = 1)
    (hd : g ∣ expand (ZMod 2) m f) : f ∣ expand (ZMod 2) r g := by
  letI : Fact (Irreducible g) := ⟨hg.2.1⟩
  let z := AdjoinRoot.root g
  have he : aeval (z ^ m) f = 0 := by
    rw [← expand_aeval, AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_eq_zero.2 hd
  have hz : (z ^ m) ^ r = z := by
    rw [← pow_mul, ← pow_mod_orderOf, show orderOf z = 2 ^ g.natDegree - 1 from hg.2.2,
      hinv, pow_one]
  rw [minpoly.eq_of_irreducible_of_monic hf.2.1 he hf.1]
  apply minpoly.dvd
  rw [expand_aeval, hz, AdjoinRoot.aeval_eq]
  exact AdjoinRoot.mk_self

/-- In odd degrees at least five, cubing primitive roots gives a bijection
between normalized primitive trinomials and the primitive five-term
polynomials whose exponents contain a four-term arithmetic progression. -/
noncomputable def trinomialProgressionEquiv (n : ℕ) (hn : 5 ≤ n) (ho : Odd n) :
    {g : BinaryPoly // IsTrinomial n g ∧ Primitive g} ≃
      {f : BinaryPoly // IsProgressionPentanomial n f ∧ Primitive f} := by
  classical
  let T := {g : BinaryPoly // IsTrinomial n g ∧ Primitive g}
  let P := {f : BinaryPoly // IsProgressionPentanomial n f ∧ Primitive f}
  have forward (g : T) : ∃ f : P, g.val ∣ expand (ZMod 2) 3 f.val := by
    obtain ⟨f, hs, hp, hd⟩ := trinomial_has_progression hn ho g.property.1 g.property.2
    exact ⟨⟨f, hs, hp⟩, hd⟩
  have backward (f : P) : ∃ g : T, g.val ∣ expand (ZMod 2) 3 f.val := by
    obtain ⟨g, hs, hp, hd⟩ := (progression_ancestors f.property.1 f.property.2).2
    exact ⟨⟨g, hs, hp⟩, hd⟩
  have hN : 1 < 2 ^ n - 1 := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    change 4 ≤ 2 ^ n at h
    omega
  have hunit := Nat.exists_mul_mod_eq_one_of_coprime ((coprime_three_iff_odd n).2 ho).symm hN
  let r := hunit.choose
  have hr : 3 * r % (2 ^ n - 1) = 1 := hunit.choose_spec.2
  have reverse {g : T} {f : P} (hd : g.val ∣ expand (ZMod 2) 3 f.val) :
      f.val ∣ expand (ZMod 2) r g.val :=
    reverse_sampling g.property.2 f.property.2 (by rw [g.property.1.degree]; exact hr) hd
  exact
    { toFun := fun g => (forward g).choose
      invFun := fun f => (backward f).choose
      left_inv := fun g => Subtype.ext <| image_unique (forward g).choose.property.2.2.1
        (backward (forward g).choose).choose.property.2 g.property.2
        (reverse (backward (forward g).choose).choose_spec) (reverse (forward g).choose_spec)
      right_inv := fun f => Subtype.ext <| image_unique (backward f).choose.property.2.2.1
        (forward (backward f).choose).choose.property.2 f.property.2
        (forward (backward f).choose).choose_spec (backward f).choose_spec }

end GF2Sparse
