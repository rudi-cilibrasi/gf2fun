import GF2Sparse.AdditiveOrbit

/-! Periodicity of short multiplicative relations when only the leading
exponent changes, from 2^s₀-r to 2^s-r. -/

namespace GF2Sparse

open Polynomial

private abbrev K := AlgebraicClosure (ZMod 2)

private noncomputable def orbitPoly (r : ℕ) (h : BinaryPoly) : ℕ → BinaryPoly
  | 0 => X
  | j+1 => (orbitPoly r h j)^r * h.comp (orbitPoly r h j)

private noncomputable def layerPoly (r : ℕ) (h : BinaryPoly) : ℕ → BinaryPoly
  | 0 => X
  | j+1 => h.comp (orbitPoly r h j)

private theorem orbit_degree {h : BinaryPoly} (hm : h.Monic) (hd : 0 < h.natDegree)
    (r j : ℕ) : (orbitPoly r h j).Monic ∧ 0 < (orbitPoly r h j).natDegree := by
  induction j with
  | zero => simp [orbitPoly]
  | succ j ih =>
    have hc := hm.comp ih.1 ih.2.ne'
    refine ⟨(ih.1.pow r).mul hc, ?_⟩
    rw [orbitPoly, (ih.1.pow r).natDegree_mul hc, natDegree_comp]
    have := Nat.mul_pos hd ih.2
    omega

private theorem layer_degree {h : BinaryPoly} (hm : h.Monic) (hd : 0 < h.natDegree)
    (r j : ℕ) : (layerPoly r h j).Monic ∧ 0 < (layerPoly r h j).natDegree := by
  cases j with
  | zero => simp [layerPoly]
  | succ j =>
    obtain ⟨hm', hd'⟩ := orbit_degree hm hd r j
    exact ⟨hm.comp hm' hd'.ne', by rw [layerPoly, natDegree_comp]; exact Nat.mul_pos hd hd'⟩

private theorem layer_later {r : ℕ} (hr : 0 < r) {h : BinaryPoly} (hc : h.coeff 0 = 1)
    {i j : ℕ} {x : K} (hx : aeval x (layerPoly r h i) = 0) (hlt : i < j) :
    aeval x (layerPoly r h j) = 1 := by
  have hi : aeval x (orbitPoly r h i) = 0 := by
    cases i with
    | zero => exact hx
    | succ i =>
      change aeval x (h.comp (orbitPoly r h i)) = 0 at hx
      simp [orbitPoly, hx]
  have hz (b : ℕ) : aeval x (orbitPoly r h (i+b)) = 0 := by
    induction b with
    | zero => simpa using hi
    | succ b ih => simp [orbitPoly, ih, zero_pow hr.ne']
  obtain ⟨l, he⟩ := Nat.exists_eq_add_of_le hlt
  rw [show j = (i+l)+1 by omega, layerPoly, aeval_comp, hz, ← coeff_zero_eq_aeval_zero', hc, map_one]

private noncomputable def nodes (r : ℕ) (h : BinaryPoly) (j : ℕ) : Multiset K :=
  ((layerPoly r h j).map (algebraMap (ZMod 2) K)).roots

private def polys (r : ℕ) (h : BinaryPoly) (k : ℕ) : Set K[X] :=
  {p | p.Monic ∧ p.natDegree = k ∧ ∀ j : Fin k, ((nodes r h j).map (fun a => p.eval a)).prod = 1}

private def tupleRoots (r : ℕ) (h : BinaryPoly) (k : ℕ) : Set K :=
  ⋃ p ∈ polys r h k, {x | p.IsRoot x}

private theorem finite_tupleRoots {r : ℕ} (hr : 0 < r) {h : BinaryPoly} (hm : h.Monic)
    (hd : 0 < h.natDegree) (hc : h.coeff 0 = 1) (k : ℕ) : (tupleRoots r h k).Finite := by
  have hpos (j : Fin k) : 0 < (nodes r h j).card := by
    rw [nodes, ← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_map]
    exact (layer_degree hm hd r j).2
  have hdis (i j : Fin k) (x : K) (hi : x ∈ nodes r h i) (hj : x ∈ nodes r h j) : i = j := by
    have root (t : Fin k) (hx : x ∈ nodes r h t) : aeval x (layerPoly r h t) = 0 := by
      have hz := (mem_roots ((layer_degree hm hd r t).1.map (algebraMap _ K)).ne_zero).1 hx
      simpa [IsRoot, eval_map, aeval_def] using hz
    rcases lt_trichotomy i.val j.val with he | he | he
    · exact (zero_ne_one ((root j hj).symm.trans (layer_later hr hc (root i hi) he))).elim
    · exact Fin.ext he
    · exact (zero_ne_one ((root i hi).symm.trans (layer_later hr hc (root j hj) he))).elim
  have hp : (polys r h k).Finite := finite_prescribed_multiset_products _ _ hpos hdis
  exact hp.biUnion fun p h => p.finite_setOf_isRoot h.1.ne_zero

private theorem mem_tupleRoots {k r s : ℕ} {h : BinaryPoly} (hm : h.Monic) (hd : 0 < h.natDegree)
    (z : Fin k → K) (hf : ∀ i, z i ^ (2^s) = z i ^ r * aeval (z i) h)
    (hp : ∏ i, z i = 1) (t : Fin k) : z t ∈ tupleRoots r h k := by
  have turn (x : K) (hx : x^(2^s)=x^r*aeval x h) (j : ℕ) :
      aeval x (orbitPoly r h (j+1)) = (aeval x (orbitPoly r h j))^(2^s) := by
    induction j with
    | zero => simpa [orbitPoly, aeval_comp] using hx.symm
    | succ j ih =>
      change aeval x ((orbitPoly r h (j+1))^r * h.comp (orbitPoly r h (j+1))) = _
      rw [map_mul, map_pow, aeval_comp, ih, aeval_dyadic, pow_right_comm, ← mul_pow]
      exact congrArg (· ^ (2^s)) (by simpa only [orbitPoly, map_mul, map_pow, aeval_comp] using ih)
  have all (j : ℕ) : ∏ i, aeval (z i) (orbitPoly r h j) = 1 := by
    induction j with
    | zero => simpa [orbitPoly] using hp
    | succ j ih => simp_rw [turn _ (hf _) j]; rw [Finset.prod_pow, ih, one_pow]
  have products (j : ℕ) : ∏ i, aeval (z i) (layerPoly r h j) = 1 := by
    cases j with
    | zero => simpa [layerPoly] using hp
    | succ j =>
      have hh := all (j+1)
      simpa only [orbitPoly, map_mul, map_pow, Finset.prod_mul_distrib, Finset.prod_pow,
        all j, one_pow, one_mul, layerPoly] using hh
  let H : K[X] := ∏ i, (X-C (z i))
  have hH : H ∈ polys r h k := by
    refine ⟨monic_prod_X_sub_C z _, by simp [H], fun j => ?_⟩
    dsimp only [nodes, H]
    rw [eval_root_products _ ((layer_degree hm hd r j).1.map _)]
    simpa [eval_map, aeval_def] using products j
  change z t ∈ ⋃ p ∈ polys r h k, {x | p.IsRoot x}
  refine Set.mem_iUnion.2 ⟨H, Set.mem_iUnion.2 ⟨hH, ?_⟩⟩
  change H.eval (z t) = 0
  simp only [H, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ t) (sub_self _)

private theorem shifted_root_iff {x : K} {h : BinaryPoly} {r s : ℕ} (hx : x ≠ 0) (hle : r ≤ 2^s) :
    aeval x (X^(2^s-r)+h) = 0 ↔ x^(2^s) = x^r * aeval x h := by
  simp only [map_add, map_pow, aeval_X, CharTwo.add_eq_zero]
  have he : 2^s-r+r=2^s := Nat.sub_add_cancel hle
  constructor
  · intro hz
    conv_lhs => rw [← he, pow_add, hz]
    exact mul_comm ..
  · intro hz
    apply mul_right_cancel₀ (pow_ne_zero r hx)
    rw [← pow_add, he, hz, mul_comm]

private theorem frobenius_mod_period {x : K} {M : ℕ} (hx : x^(2^M)=x) (a : ℕ) :
    x^(2^a) = x^(2^(a%M)) := by
  calc
    _ = x^(2^(M*(a/M)+a%M)) := by rw [Nat.add_comm (M*_), Nat.mod_add_div]
    _ = _ := by rw [pow_add, pow_mul, fixed_at_multiple hx _]

/-- No selection of exactly k roots, with repetitions allowed, has product one. -/
def NoRootProductOfLength (k : ℕ) (f : BinaryPoly) : Prop :=
  ∀ z : Fin k → AlgebraicClosure (ZMod 2), (∀ i, aeval (z i) f = 0) → ∏ i, z i ≠ 1

/-- For every fixed binary tail h of positive degree and constant term one,
the tests through any fixed rank are periodic in s at degree 2^s-r, r>0. -/
theorem periodic_shifted_product_lengths (k r : ℕ) (hr : 0 < r) (h : BinaryPoly)
    (hd : 0 < h.natDegree) (hc : h.coeff 0 = 1) :
    ∃ M > 0, ∀ s t : ℕ, r < 2^s → r < 2^t → s ≡ t [MOD M] →
      ∀ j ≤ k, NoRootProductOfLength j (X^(2^s-r)+h) ↔ NoRootProductOfLength j (X^(2^t-r)+h) := by
  have hm : h.Monic := binary_monic (by intro he; simp [he] at hc)
  let S := ⋃ j : Fin (k+1), tupleRoots r h j
  obtain ⟨M, hM, hfix⟩ := common_frobenius_period S
    (Set.finite_iUnion fun j => finite_tupleRoots hr hm hd hc j)
  have transfer (s t : ℕ) (hs : r < 2^s) (ht : r < 2^t) (hst : s ≡ t [MOD M])
      (j : ℕ) (hle : j ≤ k) (hall : NoRootProductOfLength j (X^(2^t-r)+h)) :
      NoRootProductOfLength j (X^(2^s-r)+h) := by
    intro z hz hp
    have hx0 (i : Fin j) : z i ≠ 0 := by
      intro he
      have hh := hz i
      rw [he, map_add, map_pow, aeval_X, zero_pow (Nat.sub_pos_of_lt hs).ne', zero_add,
        ← coeff_zero_eq_aeval_zero', hc, map_one] at hh
      exact one_ne_zero hh
    have hf (i : Fin j) := (shifted_root_iff (hx0 i) hs.le).1 (hz i)
    apply hall z _ hp
    intro i
    have hmem : z i ∈ S := Set.mem_iUnion.2 ⟨⟨j, by omega⟩, mem_tupleRoots hm hd z hf hp i⟩
    have hfix' := hfix _ hmem
    apply (shifted_root_iff (hx0 i) ht.le).2
    calc
      _ = (z i)^(2^(t%M)) := frobenius_mod_period hfix' _
      _ = (z i)^(2^(s%M)) := congrArg (fun a : ℕ => (z i)^(2^a)) hst.symm
      _ = _ := (frobenius_mod_period hfix' s).symm.trans (hf i)
  exact ⟨M, hM, fun s t hs ht hst j hj =>
    ⟨transfer t s ht hs hst.symm j hj, transfer s t hs ht hst j hj⟩⟩

theorem periodic_shifted_short_products (k r : ℕ) (hr : 0 < r) (h : BinaryPoly)
    (hd : 0 < h.natDegree) (hc : h.coeff 0 = 1) :
    ∃ M > 0, ∀ s t : ℕ, r < 2^s → r < 2^t → s ≡ t [MOD M] →
      (NoShortRootProducts k (X^(2^s-r)+h) ↔ NoShortRootProducts k (X^(2^t-r)+h)) := by
  obtain ⟨M, hM, per⟩ := periodic_shifted_product_lengths k r hr h hd hc
  refine ⟨M, hM, fun s t hs ht hst => ?_⟩
  exact ⟨fun hall j hj hjk => (per s t hs ht hst j hjk).1 (hall j hj hjk),
    fun hall j hj hjk => (per s t hs ht hst j hjk).2 (hall j hj hjk)⟩

/-- A nonempty product-one tuple of conjugates of a primitive root has
at least the degree many entries, even when entries repeat. -/
theorem Primitive.no_short_root_products {f : BinaryPoly} (hf : Primitive f) {k : ℕ}
    (hk : k < f.natDegree) : NoShortRootProducts k f := by
  classical
  intro d hd hdk z hz hprod
  let n := f.natDegree
  have hn : 0 < n := hf.2.1.natDegree_pos
  letI : NeZero n := ⟨hn.ne'⟩
  let r := z ⟨0, hd⟩
  have hr : aeval r f = 0 := hz _
  have hfix : r^(2^n) = r := (degree_dvd_iff_frobenius hf.2.1 hr _).1 dvd_rfl
  have hord : orderOf r = 2^n-1 := (orderOf_root_at hf.2.1 hr).trans hf.2.2
  choose a ha using fun i => exists_frobenius_root hf.2.1 hr (hz i)
  let A (i : Fin d) : Fin n := ⟨a i % n, Nat.mod_lt _ hn⟩
  let E (j : Fin n) := ∑ i, 2^((A i+j).val)
  have hrotate (i : Fin d) (j : Fin n) :
      r^(2^(A i+j).val) = (z i)^(2^j.val) := by
    rw [ha, ← pow_mul, ← pow_add, Fin.val_add]
    calc
      _ = r^(2^((a i+j.val)%n)) := by simp [A, Nat.mod_add_mod]
      _ = _ := (frobenius_mod_period hfix _).symm
  have hdiv (j : Fin n) : 2^n-1 ∣ E j := by
    rw [← hord]
    apply orderOf_dvd_of_pow_eq_one
    dsimp only [E]
    rw [← Finset.prod_pow_eq_pow_sum]
    simp_rw [hrotate]
    rw [Finset.prod_pow, hprod, one_pow]
  have hsum : ∑ j, E j = d*(2^n-1) := by
    unfold E
    rw [Finset.sum_comm]
    have hrot (i : Fin d) : ∑ j : Fin n, 2^(A i+j).val = 2^n-1 := by
      calc
        _ = ∑ j : Fin n, (2:ℕ)^j.val := Equiv.sum_comp (Equiv.addLeft (A i)) (fun j : Fin n => (2:ℕ)^j.val)
        _ = _ := by rw [Fin.sum_univ_eq_sum_range (fun j => 2^j)]; simpa using Nat.geomSum_eq (m:=2) (by decide) n
    simp [hrot]
  have hle (j : Fin n) : 2^n-1 ≤ E j := Nat.le_of_dvd
    (Finset.sum_pos (fun _ _ => Nat.two_pow_pos _) ⟨⟨0, hd⟩, Finset.mem_univ _⟩) (hdiv j)
  have hbig : n*(2^n-1) ≤ d*(2^n-1) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum] using
      (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hle j))
  have hnd := Nat.le_of_mul_le_mul_right hbig (Nat.sub_pos_of_lt (Nat.one_lt_two_pow hn.ne'))
  change k < n at hk
  omega

theorem Primitive.has_degree_length_product {f : BinaryPoly} (hf : Primitive f) :
    ¬ NoRootProductOfLength f.natDegree f := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero K f (ne_of_gt hf.2.1.degree_pos)
  intro hall
  apply hall (fun i : Fin f.natDegree => x^(2^i.val))
  · intro i
    rw [aeval_dyadic, hx, zero_pow (Nat.two_pow_pos _).ne']
  · rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun j => (2:ℕ)^j)]
    have hs : ∑ i ∈ Finset.range f.natDegree, (2:ℕ)^i = 2^f.natDegree-1 := by
      simpa using Nat.geomSum_eq (m:=2) (by decide) f.natDegree
    rw [hs, ← hf.2.2, ← orderOf_root_at hf.2.1 hx, pow_orderOf_eq_one]

/-- Translating the leading exponent of a primitive seed on an unbounded
progression preserves its exact first product-one length, even with repetition. -/
theorem primitive_seed_first_failure {s₀ r : ℕ} (hr : 0 < r) (hs : r < 2^s₀) (h : BinaryPoly)
    (hd : 0 < h.natDegree) (hc : h.coeff 0 = 1) (hf : Primitive (X^(2^s₀-r)+h)) :
    let n := (X^(2^s₀-r)+h).natDegree
    ∃ M > 0, ∀ l : ℕ, let f : BinaryPoly := X^(2^(s₀+M*l)-r)+h
      NoShortRootProducts (n-1) f ∧ ¬ NoRootProductOfLength n f := by
  let n := (X^(2^s₀-r)+h).natDegree
  have hn : 0 < n := hf.2.1.natDegree_pos
  obtain ⟨M, hM, per⟩ := periodic_shifted_product_lengths n r hr h hd hc
  refine ⟨M, hM, fun l => ?_⟩
  have he : s₀ ≡ s₀+M*l [MOD M] := by rw [Nat.add_comm]; exact Nat.ModEq.modulus_mul_add.symm
  have h := per s₀ (s₀+M*l) hs (hs.trans_le (Nat.pow_le_pow_right (by decide) (by omega))) he
  constructor
  · intro j hj hjn
    exact (h j (by omega)).1 (hf.no_short_root_products (show n-1<n by omega) j hj hjn)
  · exact fun hbad => hf.has_degree_length_product ((h n le_rfl).2 hbad)

end GF2Sparse
