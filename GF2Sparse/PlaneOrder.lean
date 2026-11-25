import GF2Sparse.SubfieldProducts

/-! Bounds for subgroups containing an element and a polynomial value at that element. -/

namespace GF2Sparse.SubfieldProducts

open Polynomial Finset

private abbrev Pair := (_ : ℕ) × ℕ

private def band (d : ℕ) : Finset Pair :=
  (range d).sigma fun i => Ico (d / 2 - i) (min d (d / 2 + d - i))

private theorem band_bounds {d : ℕ} {z : Pair} (hz : z ∈ band d) :
    z.1 < d ∧ z.2 < d ∧ d / 2 ≤ z.1 + z.2 ∧ z.1 + z.2 < d / 2 + d := by
  simp only [band, mem_sigma, mem_range, mem_Ico, lt_min_iff] at hz
  omega

private theorem increasing_sum (m c : ℕ) :
    2 * (∑ i ∈ range m, (c+i)) + m = m*(2*c+m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ]; nlinarith

private theorem decreasing_sum (m c : ℕ) (h : m ≤ c+1) :
    2 * (∑ i ∈ range m, (c-i)) + m*m = m*(2*c+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsub : c-m+m=c := by omega
    rw [sum_range_succ]
    nlinarith [ih (by omega)]

private theorem band_card (d : ℕ) : 3*d*d ≤ 4*(band d).card := by
  let k := d/2
  let t := d-k
  have hd : d = k+t := by dsimp [k,t]; omega
  let row (i : ℕ) := min d (k+d-i) - (k-i)
  have count : (band d).card = (∑ i ∈ range k, (t+i)) + ∑ j ∈ range t, (d-j) := by
    change ((range d).sigma _).card = _
    rw [card_sigma]
    change (∑ i ∈ range d, (Ico (k-i) (min d (k+d-i))).card) = _
    simp only [Nat.card_Ico]
    change (∑ i ∈ range d, row i) = _
    conv_lhs => arg 1; rw [hd]
    rw [sum_range_add]
    congr 1
    · apply sum_congr rfl
      intro i hi
      have := mem_range.mp hi
      dsimp [row,t]
      omega
    · apply sum_congr rfl
      intro i hi
      have := mem_range.mp hi
      dsimp [row]
      omega
  have hi := increasing_sum k t
  have hj := decreasing_sum t d (by omega)
  have hcase : t=k ∨ t=k+1 := by dsimp [t,k]; omega
  rcases hcase with h | h <;> nlinarith [congrArg (fun z : ℕ => z*z) hd,
    congrArg (fun z : ℕ => z*z) h, congrArg (fun z : ℕ => k*z) h,
    congrArg (fun z : ℕ => t*z) hd]

private noncomputable def monomialAtPoly (P : BinaryPoly) (i j : ℕ) : BinaryPoly :=
  X^i * P^j

private theorem monomialAtPoly_degree {P : BinaryPoly} (hn : P ≠ 0) (i j : ℕ) :
    (monomialAtPoly P i j).natDegree = i + P.natDegree * j := by
  simp [monomialAtPoly, natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hn),
    natDegree_pow, Nat.mul_comm]

private theorem scaled_difference {u v m : ℕ} (h : u % m = v % m) :
    m * (u/m - min (u/m) (v/m)) = u - min u v := by
  rcases le_total u v with hl | hl
  · simp [min_eq_left hl, min_eq_left (Nat.div_le_div_right hl)]
  · rw [min_eq_right hl, min_eq_right (Nat.div_le_div_right hl), Nat.mul_sub]
    have hu := Nat.mod_add_div u m
    have hv := Nat.mod_add_div v m
    omega

private theorem cancel_poly_band {K : Type*} [Field K] [Algebra (ZMod 2) K] {x : K}
    (P : BinaryPoly) (hP : P.eval 0 = 1) (hx : x ≠ 0) (hx' : aeval x P ≠ 0)
    {d : ℕ} (hd : d = (minpoly (ZMod 2) x).natDegree)
    {a b : Pair} (ha : a ∈ band d) (hb : b ∈ band d)
    (hr : a.2 % P.natDegree = b.2 % P.natDegree)
    (he : x^a.1*(aeval x P)^(a.2/P.natDegree) = x^b.1*(aeval x P)^(b.2/P.natDegree)) :
    a = b := by
  let m := P.natDegree
  let i := min a.1 b.1
  let j := min (a.2/m) (b.2/m)
  let A := monomialAtPoly P (a.1-i) (a.2/m-j)
  let B := monomialAtPoly P (b.1-i) (b.2/m-j)
  have hne : P ≠ 0 := by rintro rfl; simp at hP
  have wa : m*(a.2/m-j) = a.2-min a.2 b.2 := scaled_difference hr
  have wb : m*(b.2/m-j) = b.2-min a.2 b.2 := by
    simpa only [j, min_comm] using (scaled_difference hr.symm)
  have split (u v : ℕ) (hu : i ≤ u) (hv : j ≤ v) :
      x^i*(aeval x P)^j * aeval x (monomialAtPoly P (u-i) (v-j)) = x^u*(aeval x P)^v := by
    simp only [monomialAtPoly, map_mul, map_pow, aeval_X]
    rw [mul_mul_mul_comm, ← pow_add, ← pow_add, Nat.add_sub_of_le hu, Nat.add_sub_of_le hv]
  have he' : aeval x A = aeval x B := by
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero i hx) (pow_ne_zero j hx'))
    rw [show x^i*(aeval x P)^j*aeval x A = _ from split _ _ (min_le_left ..) (min_le_left ..),
        show x^i*(aeval x P)^j*aeval x B = _ from split _ _ (min_le_right ..) (min_le_right ..)]
    exact he
  have degA : A.natDegree = (a.1-i)+(a.2-min a.2 b.2) := (monomialAtPoly_degree hne ..).trans (congrArg _ wa)
  have degB : B.natDegree = (b.1-i)+(b.2-min a.2 b.2) := (monomialAtPoly_degree hne ..).trans (congrArg _ wb)
  have hdeg : max A.natDegree B.natDegree < d := by
    rw [degA, degB]
    have := band_bounds ha
    have := band_bounds hb
    dsimp [i]
    omega
  have eq : A = B := by
    by_contra hn
    have dvd := minpoly.dvd (ZMod 2) x (show aeval x (A-B) = 0 by simpa using sub_eq_zero.mpr he')
    have bound := natDegree_le_of_dvd dvd (sub_ne_zero.mpr hn)
    exact (not_lt_of_ge bound) ((natDegree_sub_le A B).trans_lt (hd ▸ hdeg))
  have hz := congrArg (eval (0 : ZMod 2)) eq
  simp only [A, B, monomialAtPoly, eval_mul, eval_pow, eval_X, hP, one_pow, mul_one] at hz
  have hfirst : a.1 = b.1 := by
    rcases lt_trichotomy a.1 b.1 with h | h | h
    · have hi : i = a.1 := min_eq_left h.le
      simp [hi, zero_pow (by omega : b.1-a.1 ≠ 0)] at hz
    · exact h
    · have hi : i = b.1 := min_eq_right h.le
      simp [hi, zero_pow (by omega : a.1-b.1 ≠ 0)] at hz
  have same := congrArg natDegree eq
  rw [degA, degB, hfirst] at same
  exact Sigma.ext hfirst (heq_of_eq (by omega : a.2 = b.2))

/-- A subgroup containing x and P(x) for a degree-m polynomial with constant term one
has at least three quarters of the square of the field degree divided by m elements. -/
theorem polynomial_plane_order_bound {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (P : BinaryPoly) (hP : P.eval 0 = 1) (hm : 0 < P.natDegree)
    {x : K} {h : ℕ} (hh : 0 < h) (hx : x^h = 1) (hs : (aeval x P)^h = 1) :
    3*(minpoly (ZMod 2) x).natDegree^2 ≤ 4*(P.natDegree*h) := by
  classical
  let m := P.natDegree
  let d := (minpoly (ZMod 2) x).natDegree
  let value (a : Pair) : ℕ × K := (a.2 % m, x^a.1 * (aeval x P)^(a.2/m))
  have hn : x ≠ 0 := by intro he; simp [he, zero_pow hh.ne'] at hx
  have hn' : aeval x P ≠ 0 := by intro he; simp [he, zero_pow hh.ne'] at hs
  have inj : Set.InjOn value (band d) := fun _ ha _ hb he =>
    cancel_poly_band P hP hn hn' rfl ha hb (congrArg Prod.fst he) (congrArg Prod.snd he)
  have subset : (band d).image value ⊆ (range m) ×ˢ (nthRootsFinset h (1 : K)) := by
    intro y hy
    obtain ⟨a, _, rfl⟩ := mem_image.mp hy
    apply mem_product.mpr
    refine ⟨mem_range.mpr (Nat.mod_lt _ hm), (mem_nthRootsFinset hh 1).2 ?_⟩
    change (x^a.1 * (aeval x P)^(a.2/m))^h = 1
    rw [mul_pow, ← pow_mul, Nat.mul_comm a.1 h, pow_mul, hx, one_pow,
        ← pow_mul, Nat.mul_comm (a.2/m) h, pow_mul, hs, one_pow, one_mul]
  have bound := card_le_card subset
  rw [card_image_of_injOn inj, card_product, card_range] at bound
  have roots : (nthRootsFinset h (1 : K)).card ≤ h :=
    Multiset.toFinset_card_le _ |>.trans (card_nthRoots h (1 : K))
  have upper := bound.trans (Nat.mul_le_mul_left m roots)
  simpa [d, m, pow_two, Nat.mul_assoc] using (band_card d).trans (Nat.mul_le_mul_left 4 upper)

/-- The specialization to a binary element and its translate. -/
theorem plane_order_bound {K : Type*} [Field K] [Algebra (ZMod 2) K]
    {x : K} {h : ℕ} (hh : 0 < h) (hx : x^h = 1) (hs : (x+1)^h = 1) :
    3*(minpoly (ZMod 2) x).natDegree^2 ≤ 4*h := by
  have hd : ((X : BinaryPoly)+1).natDegree = 1 := by simpa using (natDegree_X_add_C (1 : ZMod 2))
  have bound := polynomial_plane_order_bound ((X : BinaryPoly)+1) (by simp) (hd ▸ Nat.one_pos)
    hh hx (by simpa using hs)
  rw [hd, one_mul] at bound
  exact bound

/-- The quadratic translate appearing in a three-term progression on one subfield. -/
theorem quadratic_plane_order_bound {K : Type*} [Field K] [Algebra (ZMod 2) K]
    {x : K} {h : ℕ} (hh : 0 < h) (hx : x^h = 1) (hs : (x^2+x+1)^h = 1) :
    3*(minpoly (ZMod 2) x).natDegree^2 ≤ 8*h := by
  let P : BinaryPoly := X^2 + (X+1)
  have hlin : ((X : BinaryPoly)+1).natDegree = 1 := by simpa using (natDegree_X_add_C (1 : ZMod 2))
  have hd : P.natDegree = 2 := by
    dsimp [P]
    rw [natDegree_add_eq_left_of_natDegree_lt (by rw [hlin, natDegree_X_pow]; decide), natDegree_X_pow]
  have hp : (aeval x P)^h = 1 := by simpa [P, add_assoc] using hs
  have bound := polynomial_plane_order_bound P (by simp [P]) (by rw [hd]; decide) hh hx hp
  rw [hd] at bound
  omega

end GF2Sparse.SubfieldProducts
