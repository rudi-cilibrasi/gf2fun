import GF2Sparse.SubfieldProducts

/-! A subgroup containing an element and its translate has size at least three quarters of its field degree squared. -/

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

private noncomputable def monomialAtTwoPoints (i j : ℕ) : BinaryPoly := X^i * (X+1)^j

private theorem twoPoint_degree (i j : ℕ) : (monomialAtTwoPoints i j).natDegree = i+j := by
  have h : ((X : BinaryPoly)+1).natDegree = 1 := by simpa using (natDegree_X_add_C (1 : ZMod 2))
  have hn : (X : BinaryPoly)+1 ≠ 0 := by intro he; simp [he] at h
  simp [monomialAtTwoPoints, natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hn),
    natDegree_pow, h]

private theorem cancel_band {K : Type*} [Field K] [Algebra (ZMod 2) K] {x : K}
    (hx : x ≠ 0) (hx' : x+1 ≠ 0) {d : ℕ} (hd : d = (minpoly (ZMod 2) x).natDegree)
    {a b : Pair} (ha : a ∈ band d) (hb : b ∈ band d)
    (he : x^a.1*(x+1)^a.2 = x^b.1*(x+1)^b.2) : a = b := by
  let i := min a.1 b.1
  let j := min a.2 b.2
  let A := monomialAtTwoPoints (a.1-i) (a.2-j)
  let B := monomialAtTwoPoints (b.1-i) (b.2-j)
  have split (u v : ℕ) (hu : i ≤ u) (hv : j ≤ v) :
      x^i*(x+1)^j * aeval x (monomialAtTwoPoints (u-i) (v-j)) = x^u*(x+1)^v := by
    simp only [monomialAtTwoPoints, map_mul, map_pow, map_add, aeval_X, map_one]
    rw [mul_mul_mul_comm, ← pow_add, ← pow_add, Nat.add_sub_of_le hu, Nat.add_sub_of_le hv]
  have he' : aeval x A = aeval x B := by
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero i hx) (pow_ne_zero j hx'))
    rw [show x^i*(x+1)^j*aeval x A = _ from split _ _ (min_le_left ..) (min_le_left ..),
      show x^i*(x+1)^j*aeval x B = _ from split _ _ (min_le_right ..) (min_le_right ..)]
    exact he
  have ba := band_bounds ha
  have bb := band_bounds hb
  have hdeg : max A.natDegree B.natDegree < d := by
    simp only [A, B, twoPoint_degree, i, j]
    omega
  have eq : A = B := by
    by_contra hn
    have dvd := minpoly.dvd (ZMod 2) x (show aeval x (A-B) = 0 by simpa using sub_eq_zero.mpr he')
    have bound := natDegree_le_of_dvd dvd (sub_ne_zero.mpr hn)
    exact (not_lt_of_ge bound) ((natDegree_sub_le A B).trans_lt (hd ▸ hdeg))
  have hz := congrArg (eval (0 : ZMod 2)) eq
  simp only [A, B, monomialAtTwoPoints, eval_mul, eval_pow, eval_X, eval_add, eval_one,
    zero_add, one_pow, mul_one] at hz
  have hfirst : a.1 = b.1 := by
    rcases lt_trichotomy a.1 b.1 with h | h | h
    · have hi : i = a.1 := min_eq_left h.le
      have hp : b.1-i ≠ 0 := by omega
      simp [hi, zero_pow (by omega : b.1-a.1 ≠ 0)] at hz
    · exact h
    · have hi : i = b.1 := min_eq_right h.le
      simp [hi, zero_pow (by omega : a.1-b.1 ≠ 0)] at hz
  have same := congrArg natDegree eq
  simp only [A, B, twoPoint_degree] at same
  have hsecond : a.2 = b.2 := by dsimp [j] at same; omega
  exact Sigma.ext hfirst (heq_of_eq hsecond)

/-- The same subgroup contains all the distinct values x^i (x+1)^j in a diagonal band. -/
theorem plane_order_bound {K : Type*} [Field K] [Algebra (ZMod 2) K]
    {x : K} {h : ℕ} (hh : 0 < h) (hx : x^h = 1) (hs : (x+1)^h = 1) :
    3*(minpoly (ZMod 2) x).natDegree^2 ≤ 4*h := by
  classical
  let d := (minpoly (ZMod 2) x).natDegree
  let value (a : Pair) := x^a.1*(x+1)^a.2
  have hn : x ≠ 0 := by intro he; simp [he, zero_pow hh.ne'] at hx
  have hn' : x+1 ≠ 0 := by intro he; simp [he, zero_pow hh.ne'] at hs
  have inj : Set.InjOn value (band d) := fun _ ha _ hb he => cancel_band hn hn' rfl ha hb he
  have subset : (band d).image value ⊆ nthRootsFinset h (1 : K) := by
    intro y hy
    obtain ⟨a, _, rfl⟩ := mem_image.mp hy
    apply (mem_nthRootsFinset hh 1).2
    simp only [value, mul_pow]
    rw [← pow_mul, Nat.mul_comm a.1 h, pow_mul, hx, one_pow,
        ← pow_mul, Nat.mul_comm a.2 h, pow_mul, hs, one_pow, one_mul]
  have bound := (card_le_card subset).trans ((Multiset.toFinset_card_le _).trans (card_nthRoots h (1 : K)))
  rw [card_image_of_injOn inj] at bound
  simpa [d, pow_two, Nat.mul_assoc] using (band_card d).trans (Nat.mul_le_mul_left 4 bound)

end GF2Sparse.SubfieldProducts
