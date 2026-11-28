import GF2Sparse.SafePrimePowers

/-! Numerical bounds for low-order sparse supports and the order-91 dilations. -/

namespace GF2Sparse

/-- Combining the progression packing bound with the singleton span bounds
the degree by a constant independent of the progression width. -/
theorem circuit_degree_bound {n r j h : ℕ} (hn : 0 < n) (hj : 2 ≤ j)
    (hpack : n^3 ≤ 2*j*r^2) (hspan : j*r ≤ h*n) : n ≤ h^2 := by
  have hp : (j*n)*n^2 ≤ (2*h^2)*n^2 := by
    calc
      _ = j*n^3 := by ring
      _ ≤ j*(2*j*r^2) := Nat.mul_le_mul_left _ hpack
      _ = 2*(j*r)^2 := by ring
      _ ≤ 2*(h*n)^2 := by gcongr
      _ = _ := by ring
  have hcancel := Nat.le_of_mul_le_mul_right hp (pow_pos hn 2)
  nlinarith [Nat.mul_le_mul_right n hj]

/-- An upper bound on normalized root order and the four-dimensional packing
bound give an upper bound on normalized degree. -/
theorem pentanomial_linear_order_bound {n r c : ℕ} (hn : 0 < n)
    (hpack : 5*n^4 ≤ 16*r^3) (horder : r ≤ c*n) : 5*n ≤ 16*c^3 := by
  refine Nat.le_of_mul_le_mul_right (show (5*n)*n^3 ≤ (16*c^3)*n^3 from ?_) (pow_pos hn 3)
  calc
    _ = 5*n^4 := by ring
    _ ≤ 16*r^3 := hpack
    _ ≤ 16*(c*n)^3 := by gcongr
    _ = _ := by ring

/-- Every iterated seventh root of an order-91 element has the indicated
orders both before and after raising it to the 13th power. -/
theorem order_13th_power_dilations {M : Type*} [Monoid M] (z : M) (j : ℕ)
    (h : orderOf (z^(7^j)) = 91) :
    orderOf z = 91*7^j ∧ orderOf (z^13) = 7^(j+1) := by
  have hz := order_of_iterated_root (d := 7) (by decide) (by decide : 7 ∣ 91) j z h
  refine ⟨hz, ?_⟩
  have hd : 13 ∣ orderOf z := hz ▸ dvd_mul_of_dvd_left (by decide : 13 ∣ 91) _
  rw [orderOf_pow_of_dvd (by decide) hd, hz, show 91 = 7*13 by decide,
    Nat.mul_right_comm, Nat.mul_div_cancel _ (by decide : 0 < 13), pow_succ']


/-- The consecutive-element packing and the three singleton positions give a
degree bound in terms of the fixed field parameters t and h. -/
theorem consecutive_degree_bound {δ t h k : ℕ} (hδ : 0 < δ)
    (hpack : 3*δ^2 ≤ 4*h*k) (hspan : 2*k ≤ t*δ) : 3*(t*δ) ≤ 2*h*t^2 := by
  have hm : (3*δ)*δ ≤ (2*h*t)*δ := by
    calc
      _ = 3*δ^2 := by ring
      _ ≤ 4*h*k := hpack
      _ = (2*h)*(2*k) := by ring
      _ ≤ (2*h)*(t*δ) := Nat.mul_le_mul_left _ hspan
      _ = _ := by ring
  have hc := Nat.mul_le_mul_left t (Nat.le_of_mul_le_mul_right hm hδ)
  nlinarith

/-- The orders before and after the 41st power of an iterated 31st root. -/
theorem order_41st_power_dilations {M : Type*} [Monoid M] (z : M) (j : ℕ)
    (h : orderOf (z^(31^j)) = 1271) :
    orderOf z = 1271*31^j ∧ orderOf (z^41) = 31^(j+1) := by
  have hz := order_of_iterated_root (d := 31) (by decide) (by decide : 31 ∣ 1271) j z h
  refine ⟨hz, ?_⟩
  have hd : 41 ∣ orderOf z := hz ▸ dvd_mul_of_dvd_left (by decide : 41 ∣ 1271) _
  rw [orderOf_pow_of_dvd (by decide) hd, hz, show 1271 = 31*41 by decide,
    Nat.mul_right_comm, Nat.mul_div_cancel _ (by decide : 0 < 41), pow_succ']

/-- The finite order range for the classification at sixteen times the degree. -/
theorem order_sixteen_cutoff {n r : ℕ} (hn : 0 < n) (hpack : 5*n^4 ≤ 16*r^3)
    (hr : r ≤ 16*n) : n ≤ 13107 ∧ r ≤ 209715 := by
  have h := pentanomial_linear_order_bound hn hpack hr
  norm_num at h
  omega

/-- A proper subfield of degree at least eleven is already too large
for the prime-index exceptions when the ambient degree is at most its square. -/
theorem subfield_size_gt_sixteen_square (d : ℕ) (hd : 11 ≤ d) :
    16*d^2 + 1 < 2^d := by
  induction d, hd using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ 2 k]
    nlinarith [Nat.mul_le_mul_left k hk]

theorem order_sixteen_composite_cutoff {d n : ℕ} (hn : n ≤ d^2)
    (hsmall : 2^d ≤ 16*n+1) : n ≤ 100 := by
  by_cases hd : 11 ≤ d
  · have h := subfield_size_gt_sixteen_square d hd
    omega
  · have hle : d ≤ 10 := by omega
    have hpow : d^2 ≤ 10^2 := by gcongr
    omega

/-- Packing at the rational endpoint 127/7 bounds both variables in the finite census. -/
theorem order_127_sevenths_cutoff {n r : ℕ} (hn : 0 < n) (hpack : 5*n^4 ≤ 16*r^3)
    (hr : 7*r ≤ 127*n) : n ≤ 19110 ∧ r ≤ 346715 := by
  have hcancel : (5*7^3*n)*n^3 ≤ (16*127^3)*n^3 := by
    calc
      _ = 7^3*(5*n^4) := by ring
      _ ≤ 7^3*(16*r^3) := Nat.mul_le_mul_left _ hpack
      _ = 16*(7*r)^3 := by ring
      _ ≤ 16*(127*n)^3 := by gcongr
      _ = _ := by ring
  have hb := Nat.le_of_mul_le_mul_right hcancel (pow_pos hn 3)
  norm_num at hb
  omega

/-- A prime-index subgroup of size at most 300 times the ambient composite
degree forces the largest proper subfield degree to be at most sixteen. -/
theorem subfield_size_gt_three_hundred_square (d : ℕ) (hd : 17 ≤ d) :
    300*d^2 + 1 < 2^d := by
  induction d, hd using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ 2 k]
    nlinarith [Nat.mul_le_mul_left k hk]

theorem order_three_hundred_composite_cutoff {d n : ℕ} (hn : n ≤ d^2)
    (hsmall : 2^d ≤ 300*n+1) : n ≤ 256 := by
  by_cases hd : 17 ≤ d
  · have h := subfield_size_gt_three_hundred_square d hd
    omega
  · have hle : d ≤ 16 := by omega
    have hpow : d^2 ≤ 16^2 := by gcongr
    omega

end GF2Sparse
