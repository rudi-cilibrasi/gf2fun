import GF2Sparse.SubfieldProducts
import Mathlib.Data.Nat.Choose.Cast

/-! Arithmetic and Frobenius certificates for the upper bound on a scalar order. -/

namespace GF2Sparse.SubfieldProducts

/-- Count signed triples by their choices of positive and negative coordinates. -/
theorem scalar_ball_count (k : ℕ) :
    12 * (1 + 6*k + 6*k.choose 2 + 6*k^2 + 2*k.choose 3 + 6*k.choose 2*k)
      = 5*(2*k+1)^3 + 7*(2*k+1) := by
  have pair (a : ℕ) : 2 * a.choose 2 + a = a^2 := by
    induction a with
    | zero => simp
    | succ a ih =>
      rw [Nat.choose_succ_succ a 1, Nat.choose_one_right]
      nlinarith
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.choose_succ_succ k 2, Nat.choose_succ_succ k 1, Nat.choose_one_right]
    nlinarith [pair k]

/-- With positive budget k+1 and negative budget k, differences still have
degree at most 2k+1. This is the count for an even field degree. -/
theorem scalar_even_ball_count (k : ℕ) :
    12 * (1 + 3*(k+1) + 3*k + 3*(k+1).choose 2 + 3*k.choose 2 + 6*(k+1)*k
      + (k+1).choose 3 + k.choose 3 + 3*(k+1).choose 2*k + 3*(k+1)*k.choose 2)
      = (2*k+2)*(5*(2*k+2)^2+4) := by
  have pair (a : ℕ) : 2 * a.choose 2 + a = a^2 := by
    induction a with
    | zero => simp
    | succ a ih =>
      rw [Nat.choose_succ_succ a 1, Nat.choose_one_right]
      nlinarith
  rw [Nat.choose_succ_succ k 2, Nat.choose_succ_succ k 1, Nat.choose_one_right]
  nlinarith [scalar_ball_count k, pair k]

/-- The two exponent slopes differ by at most the support width after
multiplication by the larger denominator. -/
theorem scalar_slope_difference {a b c n u v : ℤ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (han : a ≤ n) (hbn : b ≤ n)
    (hcn : c ≤ n) (hu : 0 ≤ u) (huv : u ≤ v) :
    |v*(c-a)-u*(c-b)| ≤ n*v := by
  rw [abs_le]
  have hv : 0 ≤ v := hu.trans huv
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr huv) hc, mul_nonneg hu hb,
      mul_nonneg hv (sub_nonneg.mpr han)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hcn),
      mul_nonneg hu (sub_nonneg.mpr hbn), mul_nonneg hv ha]

/-- Bounds for a linear form on the positive-coordinate part of a signed triple.
Subtracting two values in this interval gives the signed interval. -/
theorem scalar_simplex_interval {a b c lo hi i j l k : ℚ}
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (ha : a ∈ Set.Icc lo hi)
    (hb : b ∈ Set.Icc lo hi) (hc : c ∈ Set.Icc lo hi)
    (hs : i+j+l ≤ k) (h₁ : 0 ≤ i) (h₂ : 0 ≤ j) (h₃ : 0 ≤ l) :
    a*i+b*j+c*l ∈ Set.Icc (k*lo) (k*hi) := by
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr ha.1) h₁, mul_nonneg (sub_nonneg.mpr hb.1) h₂,
      mul_nonneg (sub_nonneg.mpr hc.1) h₃, mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs) hlo]
  · nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) h₁, mul_nonneg (sub_nonneg.mpr hb.2) h₂,
      mul_nonneg (sub_nonneg.mpr hc.2) h₃, mul_nonneg (sub_nonneg.mpr hs) hhi]

/-- If the signed triple count fits in the exponent intervals, its leading
coefficient bounds the scalar independently of the larger degree. -/
theorem scalar_bound_of_count {A p q S : ℕ} (hA : 0 < A) (hq : 0 < q)
    (hc : 12*S = 5*q^3+7*q) (hpack : A*S ≤ q*(p*q)^2) :
    (5*q^2+7)*A ≤ 12*(p*q)^2 ∧ 5*A < 12*p^2 := by
  have aux : q*((5*q^2+7)*A) ≤ q*(12*(p*q)^2) := calc
    q*((5*q^2+7)*A) = A*(5*q^3+7*q) := by ring
    _ = 12*(A*S) := by rw [← hc]; ring
    _ ≤ 12*(q*(p*q)^2) := Nat.mul_le_mul_left _ hpack
    _ = q*(12*(p*q)^2) := by ring
  have hb := Nat.le_of_mul_le_mul_left aux hq
  refine ⟨hb, ?_⟩
  by_contra! bad
  nlinarith [Nat.mul_le_mul_right (q^2) bad]

/-- A composite order cannot fit below the scalar bound if all of its
prime factors are at least 2p+1. -/
theorem prime_scalar_of_bound {A p : ℕ} (ha : 2 ≤ A) (h : 5*A < 12*p^2)
    (hmin : ∀ r : ℕ, r.Prime → r ∣ A → 2*p+1 ≤ r) : A.Prime := by
  by_contra hn
  obtain ⟨a,b,ha',hb',he⟩ := (Nat.not_prime_iff_exists_mul_eq ha).1 hn
  have large (x : ℕ) (hx : x ≠ 1) (hd : x ∣ A) : 2*p+1 ≤ x := by
    have hx0 : x ≠ 0 := by rintro rfl; simp at hd; omega
    obtain ⟨r,hr,hrx⟩ := Nat.exists_prime_and_dvd hx
    exact (hmin r hr (dvd_trans hrx hd)).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hx0) hrx)
  have hla := large a (by rintro rfl; simp at he; omega) (he ▸ dvd_mul_right a b)
  have hlb := large b (by rintro rfl; simp at he; omega) (he ▸ dvd_mul_left b a)
  nlinarith [Nat.mul_le_mul hla hlb]

/-- Positive representatives of a Frobenius exponent give a short binary
polynomial vanishing on any additive pair of h-th roots of unity. -/
theorem scalar_frobenius_residue {K : Type*} [Field K] [CharP K 2] (x : K)
    {t h j : ℕ} (hx : x^h = 1) (hy : (x+1)^h = 1) (ht : t % h = 2^j % h) :
    (x+1)^t = x^t+1 := by
  have reduce (z : K) (hz : z^h = 1) (e : ℕ) : z^e = z^(e%h) := by
    calc z^e = z^(e%h + h*(e/h)) := by rw [Nat.mod_add_div]
         _ = z^(e%h) := by rw [pow_add, pow_mul, hz, one_pow, mul_one]
  calc (x+1)^t = (x+1)^(2^j) := by rw [reduce _ hy t, reduce _ hy (2^j), ht]
       _ = x^(2^j)+1 := by rw [add_pow_expChar_pow, one_pow]
       _ = x^t+1 := by rw [reduce _ hx t, reduce _ hx (2^j), ht]

end GF2Sparse.SubfieldProducts
