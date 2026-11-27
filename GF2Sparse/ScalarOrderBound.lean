import GF2Sparse.MersenneDivisors
import GF2Sparse.Progressions
import GF2Sparse.SubfieldProducts
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.NumberTheory.Multiplicity

/-! Arithmetic and Frobenius certificates for the upper bound on a scalar order. -/

namespace GF2Sparse.SubfieldProducts

private theorem twice_choose_two (a : ℕ) : 2 * a.choose 2 + a = a^2 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.choose_succ_succ a 1, Nat.choose_one_right]
    nlinarith

/-- Count signed triples by their choices of positive and negative coordinates. -/
theorem scalar_ball_count (k : ℕ) :
    12 * (1 + 6*k + 6*k.choose 2 + 6*k^2 + 2*k.choose 3 + 6*k.choose 2*k)
      = 5*(2*k+1)^3 + 7*(2*k+1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.choose_succ_succ k 2, Nat.choose_succ_succ k 1, Nat.choose_one_right]
    nlinarith [twice_choose_two k]

/-- With positive budget k+1 and negative budget k, differences still have
degree at most 2k+1. This is the count for an even field degree. -/
theorem scalar_even_ball_count (k : ℕ) :
    12 * (1 + 3*(k+1) + 3*k + 3*(k+1).choose 2 + 3*k.choose 2 + 6*(k+1)*k
      + (k+1).choose 3 + k.choose 3 + 3*(k+1).choose 2*k + 3*(k+1)*k.choose 2)
      = (2*k+2)*(5*(2*k+2)^2+4) := by
  rw [Nat.choose_succ_succ k 2, Nat.choose_succ_succ k 1, Nat.choose_one_right]
  nlinarith [scalar_ball_count k, twice_choose_two k]

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

/-- A three-position window bounds the partner degree when the signed
triples fit in exponent intervals of total length at most j*n*W. -/
theorem scalar_triple_width_bound {i j W S : ℕ} (hj : 0 < j)
    (hc : 12*S = 5*j^3+7*j) (hpack : S ≤ j*(i*j)*W) : 5*j < 12*i*W := by
  by_contra! bad
  nlinarith [Nat.mul_le_mul_right (j^2) bad]

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

/-- Once the Frobenius gap ratio reaches eight, the outer polynomial of
the Laurent composition is reducible. -/
theorem dyadic_outer_reducible (k : ℕ) (hk : 3 ≤ k) :
    ¬Irreducible ((Polynomial.X : BinaryPoly)^(2^k) + Polynomial.X + 1) := by
  open Polynomial in
  let f : BinaryPoly := X^(2^k)+X+1
  have hgt (n : ℕ) (hn : 3 ≤ n) : 2*n < 2^n := by
    induction n, hn using Nat.le_induction with
    | base => decide
    | succ n hn ih => rw [pow_succ]; omega
  have hdeg : f.natDegree = 2^k := by
    have hsmall : 1 < 2^k := by have := hgt k hk; omega
    dsimp [f]
    rw [add_assoc, Polynomial.natDegree_add_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
    calc _ ≤ max (Polynomial.X : BinaryPoly).natDegree (1 : BinaryPoly).natDegree :=
           Polynomial.natDegree_add_le _ _
         _ = 1 := by simp
         _ < _ := by simpa only [Polynomial.natDegree_X_pow] using hsmall
  have hid : f^(2^k)+f = (Polynomial.X : BinaryPoly)^(2^(k+k))-Polynomial.X := by
    dsimp [f]
    rw [add_pow_expChar_pow, add_pow_expChar_pow, one_pow, ← pow_mul, pow_add]
    rw [CharTwo.sub_eq_add]
    linear_combination (Polynomial.X^(2^k)+1) * (CharTwo.two_eq_zero (R := BinaryPoly))
  intro hi
  have hdvd : f ∣ (Polynomial.X : BinaryPoly)^(Nat.card (ZMod 2))^(k+k)-Polynomial.X := by
    rw [Nat.card_zmod, ← hid]
    exact dvd_add (dvd_pow_self f (by positivity)) (dvd_refl f)
  have bound := Nat.le_of_dvd (by omega : 0 < k+k)
    (hi.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd)
  change f.natDegree ≤ k+k at bound
  rw [hdeg] at bound
  have := hgt k hk
  omega

/-- For coprime Frobenius indices the only common nonzero fixed point is one. -/
theorem coprime_frobenius_fixed_eq_one {F : Type*} [Field F] {x : F} (hx : x ≠ 0)
    {k n : ℕ} (hc : n.Coprime k) (hn : x^(2^n) = x) (hk : x^(2^k) = x) : x = 1 := by
  have divides (a : ℕ) (h : x^(2^a) = x) : orderOf x ∣ 2^a-1 := by
    apply orderOf_dvd_of_pow_eq_one
    apply mul_right_cancel₀ hx
    rw [← pow_succ, Nat.sub_add_cancel (Nat.two_pow_pos a), h, one_mul]
  have hd := Nat.dvd_gcd (divides n hn) (divides k hk)
  rw [Nat.pow_sub_one_gcd_pow_sub_one, hc.gcd_eq_one] at hd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

/-- A normalized Frobenius triple escapes the binary plane generated by its
first two entries in odd degree when the indices are coprime. -/
theorem frobenius_triple_escapes_plane {F : Type*} [Field F] [CharP F 2]
    {x : F} (hx : x ≠ 0) (hx1 : x ≠ 1) {k n : ℕ} (hc : n.Coprime k)
    (ho : Odd n) (hn : x^(2^n) = x) :
    x^(2^k) ∉ ({0, 1, x, x+1} : Set F) := by
  have hi := (iterateFrobenius F 2 k).injective
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (h | h | h | h)
  · exact (pow_ne_zero _ hx) h
  · exact hx1 (hi (by simpa only [map_one, iterateFrobenius_def] using h :
      iterateFrobenius F 2 k x = iterateFrobenius F 2 k 1))
  · exact hx1 (coprime_frobenius_fixed_eq_one hx hc hn h)
  · exact no_dyadic_translate n k ho x hn (by rw [h]; ring_nf; simp [CharTwo.two_eq_zero (R := F)])

/-- If a nonconstant geometric triple lies in a binary plane, its common
ratio has order three. -/
theorem geometric_triple_cube {F : Type*} [Field F] [CharP F 2] {z : F}
    (hz : z ≠ 0) (h1 : z ≠ 1) (hp : z^2 ∈ ({0, 1, z, z+1} : Set F)) : z^3 = 1 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with h | h | h | h
  · exact ((pow_ne_zero _ hz) h).elim
  · apply False.elim ∘ h1
    apply (frobenius F 2).injective
    simpa only [map_one, frobenius_def] using h
  · exact (h1 (mul_left_cancel₀ hz (by simpa [sq] using h : z*z=z*1))).elim
  · calc z^3 = z*(z+1) := by rw [← h]; ring
         _ = z^2+z := by ring
         _ = 1 := by rw [h]; ring_nf; simp [CharTwo.two_eq_zero (R := F)]

/-- The exact binary degree of a root of unity of order 3^(a+1). -/
theorem three_power_divides_mersenne_iff (a n : ℕ) :
    3^(a+1) ∣ 2^n-1 ↔ 2*3^a ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ho
  · have he : n = 2*m := by omega
    have hm0 : m ≠ 0 := by omega
    have hsub : 4^m-1 ≠ 0 := by
      have : 1 < 4^m := one_lt_pow₀ (by decide) hm0
      omega
    have hval := padicValNat.pow_sub_pow (p := 3) (by decide : Odd 3) (by decide : 1 < 4)
      (by decide : 3 ∣ 4-1) (by decide : ¬3 ∣ 4) hm0
    simp only [one_pow, show padicValNat 3 (4-1) = 1 from padicValNat.self (by decide : 1 < 3)] at hval
    rw [he, pow_mul, show (2:ℕ)^2 = 4 by decide, Nat.mul_dvd_mul_iff_left (by decide : 0 < 2),
      padicValNat_dvd_iff_le hsub, padicValNat_dvd_iff_le hm0, hval]
    omega
  · have h3 := Nat.prime_three.coprime_iff_not_dvd.mp ((mersenne_coprime_three_iff_odd n).2 ho).symm
    have h2 : ¬2 ∣ n := fun h => Nat.not_even_iff_odd.mpr ho (even_iff_two_dvd.mpr h)
    exact iff_of_false (fun h => h3 (dvd_trans (dvd_pow_self 3 (by omega : a+1 ≠ 0)) h))
      (fun h => h2 (dvd_trans (dvd_mul_right 2 _) h))

/-- An odd-prime divisor of k+1 eliminates k*t+1 whenever t is one modulo that divisor. -/
theorem progression_candidate_not_prime {k t r : ℕ} (hr : 1 < r) (hd : r ∣ k+1)
    (hlt : r < k*t+1) (ht : t ≡ 1 [MOD r]) : ¬ (k*t+1).Prime := by
  have hmod : k*t+1 ≡ k+1 [MOD r] := by simpa using (ht.mul_left k).add_right 1
  have hdiv := Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr hd))
  intro hp
  rcases (Nat.dvd_prime hp).mp hdiv with h | h <;> omega

/-- Fermat's congruence eliminates a candidate for every multiple of r-1. -/
theorem progression_candidate_not_prime_of_period {k q b r : ℕ} (hr : r.Prime)
    (hc : q.Coprime r) (hd : r ∣ k+1) (hb : r-1 ∣ b) (hlt : r < k*q^b+1) :
    ¬ (k*q^b+1).Prime := by
  apply progression_candidate_not_prime hr.one_lt hd hlt
  obtain ⟨j, rfl⟩ := hb
  rw [pow_mul]
  have h := Nat.ModEq.pow_totient hc
  rw [Nat.totient_prime hr] at h
  simpa using h.pow j

/-- For a degree coprime to six, the two smallest candidate multipliers leave only
2z+1, and only in one residue class. -/
theorem two_four_mersenne_candidates {z ell : ℕ} (hz : 1 < z) (ho : Odd z) (h3 : ¬ 3 ∣ z)
    (hp : ell.Prime) (hd : ell ∣ 2^z-1) (hc : ell = 2*z+1 ∨ ell = 4*z+1) :
    z % 12 = 11 ∧ ell = 2*z+1 := by
  have h8 := odd_mersenne_prime_mod_eight ho hp hd
  obtain ⟨t, ht⟩ := ho
  rcases hc with rfl | rfl
  · have hnot : ¬ 3 ∣ 2*z+1 := by
      intro h
      rcases (Nat.dvd_prime hp).mp h with h | h <;> omega
    have hlt := Nat.mod_lt z (by decide : 0 < 12)
    constructor
    · interval_cases residue : z % 12 <;> omega
    · rfl
  · omega

/-- Exact binary degree of a root of order 31^(b+1), realizing the ramified exception. -/
theorem thirty_one_power_divides_mersenne_iff (b n : ℕ) :
    31^(b+1) ∣ 2^n-1 ↔ 5*31^b ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  by_cases h5 : 5 ∣ n
  · obtain ⟨m, rfl⟩ := h5
    have hm : m ≠ 0 := by omega
    have hsub : 32^m-1 ≠ 0 := by
      have : 1 < 32^m := one_lt_pow₀ (by decide) hm
      omega
    letI : Fact (Nat.Prime 31) := ⟨by decide⟩
    have hv := padicValNat.pow_sub_pow (p := 31) (by decide : Odd 31) (by decide : 1 < 32)
      (by decide : 31 ∣ 32-1) (by decide : ¬ 31 ∣ 32) hm
    simp only [one_pow, show padicValNat 31 (32-1) = 1 from padicValNat.self (by decide : 1 < 31)] at hv
    rw [pow_mul, show (2:ℕ)^5 = 32 by decide, Nat.mul_dvd_mul_iff_left (by decide : 0 < 5),
      padicValNat_dvd_iff_le hsub, padicValNat_dvd_iff_le hm, hv]
    omega
  · have no : ¬ 31 ∣ 2^n-1 := by
      intro h
      have hz := (ZMod.natCast_eq_zero_iff (2^n-1) 31).2 h
      rw [Nat.cast_sub (Nat.two_pow_pos n), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
        sub_eq_zero] at hz
      have hd := orderOf_dvd_of_pow_eq_one (show (2 : ZMod 31)^5 = 1 by decide)
      have ho : orderOf (2 : ZMod 31) = 5 :=
        ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd).resolve_left
          (fun h => (by decide : (2 : ZMod 31) ≠ 1) (orderOf_eq_one_iff.mp h))
      exact h5 (ho ▸ orderOf_dvd_of_pow_eq_one hz)
    exact iff_of_false (fun h => no (dvd_trans (dvd_pow_self 31 (by omega : b+1 ≠ 0)) h))
      (fun h => h5 (dvd_trans (dvd_mul_right 5 _) h))

end GF2Sparse.SubfieldProducts
