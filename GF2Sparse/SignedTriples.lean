import GF2Sparse.TripleRoots
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.Nat.Dist

/-! Three-root exclusions for signed binary degrees 2^s - 2^t - 1. -/

namespace GF2Sparse

open Polynomial Function

private abbrev K := AlgebraicClosure (ZMod 2)
private noncomputable abbrev F (j : ℕ) := iterateFrobenius K 2 j
private noncomputable def phi (x : K) := (x+1)⁻¹

private theorem phi_comm (j : ℕ) (x : K) : F j (phi x) = phi (F j x) := by
  simp [phi]

private theorem phi_three {x : K} (hx : x ≠ 0) (hx1 : x ≠ 1) : phi (phi (phi x)) = x := by
  have hp : x+1 ≠ 0 := fun h => hx1 (CharTwo.add_eq_zero.1 h)
  have hsum : (x+1)⁻¹+1 = x/(x+1) := by
    field_simp
    linear_combination CharTwo.two_eq_zero (R := K)
  have hsum' : (x+1)/x+1 = 1/x := by
    field_simp
    linear_combination x * CharTwo.two_eq_zero (R := K)
  simp only [phi, hsum, inv_div, hsum', one_div, inv_inv]

private theorem periodic_iff (x : K) (k : ℕ) :
    minimalPeriod (frobenius K 2) x ∣ k ↔ F k x = x := by
  rw [← isPeriodicPt_iff_minimalPeriod_dvd]
  exact (congrArg (fun v => v = x) (iterate_frobenius ..)).to_iff

private theorem twisted_cycle {x : K} {h : ℕ} (hx : x ≠ 0) (hx1 : x ≠ 1)
    (ht : F h x = phi x ∨ x = phi (F h x)) : F (3*h) x = x := by
  rw [show 3*h = h+(h+h) by omega, iterateFrobenius_add_apply, iterateFrobenius_add_apply]
  rcases ht with he | he
  · change F h (F h (F h x)) = x
    rw [he, phi_comm, he, phi_comm, phi_comm, he, phi_three hx hx1]
  · have h3 := congrArg (fun v : K => F h (F h (F h v))) (phi_three hx hx1)
    simp only [phi_comm] at h3
    have h2 := (congrArg (F h) he).trans (phi_comm h _)
    have h1 := (congrArg (F h) h2).trans (phi_comm h _)
    exact h3.symm.trans (by rw [← h1, ← h2, ← he])

/-- A Frobenius orbit fixed after m steps cannot contain a point related
by phi at distance h when both integer conditions hold. -/
private theorem twisted_period_impossible {x : K} {m h : ℕ} (hx : x ≠ 0) (hx1 : x ≠ 1)
    (hm : F m x = x) (ht : F h x = phi x ∨ x = phi (F h x))
    (hd : m.gcd (3*h) ∣ h) (ho : (m.gcd h).Coprime 2) : False := by
  have hcycle := twisted_cycle hx hx1 ht
  let d := minimalPeriod (frobenius K 2) x
  have hdm : d ∣ m := (periodic_iff x m).2 hm
  have hdh : d ∣ h := (Nat.dvd_gcd hdm ((periodic_iff x _).2 hcycle)).trans hd
  have hfix := (periodic_iff x h).1 hdh
  simp only [hfix] at ht
  have he : x = phi x := ht.elim id id
  have hxrel : x*(x+1) = 1 := by
    conv_lhs => lhs; rw [he]
    apply inv_mul_cancel₀
    exact fun hz => hx1 (CharTwo.add_eq_zero.1 hz)
  have hf2 : F 2 x = x := by
    change x^4 = x
    linear_combination (x^2-x) * hxrel + (x^2-x) * CharTwo.two_eq_zero (R := K)
  have hd1 : d ∣ 1 := ho.gcd_eq_one ▸ Nat.dvd_gcd (Nat.dvd_gcd hdm hdh) ((periodic_iff x 2).2 hf2)
  have hf1 := (periodic_iff x 1).1 hd1
  change x^2 = x at hf1
  exact hx1 ((mul_left_cancel₀ hx) (by simpa [pow_two] using hf1 : x*x=x*1))

private theorem signed_root_cases {s t i n : ℕ} (hdeg : n+2^t+1 = 2^s) {x y z : K}
    (hx : aeval x (trinomial n (2^i)) = 0) (hy : aeval y (trinomial n (2^i)) = 0)
    (hz : aeval z (trinomial n (2^i)) = 0) (h : x*y*z = 1) :
    (F t x = phi (F i x) ∧ F s x = x) ∨ (x = phi (F i x) ∧ F s x = F t x) := by
  have root_eq (v : K) (hv : aeval v (trinomial n (2^i)) = 0) : v^n = F i v+1 := by
    simpa only [trinomial, map_add, map_pow, aeval_X, map_one, CharTwo.add_eq_zero] using hv
  have top_eq (v : K) (hv : aeval v (trinomial n (2^i)) = 0) :
      F s v = F t v*v*(F i v+1) := by
    change v^(2^s) = _
    rw [← hdeg, pow_succ, pow_add, root_eq v hv]
    change _ = v^(2^t)*v*(F i v+1)
    ring
  have hp (k : ℕ) : x^k*y^k*z^k=1 := by rw [← mul_pow, ← mul_pow, h, one_pow]
  have ht := hp n
  rw [root_eq x hx, root_eq y hy, root_eq z hz] at ht
  obtain ⟨v, hv, hpair⟩ : ∃ v : K, aeval v (trinomial n (2^i)) = 0 ∧ v*(x+1)=1 := by
    have lift_orbit (v : K) (ho : F i v*(F i x+1)=1) : v*(x+1)=1 := by
      apply iterateFrobenius_inj K 2 i
      simpa using ho
    rcases triple_translate_orbit (hp (2^i)) ht with ho | ho
    · exact ⟨y, hy, lift_orbit y ho⟩
    · exact ⟨z, hz, lift_orbit z ho⟩
  have hden (k : ℕ) : F k x+1 ≠ 0 := by
    have hh := congrArg (F k) hpair
    simp only [map_mul, map_add, map_one] at hh
    exact fun he => by rw [he, mul_zero] at hh; exact zero_ne_one hh
  have hvphi : v = phi x := by
    apply (eq_div_iff (by simpa using hden 0 : x+1 ≠ 0)).2 at hpair
    simpa [phi] using hpair
  have htrans := top_eq v hv
  rw [hvphi, phi_comm, phi_comm, phi_comm] at htrans
  dsimp only [phi] at htrans
  have hxden : x+1 ≠ 0 := by simpa using hden 0
  field_simp [hden, hxden] at htrans
  have htop := top_eq x hx
  rw [htop] at htrans
  have hzfac : (F t x*(F i x+1)+1)*(x*(F i x+1)+1)=0 := by
    rw [show 1+(F i x+1) = F i x by
      rw [add_comm 1 _, add_assoc, CharTwo.add_self_eq_zero, add_zero]] at htrans
    linear_combination htrans + (F i x)*(F i x+1)*(F t x)*x*CharTwo.two_eq_zero (R := K)
  have to_phi (v : K) (hv : v*(F i x+1)+1=0) : v = phi (F i x) := by
    have ho := CharTwo.add_eq_zero.1 hv
    simpa [phi] using (eq_div_iff (hden i)).2 ho
  rcases mul_eq_zero.1 hzfac with hl | hr
  · refine Or.inl ⟨to_phi _ hl, ?_⟩
    rw [htop, mul_right_comm, CharTwo.add_eq_zero.1 hl, one_mul]
  · exact Or.inr ⟨to_phi _ hr, by rw [htop, mul_assoc, CharTwo.add_eq_zero.1 hr, mul_one]⟩

/-- The two arithmetic conditions exclude a Frobenius shift by h related
to the order-three fractional linear map, on points fixed after m steps. -/
def excludesTwistedPeriod (m h : ℕ) : Prop := m.gcd (3*h) ∣ h ∧ (m.gcd h).Coprime 2

instance (m h : ℕ) : Decidable (excludesTwistedPeriod m h) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem twist_of_shifted_product {i b : ℕ} {x : K}
    (hp : x^(2^i)*(x^(2^b)+1) = 1) :
    F (i.dist b) x = phi x ∨ x = phi (F (i.dist b) x) := by
  have hd : F b x + 1 ≠ 0 := by
    rintro hz
    change F i x * (F b x+1) = 1 at hp
    simp [hz] at hp
  have hrel : F i x = phi (F b x) := by
    simpa [phi] using (eq_div_iff hd).2 hp
  rcases le_total i b with hle | hle
  · rw [Nat.dist_eq_sub_of_le hle]
    right
    apply iterateFrobenius_inj K 2 i
    rw [phi_comm, ← iterateFrobenius_add_apply, Nat.add_sub_of_le hle]
    exact hrel
  · rw [Nat.dist_eq_sub_of_le_right hle]
    left
    apply iterateFrobenius_inj K 2 b
    rw [← iterateFrobenius_add_apply, Nat.add_sub_of_le hle, phi_comm]
    exact hrel

/-- A product equation relating two Frobenius shifts confines x to the
field fixed after three times their distance. -/
theorem shifted_product_frobenius_cycle {i b : ℕ} {x : AlgebraicClosure (ZMod 2)}
    (hx : x ≠ 0) (hx1 : x ≠ 1) (hp : x^(2^i)*(x^(2^b)+1) = 1) :
    x^(2^(3*i.dist b)) = x :=
  twisted_cycle hx hx1 (twist_of_shifted_product hp)

/-- A point in the degree-m field cannot satisfy the shifted product equation
when the coprimality and divisibility tests exclude an order-three shift. -/
theorem excludesTwistedPeriod.no_shifted_product {m i b : ℕ}
    (he : excludesTwistedPeriod m (i.dist b)) {x : AlgebraicClosure (ZMod 2)}
    (hx : x ≠ 0) (hx1 : x ≠ 1) (hm : x^(2^m) = x) :
    x^(2^i)*(x^(2^b)+1) ≠ 1 := by
  intro hp
  exact twisted_period_impossible hx hx1 hm (twist_of_shifted_product hp) he.1 he.2

/-- The two integer tests suffice for the signed degree 2^s-2^t-1. -/
theorem signed_dyadic_no_root_triple {s t i n : ℕ} (hts : t ≤ s) (hn : n+2^t+1 = 2^s)
    (hfirst : excludesTwistedPeriod s (i.dist t)) (hsecond : excludesTwistedPeriod (s-t) i) :
    NoRootTriple (trinomial n (2^i)) := by
  intro x y z hx hy hz h
  have hx0 : x ≠ 0 := by rintro rfl; simp at h
  have hx1 : x ≠ 1 := by rintro rfl; simp [trinomial, CharTwo.add_self_eq_zero] at hx
  rcases signed_root_cases hn hx hy hz h with ⟨ht, hs⟩ | ⟨hi, hs⟩
  · apply twisted_period_impossible hx0 hx1 hs _ hfirst.1 hfirst.2
    rcases le_total i t with hle | hle
    · rw [Nat.dist_eq_sub_of_le hle]
      left
      apply iterateFrobenius_inj K 2 i
      rw [← iterateFrobenius_add_apply, Nat.add_sub_of_le hle, phi_comm, ht]
    · rw [Nat.dist_eq_sub_of_le_right hle]
      right
      apply iterateFrobenius_inj K 2 t
      rw [phi_comm, ← iterateFrobenius_add_apply, Nat.add_sub_of_le hle, ht]
  · apply twisted_period_impossible hx0 hx1 _ (Or.inr hi) hsecond.1 hsecond.2
    apply iterateFrobenius_inj K 2 t
    rw [← iterateFrobenius_add_apply, Nat.add_sub_of_le hts, hs]

set_option exponentiation.threshold 1024 in
/-- A normalized squarefree trinomial in a degree with 999 binary ones. -/
theorem signed_example_1000_500 :
    NoRootTriple (trinomial (2^1000-2^500-1) 2) :=
  signed_dyadic_no_root_triple (s := 1000) (t := 500) (i := 1)
    (by decide) (by
      have h : (2:ℕ)^500 < 2^1000 := Nat.pow_lt_pow_right (by decide) (by decide)
      rw [Nat.add_right_comm, Nat.sub_add_cancel (Nat.sub_pos_of_lt h), Nat.sub_add_cancel h.le])
    (by decide) (by decide)

end GF2Sparse
