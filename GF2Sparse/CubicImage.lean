import GF2Sparse.Progressions

/-! The polynomial of cubed roots from the three residue classes of exponents. -/

namespace GF2Sparse.CubicImage
open Polynomial

noncomputable def source (a b c : BinaryPoly) : BinaryPoly :=
  expand (ZMod 2) 3 a + X * expand (ZMod 2) 3 b + X^2 * expand (ZMod 2) 3 c

noncomputable def image (a b c : BinaryPoly) : BinaryPoly :=
  a^3 + X*b^3 + X^2*c^3 + X*a*b*c

theorem source_dvd_expand_image (a b c : BinaryPoly) :
    source a b c ∣ expand (ZMod 2) 3 (image a b c) := by
  let u := expand (ZMod 2) 3 a
  let v := X * expand (ZMod 2) 3 b
  let w := X^2 * expand (ZMod 2) 3 c
  refine ⟨u^2 + v^2 + w^2 - u*v - v*w - w*u, ?_⟩
  have hthree : (3 : BinaryPoly) = -1 := by
    have htwo : (2 : BinaryPoly) = 0 := CharP.cast_eq_zero _ 2
    calc
      (3 : BinaryPoly) = 2 + 2 - 1 := by norm_num
      _ = -1 := by rw [htwo]; ring
  calc
    _ = u^3 + v^3 + w^3 - 3*u*v*w := by
      simp only [image, map_add, map_mul, map_pow, expand_X, u, v, w, hthree]
      ring
    _ = _ := by change _ = (u+v+w)*_; ring

/-- Cubing a root gives a root of the displayed polynomial in every binary extension. -/
theorem aeval_cube {K : Type*} [Field K] [Algebra (ZMod 2) K]
    (a b c : BinaryPoly) {x : K} (hx : aeval x (source a b c) = 0) :
    aeval (x^3) (image a b c) = 0 := by
  obtain ⟨q, hq⟩ := source_dvd_expand_image a b c
  rw [← expand_aeval, hq, map_mul, hx, zero_mul]

private noncomputable def weight (i : ℕ) (a : BinaryPoly) : ℕ :=
  if a = 0 then 0 else a.natDegree*3+i

private theorem degree_add (p q : BinaryPoly)
    (h : p ≠ 0 → q ≠ 0 → p.natDegree ≠ q.natDegree) :
    (p+q).natDegree = max p.natDegree q.natDegree := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  rcases lt_or_gt_of_ne (h hp hq) with hl | hl
  · rw [natDegree_add_eq_right_of_natDegree_lt hl, max_eq_right hl.le]
  · rw [natDegree_add_eq_left_of_natDegree_lt hl, max_eq_left hl.le]

private theorem parts_degree (a b c : BinaryPoly) (T : BinaryPoly → BinaryPoly)
    (hzero : T 0 = 0) (hne : ∀ p ≠ 0, T p ≠ 0) (hdeg : ∀ p, (T p).natDegree = p.natDegree*3) :
    (T a + X*T b + X^2*T c).natDegree = max (max (weight 0 a) (weight 1 b)) (weight 2 c) := by
  let part (i : ℕ) (p : BinaryPoly) := X^i * T p
  have hw (i : ℕ) (p : BinaryPoly) : (part i p).natDegree = weight i p := by
    by_cases hp : p = 0
    · simp [part, weight, hp, hzero]
    · simp [part, weight, hp, natDegree_X_pow_mul i (hne p hp), hdeg]
  have residue {i : ℕ} (p : BinaryPoly) (hi : i < 3) (h : part i p ≠ 0) :
      (part i p).natDegree % 3 = i := by
    have hp : p ≠ 0 := fun he => h (by simp [part, he, hzero])
    rw [hw, weight, if_neg hp]
    omega
  let p := part 0 a
  let q := part 1 b
  let r := part 2 c
  have hp (h : p ≠ 0) : p.natDegree % 3 = 0 := residue a (by decide : 0 < 3) h
  have hq (h : q ≠ 0) : q.natDegree % 3 = 1 := residue b (by decide : 1 < 3) h
  have hr (h : r ≠ 0) : r.natDegree % 3 = 2 := residue c (by decide : 2 < 3) h
  have hpq : (p+q).natDegree = max p.natDegree q.natDegree :=
    degree_add _ _ fun h₁ h₂ => by have := hp h₁; have := hq h₂; omega
  have hsum : (p+q+r).natDegree = max (max p.natDegree q.natDegree) r.natDegree := by
    rw [← hpq]
    apply degree_add
    intro h h₃
    have := hr h₃
    by_cases h₁ : p = 0
    · have h₂ : q ≠ 0 := fun he => h (by simp [h₁, he])
      have := hq h₂
      simp [h₁]
      omega
    by_cases h₂ : q = 0
    · have := hp h₁
      simp [h₂]
      omega
    have := hp h₁
    have := hq h₂
    omega
  change (part 0 a+part 1 b+part 2 c).natDegree =
    max (max (part 0 a).natDegree (part 1 b).natDegree) (part 2 c).natDegree at hsum
  rw [hw 0 a, hw 1 b, hw 2 c] at hsum
  simpa only [part, pow_zero, one_mul, pow_one] using hsum

theorem degree_image (a b c : BinaryPoly) : (image a b c).natDegree = (source a b c).natDegree := by
  have hs := parts_degree a b c (expand (ZMod 2) 3) (map_zero _)
    (fun _ h => (expand_ne_zero (by decide : 0 < 3)).2 h) (natDegree_expand 3)
  have hd := parts_degree a b c (fun p => p^3) (by simp)
    (fun _ h => pow_ne_zero _ h) (fun p => by rw [natDegree_pow, Nat.mul_comm])
  rw [source, hs, image]
  by_cases h : X*a*b*c = 0
  · rwa [h, add_zero]
  have ha : a ≠ 0 := fun he => h (by simp [he])
  have hb : b ≠ 0 := fun he => h (by simp [he])
  have hc : c ≠ 0 := fun he => h (by simp [he])
  have he : (X*a*b*c).natDegree = 1+a.natDegree+b.natDegree+c.natDegree := by
    simp [natDegree_mul, X_ne_zero, ha, hb, hc]
  rw [natDegree_add_eq_left_of_natDegree_lt, hd]
  rw [he, hd]
  simp only [weight, if_neg ha, if_neg hb, if_neg hc]
  omega

theorem primitive_image_iff (a b c : BinaryPoly) (hn : 0 < (source a b c).natDegree) :
    Primitive (image a b c) ↔ Primitive (source a b c) ∧ Odd (source a b c).natDegree := by
  have hd := degree_image a b c
  have hi : 0 < (image a b c).natDegree := hd.symm ▸ hn
  have h := primitive_iff_of_dvd_expand (binary_monic (ne_zero_of_natDegree_gt hi))
    (binary_monic (ne_zero_of_natDegree_gt hn)) hi hd.symm (by decide : 0 < 3)
    (source_dvd_expand_image a b c)
  rwa [hd, mersenne_coprime_three_iff_odd] at h

end GF2Sparse.CubicImage
