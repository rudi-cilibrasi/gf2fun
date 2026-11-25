import GF2Sparse.TripleRoots
import GF2Sparse.DyadicCertificate
import GF2Sparse.Table

/-! Squarefree pentanomials passing the first three exterior-power tests in
every positive degree divisible by eight. -/

namespace GF2Sparse

open Polynomial DyadicCertificate

private abbrev K := AlgebraicClosure (ZMod 2)

private noncomputable def tailValue (x : K) := (1 + x ^ 2) * (1 + x ^ 3)

private theorem symmetric_sum (x y z : K) (h : x*y*z = 1) :
    sumImage (x+y+z) (x*y+y*z+z*x) = tailValue x + tailValue y + tailValue z := by
  unfold sumImage tailValue
  grind only

private theorem symmetric_pairs (x y z : K) (h : x*y*z = 1) :
    pairsImage (x+y+z) (x*y+y*z+z*x) =
      tailValue x * tailValue y + tailValue y * tailValue z + tailValue z * tailValue x := by
  unfold pairsImage tailValue
  grind only

private theorem symmetric_product (x y z : K) (h : x*y*z = 1) :
    productImage (x+y+z) (x*y+y*z+z*x) = tailValue x * tailValue y * tailValue z := by
  unfold productImage tailValue
  grind only

/-- X^(2^s) + (1+X³)(1+X²) excludes product-one triples, including repetitions. -/
theorem dyadic_pentanomial_no_root_triple (s : ℕ) : NoRootTriple (productCandidate (2 ^ s) 3 2) := by
  intro x y z hx hy hz h
  let φ := iterateFrobenius K 2 s
  let p := (x+y+z, x*y+y*z+z*x)
  have root_eq (r : K) (hr : aeval r (productCandidate (2 ^ s) 3 2) = 0) : tailValue r = φ r := by
    have hr' : r ^ (2 ^ s) + (r ^ 3 + 1) * (r ^ 2 + 1) = 0 := by
      simpa only [productCandidate, map_add, map_mul, map_pow, aeval_X, map_one] using hr
    simpa only [φ, iterateFrobenius_def, tailValue, add_comm, mul_comm] using (CharTwo.add_eq_zero.mp hr').symm
  have hs : stepPair p = (φ p.1, φ p.2) := by
    simp only [p, stepPair, symmetric_sum x y z h, symmetric_pairs x y z h,
      root_eq x hx, root_eq y hy, root_eq z hz, map_add, map_mul]
  have hp : productImage p.1 p.2 = 1 := by
    dsimp only [p]
    rw [symmetric_product x y z h, root_eq x hx, root_eq y hy, root_eq z hz,
      ← map_mul, ← map_mul, h, map_one]
  have hstep (a b : K) : stepPair (φ a, φ b) = (φ (sumImage a b), φ (pairsImage a b)) := by
    simp only [stepPair, sumImage, pairsImage, map_add, map_mul, map_pow]
  have hprod (a b : K) : productImage (φ a) (φ b) = φ (productImage a b) := by
    simp only [productImage, map_add, map_mul, map_pow]
  apply no_three_iterates p.1 p.2 hp
  · change productImage (stepPair p).1 (stepPair p).2 = 1
    rw [hs, hprod, hp, map_one]
  · change productImage (stepPair (stepPair p)).1 (stepPair (stepPair p)).2 = 1
    rw [hs, hstep, hprod]
    change φ (productImage (stepPair p).1 (stepPair p).2) = 1
    rw [hs, hprod, hp, map_one, map_one]

/-- The odd dilations have exactly five terms and remain squarefree. -/
theorem dyadic_triple_dilation (s m : ℕ) (hs : 3 ≤ s) (hm : Odd m) :
    let f := productCandidate (m * 2 ^ s) (m * 3) (m * 2)
    f.natDegree = m * 2 ^ s ∧ f.support.card = 5 ∧ Squarefree f ∧ NoRootTriple f := by
  dsimp only
  have hm0 : 0 < m := by obtain ⟨k,hk⟩ := hm; omega
  have hQ : 5 < 2 ^ s := lt_of_lt_of_le (by decide : 5 < 2 ^ 3)
    (Nat.pow_le_pow_right (by decide) hs)
  have htop : m * 3 + m * 2 < m * 2 ^ s := by
    simpa only [← Nat.mul_add] using Nat.mul_lt_mul_of_pos_left hQ hm0
  obtain ⟨hd, hc⟩ := product_shape (by positivity) (by positivity) (by omega) htop
  refine ⟨hd, hc, (product_separable (by positivity) (hm.mul (by decide)) (Even.mul_left (by decide) m)
    (by positivity)).squarefree, ?_⟩
  simpa only [productCandidate, map_add, map_mul, map_pow, expand_X, map_one, ← pow_mul] using
    (dyadic_pentanomial_no_root_triple s).expand m

/-- Every positive multiple of eight has a squarefree five-term polynomial
with no product-one triple of roots, and hence no root 1 or inverse pair. -/
theorem exists_five_no_root_triple_of_eight_dvd {n : ℕ} (hn : 0 < n) (h8 : 8 ∣ n) :
    ∃ f : BinaryPoly, f.natDegree = n ∧ f.support.card = 5 ∧ Squarefree f ∧ NoRootTriple f := by
  obtain ⟨k,rfl⟩ := h8
  obtain ⟨s,m,hm,rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : k ≠ 0)
  have h := dyadic_triple_dilation (s+3) m (by omega) hm
  rw [pow_add] at h
  refine ⟨_, h.1.trans (by ring), h.2⟩

set_option maxRecDepth 8192

theorem dyadic_triple_example_eight : Primitive (productCandidate 8 3 2) := by
  have h := certify_five_terms 8 5 3 2 [3, 5, 17] (by
    intro p hp; simp at hp; rcases hp with rfl | rfl | rfl <;> decide) (by decide +kernel)
  convert h using 1
  unfold productCandidate
  ring

theorem dyadic_triple_example_sixteen : Primitive (productCandidate 16 3 2) := by
  have h := certify_five_terms 16 5 3 2 [3, 5, 17, 257] (by
    intro p hp; simp at hp; rcases hp with rfl | rfl | rfl | rfl <;> decide) (by decide +kernel)
  convert h using 1
  unfold productCandidate
  ring

end GF2Sparse
