import GF2Sparse.Linearized
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! Congruences forcing product-one Frobenius triples, simultaneously at prime degrees. -/

namespace GF2Sparse

open Polynomial FiniteField

private abbrev K := AlgebraicClosure (ZMod 2)

/-- The order of the norm-one group for the cubic extension of the field of order 2^m. -/
def cubicNormOrder (m : ℕ) := (2^m)^2 + 2^m + 1

/-- Three distinct roots whose product is one give a failure of the third exterior-power test. -/
def HasDistinctRootTriple (f : BinaryPoly) : Prop :=
  ∃ x y z : AlgebraicClosure (ZMod 2), aeval x f = 0 ∧ aeval y f = 0 ∧ aeval z f = 0 ∧
    x * y * z = 1 ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z

private theorem pow_eq_of_modEq {E : Type*} [Monoid E] {x : E} {D j k : ℕ}
    (hx : x^D = 1) (hj : j ≡ k [MOD D]) : x^j = x^k := by
  have h := Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hx) hj
  calc
    _ = x ^ (j % orderOf x) := (pow_mod_orderOf x j).symm
    _ = x ^ (k % orderOf x) := congrArg _ h
    _ = _ := pow_mod_orderOf x k

/-- A prescribed residue of n forces a triple at a prescribed inner exponent a. -/
theorem root_triple_of_norm_congruence {m n a : ℕ} (ha : a.Coprime (cubicNormOrder m))
    (h3 : Nat.Coprime 3 (cubicNormOrder m)) (hn : n ≡ a * (2^m+1) [MOD cubicNormOrder m]) :
    HasDistinctRootTriple (trinomial n a) := by
  classical
  let Q := 2^m
  let D := cubicNormOrder m
  have hQ : 0 < Q := Nat.two_pow_pos m
  have hD : 1 < D := by change 1 < Q^2+Q+1; omega
  let f := trinomial (Q+1) 1
  have hd : f.natDegree = Q+1 := trinomial_degree (by decide) (by omega)
  have hdeg : f.degree ≠ 0 := ne_of_gt (natDegree_pos_iff_degree_pos.1 (by omega))
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_aeval_eq_zero K f hdeg
  have huD : u^D = 1 := by
    obtain ⟨g, hg⟩ := associate_dvd_norm_exponent m
    have hz := congrArg (aeval u) hg
    change aeval u (X ^ D - 1) = aeval u (f*g) at hz
    simpa [hu, sub_eq_zero] using hz
  have hut : u^(Q+1) = u+1 := by
    simpa only [f, trinomial, map_add, map_pow, pow_one, aeval_X, map_one, CharTwo.add_eq_zero] using hu
  obtain ⟨b,hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime ha hD
  let x := u^b
  have hx : x^a = u := by
    rw [show x^a = u^(a*b) by change (u^b)^a = _; rw [← pow_mul, Nat.mul_comm]]
    convert pow_eq_of_modEq huD (j := a*b) (k := 1) (by simpa [Nat.ModEq, Nat.mod_eq_of_lt hD] using hb.2) using 1
    simp
  have hxD : x^D = 1 := by change (u^b)^D = 1; rw [pow_right_comm, huD, one_pow]
  have hr : aeval x (trinomial n a) = 0 := by
    simp only [trinomial, map_add, map_pow, aeval_X, map_one, CharTwo.add_eq_zero]
    rw [pow_eq_of_modEq hxD hn, pow_mul, hx, hut]
  let y := x^Q
  let z := y^Q
  have hz : z = x^(2^(m+m)) := by dsimp [z, y, Q]; rw [← pow_mul, pow_add]
  have he : D = 1+Q+2^(m+m) := by dsimp [D, cubicNormOrder, Q]; rw [pow_add]; ring
  have hprod : x*y*z = 1 := by simpa only [he, hz, y, pow_add, pow_one] using hxD
  have hcycle : z^Q = x := by
    have hrot := congrArg (fun v : K => v^Q) hprod
    change (x*y*z)^Q = 1^Q at hrot
    simp only [mul_pow, one_pow] at hrot
    change y*z*z^Q = 1 at hrot
    calc
      z^Q = z^Q * (x*y*z) := by rw [hprod, mul_one]
      _ = x * (y*z*z^Q) := by ring
      _ = x := by rw [hrot, mul_one]
  have hxy : x ≠ y := by
    intro h
    have hyz : y = z := congrArg (fun v : K => v^Q) h
    have hthree : x^3 = 1 := by simpa [← hyz, ← h, pow_succ] using hprod
    have hdiv := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hthree) (orderOf_dvd_of_pow_eq_one hxD)
    rw [h3.gcd_eq_one] at hdiv
    have hx1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdiv)
    simp [hx1, trinomial, CharTwo.add_self_eq_zero] at hr
  refine ⟨x, y, z, hr, ?_, ?_, hprod, hxy, ?_, ?_⟩
  · change aeval (x^(2^m)) _ = 0
    rw [aeval_dyadic, hr, zero_pow hQ.ne']
  · rw [hz, aeval_dyadic, hr, zero_pow (Nat.two_pow_pos _).ne']
  · intro h
    exact hxy (hcycle.symm.trans (congrArg (fun v : K => v^Q) h.symm))
  · intro h
    have hzx : z = x := (congrArg (fun v : K => v^Q) h).trans hcycle
    exact hxy (hzx.symm.trans h.symm)

/-- Every prime dividing the norm order at m=3^j exceeds 3^(j+1). -/
theorem prime_factor_cubic_norm_gt (j : ℕ) {p : ℕ} (hp : p.Prime) (hpd : p ∣ cubicNormOrder (3^j)) :
    3^(j+1) < p := by
  letI : Fact p.Prime := ⟨hp⟩
  let q := (2 : ZMod p) ^ (3^j)
  have hz : q^2 + q + 1 = 0 := by
    simpa [q, cubicNormOrder] using (ZMod.natCast_eq_zero_iff _ p).2 hpd
  have htwo3 : (2 : ZMod 3) = -1 := by decide
  have hone3 : (-1 : ZMod 3)^2 + -1 + 1 ≠ 0 := by decide
  have hp3 : p ≠ 3 := by
    rintro rfl
    have he : (2 : ZMod 3)^(3^j) = -1 := by
      rw [htwo3, (show Odd (3^j : ℕ) from (by decide : Odd (3 : ℕ)).pow).neg_one_pow]
    dsimp [q] at hz
    rw [he] at hz
    exact hone3 hz
  have hne : q ≠ 1 := by
    intro h
    rw [h] at hz
    have h3 : (3 : ZMod p) = 0 := by linear_combination hz
    have hd := (ZMod.natCast_eq_zero_iff 3 p).1 h3
    exact hp3 (((Nat.dvd_prime (by decide : Nat.Prime 3)).1 hd).resolve_left hp.ne_one)
  have hq : q^3 = 1 := by linear_combination (q-1)*hz
  have hpow : (2 : ZMod p)^(3^(j+1)) = 1 := by simpa only [q, pow_succ 3 j, pow_mul] using hq
  have hnod : ¬ orderOf (2 : ZMod p) ∣ 3^j := fun hd => hne (orderOf_dvd_iff_pow_eq_one.1 hd)
  have ho := Nat.eq_prime_pow_of_dvd_least_prime_pow Nat.prime_three hnod (orderOf_dvd_of_pow_eq_one hpow)
  have htwo : (2 : ZMod p) ≠ 0 := by intro h; simp [h, zero_pow (by positivity : 3^(j+1) ≠ 0)] at hpow
  have hcard := orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one (2 : ZMod p) htwo)
  rw [ZMod.card, ho] at hcard
  have := Nat.le_of_dvd (by have := hp.two_le; omega : 0 < p-1) hcard
  omega

private theorem exists_coprime_norm (B : ℕ) (hB : 0 < B) :
    ∃ m, B.Coprime (cubicNormOrder m) := by
  refine ⟨3^B, ?_⟩
  by_contra h
  obtain ⟨p, hp, hpB, hpD⟩ := Nat.Prime.not_coprime_iff_dvd.1 h
  have hbig := prime_factor_cubic_norm_gt B hp hpD
  have hsmall := Nat.le_of_dvd hB hpB
  have hpow := Nat.lt_pow_self (n := B+1) (a := 3) (by decide)
  omega

private theorem coprime_of_congruence {x y L : ℕ} (h : x ≡ y [MOD L])
    (hy : y.Coprime L) : x.Coprime L := by
  change x.gcd L = 1
  change y.gcd L = 1 at hy
  rw [Nat.gcd_comm x L, Nat.gcd_rec L x, h, ← Nat.gcd_rec, Nat.gcd_comm, hy]

/-- A reduced arithmetic progression simultaneously forcing a triple for every
positive inner exponent at most A, inside any prescribed reduced progression. -/
theorem fixed_taps_obstruction_progression (A : ℕ) {M r : ℕ} (hM : 0 < M)
    (hr : r.Coprime M) : ∃ L k : ℕ, 0 < L ∧ k.Coprime L ∧ ∀ n, n ≡ k [MOD L] →
      n ≡ r [MOD M] ∧ ∀ a, 0 < a → a ≤ A → HasDistinctRootTriple (trinomial n a) := by
  induction A with
  | zero => exact ⟨M, r, hM, hr, fun n hn => ⟨hn, by omega⟩⟩
  | succ A ih =>
    obtain ⟨L, k, hL, hk, ih⟩ := ih
    obtain ⟨m, hcop⟩ := exists_coprime_norm (3*(L*(A+1))) (by positivity)
    obtain ⟨h3, hcop⟩ := Nat.coprime_mul_iff_left.1 hcop
    obtain ⟨hLD, haD⟩ := Nat.coprime_mul_iff_left.1 hcop
    let Q := 2^m
    let D := cubicNormOrder m
    have hD : 0 < D := Nat.succ_pos _
    have hQD : (Q+1).Coprime D := by
      change (Q+1).Coprime (Q^2+Q+1)
      rw [show Q^2+Q = Q*(Q+1) by ring, Nat.coprime_mul_right_add_right]
      simp
    let z := Nat.chineseRemainder hLD k ((A+1)*(Q+1))
    have hzL := coprime_of_congruence z.property.1 hk
    have hzD := coprime_of_congruence z.property.2 (haD.mul_left hQD)
    refine ⟨L*D, z, Nat.mul_pos hL hD, hzL.mul_right hzD, ?_⟩
    intro n hn
    have hnL := (Nat.ModEq.of_dvd (dvd_mul_right L D) hn).trans z.property.1
    have hnD := (Nat.ModEq.of_dvd (dvd_mul_left D L) hn).trans z.property.2
    obtain ⟨hnM, hold⟩ := ih n hnL
    refine ⟨hnM, fun a hpos hle => ?_⟩
    rcases hle.eq_or_lt with rfl | hlt
    · exact root_triple_of_norm_congruence haD h3 hnD
    · exact hold a hpos (by omega)

/-- In arbitrarily large prime degrees in any reduced class, all trinomials in
a fixed finite menu have a product-one triple. -/
theorem exists_prime_fixed_taps_triple (A B : ℕ) {M r : ℕ} (hM : 0 < M)
    (hr : r.Coprime M) : ∃ n > max A B, n.Prime ∧ n ≡ r [MOD M] ∧
      ∀ a, 0 < a → a ≤ A → HasDistinctRootTriple (trinomial n a) := by
  obtain ⟨L, k, hL, hk, h⟩ := fixed_taps_obstruction_progression A hM hr
  obtain ⟨n, hn, hp, hc⟩ := Nat.forall_exists_prime_gt_and_modEq (max A B) hL.ne' hk
  exact ⟨n, hn, hp, h n hc⟩

end GF2Sparse
