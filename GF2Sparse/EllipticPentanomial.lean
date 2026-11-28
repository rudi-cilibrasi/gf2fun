import GF2Sparse.Table
import Mathlib.Tactic.ReduceModChar

/-! Binary translation for the elliptic pentanomials and the integer primitive-root
certificate for the example of degree 2^84 + 2. -/

namespace GF2Sparse.EllipticPentanomial

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Translating the elliptic x-coordinate equation gives exactly five terms for s ≥ 2. -/
theorem translate {K : Type*} [Field K] [CharP K 2] (x : K) (s : ℕ) :
    (x+1)^(2^s+2) + (x+1)^3 + 1 =
      x^(2^s+2) + x^(2^s) + x^3 + x + 1 := by
  rw [pow_add, pow_add,
    show (x+1)^(2^s) = x^(2^s) + 1 by
      simpa only [one_pow] using add_pow_expChar_pow x 1 2 s]
  ring_nf
  reduce_mod_char!

/-- Three conjugate shifts multiply to the n-th power of the unshifted coordinate. -/
theorem shift_product {K : Type*} [Field K] [CharP K 2] {u w : K} {n : ℕ}
    (hw : w^2 + w + 1 = 0) (hu : u^n + u^3 + 1 = 0) :
    (1+u)*(1+w*u)*(1+w^2*u) = u^n := by
  linear_combination (norm := (try ring_nf; reduce_mod_char!))
    ((w+1)*u^3+w*u^2+u)*hw - hu

/-- The cubic of the relative norm is a symmetric identity in the two conjugates. -/
theorem cubic_norm_identity {K : Type*} [Field K] [CharP K 2] (x y : K) :
    let s := x*y
    let b := (1+x)*(1+y)
    b^3 + (1+s)*b^2 + (1+s+s^2)*b + (1+x^3)*(1+y^3) = 0 := by
  dsimp only
  ring_nf
  reduce_mod_char!

private def p2 : ProvenPrime := ⟨2, by norm_num1⟩
private def p3 : ProvenPrime := ⟨3, by norm_num1⟩
private def p5 : ProvenPrime := ⟨5, by norm_num1⟩
private def p7 : ProvenPrime := ⟨7, by norm_num1⟩
private def p13 : ProvenPrime := ⟨13, by norm_num1⟩
private def p23 : ProvenPrime := ⟨23, by norm_num1⟩
private def p83 : ProvenPrime := ⟨83, by norm_num1⟩
private def p271 : ProvenPrime := ⟨271, by norm_num1⟩
private def p499 : ProvenPrime := ⟨499, by norm_num1⟩
private def p1163 : ProvenPrime := lucasPrime 1163 5 [p2, p7, p83] (by decide +kernel)
private def p2657 : ProvenPrime := lucasPrime 2657 3 [p2, p2, p2, p2, p2, p83] (by decide +kernel)
private def p155377 : ProvenPrime :=
  lucasPrime 155377 5 [p2, p2, p2, p2, p3, p3, p13, p83] (by decide +kernel)
private def p2711 : ProvenPrime := lucasPrime 2711 7 [p2, p5, p271] (by decide +kernel)
private def p623531 : ProvenPrime := lucasPrime 623531 2 [p2, p5, p23, p2711] (by decide +kernel)
private def p1247063 : ProvenPrime := lucasPrime 1247063 5 [p2, p623531] (by decide +kernel)
private def p13455809771 : ProvenPrime :=
  lucasPrime 13455809771 6 [p2, p5, p13, p83, p1247063] (by decide +kernel)

private def factors : List ProvenPrime := [p2, p3, p499, p1163, p2657, p155377, p13455809771]

theorem elliptic_prime : (2^84+3).Prime := by
  exact (lucasPrime (2^84+3) 2 factors (by decide +kernel)).property

private theorem binPow_eq_pow {M : Type*} [Monoid M] (e : ℕ) (a : M) :
    npowBinRec e a = a ^ e := by
  induction e with
  | zero => simp [npowBinRec_zero]
  | succ e ih => rw [npowBinRec_succ, ih, pow_succ]

private theorem order_from_powers {p n : ℕ} (a : ZMod p) (hn : 0 < n) (ps : List ProvenPrime)
    (hprod : (ps.map Subtype.val).prod = n) (hfull : npowBinRec n a = 1)
    (htests : (ps.map Subtype.val).all (fun q => npowBinRec (n/q) a != 1) = true) :
    orderOf a = n := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by omega)
  · exact (binPow_eq_pow n a).symm.trans hfull
  · intro q hq hdvd
    have hprime : ∀ t ∈ ps.map Subtype.val, Prime t := by
      intro t ht
      obtain ⟨c, _, rfl⟩ := List.mem_map.1 ht
      exact c.property.prime
    have hm := mem_list_primes_of_dvd_prod hq.prime hprime (hprod ▸ hdvd)
    simpa only [binPow_eq_pow, bne_iff_ne] using List.all_eq_true.1 htests q hm

theorem integer_order : orderOf (2 : ZMod (2^84+3)) = 2^84+2 :=
  order_from_powers 2 (by decide) factors (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

private def factors262146 : List ProvenPrime :=
  [p2, p3, lucasPrime 43691 6
    [p2, p5, ⟨17, by norm_num1⟩, ⟨257, by norm_num1⟩] (by decide +kernel)]

theorem elliptic_prime_262147 : Nat.Prime 262147 :=
  (lucasPrime 262147 2 factors262146 (by decide +kernel)).property

theorem integer_order_262147 : orderOf (2 : ZMod 262147) = 262146 :=
  order_from_powers 2 (by decide) factors262146 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- Cross multiplication costs at most the positive height of the first
exponent vector and the negative height of the second. -/
theorem quotient_height_bound (x y : Fin 5 → ℤ) :
    ∑ i, max (x i - y i) 0 ≤ (∑ i, max (x i) 0) + ∑ i, max (-y i) 0 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hx := le_max_left (x i) 0
  have hy := le_max_left (-y i) 0
  have hx0 := le_max_right (x i) 0
  have hy0 := le_max_right (-y i) 0
  exact max_le (by omega) (by omega)

end GF2Sparse.EllipticPentanomial
