import GF2Sparse.Roots
import GF2Sparse.Table
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Five-term polynomials from a projective change of variable over the field of four elements. -/

namespace GF2Sparse.TwistedCyclotomic

open Polynomial
noncomputable section

/-- The twisted cyclotomic pentanomial at Q = 2^k. -/
def candidate (Q : ℕ) : BinaryPoly := X^(Q+4) + (X^(Q+1) + (X^Q + (X^5 + 1)))

theorem candidate_degree {Q : ℕ} (hQ : 5 < Q) : (candidate Q).natDegree = Q+4 := by
  unfold candidate
  compute_degree! <;> first | omega | simp [show Q+4 ≠ 5 by omega]

theorem candidate_weight {Q : ℕ} (hQ : 5 < Q) : (candidate Q).support.card = 5 := by
  let s : Finset ℕ := {Q+4,Q+1,Q,5,0}
  have hform : candidate Q = ∑ j ∈ s, X^j := by
    simp [s, candidate, Finset.sum_insert, show Q ≠ 0 by omega, show Q ≠ 5 by omega,
      show Q+1 ≠ 5 by omega, show Q+4 ≠ 5 by omega]
  have hs : (candidate Q).support = s := by
    rw [hform]
    ext i
    simp [mem_support_iff, coeff_X_pow]
  rw [hs]
  simp [s, Finset.card_insert_of_notMem, show Q ≠ 0 by omega, show Q ≠ 5 by omega,
    show Q+1 ≠ 5 by omega, show Q+4 ≠ 5 by omega]

section Field
variable {K : Type*} [Field K] [CharP K 2]

private theorem fourth_fixed {w : K} (hw : w^2 = w+1) : w^4 = w := by
  rw [show 4=2*2 by decide, pow_mul, hw, CharTwo.add_sq, hw, one_pow, add_assoc,
    CharTwo.add_self_eq_zero, add_zero]

private theorem even_fixed {w : K} (hw : w^2 = w+1) (j : ℕ) : w^(2^(2*j)) = w := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.mul_succ, pow_add, pow_mul, ih]
    exact fourth_fixed hw

private theorem odd_swapped {w : K} (hw : w^2 = w+1) {k : ℕ} (hk : Odd k) :
    w^(2^k) = w+1 := by
  obtain ⟨j,rfl⟩ := hk
  rw [pow_succ, pow_mul, even_fixed hw, hw]

/-- Expanding three binary digits over the quadratic constant field. -/
theorem twisted_identity {w : K} (hw : w^2 = w+1) (x : K) {k : ℕ} (hk : Odd k) :
    (x+w)^(2^k+5) + (x+(w+1))^(2^k+5) =
      x^(2^k+4) + (x^(2^k+1) + (x^(2^k) + (x^5+1))) := by
  have hw' : (w+1)^2 = w := by
    rw [CharTwo.add_sq, hw, one_pow, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have h4 (u v : K) : (u+v)^4 = u^4+v^4 := add_pow_expChar_pow u v 2 2
  have hw4' : (w+1)^4 = w+1 := by
    rw [show 4=2*2 by decide, pow_mul, hw', hw]
  have hwk' : (w+1)^(2^k) = w := by
    rw [add_pow_expChar_pow, odd_swapped hw hk, one_pow, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  rw [show 5=4+1 by decide, pow_add (x+w), pow_add (x+(w+1)),
    pow_succ (x+w) 4, pow_succ (x+(w+1)) 4, h4, h4, fourth_fixed hw, hw4',
    add_pow_expChar_pow (x : K) w, add_pow_expChar_pow (x : K) (w+1), odd_swapped hw hk, hwk',
    pow_add x, pow_succ x (2^k), pow_succ x 4]
  ring_nf
  have h3 : (3 : K) = 1 := by
    calc (3 : K) = 2+1 := by norm_num
         _ = 1 := by rw [CharTwo.two_eq_zero, zero_add]
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, hw, h3, mul_one]
  abel_nf
  simp [CharTwo.two_eq_zero]

/-- An even Frobenius power fixing x also fixes its cyclotomic coordinate. -/
private theorem modulus_order_dvd {x w : K} (hw : w^2 = w+1) {p e : ℕ}
    (hz : orderOf ((x+w)/(x+(w+1))) = p) (hp : 0 < p)
    (he : Even e) (hx : x^(2^e) = x) : orderOf (2 : ZMod p) ∣ e := by
  obtain ⟨j, hj⟩ := he
  have hwf : w^(2^e) = w := by rw [show e=2*j by omega, even_fixed hw]
  let z := (x+w)/(x+(w+1))
  have hfix : z^(2^e) = z := by
    dsimp [z]
    rw [div_pow, add_pow_expChar_pow, add_pow_expChar_pow, add_pow_expChar_pow, hx, hwf, one_pow]
  have hz' : z ≠ 0 := by
    intro h
    have ho : orderOf z = p := hz
    rw [h, orderOf_zero] at ho
    omega
  have hone : z^(2^e-1) = 1 := by
    apply mul_right_cancel₀ hz'
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel (Nat.two_pow_pos e), hfix]
  have hd : p ∣ 2^e-1 := hz ▸ orderOf_dvd_of_pow_eq_one hone
  apply orderOf_dvd_of_pow_eq_one
  have hc := (ZMod.natCast_eq_zero_iff _ _).2 hd
  rw [Nat.cast_sub (Nat.two_pow_pos e), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
    sub_eq_zero] at hc
  exact hc

private theorem period_triple {z : K} (hz : z ≠ 0) {j : ℕ} (h : z^(2^j) = z^3) :
    (z+z⁻¹)^(2^j) = (z+z⁻¹)^3 + (z+z⁻¹) := by
  rw [add_pow_expChar_pow, inv_pow, h, ← inv_pow]
  field_simp
  ring_nf
  simp [show (4 : K) = 0 by rw [show (4 : K) = 2*2 by norm_num, CharTwo.two_eq_zero, zero_mul]]

private theorem period_ratio {z : K} (hz : z ≠ 0) : z+z⁻¹ = (1+z)^2 / z := by
  rw [CharTwo.add_sq]
  field_simp
  ring

/-- The order of the half-field projection of a twisted cyclotomic root. -/
theorem half_projection_order {z w : K} (hz : z ≠ 0) (hz1 : z ≠ 1) (hw : w^2 = w+1)
    {m j : ℕ} (hm : Even m) (hzq : z^(2^m) = z⁻¹)
    (hj : 3 < 2^j) (hthree : z^(2^j) = z^3) :
    let x := (w+(w+1)*z)/(1+z)
    let t := z+z⁻¹
    orderOf (x^(2^m+1)) = orderOf t / (orderOf t).gcd (2^j-3) := by
  let x := (w+(w+1)*z)/(1+z)
  let t := z+z⁻¹
  change orderOf (x^(2^m+1)) = orderOf t / (orderOf t).gcd (2^j-3)
  have hd : 1 + z ≠ 0 := fun h => hz1 (CharTwo.add_eq_zero.mp h).symm
  have hdi : 1 + z⁻¹ ≠ 0 := by
    intro h
    exact hz1 (inv_eq_one.mp (CharTwo.add_eq_zero.mp h).symm)
  have hwq : w^(2^m) = w := by
    obtain ⟨v, hv⟩ := hm
    rw [show m = 2*v by omega]
    exact even_fixed hw v
  have hx : x^(2^m) = x+1 := by
    dsimp [x]
    rw [div_pow, add_pow_expChar_pow, mul_pow, add_pow_expChar_pow, add_pow_expChar_pow,
        hwq, hzq, one_pow]
    field_simp
    grind
  have hn : x*(x+1) = 1+t⁻¹ := by
    dsimp [x, t]
    rw [period_ratio hz, inv_div]
    field_simp
    grind
  have ht : t ≠ 0 := by
    dsimp [t]
    rw [period_ratio hz]
    exact div_ne_zero (pow_ne_zero _ hd) hz
  have hpow : t^(2^j) = t^3+t := period_triple hz hthree
  have heq : (1+t⁻¹)^2 = t^(2^j-3) := by
    apply mul_right_cancel₀ (pow_ne_zero 3 ht)
    rw [← pow_add, Nat.sub_add_cancel hj.le, hpow, CharTwo.add_sq]
    field_simp [ht]
  have hs := orderOf_injective (frobenius K 2).toMonoidHom (frobenius K 2).injective (1+t⁻¹)
  change orderOf ((1+t⁻¹)^2) = orderOf (1+t⁻¹) at hs
  rw [pow_succ, hx, mul_comm (x+1), hn, ← hs, heq, orderOf_pow' _ (by omega)]

end Field

/-- Full order of two modulo Q+5 proves irreducibility without constructing a
    quotient ring of dimension Q+4. -/
theorem irreducible_candidate {k : ℕ} (hk : Odd k) (hk3 : 3 ≤ k)
    (hp : Nat.Prime (2^k+5)) (horder : orderOf (2 : ZMod (2^k+5)) = 2^k+4) :
    Irreducible (candidate (2^k)) := by
  let K := AlgebraicClosure (ZMod 2)
  let Q := 2^k
  have hQ : 5 < Q := lt_of_lt_of_le (by decide : 5 < 2^3)
    (Nat.pow_le_pow_right (by decide) hk3)
  have hf := candidate_degree hQ
  have hpos : 0 < (candidate Q).natDegree := hf ▸ Nat.zero_lt_succ _
  have hm := binary_monic (fun h => by simp [h] at hpos : candidate Q ≠ 0)
  obtain ⟨g, hg, hdiv⟩ := WfDvdMonoid.exists_irreducible_factor
    (not_isUnit_of_natDegree_pos _ hpos) hm.ne_zero
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero K g
    (fun h => hg.natDegree_pos.ne' (natDegree_eq_of_degree_eq_some h))
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_root (X^2+X+1 : K[X]) (by
    have h : (X^2+X+1 : K[X]).natDegree = 2 := by compute_degree!
    intro e
    exact (by decide : (2 : ℕ) ≠ 0) (h.symm.trans (natDegree_eq_of_degree_eq_some e)))
  have hw' : w^2 = w+1 := by
    change eval w _ = 0 at hw
    simp only [eval_add, eval_pow, eval_X, eval_one] at hw
    exact (CharTwo.add_eq_zero.mp (show w^2+(w+1)=0 by rwa [← add_assoc]))
  have hxf := aeval_eq_zero_of_dvd_aeval_eq_zero hdiv hx
  simp only [candidate, map_add, map_pow, aeval_X, map_one] at hxf
  have he : (x+w)^(Q+5) = (x+(w+1))^(Q+5) :=
    CharTwo.add_eq_zero.mp ((twisted_identity hw' x hk).trans hxf)
  have hden : x+(w+1) ≠ 0 := by
    intro e
    rw [e, zero_pow (by omega)] at he
    have en : x+w=0 := eq_zero_of_pow_eq_zero he
    simp [← add_assoc, en] at e
  let z := (x+w)/(x+(w+1))
  have hz : orderOf z = Q+5 := by
    letI : Fact (Nat.Prime (Q+5)) := ⟨hp⟩
    apply orderOf_eq_prime
    · dsimp [z]
      rw [div_pow, he, div_self (pow_ne_zero _ hden)]
    · intro e
      have ex := (div_eq_one_iff_eq hden).1 e
      exact one_ne_zero (add_left_cancel (show (x+w)+1=(x+w)+0 by
        simpa [add_assoc] using ex.symm))
  let d := g.natDegree
  have twice : Q+4 ∣ 2*d := horder ▸ modulus_order_dvd hw' hz (by omega)
    (even_two_mul d) ((degree_dvd_iff_frobenius hg hx _).1 (dvd_mul_left d 2))
  have h4 : 4 ∣ Q+4 := dvd_add (by
    change 2^2 ∣ 2^k
    exact pow_dvd_pow 2 (by omega)) dvd_rfl
  have evenD : Even d := by
    have hd := h4.trans twice
    exact ⟨d/2, by omega⟩
  have hd : Q+4 ∣ d := horder ▸ modulus_order_dvd hw' hz (by omega) evenD
    ((degree_dvd_iff_frobenius hg hx _).1 dvd_rfl)
  have heq := eq_of_monic_of_dvd_of_natDegree_le (binary_monic hg.ne_zero) hm hdiv
    (hf ▸ Nat.le_of_dvd hg.natDegree_pos hd)
  exact heq.symm ▸ hg


private def orderCheck (p : ℕ) (factors : List ProvenPrime) : Bool :=
  let power (j : ℕ) := npowBinRec j (2 : ZMod p)
  (factors.map Subtype.val).prod == p-1 && power (p-1) == 1 &&
    factors.all (fun q => power ((p-1)/q.val) != 1)

private theorem checked_order {p : ℕ} (hp : 1 < p) (factors : List ProvenPrime)
    (hc : orderCheck p factors = true) : p.Prime ∧ orderOf (2 : ZMod p) = p-1 := by
  have bin (j : ℕ) (x : ZMod p) : npowBinRec j x = x^j := by
    induction j with
    | zero => simp [npowBinRec_zero]
    | succ i ih => rw [npowBinRec_succ, ih, pow_succ]
  simp only [orderCheck, bin, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, List.all_eq_true] at hc
  have powers (q : ℕ) (hq : q.Prime) (hd : q ∣ p-1) : (2 : ZMod p)^((p-1)/q) ≠ 1 := by
    have hm := mem_list_primes_of_dvd_prod hq.prime (L := factors.map Subtype.val)
      (by intro a ha; obtain ⟨c, _, rfl⟩ := List.mem_map.1 ha; exact c.property.prime)
      (hc.1.1.symm ▸ hd)
    obtain ⟨c, hmem, rfl⟩ := List.mem_map.1 hm
    exact hc.2 c hmem
  exact ⟨lucas_primality p 2 hc.1.2 powers,
    orderOf_eq_of_pow_and_pow_div_prime (Nat.sub_pos_of_lt hp) hc.1.2 powers⟩

set_option maxRecDepth 8000
set_option maxHeartbeats 800000

private def p2 : ProvenPrime := ⟨2, by norm_num1⟩
private def p3 : ProvenPrime := ⟨3, by norm_num1⟩
private def p7 : ProvenPrime := ⟨7, by norm_num1⟩
private def p139 : ProvenPrime := ⟨139, by norm_num1⟩
private def p193 : ProvenPrime := ⟨193, by norm_num1⟩
private def p4506937 : ProvenPrime := lucasPrime 4506937 11 [p2, p2, p2, p3, p7, p139, p193] (by decide +kernel)
private def p11 : ProvenPrime := ⟨11, by norm_num1⟩
private def p5 : ProvenPrime := ⟨5, by norm_num1⟩
private def p103 : ProvenPrime := ⟨103, by norm_num1⟩
private def p1031 : ProvenPrime := lucasPrime 1031 14 [p2, p5, p103] (by decide +kernel)
private def p2063 : ProvenPrime := lucasPrime 2063 5 [p2, p1031] (by decide +kernel)
private def p761 : ProvenPrime := ⟨761, by norm_num1⟩
private def p1523 : ProvenPrime := lucasPrime 1523 2 [p2, p761] (by decide +kernel)
private def p809 : ProvenPrime := ⟨809, by norm_num1⟩
private def p1619 : ProvenPrime := lucasPrime 1619 2 [p2, p809] (by decide +kernel)
private def p34270993 : ProvenPrime := lucasPrime 34270993 5 [p2, p2, p2, p2, p3, p3, p3, p7, p7, p1619] (by decide +kernel)
private def p31 : ProvenPrime := ⟨31, by norm_num1⟩
private def p53 : ProvenPrime := ⟨53, by norm_num1⟩
private def p157 : ProvenPrime := ⟨157, by norm_num1⟩
private def p5653 : ProvenPrime := lucasPrime 5653 5 [p2, p2, p3, p3, p157] (by decide +kernel)
private def p557272741 : ProvenPrime := lucasPrime 557272741 6 [p2, p2, p3, p5, p31, p53, p5653] (by decide +kernel)
private def p34033153146917030767 : ProvenPrime := lucasPrime 34033153146917030767 3 [p2, p3, p3, p3, p3, p11, p34270993, p557272741] (by decide +kernel)
private def p389054686774116311763206347 : ProvenPrime := lucasPrime 389054686774116311763206347 2 [p2, p3, p3, p3, p139, p1523, p34033153146917030767] (by decide +kernel)
private def p51542639524661795300074174250365699 : ProvenPrime := lucasPrime 51542639524661795300074174250365699 3 [p2, p3, p7, p11, p139, p2063, p389054686774116311763206347] (by decide +kernel)
private def p19 : ProvenPrime := ⟨19, by norm_num1⟩
private def p43 : ProvenPrime := ⟨43, by norm_num1⟩
private def p379 : ProvenPrime := ⟨379, by norm_num1⟩
private def p5419 : ProvenPrime := lucasPrime 5419 3 [p2, p3, p3, p7, p43] (by decide +kernel)
private def p317 : ProvenPrime := ⟨317, by norm_num1⟩
private def p119827 : ProvenPrime := lucasPrime 119827 3 [p2, p3, p3, p3, p7, p317] (by decide +kernel)
private def p17 : ProvenPrime := ⟨17, by norm_num1⟩
private def p87211 : ProvenPrime := lucasPrime 87211 13 [p2, p3, p3, p3, p5, p17, p19] (by decide +kernel)
private def p73 : ProvenPrime := ⟨73, by norm_num1⟩
private def p174763 : ProvenPrime := lucasPrime 174763 17 [p2, p3, p3, p7, p19, p73] (by decide +kernel)
private def p699053 : ProvenPrime := lucasPrime 699053 2 [p2, p2, p174763] (by decide +kernel)
private def p77158673929 : ProvenPrime := lucasPrime 77158673929 11 [p2, p2, p2, p3, p3, p3, p7, p73, p699053] (by decide +kernel)
private def p2053 : ProvenPrime := lucasPrime 2053 2 [p2, p2, p3, p3, p3, p19] (by decide +kernel)
private def p977 : ProvenPrime := ⟨977, by norm_num1⟩
private def p7817 : ProvenPrime := lucasPrime 7817 3 [p2, p2, p2, p977] (by decide +kernel)
private def p127391413339 : ProvenPrime := lucasPrime 127391413339 11 [p2, p3, p3, p3, p3, p7, p7, p2053, p7817] (by decide +kernel)
private def p443 : ProvenPrime := ⟨443, by norm_num1⟩
private def p13 : ProvenPrime := ⟨13, by norm_num1⟩
private def p127 : ProvenPrime := ⟨127, by norm_num1⟩
private def p27941 : ProvenPrime := lucasPrime 27941 2 [p2, p2, p5, p11, p127] (by decide +kernel)
private def p5085263 : ProvenPrime := lucasPrime 5085263 5 [p2, p7, p13, p27941] (by decide +kernel)
private def p49560973199 : ProvenPrime := lucasPrime 49560973199 11 [p2, p11, p443, p5085263] (by decide +kernel)
private def p56202143607667 : ProvenPrime := lucasPrime 56202143607667 3 [p2, p3, p3, p3, p3, p7, p49560973199] (by decide +kernel)

theorem irreducible_141 : Irreducible (candidate (2^141)) := by
  obtain ⟨hp, ho⟩ := checked_order (p := 2^141+5) (by decide)
    [p2, p2, p3, p4506937, p51542639524661795300074174250365699]
    (by decide +kernel)
  exact irreducible_candidate (by decide) (by decide) hp ho

theorem irreducible_191 : Irreducible (candidate (2^191)) := by
  obtain ⟨hp, ho⟩ := checked_order (p := 2^191+5) (by decide)
    [p2, p2, p3, p3, p3, p3, p19, p43, p379, p5419, p119827, p87211,
      p77158673929, p127391413339, p56202143607667]
    (by decide +kernel)
  exact irreducible_candidate (by decide) (by decide) hp ho

end
end GF2Sparse.TwistedCyclotomic
