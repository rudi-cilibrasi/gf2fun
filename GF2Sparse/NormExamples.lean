import GF2Sparse.FrobeniusPairs

/-! A primitive quartic composition and a reducible one passing the same norm test. -/

namespace GF2Sparse

open Polynomial

set_option maxRecDepth 8192

private theorem decode_two_eq_X : decode 2 = X := by simpa using decode_pow_two 1

private theorem norm_power_184 :
    xPow 184 (fiveTermMask 184 46 4 1) ((16 ^ 46 - 1) / (16 - 1)) = 2 ^ 46 ^^^ 2 ^ 1 := by
  decide +kernel

private theorem frobenius_power_184 :
    xPow 184 (fiveTermMask 184 46 4 1) (2 ^ 92) = 2 := by decide +kernel

/-- The degree-20 pentanomial passes the smooth relative-degree test and is primitive. -/
theorem norm_example_20 :
    let h : BinaryPoly := X ^ 5 + X ^ 4 + X
    let f : BinaryPoly := X ^ 20 + X ^ 16 + X ^ 5 + X + 1
    (frobeniusOuter 2).comp h = f ∧ f ∣ X ^ normExponent 16 5 - h ∧ Primitive f := by
  dsimp only
  constructor
  · simp only [frobeniusOuter, add_comp, pow_comp, X_comp, one_comp, add_pow_expChar_pow, ← pow_mul]
    change (X ^ 20 + X ^ 16 + X ^ 4) + (X ^ 5 + X ^ 4 + X) + 1 = _
    calc
      _ = (X ^ 4 + X ^ 4) + (X ^ 20 + X ^ 16 + X ^ 5 + X + 1) := by ring
      _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]
  constructor
  · have he := dvd_X_pow_sub_decode (n := 20) (f := fiveTermMask 20 16 5 1)
      (e := normExponent 16 5) (r := 2 ^ 5 ^^^ 2 ^ 4 ^^^ 2 ^ 1) (by decide +kernel)
    simpa only [decode_fiveTermMask, decode_xor, decode_pow_two, pow_one, decode_two_eq_X] using he
  · have he := certify_five_terms 20 16 5 1 [3, 5, 5, 11, 31, 41] (by
      intro p hp
      simp at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide) (by decide +kernel)
    simpa only [pow_one] using he

private theorem no_quartic_factor_184 {p : BinaryPoly} (hp : Irreducible p)
    (hd : p ∣ (frobeniusOuter 2).comp (X ^ 46 + X)) : p.natDegree ≠ 4 := by
  intro hdeg
  letI : Fact (Irreducible p) := ⟨hp⟩
  letI : CharP (AdjoinRoot p) 2 := charP_of_injective_ringHom (AdjoinRoot.of p).injective 2
  let z := AdjoinRoot.root p
  have hz : aeval z p = 0 := (AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self
  have h16 : z ^ 16 = z := (degree_dvd_iff_frobenius hp hz 4).1 (hdeg ▸ dvd_rfl)
  have h15 : z ^ 15 * z = z := (pow_succ z 15).symm.trans h16
  have h46 : z ^ 46 = z := calc
    _ = z ^ 15 * (z ^ 15 * z ^ 16) := by rw [← pow_add, ← pow_add]
    _ = z := by rw [h16, h15, h15]
  have hinner : aeval z (X ^ 46 + X : BinaryPoly) = 0 := by
    rw [map_add, map_pow, aeval_X, h46, CharTwo.add_self_eq_zero]
  have hout : aeval (aeval z (X ^ 46 + X : BinaryPoly)) (frobeniusOuter 2) = 0 := by
    rw [← aeval_comp, AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_eq_zero.2 hd
  rw [hinner] at hout
  apply one_ne_zero (α := AdjoinRoot p)
  simpa only [frobeniusOuter, map_add, map_pow, aeval_X, map_one, zero_pow (by decide : 2 ^ 2 ≠ 0),
    zero_add] using hout

private noncomputable def inner184 : BinaryPoly := X ^ 46 + X
private noncomputable def polynomial184 : BinaryPoly := X ^ 184 + X ^ 46 + X ^ 4 + X + 1

private theorem comp184 : (frobeniusOuter 2).comp inner184 = polynomial184 := by
  simp only [inner184, polynomial184, frobeniusOuter, add_comp, pow_comp, X_comp, one_comp,
    add_pow_expChar_pow, ← pow_mul]
  ring

private theorem degree_inner184 : inner184.natDegree = 46 := by
  rw [inner184, natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
  simp

private theorem mask184 : decode (fiveTermMask 184 46 4 1) = polynomial184 := by
  simpa only [pow_one] using decode_fiveTermMask 184 46 4 1

private theorem norm184 : polynomial184 ∣ X ^ normExponent 16 46 - inner184 := by
  have hh : decode (2 ^ 46 ^^^ 2 ^ 1) = inner184 := by
    rw [decode_xor, decode_pow_two, decode_pow_two, pow_one, inner184]
  have he := dvd_X_pow_sub_decode norm_power_184
  rw [mask184, hh] at he
  rw [normExponent_eq_div (by decide : 1 < 16)]
  exact he

private theorem squarefree184 : Squarefree polynomial184 := by
  have hq : 2 ^ (frobeniusOuter 2).natDegree = 16 := by
    rw [frobeniusOuter_natDegree (by decide : 0 < 2)]
    decide
  rw [← comp184]
  apply squarefree_comp_of_norm primitive_frobeniusOuter_two (by rw [degree_inner184]; decide)
  rw [comp184, degree_inner184, hq]
  exact norm184

private theorem frobenius184 : polynomial184 ∣ X ^ (2 ^ 92) - X := by
  have he := dvd_X_pow_sub_decode frobenius_power_184
  rwa [mask184, decode_two_eq_X] at he

private theorem factor_degree184 {p : BinaryPoly} (hp : Irreducible p) (hpf : p ∣ polynomial184) :
    p.natDegree = 92 := by
  have h92 : p.natDegree ∣ 92 := hp.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
    (by rw [Nat.card_zmod]; exact hpf.trans frobenius184)
  have hpc : p ∣ (frobeniusOuter 2).comp inner184 := comp184 ▸ hpf
  obtain ⟨t, ht⟩ := outer_degree_dvd_factor primitive_frobeniusOuter_two.2.1 hp hpc
  rw [frobeniusOuter_natDegree (by decide : 0 < 2)] at ht
  have h23 : t ∣ 23 := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 4) (ht ▸ h92)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 23)).mp h23 with h1 | h23
  · exact ((no_quartic_factor_184 hp hpc) (by simpa [h1] using ht)).elim
  · simp [ht, h23]

/-- In degree 184 the norm congruence holds, but the polynomial is squarefree
and every irreducible factor has degree 92. Hence there are exactly two. -/
theorem norm_counterexample_184 :
    let h : BinaryPoly := X ^ 46 + X
    let f : BinaryPoly := X ^ 184 + X ^ 46 + X ^ 4 + X + 1
    (frobeniusOuter 2).comp h = f ∧ f ∣ X ^ normExponent 16 46 - h ∧
      Squarefree f ∧ ∀ p : BinaryPoly, Irreducible p → p ∣ f → p.natDegree = 92 :=
  ⟨comp184, norm184, squarefree184, fun _ => factor_degree184⟩

end GF2Sparse
