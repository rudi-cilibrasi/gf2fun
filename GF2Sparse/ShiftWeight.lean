import GF2Sparse.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.Nat.BitIndices

/-! Sparsity in the power bases at zero and one. -/

namespace GF2Sparse.ShiftWeight

open Polynomial

noncomputable section

def shift (f : BinaryPoly) : BinaryPoly := f.comp (X + 1)

private abbrev wt (f : BinaryPoly) := f.support.card

private def join (a b : BinaryPoly) : BinaryPoly :=
  expand (ZMod 2) 2 a + X * expand (ZMod 2) 2 b

private theorem expand_odd (a : BinaryPoly) (k : ℕ) :
    (expand (ZMod 2) 2 a).coeff (2*k+1) = 0 := by
  rw [coeff_expand (by decide)]
  simp

private theorem coeff_even (a b : BinaryPoly) (k : ℕ) :
    (join a b).coeff (2*k) = a.coeff k := by
  rw [join, coeff_add, coeff_expand_mul' (by decide)]
  cases k with
  | zero => simp
  | succ k =>
    rw [show 2*(k+1) = (2*k+1)+1 by omega, coeff_X_mul, expand_odd, add_zero]

private theorem coeff_odd (a b : BinaryPoly) (k : ℕ) :
    (join a b).coeff (2*k+1) = b.coeff k := by
  rw [join, coeff_add, expand_odd, coeff_X_mul, coeff_expand_mul' (by decide), zero_add]

private theorem split (f : BinaryPoly) : ∃ a b, f = join a b := by
  refine ⟨contract 2 f, contract 2 f.divX, ?_⟩
  ext k
  rcases (show k = 2*(k/2) ∨ k = 2*(k/2)+1 by omega) with h | h
  · conv_lhs => rw [h]
    conv_rhs => rw [h, coeff_even, coeff_contract (by decide)]
    rw [Nat.mul_comm]
  · conv_lhs => rw [h]
    conv_rhs => rw [h, coeff_odd, coeff_contract (by decide), coeff_divX]
    rw [Nat.mul_comm]

private theorem wt_join (a b : BinaryPoly) : wt (join a b) = wt a + wt b := by
  classical
  let ev := a.support.image (fun k => 2*k)
  let od := b.support.image (fun k => 2*k+1)
  have he (k : ℕ) : 2*k ∈ ev ∪ od ↔ k ∈ a.support := by
    simp only [ev, od, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (⟨j,hj,h⟩ | ⟨j,_,h⟩)
      · rwa [show k = j by omega]
      · omega
    · exact fun h => Or.inl ⟨k,h,rfl⟩
  have ho (k : ℕ) : 2*k+1 ∈ ev ∪ od ↔ k ∈ b.support := by
    simp only [ev, od, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (⟨j,_,h⟩ | ⟨j,hj,h⟩)
      · omega
      · rwa [show k = j by omega]
    · exact fun h => Or.inr ⟨k,h,rfl⟩
  have hs : (join a b).support = ev ∪ od := by
    ext k
    rcases (show ∃ j, k = 2*j ∨ k = 2*j+1 from ⟨k/2, by omega⟩) with ⟨j,rfl | rfl⟩
    · rw [he, mem_support_iff, mem_support_iff, coeff_even]
    · rw [ho, mem_support_iff, mem_support_iff, coeff_odd]
  have hd : Disjoint ev od := by
    apply Finset.disjoint_left.2
    intro k hk hl
    obtain ⟨j,_,hj⟩ := Finset.mem_image.1 hk
    obtain ⟨l,_,hl⟩ := Finset.mem_image.1 hl
    omega
  unfold wt
  rw [hs, Finset.card_union_of_disjoint hd]
  dsimp only [ev, od]
  rw [Finset.card_image_of_injective _ (by intro x y h; dsimp at h; omega),
      Finset.card_image_of_injective _ (by intro x y h; dsimp at h; omega)]

/-- The even and odd supports in a binary Frobenius decomposition are disjoint. -/
theorem card_support_sq_add_X_mul_sq (a b : BinaryPoly) :
    (a^2 + X*b^2).support.card = a.support.card + b.support.card := by
  have hf : frobenius (ZMod 2) 2 = RingHom.id _ := by
    ext1 c
    exact ZMod.pow_card c
  have he (p : BinaryPoly) : expand (ZMod 2) 2 p = p^2 := by
    simpa [hf] using map_frobenius_expand 2 p
  simpa only [join, wt, he] using wt_join a b

private theorem shift_join (a b : BinaryPoly) :
    shift (join a b) = join (shift (a+b)) (shift b) := by
  have commute (p : BinaryPoly) :
      shift (expand (ZMod 2) 2 p) = expand (ZMod 2) 2 (shift p) := by
    simp only [shift, expand_eq_comp_X_pow, comp_assoc, pow_comp, X_comp, add_comp, one_comp]
    rw [CharTwo.add_sq, one_pow]
  change shift (expand (ZMod 2) 2 a + X * expand (ZMod 2) 2 b) = _
  rw [show ∀ p q : BinaryPoly, shift (p+q) = shift p + shift q from fun _ _ => add_comp]
  rw [show shift (X * expand (ZMod 2) 2 b) = (X+1) * shift (expand (ZMod 2) 2 b) by
    simp [shift, mul_comp]]
  rw [commute, commute]
  simp only [join, shift, add_comp, map_add]
  ring

private theorem wt_add (a b : BinaryPoly) : wt (a+b) ≤ wt a + wt b :=
  (Finset.card_le_card support_add).trans (Finset.card_union_le _ _)

private theorem wt_shift_left (a b : BinaryPoly) :
    wt (shift a) ≤ wt (shift (a+b)) + wt (shift b) := by
  have h : shift a = shift (a+b) + shift b := by
    simp [shift, add_comp, add_assoc, CharTwo.add_self_eq_zero]
  rw [h]
  exact wt_add _ _

private theorem log_mono {a b : ℕ} (h : a ≤ b) : a.log2 ≤ b.log2 := by
  by_cases ha : a = 0
  · simp [ha]
  exact (Nat.le_log2 (by omega)).2 ((Nat.log2_self_le ha).trans h)

private theorem pair_gain {a b d t : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h₁ : d ≤ a.log2+t) (h₂ : d ≤ b.log2+t) : d+1 ≤ (a+b).log2+t := by
  rcases le_total a b with h | h
  · have h' := log_mono (show 2*a ≤ a+b by omega)
    rw [Nat.log2_two_mul ha.ne'] at h'
    omega
  · have h' := log_mono (show 2*b ≤ a+b by omega)
    rw [Nat.log2_two_mul hb.ne'] at h'
    omega

private theorem shift_twice (p : BinaryPoly) : shift (shift p) = p := by
  simp [shift, comp_assoc, add_assoc, CharTwo.add_self_eq_zero]

private theorem pos_shift {p : BinaryPoly} {k : ℕ} (h : p.coeff k ≠ 0) : 0 < wt (shift p) := by
  apply Finset.card_pos.2
  by_contra! he
  have hz : shift p = 0 := by simpa [Finset.not_nonempty_iff_eq_empty] using he
  have := shift_twice p
  rw [hz] at this
  simp [shift] at this
  simp [← this] at h

/-- Every exponent occurring in a polynomial gives a lower bound for the two support sizes. -/
theorem bitIndices_le (k : ℕ) (p : BinaryPoly) (hk : p.coeff k ≠ 0) :
    k.bitIndices.length ≤ p.support.card.log2 + (shift p).support.card.log2 := by
  induction k using Nat.strong_induction_on generalizing p with
  | h k ih =>
    by_cases zero : k = 0
    · simp [zero]
    let j := k/2
    have lt : j < k := by dsimp [j]; omega
    obtain ⟨a,b,rfl⟩ := split p
    have bound_a := wt_shift_left a b
    rcases (show k = 2*j ∨ k = 2*j+1 by dsimp [j]; omega) with e | e
    · rw [e, coeff_even] at hk
      have h := ih j lt a hk
      rw [e, Nat.bitIndices_two_mul, List.length_map]
      change _ ≤ (wt (join a b)).log2 + (wt (shift (join a b))).log2
      rw [shift_join, wt_join, wt_join]
      exact h.trans (Nat.add_le_add (log_mono (Nat.le_add_right _ _)) (log_mono bound_a))
    · rw [e, coeff_odd] at hk
      have hb := ih j lt b hk
      have pos_b : 0 < wt b := Finset.card_pos.2 ⟨j,mem_support_iff.2 hk⟩
      rw [e, Nat.bitIndices_two_mul_add_one, List.length_cons, List.length_map]
      change _ ≤ (wt (join a b)).log2 + (wt (shift (join a b))).log2
      rw [shift_join, wt_join, wt_join]
      by_cases ha : a.coeff j ≠ 0
      · have posa : 0 < wt a := Finset.card_pos.2 ⟨j,mem_support_iff.2 ha⟩
        exact pair_gain posa pos_b ((ih j lt a ha).trans (Nat.add_le_add_left (log_mono bound_a) _))
          (hb.trans (Nat.add_le_add_left (log_mono (Nat.le_add_left _ _)) _))
      · have hc : (a+b).coeff j ≠ 0 := by simpa [coeff_add, not_ne_iff.1 ha] using hk
        have h₁ := (ih j lt (a+b) hc).trans
          (Nat.add_le_add_right (log_mono (wt_add a b)) _)
        have h₂ := hb.trans (Nat.add_le_add_right (log_mono (Nat.le_add_left (wt b) (wt a))) _)
        rw [Nat.add_comm] at h₁ h₂
        have h := pair_gain (pos_shift hc) (pos_shift hk) h₁ h₂
        omega

/-- Two five-term translates require at most four binary ones in the degree. -/
theorem five_term_shifts {p : BinaryPoly} (hp : p ≠ 0) (h : p.support.card ≤ 5)
    (h' : (shift p).support.card ≤ 5) : p.natDegree.bitIndices.length ≤ 4 := by
  have bound := bitIndices_le p.natDegree p (leadingCoeff_ne_zero.mpr hp)
  have first := log_mono h
  have second := log_mono h'
  change p.support.card.log2 ≤ 2 at first
  change (shift p).support.card.log2 ≤ 2 at second
  omega

private theorem prod_bound {p : BinaryPoly} {k : ℕ} (hk : p.coeff k ≠ 0) :
    2^k.bitIndices.length ≤ wt p * wt (shift p) := by
  have pos : 0 < wt p := Finset.card_pos.2 ⟨k,mem_support_iff.2 hk⟩
  calc
    _ ≤ 2^((wt p).log2 + (wt (shift p)).log2) :=
      Nat.pow_le_pow_right (by decide) (bitIndices_le k p hk)
    _ ≤ _ := by
      rw [pow_add]
      exact Nat.mul_le_mul (Nat.log2_self_le pos.ne') (Nat.log2_self_le (pos_shift hk).ne')

private theorem expand_shape (i j : ℕ) :
    expand (ZMod 2) 2 ((X : BinaryPoly)^i * (X+1)^j) = X^(2*i) * (X+1)^(2*j) := by
  simp only [map_mul, map_pow, expand_X, map_add, map_one, pow_mul]
  rw [CharTwo.add_sq, one_pow]

/-- Equality in the product bound forces the polynomial to split between zero and one. -/
theorem shape_of_equality (k : ℕ) (p : BinaryPoly) (hk : p.coeff k ≠ 0)
    (eqn : p.support.card * (shift p).support.card = 2^k.bitIndices.length) :
    ∃ i j : ℕ, i+j = k ∧ i.bitIndices.length + j.bitIndices.length = k.bitIndices.length ∧
      p = X^i * (X+1)^j := by
  induction k using Nat.strong_induction_on generalizing p with
  | h k ih =>
    by_cases zero : k = 0
    · subst k
      have one : p.support.card = 1 := Nat.eq_one_of_mul_eq_one_right (by simpa using eqn)
      obtain ⟨l,hl⟩ := Finset.card_eq_one.mp one
      have h0 := mem_support_iff.2 hk
      rw [hl, Finset.mem_singleton] at h0
      subst l
      refine ⟨0,0,rfl,by decide,?_⟩
      simp only [pow_zero, mul_one]
      ext l
      by_cases hl0 : l = 0
      · subst l
        have h : p.coeff 0 = 1 := by
          exact ((show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) _).resolve_left hk
        simpa using h
      · rw [notMem_support_iff.1 (show l ∉ p.support by simpa [hl] using hl0)]
        simp [coeff_one, hl0]
    let m := k/2
    have lt : m < k := by dsimp [m]; omega
    obtain ⟨a,b,rfl⟩ := split p
    change wt (join a b) * wt (shift (join a b)) = _ at eqn
    rw [shift_join, wt_join, wt_join] at eqn
    have bound_a := wt_shift_left a b
    rcases (show k = 2*m ∨ k = 2*m+1 by dsimp [m]; omega) with e | e
    · rw [e, coeff_even] at hk
      rw [e, Nat.bitIndices_two_mul, List.length_map] at eqn
      have bound := (prod_bound hk).trans (Nat.mul_le_mul_left _ bound_a)
      have pos : 0 < wt (shift (a+b)) + wt (shift b) := lt_of_lt_of_le (pos_shift hk) bound_a
      have bz : wt b = 0 := by
        by_contra! h
        nlinarith [Nat.mul_pos (Nat.pos_of_ne_zero h) pos]
      have hb : b = 0 := card_support_eq_zero.1 bz
      subst b
      simp [shift, wt] at eqn
      obtain ⟨i,j,sum,bits,shape⟩ := ih m lt a hk eqn
      refine ⟨2*i,2*j,by omega,by simpa [e] using bits,?_⟩
      simp [join, shape, expand_shape]
    · rw [e, coeff_odd] at hk
      rw [e, Nat.bitIndices_two_mul_add_one, List.length_cons, List.length_map, pow_succ] at eqn
      have pos_b : 0 < wt b := Finset.card_pos.2 ⟨m,mem_support_iff.2 hk⟩
      have lower := prod_bound hk
      by_cases ha : a.coeff m ≠ 0
      · have ba := (prod_bound ha).trans (Nat.mul_le_mul_left _ bound_a)
        have hz : wt (shift (a+b)) = 0 := by
          by_contra! h
          nlinarith [Nat.mul_pos pos_b (Nat.pos_of_ne_zero h)]
        have hs : shift (a+b) = 0 := card_support_eq_zero.1 hz
        have h := shift_twice (a+b)
        rw [hs] at h
        have same : a = b := CharTwo.add_eq_zero.mp (by simpa [shift] using h.symm)
        subst a
        simp [shift, wt, CharTwo.add_self_eq_zero] at eqn
        have eqb : wt b * wt (shift b) = 2^m.bitIndices.length := by
          change (wt b + wt b) * wt (shift b) = _ at eqn
          nlinarith
        obtain ⟨i,j,sum,bits,shape⟩ := ih m lt b hk eqb
        refine ⟨2*i,2*j+1,by omega,by simp [e]; omega,?_⟩
        rw [join, shape, expand_shape, pow_succ]
        ring
      · have hc : (a+b).coeff m ≠ 0 := by simpa [coeff_add, not_ne_iff.1 ha] using hk
        have bc := (prod_bound hc).trans (Nat.mul_le_mul_right _ (wt_add a b))
        have hz : wt a = 0 := by
          by_contra! h
          nlinarith [Nat.mul_pos (Nat.pos_of_ne_zero h) (pos_shift hk)]
        have hz' : a = 0 := card_support_eq_zero.1 hz
        subst a
        simp [shift, wt] at eqn
        have eqb : wt b * wt (shift b) = 2^m.bitIndices.length := by
          change wt b * (wt (shift b) + wt (shift b)) = _ at eqn
          nlinarith
        obtain ⟨i,j,sum,bits,shape⟩ := ih m lt b hk eqb
        refine ⟨2*i+1,2*j,by omega,by simp [e]; omega,?_⟩
        simp only [join, map_zero, zero_add, shape, expand_shape, pow_succ]
        ring

/-- A trinomial root gives the two consecutive values in an extremal support pair. -/
theorem trinomial_values {K : Type*} [Field K] {z : K} (hz : z ≠ 0) (i j : ℕ)
    (h : z^(i+j) = z^j+1) :
    let r := (z^j)⁻¹
    1+r = z^i ∧ r^i*(1+r)^j = 1 := by
  have h₁ : (1+(z^j)⁻¹)*z^j = z^j+1 := by
    rw [add_mul, one_mul, inv_mul_cancel₀ (pow_ne_zero _ hz)]
  have value : 1+(z^j)⁻¹ = z^i :=
    mul_right_cancel₀ (pow_ne_zero _ hz) (h₁.trans (by simpa only [pow_add] using h.symm))
  refine ⟨value, ?_⟩
  dsimp only
  rw [value, inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm j i, inv_mul_cancel₀ (pow_ne_zero _ hz)]

end
end GF2Sparse.ShiftWeight
