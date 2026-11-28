import GF2Sparse.Certificate
import GF2Sparse.ShiftWeight
import Mathlib.Tactic.NormNum.Prime

/-! Binary recurrences for Gauss period polynomials and their projective changes of variable. -/

namespace GF2Sparse.GaussPeriod
open Polynomial
noncomputable section

/-- The two consecutive homogeneous continuants at the binary forms A and B. -/
def continuants (A B : BinaryPoly) : ℕ → BinaryPoly × BinaryPoly
  | 0 => (1, 0)
  | n+1 => let (u,v) := continuants A B n; (A*u+B^2*v,u)

theorem continuants_double (A B : BinaryPoly) (n : ℕ) :
    continuants A B (2*n) =
      let (u,v) := continuants A B n
      ((u+B*v)^2,A*v^2) := by
  induction n with
  | zero => simp [continuants]
  | succ n ih =>
    rw [Nat.mul_succ, show 2*n+2 = (2*n+1)+1 by omega, continuants, continuants, ih]
    simp only [continuants]
    generalize continuants A B n = p
    rcases p with ⟨u,v⟩
    apply Prod.ext <;> dsimp <;> simp only [CharTwo.add_sq] <;> ring_nf <;> simp [CharTwo.two_eq_zero]

theorem continuants_odd (A B : BinaryPoly) (n : ℕ) :
    continuants A B (2*n+1) =
      let (u,v) := continuants A B n
      (A*u^2,(u+B*v)^2) := by
  rw [continuants, continuants_double]
  generalize continuants A B n = p
  rcases p with ⟨u,v⟩
  apply Prod.ext
  · dsimp
    simp only [CharTwo.add_sq]
    ring_nf
    simp [CharTwo.two_eq_zero]
  · rfl

/-- For the period polynomial Pₙ this gives Bⁿ Pₙ(A/B). -/
def periodForm (A B : BinaryPoly) (n : ℕ) : BinaryPoly :=
  let (u,v) := continuants A B n
  u + B*v

theorem periodForm_recurrence (A B : BinaryPoly) (n : ℕ) :
    periodForm A B (n+2) = A * periodForm A B (n+1) + B^2 * periodForm A B n := by
  simp only [periodForm, continuants]
  ring

/-- Clearing the reciprocal substitution gives the geometric sum over the nontrivial
    roots of unity of order dividing 2n+1. -/
theorem cyclotomic_identity (n : ℕ) :
    (X+1) * periodForm (X^2+1) X n = X^(2*n+1)+1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [periodForm, continuants]
  | one =>
    simp only [periodForm, continuants]
    ring_nf
    simp [CharTwo.two_eq_zero]
  | more n he ho =>
    rw [periodForm_recurrence, mul_add,
      show (X+1) * ((X^2+1) * periodForm (X^2+1) X (n+1)) =
        (X^2+1) * ((X+1) * periodForm (X^2+1) X (n+1)) by ring,
      show (X+1) * (X^2 * periodForm (X^2+1) X n) =
        X^2 * ((X+1) * periodForm (X^2+1) X n) by ring, he, ho,
      show 2*(n+1)+1=(2*n+1)+2 by omega,
      show 2*(n+2)+1=(2*n+1)+4 by omega, pow_add, pow_add]
    ring_nf
    simp [CharTwo.two_eq_zero]

private abbrev weight (p : BinaryPoly) := p.support.card

private theorem splitWeight (f a b : BinaryPoly) (h : f = a^2+X*b^2) :
    weight f = weight a + weight b := h ▸ ShiftWeight.card_support_sq_add_X_mul_sq a b

private theorem wt_zero : weight 0 = 0 := by simp [weight]

/-- Check each claimed even/odd decomposition in the polynomial ring. -/
local macro "weigh" f:term:max "as" a:term:max "," b:term:max : term =>
  `(splitWeight $f $a $b (by
      try dsimp +zetaDelta only
      try simp only [CharTwo.add_sq]
      all_goals ring_nf
      all_goals simp [CharTwo.two_eq_zero, show (3 : BinaryPoly) = 1 by
        calc (3 : BinaryPoly) = 2+1 := by norm_num
             _ = 0+1 := congrArg (· + (1 : BinaryPoly)) (CharTwo.two_eq_zero (R := BinaryPoly))
             _ = 1 := zero_add _]))

private theorem propagate {A B : BinaryPoly} (J : ℕ → BinaryPoly → BinaryPoly → Prop)
    (initial : J 1 A 1)
    (step : ∀ k u v, 0 < k → J k u v →
      J (k+1) ((u+B*v)^2) (A*v^2) ∧ J (k+1) (A*u^2) ((u+B*v)^2))
    (n : ℕ) (hn : 0 < n) : J (n.log2+1) (continuants A B n).1 (continuants A B n).2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n = 1
    · subst n
      simpa [continuants] using initial
    let m := n / 2
    have hm : 0 < m := by dsimp [m]; omega
    have hs := step _ _ _ (Nat.succ_pos _) (ih m (by dsimp [m]; omega) hm)
    rw [Nat.log2_def n, if_pos (by omega : 2 ≤ n)]
    change J (m.log2+1+1) _ _
    rcases (show n = 2*m ∨ n = 2*m+1 by dsimp [m]; omega) with he | ho
    · rw [he, continuants_double]
      exact hs.1
    · rw [ho, continuants_odd]
      exact hs.2

private def plainInv (k : ℕ) (u v : BinaryPoly) : Prop :=
  k+1 ≤ weight (u+v) ∧ 0 < weight u ∧ 0 < weight v

private def shiftedInv (k : ℕ) (u v : BinaryPoly) : Prop :=
  k ≤ weight (u+v) ∧ k+1 ≤ weight u + weight v ∧ 0 < weight u ∧ 0 < weight v

private def reciprocalInv (k : ℕ) (u v : BinaryPoly) : Prop :=
  k ≤ weight (u+(X+1)*v) ∧ k ≤ weight (u+X*v) ∧
  0 < weight u ∧ 0 < weight v ∧ 0 < weight ((X+1)*v)

private theorem plainStep (k : ℕ) (u v : BinaryPoly) (_hk : 0 < k) (h : plainInv k u v) :
    plainInv (k+1) ((u+1*v)^2) (X*v^2) ∧ plainInv (k+1) (X*u^2) ((u+1*v)^2) := by
  simp only [one_mul, plainInv] at *
  have h₁ := weigh ((u+v)^2 + X*v^2) as (u+v), v
  have h₂ := weigh (X*u^2 + (u+v)^2) as (u+v), u
  have h₃ := weigh ((u+v)^2) as (u+v), 0
  have h₄ := weigh (X*v^2) as 0, v
  have h₅ := weigh (X*u^2) as 0, u
  simp only [wt_zero, zero_add, add_zero] at h₃ h₄ h₅
  obtain ⟨ha, hb, hc⟩ := h
  repeat' apply And.intro
  all_goals omega

private theorem shiftedStep (k : ℕ) (u v : BinaryPoly) (hk : 0 < k) (h : shiftedInv k u v) :
    shiftedInv (k+1) ((u+1*v)^2) ((X+1)*v^2) ∧ shiftedInv (k+1) ((X+1)*u^2) ((u+1*v)^2) := by
  simp only [one_mul, shiftedInv] at *
  have h₁ := weigh ((u+v)^2 + (X+1)*v^2) as u, v
  have h₂ := weigh ((X+1)*u^2 + (u+v)^2) as v, u
  have h₃ := weigh ((u+v)^2) as (u+v), 0
  have h₄ := weigh ((X+1)*v^2) as v, v
  have h₅ := weigh ((X+1)*u^2) as u, u
  simp only [wt_zero, add_zero] at h₃
  obtain ⟨ha, hb, hc, hd⟩ := h
  repeat' apply And.intro
  all_goals omega

private theorem reciprocalStep (k : ℕ) (u v : BinaryPoly) (hk : 0 < k) (h : reciprocalInv k u v) :
    reciprocalInv (k+1) ((u+(X+1)*v)^2) (1*v^2) ∧
    reciprocalInv (k+1) (1*u^2) ((u+(X+1)*v)^2) := by
  simp only [one_mul, reciprocalInv] at *
  let t := u+(X+1)*v
  have h₁ := weigh (t^2+(X+1)*v^2) as (u+X*v), v
  have h₂ := weigh (t^2+X*v^2) as t, v
  have h₃ := weigh (u^2+(X+1)*t^2) as ((X+1)*v), t
  have h₄ := weigh (u^2+X*t^2) as u, t
  have h₅ := weigh (t^2) as t, 0
  have h₆ := weigh (v^2) as v, 0
  have h₇ := weigh (u^2) as u, 0
  have h₈ := weigh ((X+1)*v^2) as v, v
  have h₉ := weigh ((X+1)*t^2) as t, t
  simp only [wt_zero, add_zero] at h₅ h₆ h₇
  dsimp [t] at *
  obtain ⟨ha, hb, hc, hd, he⟩ := h
  repeat' apply And.intro
  all_goals omega

/-- The three representatives, each paired with its reciprocal, have growing weight. -/
theorem projective_weights (n : ℕ) (hn : 0 < n) :
    n.log2+2 ≤ (periodForm X 1 n).support.card ∧
    n.log2+1 ≤ (periodForm (X+1) 1 n).support.card ∧
    n.log2+1 ≤ (periodForm 1 (X+1) n).support.card := by
  have hX : weight X = 1 := by simp [weight, Polynomial.support_X one_ne_zero]
  have h1 : weight 1 = 1 := by
    simpa only [map_one] using congrArg Finset.card (Polynomial.support_C (R := ZMod 2) (a := 1) one_ne_zero) |>.trans (Finset.card_singleton 0)
  have hX1 : weight (X+1) = 2 := by
    simpa only [h1] using (weigh (X+1) as 1, 1)
  have hx : (X+1+1 : BinaryPoly) = X := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hp := propagate plainInv (A := X) (B := 1) (by
    simp only [plainInv, hX, h1, hX1]; decide) plainStep n hn
  have hs := propagate shiftedInv (A := X+1) (B := 1) (by
    simp only [shiftedInv, hx, hX, h1, hX1]; decide) shiftedStep n hn
  have hr := propagate reciprocalInv (A := 1) (B := X+1) (by
    simp only [reciprocalInv, mul_one, add_comm (1 : BinaryPoly) (X+1), hx,
      add_comm (1 : BinaryPoly) X, hX, h1, hX1]; decide) reciprocalStep n hn
  simpa [periodForm] using And.intro hp.1 (And.intro hs.1 hr.1)

/-- Packed coefficients of two consecutive forms, starting at indices zero and one. -/
private def masks (a b : ℕ → ℕ) (seed : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, seed)
  | n+1 => let (f,g) := masks a b seed n; (g, a g ^^^ b f)

private theorem masks_spec (A B : BinaryPoly) (a b : ℕ → ℕ) (seed : ℕ)
    (ha : ∀ m, decode (a m) = A * decode m)
    (hb : ∀ m, decode (b m) = B^2 * decode m)
    (hs : decode seed = A+B) (n : ℕ) :
    decode (masks a b seed n).1 = periodForm A B n ∧
    decode (masks a b seed n).2 = periodForm A B (n+1) := by
  induction n with
  | zero => simp [masks, periodForm, continuants, hs]
  | succ n ih =>
    constructor
    · exact ih.2
    · simp only [masks, decode_xor, ha, hb, ih.1, ih.2, periodForm_recurrence]

private def plainMask := masks (· <<< 1) id 3
private def shiftedMask := masks (fun m => (m <<< 1) ^^^ m) id 2
private def reciprocalMask := masks id (fun m => (m <<< 2) ^^^ m) 2

private theorem three_mask : decode 3 = X+1 := by
  simpa only [decode_one, mul_one] using
    (show decode ((1 <<< 1) ^^^ 1) = X * decode 1 + decode 1 by rw [decode_xor, decode_shift])
private theorem two_mask : decode 2 = X := by
  simpa only [decode_one, mul_one] using decode_shift 1

private theorem mask_forms (n : ℕ) :
    decode (plainMask n).1 = periodForm X 1 n ∧
    decode (shiftedMask n).1 = periodForm (X+1) 1 n ∧
    decode (reciprocalMask n).1 = periodForm 1 (X+1) n := by
  have h : (X+1+1 : BinaryPoly) = X := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have h' : (1+(X+1) : BinaryPoly) = X := by rw [add_comm 1, h]
  refine ⟨(masks_spec X 1 _ _ 3 decode_shift (fun m => by simp) three_mask n).1,
    (masks_spec (X+1) 1 _ _ 2 ?_ (fun m => by simp) (by rw [h, two_mask]) n).1,
    (masks_spec 1 (X+1) _ _ 2 (fun m => by simp) ?_ (by rw [h', two_mask]) n).1⟩
  · intro m
    simp only [decode_xor, decode_shift, add_mul, one_mul]
  · intro m
    simp only [decode_xor, decode_shift_by, CharTwo.add_sq, one_pow, add_mul, one_mul]

private def plainSmall : List ℕ := [0,1,2,3,4,5,6,7,8,15]
private def shiftedSmall : List ℕ := [0,1,2,3,4,5,6,7,10,11,12,13]
private def reciprocalSmall : List ℕ := [0,1,2,3,4,5,6,7,8,9,12,13,16,24]

private theorem finite_cases : ∀ i : Fin 32,
    ((positions (plainMask i).1).card ≤ 5 ↔ (i : ℕ) ∈ plainSmall) ∧
    ((positions (shiftedMask i).1).card ≤ 5 ↔ (i : ℕ) ∈ shiftedSmall) ∧
    ((positions (reciprocalMask i).1).card ≤ 5 ↔ (i : ℕ) ∈ reciprocalSmall) := by
  decide +kernel

/-- Exact five-term cutoff in all three charts, including every reducible index. -/
theorem projective_five_term_degrees (n : ℕ) :
    ((periodForm X 1 n).support.card ≤ 5 ↔ n ∈ [0,1,2,3,4,5,6,7,8,15]) ∧
    ((periodForm (X+1) 1 n).support.card ≤ 5 ↔ n ∈ [0,1,2,3,4,5,6,7,10,11,12,13]) ∧
    ((periodForm 1 (X+1) n).support.card ≤ 5 ↔ n ∈ [0,1,2,3,4,5,6,7,8,9,12,13,16,24]) := by
  by_cases h : n < 32
  · obtain ⟨hp, hs, hr⟩ := mask_forms n
    rw [← hp, ← hs, ← hr, support_decode, support_decode, support_decode]
    exact finite_cases ⟨n,h⟩
  · have hn : n ≠ 0 := by omega
    have hl : 5 ≤ n.log2 := (Nat.le_log2 hn).2 (by norm_num; omega)
    obtain ⟨hp, hs, hr⟩ := projective_weights n (Nat.pos_of_ne_zero hn)
    have hp' : ¬ (periodForm X 1 n).support.card ≤ 5 := by omega
    have hs' : ¬ (periodForm (X+1) 1 n).support.card ≤ 5 := by omega
    have hr' : ¬ (periodForm 1 (X+1) n).support.card ≤ 5 := by omega
    simp only [hp', hs', hr', false_iff, List.mem_cons, List.not_mem_nil, or_false, not_or]
    repeat' apply And.intro
    all_goals omega

/-- The signed Frobenius orbit of a nontrivial pair has full length n
    at prime conductor 2n+1. -/
def typeIIIndex (n : ℕ) : Prop :=
  (2*n+1).Prime ∧ ∀ k : Fin n, 0 < (k : ℕ) →
    2^(k : ℕ) % (2*n+1) ≠ 1 ∧ 2^(k : ℕ) % (2*n+1) ≠ 2*n

private instance (n : ℕ) : Decidable (typeIIIndex n) := by unfold typeIIIndex; infer_instance

private theorem finite_typeII : ∀ i : Fin 32,
    (1 < (i : ℕ) ∧ typeIIIndex i ∧
      ((i : ℕ) ∈ plainSmall ∨ (i : ℕ) ∈ shiftedSmall ∨ (i : ℕ) ∈ reciprocalSmall)) ↔
    (i : ℕ) ∈ [2,3,5,6,9,11] := by decide +kernel

theorem typeII_sparse_degrees (n : ℕ) :
    (1 < n ∧ typeIIIndex n ∧ ((periodForm X 1 n).support.card ≤ 5 ∨
      (periodForm (X+1) 1 n).support.card ≤ 5 ∨ (periodForm 1 (X+1) n).support.card ≤ 5)) ↔
    n ∈ [2,3,5,6,9,11] := by
  by_cases h : n < 32
  · obtain ⟨hp, hs, hr⟩ := projective_five_term_degrees n
    rw [hp, hs, hr]
    exact finite_typeII ⟨n,h⟩
  · have hn : n ≠ 0 := by omega
    have hl : 5 ≤ n.log2 := (Nat.le_log2 hn).2 (by norm_num; omega)
    obtain ⟨hp, hs, hr⟩ := projective_weights n (Nat.pos_of_ne_zero hn)
    have h₁ : ¬ (periodForm X 1 n).support.card ≤ 5 := by omega
    have h₂ : ¬ (periodForm (X+1) 1 n).support.card ≤ 5 := by omega
    have h₃ : ¬ (periodForm 1 (X+1) n).support.card ≤ 5 := by omega
    simp only [h₁, h₂, h₃, or_self, and_false, false_iff, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    repeat' apply And.intro
    all_goals omega

/-- One of the three forms supplies a primitive at each surviving type-II degree. -/
theorem typeII_primitive_examples :
    Primitive (periodForm X 1 2) ∧ Primitive (periodForm X 1 3) ∧
    Primitive (periodForm X 1 5) ∧ Primitive (periodForm X 1 6) ∧
    Primitive (periodForm 1 (X+1) 9) ∧ Primitive (periodForm (X+1) 1 11) := by
  rw [← (mask_forms 2).1, ← (mask_forms 3).1, ← (mask_forms 5).1,
    ← (mask_forms 6).1, ← (mask_forms 9).2.2, ← (mask_forms 11).2.1]
  exact ⟨(check_sound (factors := [3]) (by decide) (by decide +kernel : check 2 _ _ = true)).2.2,
    (check_sound (factors := [7]) (by decide) (by decide +kernel : check 3 _ _ = true)).2.2,
    (check_sound (factors := [31]) (by decide) (by decide +kernel : check 5 _ _ = true)).2.2,
    (check_sound (factors := [3,3,7]) (by decide) (by decide +kernel : check 6 _ _ = true)).2.2,
    (check_sound (factors := [7,73]) (by decide) (by decide +kernel : check 9 _ _ = true)).2.2,
    (check_sound (factors := [23,89]) (by decide) (by decide +kernel : check 11 _ _ = true)).2.2⟩

/-- Pull a sparse polynomial back along (X+1)/X² and clear its denominator. -/
def quadraticPullback (n : ℕ) (exponents : List ℕ) : BinaryPoly :=
  (exponents.map (fun i => X^(2*(n-i)) * (X+1)^i)).sum

private def shiftedPower : ℕ → ℕ
  | 0 => 1
  | k+1 => let m := shiftedPower k; (m <<< 1) ^^^ m

private theorem decode_shiftedPower (i : ℕ) : decode (shiftedPower i) = (X+1)^i := by
  induction i with
  | zero => simp [shiftedPower]
  | succ i ih => simp only [shiftedPower, decode_xor, decode_shift, ih, pow_succ']; ring

private def pullbackMask (n : ℕ) : List ℕ → ℕ
  | [] => 0
  | i :: rest => ((shiftedPower i) <<< (2*(n-i))) ^^^ pullbackMask n rest

private theorem decode_pullback (n : ℕ) (taps : List ℕ) :
    decode (pullbackMask n taps) = quadraticPullback n taps := by
  induction taps with
  | nil => simp [pullbackMask, quadraticPullback]
  | cons i rest ih =>
    simp only [pullbackMask, decode_xor, decode_shift_by, decode_shiftedPower, ih,
      quadraticPullback, List.map_cons, List.sum_cons]

theorem quadratic_period_witnesses :
    (periodForm X 1 23 ∣ quadraticPullback 23 [0,3,15,17,23]) ∧
    (periodForm X 1 30 ∣ quadraticPullback 30 [0,1,6,13,30]) ∧
    Primitive (decode 0x828009) ∧ Primitive (decode 0x40002043) := by
  refine ⟨⟨decode 0xffff4f, ?_⟩, ⟨decode 0x43003333, ?_⟩, ?_, ?_⟩
  · rw [← (mask_forms 23).1, ← decode_maskProduct, ← decode_pullback]
    exact congrArg decode (by decide +kernel)
  · rw [← (mask_forms 30).1, ← decode_maskProduct, ← decode_pullback]
    exact congrArg decode (by decide +kernel)
  · have primes : ∀ p ∈ [47,178481], Nat.Prime p := by
      intro p hp
      simp at hp
      rcases hp with rfl | rfl <;> norm_num
    exact (check_sound primes
      (by decide +kernel : check 23 _ _ = true)).2.2
  · exact (check_sound (factors := [3,3,7,11,31,151,331]) (by decide +kernel)
      (by decide +kernel : check 30 _ _ = true)).2.2

end
end GF2Sparse.GaussPeriod
