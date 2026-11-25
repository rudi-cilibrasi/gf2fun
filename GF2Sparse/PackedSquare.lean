import GF2Sparse.FrobeniusWitness
import Mathlib.NumberTheory.LucasLehmer

/-! Kernel certificates for binary squaring by parallel shifts and masks.
Testing an XOR-linear circuit on the monomials proves it correct on every
input of the specified width. -/

namespace GF2Sparse.PackedSquare

open Polynomial

/-- Each stage XORs a shifted copy and keeps the positions selected by its mask. -/
def spread : List (ℕ × ℕ) → ℕ → ℕ
  | [], a => a
  | (s,mask)::rest, a => spread rest ((a ^^^ (a <<< s)) &&& mask)

private theorem spread_xor (stages : List (ℕ × ℕ)) (a b : ℕ) :
    spread stages (a ^^^ b) = spread stages a ^^^ spread stages b := by
  induction stages generalizing a b with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨s,mask⟩ := p
    simp only [spread, Nat.shiftLeft_xor_distrib]
    rw [show (a ^^^ b ^^^ (a <<< s ^^^ b <<< s)) =
      ((a ^^^ a <<< s) ^^^ (b ^^^ b <<< s)) by ac_rfl, Nat.and_xor_distrib_right, ih]

private theorem spread_zero (stages : List (ℕ × ℕ)) : spread stages 0 = 0 := by
  simpa using spread_xor stages 0 0

/-- The circuit squares the monomials in a half-open interval of input positions. -/
def BasisOn (stages : List (ℕ × ℕ)) (start count : ℕ) : Prop :=
  ∀ i < count, spread stages (1 <<< (start+i)) = 1 <<< (2*(start+i))

def checkBasisBlock (stages : List (ℕ × ℕ)) (start count : ℕ) : Bool :=
  (List.range count).all fun i => spread stages (1 <<< (start+i)) == 1 <<< (2*(start+i))

theorem basisOn_of_check {stages : List (ℕ × ℕ)} {start count : ℕ}
    (h : checkBasisBlock stages start count = true) : BasisOn stages start count := by
  simpa [BasisOn, checkBasisBlock, List.all_eq_true] using h

theorem BasisOn.append {stages : List (ℕ × ℕ)} {start k l : ℕ}
    (left : BasisOn stages start k) (right : BasisOn stages (start+k) l) :
    BasisOn stages start (k+l) := by
  intro i hi
  by_cases h : i < k
  · exact left i h
  · simpa only [Nat.add_assoc, Nat.add_sub_cancel' (Nat.le_of_not_lt h)] using right (i-k) (by omega)

/-- The basis test permits any circuit whose images are the right monomials. -/
def checkBasis (width : ℕ) (stages : List (ℕ × ℕ)) : Bool :=
  (List.range width).all fun i => spread stages (1 <<< i) == 1 <<< (2*i)

theorem checkBasis_of_basisOn {stages : List (ℕ × ℕ)} {n : ℕ} (h : BasisOn stages 0 n) :
    checkBasis n stages = true := by
  simpa [BasisOn, checkBasis, List.all_eq_true] using h

private theorem split_high_bit {a n : ℕ} (hlo : 2^n ≤ a) (hhi : a < 2^(n+1)) :
    a = (a % 2^n) ^^^ (1 <<< n) := by
  have hq : a / 2^n = 1 := by
    have h0 := Nat.two_pow_pos n
    have h1 := (Nat.le_div_iff_mul_le h0).2 (by simpa using hlo : 1 * 2^n ≤ a)
    have h2 := (Nat.div_lt_iff_lt_mul h0).2 (by simpa [pow_succ, Nat.mul_comm] using hhi : a < 2 * 2^n)
    omega
  calc
    a = (a % 2^n) ^^^ ((a / 2^n) <<< n) := by
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < n
      · simp [hi, Nat.not_le_of_lt hi]
      · simp [hi, Nat.le_of_not_lt hi, Nat.testBit_div_two_pow, Nat.sub_add_cancel (Nat.le_of_not_lt hi)]
    _ = _ := by rw [hq]

/-- Equality on the monomials suffices because squaring is additive in characteristic two. -/
theorem decode_spread {width a : ℕ} {stages : List (ℕ × ℕ)}
    (hc : checkBasis width stages = true) (ha : a < 2^width) :
    decode (spread stages a) = (decode a)^2 := by
  have basis : ∀ i < width, spread stages (1 <<< i) = 1 <<< (2*i) := by
    simpa [checkBasis, List.all_eq_true] using hc
  clear hc
  induction width generalizing a with
  | zero =>
    have hz : a=0 := by simpa using ha
    simp [hz, spread_zero]
  | succ n ih =>
    have low := fun i (hi : i < n) => basis i (by omega)
    by_cases hlo : a < 2^n
    · exact ih hlo low
    · have hs := split_high_bit (Nat.le_of_not_gt hlo) ha
      conv_lhs => rw [hs, spread_xor, decode_xor, ih (Nat.mod_lt _ (Nat.two_pow_pos _)) low,
        basis n (by omega)]
      conv_rhs => rw [hs, decode_xor, CharTwo.add_sq]
      simp [decode_shift_by, ← pow_mul, Nat.mul_comm]

/-- Use descending blocks of lengths 2^(k-1), ..., 1 to interleave zero bits. -/
def stagesFor (k : ℕ) : List (ℕ × ℕ) :=
  let full := 2^(2*2^k)-1
  (List.range k).reverse.map fun j =>
    let s := 2^j
    (s, full/(2^s+1))

/-- Append k one-bits to an exponent using X times a square at each step.
An input outside the certified width causes the check to fail. -/
def run (width n fuel : ℕ) (stages : List (ℕ × ℕ)) (js : List ℕ) : ℕ → ℕ → Option ℕ
  | 0, a => some a
  | k+1, a => if a < 2^width then
      run width n fuel stages js k (reduceHigh n js fuel ((spread stages a) <<< 1))
    else none

/-- Join independently checked runs at their common residue. -/
theorem run_append {width n fuel k l a b c : ℕ} {stages : List (ℕ × ℕ)} {js : List ℕ}
    (first : run width n fuel stages js k a = some b)
    (second : run width n fuel stages js l b = some c) :
    run width n fuel stages js (k+l) a = some c := by
  induction k generalizing a with
  | zero =>
    have he : a=b := Option.some.inj first
    simpa [he] using second
  | succ k ih =>
    simp only [run] at first
    rw [Nat.succ_add, run]
    split at first <;> simp_all

/-- Keep the block endpoints in the type so that checking a concatenation compares
integers without unfolding the whole polynomial computation. -/
structure PowerBlock (width n fuel : ℕ) (stages : List (ℕ × ℕ)) (js : List ℕ)
    (count a b : ℕ) : Prop where
  checked : run width n fuel stages js count a = some b

theorem PowerBlock.append {width n fuel k l a b c : ℕ} {stages : List (ℕ × ℕ)} {js : List ℕ}
    (first : PowerBlock width n fuel stages js k a b)
    (second : PowerBlock width n fuel stages js l b c) :
    PowerBlock width n fuel stages js (k+l) a c := ⟨run_append first.checked second.checked⟩

private noncomputable abbrev residue (f a : ℕ) := AdjoinRoot.mk (decode f) (decode a)

theorem run_sound {width n f fuel k a v : ℕ} {js : List ℕ} {stages : List (ℕ × ℕ)}
    (hc : checkBasis width stages = true) (hf : xorShifts js 1 = f)
    (hr : run width n fuel stages js k a = some v) {e : ℕ} (he : 0 < e)
    (ha : residue f a = AdjoinRoot.root (decode f)^(e-1)) :
    residue f v = AdjoinRoot.root (decode f)^(2^k*e-1) := by
  induction k generalizing a e with
  | zero =>
    have hv : a=v := Option.some.inj hr
    simpa [← hv] using ha
  | succ k ih =>
    simp only [run] at hr
    split at hr
    · rename_i hsmall
      have step : residue f (reduceHigh n js fuel ((spread stages a) <<< 1)) =
          AdjoinRoot.root (decode f)^(2*e-1) := by
        rw [residue, mk_reduceHigh _ _ _ _ _ hf, decode_shift, decode_spread hc hsmall, map_mul,
          map_pow, AdjoinRoot.mk_X]
        change _ * (residue f a)^2 = _
        rw [ha, ← pow_mul, ← pow_succ']
        congr 1
        omega
      simpa only [pow_succ, Nat.mul_assoc] using ih hr (by omega : 0 < 2*e) step
    · contradiction

open LucasLehmer.norm_num_ext

/-- A Lucas–Lehmer block with explicit start and end residues. -/
structure LucasBlock (q count a b : ℕ) : Prop where
  checked : sModNat_aux a q count = b

/-- Concatenate two blocks of the integer Lucas–Lehmer recurrence. -/
theorem LucasBlock.append {a b c q k l : ℕ} (first : LucasBlock q k a b)
    (second : LucasBlock q l b c) : LucasBlock q (k+l) a c := by
  have join (j : ℕ) : sModNat_aux a q (k+j) = sModNat_aux b q j := by
    induction j with
    | zero => simpa using first.checked
    | succ j ih => rw [Nat.add_succ, sModNat_aux, ih, sModNat_aux]
  exact ⟨(join l).trans second.checked⟩

theorem mersenne_prime_of_lucas_blocks {n : ℕ} (hn : 1 < n)
    (hc : LucasBlock (mersenne n) (n-2) (4 % mersenne n) 0) : (mersenne n).Prime := by
  have h := hc.checked
  apply lucas_lehmer_sufficiency n hn
  simp only [mersenne] at h
  rw [LucasLehmer.LucasLehmerTest, LucasLehmer.residue_eq_zero_iff_sMod_eq_zero n hn, ← sModNat_eq_sMod n _ hn,
    ← sModNat_aux_eq, h]
  rfl

theorem decode_trinomial_taps (n a : ℕ) :
    decode (xorShifts [n,a,0] 1) = (X : BinaryPoly)^n+(X^a+1) := by
  simp only [xorShifts, decode_xor, decode_shift_by, decode_one, decode_zero, pow_zero,
    mul_one, add_zero]

/-- A prime Mersenne group order and a successful run certify primitivity
for any supplied binary modulus of the stated degree. -/
theorem primitive_of_run {n f width fuel : ℕ} {js : List ℕ} {stages : List (ℕ × ℕ)}
    (hn : 1 < n) (hdeg : f.log2 = n) (hp : (mersenne n).Prime)
    (hc : checkBasis width stages = true) (hf : xorShifts js 1 = f)
    (hr : run width n fuel stages js n 1 = some 1) : Primitive (decode f) := by
  have hd : (decode f).natDegree = n := (natDegree_decode f).trans hdeg
  have hf0 : f ≠ 0 := by rintro rfl; simp at hdeg; omega
  have full := run_sound hc hf hr (e := 1) (by decide) (by simp [residue])
  have hpow : AdjoinRoot.root (decode f)^(mersenne n) = 1 := by
    simpa [mersenne, residue] using full.symm
  have hroot : AdjoinRoot.root (decode f) ≠ 1 := by
    intro he
    have hdiv : decode f ∣ (X-1 : BinaryPoly) := AdjoinRoot.mk_eq_zero.1 (by simp [AdjoinRoot.mk_X, he])
    have hle := natDegree_le_of_dvd hdiv (X_sub_C_ne_zero (1 : ZMod 2))
    change (decode f).natDegree ≤ (X-C (1 : ZMod 2)).natDegree at hle
    rw [natDegree_X_sub_C, hd] at hle
    omega
  apply primitive_of_order (monic_decode hf0) (hd ▸ by omega)
  rw [hd]
  exact ((Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hpow)).resolve_left
    (fun h => hroot (orderOf_eq_one_iff.1 h))

/-- Check the width, monomial images and full Mersenne power for a product pentanomial. -/
def checkProduct (n u v : ℕ) : Bool :=
  let stages := stagesFor ((n-1).log2+1)
  (productMask n u v).log2 == n && checkBasis n stages &&
    run n n 3 stages [n,u+v,u,v,0] n 1 == some 1

theorem primitive_product_of_check {n u v : ℕ} (hn : 1 < n) (hp : (mersenne n).Prime)
    (hc : checkProduct n u v = true) : Primitive (productCandidate n u v) := by
  simp only [checkProduct, Bool.and_eq_true, beq_iff_eq] at hc
  rw [← decode_productMask]
  apply primitive_of_run hn hc.1.1 hp hc.1.2 _ hc.2
  simp [xorShifts, productMask, Nat.shiftLeft_eq, Nat.xor_assoc]

end GF2Sparse.PackedSquare
