import GF2Sparse.Table
import GF2Sparse.OrderBound

/-! A short certificate for a missing order factor. A nonzero residue y
satisfying y^(2^d) = X*y exhibits X as a (2^d-1)-st power. -/

namespace GF2Sparse

open Polynomial

private def stretch (stride : ℕ) : ℕ → ℕ → ℕ
  | 0, w => w%2
  | k+1, w =>
    let half := 2^k
    stretch stride k (w % 2^half) ^^^ (stretch stride k (w / 2^half) <<< (half*stride))

private theorem decode_stretch (d k w : ℕ) (hw : w < 2^(2^k)) :
    decode (stretch (2^d) k w) = (decode w)^(2^d) := by
  induction k generalizing w with
  | zero =>
    have h : w < 2 := by simpa using hw
    interval_cases w <;> simp [stretch]
  | succ k ih =>
    have hbound : w < 2^(2^k) * 2^(2^k) := by
      rwa [pow_succ 2 k, Nat.mul_two, pow_add] at hw
    have split : decode w = decode (w % 2^(2^k)) + X^(2^k) * decode (w / 2^(2^k)) := by
      rw [← decode_shift_by]
      ext i
      by_cases hi : i < 2^k
      · simp [hi, Nat.not_le_of_lt hi]
      · simp [hi, Nat.le_of_not_lt hi, Nat.testBit_div_two_pow, Nat.sub_add_cancel (Nat.le_of_not_lt hi)]
    conv_rhs => rw [split]
    rw [stretch, decode_xor, decode_shift_by, ih _ (Nat.mod_lt _ (Nat.two_pow_pos _)),
      ih _ ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 hbound), add_pow_expChar_pow, mul_pow, ← pow_mul]

private theorem stretch_bound (w : ℕ) : w < 2^(2^(w.log2.log2+1)) :=
  Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt Nat.lt_log2_self))

private def xorShifts : List ℕ → ℕ → ℕ
  | [], _ => 0
  | j::js, a => (a <<< j) ^^^ xorShifts js a

private theorem decode_xorShifts (js : List ℕ) (w : ℕ) :
    decode (xorShifts js w) = decode (xorShifts js 1) * decode w := by
  induction js with
  | nil => simp [xorShifts]
  | cons j js ih => simp [xorShifts, decode_shift_by, ih, add_mul]

private def reduceHigh (n : ℕ) (js : List ℕ) : ℕ → ℕ → ℕ
  | 0, a => a
  | k+1, a => if a < 2^n then a else reduceHigh n js k (a ^^^ xorShifts js (a >>> n))

private theorem mk_reduceHigh (n f k a : ℕ) (js : List ℕ) (hf : xorShifts js 1 = f) :
    AdjoinRoot.mk (decode f) (decode (reduceHigh n js k a)) = AdjoinRoot.mk (decode f) (decode a) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [reduceHigh]
    split
    · rfl
    · rw [ih]
      simp [decode_xorShifts, hf]

/-- Check y^(2^d) = X*y using one bit mask for y. The fuel bounds
the number of reductions; a true result always proves the congruence. -/
def frobeniusPowerCheck (d n f w fuel : ℕ) (js : List ℕ) : Bool :=
  xorShifts js 1 == f && reduceHigh n js fuel (stretch (2^d) (w.log2.log2+1) w ^^^ (w <<< 1)) == 0

theorem order_dvd_of_frobeniusPowerCheck {d n f w fuel : ℕ} {js : List ℕ} (hf : Irreducible (decode f))
    (hn : f.log2 = n) (hw : w ≠ 0) (hsmall : w.log2 < n) (hd : 2^d-1 ∣ 2^n-1)
    (h : frobeniusPowerCheck d n f w fuel js = true) :
    orderOf (AdjoinRoot.root (decode f)) ∣ (2^n-1)/(2^d-1) := by
  classical
  letI : Fact (Irreducible (decode f)) := ⟨hf⟩
  letI : CharP (AdjoinRoot (decode f)) 2 := charP_of_injective_ringHom (AdjoinRoot.of _).injective 2
  let e := (AdjoinRoot.powerBasisAux hf.ne_zero).equivFun.toEquiv
  letI : Fintype (AdjoinRoot (decode f)) := Fintype.ofEquiv _ e.symm
  let y := AdjoinRoot.mk (decode f) (decode w)
  have hw' : decode w ≠ 0 := fun he => hw (decode_injective (he.trans decode_zero.symm))
  have hy : y ≠ 0 := by
    intro he
    have hle := natDegree_le_of_dvd (AdjoinRoot.mk_eq_zero.1 he) hw'
    simp only [natDegree_decode, hn] at hle
    omega
  simp only [frobeniusPowerCheck, Bool.and_eq_true, beq_iff_eq] at h
  have he := mk_reduceHigh n f fuel (stretch (2^d) (w.log2.log2+1) w ^^^ (w <<< 1)) js h.1
  rw [h.2, decode_zero, map_zero,
      decode_xor, map_add, decode_stretch _ _ _ (stretch_bound _), map_pow, decode_shift,
      map_mul, AdjoinRoot.mk_X] at he
  have hroot : y^(2^d-1) = AdjoinRoot.root (decode f) := by
    apply mul_right_cancel₀ hy
    rw [← pow_succ, Nat.sub_add_cancel (Nat.two_pow_pos d)]
    exact CharTwo.add_eq_zero.1 he.symm
  apply orderOf_dvd_of_pow_eq_one
  rw [← hroot, ← pow_mul, Nat.mul_div_cancel' hd]
  have hfull := FiniteField.pow_card_sub_one_eq_one y hy
  simpa only [card_adjoinRoot hf.ne_zero, natDegree_decode, hn] using hfull

private def witnessPower (n fuel : ℕ) (js : List ℕ) (w : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k+1, e =>
    let a := witnessPower n fuel js w k (e/2)
    let sq := reduceHigh n js fuel (stretch 2 (a.log2.log2+1) a)
    if e%2 = 0 then sq else reduceHigh n js fuel (maskProduct sq w)

private theorem mk_witnessPower (n f fuel : ℕ) (js : List ℕ) (w : ℕ)
    (hf : xorShifts js 1 = f) (k e : ℕ) (hb : e < 2^k) :
    AdjoinRoot.mk (decode f) (decode (witnessPower n fuel js w k e)) =
      AdjoinRoot.mk (decode f) (decode w)^e := by
  induction k generalizing e with
  | zero =>
    have he : e = 0 := by simpa using hb
    simp [he, witnessPower]
  | succ k ih =>
    have he : e/2 < 2^k := (Nat.div_lt_iff_lt_mul (by decide)).2 (by simpa [pow_succ] using hb)
    let a := witnessPower n fuel js w k (e/2)
    let sq := reduceHigh n js fuel (stretch 2 (a.log2.log2+1) a)
    have hs : AdjoinRoot.mk (decode f) (decode sq) = AdjoinRoot.mk (decode f) (decode w)^(e/2*2) := by
      have hsquare : decode (stretch 2 (a.log2.log2+1) a) = (decode a)^2 := by
        simpa only [pow_one] using decode_stretch 1 (a.log2.log2+1) a (stretch_bound a)
      rw [show sq = _ from rfl, mk_reduceHigh _ _ _ _ _ hf, hsquare, map_pow]
      change (AdjoinRoot.mk (decode f) (decode (witnessPower n fuel js w k (e/2))))^2 = _
      rw [ih _ he, pow_mul]
    change AdjoinRoot.mk (decode f) (decode (if e%2 = 0 then sq else _)) = _
    split
    · rename_i h
      rw [hs, show e/2*2=e by omega]
    · rename_i h
      rw [mk_reduceHigh _ _ _ _ _ hf, decode_maskProduct, map_mul, hs, ← pow_succ]
      congr 1
      omega

/-- A mask for an m-th root of X suffices to check a missing order
factor, even if the remaining cofactor of the group size is unfactored. -/
def rootPowerCheck (m n f w fuel : ℕ) (js : List ℕ) : Bool :=
  xorShifts js 1 == f && witnessPower n fuel js w (m.log2+1) m == 2

theorem order_dvd_of_rootPowerCheck {m n f w fuel : ℕ} {js : List ℕ}
    (hf : Irreducible (decode f)) (hn : f.log2 = n) (hc : (decode f).coeff 0 = 1)
    (hm : 0 < m) (hd : m ∣ 2^n-1) (h : rootPowerCheck m n f w fuel js = true) :
    orderOf (AdjoinRoot.root (decode f)) ∣ (2^n-1)/m := by
  classical
  letI : Fact (Irreducible (decode f)) := ⟨hf⟩
  let e := (AdjoinRoot.powerBasisAux hf.ne_zero).equivFun.toEquiv
  letI : Fintype (AdjoinRoot (decode f)) := Fintype.ofEquiv _ e.symm
  simp only [rootPowerCheck, Bool.and_eq_true, beq_iff_eq] at h
  have he := mk_witnessPower n f fuel js w h.1 (m.log2+1) m Nat.lt_log2_self
  have htwo : decode 2 = (X : BinaryPoly) := by simpa only [pow_one] using decode_pow_two 1
  rw [h.2, htwo, AdjoinRoot.mk_X] at he
  let z := AdjoinRoot.mk (decode f) (decode w)
  have hz : z ≠ 0 := by
    intro hz
    change AdjoinRoot.root (decode f) = z^m at he
    rw [hz, zero_pow hm.ne'] at he
    exact (root_unit hc).ne_zero he
  apply orderOf_dvd_of_pow_eq_one
  rw [he, ← pow_mul, Nat.mul_div_cancel' hd]
  have full := FiniteField.pow_card_sub_one_eq_one z hz
  simpa only [card_adjoinRoot hf.ne_zero, natDegree_decode, hn] using full

end GF2Sparse
