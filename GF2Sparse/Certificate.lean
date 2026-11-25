import GF2Sparse.Basic
import Mathlib.Data.Nat.Bitwise

/-! A bit represents the coefficient of the corresponding power of X. All
executable tests below have soundness proofs in mathlib's polynomial ring. -/

namespace GF2Sparse

open Polynomial

def positions (m : ℕ) : Finset ℕ :=
  (Finset.range (m.log2 + 1)).filter (fun i => m.testBit i)

private theorem bit_above {m i : ℕ} (h : m.log2 < i) : m.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by decide) h))

def decode (m : ℕ) : BinaryPoly :=
  .ofFinsupp ⟨positions m, fun i => if m.testBit i then 1 else 0, by
    intro i
    by_cases h : i < m.log2 + 1
    · simp [positions, h]
    · simp [positions, h, bit_above (show m.log2 < i by omega)]⟩

@[simp] theorem coeff_decode (m i : ℕ) :
    (decode m).coeff i = if m.testBit i then 1 else 0 := rfl

@[simp] theorem support_decode (m : ℕ) : (decode m).support = positions m := rfl

@[simp] theorem decode_zero : decode 0 = 0 := by ext; simp

@[simp] theorem decode_one : decode 1 = 1 := by
  ext i
  cases i <;> simp [Nat.testBit_succ, coeff_one]

theorem decode_injective : Function.Injective decode := by
  intro a b h
  apply Nat.eq_of_testBit_eq
  intro i
  have heq := congrArg (fun f : BinaryPoly => f.coeff i) h
  change (decode a).coeff i = (decode b).coeff i at heq
  rw [coeff_decode, coeff_decode] at heq
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

@[simp] theorem natDegree_decode (m : ℕ) : (decode m).natDegree = m.log2 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · apply natDegree_eq_of_le_of_coeff_ne_zero
    · exact natDegree_le_iff_coeff_eq_zero.2 fun i hi => by simp [bit_above hi]
    · simp [Nat.testBit_log2 hm]

theorem monic_decode {m : ℕ} (hm : m ≠ 0) : (decode m).Monic := by
  rw [Monic, ← coeff_natDegree]
  simp [Nat.testBit_log2 hm]

@[simp] theorem decode_xor (a b : ℕ) : decode (a ^^^ b) = decode a + decode b := by
  ext i
  simp only [coeff_decode, coeff_add, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> decide

@[simp] theorem decode_shift (a : ℕ) : decode (a <<< 1) = X * decode a := by
  ext i
  cases i with
  | zero => simp
  | succ i => simp [coeff_X_mul]

theorem decode_split (b : ℕ) :
    decode b = X * decode (b / 2) + (if b % 2 = 1 then 1 else 0) := by
  ext i
  cases i with
  | zero => split_ifs <;> simp_all
  | succ i => split_ifs <;> simp [coeff_X_mul, Nat.testBit_succ, coeff_one]

/-- One multiplication by X with a conditional subtraction of the modulus. -/
def step (n f a : ℕ) : ℕ :=
  let shifted := a <<< 1
  if shifted.testBit n then shifted ^^^ f else shifted

private noncomputable def residue (f a : ℕ) := AdjoinRoot.mk (decode f) (decode a)

private theorem residue_step (n f a : ℕ) :
    residue f (step n f a) = AdjoinRoot.root (decode f) * residue f a := by
  simp only [step, residue]
  split <;> simp

theorem decode_shift_by (a k : ℕ) : decode (a <<< k) = X ^ k * decode a := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.shiftLeft_add, decode_shift, ih, pow_succ', mul_assoc]

private theorem decode_split_at (a k : ℕ) :
    decode a = decode (a % 2 ^ k) + X ^ k * decode (a / 2 ^ k) := by
  rw [← decode_shift_by]
  ext i
  by_cases hi : i < k
  · simp [Nat.not_le_of_lt hi, hi]
  · simp [hi, Nat.le_of_not_lt hi, Nat.testBit_div_two_pow, Nat.sub_add_cancel (Nat.le_of_not_lt hi)]

private def spreadBits : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, b =>
    let shifted := spreadBits k (b / 2) <<< 2
    if b % 2 = 1 then shifted ^^^ 1 else shifted

private theorem decode_spreadBits (k b : ℕ) (hb : b < 2 ^ k) :
    decode (spreadBits k b) = (decode b) ^ 2 := by
  induction k generalizing b with
  | zero =>
    have : b = 0 := by simpa using hb
    simp [this, spreadBits]
  | succ k ih =>
    have hb' : b / 2 < 2 ^ k := by rw [pow_succ] at hb; omega
    conv_rhs => rw [decode_split b]
    by_cases h : b % 2 = 1 <;> simp [spreadBits, h, decode_shift_by, ih _ hb', CharTwo.add_sq, mul_pow]

/-- Spread eight bits over the even positions of a sixteen-bit word. -/
private def spreadByte (b : ℕ) : ℕ :=
  let nibbles := (b ||| (b <<< 4)) &&& 0x0f0f
  let pairs := (nibbles ||| (nibbles <<< 2)) &&& 0x3333
  (pairs ||| (pairs <<< 1)) &&& 0x5555

set_option maxRecDepth 4096 in
private theorem byte_table : ∀ b : Fin 256, spreadByte b = spreadBits 8 b := by decide +kernel

private def spreadBytes : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, a => spreadByte (a % 256) ^^^ (spreadBytes k (a / 256) <<< 16)

private theorem decode_spreadBytes (k a : ℕ) (ha : a < 256 ^ k) :
    decode (spreadBytes k a) = (decode a) ^ 2 := by
  induction k generalizing a with
  | zero =>
    have : a = 0 := by simpa using ha
    simp [this, spreadBytes]
  | succ k ih =>
    have hb : a % 256 < 256 := Nat.mod_lt _ (by decide)
    have hq : a / 256 < 256 ^ k := (Nat.div_lt_iff_lt_mul (by decide)).2 (pow_succ 256 k ▸ ha)
    conv_rhs => rw [decode_split_at a 8, CharTwo.add_sq, mul_pow, ← pow_mul]
    rw [spreadBytes, decode_xor, decode_shift_by, ih _ hq, byte_table ⟨_, hb⟩, decode_spreadBits _ _ hb]
    rfl

private def taps (f : ℕ) := (List.range (f.log2 + 1)).filter f.testBit

private theorem sum_taps (f : ℕ) : ((taps f).map (fun j => (X : BinaryPoly) ^ j)).sum = decode f := by
  unfold taps
  rw [← List.sum_toFinset _ (List.nodup_range.filter f.testBit), List.toFinset_filter, List.toFinset_range]
  ext i
  by_cases hi : i < f.log2 + 1
  · simp [coeff_X_pow, hi]
  · simp [coeff_X_pow, hi, bit_above (show f.log2 < i by omega)]

private def shiftedSum (a : ℕ) : List ℕ → ℕ
  | [] => 0
  | j :: js => (a <<< j) ^^^ shiftedSum a js

private theorem decode_shiftedSum (a : ℕ) (js : List ℕ) :
    decode (shiftedSum a js) = ((js.map (fun j => X ^ j)).sum : BinaryPoly) * decode a := by
  induction js with
  | nil => simp [shiftedSum]
  | cons j js ih => simp [shiftedSum, decode_shift_by, ih, add_mul]

/-- Carryless multiplication of two binary coefficient masks. -/
def maskProduct (a b : ℕ) : ℕ := shiftedSum b (taps a)

@[simp] theorem decode_maskProduct (a b : ℕ) :
    decode (maskProduct a b) = decode a * decode b := by
  rw [maskProduct, decode_shiftedSum, sum_taps]

/-- Cancel all terms at or above degree n in one XOR with a polynomial
multiple of f. Low interior exponents usually need only a few rounds. -/
private def reduce (n : ℕ) (js : List ℕ) : ℕ → ℕ → ℕ
  | 0, a => a
  | k + 1, a =>
    if a < 2 ^ n then a else reduce n js k (a ^^^ shiftedSum (a >>> n) js)

private theorem residue_reduce (n f k a : ℕ) :
    residue f (reduce n (taps f) k a) = residue f a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [reduce]
    split
    · rfl
    · rw [ih]
      simp [residue, decode_shiftedSum, sum_taps]

private def squareMod (n f a : ℕ) : ℕ :=
  reduce n (taps f) (2 * n + 1) (spreadBytes (a.log2 / 8 + 1) a)

private theorem residue_squareMod (n f a : ℕ) :
    residue f (squareMod n f a) = residue f a * residue f a := by
  have hb : a < 256 ^ (a.log2 / 8 + 1) := by
    change a < (2 ^ 8) ^ _
    rw [← pow_mul]
    exact Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  rw [squareMod, residue_reduce]
  simp only [residue, decode_spreadBytes _ _ hb, pow_two, map_mul]

/-- The k-bit square-and-multiply recurrence for powers of X. -/
def powBits (n f : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k + 1, e =>
    let r := powBits n f k (e / 2)
    let sq := squareMod n f r
    if e % 2 = 1 then step n f sq else sq

def xPow (n f e : ℕ) : ℕ := powBits n f (e.log2 + 1) e

/-- Every binary digit of the full-order exponent is one. Intermediate
residues allow blocks of the powering computation to be checked separately. -/
def mersenneStep (n f a : ℕ) : ℕ := step n f (squareMod n f a)

theorem xPow_mersenne (n f k : ℕ) (hk : 0 < k) :
    xPow n f (2 ^ k - 1) = (mersenneStep n f)^[k] 1 := by
  have hbits (j : ℕ) : powBits n f j (2 ^ j - 1) = (mersenneStep n f)^[j] 1 := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have hpos := Nat.two_pow_pos j
      have hd : (2 ^ (j+1) - 1) / 2 = 2 ^ j - 1 := by rw [pow_succ]; omega
      have hm : (2 ^ (j+1) - 1) % 2 = 1 := by rw [pow_succ]; omega
      rw [powBits, hd, hm, if_pos rfl, ih, Function.iterate_succ_apply']
      rfl
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hs : (2 ^ (j+1) - 1).log2 = j := by
    have := Nat.two_pow_pos j
    rw [Nat.log2_eq_iff] <;> rw [pow_succ] <;> omega
  simpa only [xPow, hs] using hbits (j+1)

private theorem residue_powBits (n f k e : ℕ) (he : e < 2 ^ k) :
    residue f (powBits n f k e) = AdjoinRoot.root (decode f) ^ e := by
  induction k generalizing e with
  | zero =>
    have : e = 0 := by simpa using he
    simp [this, powBits, residue]
  | succ k ih =>
    have he' : e / 2 < 2 ^ k := by rw [pow_succ] at he; omega
    by_cases h : e % 2 = 1
    · simp only [powBits, h, if_true, residue_step, residue_squareMod, ih _ he']
      nth_rw 3 [show e = e / 2 + e / 2 + 1 by omega]
      rw [pow_succ, pow_add, mul_comm]
    · simp only [powBits, h, if_false, residue_squareMod, ih _ he']
      rw [← pow_add, show e / 2 + e / 2 = e by omega]

private theorem residue_xPow (n f e : ℕ) :
    residue f (xPow n f e) = AdjoinRoot.root (decode f) ^ e :=
  residue_powBits n f _ e Nat.lt_log2_self

/-- A computed residue proves a polynomial congruence for the indicated power of X. -/
theorem dvd_X_pow_sub_decode {n f e r : ℕ} (he : xPow n f e = r) :
    decode f ∣ X ^ e - decode r := by
  apply AdjoinRoot.mk_eq_zero.1
  rw [map_sub, map_pow, AdjoinRoot.mk_X, sub_eq_zero]
  simpa only [residue, he] using (residue_xPow n f e).symm

/-- Distinct reduced bit strings are distinct elements of the quotient. -/
private theorem residue_ne_one {f r : ℕ} (hf : f ≠ 0) (hr : r ≠ 1)
    (hsmall : r < 2 ^ f.log2) (hn : 0 < f.log2) : residue f r ≠ 1 := by
  intro h
  have hxor := Nat.xor_lt_two_pow hsmall (Nat.one_lt_two_pow hn.ne')
  have hne : r ^^^ 1 ≠ 0 := fun hzero => hr (Nat.xor_eq_zero_iff.1 hzero)
  have hdeg : (decode (r ^^^ 1)).natDegree < (decode f).natDegree := by
    simpa only [natDegree_decode] using (Nat.log2_lt hne).2 hxor
  have hpoly : decode (r ^^^ 1) ≠ 0 := fun hzero => hne (decode_injective (hzero.trans decode_zero.symm))
  apply AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_decode hf) hpoly hdeg
  rw [decode_xor, decode_one, map_add, map_one]
  change residue f r + 1 = 0
  rw [h]
  simpa using congrArg (AdjoinRoot.of (decode f)) (show (1 : ZMod 2) + 1 = 0 by decide)

/-- Either the full exponent fails, or a positive exponent below it already
gives one. Both outcomes certify that the modulus is not primitive. -/
def excludesFullOrder (n f e : ℕ) : Bool :=
  let r := xPow n f (2 ^ n - 1)
  (r != 1 && r < 2 ^ n) || xPow n f e == 1

theorem excludesFullOrder_sound {n f e : ℕ} (hn : 0 < n) (hf : f ≠ 0) (hd : f.log2 = n)
    (he : 0 < e) (hlt : e < 2 ^ n - 1) (h : excludesFullOrder n f e = true) :
    ¬ Primitive (decode f) := by
  intro hp
  have ho : orderOf (AdjoinRoot.root (decode f)) = 2 ^ n - 1 := by
    rw [hp.2.2, natDegree_decode, hd]
  simp only [excludesFullOrder, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne,
    decide_eq_true_eq, beq_iff_eq] at h
  rcases h with ⟨hr, hsmall⟩ | hshort
  · apply residue_ne_one hf hr (hd ▸ hsmall) (hd ▸ hn)
    rw [residue_xPow, ← ho, pow_orderOf_eq_one]
  · have hpow : AdjoinRoot.root (decode f) ^ e = 1 := by
      rw [← residue_xPow n f, hshort]
      simp [residue]
    have hle := Nat.le_of_dvd he (orderOf_dvd_of_pow_eq_one hpow)
    rw [ho] at hle
    omega

/-- Prime factors are supplied with multiplicity. The caller supplies proofs
of their primality. The test checks their product and every required power. -/
def check (n f : ℕ) (factors : List ℕ) : Bool :=
  let N := 2 ^ n - 1
  n > 0 && f ≠ 0 && f.log2 == n && (positions f).card ≤ 5 &&
    factors.prod == N && xPow n f N == 1 &&
    factors.all (fun p =>
      let r := xPow n f (N / p)
      r != 1 && r < 2 ^ n)

theorem check_sound {n f : ℕ} {factors : List ℕ}
    (hprimes : ∀ p ∈ factors, p.Prime) (h : check n f factors = true) :
    (decode f).natDegree = n ∧ (decode f).support.card ≤ 5 ∧ Primitive (decode f) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨⟨hn, hf⟩, hdeg⟩, hwt⟩, hprod⟩, hfull⟩, hproper⟩ := h
  have hd : (decode f).natDegree = n := (natDegree_decode f).trans hdeg
  refine ⟨hd, hwt, primitive_of_prime_checks (monic_decode hf) (hd ▸ hn) ?_ ?_⟩
  · rw [hd, ← residue_xPow n f, hfull]
    simp [residue]
  · rw [hd]
    intro p hp hdvd
    have hmem := mem_list_primes_of_dvd_prod hp.prime
      (fun q hq => (hprimes q hq).prime) (hprod.symm ▸ hdvd)
    obtain ⟨hne, hlt⟩ := hproper p hmem
    rw [← residue_xPow n f]
    exact residue_ne_one hf hne (hdeg ▸ hlt) (hdeg ▸ hn)

/-- Append the low k bits of e to an exponent whose residue is already a. -/
def appendBits (n f a : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => a
  | k + 1, e =>
    let sq := squareMod n f (appendBits n f a k (e / 2))
    if e % 2 = 1 then step n f sq else sq

private theorem residue_appendBits (n f a k e : ℕ) (he : e < 2 ^ k) :
    residue f (appendBits n f a k e) =
      residue f a ^ (2 ^ k) * AdjoinRoot.root (decode f) ^ e := by
  induction k generalizing e with
  | zero =>
    have : e = 0 := by simpa using he
    simp [this, appendBits]
  | succ k ih =>
    have hdiv : e / 2 < 2 ^ k := by rw [pow_succ] at he; omega
    by_cases h : e % 2 = 1
    · rw [appendBits, if_pos h, residue_step, residue_squareMod, ih _ hdiv]
      nth_rw 3 [show e = e / 2 + e / 2 + 1 by omega]
      rw [pow_succ 2, pow_mul, pow_succ (AdjoinRoot.root _) (_ + _), pow_add]
      ring
    · rw [appendBits, if_neg h, residue_squareMod, ih _ hdiv]
      nth_rw 3 [show e = e / 2 + e / 2 by omega]
      rw [pow_succ 2, pow_mul, pow_add]
      ring

/-- The list gives earlier residues in reverse order, ending at 1.
Each check starts from the supplied previous residue, bounding evaluation depth. -/
def powerBlocks (n f bits : ℕ) : ℕ → ℕ → List ℕ → Bool
  | e, r, [] => e == 0 && r == 1
  | e, r, a :: rest =>
    appendBits n f a bits (e % 2 ^ bits) == r &&
      powerBlocks n f bits (e / 2 ^ bits) a rest

private theorem powerBlocks_sound (n f bits e r : ℕ) (blocks : List ℕ)
    (h : powerBlocks n f bits e r blocks = true) :
    residue f r = AdjoinRoot.root (decode f) ^ e := by
  induction blocks generalizing e r with
  | nil =>
    simp only [powerBlocks, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, h.2, residue]
  | cons a rest ih =>
    obtain ⟨hb, ht⟩ := Bool.and_eq_true_iff.1 h
    rw [← beq_iff_eq.1 hb, residue_appendBits _ _ _ _ _ (Nat.mod_lt _ (by positivity)),
      ih _ _ ht, ← pow_mul, ← pow_add, Nat.mul_comm, Nat.div_add_mod]

theorem root_pow_one_of_blocks (n f bits e : ℕ) (blocks : List ℕ)
    (h : powerBlocks n f bits e 1 blocks = true) : AdjoinRoot.root (decode f) ^ e = 1 := by
  simpa [residue] using (powerBlocks_sound n f bits e 1 blocks h).symm

theorem root_pow_ne_one_of_blocks (n f bits e r : ℕ) (blocks : List ℕ)
    (h : powerBlocks n f bits e r blocks = true) (hf : f ≠ 0) (hr : r ≠ 1)
    (hs : r < 2 ^ f.log2) (hn : 0 < f.log2) : AdjoinRoot.root (decode f) ^ e ≠ 1 := by
  rw [← powerBlocks_sound n f bits e r blocks h]
  exact residue_ne_one hf hr hs hn

end GF2Sparse
