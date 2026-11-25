import GF2Sparse.Certificate

/-! A Bézout certificate excluding three consecutive product-one conditions.
The binary masks encode Laurent polynomials after clearing powers of t. -/

namespace GF2Sparse.DyadicCertificate

open Polynomial

/-- Coefficients of the image cubic for h(X) = (1+X²)(1+X³). -/
def sumImage [Add R] [Mul R] [Pow R ℕ] (u v : R) : R :=
  u ^ 5 + u ^ 3 * v + u ^ 3 + u * v ^ 2 + u * v + v

def pairsImage [Add R] [Mul R] [Pow R ℕ] (u v : R) : R :=
  u ^ 3 * v ^ 2 + u ^ 3 * v + u ^ 2 * v ^ 3 + u ^ 2 * v + u ^ 2 +
    u * v ^ 2 + u * v + v ^ 5 + v ^ 3 + v ^ 2

def productImage [Add R] [Mul R] [Pow R ℕ] (u v : R) : R :=
  (u + v) ^ 3 * ((u + v) ^ 2 + u * v)

def stepPair [Add R] [Mul R] [Pow R ℕ] (p : R × R) : R × R :=
  (sumImage p.1 p.2, pairsImage p.1 p.2)

private structure Laurent where
  num : ℕ
  den : ℕ
  deriving DecidableEq, Repr

private instance : Add Laurent where
  add a b :=
    let k := max a.den b.den
    ⟨(a.num <<< (k - a.den)) ^^^ (b.num <<< (k - b.den)), k⟩

private instance : Mul Laurent where
  mul a b := ⟨maskProduct a.num b.num, a.den + b.den⟩

private def oneL : Laurent := ⟨1, 0⟩
private def zeroL : Laurent := ⟨0, 0⟩
private def varL : Laurent := ⟨2, 0⟩
private def relationL : Laurent := ⟨33, 5⟩  -- (t⁵ + 1)/t⁵

variable {K : Type*} [Field K] [Algebra (ZMod 2) K]

private noncomputable def valL (t : K) (a : Laurent) : K :=
  aeval t (decode a.num) / t ^ a.den

private theorem valL_add {t : K} (ht : t ≠ 0) (a b : Laurent) :
    valL t (a + b) = valL t a + valL t b := by
  let k := max a.den b.den
  change (aeval t (decode ((a.num <<< (k - a.den)) ^^^ (b.num <<< (k - b.den)))) / t ^ k) = _
  simp only [decode_xor, decode_shift_by, map_add, map_mul, map_pow, aeval_X, add_div, valL]
  have align (c : Laurent) (hc : c.den ≤ k) :
      t ^ (k - c.den) * (aeval t) (decode c.num) / t ^ k = (aeval t) (decode c.num) / t ^ c.den := by
    conv_lhs => rw [show k = (k - c.den) + c.den from (Nat.sub_add_cancel hc).symm]
    simp only [Nat.add_sub_cancel, pow_add]
    field_simp
  rw [align a (le_max_left ..), align b (le_max_right ..)]

private theorem valL_mul (t : K) (a b : Laurent) : valL t (a * b) = valL t a * valL t b := by
  change aeval t (decode (maskProduct a.num b.num)) / t ^ (a.den + b.den) = _
  rw [decode_maskProduct, map_mul, pow_add, ← div_mul_div_comm]
  rfl

private theorem valL_one (t : K) : valL t oneL = 1 := by simp [valL, oneL]
private theorem valL_zero (t : K) : valL t zeroL = 0 := by simp [valL, zeroL]
private theorem valL_var (t : K) : valL t varL = t := by
  have h : decode 2 = X := by simpa using decode_shift 1
  simp [valL, varL, h]

private theorem valL_relation {t : K} (ht : t ≠ 0) : valL t relationL = 1 + 1 / t ^ 5 := by
  have he : decode 33 = X ^ 5 + 1 := by
    change decode ((1 <<< 5) ^^^ 1) = _
    rw [decode_xor, decode_shift_by, decode_one, mul_one]
  simp only [valL, relationL, he, map_add, map_pow, aeval_X, map_one, add_div, div_self (pow_ne_zero 5 ht)]

/-- a + bz with z² = z + 1 + t⁻⁵. -/
private structure Quad where
  a : Laurent
  b : Laurent
  deriving DecidableEq, Repr

private instance : Add Quad where
  add x y := ⟨x.a + y.a, x.b + y.b⟩

private instance : Mul Quad where
  mul x y :=
    let bd := x.b * y.b
    ⟨x.a * y.a + relationL * bd, x.a * y.b + x.b * y.a + bd⟩

private def oneQ : Quad := ⟨oneL, zeroL⟩

private def powQ (x : Quad) : ℕ → Quad
  | 0 => oneQ
  | n + 1 => powQ x n * x

private instance : Pow Quad ℕ := ⟨powQ⟩

private noncomputable def valQ (t z : K) (x : Quad) := valL t x.a + valL t x.b * z

private theorem valQ_one (t z : K) : valQ t z oneQ = 1 := by
  simp [valQ, oneQ, valL_one, valL_zero]

private theorem valQ_add {t z : K} (ht : t ≠ 0) (x y : Quad) :
    valQ t z (x + y) = valQ t z x + valQ t z y := by
  change valL t (x.a + y.a) + valL t (x.b + y.b) * z = _
  rw [valL_add ht, valL_add ht]
  unfold valQ
  ring

private theorem valQ_mul {t z : K} (ht : t ≠ 0) (hz : z*z = z + valL t relationL) (x y : Quad) :
    valQ t z (x * y) = valQ t z x * valQ t z y := by
  change valL t (x.a * y.a + relationL * (x.b * y.b)) +
    valL t (x.a * y.b + x.b * y.a + x.b * y.b) * z = _
  simp only [valL_add ht, valL_mul, valQ]
  linear_combination -(valL t x.b * valL t y.b) * hz

private theorem valQ_pow {t z : K} (ht : t ≠ 0) (hz : z*z = z + valL t relationL)
    (x : Quad) (n : ℕ) : valQ t z (x ^ n) = valQ t z x ^ n := by
  induction n with
  | zero => exact (valQ_one t z).trans (pow_zero _).symm
  | succ n ih => exact (valQ_mul ht hz (x ^ n) x).trans (by rw [ih, pow_succ])

private def normQ (x : Quad) : Laurent := x.a*x.a + x.a*x.b + relationL*(x.b*x.b)

private theorem val_normQ [CharP K 2] {t z : K} (ht : t ≠ 0) (hz : z*z = z + valL t relationL)
    (x : Quad) : valL t (normQ x) = valQ t z x * valQ t (z+1) x := by
  simp only [normQ, valL_add ht, valL_mul, valQ]
  grind only

private def start : Quad × Quad := (⟨zeroL, varL⟩, ⟨varL, varL⟩)
private def normDefect (p : Quad × Quad) := normQ (productImage p.1 p.2 + oneQ)

-- These multipliers come from the extended Euclidean algorithm on the two
-- normalized norms. The shifts undo their respective denominators.
private def bezoutA : Laurent :=
  ⟨0x2671346677a898800afce8a9a9f570d7da770dc7a0737a7258b5d25702dec176222483fee8098c55568dab675e43cef3beee13af5c3e18ba19ed0e365d6d95e24e26e3 <<< 57, 0⟩
private def bezoutB : Laurent := ⟨0x2f77e0d8291d51b63da30a02 <<< 321, 0⟩

private def combination : Laurent :=
  bezoutA * normDefect (stepPair start) + bezoutB * normDefect (stepPair (stepPair start))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem combination_one : combination.num = 1 <<< combination.den := by decide +kernel

private theorem val_combination {t : K} (ht : t ≠ 0) : valL t combination = 1 := by
  rw [valL, combination_one, decode_shift_by, decode_one, mul_one, map_pow, aeval_X,
    div_self (pow_ne_zero _ ht)]

/-- The product defect and its first two iterates never vanish together.
The statement holds in every extension field of F₂, including its closure. -/
theorem no_three_iterates [CharP K 2] (u v : K)
    (h₀ : productImage u v = 1)
    (h₁ : let p := stepPair (u,v); productImage p.1 p.2 = 1)
    (h₂ : let p := stepPair (stepPair (u,v)); productImage p.1 p.2 = 1) : False := by
  let t := u + v
  have ht : t ≠ 0 := by
    intro h
    change t ^ 3 * (t ^ 2 + u*v) = 1 at h₀
    simp [h] at h₀
  let z := u/t
  have htu : t*z = u := by dsimp [z]; field_simp
  have htv : t*(z+1) = v := by rw [mul_add, htu, mul_one]; dsimp [t]; grind
  have he : t ^ 5 * (1 + z * (z + 1)) = 1 := by
    calc
      _ = t ^ 3 * (t ^ 2 + (t*z) * (t*(z+1))) := by ring
      _ = 1 := by rw [htu, htv]; exact h₀
  have hz : z*z = z + valL t relationL := by
    rw [valL_relation ht]
    field_simp
    grind only
  let evalPair (p : Quad × Quad) := (valQ t z p.1, valQ t z p.2)
  have hs : evalPair start = (u,v) := by
    apply Prod.ext
    · simpa [evalPair, start, valQ, valL_zero, valL_var] using htu
    · change valQ t z ⟨varL, varL⟩ = v
      rw [valQ, valL_var, htu]
      dsimp [t]
      grind
  have hstep (p : Quad × Quad) : evalPair (stepPair p) = stepPair (evalPair p) := by
    simp only [evalPair, stepPair, sumImage, pairsImage, valQ_add ht, valQ_mul ht hz, valQ_pow ht hz]
  have hnorm (p : Quad × Quad) (hp : productImage (evalPair p).1 (evalPair p).2 = 1) :
      valL t (normDefect p) = 0 := by
    have h : valQ t z (productImage p.1 p.2) = 1 := by
      simpa only [productImage, evalPair, valQ_pow ht hz, valQ_add ht, valQ_mul ht hz] using hp
    rw [normDefect, val_normQ ht hz, valQ_add ht, h, valQ_one, CharTwo.add_self_eq_zero, zero_mul]
  have hfirst := hnorm (stepPair start) (by rwa [hstep, hs])
  have hsecond := hnorm (stepPair (stepPair start)) (by rwa [hstep, hstep, hs])
  have h := val_combination ht
  rw [combination, valL_add ht, valL_mul, valL_mul, hfirst, hsecond, mul_zero, mul_zero, zero_add] at h
  exact zero_ne_one h

end GF2Sparse.DyadicCertificate
