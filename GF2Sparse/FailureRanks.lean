import GF2Sparse.RootProducts
import Mathlib.Analysis.Real.Pi.Bounds

/-! Finite moment and integer bounds for an omitted prime divisor of a root order. -/

namespace GF2Sparse.FailureRanks

/-- A lower correlation and an upper test-function energy give a lower second moment. -/
theorem square_sum_of_correlation {ι : Type*} [Fintype ι] (s t : ι → ℝ)
    {c e : ℝ} (hc : 0 ≤ c) (he : 0 < e)
    (hcor : c ≤ ∑ i, s i * t i) (henergy : (∑ i, t i^2) ≤ e) :
    c^2/e ≤ ∑ i, s i^2 := by
  apply (div_le_iff₀ he).mpr
  calc
    c^2 ≤ (∑ i, s i * t i)^2 := by gcongr
    _ ≤ (∑ i, s i^2) * ∑ i, t i^2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ s t
    _ ≤ (∑ i, s i^2) * e := by gcongr

/-- Round the sums of 1/t² and 1/t over the first m odd frequencies outwards. -/
private def certifies (n m bound least target : ℕ) : Bool := Id.run do
  let scale : ℕ := 10^9
  let frequencies := (List.range m).map fun i => 2*i+1
  let squares : ℕ := (frequencies.map fun t => scale / (t*t)).sum
  let first : ℕ := (frequencies.map fun t => scale / t).sum
  let aLow : ℚ := (squares : ℚ) / scale
  let aHigh : ℚ := ((squares+m : ℕ) : ℚ) / scale
  let vHigh : ℚ := ((first+m : ℕ) : ℚ) / scale
  let corr : ℚ := (2500/3927) * (aLow - ((n-1 : ℕ) : ℚ) * vHigh / bound)
    - (4*m : ℚ) / (least : ℚ)^2
  return decide (0 < corr ∧ target*aHigh < 2*n*corr^2)

/-- The rational lower bound uses π < 3.1416. -/
theorem reciprocal_pi_bound : (2500/3927 : ℝ) < 2/Real.pi := by
  apply (lt_div_iff₀ Real.pi_pos).mpr
  nlinarith [Real.pi_lt_d4]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem six_integer_moment_bounds :
    certifies 1229 128 (2^23) 818085338814611458 1226 ∧
    certifies 1231 128 (2^21) (2+2*1231*2^32) 1225 ∧
    certifies 1237 64 (2^20) (2+2*1237*2^32) 1225 ∧
    certifies 1243 24 (2^20) (2+2*1243*2^32) 1225 ∧
    certifies 1249 24 (2^19) (2+2*1249*2^32) 1225 ∧
    certifies 1259 16 (2^19) (2+2*1259*2^32) 1225 := by
  decide +kernel

/-- Use one absolute imbalance per sign pair. Odd imbalances above 35 or 33
give light subsets of at most 596 or 597 positions, respectively. -/
theorem degree1229_light_pairs {ι : Type*} [Fintype ι] (d : ι → ℕ)
    (hb : ∀ i, d i ≤ 1229) (hsize : 818085338814611458 ≤ 2 * Fintype.card ι + 1)
    (hm : 1226 * Fintype.card ι < ∑ i, d i^2) :
    270000000000 < (Finset.univ.filter (fun i => 35 < d i)).card ∧
    37000000000000 < (Finset.univ.filter (fun i => 33 < d i)).card := by
  have h₁ := square_sum_le_of_threshold d 35 1229 (by decide) hb
  have h₂ := square_sum_le_of_threshold d 33 1229 (by decide) hb
  norm_num only [Nat.reducePow, Nat.reduceSub] at h₁ h₂
  omega

/-- Exchanging opposite digits at distance two moves one factor from the larger side. -/
theorem balance_signed_products {p q r : ℕ} (h : q ≤ p) :
    let t := min r ((p-q)/2)
    max (p-t) (q+t) ≤ max ((p+q+1)/2) (p-r) := by
  dsimp
  omega

private def digitPotential : List ℤ :=
  [0,0,0,0,-6,-6,-6,-6,-2,-2,-2,-2,-2,-2,-14,-14,0,0,0,0,0,0,0,0]

private def digitExcess (i : ℕ) : ℤ :=
  (if 4 ≤ i ∧ i < 8 then 1 else 0) - (if 16 ≤ i ∧ i < 20 then 1 else 0) -
    (if i = 19 then 2 else 0)

private def digitStep (i : ℕ) : ℤ :=
  12*digitExcess i + 1 + digitPotential.getD i 0 - digitPotential.getD ((2*i)%24) 0

/-- The 24 cells for the half-period antisymmetric representative of the exchange count. -/
theorem exchange_step_arithmetic :
    (∀ i ∈ List.range 12, digitPotential.getD (2*i) 0 = digitPotential.getD (2*i+1) 0 ∧
      digitStep (i+12) = -digitStep i) ∧
    ((List.range 24).map digitExcess).sum = -2 ∧
    ((List.range 24).map (fun i => (digitStep i)^2)).sum = 1576 ∧
    ((List.range 24).map (fun i => (digitStep i).natAbs)).foldl max 0 = 21 ∧
    ((List.range 24).map (fun i => (digitStep i-digitStep ((i+23)%24)).natAbs)).sum = 84 := by
  decide +kernel

private def leastOrderPrime : ℚ := 8317007399072301058

private def spectralCheck (energy height variation main tail total : ℚ) : Prop :=
  1229*(energy+2*height*variation/leastOrderPrime) < main^2 ∧
  (1229*variation)^2*(1/(36*2^20)+3/leastOrderPrime) < tail^2 ∧
  leastOrderPrime/(leastOrderPrime-1)*(main+tail)^2 < total^2

/-- Outward square-root bounds and the counts of unordered collisions. -/
theorem short_collision_arithmetic :
    let j := leastOrderPrime
    let halfWeight := 1229*(j+1)/(6*(j-1))
    spectralCheck (1/3) 1 4 (20241/1000) (801/1000) (21044/1000) ∧
    spectralCheck (197/432) (7/4) 7 (23674/1000) (1401/1000) (25076/1000) ∧
    12*10^15 < (j-1)/2*(1-(halfWeight+21044/2000)/216) ∧
    26*10^14 < (j-1)/2*(1-(halfWeight+1/2+3*(25076/1000)^2/1229)/207) := by
  dsimp only [spectralCheck]
  decide +kernel


/-- Split a correlation at a threshold for the absolute value of its first argument. -/
theorem correlation_le_threshold {ι : Type*} [Fintype ι] (s v : ι → ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : ∀ i, |s i| ≤ b) :
    ∑ i, s i*v i ≤ a*(∑ i, |v i|) +
      b*∑ i ∈ Finset.univ.filter (fun i => a < |s i|), |v i| := by
  classical
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  calc
    s i*v i ≤ |s i| * |v i| := by
      rw [← abs_mul]
      exact le_abs_self _
    _ ≤ _ := by
      split_ifs with h
      · exact le_add_of_nonneg_of_le (mul_nonneg ha (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (hb i) (abs_nonneg _))
      · simpa only [add_zero] using mul_le_mul_of_nonneg_right (le_of_not_gt h) (abs_nonneg (v i))

/-- Cauchy--Schwarz bounds the selected absolute values using the size of the selected set. -/
theorem subset_sum_abs_sq {ι : Type*} [Fintype ι] (u : Finset ι) (v : ι → ℝ) :
    (∑ i ∈ u, |v i|)^2 ≤ (u.card : ℝ)*(∑ i, v i^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq u (fun _ => (1 : ℝ)) (fun i => |v i|)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ u) (fun i _ _ => sq_nonneg (v i)))
    (Nat.cast_nonneg _))

/-- The cubic projection, its residual, and three population bounds rounded outwards. -/
theorem cubic_failure_arithmetic :
    let j := leastOrderPrime
    let b : ℚ := 2^20
    let t : ℚ := 65535
    let lo : ℚ := 31415/10000
    let hi : ℚ := 31416/10000
    let m₂ : ℚ := 1229/2
    let m₄ : ℚ := 1229*7359/8
    let m₆ : ℚ := 1229*90074545/32
    let d : ℚ := 26357323/1000
    let high := fun (a : ℚ) => j/2*((1405565-a*d)/(1229*58818))^2
    1229/(t-1) < (136944/1000000)^2 ∧
    4/(lo^2*b)+1/j < (62172/100000000)^2 ∧
    2*1229*t^2/j^2+2/lo*(136944/1000000)+1229*(62172/100000000) < 85128/100000 ∧
    1229*(hi/(4*j^2)+2*1228/(lo*b)) < 91632/100000 ∧
    m₆-m₄^2/m₂ < (37142154/1000)^2 ∧ m₂*m₄ < d^2 ∧ m₆ < 58818^2 ∧
    1405565 < 1229*(735615/100)/(2*hi) - m₄/m₂*(91632/100000)
      - (85128/100000)*(37142154/1000) ∧
    53*d < 1405565 ∧ 59*10^9 < high 53 ∧ 29*10^11 < high 51 ∧ 10^13 < high 49 := by
  decide +kernel

end GF2Sparse.FailureRanks
