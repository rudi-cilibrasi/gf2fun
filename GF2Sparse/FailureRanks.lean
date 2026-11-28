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

end GF2Sparse.FailureRanks
