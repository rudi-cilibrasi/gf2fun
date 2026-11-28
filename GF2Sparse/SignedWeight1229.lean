import GF2Sparse.SelbergWeight

/-! Integer and rational checks for the signed coefficient-weight bound at degree 1229. -/

namespace GF2Sparse.SignedWeight1229

private def frequency : List ℕ :=
  [101808133126899,25258413561571,6081049088867,1416285931840,317871134706,
   68414645634,14029353531,2716735113,490355574,80796147,11703889,1371565,100000]

private def overlap (w : ℕ) : ℕ :=
  ((List.range (w+1)).map fun a =>
    Nat.fast_choose w a * ((List.range (13-max a (w-a))).map fun o =>
      Nat.fast_choose (516-w) o * frequency.getD (o+a) 0 * frequency.getD (o+w-a) 0).sum).sum

private def peak : ℕ :=
  (frequency.zipIdx.map fun (v, k) => Nat.fast_choose 516 k * v).sum ^ 2

private def irreducibles : List ℕ := [0, 2, 1, 2, 3, 6, 9, 18, 30]

/-- The degree counts used for the bound on distinct irreducible factors. -/
theorem smallPrimeCounts : (∀ i ∈ List.range 8,
    ((List.range (i+1)).map (fun k =>
      if (k+1) ∣ i+1 then (k+1)*irreducibles.getD (k+1) 0 else 0)).sum = 2^(i+1)) ∧
    321 ≤ ((List.range 7).map fun k => (k+2)*irreducibles.getD (k+2) 0).sum := by
  decide +kernel

private def factorCap (degree : ℕ) : ℕ :=
  ((List.range 7).foldl (fun (st : ℕ × ℕ) i =>
    let d := i+2
    let used := min (st.1/d) (irreducibles.getD d 0)
    (st.1-d*used, st.2+used)) (degree, 0)).2

private def denominator : ℕ := 163 * 2^321

private def localNum (f : ℕ) : ℕ :=
  min (4*2^321) (5*160^3 * 3^(factorCap f) * 163 * 2^(321-f))

private def characterCount (m w : ℕ) : ℕ :=
  let blocks := 516/(2*m)
  let all := Nat.fast_choose 516 w * 2^(2*m-516-20)
  if blocks = 0 then all else
    min all (blocks * ((List.range (w/blocks)).map (fun k => Nat.fast_choose (2*m) (k+1))).sum)

private def tailNums : List ℕ :=
  (List.range 157).map fun v =>
    ((SelbergWeight.krawtchoukRow 156 v 156).zipIdx.map
      fun (val, k) => val * ((k-85 : ℕ) : ℤ)).sum.natAbs

private def tailNumerator : ℕ :=
  let tails := tailNums
  let overlaps := (List.range 25).map overlap
  let locals := (List.range 322).map localNum
  4*2^321 * tails.head! * overlaps.head! +
    ((List.range 76).map fun i =>
      let lo := 21+4*i
      let hi := min (lo+3) 321
      let cap := ((locals.drop (lo-1)).take (hi-lo+2)).foldl max 0
      let z := 516/hi
      let coeff := ((List.range (25-z)).map fun r =>
        characterCount hi (r+z) * overlaps.getD (r+z) 0).sum
      cap * coeff * ((tails.drop (156/hi)).foldl max 0)).sum

set_option maxRecDepth 30000
set_option maxHeartbeats 40000000

/-- The entire parity and Selberg weighted tail is at most 0.005025. -/
theorem signedTailArithmetic :
    10^6 * tailNumerator ≤ 5025 * denominator * overlap 0 * 2^157 := by
  decide +kernel

private def signCost70 : ℕ :=
  ((List.range 20).map fun k => (1033+k)*2^(k/2)*(if k%2 = 0 then 70 else 99)).sum

/-- The outward bounds still leave more than the claimed number of distinct primitive polynomials. -/
theorem signedPrimitiveCountArithmetic :
    let group : ℕ := 2^1229-1
    let mass : ℚ := overlap 0 / (2^516 : ℚ)
    let gain : ℚ := 516*overlap 1 / (2*(overlap 0 : ℚ))
    let fieldCost : ℚ := 1032*(60+258+19*305) + (signCost70 : ℚ)/70
    let score := group*mass*(gain-60-305/20000) -
      (group.sqrt+1)*peak*fieldCost - 1229*2^1228*mass*(5025/1000000)
    group*mass*(91/100) < score ∧ (2^619 : ℚ)*1229*305*peak < score := by
  decide +kernel

private def freePrefix (parity : ℕ) : List (ℕ × ℕ) :=
  ((List.range 197).foldl (fun (rev : List (ℕ × ℕ)) k =>
    let last := rev.head!
    let count := if k % 2 = parity then Nat.fast_choose 196 k else 0
    (last.1 + count, last.2 + k * count) :: rev) [(0, 0)]).reverse

private def clipThreshold : ℕ := 21 * peak / 2^35

private def clippedExcess (parity : ℕ) : ℕ :=
  let even := freePrefix 0
  let odd := freePrefix 1
  let threshold := clipThreshold
  ((List.range 303).map fun i =>
    let row := SelbergWeight.krawtchoukRow 516 i 12
    let value := ((List.zipWith (fun (g : ℕ) (k : ℤ) => g*k) frequency row).sum).natAbs^2
    if value = 0 then 0 else
      let limit := min 197 (303-i-threshold/value)
      let totals := (if i%2 = parity then even else odd).getD limit (0, 0)
      Nat.fast_choose 516 i * (value*((303-i)*totals.1-totals.2)-threshold*totals.1)).sum

/-- Capping the score gives over nine times 2^654 polynomials for either parity. -/
theorem cappedMultiplicityArithmetic : 0 < clipThreshold ∧
    (∀ p ∈ List.range 2, 100*2^516*1229*(clippedExcess p + 9*2^654*clipThreshold) <
      91*(2^1229-1)*overlap 0) ∧ 2^658+2^196 < 2*(9*2^654) := by
  decide +kernel

end GF2Sparse.SignedWeight1229
