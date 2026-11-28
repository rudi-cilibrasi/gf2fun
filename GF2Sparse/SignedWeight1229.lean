import GF2Sparse.SelbergWeight

/-! Integer and rational checks for the signed coefficient-weight bound at degree 1229. -/

namespace GF2Sparse.SignedWeight1229

private def frequency : List ℕ :=
  [101808133126899,25258413561571,6081049088867,1416285931840,317871134706,
   68414645634,14029353531,2716735113,490355574,80796147,11703889,1371565,100000]

private def overlapWith (frequency : List ℕ) (w : ℕ) : ℕ :=
  ((List.range (w+1)).map fun a =>
    Nat.fast_choose w a * ((List.range (13-max a (w-a))).map fun o =>
      Nat.fast_choose (516-w) o * frequency.getD (o+a) 0 * frequency.getD (o+w-a) 0).sum).sum

private def overlap := overlapWith frequency

private def peakWith (frequency : List ℕ) : ℕ :=
  (frequency.zipIdx.map fun (v, k) => Nat.fast_choose 516 k * v).sum ^ 2

private def peak := peakWith frequency

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

private def characterCount (observed m w : ℕ) : ℕ :=
  let blocks := 516/(2*m)
  let all := Nat.fast_choose 516 w * 2^(2*m-516-observed)
  if blocks = 0 then all else
    min all (blocks * ((List.range (w/blocks)).map (fun k => Nat.fast_choose (2*m) (k+1))).sum)

private def tailNums (free threshold : ℕ) : List ℕ :=
  (List.range (free+1)).map fun v =>
    ((SelbergWeight.krawtchoukRow free v free).zipIdx.map
      fun (val, k) => val * ((k-threshold : ℕ) : ℤ)).sum.natAbs

private def tailNumerator : ℕ :=
  let tails := tailNums 156 85
  let overlaps := (List.range 25).map overlap
  let locals := (List.range 322).map localNum
  4*2^321 * tails.head! * overlaps.head! +
    ((List.range 76).map fun i =>
      let lo := 21+4*i
      let hi := min (lo+3) 321
      let cap := ((locals.drop (lo-1)).take (hi-lo+2)).foldl max 0
      let z := 516/hi
      let coeff := ((List.range (25-z)).map fun r =>
        characterCount 20 hi (r+z) * overlaps.getD (r+z) 0).sum
      cap * coeff * ((tails.drop (156/hi)).foldl max 0)).sum

set_option maxRecDepth 30000
set_option maxHeartbeats 40000000

/-- The entire parity and Selberg weighted tail is at most 0.005025. -/
theorem signedTailArithmetic :
    10^6 * tailNumerator ≤ 5025 * denominator * overlap 0 * 2^157 := by
  decide +kernel

private def signCost70 (observed : ℕ) : ℕ :=
  ((List.range observed).map fun k => (1033+k)*2^(k/2)*(if k%2 = 0 then 70 else 99)).sum

/-- The outward bounds still leave more than the claimed number of distinct primitive polynomials. -/
theorem signedPrimitiveCountArithmetic :
    let group : ℕ := 2^1229-1
    let mass : ℚ := overlap 0 / (2^516 : ℚ)
    let gain : ℚ := 516*overlap 1 / (2*(overlap 0 : ℚ))
    let fieldCost : ℚ := 1032*(60+258+19*305) + (signCost70 20 : ℚ)/70
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

private def clippedExcess (frequency : List ℕ) (base threshold parity : ℕ) : ℕ :=
  let even := freePrefix 0
  let odd := freePrefix 1
  ((List.range base).map fun i =>
    let row := SelbergWeight.krawtchoukRow 516 i 12
    let value := ((List.zipWith (fun (g : ℕ) (k : ℤ) => g*k) frequency row).sum).natAbs^2
    if value = 0 then 0 else
      let limit := min 197 (base-i-threshold/value)
      let totals := (if i%2 = parity then even else odd).getD limit (0, 0)
      Nat.fast_choose 516 i * (value*((base-i)*totals.1-totals.2)-threshold*totals.1)).sum

/-- Capping the score gives over nine times 2^654 polynomials for either parity. -/
theorem cappedMultiplicityArithmetic : 0 < clipThreshold ∧
    (∀ p ∈ List.range 2, 100*2^516*1229*(clippedExcess frequency 303 clipThreshold p + 9*2^654*clipThreshold) <
      91*(2^1229-1)*overlap 0) ∧ 2^658+2^196 < 2*(9*2^654) := by
  decide +kernel

private def lighter : List ℕ :=
  [80937526401525, 20205228627900, 4896663404176, 1148538982619, 259762329274,
   56380679122, 11670879365, 2284495018, 417645065, 69930827, 10357995, 1259244, 100000]

/-- The constants for the local Euler estimate through conductor degree 461. -/
theorem gradedEulerArithmetic :
    ((List.range 7).map (fun (k : ℕ) => (1 : ℚ)/(k+2 : ℕ))).sum + 461/(9*512) < 2 ∧
    (11 : ℕ)^5 < 192*4^5 ∧
    461 ≤ ((List.range 7).map fun k => (k+2)*irreducibles.getD (k+2) 0).sum := by
  decide +kernel

private def jointLocalNum (f : ℕ) : ℕ :=
  let k := factorCap f
  min (4*2^922) (min (5*230^3 * 3^k * 233 * 2^(922-f)) (192*233*2^(922+k+460-2*f)))

private def jointTailNumerator : ℕ :=
  let tails := tailNums 160 86
  let weighted := tails.zipIdx.map fun (t, v) => t * Nat.fast_choose 160 v
  let overlaps := (List.range 25).map (overlapWith lighter)
  let locals := (List.range 462).map jointLocalNum
  4*2^922 * tails.head! * overlaps.head! +
    ((List.range 111).map fun i =>
      let lo := 19+4*i
      let hi := min (lo+3) 461
      let cap := ((locals.drop (lo-1)).take (hi-lo+2)).foldl max 0
      let largest := (tails.drop (160/hi)).foldl max 0
      let total := (weighted.drop (160/hi)).sum
      let first := 516/hi
      cap * ((List.range (25-first)).map fun j =>
        let w := first+j
        let words := Nat.fast_choose 516 w * 2^(2*hi-712)
        overlaps.getD w 0 * min (characterCount 18 hi w * largest) (words * total)).sum).sum

/-- Both short codes together bound the level-230 Selberg tail. -/
theorem jointTailArithmetic : 10^6 * jointTailNumerator ≤
    5089 * (233*2^922) * overlapWith lighter 0 * 2^161 := by
  decide +kernel

/-- The signed score at cutoff 303 exceeds 0.26 times the group size and mean. -/
theorem jointScoreArithmetic :
    let n : ℕ := 2^1229-1
    let mass : ℚ := overlapWith lighter 0 / (2^516 : ℚ)
    let gain : ℚ := 516*overlapWith lighter 1 / (2*(overlapWith lighter 0 : ℚ))
    let cost : ℚ := 1032*(61+258+18*215) + (signCost70 18 : ℚ)/70
    n*mass*(26/100) < n*mass*(gain-61-215/20000) - (n.sqrt+1)*peakWith lighter*cost -
      1229*2^1228*mass*(5089/1000000) := by
  decide +kernel

/-- The positive score supplies more than 2^655 distinct 301-term polynomials across both ends. -/
theorem jointCappedArithmetic :
    let cap := 5 * peakWith lighter / 2^32
    0 < cap ∧ (∀ p ∈ List.range 2, 100*2^516*1229*(clippedExcess lighter 301 cap p +
      17*2^650*cap) < 26*(2^1229-1)*overlapWith lighter 0) ∧
      2^655+2^196 < 2*(17*2^650) := by
  decide +kernel

end GF2Sparse.SignedWeight1229
