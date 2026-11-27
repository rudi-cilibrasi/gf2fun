import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Rat.Defs

/-! Exact arithmetic for the squarefree-divisor sieve at degree 1229. -/

namespace GF2Sparse.SelbergWeight

private def primeCounts : List ℕ :=
  [0, 2, 1, 2, 3, 6, 9, 18, 30, 56, 99, 186, 335, 630, 1161, 2182, 4080, 7710, 14532, 27594, 52377]

/-- The counts satisfy the binary irreducible-polynomial divisor identity. -/
theorem primeCountsDivisorIdentity : ∀ n ∈ List.range 20,
    ((List.range (n+1)).map fun i =>
      if (i+1) ∣ (n+1) then (i+1)*primeCounts.getD (i+1) 0 else 0).sum = 2^(n+1) := by
  decide +kernel

private def divisorSum (z : ℕ) (absolute : Bool) : ℚ :=
  let initial : List ℚ := 1 :: List.replicate z 0
  let coeff := (List.range (z-1)).foldl (fun old i =>
    let d := i+2
    let p : ℕ := 2^d
    let weight : ℚ := (if absolute then (1+p : ℕ) else 1) / ((p-1 : ℕ) : ℚ)
    let choices := (List.range (z/d+1)).map fun k =>
      (Nat.fast_choose (primeCounts.getD d 0) k : ℚ) * weight^k
    (List.range (z+1)).map fun j =>
      ((List.range (j/d+1)).map fun k => choices.getD k 0 * old.getD (j-k*d) 0).sum) initial
  coeff.sum

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

/-- Outward rational bounds for the constant and absolute Fourier coefficients. -/
theorem sieveConstants :
    0 < divisorSum 20 false ∧ (1 : ℚ)/divisorSum 20 false ≤ 171067/1000000 ∧
    (divisorSum 20 true / divisorSum 20 false)^2 ≤ 10090475241 := by
  decide +kernel

/-- Level 19 allows the two weighted intervals to be separated by the free interval. -/
theorem twoEndedSieveConstants :
    0 < divisorSum 19 false ∧ (1 : ℚ)/divisorSum 19 false ≤ 178710/1000000 ∧
    (divisorSum 19 true / divisorSum 19 false)^2 ≤ 2753023822 := by
  decide +kernel

/-- Every division of the 508 positions supplies the same character-weight lower bounds. -/
theorem twoEndedCharacterWeights : ∀ a ∈ List.range 509,
    12 ≤ a/39 + (508-a)/39 ∧ 5 ≤ 212/39 := by
  decide +kernel

private def frequencies : List ℕ :=
  [87562546122, 22856382314, 5849044663, 1460837027, 354444590, 83157868, 18776391,
   4059835, 835957, 162853, 29770, 5050, 783, 108, 13, 1]

/-- The coefficient recurrence of (1-z)^u (1+z)^(n-u). -/
private def krawtchoukRow (n u last : ℕ) : List ℤ :=
  ((List.range last).foldl (fun (rev : List ℤ) j =>
    let next := (((n : ℤ) - 2*u)*rev.head! - ((n+1-j : ℕ) : ℤ)*rev.getD 1 0) / (j+1 : ℕ)
    next :: rev) [1]).reverse

private def sameParityTails (row : List ℤ) : List ℤ :=
  row.foldr (fun v tail => (v+tail.getD 1 0) :: tail) [0, 0]

private def characterMaxima (n lower : ℕ) (tails : Bool) : List ℕ :=
  let initial := List.replicate (n+1+(if tails then 2 else 0)) 0
  (List.range (n/2+1-lower)).foldl (fun acc offset =>
    let row := krawtchoukRow n (lower+offset) n
    let values := if tails then sameParityTails row else row
    List.zipWith max acc (values.map Int.natAbs)) initial

private def positiveTails (n parity : ℕ) : List ℕ :=
  (List.range (n+1)).reverse.foldl (fun tails k =>
    (tails.head! + if k%2 = parity then Nat.fast_choose n k else 0) :: tails) [0]

private def weightedCount (d cutoff middleMin freeMin millionths absolute
    mainNum mainDen errorCount : ℕ) (weights : List ℕ) : ℕ :=
  let n := 1229
  let free := n-1-2*d
  let terms := weights.zipIdx
  let maximum := (terms.map fun (g,j) => Nat.fast_choose d j * g).sum ^ 2
  let mass := 2^d * (terms.map fun (g,j) => Nat.fast_choose d j * g^2).sum
  let middle := characterMaxima d middleMin false
  let tail := characterMaxima free freeMin true
  let even := positiveTails free 0
  let odd := positiveTails free 1
  let sums := (List.range (d+1)).foldl (fun (tot : ℕ × ℕ) i =>
    let row := krawtchoukRow d i (weights.length-1)
    let squared := ((List.zipWith (fun (g : ℕ) (k : ℤ) => g*k) weights row).sum).natAbs^2
    let first := min (free+1) (cutoff-1-i)
    let k := first + (1+i+first)%2
    let tails := if i%2 = 0 then odd else even
    (tot.1 + squared*Nat.fast_choose d i*tails.getD first 0,
     tot.2 + squared*middle.getD i 0*tail.getD k 0)) (0,0)
  let bad := (millionths*sums.1 + 999999)/1000000 + absolute*sums.2
  let order := 2^n-1
  let denominator := mainDen*2^(2*d)
  let mainTerm := mainNum*order*mass
  let cost := errorCount*(2*d)*(order.sqrt+1)*maximum + n*bad
  (mainTerm-denominator*cost)/(denominator*n*maximum)

private def frequencyBound309 (millionths absolute : ℕ) : ℕ :=
  weightedCount 508 309 12 5 millionths absolute 2440 2459 20 frequencies

/-- The level-20 bound when all prescribed coefficients are at one end. -/
def count309 : ℕ := frequencyBound309 171067 10090475241

theorem primitiveCountArithmetic309 : 2^616 < count309 := by
  decide +kernel

/-- The level-19 bound for every allocation of the prescribed coefficients to the two ends. -/
theorem twoEndedCountArithmetic309 : 2^616 < frequencyBound309 178710 2753023822 := by
  decide +kernel

/-- Character weights for a window of 680 possible interior terms at sieve level 20. -/
theorem window680CharacterWeights : ∀ a ∈ List.range 549,
    12 ≤ a/41 + (548-a)/41 ∧ 3 ≤ 132/41 := by
  decide +kernel

private def window680FailureBound : ℕ :=
  let indexFloor := 818085338814611458
  let order : ℕ := 2^1229-1
  let period := indexFloor*2^548
  let denominator := 1229*period
  (15*(order+548*(order.sqrt+1)*period)+denominator-1)/denominator

/-- Cutoffs, frequency weights, population exponents and upper failure fractions. -/
private def window680Cases : List (ℕ × List ℕ × ℕ × ℕ × ℕ) := [
  (313, [338258387341,50052925585,6895969111,874342382,100279148,10121411,854553,52701,100],
    619, 29, 100),
  (315, [1312773419,185773167,24377617,2927119,315242,29457,2229,100], 622, 37, 1000),
  (319, [185918844,23803765,2788558,293226,26826,2009,100], 627, 1, 1000),
  (325, [39562098,4303710,417529,34924,2356,100], 634, 1, 100000),
  (345, [94296071,4797761,160903,100], 653, 14, 10^12),
  (375, [1], 670, 13, 10^17)]

/-- Counts and conditional failure bounds using the four known prime tests. -/
theorem window680DensityArithmetic : window680Cases.all (fun (w, g, e, num, den) =>
    let lower := weightedCount 548 w 12 3 171067 10090475241 19999 20000 5 g
    decide (2^e < lower ∧ den*window680FailureBound < num*lower)) = true := by
  decide +kernel

end GF2Sparse.SelbergWeight
