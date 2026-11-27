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

private def divisorSum (absolute : Bool) : ℚ :=
  let initial : List ℚ := 1 :: List.replicate 20 0
  let coeff := (List.range 19).foldl (fun old i =>
    let d := i+2
    let p : ℕ := 2^d
    let weight : ℚ := (if absolute then (1+p : ℕ) else 1) / ((p-1 : ℕ) : ℚ)
    let choices := (List.range (20/d+1)).map fun k =>
      (Nat.fast_choose (primeCounts.getD d 0) k : ℚ) * weight^k
    (List.range 21).map fun j =>
      ((List.range (j/d+1)).map fun k => choices.getD k 0 * old.getD (j-k*d) 0).sum) initial
  coeff.sum

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000

/-- Outward rational bounds for the constant and absolute Fourier coefficients. -/
theorem sieveConstants :
    0 < divisorSum false ∧ (1 : ℚ)/divisorSum false ≤ 171067/1000000 ∧
    (divisorSum true / divisorSum false)^2 ≤ 10090475241 := by
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

private def characterMaxima (n : ℕ) (tails : Bool) : List ℕ :=
  let initial := List.replicate (n+1+(if tails then 2 else 0)) 0
  (List.range (n/2+1-n/41)).foldl (fun acc offset =>
    let row := krawtchoukRow n (n/41+offset) n
    let values := if tails then sameParityTails row else row
    List.zipWith max acc (values.map Int.natAbs)) initial

private def positiveTails (n parity : ℕ) : List ℕ :=
  (List.range (n+1)).reverse.foldl (fun tails k =>
    (tails.head! + if k%2 = parity then Nat.fast_choose n k else 0) :: tails) [0]

/-- The integer lower bound on the number of primitive polynomials with at most 309 terms. -/
def count309 : ℕ :=
  let n := 1229
  let d := 508
  let free := n-1-2*d
  let terms := frequencies.zipIdx
  let maximum := (terms.map fun (g,j) => Nat.fast_choose d j * g).sum ^ 2
  let mass := 2^d * (terms.map fun (g,j) => Nat.fast_choose d j * g^2).sum
  let middle := characterMaxima d false
  let tail := characterMaxima free true
  let even := positiveTails free 0
  let odd := positiveTails free 1
  let sums := (List.range (d+1)).foldl (fun (tot : ℕ × ℕ) i =>
    let row := krawtchoukRow d i (frequencies.length-1)
    let squared := ((List.zipWith (fun (g : ℕ) (k : ℤ) => g*k) frequencies row).sum).natAbs^2
    let first := min (free+1) (309-1-i)
    let k := first + (1+i+first)%2
    let tails := if i%2 = 0 then odd else even
    (tot.1 + squared*Nat.fast_choose d i*tails.getD first 0,
     tot.2 + squared*middle.getD i 0*tail.getD k 0)) (0,0)
  let bad := (171067*sums.1 + 999999)/1000000 + 10090475241*sums.2
  let order := 2^n-1
  let denominator := (2*n+1)*2^(2*d)
  let mainTerm := (2*n+1-19)*order*mass
  let cost := 20*(2*d)*(order.sqrt+1)*maximum + n*bad
  (mainTerm-denominator*cost)/(denominator*n*maximum)

theorem primitiveCountArithmetic309 : 2^616 < count309 := by
  decide +kernel

end GF2Sparse.SelbergWeight
