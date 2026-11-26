import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Sqrt

/-! Integer checks for the Fourier weight count at degree 1229. Mathlib proves
`Nat.fast_choose` equal to `Nat.choose` by `Nat.choose_eq_fast_choose`. -/

namespace GF2Sparse.FourierWeightBounds

private def ceilDiv (value divisor : ℕ) := (value + divisor - 1) / divisor

/-- Coefficient of degree j in (1 - z)^i (1 + z)^(d - i). -/
private def krawtchouk (d i j : ℕ) : ℤ :=
  ((List.range (j + 1)).map fun h =>
    let term : ℤ := (Nat.fast_choose i h * Nat.fast_choose (d - i) (j - h) : ℕ)
    if h % 2 = 0 then term else -term).sum

private def freeTails (free parity : ℕ) : List ℕ :=
  (List.range (free + 1)).reverse.foldl (fun tail k =>
    (tail.headD 0 + if k % 2 = parity then Nat.fast_choose free k else 0) :: tail) [0]

/-- Integer lower bound from the degree-1229 corollary, with the two
small-factor error terms rounded upward. -/
def polynomialCount (d radius base cutoff primeCount : ℕ) : ℕ :=
  let n := 1229
  let free := n - 1 - 2 * d
  let frequencies := (List.range (radius + 1)).map fun j =>
    (j, (base ^ (2 * (radius - j)) * radius.descFactorial j).sqrt)
  let maximum := ((frequencies.map fun (j, g) => Nat.fast_choose d j * g).sum) ^ 2
  let mass := 2 ^ d * (frequencies.map fun (j, g) => Nat.fast_choose d j * g ^ 2).sum
  let evenTail := freeTails free 0
  let oddTail := freeTails free 1
  let overweight := ((List.range (d + 1)).map fun i =>
    let amplitude := (frequencies.map fun (j, g) => (g : ℤ) * krawtchouk d i j).sum
    let tail := if i % 2 = 0 then oddTail else evenTail
    Nat.fast_choose d i * amplitude.natAbs ^ 2 * tail.getD (cutoff - 1 - i) 0).sum
  let errorBits := (Nat.fast_choose free (free / 21)).log2 / 2
  let bad := ceilDiv ((3 * 7^2 * 15^3) * overweight) (2^20) +
    ceilDiv (mass * 2 ^ (free + 6)) (2 ^ errorBits)
  let order := 2 ^ n - 1
  let denominator := (2 * n + 1) * 2 ^ (2 * d)
  let mainTerm := (2 * n + 1 - primeCount) * order * mass
  let cost := (primeCount + 1) * (2 * d) * (order.sqrt + 1) * maximum + n * bad
  (mainTerm - denominator * cost) / (denominator * n * maximum)

theorem orderPrimeCount1229 :
    2 ^ 1229 - 1 < ((List.range 77).map fun i => 2 * 1229 * (i + 1) + 1).prod := by
  decide +kernel

set_option maxRecDepth 20000
set_option maxHeartbeats 12000000

theorem primitiveCountArithmetic315 : 2 ^ 621 < polynomialCount 502 16 14 315 76 := by
  decide +kernel

theorem primitiveCountArithmetic313 : 2 ^ 616 < polynomialCount 509 15 14 313 19 := by
  decide +kernel

end GF2Sparse.FourierWeightBounds
