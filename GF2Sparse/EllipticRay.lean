import GF2Sparse.FactorBaseExamples

/-! Orbit propagation, integer point bounds, and degree-53 logarithm certificates
for the elliptic ray class construction in the research note. -/

namespace GF2Sparse.EllipticRay

/-- A translation with a known multiplier propagates membership along the orbit. -/
theorem orbit_mem {G : Type*} [Group G] (H : Subgroup G) {v : ℕ → G} {u : G} {q : ℕ}
    (step : ∀ i, v (i+1) = u * (v i)^q) (hu : u ∈ H) (hv : v 0 ∈ H) :
    ∀ i, v i ∈ H := by
  intro i
  induction i with
  | zero => exact hv
  | succ i ih => rw [step]; exact H.mul_mem hu (H.pow_mem ih q)

private def scaledCross (d shift k : ℕ) (weights : List ℕ) : ℕ :=
  ((List.range (weights.length-k)).map fun i =>
    weights[i]! * weights[i+k]! * 2^(shift-(d*k+i%2+(i+k)%2)/2)).sum

/-- The strict Fejér inequality after clearing the index and powers of two.
The odd-index weights are divided by the real square root of two. -/
def pointBound (n d orbits indexFloor : ℕ) (weights : List ℕ) : Bool :=
  let cross := scaledCross d (d*weights.length+2)
  let shifts := (List.range (weights.length-1)).map (·+1)
  let split := 2 * n * orbits * indexFloor * (shifts.map (fun k => cross k weights)).sum
  let total := 2 * (shifts.map (fun k => cross k weights * (2^(d*k)+1))).sum
  d % 2 == 1 && decide (n * indexFloor * cross 0 weights + total < split)

theorem point_bound_1229 :
    pointBound 1229 19 387 818085338814611458 [3,9,9,14,10,12,6,4] = true := by
  decide +kernel

theorem point_bounds_53 :
    pointBound 53 11 30 6361 [10,28,20,15] = true ∧
    pointBound 53 11 38 107 [12,28,12] = true := by
  decide +kernel

theorem index_tests_53 :
    ((List.range 59).map (fun k => 106*(k+1)+1)).all
      (fun v => Nat.gcd v (2^53-1) == 1) = true := by
  decide +kernel

open FactorBase

def logs53 : List (ℕ × ℕ) := logRows% (include_str "../data/degree-53-elliptic-logs.csv")

set_option maxRecDepth 4096 in
theorem checked_logs_53 :
    logs53.length = 38 ∧ (logs53.map Prod.fst).Nodup ∧
    checkLogs 53 3 [53,23,21,2,0] logs53 = true := by decide +kernel

end GF2Sparse.EllipticRay
