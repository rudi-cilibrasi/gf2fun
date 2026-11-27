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

/-- The strict two-moment inequality for weights (1,t,1), after clearing
denominators. Here D is the degree times the lower bound on a possible index prime. -/
theorem two_moment_sufficient {D Q k s t : ℝ} (hD : 0 < D) (hk : 0 ≤ k)
    (hs : 0 < s) (ht : 0 < t) (hsq : s^2 = Q)
    (hopt : D * Q * t^2 = 2 * D * Q + 2 * (Q^2 + 1))
    (hgap : D * s * t < 2 * (D * k - Q - 1)) :
    D * Q * (2 + t^2) < 4*t*s*(D*k-Q-1) + 2*(D*k-Q^2-1) := by
  have h := mul_lt_mul_of_pos_left hgap (by positivity : 0 < 2 * t * s)
  rw [show 2*t*s*(D*s*t) = 2*D*s^2*t^2 by ring, hsq] at h
  nlinarith only [h, hopt, mul_nonneg hD.le hk]

def quadraticBound (n Q k J : ℕ) : Bool :=
  let D := n * J
  decide (Q + 1 < k*D ∧ D*(Q*D + Q^2 + 1) < 2*(k*D - (Q+1))^2)

/-- No possible index prime is smaller than 36871. The integer two-moment
test covers all larger indices in the model over the field of size 2^20. -/
theorem unconditional_points_1229 :
    ((List.range 14).map (fun k => 2458*(k+1)+1)).all
      (fun v => Nat.gcd v (2^1229-1) == 1) = true ∧
    quadraticBound 1229 (2^20) 733 36871 = true ∧
    733 ≤ 1049566/1229 ∧ Nat.gcd (1049566*(2^20-1)) (2^1229-1) = 1 := by
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
