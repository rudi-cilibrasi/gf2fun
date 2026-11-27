import GF2Sparse.MersenneDivisors

/-! Integer estimates and the prime sieve for generation by two constant fields. -/

namespace GF2Sparse.FactorFieldIndex

/-- Cleared form of the decreasing tail bound for the three character-weight blocks. -/
theorem tail_bound {y : ℕ} (hy : 2048 ≤ y) :
    (7076*y^2 + 17487*y + 16672)^2 < 64*83*9452*y^4 := by
  have h₁ : 17487*y + 16672 ≤ 18432*y := by omega
  have h₂ : 18432*y ≤ 9*y^2 := by nlinarith [Nat.mul_le_mul_right y hy]
  have h₃ : 7076*y^2 + 17487*y + 16672 ≤ 7085*y^2 := by omega
  calc
    _ ≤ (7085*y^2)^2 := Nat.pow_le_pow_left h₃ 2
    _ = 7085^2*y^4 := by ring
    _ < _ := Nat.mul_lt_mul_of_pos_right (by decide) (by positivity)

/-- In prime extension degree every possible small factor has one of twenty multipliers. -/
theorem prime_multiplier {n q p : ℕ} (hn : n.Prime) (ho : Odd n) (hp : p.Prime)
    (hd : p ∣ 2^n - 1) (hcap : p ≤ 83*q) (hq : 2*q < n) :
    ∃ k, 1 ≤ k ∧ k ≤ 20 ∧ p = 2*n*k+1 ∧ (p % 8 = 1 ∨ p % 8 = 7) := by
  obtain ⟨k, hk⟩ := prime_mersenne_factor_progression hn ho hp hd
  have hpos := hp.two_le
  have heq : p = 2*n*k+1 := by omega
  refine ⟨k, ?_, ?_, heq, odd_mersenne_prime_mod_eight ho hp hd⟩
  · by_contra! h
    have : k = 0 := by omega
    simp [this] at heq
    omega
  · by_contra! h
    have hl := Nat.mul_le_mul_left (2*n) (show 21 ≤ k by omega)
    nlinarith

def allowed (a k : ℕ) : Bool :=
  let p := 2*a*k+1
  (p % 8 == 1 || p % 8 == 7) && p % 3 != 0 && p % 5 != 0

def multipliers (a : ℕ) : List ℕ :=
  ((List.range 20).map (· + 1)).filter (allowed a)

/-- The sieve on the unit residue classes modulo 60 leaves at most six multipliers. -/
theorem residue_sieve : (List.range 60).all (fun a =>
    decide (a.Coprime 60 → (multipliers a).length ≤ 6)) = true := by decide +kernel

/-- The degree-1229 linear cutoff leaves just 36871. Testing divisibility also
removes composite progression entries, using the fact that the list has one survivor. -/
theorem degree1229_sieve :
    (((multipliers 1229).map (fun k => 2458*k+1)).filter (fun p =>
      decide (p ≤ 42496 ∧ p ∣ 2^1229-1))) = [36871] := by decide +kernel

/-- A block stores integer numerators. Position i has the extra denominator
sqrt(2) if i is odd. The square roots cancel in every entry below. -/
private def blockNorm (s : List ℕ) : ℚ :=
  (s.zipIdx.map fun (u,i) => (u:ℚ)^2 / 2^(i%2)).sum

private def pairs (s t : List ℕ) (coeff : ℕ → ℕ → ℚ) : ℚ :=
  (s.zipIdx.map fun (u,i) => (t.zipIdx.map fun (v,j) =>
    (u:ℚ)*v * (2:ℚ)^(((j:ℤ)-i-(i%2:ℕ)-(j%2:ℕ))/2) * coeff i j).sum).sum

private def intervalOK (w small : ℕ) (bad good : ℚ) (s t : List ℕ) : Prop :=
  let cross := pairs s t (fun i j => if j ≤ i ∧ i < j+w then good else bad)
  let inside := fun i j => if j ≤ i then (0:ℚ) else if j-i ≤ small then 1 else bad
  4*(blockNorm s + blockNorm t) < 4*cross ∧ 0 ≤ pairs s s inside + pairs t t inside

instance (w small : ℕ) (bad good : ℚ) (s t : List ℕ) :
    Decidable (intervalOK w small bad good s t) := by unfold intervalOK; infer_instance

theorem three_fields : intervalOK 3 3 (-1/40) 1
    [0,7,13,28,22,27,12,7] [5,17,19,31,20,19,5] := by decide +kernel

theorem four_fields : intervalOK 4 4 (-1/7) 1
    [0,0,2,4,3,3,1] [1,3,3,4,2] := by decide +kernel

theorem five_fields : intervalOK 5 5 (-1/4) 1
    [0,0,1,3,2,2,1] [1,2,2,3,1] := by decide +kernel

theorem seven_fields : intervalOK 7 5 (-1/2) (197/200)
    [0,0,0,0,3,6,3,3,1,1] [1,2,2,4,4,4] := by decide +kernel

/-- The two blocks for seven intervals overlap at 2d = 8. -/
theorem seven_fields_first :
    let s := [0,0,0,0,3,6,3,3,2,3,2,4,4,4]
    32 * blockNorm s < 2 * pairs s s (fun i j =>
      if j ≤ i then 0 else if j-i ≤ 5 then 1 else if j-i ≤ 8 then 197/200 else -1/2) :=
  by decide +kernel

private def sixLeft : List ℤ := [58,120,59,56,24,17,1,-5,-1,2]
private def sixRight : List ℤ := [1,-2,-4,1,12,34,39,83,85,82]

private def signedNorm (xs : List ℤ) : ℚ :=
  (xs.zipIdx.map fun (u,i) => (u:ℚ)^2 / 2^(i%2)).sum

/-- The correlation at h multiplied by 2^(h/2), using integer entries
with the same odd-position normalization as in the nonnegative test. -/
private def signedLag (xs ys : List ℤ) (h : ℤ) : ℚ :=
  (xs.zipIdx.map fun (u,i) =>
    let j := (i:ℤ)+h
    if j < 0 then (0:ℚ) else
      (u:ℚ) * (ys[j.toNat]?.getD 0 : ℤ) *
        (2:ℚ)^((h-(i%2:ℕ)-(j.toNat%2:ℕ))/2)).sum

private def signedLower (v lower : ℚ) : ℚ := min v (v*lower)

private def sixSlope : ℚ :=
  ((List.range 19).map fun j =>
    let h := (j:ℤ)-9
    signedLower (signedLag sixLeft sixRight h) (if 3 ≤ h ∧ h ≤ 8 then 3997/4000 else -1/2)
    ).sum / (4*(signedNorm sixLeft + signedNorm sixRight))

private def sixInside : ℚ :=
  2*((List.range 9).map fun j =>
    signedLower (signedLag sixLeft sixLeft (j+1:ℕ) + signedLag sixRight sixRight (j+1:ℕ))
      (-1/2)).sum / (signedNorm sixLeft + signedNorm sixRight)

/-- Signed autocorrelations give a positive margin for all d ≥ 13. -/
theorem six_fields_tail :
    sixSlope = 2089970613/522304000 ∧ sixInside = -37473/8161 ∧
    4 < sixSlope ∧ 1 < (sixSlope-4)*4096+sixInside := by decide +kernel

private def sixFiniteWeights (d : ℕ) : List ℤ :=
  match d with
  | 9 => [29,60,29,28,12,8,0,-2,0,3,2,0,-2,1,6,17,20,42,42,41]
  | 10 => [31,63,31,29,13,9,0,-3,-1,1,1,1,0,-1,-2,1,6,18,21,44,45,43]
  | 11 => [28,58,28,27,12,8,1,-3,-1,1,1,0,0,1,0,-1,-2,1,6,16,19,40,41,40]
  | _ => (List.range (2*d+2)).map fun i =>
    sixLeft[i]?.getD 0 + (if i+8 < 2*d then 0 else sixRight[i+8-2*d]?.getD 0)

private def sixCovered (m k p : ℕ) : ℕ :=
  let automatic := if p = 3 ∧ 3 ∣ k then 2^(k/3) else 0
  ((List.range 6).map fun j =>
    if k ∣ m-j then 2^k-2^(m-j)/2000 else 0).foldl max automatic

private def sixFiniteOK (d p : ℕ) : Bool := Id.run do
  let xs := sixFiniteWeights d
  let score := ((List.range (xs.length-1)).map fun i =>
    let k : ℕ := i+1
    let v := signedLag xs xs k
    let size : ℚ := 2^k
    let lower : ℚ := ((p:ℚ)*(sixCovered (2*d) k p)-size)/(((p:ℚ)-1)*size)
    v/size + signedLower v lower).sum
  return decide (2^(d+1)*signedNorm xs < 2*score)

/-- All nine remaining dyadic ranges, for a cubic quotient or any larger prime quotient. -/
theorem six_fields_small :
    ((List.range 9).all fun j => sixFiniteOK (j+4) 3 && sixFiniteOK (j+4) 5) = true := by
  decide +kernel

end GF2Sparse.FactorFieldIndex
