import GF2Sparse.PackedSquare
import GF2Sparse.ProgressionTriples
import GF2Sparse.Table

/-! Proper factors of every degree-1229 trinomial and every pentanomial with both adjacent endpoint taps. -/

namespace GF2Sparse.Degree1229

open Polynomial

-- Expand one divisor from each reciprocal pair. Only the checked mask
-- products below enter the mathematical proof.
open Lean Elab Term in
elab "reciprocalFactors1229% " family:str csv:term : term => do
  let endpoints ← match family.getString with
    | "trinomial" => pure false
    | "endpoints" => pure true
    | _ => throwError "unknown degree-1229 family"
  let first := if endpoints then 2 else 1
  let e ← elabTerm csv (some (mkConst ``String))
  let .lit (.strVal value) := e.consumeMData | throwError "expected a literal CSV"
  let "tap,factor_mask" :: lines := value.trimAscii.toString.splitOn "\n"
    | throwError "expected the tap and factor mask header"
  let mut small := #[]
  for line in lines do
    let [sa,sf] := line.splitOn "," | throwError "invalid factor row"
    let some a := sa.toNat? | throwError "invalid tap"
    let some g := sf.toNat? | throwError "invalid divisor"
    unless a == small.size + first && 1 < g && g.log2 < 1229 do
      throwError "invalid tap sequence or factor degree"
    small := small.push g
  unless small.size + first == 615 do throwError "incomplete factor table"
  let base := if endpoints then (1 <<< 1228) ||| 3 else 1
  let mut rows := #[]
  for a in [first:1230-first] do
    let source := small[min a (1229-a) - first]!
    let mut g := source
    if a > 614 then
      g := 0
      for j in [0:source.log2+1] do
        if source.testBit j then g := g ||| (1 <<< (source.log2-j))
    let mut rem := (1 <<< 1229) ||| (1 <<< a) ||| base
    let mut q := 0
    while rem > 0 && g.log2 ≤ rem.log2 do
      let j := rem.log2-g.log2
      q := q ^^^ (1 <<< j)
      rem := rem ^^^ (g <<< j)
    unless rem == 0 do throwError "factor fails at tap {a}"
    rows := rows.push (g,q)
  return toExpr rows.toList

private def checkFrom (mask : ℕ → ℕ) (stop a : ℕ) : List (ℕ × ℕ) → Bool
  | [] => a == stop
  | (g,q) :: rest => 1 < g && 1 < q &&
      maskProduct g q == mask a && checkFrom mask stop (a+1) rest

private def trinomialFactors : List (ℕ × ℕ) :=
  reciprocalFactors1229% "trinomial" (include_str "../data/degree-1229-trinomial-factors.csv")

private def endpointFactors : List (ℕ × ℕ) :=
  reciprocalFactors1229% "endpoints" (include_str "../data/degree-1229-endpoint-factors.csv")

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem trinomials_checked :
    checkFrom (fun a => xorShifts [1229,a,0] 1) 1229 1 trinomialFactors = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem endpoints_checked :
    checkFrom (fun a => fiveTermMask 1229 1228 a 1) 1228 2 endpointFactors = true := by decide +kernel

private theorem reducible_of_checked {mask : ℕ → ℕ} {stop a k : ℕ} {xs : List (ℕ × ℕ)}
    (hc : checkFrom mask stop a xs = true) (ha : a ≤ k) (hk : k < stop) :
    ¬Irreducible (decode (mask k)) := by
  induction xs generalizing a with
  | nil =>
    simp only [checkFrom, beq_iff_eq] at hc
    omega
  | cons row rows ih =>
    obtain ⟨g,q⟩ := row
    simp only [checkFrom, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨⟨⟨hg,hq⟩,he⟩,ht⟩ := hc
    by_cases heq : k = a
    · subst k
      rw [← he, decode_maskProduct]
      intro hi
      have nonunit (x : ℕ) (hx : 1 < x) : ¬IsUnit (decode x) := by
        apply not_isUnit_of_natDegree_pos
        rw [natDegree_decode]
        exact (Nat.le_log2 (by omega)).2 (by simpa using hx)
      exact (hi.isUnit_or_isUnit rfl).elim (nonunit g hg) (nonunit q hq)
    · exact ih ht (by omega)

/-- Every normalized degree-1229 trinomial has a factorization into two nonunits. -/
theorem trinomial_reducible {a : ℕ} (ha : 0 < a) (han : a < 1229) :
    ¬Irreducible (trinomial 1229 a) := by
  simpa only [PackedSquare.decode_trinomial_taps, trinomial] using
    reducible_of_checked trinomials_checked ha han

/-- Both adjacent endpoint coefficients cannot be one in an irreducible
degree-1229 pentanomial. -/
theorem endpoint_pentanomial_reducible {b : ℕ} (hb : 1 < b) (hbn : b < 1228) :
    ¬Irreducible ((X : BinaryPoly)^1229 + X^1228 + X^b + X + 1) := by
  simpa only [decode_fiveTermMask, pow_one] using
    reducible_of_checked endpoints_checked hb hbn

/-- Every irreducible degree-1229 polynomial excludes all same-degree trinomial
sources under power sampling. -/
theorem no_trinomial_sampling {f : BinaryPoly} (hf : Irreducible f)
    (hn : f.natDegree = 1229) {a : ℕ} (ha : 0 < a) (han : a < 1229) (m : ℕ) :
    ¬trinomial 1229 a ∣ expand (ZMod 2) m f := by
  intro h
  exact trinomial_reducible ha han
    (irreducible_of_dvd_expand_same_degree hf ((trinomial_degree ha han).trans hn.symm) h)

/-- Sampling a degree-1229 endpoint trinomial gives a reducible block for
every positive exponent whose inner block stays below degree 1229. -/
theorem sampled_block_reducible {u m : ℕ} (hu : 0 < u) (hm : 0 < m) (hs : m*u < 1229) :
    ¬Irreducible (sampledBlock 1229 0 u m) := by
  intro hf
  have hb : ((X : BinaryPoly)^u + 1).natDegree = u := by
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
    simpa using hu
  have hn : (sampledBlock 1229 0 u m).natDegree = 1229 := by
    simp only [sampledBlock, pow_zero, one_mul]
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
    simpa [natDegree_pow, hb] using hs
  apply no_trinomial_sampling hf hn (Nat.mul_pos hm hu) hs m
  simpa only [blockEndpoints, pow_zero, one_mul, trinomial] using
    endpoints_dvd_expand_block 1229 0 u m

/-- The corresponding block with constant term outside the binomial power. -/
theorem upper_block_reducible {t u m : ℕ} (ht : 0 < t) (hu : 0 < u) (hm : 0 < m)
    (hs : t + m*u = 1229) : ¬Irreducible (sampledBlock 0 t u m) := by
  intro hf
  have hmu := Nat.mul_pos hm hu
  have hb : ((X : BinaryPoly)^u + 1).natDegree = u := by
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
    simpa using hu
  have hzero : (X : BinaryPoly)^u + 1 ≠ 0 := by
    intro h
    simp [h] at hb
    omega
  have hd : ((X : BinaryPoly)^t * (X^u+1)^m).natDegree = 1229 := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hzero), natDegree_X_pow,
      natDegree_pow, hb, hs]
  have hn : (sampledBlock 0 t u m).natDegree = 1229 := by
    rw [sampledBlock, pow_zero, natDegree_add_eq_right_of_natDegree_lt, hd]
    simp [hd]
  apply no_trinomial_sampling hf hn ht (by omega) m
  have he : trinomial 1229 t = blockEndpoints 0 t u m := by
    rw [← hs]
    simp [trinomial, blockEndpoints, pow_add]
    ring
  rw [he]
  exact endpoints_dvd_expand_block 0 t u m

/-- Every degree-1229 pentanomial containing a four-term progression is reducible. -/
theorem progression_reducible {f : BinaryPoly} (h : IsProgressionPentanomial 1229 f) :
    ¬Irreducible f := by
  obtain ⟨a,t,u,hu,h0,ha,_,_,hd,hn,rfl⟩ := h
  rcases h0 with rfl | rfl
  · apply upper_block_reducible (by omega) hu (by decide)
    omega
  · have hlt : 3*u < a := by omega
    have he : a = 1229 := by omega
    subst a
    exact sampled_block_reducible hu (by decide) hlt

end GF2Sparse.Degree1229
