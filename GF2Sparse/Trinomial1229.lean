import GF2Sparse.PackedSquare
import GF2Sparse.ProgressionTriples

/-! Proper factors of all 1228 trinomials in degree 1229. -/

namespace GF2Sparse.Degree1229

open Polynomial

-- Expand the 614 divisors and their reciprocals into literal factors. The
-- theorem below checks their products independently of this preprocessing.
open Lean Elab Term in
elab "trinomialFactors1229% " csv:term : term => do
  let e ← elabTerm csv (some (mkConst ``String))
  let .lit (.strVal value) := e.consumeMData | throwError "expected a literal CSV"
  let "tap,factor_mask" :: lines := value.trimAscii.toString.splitOn "\n"
    | throwError "expected the tap and factor mask header"
  let mut small := #[]
  for line in lines do
    let [sa,sf] := line.splitOn "," | throwError "invalid factor row"
    let some a := sa.toNat? | throwError "invalid tap"
    let some g := sf.toNat? | throwError "invalid divisor"
    unless a == small.size + 1 && 1 < g && g.log2 < 1229 do
      throwError "invalid tap sequence or factor degree"
    small := small.push g
  unless small.size == 614 do throwError "expected 614 proper divisors"
  let mut rows := #[]
  for i in [0:1228] do
    let a := i+1
    let source := small[min a (1229-a) - 1]!
    let mut g := source
    if a > 614 then
      g := 0
      for j in [0:source.log2+1] do
        if source.testBit j then g := g ||| (1 <<< (source.log2-j))
    let mut rem := (1 <<< 1229) ||| (1 <<< a) ||| 1
    let mut q := 0
    while rem > 0 && g.log2 ≤ rem.log2 do
      let j := rem.log2-g.log2
      q := q ^^^ (1 <<< j)
      rem := rem ^^^ (g <<< j)
    unless rem == 0 do throwError "factor fails at tap {a}"
    rows := rows.push (g,q)
  return toExpr rows.toList

private def factors : List (ℕ × ℕ) :=
  trinomialFactors1229% (include_str "../data/degree-1229-trinomial-factors.csv")

private def checkFrom (a : ℕ) : List (ℕ × ℕ) → Bool
  | [] => a == 1229
  | (g,q) :: rest => 1 < g && 1 < q &&
      maskProduct g q == xorShifts [1229,a,0] 1 && checkFrom (a+1) rest

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem checked : checkFrom 1 factors = true := by decide +kernel

private theorem reducible_of_product {n k g q : ℕ} (hg : 1 < g) (hq : 1 < q)
    (he : maskProduct g q = xorShifts [n,k,0] 1) : ¬Irreducible (trinomial n k) := by
  intro hi
  have hp : trinomial n k = decode g * decode q := by
    rw [← decode_maskProduct, he, PackedSquare.decode_trinomial_taps, trinomial]
  have deg (x : ℕ) (hx : 1 < x) : 0 < (decode x).natDegree := by
    rw [natDegree_decode]
    exact (Nat.le_log2 (by omega)).2 (by simpa using hx)
  rcases hi.isUnit_or_isUnit hp with hu | hu
  · exact (not_isUnit_of_natDegree_pos _ (deg g hg)) hu
  · exact (not_isUnit_of_natDegree_pos _ (deg q hq)) hu

private theorem reducible_of_checked {a k : ℕ} {xs : List (ℕ × ℕ)}
    (hc : checkFrom a xs = true) (ha : a ≤ k) (hk : k < 1229) :
    ¬Irreducible (trinomial 1229 k) := by
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
      exact reducible_of_product hg hq he
    · exact ih ht (by omega)

/-- Every normalized degree-1229 trinomial has a factorization into two nonunits. -/
theorem trinomial_reducible {a : ℕ} (ha : 0 < a) (han : a < 1229) :
    ¬Irreducible (trinomial 1229 a) := reducible_of_checked checked ha han

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
