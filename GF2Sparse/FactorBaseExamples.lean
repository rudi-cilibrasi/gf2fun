import GF2Sparse.FactorBase

/-! Kernel verification of the polynomial logarithms in the public factor-base files. -/

namespace GF2Sparse.FactorBase

open Lean Elab Term in
elab "logRows% " csv:term : term => do
  let e ← elabTerm csv (some (mkConst ``String))
  let .lit (.strVal value) := e.consumeMData | throwError "expected a literal CSV"
  let "mask,exponent" :: lines := value.trimAscii.toString.splitOn "\n"
    | throwError "expected the polynomial logarithm header"
  let rows ← lines.mapM fun line => do
    let [a,b] := line.splitOn "," | throwError "invalid logarithm row"
    let some mask := a.toNat? | throwError "invalid polynomial mask"
    let some exponent := b.toNat? | throwError "invalid exponent"
    pure (mask, exponent)
  return toExpr rows

def logs47 : List (ℕ × ℕ) := logRows% (include_str "../data/factor-base-47.csv")
def logs61 : List (ℕ × ℕ) := logRows% (include_str "../data/factor-base-61.csv")
def logs89 : List (ℕ × ℕ) := logRows% (include_str "../data/factor-base-89.csv")

open PackedSquare

/-- Every entry is checked by binary exponentiation with the same squaring circuit. -/
def checkLogs (n fuel : ℕ) (js : List ℕ) (rows : List (ℕ × ℕ)) : Bool :=
  let stages := stagesFor ((n-1).log2+1)
  checkBasis n stages && rows.all fun (p,e) =>
    powerBits n n fuel stages js (e.log2+1) e == some p

theorem checkLogs_sound {n fuel : ℕ} {js : List ℕ} {rows : List (ℕ × ℕ)}
    (hc : checkLogs n fuel js rows = true) {p e : ℕ} (hp : (p,e) ∈ rows) :
    let f := decode (xorShifts js 1)
    AdjoinRoot.mk f (decode p) = AdjoinRoot.root f ^ e := by
  simp only [checkLogs, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hc
  exact powerBits_sound hc.1 rfl Nat.lt_log2_self (hc.2 _ hp)

set_option maxRecDepth 4096

theorem checked47 : logs47.length = 71 ∧ (logs47.map Prod.fst).Nodup ∧
    checkLogs 47 3 [47,5,4,1,0] logs47 = true := by decide +kernel

theorem checked61 : logs61.length = 71 ∧ (logs61.map Prod.fst).Nodup ∧
    checkLogs 61 3 [61,5,2,1,0] logs61 = true := by decide +kernel

theorem checked89 : logs89.length = 71 ∧ (logs89.map Prod.fst).Nodup ∧
    checkLogs 89 3 [89,6,5,3,0] logs89 = true := by decide +kernel


/-- The exponent connecting the degree-89 sparse root to its Gauss period coordinate. -/
theorem period_power89 :
    let f := decode (xorShifts [89,6,5,3,0] 1)
    AdjoinRoot.mk f (decode 0x1df48cb4ae9eca599f5eb5e) =
      AdjoinRoot.root f ^ 237608358309219314788467309 :=
  checkLogs_sound (n := 89) (fuel := 3) (js := [89,6,5,3,0])
    (rows := [(0x1df48cb4ae9eca599f5eb5e,237608358309219314788467309)])
    (by decide +kernel) (by simp)

end GF2Sparse.FactorBase
