import TetraStereo.OneCenter.LocalizedNoDoubleCachedEvaluation
import TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedNoDoubleCachedPipelineProbe
open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open LocalizedNoDoubleReference LocalizedNoDoubleReferenceFixtures

private def checkAssertion (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

private def accepted (name : String) (admitted : Except ParserError (Option Input)) : IO Input :=
  match admitted with
  | .ok (some input) => pure input
  | _ => throw (IO.userError ("fixture rejected: " ++ name))

private def checkedReport (input : Input) : IO (List (Nat × Option LocalizedAuxiliaryLabel)) := do
  let some facts := LocalizedNoDoubleCachedEvaluation.cachedCheckProposals? input
    | throw (IO.userError "generated ranked certificate was rejected")
  pure (LocalizedNoDoubleCachedEvaluation.centersLookup input facts)

/-- Run the ranked producer and replay its complete certificate; the independently proved cached
reader preserves the original descriptor semantics. Expected labels below were observed in the
separate iterative-reference regression, not supplied to the evaluator. -/
def main : IO Unit := do
  let ringInput ← accepted "ring" ring.admitted
  let ringReport ← checkedReport ringInput
  checkAssertion "ranked ring certificate reproduces all reference center outcomes"
    (decide (ringReport = [(0, some (.chiral .S)), (2, some (.chiral .R)), (4, none)]))
  let tripleInput ← accepted "nitrile" nitrile.admitted
  let tripleReport ← checkedReport tripleInput
  checkAssertion "ranked triple-bond certificate reproduces all reference center outcomes"
    (decide (tripleReport = [(0, some (.chiral .S)), (4, some (.chiral .R)), (6, none)]))
  let deepInput ← accepted "deep" deep.admitted
  let deepReport ← checkedReport deepInput
  checkAssertion "ranked deep certificate reproduces all reference center outcomes"
    (decide (deepReport = [(1, some (.chiral .R)), (2, none), (3, none), (4, none),
      (6, none), (7, none), (8, none)]))
  let beforeInput ← accepted "interacting" interacting.admitted
  let afterInput ← accepted "interacting variation" interactingVariation.admitted
  let before ← checkedReport beforeInput
  let after ← checkedReport afterInput
  checkAssertion "ranked interacting certificates reproduce central none to r and branch R to S"
    (decide (before = [(1, none), (2, some (.chiral .R)), (7, some (.chiral .R))] ∧
      after = [(1, some (.pseudoasymmetric .r)), (2, some (.chiral .S)), (7, some (.chiral .R))]))
  IO.println "ranked cached molecular certificates complete"

#eval main
end TetraStereo.Examples.LocalizedNoDoubleCachedPipelineProbe
