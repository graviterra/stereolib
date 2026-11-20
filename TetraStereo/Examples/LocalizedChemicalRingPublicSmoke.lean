import TetraStereo.Engine.PublicAPI

set_option autoImplicit false

/-! Small generated-code smoke of the opt-in public route, through the existing PublicAPI import.
The five-atom strict fixture, reflection, degenerate-geometry refusal, coordinate-count rejection
and parser error are runtime assertions. This does not benchmark recursive ring breadth and does
not replace the general source-model/report proofs. Execute only under the aggregate build cap. -/
namespace TetraStereo.Examples.LocalizedChemicalRingPublicSmoke

open OneCenter Engine.LocalizedChemicalRing

/-- Atom order of `FC(Cl)(Br)I`: F, C, Cl, Br, I. The descending ligand volume is -1. -/
def spatial : SpatialConfiguration :=
  { positions := [
      { x := 0, y := 0, z := 0 },
      { x := 0, y := 0, z := 0 },
      { x := 1, y := 0, z := 0 },
      { x := 0, y := 1, z := 0 },
      { x := 0, y := 0, z := 1 }] }

def reflected : SpatialConfiguration :=
  { positions := spatial.positions.map CartesianPoint3.reflectX }

def degenerate : SpatialConfiguration :=
  { positions := List.replicate 5 { x := 0, y := 0, z := 0 } }

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def smoke : IO Unit := do
  let input ← match admitSmilesSpatial? "FC(Cl)(Br)I" spatial with
    | .ok (some input) => pure input
    | _ => throw (IO.userError "public ring profile: strict structural admission failed")
  expect (coordinatesAdmitted input)
    "public ring profile: strict nonzero coordinates must pass physical admission"
  let flatInput ← match admitSmilesSpatial? "FC(Cl)(Br)I" degenerate with
    | .ok (some input) => pure input
    | _ => throw (IO.userError "public ring profile: flat structural admission failed")
  expect (!coordinatesAdmitted flatInput)
    "public ring profile: zero-volume coordinates must fail physical admission"
  let strict := analyzeSmilesStereoSpatial? .accumulatedReferencesRegenerated "FC(Cl)(Br)I" spatial
  expect (match strict with
    | .ok (some [{ unit := .tetrahedral 1, outcome := .tetrahedral .R }]) => true
    | _ => false)
    "public ring profile: strict five-atom spatial report must be R at atom 1"
  let mirror := analyzeSmilesStereoSpatial? .accumulatedReferencesRegenerated "FC(Cl)(Br)I" reflected
  expect (match mirror with
    | .ok (some [{ unit := .tetrahedral 1, outcome := .tetrahedral .S }]) => true
    | _ => false)
    "public ring profile: reflected five-atom spatial report must be S at atom 1"
  let refused := analyzeSmilesStereoSpatial? .accumulatedReferencesRegenerated "FC(Cl)(Br)I" degenerate
  expect (match refused with
    | .ok (some [{ unit := .tetrahedral 1, outcome := .refused .rankingUnresolved }]) => true
    | _ => false)
    "public ring profile: degenerate geometry must retain a refusal at atom 1"
  let rejected := analyzeSmilesStereoSpatial? .accumulatedReferencesRegenerated
    "FC(Cl)(Br)I" { positions := [] }
  expect (match rejected with | .ok none => true | _ => false)
    "public ring profile: wrong coordinate count must fail admission"
  let malformed := analyzeSmilesStereoSpatial? .accumulatedReferencesRegenerated "(" spatial
  expect (match malformed with | .error _ => true | .ok _ => false)
    "public ring profile: malformed SMILES must preserve parser error"
  IO.println "public ring profile smoke passed: R, reflected S, refusal, rejection, parser error, coordinate admission and zero-volume rejection"

#eval smoke

end TetraStereo.Examples.LocalizedChemicalRingPublicSmoke
