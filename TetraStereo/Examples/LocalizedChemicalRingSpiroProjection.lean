import TetraStereo.Engine.LocalizedChemicalRingCenterProjection
import TetraStereo.Engine.LocalizedChemicalRingPhysicalCertificate

set_option autoImplicit false

/-! Runtime source control, not a theorem or a family-completeness claim.
Source: IUPAC2013 P-93.5.3.2 Example2, PDFpage72 of the frozen iupac-P9.pdf,
SHA256 9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450.
The drawing labels (5R)-1,6-dioxaspiro[4.4]nonane. Source O1 is a solid wedge lower-right,
O6 ordinary upper-left, C4 hashed upper-right and C9 ordinary lower-left. The stencil below
preserves those directions; source priority O1>O6>C4>C9 has volume -8, hence R.
Lexical atoms0..8 have source locants5,1,2,3,4,6,7,8,9. Public intake appends12 hydrogens.
Execute only under the aggregate build-memory cap. No runtime result is asserted as a theorem. -/
namespace TetraStereo.Examples.LocalizedChemicalRingSpiroProjection

open OneCenter Engine.LocalizedChemicalRing
open OneCenter.LocalizedGenericMarkedRecalculation (frameAtoms? readback? structuralDepth
  consistent strict eligibleOf atomsAt?)
open OneCenter.LocalizedChemicalRingPreparedContextRecursion
  (childrenUnder preparedFacts prepareComparison? evaluateFallback?)
open OneCenter.LocalizedChemicalRingPhysicalSense (inputGeometry)

def smiles : String := "C12(OCCC1)OCCC2"

def spatial : SpatialConfiguration :=
  { positions := [
      { x := 0, y := 0, z := 0 },
      { x := 1, y := -1, z := 1 },
      { x := 3, y := -1, z := 1 },
      { x := 3, y := 1, z := -1 },
      { x := 1, y := 1, z := -1 },
      { x := -1, y := 1, z := 0 },
      { x := -3, y := 1, z := 0 },
      { x := -3, y := -1, z := 0 },
      { x := -1, y := -1, z := 0 },
      { x := 3, y := -1, z := 2 },
      { x := 3, y := -1, z := 0 },
      { x := 3, y := 1, z := 0 },
      { x := 3, y := 1, z := -2 },
      { x := 1, y := 1, z := 0 },
      { x := 1, y := 1, z := -2 },
      { x := -3, y := 1, z := 1 },
      { x := -3, y := 1, z := -1 },
      { x := -3, y := -1, z := 1 },
      { x := -3, y := -1, z := -1 },
      { x := -1, y := -1, z := 1 },
      { x := -1, y := -1, z := -1 }] }

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def smoke : IO Unit := do
  let input ← match admitSmilesSpatial? smiles spatial with
    | .ok (some input) => pure input
    | .ok none => throw (IO.userError "spiro source control: structural/spatial admission failed")
    | .error message => throw (IO.userError ("spiro source control: parser failed: " ++ message))
  let molecule := input.molecule
  expect (decide (molecule.atoms.map AtomSpec.element =
    [.C, .O, .C, .C, .C, .O, .C, .C, .C] ++ List.replicate 12 .H))
    "spiro source control: lexical heavy atoms or hydrogen expansion changed"
  expect (decide (molecule.bondOrder 0 1 = 1 ∧ molecule.bondOrder 1 2 = 1 ∧
    molecule.bondOrder 2 3 = 1 ∧ molecule.bondOrder 3 4 = 1 ∧ molecule.bondOrder 4 0 = 1 ∧
    molecule.bondOrder 0 5 = 1 ∧ molecule.bondOrder 5 6 = 1 ∧ molecule.bondOrder 6 7 = 1 ∧
    molecule.bondOrder 7 8 = 1 ∧ molecule.bondOrder 8 0 = 1))
    "spiro source control: two five-membered source rings changed"
  expect (decide (molecule.bonds.length = 22))
    "spiro source control: ten skeletal plus twelve hydrogen bonds required"
  expect ([(2,9),(2,10),(3,11),(3,12),(4,13),(4,14),
    (6,15),(6,16),(7,17),(7,18),(8,19),(8,20)].all fun edge =>
      molecule.bondOrder edge.1 edge.2 == 1)
    "spiro source control: hydrogen append/attachment order changed"
  let centers := input.certified.canonicalTetrahedralCenters.map fun center => center.1.val
  expect (decide (centers = [0,2,3,4,6,7,8]))
    "spiro source control: root and six methylene candidate inventory changed"
  expect (coordinatesAdmitted input)
    "spiro source control: all seven frames must pass physical coordinate admission"
  let geom := inputGeometry input.certified
  expect (centers.all fun atom =>
    ((frameAtoms? molecule (canonicalCenterRoot atom)).bind (readback? geom)).isSome)
    "spiro source control: a candidate frame has degenerate coordinates"
  expect (match readback? geom [1,5,4,8] with | some .R => true | _ => false)
    "spiro source control: independent source-priority geometry must read R"
  let some c := input.certified.canonicalTetrahedralCenters.find? (fun c => c.1.val == 0)
    | throw (IO.userError "annotated center 0 missing")
  let ids := List.range molecule.atoms.length
  let marks := [1,4,5,8]
  let contexts := [] :: ((ids.map (fun i => [i])) ++
    (marks.flatMap fun i => ids.map fun j => [i,j]))
  let actual := centerOutcome input c contexts
  expect (actual == some (.chiral .R)) s!"expected published (5R), observed {repr actual}"
  IO.println s!"P-93.5.3.2 Example 2: source locant 5, parser atom 0, public entry {repr actual}"

#eval smoke

end TetraStereo.Examples.LocalizedChemicalRingSpiroProjection
