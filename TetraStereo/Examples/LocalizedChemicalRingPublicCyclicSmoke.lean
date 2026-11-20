import TetraStereo.Engine.PublicAPI

set_option autoImplicit false

/-! Generated-code smoke of an actual three-membered ring through the accepted public profile.
Parser order, hydrogen attachments, the triangle, nondegenerate frames and detected candidates
are checked independently of the result. The actual generated root context is tied; its two
actual sparse reference fallbacks return opposite letters. The public report retains all three
refusals. This is one tiny cyclic execution, not a ring-family performance or coverage benchmark.
Execute only under the aggregate build-memory cap. -/
namespace TetraStereo.Examples.LocalizedChemicalRingPublicCyclicSmoke

open OneCenter Engine.LocalizedChemicalRing
open OneCenter.LocalizedGenericMarkedRecalculation (frameAtoms? readback? structuralDepth
  consistent strict eligibleOf)
open OneCenter.LocalizedChemicalRingPreparedContextRecursion
  (childrenUnder preparedFacts prepareComparison? evaluateFallback?)
open OneCenter.LocalizedChemicalRingPhysicalSense (inputGeometry)

def smiles : String := "FC1(Cl)CC1"

/-- `ParseState.addAtom` appends the five lexical atoms. Ring closure adds a bond, not an atom.
`withExplicitHydrogens` visits original indices in order and appends two H for C3, then two for C4. -/
def spatial : SpatialConfiguration :=
  { positions := [
      { x := 0, y := 0, z := 1 },
      { x := 0, y := 0, z := 0 },
      { x := 0, y := 0, z := -1 },
      { x := 1, y := 0, z := 0 },
      { x := 0, y := 1, z := 0 },
      { x := 1, y := 0, z := 1 },
      { x := 1, y := 0, z := -1 },
      { x := 0, y := 1, z := 1 },
      { x := 0, y := 1, z := -1 }] }

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def smoke : IO Unit := do
  let input ← match admitSmilesSpatial? smiles spatial with
    | .ok (some input) => pure input
    | _ => throw (IO.userError "cyclic public profile: nine-atom ring admission failed")
  let molecule := input.molecule
  expect (coordinatesAdmitted input)
    "cyclic public profile: nonzero coordinates must pass physical admission despite later refusals"
  expect (decide (molecule.atoms.map AtomSpec.element =
    [.F, .C, .Cl, .C, .C, .H, .H, .H, .H]))
    "cyclic public profile: parser/expanded atom order changed"
  expect (decide (molecule.bondOrder 3 5 = 1 ∧ molecule.bondOrder 3 6 = 1 ∧
    molecule.bondOrder 4 7 = 1 ∧ molecule.bondOrder 4 8 = 1))
    "cyclic public profile: expanded hydrogen attachments changed"
  expect (decide (molecule.bondOrder 1 3 = 1 ∧ molecule.bondOrder 3 4 = 1 ∧
    molecule.bondOrder 4 1 = 1))
    "cyclic public profile: actual distinct atoms 1, 3, 4 must form a triangle"
  let centers := input.certified.canonicalTetrahedralCenters.map fun center => center.1.val
  expect (decide (centers = [1, 3, 4]))
    "cyclic public profile: detected candidate inventory must be exactly 1, 3, 4"
  let geom := inputGeometry input.certified
  expect (centers.all fun atom =>
    ((frameAtoms? molecule (canonicalCenterRoot atom)).bind (readback? geom)).isSome)
    "cyclic public profile: all three coordinate frames must be nondegenerate"
  let full := input.certified.localizedRerootCarrierCache
    (LocalizedMarkedRetainedMolecularSelection.retainedCarrierFuel input.certified)
  let rootAtom : input.certified.Atom ←
    if bound : 1 < input.certified.certified.input.molecule.atomCount then pure ⟨1, bound⟩
    else throw (IO.userError "cyclic public profile: root atom 1 is out of bounds")
  let slice := CertifiedLocalizedCIPInput.localizedRerootRootSliceCache full rootAtom
  let ops := LocalizedChemicalRingJointCachedExecutable.operations input.certified slice.reader molecule
  let root := canonicalCenterRoot 1
  let under := childrenUnder molecule (preparedFacts molecule ops (structuralDepth molecule root))
    geom [] root
  let atoms ← match frameAtoms? molecule root with
    | some atoms => pure atoms
    | none => throw (IO.userError "cyclic public profile: missing root frame")
  let prepared ← match prepareComparison? [] under [] with
    | some prepared => pure prepared
    | none => throw (IO.userError "cyclic public profile: generated root fact insertion failed")
  let (sorted, adjacent) ← match ops.contextOrder prepared root [] with
    | some partition => pure partition
    | none => throw (IO.userError "cyclic public profile: generated root partition failed")
  expect (consistent adjacent && !strict adjacent)
    "cyclic public profile: actual prepared root comparison must reach the tied fallback branch"
  let references := eligibleOf atoms sorted adjacent
  expect (decide (references.length = 2) && references.contains 3 && references.contains 4)
    "cyclic public profile: actual eligible root references must be precisely the two ring arms"
  let readings := references.map (evaluateFallback? molecule ops geom [] root [] under)
  expect (match readings with
    | [some .R, some .S] | [some .S, some .R] => true
    | _ => false)
    "cyclic public profile: actual sparse reference fallback readings must cancel as opposite letters"
  let report := analyze .accumulatedReferencesRegenerated input
  expect (match report with
    | [(1, none), (3, none), (4, none)] => true
    | _ => false)
    "cyclic public profile: public report must retain all three candidate refusals"
  expect (match stereoAssignments report with
    | [{ unit := .tetrahedral 1, outcome := .refused .rankingUnresolved },
       { unit := .tetrahedral 3, outcome := .refused .rankingUnresolved },
       { unit := .tetrahedral 4, outcome := .refused .rankingUnresolved }] => true
    | _ => false)
    "cyclic public profile: current public assignment conversion must retain every refusal"
  IO.println "cyclic public ring smoke passed: actual triangle, 9 atoms, 3 nondegenerate candidates, sparse opposite fallbacks, 3 retained refusals"

#eval smoke

end TetraStereo.Examples.LocalizedChemicalRingPublicCyclicSmoke
