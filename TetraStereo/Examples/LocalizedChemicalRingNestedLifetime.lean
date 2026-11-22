import TetraStereo.Engine.PublicAPI

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedChemicalRingNestedLifetime

open OneCenter Engine.LocalizedChemicalRing
open LocalizedGenericMarkedRecalculation
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingMultiMarkRecursion (MultiOperations markedReadingJoint?)
open LocalizedChemicalRingPhysicalSense (inputGeometry)

-- Atom 0 and atom 2 each have four oxygen bridges. No implicit hydrogen is required.
def spatial : SpatialConfiguration :=
  { positions := [
    { x := 0, y := 0, z := 1 }, { x := 1, y := 1, z := 1 },
    { x := 0, y := 0, z := -1 }, { x := -1, y := -1, z := 1 },
    { x := -1, y := 1, z := -1 }, { x := 1, y := -1, z := -1 }] }

private def get {α : Type} (reason : String) : Option α → IO α
  | some value => pure value
  | none => throw (IO.userError reason)

/-- Every recursive promotion supplies only its new atom to both the comparison and the
regenerated child observations. All other operations are the prepared evaluator's. -/
def replacement (ops : MultiOperations) : PreparedStep := fun mol geom state refs node under => do
  let atoms ← frameAtoms? mol node
  let prepared ← prepareComparison? state under refs
  match ops.contextOrder prepared node refs with
  | none => none
  | some (positions, adjacent) =>
    if ¬ atoms.Nodup ∨ consistent adjacent = false then none
    else if strict adjacent then do
      let ranked ← atomsAt? atoms positions
      readback? geom ranked
    else
      consensus ((eligibleOf atoms positions adjacent).map
        (evaluateFallback? mol ops geom state node [] under))

theorem first_promotion (ops : MultiOperations) (mol : RawMolecule) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (under : ChildStates) :
    replacement ops mol geom state [] node under =
      rawStepPrepared? ops mol geom state [] node under := rfl

private def expect (ok : Bool) (message : String) : IO Unit := unless ok do throw (IO.userError message)

private def run : IO Unit := do
  let input ← match admitSmilesSpatial? "C123OC(O1)(O2)O3" spatial with
    | .ok (some input) => pure input
    | _ => throw (IO.userError "four-bridge admission")
  let mol := input.molecule
  unless coordinatesAdmitted input do throw (IO.userError "degenerate frame")
  let full := input.certified.localizedRerootCarrierCache
    (LocalizedMarkedRetainedMolecularSelection.retainedCarrierFuel input.certified)
  let rootAtom : input.certified.Atom ← if h : 0 < input.certified.certified.input.molecule.atomCount
    then pure ⟨0,h⟩ else throw (IO.userError "empty molecule")
  let slice := CertifiedLocalizedCIPInput.localizedRerootRootSliceCache full rootAtom
  let ops := LocalizedChemicalRingJointCachedExecutable.operations input.certified slice.reader mol
  let root := canonicalCenterRoot 0
  let bridge ← get "bridge 1" ((mol.canonicalChildren root).find? (·.atom == 1))
  let node ← get "distal center" ((mol.canonicalChildren bridge).find? (·.atom == 2))
  let base := inputGeometry input.certified
  let rootAtoms ← get "root frame" (frameAtoms? mol root)
  let atoms ← get "distal ligands" (frameAtoms? mol node)
  expect (mol.valenceOK? && (input.certified.canonicalTetrahedralCenters.map (·.1.val)) == [0,2] &&
    atoms == [1,3,4,5]) "valence, detected inventory or distal frame"
  for keep in [true,false] do
    let step := if keep then rawStepPrepared? ops else replacement ops
    for reflected in [false,true] do
      let geom := if reflected then mirror base else base
      let under := childrenUnder mol (factsOfStep step mol (structuralDepth mol node)) geom [] node
      let rootUnder := childrenUnder mol (factsOfStep step mol (structuralDepth mol root)) geom [] root
      let rootFacts ← get "root preparation" (prepareComparison? [] rootUnder [])
      let (pos,adj) ← get "root comparison" (ops.contextOrder rootFacts root [])
      expect ((eligibleOf rootAtoms pos adj).contains 3) "first promotion not selected"
      let prepared ← get "inherited child observations" (prepareComparison? [] under [3])
      let (sort,cmp) ← get "inherited partition" (ops.contextOrder prepared node [3])
      let selected := eligibleOf atoms sort cmp
      expect (selected == [4,5]) "nested promotions not selected"
      let incoming := if keep then [3] else []
      let readings := selected.map (evaluateFallback? mol ops geom [] node incoming under)
      let expected : List (Option RS) := if !keep then [none,none] else
        if reflected then [some .S,some .R] else [some .R,some .S]
      expect (readings == expected) "nested raw readings"
      let outcome := step mol geom [] [3] node under
      expect (outcome.isNone) "distal consensus"
      for mark in selected do
        let refs := incoming ++ [mark]
        let temp ← get "promoted child observations" (prepareComparison? [] under refs)
        let (order,relations) ← get "promoted partition" (ops.contextOrder temp node refs)
        let ranked ← get "invalid ranking positions" (atomsAt? atoms order)
        expect (temp.isEmpty && consistent relations && strict relations == keep) "promoted partition strictness"
        IO.println s!"keep={keep} mirror={reflected} refs={refs} order={ranked} ties={eligibleOf atoms order relations}"
      IO.println s!"nested promotion readings {repr readings}"
    let results ← input.certified.canonicalTetrahedralCenters.mapM fun c => do
      let ownSlice := CertifiedLocalizedCIPInput.localizedRerootRootSliceCache full c.1
      let ownOps := LocalizedChemicalRingJointCachedExecutable.operations input.certified ownSlice.reader mol
      let ownStep := if keep then rawStepPrepared? ownOps else replacement ownOps
      let q := canonicalCenterRoot c.1.val
      pure (c.1.val, descriptorOfStep ownStep mol (structuralDepth mol q) base [] [] q)
    expect (results.all (fun r => r.2.isNone)) "complete report"
    IO.println s!"keep={keep} report={repr results}"

#eval run

end TetraStereo.Examples.LocalizedChemicalRingNestedLifetime

assert_kernel_only TetraStereo.Examples.LocalizedChemicalRingNestedLifetime.first_promotion
