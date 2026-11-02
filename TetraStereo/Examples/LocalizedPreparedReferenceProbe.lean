import TetraStereo.OneCenter.LocalizedPreparedReferencePipeline
import TetraStereo.Examples.LocalizedOmissionReadinessProbe
import TetraStereo.Examples.LocalizedDieneReferenceProbe
import TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedPreparedReferenceProbe

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.LocalizedExtendedShortCircuit
open TetraStereo.OneCenter.LocalizedExtendedShortCircuit.Prepared





































private def flushOut : IO Unit := do
  (← IO.getStdout).flush

private def checkTest (name : String) (condition : Bool) : IO Unit :=
  if condition then do
    IO.println ("ok: " ++ name)
    flushOut
  else throw (IO.userError ("failed: " ++ name))

private def note (message : String) : IO Unit := do
  IO.println message
  flushOut

/-! ## A local odd cumulene fixture

`F,Cl,Br` on C0, and a branch `C4=C5=C6=C7` with three consecutive double bonds (an odd cumulene),
one explicit hydrogen on C4 and two on C7.  Coordinates are intentionally absent: this fixture
checks preparation plans and both evaluator branches only, never a spatial descriptor. -/

private def carbon : PeriodicElement := ⟨6, by decide, by decide⟩
private def hydrogen : PeriodicElement := ⟨1, by decide, by decide⟩
private def fluorine : PeriodicElement := ⟨9, by decide, by decide⟩
private def chlorine : PeriodicElement := ⟨17, by decide, by decide⟩
private def bromine : PeriodicElement := ⟨35, by decide, by decide⟩
private def iodine : PeriodicElement := ⟨53, by decide, by decide⟩

private def atom (element : PeriodicElement) : SemanticAtom := { element := element }

private def bond (left right order : Nat) : SemanticInteraction :=
  { participants := [left, right], kind := .covalent order }

/-- An odd cumulene branch on a strict tetrahedral candidate: atoms
`0=C, 1=F, 2=Cl, 3=Br, 4..7=C, 8..10=H`. -/
def oddSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, fluorine, chlorine, bromine, carbon, carbon, carbon, carbon,
          hydrogen, hydrogen, hydrogen].map atom
        interactions := [bond 0 1 1, bond 0 2 1, bond 0 3 1, bond 0 4 1,
          bond 4 5 2, bond 5 6 2, bond 6 7 2,
          bond 4 8 1, bond 7 9 1, bond 7 10 1] }
    spatial? := none }

/-- Five-atom bromochlorofluoroiodomethane: the smallest strict tetrahedral center with exact
coordinates, already established as a safe `R` descriptor in `AuthoritativeLocalizedCIPAnalysis`.
It has no multiple bonds, so the callback-free readiness branch is exercised. -/
def halomethaneSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, fluorine, chlorine, bromine, iodine].map atom
        interactions := [bond 0 1 1, bond 0 2 1, bond 0 3 1, bond 0 4 1] }
    spatial? := some { positions :=
      [{ x := 0, y := 0, z := 0 }, { x := -1, y := -1, z := 1 },
       { x := -1, y := 1, z := -1 }, { x := 1, y := -1, z := -1 },
       { x := 1, y := 1, z := 1 }] } }

/-! ## Complete frame comparison

`LocalizedRerootRecursiveRule3SpatialKey` and `LocalizedRule3CanonicalKeyFrame` export no
`DecidableEq` instance, so a frame is compared on every stored field, exactly as the existing frame
probes do.  A `none`/`some` mismatch is rejected. -/

private def sameKey {input : CertifiedLocalizedCIPInput}
    (a b : input.LocalizedRerootRecursiveRule3SpatialKey) : Bool :=
  decide (a.constitutional.rule1a = b.constitutional.rule1a) &&
    decide (a.constitutional.rule1b = b.constitutional.rule1b) &&
      decide (a.constitutional.rule2 = b.constitutional.rule2) &&
        decide (a.constitutional.sourceNodes = b.constitutional.sourceNodes) &&
          decide (a.constitutional.complete = b.constitutional.complete) &&
            decide (a.observations = b.observations) && decide (a.rule3 = b.rule3)

private def sameKeys {input : CertifiedLocalizedCIPInput}
    (a b : List input.LocalizedRerootRecursiveRule3SpatialKey) : Bool :=
  a.length == b.length && (a.zip b).all fun pair => sameKey pair.1 pair.2

private def sameFrame {input : CertifiedLocalizedCIPInput}
    (a b : input.LocalizedRule3CanonicalKeyFrame) : Bool :=
  sameKeys a.rawKeys b.rawKeys && sameKeys a.keys b.keys &&
    decide (a.coupled = b.coupled) && decide (a.excluded = b.excluded)

private def sameFrameOption {input : CertifiedLocalizedCIPInput}
    (a b : Option input.LocalizedRule3CanonicalKeyFrame) : Bool :=
  match a, b with
  | none, none => true
  | some left, some right => sameFrame left right
  | none, some _ => false
  | some _, none => false




private structure PlanRowReport where
  rootsLength : Bool
  baseMatches : Bool
  positive : Bool
  children : Bool
  callbacks : Bool
  rootsCovered : Bool
  boundFormula : Bool
  rechecked : Bool
  vertexCount : Nat

private def checkPlanRow (input : Input) {fuel : Nat}
    (base : input.certified.LocalizedOccurrenceFourLigandFrame fuel)
    (row : Prepared.FourLigandPlan input.certified fuel) : PlanRowReport :=
  let heights := row.plan.ranks.height
  let vertices := row.plan.ranks.vertices
  let table : input.certified.ExtendedRule3DemandRankTable fuel :=
    vertices.map fun cursor => (cursor, heights cursor)
  let recheck := input.certified.checkExtendedRule3DemandRanks? table
  { rootsLength := row.roots.length == 4
    baseMatches := decide (row.roots = base.cursors) && decide (base.cursors.length = 4)
    positive := vertices.all fun cursor => 0 < heights cursor
    children := vertices.all fun cursor =>
      (input.certified.executableLocalizedRerootChildren cursor).all fun child =>
        decide (child ∈ vertices) && decide (heights child + 1 ≤ heights cursor)
    callbacks := vertices.all fun cursor =>
      (input.certified.rule3ExtendedNodeCallbackRequests cursor.occurrence).all fun request =>
        request.all (fun reference => decide (reference ∈ vertices)) &&
          decide (rule3CursorListHeight heights request + 2 ≤ heights cursor)
    rootsCovered := row.roots.all fun root => decide (root ∈ vertices)
    boundFormula := row.plan.bound == rule3CursorListHeight heights row.roots + 1
    rechecked :=
      match recheck with
      | some certificate => decide (certificate.vertices = vertices)
      | none => false
    vertexCount := vertices.length }

/-! ## Candidate corruption (outcome only; the rest of the node is preserved) -/

private def corruptOutcome {input : Input} (nodes : Nodes input) : Nodes input :=
  match nodes with
  | [] => []
  | head :: tail =>
      let changed : Option LocalizedAuxiliaryLabel :=
        if head.outcome = some (.chiral .R) then some (.chiral .S) else some (.chiral .R)
      { head with outcome := changed } :: tail

/-! ## The per-input probe -/

private def runAdmitted (name : String) (input : Input)
    (withReference withCachedChecks withFrameChecks requirePlans : Bool)
    (expected : Option (Nat × LocalizedAuxiliaryLabel)) : IO Unit := do
  let start ← IO.monoMsNow
  note s!"START {name}"
  let fuel := carrierFuel input
  let prep := Prepared.prepare input
  let preparedAt ← IO.monoMsNow
  note s!"PREPARED {name}: {preparedAt - start}ms"
  let carrier := prep.cache.carrier
  checkTest s!"{name} cached carrier equals the executable occurrence carrier"
    (decide (carrier = input.certified.localizedOccurrenceCarrier fuel))
  let entries := prep.entries
  checkTest s!"{name} preparation has one row per carrier occurrence"
    (entries.length == carrier.length)
  checkTest s!"{name} preparation rows enumerate exactly the carrier"
    (decide (entries.map (fun entry => entry.target) = carrier))
  checkTest s!"{name} lookup covers every carrier occurrence"
    (carrier.all fun target =>
      match prep.lookup? target with
      | some entry => decide (entry.target = target)
      | none => false)
  checkTest s!"{name} every lookup carries the production descriptor center"
    (carrier.all fun target =>
      decide (prep.center? target =
        input.certified.localizedOccurrenceDescriptorCenter? target))
  checkTest s!"{name} readiness decision equals carrier-wide empty callback requests"
    (prep.cache.ready?.isSome ==
      carrier.all (fun occurrence =>
        (input.certified.rule3ExtendedNodeCallbackRequests occurrence).isEmpty))
  let planReports := entries.filterMap fun entry =>
    match entry.base?, entry.plan? with
    | some base, some row => some (checkPlanRow input base row)
    | _, _ => none
  let planRowCount := (entries.filter fun entry => entry.plan?.isSome).length
  checkTest s!"{name} every stored plan row carries a stored four-ligand base"
    (planReports.length == planRowCount)
  checkTest s!"{name} every stored plan row has four roots matching its base"
    (planReports.all fun rowReport => rowReport.rootsLength && rowReport.baseMatches)
  checkTest s!"{name} every stored plan has positive ranks"
    (planReports.all fun rowReport => rowReport.positive)
  checkTest s!"{name} every stored plan closes every executable child edge"
    (planReports.all fun rowReport => rowReport.children)
  checkTest s!"{name} every stored plan closes every extended callback request"
    (planReports.all fun rowReport => rowReport.callbacks)
  checkTest s!"{name} every stored plan covers its four base cursors"
    (planReports.all fun rowReport => rowReport.rootsCovered)
  checkTest s!"{name} every stored plan bound is the root height plus one"
    (planReports.all fun rowReport => rowReport.boundFormula)
  checkTest s!"{name} the independent rank checker accepts every stored plan table"
    (planReports.all fun rowReport => rowReport.rechecked)
  if requirePlans then
    checkTest s!"{name} at least one checked plan row is stored" (0 < planRowCount)
  let facts? : Option (Facts input) :=
    if withReference then some (referenceFacts input) else none
  let nonCenters := carrier.filter fun target => (prep.center? target).isNone
  checkTest s!"{name} all {nonCenters.length} non-center occurrences agree with production (none)"
    (nonCenters.all fun target =>
      decide (Prepared.descriptorWithTerminalTie? input prep prep.cache.ready? target
          (fun _ _ => none) =
        input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
          target (fun _ _ => none)))
  let mut viewComparisons := 0
  let mut skippedCenters := 0
  for center in input.certified.canonicalTetrahedralCenters do
    let index := center.val.val
    let target := input.certified.localizedFinalOccurrenceExecutable fuel center
    checkTest s!"{name} center {index} final occurrence stores its descriptor center"
      (match prep.center? target with
       | some stored => decide (stored = center)
       | none => false)
    let storedBase := prep.base? target
    checkTest s!"{name} center {index} stores a four-ligand base"
      (match storedBase with
       | some base => decide (base.cursors.length = 4)
       | none => false)
    let storedPlan := prep.plan? target
    let evaluable := prep.cache.ready?.isSome || storedPlan.isSome
    if !evaluable then
      skippedCenters := skippedCenters + 1
      IO.println s!"  {name} center {index}: view comparison skipped (no stored plan, no readiness)"
    else
      let viewNone : input.certified.LocalizedDependencyView target := fun _ _ => none
      let productionNone :=
        input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
          target viewNone
      let preparedNone :=
        Prepared.descriptorWithTerminalTie? input prep prep.cache.ready? target viewNone
      checkTest s!"{name} center {index} prepared equals production at the empty view"
        (decide (preparedNone = productionNone))
      let viewParity : input.certified.LocalizedDependencyView target :=
        fun source _ =>
          if source.1.address.length % 2 = 0 then some (.chiral .R) else some (.chiral .S)
      let productionParity :=
        input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
          target viewParity
      let preparedParity :=
        Prepared.descriptorWithTerminalTie? input prep prep.cache.ready? target viewParity
      checkTest s!"{name} center {index} prepared equals production at the alternating view"
        (decide (preparedParity = productionParity))
      viewComparisons := viewComparisons + 2
      match facts? with
      | none => pure ()
      | some facts =>
          let viewReference : input.certified.LocalizedDependencyView target :=
            fun source _ => TetraStereo.Certificate.Dependency.lookup facts source
          let productionReference :=
            input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
              target viewReference
          let preparedReference :=
            Prepared.descriptorWithTerminalTie? input prep prep.cache.ready? target viewReference
          checkTest s!"{name} center {index} prepared equals production at the reference view"
            (decide (preparedReference = productionReference))
          let referenceLookup := TetraStereo.Certificate.Dependency.lookup facts target
          checkTest s!"{name} center {index} reference view reproduces the reference facts"
            (decide (preparedReference = referenceLookup))
          viewComparisons := viewComparisons + 1
          match expected with
          | some (expectedIndex, label) =>
              if expectedIndex == index then
                checkTest
                  s!"{name} center {index} successful descriptor matches the expected production value"
                  (decide (preparedReference = some label))
                checkTest
                  s!"{name} center {index} reference facts carry the expected production value"
                  (decide (referenceLookup = some label))
          | none => pure ()
      if withFrameChecks then
        match storedBase, storedPlan with
        | some base, some _ =>
            let viewNone : input.certified.LocalizedDependencyView target := fun _ _ => none
            let productionFuel := localizedDescriptorBearingRule3EvaluationFuel fuel
            let preparedFrame := Prepared.rule3FrameFrom? input prep target viewNone base
            let productionFrame :=
              input.certified.buildLocalizedExtendedShortCircuitRule3FrameExec?
                target viewNone productionFuel base.cursors
            checkTest
              s!"{name} center {index} stored-plan Rule3 frame matches production on every field"
              (sameFrameOption (input := input.certified) preparedFrame productionFrame)
        | _, _ => pure ()
  note s!"FIXTURE {name}: atoms={input.certified.certified.input.molecule.atomCount}, \
carrier={carrier.length}, entries={entries.length}, \
centers={input.certified.canonicalTetrahedralCenters.length}, planRows={planRowCount}, \
planVertices={(planReports.foldl (fun total rowReport => total + rowReport.vertexCount) 0)}, \
ready={prep.cache.ready?.isSome}, viewComparisons={viewComparisons}, skippedCenters={skippedCenters}"
  match facts? with
  | none => pure ()
  | some originalFacts =>
      if withCachedChecks then
        let cachedNodes := Cached.nodesUsingCache input prep.cache
        let cachedFacts? := Cached.checkUsingCache? input prep.cache cachedNodes
        checkTest s!"{name} cached checker fast-accepts the cached reference nodes"
          cachedFacts?.isSome
        checkTest s!"{name} cached checker reproduces the production reference facts"
          (match cachedFacts? with
           | some facts => decide (facts = originalFacts)
           | none => false)
        let preparedFacts? := PreparedPipeline.checkPrepared? input prep cachedNodes
        checkTest s!"{name} prepared checker fast-accepts the cached reference nodes"
          preparedFacts?.isSome
        checkTest s!"{name} prepared checker reproduces the production reference facts"
          (match preparedFacts? with
           | some facts => decide (facts = originalFacts)
           | none => false)
        let accepted := PreparedPipeline.evaluatePrepared input prep cachedNodes
        checkTest s!"{name} prepared pipeline keeps the accepted candidate nodes"
          (decide (accepted.nodes = cachedNodes))
        checkTest s!"{name} prepared pipeline accepted facts equal the production reference facts"
          (decide (accepted.facts = originalFacts))
        let corrupt := corruptOutcome cachedNodes
        checkTest s!"{name} a corrupted outcome is rejected by the prepared checker"
          (PreparedPipeline.checkPrepared? input prep corrupt).isNone
        let fallback := PreparedPipeline.evaluatePrepared input prep corrupt
        checkTest s!"{name} a corrupted outcome falls back to the prepared reference facts"
          (decide (fallback.facts = originalFacts))
        checkTest s!"{name} the fallback keeps the cached reference nodes"
          (decide (fallback.nodes = cachedNodes))
        let invalidReferences : Nodes input :=
          match cachedNodes with
          | [] => []
          | head :: tail => { head with references := [0] } :: tail
        checkTest s!"{name} an out-of-range reference index is rejected by the prepared checker"
          (PreparedPipeline.checkPrepared? input prep invalidReferences).isNone
        checkTest s!"{name} the empty candidate is rejected by the prepared checker"
          (PreparedPipeline.checkPrepared? input prep ([] : Nodes input)).isNone
        checkTest s!"{name} an incomplete single-node candidate is rejected by the prepared checker"
          (PreparedPipeline.checkPrepared? input prep (cachedNodes.take 1)).isNone
  let finish ← IO.monoMsNow
  note s!"TIMING {name}: {finish - start}ms"

private def runSourceFixture (name : String) (source : AuthoritativeChemicalInput)
    (withReference withCachedChecks withFrameChecks requirePlans : Bool)
    (expected : Option (Nat × LocalizedAuxiliaryLabel)) : IO Unit := do
  let some input := admitSource? source
    | throw (IO.userError (name ++ ": admission failed"))
  checkTest s!"{name} admitted" true
  runAdmitted name input withReference withCachedChecks withFrameChecks requirePlans expected

private def runSmilesFixture (name : String) (text : String) (spatial : SpatialConfiguration)
    (withReference withCachedChecks withFrameChecks requirePlans : Bool)
    (expected : Option (Nat × LocalizedAuxiliaryLabel)) : IO Unit := do
  match admitSmilesSpatial? text spatial with
  | .error message => throw (IO.userError (name ++ ": parse or admission error: " ++ message))
  | .ok none => throw (IO.userError (name ++ ": admission returned none"))
  | .ok (some input) =>
      checkTest s!"{name} admitted" true
      runAdmitted name input withReference withCachedChecks withFrameChecks requirePlans expected

/-! ## Entry point

The imported fixtures are data only.  Each imported module's own `#eval` block is *not* re-run by
importing it; the observations below are computed in this module from the imported source records.
-/

private def measurePreparation (name : String) (input : Input) : IO Unit := do
  let start ← IO.monoMsNow
  note s!"START {name}"
  let prep := Prepared.prepare input
  let finish ← IO.monoMsNow
  let planRows := prep.entries.filter fun entry => entry.plan?.isSome
  let planVertices := planRows.foldl
    (fun total entry =>
      total + match entry.plan? with
        | some row => row.plan.ranks.vertices.length
        | none => 0) 0
  note s!"PREP-ONLY {name}: atoms={input.certified.certified.input.molecule.atomCount}, \
carrier={prep.cache.carrier.length}, entries={prep.entries.length}, \
centers={input.certified.canonicalTetrahedralCenters.length}, planRows={planRows.length}, \
planVertices={planVertices}, ready={prep.cache.ready?.isSome}, {finish - start}ms"

def main : IO Unit := do
  -- Smallest known-positive first: five atoms, no multiple bonds, exact coordinates.  This is
  -- the complete assertion battery (preparation rows, plans, three views, positive descriptor,
  -- field-by-field frame, cached fast acceptance and corrupt/incomplete fallback).
  runSourceFixture "positive-halomethane" halomethaneSource
    true true true true (some (0, .chiral .R))
  -- Diagnostic pass for the larger fixtures: preparation cost only, so an expensive fixture is
  -- identified before any further whole-carrier replay is attempted.
  let some diene := admitSource? LocalizedDieneReferenceProbe.dieneSource
    | throw (IO.userError "diene admission failed")
  measurePreparation "diene-positive" diene
  match admitSmilesSpatial? LocalizedNoDoubleReferenceFixtures.interactingSmiles
      LocalizedNoDoubleReferenceFixtures.interactingSpatial with
  | .ok (some input) => measurePreparation "interacting-centers" input
  | _ => throw (IO.userError "interacting admission failed")
  let some ring := admitSource? LocalizedOmissionReadinessProbe.ringSource
    | throw (IO.userError "ring admission failed")
  measurePreparation "cyclic-ring" ring
  let some odd := admitSource? oddSource
    | throw (IO.userError "odd admission failed")
  measurePreparation "odd-cumulene" odd
  match admitSmilesSpatial? LocalizedNoDoubleReferenceFixtures.deepSmiles
      LocalizedNoDoubleReferenceFixtures.deepSpatial with
  | .ok (some input) => measurePreparation "deep-comparison" input
  | _ => throw (IO.userError "deep admission failed")

#eval main

end TetraStereo.Examples.LocalizedPreparedReferenceProbe
