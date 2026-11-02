import TetraStereo.OneCenter.LocalizedPreflightDemandDiscovery
import TetraStereo.OneCenter.LocalizedOccurrenceExecutableRoots
import TetraStereo.OneCenter.LocalizedShortCircuitPipeline
import TetraStereo.OneCenter.LocalizedRule3DemandRankProducer

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedRetainedDemandCycleProbe

open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedShortCircuit
open TetraStereo.Certificate.WeightedDemand

/-!
# Executable retained-demand cycle probe

This module is a runtime witness, not a chemical statement and not a general classification.

The admitted fixture is the graph `S(=CH₂)₃` with ten atoms:

* atom `0` is sulfur, atoms `1,2,3` are the three doubly bonded carbons, and atoms `4..9` are one
  hydrogen pair per carbon;
* the covalent interactions are the three order-two `C=S` bonds and the six order-one `C-H` bonds.

No coordinates are supplied.  The fixture is admitted by the real source-admission pipeline, and
`graphReady` there checks structural well-formedness (closed shells, known Rule-2 masses, covalent
pairs only, unique records); it is **not** an external chemical-validity claim.

The probe establishes the following concrete facts, each by execution:

1. The atom-`0` root at `carrierFuel` has the three real carbon children with incoming cut at the
   sulfur root.  Both endpoint pairs of the physical `C=S` frame are pairwise ready, and the
   preflight-pruned extended demand at the first carbon keeps exactly the sibling request pairs
   `[C₂, C₃]` and `[H, H]`.
2. Those pruned requests produce an actual two-cycle in the demand graph:
   `C₁ -> C₂ -> C₁` (the reference cursors are the root's own real carbon children).
   `preparePreflightExtendedDemandPlan` rejects the root with a concrete `cycle` failure, not a
   traversal limit.
3. The leaf `H/H` endpoint of the first carbon, evaluated through the real recursive frame
   constructor at the reroot evaluation fuel, yields a full frame and the endpoint priority is
   `nonstereogenic`.
4. A *diagnostic* pair of arbitrary sibling callback answers (arbitrary Rule-3 key layers, not
   produced by any recursion and not claimed to be coherent) changes the projected left spatial
   reference from `C₂` to `C₃` while the projected geometry stays `nonstereogenic` by the
   absorption branch.  This is a function-dependence observation about the projection, not a
   certificate and not an existence claim for a coherent frame.
5. The unchanged recursive full frame from the atom-`0` root is `none` at the two candidate
   budgets `carrierFuel` and `carrierFuel + 2`.  No claim is made about any other budget.

The module proves no new chemical statement.  Unless a line says otherwise, the executable
assertions below are runtime observations of the existing definitions.
-/

/-! ## A kernel-checked absorption fact used by the projection diagnostic -/

namespace CertifiedLocalizedCIPInput

/-- Once the right endpoint priority is `nonstereogenic`, the descriptor-bearing spatial unit is
`nonstereogenic` regardless of the left priority and without consulting any coordinate.  This is the
absorptive branch of the existing executable unit compiler; the proof below is the sole new
kernel-checked declaration of this module. -/
theorem localizedRule3DescriptorBearingSpatialUnitOfPriorities?_eq_nonstereogenic_of_right
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftPriority rightPriority : input.LocalizedRule3EndpointPriority)
    (rightNonstereogenic : rightPriority = .nonstereogenic)
    (doubleBond : input.moleculeGraph.bond left right = 2) :
    input.localizedRule3DescriptorBearingSpatialUnitOfPriorities?
        left right leftPriority rightPriority =
      some { leftPriority := leftPriority, rightPriority := rightPriority,
             geometry := OfficialRule3Geometry.nonstereogenic } := by
  unfold localizedRule3DescriptorBearingSpatialUnitOfPriorities?
  rw [if_pos doubleBond]
  subst rightPriority
  cases leftPriority <;> rfl

end CertifiedLocalizedCIPInput

/-! ## Shared executable helpers -/

private def checkTest (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

private def cursorId {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) : String :=
  s!"atom={cursor.occurrence.1.root.val}, addr={repr cursor.occurrence.1.address}, \
prev={repr (cursor.previous?.map fun previous => previous.1.root.val)}"

private def weightedFailureName {input : CertifiedLocalizedCIPInput} {fuel : Nat} :
    DiscoveryFailure (input.LocalizedRerootCursor fuel) → String
  | .cycle cursor => "cycle(" ++ cursorId cursor ++ ")"
  | .traversalLimit => "traversalLimit"
  | .invalidRanks => "invalidRanks"
  | .missingRoot => "missingRoot"

private def axisEntryName {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (entry : input.LocalizedRule3CumulatedAxisEntry fuel) : String :=
  match entry with
  | .terminalStart _ => "terminalStart"
  | .internal _ _ => "internal"
  | .ringClosure _ _ => "ringClosure"
  | .branched _ _ _ _ => "branched"

private def endpointPriorityName {input : CertifiedLocalizedCIPInput}
    (priority : input.LocalizedRule3EndpointPriority) : String :=
  match priority with
  | .senior reference => "senior(" ++ toString reference.val ++ ")"
  | .nonstereogenic => "nonstereogenic"

private def geometryName : OfficialRule3Geometry → String
  | .seqcis => "seqcis"
  | .seqtrans => "seqtrans"
  | .nonstereogenic => "nonstereogenic"

private def nodeIsReal {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) : Bool :=
  match cursor.occurrence.1.node.provenance with
  | .realAtom => true
  | _ => false

private def nodeCurrentValue {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) : Option Nat :=
  cursor.occurrence.1.node.current?.map fun atom => atom.val

private def tripleOfList {α : Type} : List α → Option (α × α × α)
  | [first, second, third] => some (first, second, third)
  | _ => none

/-- The two reference cursors of the first explicit endpoint substituent pair, when both resolve
uniquely in the endpoint cursor's cut neighborhood. -/
private def referencePair {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (endpoint partner : input.Atom) :
    Option (input.LocalizedRerootCursor fuel × input.LocalizedRerootCursor fuel) :=
  match input.localizedRule3ExplicitSubstituents endpoint partner with
  | [first, second] => do
      let firstCursor ← input.localizedRule3ReferenceCursorExec? cursor first
      let secondCursor ← input.localizedRule3ReferenceCursorExec? cursor second
      some (firstCursor, secondCursor)
  | _ => none

/-! ## The admitted ten-atom `S(=CH₂)₃` graph -/

/-- Sulfur at `0`, three carbons at `1,2,3` doubly bonded to `0`, and one hydrogen pair per carbon
at `4..9`.  Coordinates are intentionally absent. -/
def source : AuthoritativeChemicalInput :=
  let sulfur : PeriodicElement := ⟨16, by decide, by decide⟩
  let carbon : PeriodicElement := ⟨6, by decide, by decide⟩
  let hydrogen : PeriodicElement := ⟨1, by decide, by decide⟩
  let bond (first second order : Nat) : SemanticInteraction :=
    { participants := [first, second], kind := .covalent order }
  { molecule :=
      { atoms :=
          [sulfur, carbon, carbon, carbon,
            hydrogen, hydrogen, hydrogen, hydrogen, hydrogen, hydrogen].map
            fun element => { element := element }
        interactions :=
          [ bond 0 1 2, bond 0 2 2, bond 0 3 2
          , bond 1 4 1, bond 1 5 1
          , bond 2 6 1, bond 2 7 1
          , bond 3 8 1, bond 3 9 1 ] } }

/-! ## Entry point -/

def main : IO Unit := do
  let start1 ← IO.monoMsNow
  match admitted : admitSource? source with
  | none => throw (IO.userError "test1: S(=CH2)3-like source admission failed")
  | some input => do
    checkTest "test1 admitted ten-atom graph" (input.molecule.atomCount == 10)
    have sourceExact : input.certified.certified.input = source :=
      TetraStereo.OneCenter.LocalizedReference.admitSource?_exact source input admitted
    have atomCountEq : input.certified.certified.input.molecule.atomCount = 10 := by
      rw [sourceExact]
      decide
    have atom0Mem : 0 < input.certified.certified.input.molecule.atomCount := by
      rw [atomCountEq]
      decide
    let fuel := carrierFuel input
    checkTest "test1 carrier fuel is atomCount + 1 (11)" (fuel == 11)
    let atom0 : input.certified.Atom := ⟨0, atom0Mem⟩
    let root : input.certified.LocalizedRerootCursor fuel :=
      { occurrence := input.certified.localizedAtomRootOccurrenceExecutable fuel atom0 }
    checkTest "test1 atom0 root is the root occurrence of atom 0"
      (root.occurrence.1.root.val == 0 && root.previous?.isNone)
    let children := input.certified.executableLocalizedRerootChildren root
    checkTest "test1 atom0 root has six executable children (three real C copies and three bond copies)"
      (children.length == 6)
    IO.println s!"atom0 root {cursorId root}: executable children={children.length}"
    for child in children do
      IO.println s!"  child {cursorId child}; provenance={repr child.occurrence.1.node.provenance}; \
current={repr (nodeCurrentValue child)}; ordinaryPairReady={input.certified.ordinaryPairReady child.occurrence}"
    let carbonChildren := children.filter fun cursor =>
      nodeIsReal cursor &&
        (match nodeCurrentValue cursor with
         | some value => value == 1 || value == 2 || value == 3
         | none => false)
    let some (c1, c2, c3) := tripleOfList carbonChildren
      | throw (IO.userError
          s!"test1: expected exactly three real carbon children, found {carbonChildren.length}")
    checkTest "test1 the three real carbon cursors carry the sulfur root as incoming cut"
      (decide (c1.previous? = some root.occurrence) &&
        decide (c2.previous? = some root.occurrence) &&
        decide (c3.previous? = some root.occurrence))
    checkTest "test1 real carbon cursor addresses are [0], [2], [4]"
      (decide (c1.occurrence.1.address = [0]) &&
        decide (c2.occurrence.1.address = [2]) &&
        decide (c3.occurrence.1.address = [4]))
    IO.println s!"carbon witness c1: {cursorId c1}"
    IO.println s!"carbon witness c2: {cursorId c2}"
    IO.println s!"carbon witness c3: {cursorId c3}"
    let some topology :=
        input.certified.localizedRule3PhysicalEndpointCursorFrameExec? c1.occurrence
      | throw (IO.userError "test1: c1 has no physical endpoint cursor frame")
    IO.println s!"c1 physical endpoint frame: left={topology.left.val}, right={topology.right.val}"
    IO.println s!"  leftCursor {cursorId topology.leftCursor}"
    IO.println s!"  rightCursor {cursorId topology.rightCursor}"
    checkTest "test1 c1 ordinaryPairReady holds (bilateral endpoint preflight)"
      (input.certified.ordinaryPairReady c1.occurrence)
    checkTest "test1 c1 left endpoint pair is ready"
      (input.certified.rule3EndpointPairReady topology.left topology.right topology.leftCursor)
    checkTest "test1 c1 right endpoint pair is ready"
      (input.certified.rule3EndpointPairReady topology.right topology.left topology.rightCursor)
    let leftSubstituents :=
      input.certified.localizedRule3ExplicitSubstituents topology.left topology.right
    let rightSubstituents :=
      input.certified.localizedRule3ExplicitSubstituents topology.right topology.left
    checkTest "test1 left endpoint explicit substituents are the sibling carbons (2,3)"
      (decide ((leftSubstituents.map fun atom => atom.val) = [2, 3]))
    checkTest "test1 right endpoint explicit substituents are the hydrogen pair (4,5)"
      (decide ((rightSubstituents.map fun atom => atom.val) = [4, 5]))
    let some (refC2, refC3) := referencePair topology.leftCursor topology.left topology.right
      | throw (IO.userError "test1: the left endpoint reference cursors do not resolve")
    let some (h4, h5) := referencePair topology.rightCursor topology.right topology.left
      | throw (IO.userError "test1: the right endpoint reference cursors do not resolve")
    IO.println s!"left references: {cursorId refC2}; {cursorId refC3}"
    IO.println s!"right (H/H) references: {cursorId h4}; {cursorId h5}"
    checkTest "test1 the left reference cursors are exactly the root's real carbon children c2 and c3"
      (decide (refC2 = c2) && decide (refC3 = c3))
    checkTest "test1 the H/H reference cursor addresses are [0,1] and [0,2]"
      (decide (h4.occurrence.1.address = [0, 1]) &&
        decide (h5.occurrence.1.address = [0, 2]))
    let entry? := input.certified.localizedRule3CumulatedAxisEntryExec? c1.occurrence
    match entry? with
    | some entry => IO.println s!"c1 cumulated axis route: {axisEntryName entry}"
    | none => IO.println "c1 cumulated axis route: none"
    checkTest "test1 c1 route is branched at the two sibling carbon continuations"
      (match entry? with
       | some (.branched _ _ _ _) => true
       | _ => false)
    checkTest "test1 c1 has an ordinary route certificate"
      (input.certified.localizedRule3OrdinaryRouteCertificate? c1.occurrence).isSome
    let requestsC1 :=
      input.certified.rule3PreflightExtendedNodeCallbackRequests c1.occurrence
    let extendedC1 :=
      input.certified.rule3ExtendedNodeCallbackRequests c1.occurrence
    IO.println s!"c1 pruned requests: {repr (requestsC1.map fun request => request.map cursorId)}"
    IO.println s!"c1 unpruned extended requests: \
{repr (extendedC1.map fun request => request.map cursorId)}"
    checkTest "test1 c1 pruned requests are exactly [[c2,c3],[h4,h5]]"
      (decide (requestsC1 = [[c2, c3], [h4, h5]]))
    checkTest "test1 the preflight-pruned request list equals the unpruned extended list at c1"
      (decide (requestsC1 = extendedC1))
    let requestsC2 :=
      input.certified.rule3PreflightExtendedNodeCallbackRequests c2.occurrence
    IO.println s!"c2 pruned requests: {repr (requestsC2.map fun request => request.map cursorId)}"
    checkTest "test1 c2 pruned requests reference c1 (concrete reverse edge)"
      (decide (c1 ∈ requestsC2.flatten))
    checkTest "test1 concrete pruned two-cycle c1 -> c2 -> c1"
      (decide (c2 ∈ requestsC1.flatten) && decide (c1 ∈ requestsC2.flatten))
    match input.certified.preparePreflightExtendedDemandPlan [root] with
    | .ok _ =>
        throw (IO.userError
          "test1: preflight-pruned constructor unexpectedly accepted the atom0 root")
    | .error (.cycle repeated) =>
        checkTest "test1 preflight-pruned constructor rejects with an actual cycle, not a traversal limit"
          true
        checkTest "test1 the repeated cursor is one of the carbon witnesses"
          (decide (repeated = c1) || decide (repeated = c2) || decide (repeated = c3))
        IO.println s!"preflight cycle repeated at {cursorId repeated}"
        IO.println s!"  its pruned requests: \
{repr ((input.certified.rule3PreflightExtendedNodeCallbackRequests repeated.occurrence).map
  fun request => request.map cursorId)}"
    | .error other =>
        throw (IO.userError
          ("test1: preflight-pruned constructor failed without a cycle: " ++
            weightedFailureName other))
    let finish1 ← IO.monoMsNow
    IO.println s!"TIMING test1 admission + bilateral preflight + concrete 2-cycle: {finish1 - start1}ms"

    -- ### Test 2: the real leaf `H/H` callback is a full frame and is nonstereogenic

    let start2 ← IO.monoMsNow
    let view : input.certified.LocalizedDependencyView c1.occurrence := fun _ _ => none
    let frameFuel := localizedOccurrenceRerootEvaluationFuel fuel
    checkTest "test2 reroot evaluation fuel is 2 * (carrierFuel + 1) = 24" (frameFuel == 24)
    let fullCallback : List (input.certified.LocalizedRerootCursor fuel) →
        Option input.certified.LocalizedRule3CanonicalKeyFrame :=
      fun cursors => input.certified.buildLocalizedExtendedShortCircuitRule3FrameExec?
        c1.occurrence view frameFuel cursors
    let hPair : List (input.certified.LocalizedRerootCursor fuel) := [h4, h5]
    checkTest "test2 the leaf H/H callback returns a full frame at adequate budget"
      ((fullCallback hPair).isSome)
    match fullCallback hPair with
    | none => throw (IO.userError "test2: leaf H/H full frame is none at budget 24")
    | some hFrame =>
        IO.println s!"H/H full frame at budget {frameFuel}: rawKeys={hFrame.rawKeys.length}, \
keys={hFrame.keys.length}, coupled={hFrame.coupled}, excluded={hFrame.excluded.length}"
    let rightPriority? := input.certified.localizedRule3ShortCircuitEndpointPriorityExec?
      c1.occurrence view fullCallback topology.right topology.left topology.rightCursor
    match rightPriority? with
    | none => throw (IO.userError "test2: H/H endpoint priority compiler returned none")
    | some result =>
        checkTest "test2 the H/H endpoint priority is nonstereogenic under the real recursive callback"
          (match result.priority with
           | .senior _ => false
           | .nonstereogenic => true)
        IO.println s!"H/H endpoint priority: {endpointPriorityName result.priority}"
    let finish2 ← IO.monoMsNow
    IO.println s!"TIMING test2 real leaf H/H full-frame projection: {finish2 - start2}ms"

    -- ### Test 3 (diagnostic): varying sibling callback answers

    let start3 ← IO.monoMsNow
    let emptyConstitutional : OfficialRuleMajorKey input.certified.Atom :=
      { rule1a := [], rule1b := [], rule2 := [], sourceNodes := [], complete := true }
    let diagKey (priority : Nat) : input.certified.LocalizedRerootRecursiveRule3SpatialKey :=
      { constitutional := emptyConstitutional
        observations := []
        rule3 := [[([], priority)]] }
    let diagFrame (firstPriority secondPriority : Nat) :
        input.certified.LocalizedRule3CanonicalKeyFrame :=
      { rawKeys := [diagKey firstPriority, diagKey secondPriority]
        coupled := false
        excluded := []
        keys := [diagKey firstPriority, diagKey secondPriority] }
    let diagCallback (firstPriority secondPriority : Nat) :
        List (input.certified.LocalizedRerootCursor fuel) →
          Option input.certified.LocalizedRule3CanonicalKeyFrame :=
      fun cursors =>
        if decide (cursors = [c2, c3]) then
          some (diagFrame firstPriority secondPriority)
        else
          fullCallback cursors
    let firstSenior? := input.certified.localizedRule3ShortCircuitSpatialUnitWithExec?
      c1.occurrence c1.occurrence view (diagCallback 2 1)
    let secondSenior? := input.certified.localizedRule3ShortCircuitSpatialUnitWithExec?
      c1.occurrence c1.occurrence view (diagCallback 1 2)
    checkTest "test3 DIAGNOSTIC both arbitrary sibling callback answers yield a spatial unit"
      (firstSenior?.isSome && secondSenior?.isSome)
    match firstSenior?, secondSenior? with
    | some firstResult, some secondResult =>
        let firstObs :=
          input.certified.localizedRule3ShortCircuitSpatialObservation firstResult
        let secondObs :=
          input.certified.localizedRule3ShortCircuitSpatialObservation secondResult
        checkTest "test3 DIAGNOSTIC geometry is constant (nonstereogenic) under sibling variation"
          ((match firstObs.unit.geometry with
            | .nonstereogenic => true
            | _ => false) &&
           (match secondObs.unit.geometry with
            | .nonstereogenic => true
            | _ => false))
        checkTest "test3 DIAGNOSTIC the projected left reference varies with the sibling answer"
          (firstObs.unit.leftReference.val != secondObs.unit.leftReference.val)
        checkTest "test3 DIAGNOSTIC the projected left references are the siblings C2 and C3"
          (firstObs.unit.leftReference.val == 2 && secondObs.unit.leftReference.val == 3)
        checkTest "test3 DIAGNOSTIC the projected right reference is the same H candidate"
          (firstObs.unit.rightReference.val == secondObs.unit.rightReference.val)
        checkTest "test3 DIAGNOSTIC the projected right reference is the first H substituent (4)"
          (firstObs.unit.rightReference.val == 4)
        checkTest "test3 DIAGNOSTIC the projected geometry is field-equal across the two answers"
          (decide (firstObs.unit.geometry = secondObs.unit.geometry))
        IO.println s!"DIAGNOSTIC answer A: leftRef={firstObs.unit.leftReference.val}, \
rightRef={firstObs.unit.rightReference.val}, geometry={geometryName firstObs.unit.geometry}"
        IO.println s!"DIAGNOSTIC answer B: leftRef={secondObs.unit.leftReference.val}, \
rightRef={secondObs.unit.rightReference.val}, geometry={geometryName secondObs.unit.geometry}"
        IO.println "DIAGNOSTIC: the sibling frame answers are arbitrary data; this is a projection \
function-dependence observation, not a certificate and not a coherent-frame existence claim."
    | _, _ =>
        throw (IO.userError
          "test3: a diagnostic sibling callback answer did not yield a spatial unit")
    let finish3 ← IO.monoMsNow
    IO.println s!"TIMING test3 diagnostic observation/key projection: {finish3 - start3}ms"

    -- ### Test 4: unchanged recursive full frame at two candidate budgets

    let start4 ← IO.monoMsNow
    let rootView : input.certified.LocalizedDependencyView root.occurrence := fun _ _ => none
    let rootFrameAtFuel :=
      input.certified.buildLocalizedExtendedShortCircuitRule3FrameExec?
        root.occurrence rootView fuel [root]
    let rootFrameAbove :=
      input.certified.buildLocalizedExtendedShortCircuitRule3FrameExec?
        root.occurrence rootView (fuel + 2) [root]
    checkTest "test4 recursive full frame from the atom0 root is none at budget carrierFuel (11)"
      rootFrameAtFuel.isNone
    checkTest "test4 recursive full frame from the atom0 root is none at budget carrierFuel+2 (13)"
      rootFrameAbove.isNone
    IO.println s!"recursive root frame: budget {fuel} some={rootFrameAtFuel.isSome}; \
budget {fuel + 2} some={rootFrameAbove.isSome} (no claim for other budgets)"
    let finish4 ← IO.monoMsNow
    IO.println s!"TIMING test4 two candidate recursive root budgets: {finish4 - start4}ms"

#eval main

end TetraStereo.Examples.LocalizedRetainedDemandCycleProbe
