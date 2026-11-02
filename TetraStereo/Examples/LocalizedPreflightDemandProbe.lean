import TetraStereo.OneCenter.LocalizedPreflightDemandDiscovery
import TetraStereo.OneCenter.LocalizedOccurrenceExecutableRoots
import TetraStereo.Examples.LocalizedRule3DemandCoupledAxesProbe

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedPreflightDemandProbe

open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedShortCircuit
open TetraStereo.Certificate.WeightedDemand



























/-! ## Shared executable helpers -/

private def checkTest (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

private def cursorId {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) : String :=
  s!"atom={cursor.occurrence.1.root.val}, addr={repr cursor.occurrence.1.address}, \
prev={repr (cursor.previous?.map fun previous => previous.1.root.val)}"

private def rule3FailureName {input : CertifiedLocalizedCIPInput} {fuel : Nat} :
    input.Rule3DemandDiscoveryFailure fuel → String
  | .cycle cursor => "cycle(" ++ cursorId cursor ++ ")"
  | .traversalLimit => "traversalLimit"
  | .invalidRanks => "invalidRanks"
  | .missingRoot => "missingRoot"

private def weightedFailureName {input : CertifiedLocalizedCIPInput} {fuel : Nat} :
    DiscoveryFailure (input.LocalizedRerootCursor fuel) → String
  | .cycle cursor => "cycle(" ++ cursorId cursor ++ ")"
  | .traversalLimit => "traversalLimit"
  | .invalidRanks => "invalidRanks"
  | .missingRoot => "missingRoot"

/-! ## Test 1: the generic weighted demand constructor -/

inductive TestNode where
  | a
  | b
  | c
  | emptyOnly
  deriving DecidableEq, Repr

/-- `a -> b -> c` by children; `a` also requests `c`, and the empty request `[]`.  `emptyOnly`
has no children and exactly one empty request, so its rank can only be `2`. -/
def testDag : Graph TestNode where
  children := fun
    | .a => [.b]
    | .b => [.c]
    | .c => []
    | .emptyOnly => []
  requests := fun
    | .a => [[], [.c]]
    | .b => []
    | .c => []
    | .emptyOnly => [[]]

/-- A genuine child cycle `a -> b -> a`. -/
def testChildCycle : Graph TestNode where
  children := fun
    | .a => [.b]
    | .b => [.a]
    | .c => []
    | .emptyOnly => []
  requests := fun _ => []

/-- A genuine request cycle `a -> b -> a` with no child edges. -/
def testRequestCycle : Graph TestNode where
  children := fun _ => []
  requests := fun
    | .a => [[.b]]
    | .b => [[.a]]
    | .c => []
    | .emptyOnly => []

private def testDagPlan? : Option (Plan testDag [TestNode.a, TestNode.emptyOnly]) :=
  match prepare testDag 64 [TestNode.a, TestNode.emptyOnly] with
  | .ok plan => some plan
  | .error _ => none

private def testChildCycleRejected : Bool :=
  match prepare testChildCycle 64 [TestNode.a] with
  | .error (.cycle _) => true
  | _ => false

private def testRequestCycleRejected : Bool :=
  match prepare testRequestCycle 64 [TestNode.a] with
  | .error (.cycle _) => true
  | _ => false



theorem preparedPlan_acyclic {α : Type} [DecidableEq α] {g : Graph α} {roots : List α}
    {budget : Nat} {plan : Plan g roots} (_computed : prepare g budget roots = .ok plan) :
    Acyclic g roots :=
  plan.acyclic

private def runTest1 : IO Unit := do
  let start ← IO.monoMsNow
  let some plan := testDagPlan?
    | throw (IO.userError "test1: generic acyclic prepare failed")
  checkTest "test1 generic acyclic prepare succeeds" true
  checkTest "test1 child edge consumes +1 (rank b = 2)"
    (plan.ranks.height TestNode.b == 2)
  checkTest "test1 child edge consumes +1 (rank c = 1)"
    (plan.ranks.height TestNode.c == 1)
  checkTest "test1 request edge consumes +2 (rank a = 3)"
    (plan.ranks.height TestNode.a == 3)
  checkTest "test1 empty request still consumes +2 (rank emptyOnly = 2)"
    (plan.ranks.height TestNode.emptyOnly == 2)
  checkTest "test1 computed bound is max root rank + 1 (4)" (plan.bound == 4)
  let table := plan.ranks.vertices.map fun cursor => (cursor, plan.ranks.height cursor)
  checkTest "test1 independent generic checker accepts the exported table"
    ((check? testDag table).isSome)
  let decreases := plan.ranks.vertices.all fun parent =>
    (successors testDag parent).all fun child =>
      decide (child ∈ plan.ranks.vertices) &&
        decide (plan.ranks.height child < plan.ranks.height parent)
  checkTest "test1 every certificate edge strictly decreases (acyclic witness)" decreases
  checkTest "test1 child cycle is rejected with an actual cycle" testChildCycleRejected
  checkTest "test1 request cycle is rejected with an actual cycle" testRequestCycleRejected
  let finish ← IO.monoMsNow
  IO.println s!"TIMING test1 generic weighted demand: {finish - start}ms"

/-! ## Test 2: the admitted SO3-like source -/

/-- Sulfur trioxide topology as an explicit semantic source: four atoms `[S, O, O, O]` and
three S=O double bonds.  Coordinates are intentionally absent; this probe inspects only demand
topology and bounded frame stability. -/
def so3Source : AuthoritativeChemicalInput :=
  let sulfur : PeriodicElement := ⟨16, by decide, by decide⟩
  let oxygen : PeriodicElement := ⟨8, by decide, by decide⟩
  let bond (a b order : Nat) : SemanticInteraction :=
    { participants := [a, b], kind := .covalent order }
  { molecule :=
      { atoms := [sulfur, oxygen, oxygen, oxygen].map fun element => { element := element }
        interactions := [bond 0 1 2, bond 0 2 2, bond 0 3 2] } }

/-! ### Frame-field comparison

`LocalizedRerootRecursiveRule3SpatialKey` has no exported `DecidableEq` instance, so the
complete optional frame is compared field by field, exactly as the existing frame probes do. -/

private def keySame {input : CertifiedLocalizedCIPInput}
    (a b : input.LocalizedRerootRecursiveRule3SpatialKey) : Bool :=
  decide (a.constitutional.rule1a = b.constitutional.rule1a) &&
    decide (a.constitutional.rule1b = b.constitutional.rule1b) &&
      decide (a.constitutional.rule2 = b.constitutional.rule2) &&
        decide (a.constitutional.sourceNodes = b.constitutional.sourceNodes) &&
          decide (a.constitutional.complete = b.constitutional.complete) &&
            decide (a.observations = b.observations) && decide (a.rule3 = b.rule3)

private def keysSame {input : CertifiedLocalizedCIPInput}
    (a b : List input.LocalizedRerootRecursiveRule3SpatialKey) : Bool :=
  a.length == b.length && (a.zip b).all fun pair => keySame pair.1 pair.2

private def frameSame {input : CertifiedLocalizedCIPInput}
    (a b : input.LocalizedRule3CanonicalKeyFrame) : Bool :=
  keysSame a.rawKeys b.rawKeys && keysSame a.keys b.keys &&
    decide (a.coupled = b.coupled) && decide (a.excluded = b.excluded)

/-- Complete optional-frame equality: every stored field is compared, and `none`/`some`
mismatches are rejected. -/
private def fullOptionEq {input : CertifiedLocalizedCIPInput}
    (a b : Option input.LocalizedRule3CanonicalKeyFrame) : Bool :=
  match a, b with
  | none, none => true
  | some left, some right => frameSame left right
  | none, some _ => false
  | some _, none => false

private def runTest2 : IO Unit := do
  let start ← IO.monoMsNow
  match admitted : admitSource? so3Source with
  | none => throw (IO.userError "test2: SO3-like source admission failed")
  | some input =>
      checkTest "test2 SO3-like source admitted" true
      checkTest "test2 admitted atom count is 4" (input.molecule.atomCount == 4)
      let fuel := carrierFuel input
      checkTest "test2 carrier fuel is atomCount + 1 (5)" (fuel == 5)
      have sourceExact : input.certified.certified.input = so3Source :=
        TetraStereo.OneCenter.LocalizedReference.admitSource?_exact so3Source input admitted
      have atomCountEq : input.certified.certified.input.molecule.atomCount = 4 := by
        rw [sourceExact]
        decide
      have atom0Mem : 0 < input.certified.certified.input.molecule.atomCount := by
        rw [atomCountEq]
        decide
      let atom0 : input.certified.Atom := ⟨0, atom0Mem⟩
      let root : input.certified.LocalizedRerootCursor fuel :=
        { occurrence :=
            input.certified.localizedAtomRootOccurrenceExecutable fuel atom0 }
      let children := input.certified.executableLocalizedRerootChildren root
      checkTest "test2 atom0 root is the root occurrence of atom 0"
        (root.occurrence.1.root.val == 0 && root.previous?.isNone)
      IO.println s!"SO3 root {cursorId root}: executable children={children.length}"
      for child in children do
        IO.println s!"  child {cursorId child}; \
nodeCurrent={repr (child.occurrence.1.node.current?.map fun atom => atom.val)}; \
ordinaryPairReady={input.certified.ordinaryPairReady child.occurrence}; \
oddPairReady={input.certified.oddPairReady child.occurrence}"
      checkTest "test2 every root child records the atom0 occurrence as incoming cut"
        (children.all fun child => decide (child.previous? = some root.occurrence))
      let childAtoms := children.filterMap fun child =>
        child.occurrence.1.node.current?.map fun atom => atom.val
      checkTest "test2 all three distinct O atoms occur among the root's executable children"
        (decide (1 ∈ childAtoms) && decide (2 ∈ childAtoms) && decide (3 ∈ childAtoms))

      let oldResult := input.certified.prepareExtendedRule3DemandPlan [root]
      let newResult := input.certified.preparePreflightExtendedDemandPlan [root]
      match oldResult with
      | .ok _ =>
          throw (IO.userError
            "test2: old extended demand constructor unexpectedly accepted the atom0 root")
      | .error (.cycle repeated) =>
          checkTest "test2 old extended prepare rejects an actual conservative cycle" true
          let repeatedExtended :=
            input.certified.rule3ExtendedNodeCallbackRequests repeated.occurrence
          let repeatedPreflight :=
            input.certified.rule3PreflightExtendedNodeCallbackRequests repeated.occurrence
          IO.println s!"  old cycle repeated at {cursorId repeated}: \
extendedRequests={repeatedExtended.length}, \
preflightRequests={repeatedPreflight.length}, \
ordinaryPairReady={input.certified.ordinaryPairReady repeated.occurrence}, \
oddPairReady={input.certified.oddPairReady repeated.occurrence}"
      | .error other =>
          throw (IO.userError
            ("test2: old extended prepare failed without a cycle: " ++
              rule3FailureName other))

      match newResult with
      | .error failure =>
          throw (IO.userError
            ("test2: preflight-pruned prepare failed: " ++ weightedFailureName failure))
      | .ok plan =>
          checkTest "test2 preflight-pruned prepare succeeds on the same root" true
          checkTest "test2 preflight plan covers the atom0 root"
            (decide (root ∈ plan.ranks.vertices))
          IO.println s!"  preflight plan: vertices={plan.ranks.vertices.length}, \
bound={plan.bound}"
          let subsetOk := plan.ranks.vertices.all fun cursor =>
            (input.certified.rule3PreflightExtendedNodeCallbackRequests cursor.occurrence).all
              fun request =>
                decide (request ∈
                  input.certified.rule3ExtendedNodeCallbackRequests cursor.occurrence)
          checkTest "test2 every pruned request is an extended request (pointwise subset)"
            subsetOk
          let witnesses := plan.ranks.vertices.filter fun cursor =>
            (input.certified.rule3ExtendedNodeCallbackRequests cursor.occurrence).any
              fun request =>
                !(decide (request ∈
                  input.certified.rule3PreflightExtendedNodeCallbackRequests cursor.occurrence))
          checkTest "test2 an actual removed request is reachable in the pruned plan"
            (!witnesses.isEmpty)
          match witnesses with
          | [] => pure ()
          | cursor :: _ =>
              let extended :=
                input.certified.rule3ExtendedNodeCallbackRequests cursor.occurrence
              let preflight :=
                input.certified.rule3PreflightExtendedNodeCallbackRequests cursor.occurrence
              let removed := extended.filter fun request =>
                !(decide (request ∈ preflight))
              checkTest "test2 the witness cursor has a nonempty removed request"
                (removed.any fun request => !request.isEmpty)
              checkTest "test2 removed requests form a strict request subset at the witness"
                (preflight.all (fun request => decide (request ∈ extended)) &&
                  !removed.isEmpty)
              IO.println s!"  removed request witness at {cursorId cursor}: \
extendedRequests={extended.length}, preflightRequests={preflight.length}, \
removedRequests={removed.length}"
              for request in removed do
                IO.println s!"    removed request ({request.length} refs): \
{repr (request.map cursorId)}"

          let view : input.certified.LocalizedDependencyView root.occurrence :=
            fun _ _ => none
          let boundedFrame :=
            preflightExtendedDemandEvaluate plan root.occurrence view
          let sameViewFrame :=
            input.certified.buildLocalizedExtendedShortCircuitRule3FrameExec?
              root.occurrence view (plan.bound + 9) [root]
          checkTest "test2 bounded frame equals same-view frame at bound+9 on every field"
            (fullOptionEq (input := input.certified) boundedFrame sameViewFrame)
          IO.println s!"  frame at bound: some={boundedFrame.isSome}; \
at bound+9: some={sameViewFrame.isSome}"

          for child in children do
            let childView : input.certified.LocalizedDependencyView child.occurrence :=
              fun _ _ => none
            let ordinary := input.certified.ordinaryPairReady child.occurrence
            let odd := input.certified.oddPairReady child.occurrence
            let spatial := input.certified.localizedRule3ShortCircuitSpatialUnitWithExec?
              child.occurrence child.occurrence childView (fun _ => none)
            let guarded := input.certified.rule3PreflightShortCircuitSpatialUnitWithExec?
              child.occurrence child.occurrence childView (fun _ => none)
            checkTest s!"test2 O sibling {cursorId child} has bilateral preflight false"
              (ordinary == false && odd == false)
            checkTest s!"test2 O sibling {cursorId child} spatial result is none" spatial.isNone
            checkTest s!"test2 O sibling {cursorId child} guarded spatial result is none"
              guarded.isNone
  let finish ← IO.monoMsNow
  IO.println s!"TIMING test2 SO3-like preflight demand: {finish - start}ms"



private def runTest3 : IO Unit := do
  let start ← IO.monoMsNow
  let some linked := admitSource? LocalizedRule3DemandCoupledAxesProbe.source
    | throw (IO.userError "test3: linked odd-cumulene source admission failed")
  let bonds := (Families.canonicalDoubleBonds linked).filter fun bond =>
    (bond.val.1.val == 0 && bond.val.2.val == 1) ||
      (bond.val.1.val == 4 && bond.val.2.val == 5)
  checkTest "test3 linked odd source admits and has the two linked double-bond axes"
    (bonds.length == 2)
  let mut witnessFound := false
  let mut witnessCount := 0
  for bond in bonds do
    let occurrence :=
      linked.certified.localizedCanonicalDoubleBondFirstChildOccurrenceExec
        (carrierFuel linked) bond
    let cursor : linked.certified.LocalizedRerootCursor (carrierFuel linked) :=
      { occurrence := occurrence }
    let bondLabel := s!"({bond.val.1.val},{bond.val.2.val})"
    match linked.certified.prepareRule3DemandPlan [cursor] with
    | .error (.cycle repeated) =>
        IO.println s!"  old short cycle at bond {bondLabel}: {cursorId repeated}"
        match linked.certified.prepareExtendedRule3DemandPlan [cursor] with
        | .ok plan =>
            witnessFound := true
            witnessCount := witnessCount + 1
            checkTest s!"test3 bond {bondLabel} direct extended plan covers the root"
              (decide (cursor ∈ plan.ranks.vertices))
            IO.println s!"  witness bond {bondLabel}: old short=cycle, \
direct extended=ok, vertices={plan.ranks.vertices.length}, bound={plan.bound}"
        | .error failure =>
            IO.println s!"  bond {bondLabel}: old short=cycle, direct extended fails: \
{rule3FailureName failure}"
    | .ok _ =>
        IO.println s!"  bond {bondLabel}: old short plan unexpectedly succeeds"
    | .error failure =>
        IO.println s!"  bond {bondLabel}: old short fails without cycle: \
{rule3FailureName failure}"
  checkTest "test3 old short cycle vs direct extended plan witness exists" witnessFound
  checkTest "test3 both linked axes show the old short cycle / direct extended plan split"
    (witnessCount == bonds.length)
  IO.println s!"  witness count={witnessCount} of {bonds.length} double-bond roots"
  let finish ← IO.monoMsNow
  IO.println s!"TIMING test3 linked odd witness: {finish - start}ms"

/-! ## Entry point -/

def main : IO Unit := do
  runTest1
  runTest2
  runTest3

#eval main

end TetraStereo.Examples.LocalizedPreflightDemandProbe
