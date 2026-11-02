import TetraStereo.OneCenter.LocalizedUniversalReferencePipeline
import TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedUniversalInteractingDeepProbe

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures

/-!
# Scoped runtime probe: universal reference pipeline on interacting centres and the deep fixture

This module is a *scoped runtime regression probe* for the exported API of
`TetraStereo.OneCenter.LocalizedUniversalReference` on the two existing SMILES fixtures of
`TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures`:

* `interactingSmiles`/`interactingSpatial` — two constitutionally identical `CH(F)(Cl)` branches
  around a central carbon (the interacting-centres fixture);
* `deepSmiles`/`deepSpatial` — an acyclic centre whose branches are constitutionally distinct only
  far from the centre (the deep fixture).

Both are admitted through the actual executable intake `admitSmilesSpatial?` of
`TetraStereo.OneCenter.LocalizedNoDoubleReference`, and the resulting certified localized input is
fed unchanged to the universal reference pipeline.

## Executed scope

The full ranked production `referenceNodes` (and therefore checker acceptance of that produced
list) is **not executed** here.  The measured cost of one `universalDescriptor?` call on the
interacting fixture's descriptor-bearing occurrences is about 2.4 s in the interpreter, and the
carrier contains 33 such occurrences, so a single production plus a checker replay is far outside
the 30 s runtime budget; on the deep fixture a full-fuel descriptor scan was stopped after more
than eight minutes.  This module therefore reports *local-view coverage only*:

* admission counts and the canonical centre indices;
* for the interacting fixture, one direct `universalDescriptor?` call at each canonical centre's
  final occurrence, evaluated at an explicit empty supplied dependency view.  The three observed
  labels are asserted against explicit expected labels.  These are local-view outcomes, **not** an
  agreement theorem between the universal reference state and any other pipeline state;
* the actual ranked dependency structure of the carrier (dependency edge count, a concrete
  first-dependency path, and reference indices that resolve exactly to the ranked dependency list).
  For the interacting fixture this uses the full carrier (121 occurrences, computed cheaply).  For
  the deep fixture the full carrier is not enumerated; the same dependency observations are made
  at the small expansion bound `2` and reported as bounded-fuel evidence only.

The universal kernel claims remain the existing theorems of `LocalizedUniversalReferencePipeline`
(`reference_check`, `reference_targets`, `reference_state_unique`, `reference_accepted`,
`checked_eq_reference`, `evaluate_state`, `evaluation_positive_sound`).  This probe does not
re-prove them and does not assert their preconditions on unexecuted objects.

## Expected labels

The interacting expected labels `[(1, none), (2, R), (7, R)]` combine two independent sources:

* `(1, none)` is the explicit assertion of
  `Examples/LocalizedNoDoubleReferenceRegression`: the central candidate receives no descriptor
  (`labelAt interactingRun 1 = some none`);
* `(2, R)` and `(7, R)` are the runtime labels observed from the universal pipeline on these exact
  fixture data.  They satisfy the no-double regression's independent expectation that both branch
  candidates receive a descriptor (`assignedAt` is `some`).  They are pinned here as explicit
  regression values so any change in the computed label fails elaboration.

No deep-fixture descriptor label is asserted, because no deep-fixture descriptor call is executed.
-/

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

/-! ## Fixture admission and the pipeline adapter -/

/-- The universal reference pipeline consumes the certified localized input; the no-double intake
adds a source-record restriction proof but does not alter that certificate. -/
def asPipelineInput (input : LocalizedNoDoubleReference.Input) :
    LocalizedUniversalReference.Input :=
  { certified := input.certified }

/-- Admit one imported fixture through the actual `admitSmilesSpatial?` intake. -/
def admitFixture (fixture : Fixture) : IO LocalizedNoDoubleReference.Input :=
  match LocalizedNoDoubleReference.admitSmilesSpatial? fixture.smiles fixture.spatial with
  | Except.error message =>
      throw (IO.userError (fixture.name ++ ": parse/normalization error: " ++ message))
  | Except.ok none =>
      throw (IO.userError (fixture.name ++ ": rejected by the checked intake"))
  | Except.ok (some input) => pure input

/-- Spell one auxiliary label, preserving `none` as an explicit outcome. -/
def labelText : Option LocalizedAuxiliaryLabel → String
  | none => "none"
  | some (.chiral .R) => "R"
  | some (.chiral .S) => "S"
  | some (.pseudoasymmetric .r) => "r"
  | some (.pseudoasymmetric .s) => "s"

/-! ## Actual ranked dependency structure of a carrier at one expansion bound -/

/-- The ranked dependency list of one occurrence, as used by the certificate producer. -/
def dependenciesAt (input : LocalizedUniversalReference.Input) (fuel : Nat)
    (target : input.certified.LocalizedCIPOccurrence fuel) :
    List (input.certified.LocalizedCIPOccurrence fuel) :=
  input.certified.localizedDependencyList fuel target

/-- Number of carrier occurrences that carry at least one ranked dependency. -/
def dependencyEdgeCount (input : LocalizedUniversalReference.Input) (fuel : Nat)
    (carrier : List (input.certified.LocalizedCIPOccurrence fuel)) : Nat :=
  (carrier.filter fun target => !(dependenciesAt input fuel target).isEmpty).length

/-- Length of a concrete dependency path, obtained by starting at the first carrier occurrence that
has a dependency and following the first ranked dependency until none remains.  Each strict
dependency increases the address length, so the walk is bounded by `fuel + 2` steps. -/
def dependencyPathLength (input : LocalizedUniversalReference.Input) (fuel : Nat)
    (carrier : List (input.certified.LocalizedCIPOccurrence fuel)) : Option Nat :=
  match carrier.find? (fun target => !(dependenciesAt input fuel target).isEmpty) with
  | none => none
  | some start =>
      let rec go : Nat → input.certified.LocalizedCIPOccurrence fuel → Nat
        | 0, _ => 0
        | steps + 1, target =>
            match (dependenciesAt input fuel target).head? with
            | none => 0
            | some next => 1 + go steps next
      some (go (fuel + 2) start)

/-- A concrete reference witness: take the first carrier occurrence with dependencies, index each
dependency into the ranked order (viewed as an all-`none` supplied fact table), and check that the
indices are nonempty, duplicate free and resolve back to exactly the ranked dependency list. -/
def referenceWitness (input : LocalizedUniversalReference.Input) (fuel : Nat)
    (carrier : List (input.certified.LocalizedCIPOccurrence fuel)) :
    Option (Nat × Nat × Bool) :=
  match carrier.find? (fun target => !(dependenciesAt input fuel target).isEmpty) with
  | none => none
  | some target =>
      let order := input.certified.localizedCertificateOrder fuel
      let facts : List (TetraStereo.Certificate.Dependency.Fact
          (input.certified.LocalizedCIPOccurrence fuel) LocalizedAuxiliaryLabel) :=
        order.map fun occurrence => (occurrence, none)
      let references :=
        TetraStereo.Certificate.Dependency.producerReferences
          (input.certified.localizedCertificateDependencies fuel) facts target
      let resolved :=
        (TetraStereo.Certificate.Dependency.referenced facts references).map Prod.fst
      some (references.length, (dependenciesAt input fuel target).length,
        decide references.Nodup && decide (resolved = dependenciesAt input fuel target))

/-- One-line numeric summary of the dependency-structure observations. -/
structure DependencyStats where
  carrier : Nat
  order : Nat
  edges : Nat
  pathLength : Nat
  references : Nat
  dependencies : Nat
  elapsedMs : Nat

/-- Run the dependency-structure observations at one expansion bound.  This enumerates the carrier
(and the ranked order) at that bound only; it runs no descriptor. -/
def runDependencyStructure (name : String) (input : LocalizedUniversalReference.Input)
    (fuel : Nat) : IO DependencyStats := do
  let start ← IO.monoMsNow
  let carrier := input.certified.localizedOccurrenceCarrier fuel
  let carrierAt ← IO.monoMsNow
  checkTest s!"{name}: the carrier at bound {fuel} is nonempty" (decide (0 < carrier.length))
  let order := input.certified.localizedCertificateOrder fuel
  let orderAt ← IO.monoMsNow
  checkTest s!"{name}: the ranked order at bound {fuel} has the carrier length"
    (order.length == carrier.length)
  checkTest s!"{name}: the ranked order at bound {fuel} is duplicate free" (decide order.Nodup)
  checkTest s!"{name}: the ranked order at bound {fuel} covers every carrier occurrence"
    (carrier.all fun occurrence => decide (occurrence ∈ order))
  let edges := dependencyEdgeCount input fuel carrier
  let edgesAt ← IO.monoMsNow
  checkTest s!"{name}: the carrier at bound {fuel} has nonzero dependency edges"
    (decide (0 < edges))
  let pathLength ← match dependencyPathLength input fuel carrier with
    | none => throw (IO.userError (name ++ ": no occurrence with a ranked dependency"))
    | some pathLength =>
        checkTest s!"{name}: the concrete first-dependency path at bound {fuel} is nonempty"
          (decide (0 < pathLength))
        pure pathLength
  let witness ← match referenceWitness input fuel carrier with
    | none => throw (IO.userError (name ++ ": no reference witness target"))
    | some witness => pure witness
  let finish ← IO.monoMsNow
  checkTest s!"{name}: the reference witness at bound {fuel} is nonempty"
    (decide (0 < witness.1))
  checkTest s!"{name}: the reference witness at bound {fuel} covers every ranked dependency"
    (witness.1 == witness.2.1)
  checkTest s!"{name}: the reference witness at bound {fuel} resolves to the ranked dependencies"
    witness.2.2
  note s!"DEPENDENCY {name} bound {fuel}: carrier={carrier.length}, order={order.length}, \
edges={edges}, pathLength={pathLength}, references={witness.1}, \
dependencies={witness.2.1}, resolves={witness.2.2}, \
carrierTime={carrierAt - start}ms, orderTime={orderAt - carrierAt}ms, \
edgesTime={edgesAt - orderAt}ms, total={finish - start}ms"
  pure { carrier := carrier.length, order := order.length, edges, pathLength,
         references := witness.1, dependencies := witness.2.1, elapsedMs := finish - start }

/-! ## Interacting fixture: three direct local-view outcomes -/

/-- One direct universal descriptor outcome at a canonical centre's final occurrence, evaluated at
an explicit empty supplied dependency view.  This is a local-view observation: no ranked
production and no reference state is computed. -/
def directCenterLabel (input : LocalizedUniversalReference.Input) (fuel : Nat)
    (center : input.certified.TetrahedralCenter) :
    IO (Nat × Option LocalizedAuxiliaryLabel × Nat) := do
  let before ← IO.monoMsNow
  let target := input.certified.localizedFinalOccurrenceExecutable fuel center
  let view : input.certified.LocalizedDependencyView target := fun _ _ => none
  let outcome := input.certified.universalDescriptor? target view
  let text := labelText outcome
  let after ← IO.monoMsNow
  note s!"CENTER interacting {center.val.val}: {text} ({after - before}ms)"
  pure (center.val.val, outcome, after - before)

/-- The interacting fixture at full carrier budget: admission, the three canonical centres with
their direct local-view labels, and the actual ranked dependency structure.  Returns the observed
labels, the dependency statistics and the elapsed milliseconds. -/
def runInteracting :
    IO (List (Nat × Option LocalizedAuxiliaryLabel) × DependencyStats × Nat) := do
  let start ← IO.monoMsNow
  let admitted ← admitFixture interacting
  let input := asPipelineInput admitted
  let admittedAt ← IO.monoMsNow
  checkTest "interacting: admitted through admitSmilesSpatial?"
    (input.certified.certified.input.spatial?.isSome)
  checkTest "interacting: the hydrogen-expanded molecule has eleven atoms"
    (input.certified.certified.input.molecule.atomCount == 11)
  let fuel := LocalizedUniversalReference.carrierFuel input
  let centers := input.certified.canonicalTetrahedralCenters
  checkTest "interacting: the canonical centres are exactly atoms 1, 2 and 7"
    (decide (centers.map (fun center => center.val.val) = [1, 2, 7]))
  let mut observed : List (Nat × Option LocalizedAuxiliaryLabel) := []
  for center in centers do
    let (index, outcome, _) ← directCenterLabel input fuel center
    observed := observed ++ [(index, outcome)]
  let centersAt ← IO.monoMsNow
  let expected : List (Nat × Option LocalizedAuxiliaryLabel) :=
    [(1, none), (2, some (.chiral .R)), (7, some (.chiral .R))]
  checkTest "interacting: the final-centre labels equal the explicit expected labels"
    (decide (observed = expected))
  checkTest "interacting: the central centre 1 has no descriptor, as in the no-double regression"
    (decide (observed.find? (fun entry => entry.1 == 1) = some (1, none)))
  checkTest "interacting: branch centres 2 and 7 are assigned, as in the no-double regression"
    (decide ((observed.find? (fun entry => entry.1 == 2)).map (fun entry => entry.2.isSome)
        = some true) &&
      decide ((observed.find? (fun entry => entry.1 == 7)).map (fun entry => entry.2.isSome)
        = some true))
  note s!"OBSERVED interacting: {repr observed}"
  let stats ← runDependencyStructure "interacting" input fuel
  let finish ← IO.monoMsNow
  note s!"TIMING interacting: admission={admittedAt - start}ms, \
centres={centersAt - admittedAt}ms, total={finish - start}ms"
  note "SCOPE interacting: local-view centre outcomes and ranked dependency structure only; \
selected referenceNodes production and checker acceptance were not executed (33 descriptor-bearing \
occurrences at about 2.4s each, plus replay, exceed the 30s budget)."
  pure (observed, stats, finish - start)

/-! ## Deep fixture: admission and bounded-fuel dependency structure -/

/-- The deep fixture: admission only (the full-fuel descriptor scan was measured at more than eight
minutes and is not executed), plus the actual ranked dependency structure at the small expansion
bound 2.  Returns the dependency statistics and the elapsed milliseconds. -/
def runDeep : IO (DependencyStats × Nat) := do
  let start ← IO.monoMsNow
  let admitted ← admitFixture deep
  let input := asPipelineInput admitted
  let admittedAt ← IO.monoMsNow
  checkTest "deep: admitted through admitSmilesSpatial?"
    (input.certified.certified.input.spatial?.isSome)
  checkTest "deep: the hydrogen-expanded molecule has twenty-three atoms"
    (input.certified.certified.input.molecule.atomCount == 23)
  note s!"ADMITTED deep: atoms={input.certified.certified.input.molecule.atomCount}, \
{admittedAt - start}ms"
  let stats ← runDependencyStructure "deep" input 2
  let finish ← IO.monoMsNow
  note s!"TIMING deep: admission={admittedAt - start}ms, total={finish - start}ms"
  note "SCOPE deep: bounded-fuel (bound 2) dependency structure only; the full-fuel carrier and \
the deep final-centre descriptor were not executed, because the deep full-fuel scan exceeded the \
helper deadline."
  pure (stats, finish - start)

/-! ## Entry point -/

def main : IO Unit := do
  let start ← IO.monoMsNow
  note "== universal reference probe: interacting centres and deep fixture (scoped) =="
  let (labels, interactingStats, interactingMs) ← runInteracting
  let (deepStats, deepMs) ← runDeep
  let finish ← IO.monoMsNow
  note s!"SUMMARY interacting: labels={repr labels}, carrier={interactingStats.carrier}, \
order={interactingStats.order}, edges={interactingStats.edges}, \
pathLength={interactingStats.pathLength}, references={interactingStats.references}, \
dependencies={interactingStats.dependencies}, elapsed={interactingMs}ms"
  note s!"SUMMARY deep bound2: carrier={deepStats.carrier}, order={deepStats.order}, \
edges={deepStats.edges}, pathLength={deepStats.pathLength}, references={deepStats.references}, \
dependencies={deepStats.dependencies}, elapsed={deepMs}ms"
  note s!"SUMMARY total={finish - start}ms"
  IO.println "universal interacting/deep scoped probe complete"

#eval main

end TetraStereo.Examples.LocalizedUniversalInteractingDeepProbe
