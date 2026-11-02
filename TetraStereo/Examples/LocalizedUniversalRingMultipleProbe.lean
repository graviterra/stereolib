import TetraStereo.OneCenter.LocalizedUniversalReferencePipeline
import TetraStereo.OneCenter.LocalizedUniversalCachedPipeline

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedUniversalRingMultipleProbe

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.LocalizedUniversalReference



































































/-! ## IO helpers -/

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

/-! ## Fixture data (copied with attribution; see the module docstring) -/

private def carbon : PeriodicElement := ⟨6, by decide, by decide⟩
private def hydrogen : PeriodicElement := ⟨1, by decide, by decide⟩
private def fluorine : PeriodicElement := ⟨9, by decide, by decide⟩
private def chlorine : PeriodicElement := ⟨17, by decide, by decide⟩
private def bromine : PeriodicElement := ⟨35, by decide, by decide⟩

private def bond (left right order : Nat) : SemanticInteraction :=
  { participants := [left, right], kind := .covalent order }

/-- Coordinates of the ring fixture, copied from
`LocalizedOmissionReadinessProbe.spatial`.  Atoms `1,2,3,6` are the four ligands of atom `0`. -/
private def ringSpatial (branch : Nat) : SpatialConfiguration :=
  { positions := (List.range 10).map fun i =>
      if i = 0 then { x := 0, y := 0, z := 0 }
      else if i = 1 then { x := -1, y := 1, z := -1 }
      else if i = 2 then { x := 1, y := -1, z := -1 }
      else if i = 3 then { x := 1, y := 1, z := 1 }
      else if i = branch then { x := -1, y := -1, z := 1 }
      else { x := (i + 2 : Nat), y := ((i + 2 : Nat) : Rat) ^ 2, z := ((i + 2 : Nat) : Rat) ^ 3 } }

/-- Three-membered ordinary monocycle `C4=C5-C6-C4` attached to the strict tetrahedral
centre at atom `0`.  Copied from `LocalizedOmissionReadinessProbe.ringSource`. -/
def ringSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, fluorine, chlorine, bromine, carbon, carbon, carbon,
          hydrogen, hydrogen, hydrogen].map fun element => { element }
        interactions := [bond 0 1 1, bond 0 2 1, bond 0 3 1, bond 0 6 1,
          bond 4 5 2, bond 5 6 1, bond 6 4 1, bond 4 7 1, bond 5 8 1, bond 6 9 1] }
    spatial? := some (ringSpatial 6) }

/-- Planar diene `C4=C5-C6=C7` attached to the strict tetrahedral centre at atom `0`.
Copied from `LocalizedDieneReferenceProbe.dieneSource`. -/
def dieneSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, fluorine, chlorine, bromine, carbon, carbon, carbon, carbon,
          fluorine, hydrogen, hydrogen, hydrogen, hydrogen].map (fun e => { element := e })
        interactions := [bond 0 1 1, bond 0 2 1, bond 0 3 1, bond 0 4 1,
          bond 4 5 2, bond 5 6 1, bond 6 7 2, bond 7 8 1,
          bond 4 9 1, bond 5 10 1, bond 6 11 1, bond 7 12 1] }
    spatial? := some { positions :=
      [{ x := 0, y := 1, z := 0 }, { x := 0, y := 2, z := 0 },
       { x := 0, y := 1, z := 1 }, { x := -1, y := 0, z := -1 },
       { x := 1, y := 0, z := 0 }, { x := 2, y := 0, z := 0 },
       { x := 3, y := 1, z := 0 }, { x := 4, y := 1, z := 0 },
       { x := 5, y := 2, z := 0 }, { x := 1, y := -1, z := 0 },
       { x := 2, y := -1, z := 0 }, { x := 3, y := 2, z := 0 },
       { x := 4, y := 0, z := 0 }] } }

/-- Odd cumulene `C4=C5=C6=C7` attached to the strict tetrahedral centre at atom `0`, with
`spatial? := none`.  Copied from the local `oddSource` of
`LocalizedPreparedReferenceProbe` (that module is not imported). -/
def oddSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, fluorine, chlorine, bromine, carbon, carbon, carbon, carbon,
          hydrogen, hydrogen, hydrogen].map fun element => { element }
        interactions := [bond 0 1 1, bond 0 2 1, bond 0 3 1, bond 0 4 1,
          bond 4 5 2, bond 5 6 2, bond 6 7 2,
          bond 4 8 1, bond 7 9 1, bond 7 10 1] }
    spatial? := none }

/-! ## The materialized outcome is the universal descriptor

The probe calls `universalDescriptorOutcome` once and reports its second component.  The
following kernel-checked `rfl` records that this component *is* `universalDescriptor?`, so the
probe does not run a second preparation to print the universal value. -/

private theorem universalDescriptor?_eq_outcome_snd
    (input : Input) {carrierFuel : Nat}
    (target : input.certified.LocalizedCIPOccurrence carrierFuel)
    (view : input.certified.LocalizedDependencyView target) :
    input.certified.universalDescriptor? target view =
      (input.certified.universalDescriptorOutcome target view).2 :=
  rfl

/-! ## Actual Rule-3 axis/ring route counts -/

/-- One count per `LocalizedRule3CumulatedAxisEntry` constructor observed on the executable
occurrence carrier.  `ringClosure` is the cyclic-ring branch; `internal` is the traversal of a
multiple-bond axis away from a terminal end. -/
private structure AxisRoutes where
  terminalStart : Nat
  internal : Nat
  ringClosure : Nat
  branched : Nat

private def AxisRoutes.zero : AxisRoutes :=
  { terminalStart := 0, internal := 0, ringClosure := 0, branched := 0 }

private def axisRoutes (input : Input) (fuel : Nat) : AxisRoutes :=
  (input.certified.localizedOccurrenceCarrier fuel).foldl
    (fun routes occurrence =>
      match input.certified.localizedRule3CumulatedAxisEntryExec? occurrence with
      | some (.terminalStart _) => { routes with terminalStart := routes.terminalStart + 1 }
      | some (.internal _ _) => { routes with internal := routes.internal + 1 }
      | some (.ringClosure _ _) => { routes with ringClosure := routes.ringClosure + 1 }
      | some (.branched _ _ _ _) => { routes with branched := routes.branched + 1 }
      | none => routes)
    AxisRoutes.zero

/-! ## Shared target helpers -/

private def admitOrFail (name : String) (source : AuthoritativeChemicalInput) : IO Input := do
  match admitSource? source with
  | some input => pure input
  | none => throw (IO.userError (name ++ ": admission returned none"))

private def centerAt? (input : Input) (atom : Nat) :
    Option input.certified.TetrahedralCenter :=
  input.certified.canonicalTetrahedralCenters.find? fun center =>
    center.val.val == atom

private def centerIndices (input : Input) : List Nat :=
  input.certified.canonicalTetrahedralCenters.map fun center => center.val.val

/-- Run the universal outcome and the parameterized descriptor at the computed bound for one
final centre occurrence.  Returns the computed bound and the materialized universal outcome. -/
private def probeFinalCentre (name : String) (input : Input) (centerAtom : Nat)
    (expected : LocalizedAuxiliaryLabel) (checkAtBound : Bool) :
    IO (Nat × Option LocalizedAuxiliaryLabel) := do
  let start ← IO.monoMsNow
  let fuel := carrierFuel input
  let some center := centerAt? input centerAtom
    | throw (IO.userError (name ++ ": no canonical tetrahedral centre at atom " ++
        toString centerAtom))
  let target := input.certified.localizedFinalOccurrenceExecutable fuel center
  let view : input.certified.LocalizedDependencyView target := fun _ _ => none
  checkTest s!"{name} final occurrence stores its descriptor centre"
    (match input.certified.localizedOccurrenceDescriptorCenter? target with
     | some stored => decide (stored = center)
     | none => false)
  let base? := input.certified.localizedNoDoubleFourLigandFrameExec? target
  checkTest s!"{name} final occurrence has a four-ligand base" base?.isSome
  let basedAt ← IO.monoMsNow
  let outcome := input.certified.universalDescriptorOutcome target view
  let outcomeAt ← IO.monoMsNow
  note s!"UNIVERSAL {name}: atom={centerAtom}, bound={outcome.1}, \
descriptor={repr outcome.2}, {outcomeAt - basedAt}ms"
  checkTest s!"{name} the universal outcome is a positive computed bound"
    (decide (0 < outcome.1))
  checkTest s!"{name} the universal descriptor equals the fixture expectation"
    (decide (outcome.2 = some expected))
  if checkAtBound then
    let atBound := input.certified.descriptorAt? target view outcome.1
    let atBoundAt ← IO.monoMsNow
    note s!"DESCRIPTOR-AT {name}: bound={outcome.1}, result={repr atBound}, \
{atBoundAt - outcomeAt}ms"
    checkTest s!"{name} descriptorAt? at the computed bound equals the universal descriptor"
      (decide (atBound = outcome.2))
    checkTest s!"{name} descriptorAt? at the computed bound equals the fixture expectation"
      (decide (atBound = some expected))
  let finish ← IO.monoMsNow
  note s!"TARGET-TIMING {name}: base={basedAt - start}ms, universal={outcomeAt - basedAt}ms, \
total={finish - start}ms"
  pure (outcome.1, outcome.2)

/-! ## Direct diene target

No carrier enumeration and no all-occurrence production. -/

private def runDieneTargetOnly : IO Unit := do
  let name := "diene-target"
  note s!"START {name}"
  let start ← IO.monoMsNow
  let input ← admitOrFail name dieneSource
  let admittedAt ← IO.monoMsNow
  note s!"ADMIT {name}: atoms={input.certified.certified.input.molecule.atomCount}, \
centres={repr (centerIndices input)}, {admittedAt - start}ms"
  let (bound, universal) ← probeFinalCentre name input 0 (.chiral .R) true
  let finish ← IO.monoMsNow
  note s!"FIXTURE {name}: bound={bound}, descriptor={repr universal}, total={finish - start}ms"

/-! ## Diagnostic: direct ring target only (no carrier enumeration, no production) -/

private def runRingTargetOnly : IO Unit := do
  let name := "ring-target"
  note s!"START {name}"
  let start ← IO.monoMsNow
  let input ← admitOrFail name ringSource
  let admittedAt ← IO.monoMsNow
  note s!"ADMIT {name}: atoms={input.certified.certified.input.molecule.atomCount}, \
centres={repr (centerIndices input)}, {admittedAt - start}ms"
  let (bound, universal) ← probeFinalCentre name input 0 (.chiral .R) true
  let finish ← IO.monoMsNow
  note s!"FIXTURE {name}: bound={bound}, descriptor={repr universal}, total={finish - start}ms"

/-! ## Odd cumulene fixture (no spatial configuration) -/

private def runOdd : IO Unit := do
  let name := "odd-cumulene"
  note s!"START {name}"
  let start ← IO.monoMsNow
  let input ← admitOrFail name oddSource
  let fuel := carrierFuel input
  let admittedAt ← IO.monoMsNow
  note s!"ADMIT {name}: atoms={input.certified.certified.input.molecule.atomCount}, \
carrierFuel={fuel}, carriers={(input.certified.localizedOccurrenceCarrier fuel).length}, \
centres={repr (centerIndices input)}, {admittedAt - start}ms"
  checkTest s!"{name} admits the odd cumulene fixture without coordinates"
    (decide (oddSource.spatial? = none))
  checkTest s!"{name} atom 0 is a canonical tetrahedral centre" (centerAt? input 0).isSome
  let routes := axisRoutes input fuel
  note s!"ROUTES {name}: terminalStart={routes.terminalStart}, internal={routes.internal}, \
ringClosure={routes.ringClosure}, branched={routes.branched}"
  checkTest s!"{name} exercises the odd multiple-bond axis route"
    (decide (0 < routes.internal))
  checkTest s!"{name} exercises a terminal multiple-bond axis route"
    (decide (0 < routes.terminalStart))
  -- Materialize the outcome once.  The missing coordinates must produce an operational
  -- refusal at the computed bound; this is not a chemical-impossibility conclusion.
  let some center := centerAt? input 0
    | throw (IO.userError (name ++ ": no canonical centre at atom 0"))
  let target := input.certified.localizedFinalOccurrenceExecutable fuel center
  let view : input.certified.LocalizedDependencyView target := fun _ _ => none
  let outcome := input.certified.universalDescriptorOutcome target view
  note s!"UNIVERSAL {name}: atom=0, bound={outcome.1}, descriptor={repr outcome.2}"
  checkTest s!"{name} the universal outcome refuses the missing spatial geometry"
    (decide (outcome.2 = none))
  let atBound := input.certified.descriptorAt? target view outcome.1
  note s!"DESCRIPTOR-AT {name}: bound={outcome.1}, result={repr atBound}"
  checkTest s!"{name} descriptorAt? at the computed bound equals the universal refusal"
    (decide (atBound = outcome.2))
  let finish ← IO.monoMsNow
  note s!"FIXTURE {name}: bound={outcome.1}, descriptor={repr outcome.2}, \
internal={routes.internal}, terminalStart={routes.terminalStart}, total={finish - start}ms"












private def runCachedOdd : IO Unit := do
  let name := "odd-cached"
  note s!"START {name}"
  let start ← IO.monoMsNow
  let input ← admitOrFail name oddSource
  let cache := LocalizedUniversalReference.Cached.buildRuntimeCache input
  let builtAt ← IO.monoMsNow
  let carrier := cache.carrier
  let nodes := LocalizedUniversalReference.Cached.nodesUsingCache input cache
  let producedAt ← IO.monoMsNow
  let facts : LocalizedUniversalReference.Facts input :=
    nodes.map fun node => (node.target, node.outcome)
  note s!"CACHED {name}: carrier={carrier.length}, nodes={nodes.length}, facts={facts.length}, \
build={builtAt - start}ms, produce={producedAt - builtAt}ms"
  checkTest s!"{name} the production covers the materialized carrier"
    (decide (facts.length = carrier.length))
  checkTest s!"{name} the production targets are duplicate free"
    ((facts.map Prod.fst).Nodup)
  let checked? := LocalizedUniversalReference.Cached.checkUsingCache? input cache nodes
  let checkedAt ← IO.monoMsNow
  checkTest s!"{name} the cached checker accepts the materialized nodes"
    (decide (checked? = some facts))
  let report := LocalizedUniversalReference.report input facts
  note s!"CACHED-REPORT {name}: report={repr report}, check={checkedAt - producedAt}ms, \
total={checkedAt - start}ms"
  checkTest s!"{name} the cached report is the grounded missing-geometry refusal"
    (decide (report = [(0, none)]))
  let finish ← IO.monoMsNow
  note s!"FIXTURE {name}: carrier={carrier.length}, nodes={nodes.length}, \
report={repr report}, total={finish - start}ms"

/-! ## Entry point -/

def main : IO Unit := do
  let start ← IO.monoMsNow
  note "== universal Rule-3/descriptor probe: odd cumulene + diene + cyclic ring direct targets =="
  runOdd
  runDieneTargetOnly
  runRingTargetOnly
  let finish ← IO.monoMsNow
  note s!"DONE universal-ring-multiple-probe: total={finish - start}ms"

#eval main

end TetraStereo.Examples.LocalizedUniversalRingMultipleProbe
