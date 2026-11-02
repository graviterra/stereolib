import TetraStereo.OneCenter.LocalizedUniversalDescriptorEvaluation
import TetraStereo.OneCenter.LocalizedExtendedShortCircuitPipeline

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedUniversalDescriptorProbe

open TetraStereo.OneCenter















































/-! ## Small IO assertion helpers -/

private def checkTest (counter : IO.Ref Nat) (name : String) (condition : Bool) : IO Unit := do
  counter.modify (· + 1)
  if condition then
    IO.println ("ok: " ++ name)
  else
    throw (IO.userError ("failed: " ++ name))

private def note (message : String) : IO Unit :=
  IO.println message

/-! ## The five-atom positive halomethane fixture

Copied from `TetraStereo.Examples.LocalizedPreparedReferenceProbe.halomethaneSource`
(`C, F, Cl, Br, I` at atom indices `0..4`, tetrahedral coordinates).  The expected production
descriptor for the final occurrence of the unique centre (carbon, atom `0`) is `R`; see
`TetraStereo.Examples.AuthoritativeLocalizedCIPAnalysis`. -/

private def element (atomicNumber : ℕ) (positive : 0 < atomicNumber)
    (bounded : atomicNumber ≤ 118) : PeriodicElement :=
  { atomicNumber := atomicNumber, positive := positive, atMost118 := bounded }

private def carbon : PeriodicElement := element 6 (by decide) (by decide)
private def fluorine : PeriodicElement := element 9 (by decide) (by decide)
private def chlorine : PeriodicElement := element 17 (by decide) (by decide)
private def bromine : PeriodicElement := element 35 (by decide) (by decide)
private def iodine : PeriodicElement := element 53 (by decide) (by decide)

private def atom (element : PeriodicElement) : SemanticAtom :=
  { element := element }

private def bond (left right order : Nat) : SemanticInteraction :=
  { participants := [left, right], kind := .covalent order }

/-- Five-atom bromochlorofluoroiodomethane with exact rational tetrahedral coordinates. -/
def halomethaneSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, fluorine, chlorine, bromine, iodine].map atom
        interactions := [bond 0 1 1, bond 0 2 1, bond 0 3 1, bond 0 4 1] }
    spatial? := some { positions :=
      [{ x := 0, y := 0, z := 0 }, { x := -1, y := -1, z := 1 },
       { x := -1, y := 1, z := -1 }, { x := 1, y := -1, z := -1 },
       { x := 1, y := 1, z := 1 }] } }

/-! ## The materialized outcome and `universalDescriptor?` -/

/-- The second component of the materialized outcome is `universalDescriptor?` by definition.
This lets the probe run the preparation **once** while still reporting the value of
`universalDescriptor?` itself, with no repeated preparation and no extra hypothesis. -/
private theorem universalDescriptor?_eq_outcome_snd
    (input : LocalizedExtendedShortCircuit.Input) {carrierFuel : Nat}
    (target : input.certified.LocalizedCIPOccurrence carrierFuel)
    (view : input.certified.LocalizedDependencyView target) :
    input.certified.universalDescriptor? target view =
      (input.certified.universalDescriptorOutcome target view).2 :=
  rfl

/-! ## The one-target probe -/

private def runProbe : IO Unit := do
  let start ← IO.monoMsNow
  let counter ← IO.mkRef (0 : Nat)
  note "START universal-descriptor-probe positive-halomethane"

  -- Acceptance through the authoritative chemical input path.
  let some input := LocalizedExtendedShortCircuit.admitSource? halomethaneSource
    | throw (IO.userError "failed: halomethane acceptance returned none")
  let acceptedAt ← IO.monoMsNow
  checkTest counter "acceptance preserves the explicit spatial configuration"
    (decide (input.certified.certified.input.spatial? = halomethaneSource.spatial?))
  checkTest counter "acceptance preserves the fixture molecule"
    (decide (input.certified.certified.input.molecule = halomethaneSource.molecule))
  let fuel := LocalizedExtendedShortCircuit.carrierFuel input
  note s!"ACCEPT: atoms={input.certified.certified.input.molecule.atomCount}, \
carrierFuel={fuel}, {acceptedAt - start}ms"

  -- One detected centre; the fixture is known to have exactly atom 0.
  let centers := input.certified.canonicalTetrahedralCenters
  checkTest counter "exactly one canonical tetrahedral centre is detected" (centers.length == 1)
  let center ← match centers with
    | [center] => pure center
    | _ => throw (IO.userError "failed: expected exactly one canonical tetrahedral centre")
  checkTest counter "the detected centre is atom 0 (carbon)" (center.val.val == 0)
  let target := input.certified.localizedFinalOccurrenceExecutable fuel center
  let view : input.certified.LocalizedDependencyView target := fun _ _ => none

  -- Centre behaviour.
  checkTest counter "the final-centre occurrence stores its descriptor centre"
    (match input.certified.localizedOccurrenceDescriptorCenter? target with
     | some stored => decide (stored = center)
     | none => false)

  -- Base behaviour.
  let base? := input.certified.localizedNoDoubleFourLigandFrameExec? target
  checkTest counter "the final-centre occurrence has a four-ligand base" base?.isSome
  let base ← match base? with
    | some base => pure base
    | none => throw (IO.userError "failed: missing four-ligand base at the final centre")
  checkTest counter "the four-ligand base has exactly four cursors" (base.cursors.length == 4)
  let basedAt ← IO.monoMsNow
  note s!"BASE: cursors={base.cursors.length}, {basedAt - acceptedAt}ms"

  -- The universal outcome, materialized exactly once.  `universal` is definitionally
  -- `universalDescriptor?` by `universalDescriptor?_eq_outcome_snd`.
  let outcome := input.certified.universalDescriptorOutcome target view
  let bound := outcome.1
  let universal := outcome.2
  let universalDone ← IO.monoMsNow
  note s!"UNIVERSAL: bound={bound}, descriptor={repr universal}, {universalDone - basedAt}ms"
  checkTest counter "universalDescriptor? is some (.chiral .R)"
    (decide (universal = some (.chiral .R)))

  -- Equality with the parameterized pipeline at the computed bound and one step above it.
  let atBound := input.certified.descriptorAt? target view bound
  let atBoundDone ← IO.monoMsNow
  let aboveBound := input.certified.descriptorAt? target view (bound + 1)
  let aboveDone ← IO.monoMsNow
  note s!"DESCRIPTOR-AT: bound={repr atBound} ({atBoundDone - universalDone}ms), \
bound+1={repr aboveBound} ({aboveDone - atBoundDone}ms)"
  checkTest counter "descriptorAt? at the computed bound equals the universal descriptor"
    (decide (atBound = universal))
  checkTest counter "descriptorAt? at the computed bound is some (.chiral .R)"
    (decide (atBound = some (.chiral .R)))
  checkTest counter "descriptorAt? at bound + 1 equals the universal descriptor"
    (decide (aboveBound = universal))
  checkTest counter "descriptorAt? at bound + 1 is some (.chiral .R)"
    (decide (aboveBound = some (.chiral .R)))

  -- Production positive preservation on the same target and empty view.
  let production :=
    input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view
  let productionDone ← IO.monoMsNow
  note s!"PRODUCTION: descriptor={repr production}, {productionDone - aboveDone}ms"
  checkTest counter "the production descriptor is some (.chiral .R)"
    (decide (production = some (.chiral .R)))
  checkTest counter "the production positive result is preserved by the universal descriptor"
    (decide (production = universal))

  -- No-label behaviour: a terminal ligand root has no descriptor centre.
  let ligandAtom := input.certified.canonicalLigandAtom center 0
  let ligandTarget := input.certified.localizedAtomRootOccurrenceExecutable fuel ligandAtom
  let ligandView : input.certified.LocalizedDependencyView ligandTarget := fun _ _ => none
  checkTest counter "the first canonical ligand root has no descriptor centre"
    (input.certified.localizedOccurrenceDescriptorCenter? ligandTarget).isNone
  let ligandOutcome := input.certified.universalDescriptorOutcome ligandTarget ligandView
  note s!"NO-CENTRE: bound={ligandOutcome.1}, descriptor={repr ligandOutcome.2}"
  checkTest counter "the no-centre universal outcome carries the zero bound" (ligandOutcome.1 == 0)
  checkTest counter "the no-centre universal outcome has no label"
    (decide (ligandOutcome.2 = none))
  checkTest counter "descriptorAt? refuses the no-centre root at the declared bound"
    (decide (input.certified.descriptorAt? ligandTarget ligandView ligandOutcome.1 = none))

  let assertions ← counter.get
  let finish ← IO.monoMsNow
  note s!"TIMING positive-halomethane: total={finish - start}ms \
(accept={acceptedAt - start}ms, base={basedAt - acceptedAt}ms, \
universal={universalDone - basedAt}ms, bounds={aboveDone - universalDone}ms, \
production={productionDone - aboveDone}ms)"
  note s!"SUMMARY: assertions={assertions}, bound={bound}, universal={repr universal}, \
atBound={repr atBound}, aboveBound={repr aboveBound}, production={repr production}, \
noCentreOutcome=({ligandOutcome.1}, {repr ligandOutcome.2})"
  note "DONE universal-descriptor-probe (final verified)"

#eval runProbe

end TetraStereo.Examples.LocalizedUniversalDescriptorProbe
