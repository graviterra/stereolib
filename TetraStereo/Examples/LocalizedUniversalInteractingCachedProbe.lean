import TetraStereo.OneCenter.LocalizedUniversalCachedPipeline

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedUniversalInteractingCachedProbe

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-!
# Full cached universal reference pipeline on the interacting eleven-atom fixture

This module is a *runtime exercise* of the universal reference pipeline of
`TetraStereo.OneCenter.LocalizedUniversalReference` on the interacting-centres fixture, using the
one-shot materialization of `TetraStereo.OneCenter.LocalizedUniversalReference.Cached`.  It is not a
new correctness claim: the universal pipeline statements are the existing kernel-checked theorems
of `LocalizedUniversalReferencePipeline` and `LocalizedUniversalCachedPipeline`
(`reference_check`, `reference_targets`, `reference_state_unique`, `reference_accepted`,
`checked_eq_reference`, `nodesUsingCache_eq`, `checkUsingCache?_eq`, `evaluate_state`,
`evaluation_positive_sound`).  This probe only executes their executable counterparts on data and
reports what they produced.

## Fixture and admission

The fixture is the `interacting` data of
`TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures`: two constitutionally identical
`CH(F)(Cl)` branches around a central carbon, written
`[H][C@]([C@]([H])([F])[Cl])([Br])[C@@]([H])([F])[Cl]`.  The SMILES text and the synthetic
moment-curve geometry are *copied verbatim, with attribution*, from that data-only module (the
module itself and the runtime probes of `Examples/` are deliberately **not** imported, so no other
`#eval` battery is re-run).  Coordinates are the exact rational moment-curve points `(i, i², i³)`,
one per hydrogen-expanded atom, read from the certified parse.

Admission runs through the actual executable intake `LocalizedExtendedShortCircuit.admitSmilesSpatial?`
(definitionally `LocalizedReference.admitSmilesSpatial?`, the same OpenSMILES parse/normalization,
hydrogen-expansion admissibility gate and checked `admitRawSpatial?` used by the pipeline; the
`LocalizedNoDoubleReference` intake only adds a source-record restriction proof and leaves the
certificate unchanged).  No stored per-molecule certificate and no handwritten admission proof is
used.

## Executed scope

Exactly one full pipeline run:

* `Cached.buildRuntimeCache` is called **once** and its `carrier` and dependency table are reused;
* `Cached.nodesUsingCache` performs **one** ranked production over that materialized carrier;
* `Cached.checkUsingCache?` is called **once** and its `Option` result is matched **once** (the
  prior odd-cumulene probe showed generated C re-evaluating the pure checker when the result was
  first tested with `isSome` and then matched again); there is no `evaluate`/`checkProposals?`
  fallback replay and no second production;
* the stored cache is never rebuilt and `referenceNodes`/`referenceFacts`/`referenceState` are never
  invoked.

In the accepted branch the probe asserts, as runtime observations only:

* the cached checker returned exactly the target/outcome projection of the one produced node list,
  and that table is not the synthetic all-`none` table;
* the checked facts enumerate the complete ranked certificate order, are duplicate free, cover every
  materialized carrier occurrence, and have the carrier length;
* the canonical report lists exactly the canonical centre atoms and every report label is the
  produced fact at that centre's final occurrence;
* at each interacting centre target, the actual cached dependency-table row equals the ranked
  strict-dependency list, every dependency carries a produced fact, and the produced node's
  references resolve back to exactly that table row (the checker's own structural witness).

The actual report, the computed fact labels, the inventory of every positive fact as
`(occurrence root atom, occurrence address, label)`, and each centre's actual dependency
occurrences (with the descriptor-bearing ones) are printed as data.  The prior probe's *empty-view*
labels
`[(1, none), (2, R), (7, R)]` are local-view outcomes only and do **not** determine the global
reference state, so no global centre label is asserted here; the computed global report is reported
as observed data.  If a centre's final occurrence has no recognized descriptor centre ("unsupported
view root") or no four-ligand frame, the probe says so and does not claim a positive centre
assignment: a `none` outcome there is an operational refusal, never a chemical nonexistence claim.

## Budget

The measured cost of this full pipeline is reported in the log.  There is one expensive trial; if
the single interaction carrier run is too slow, the timings are reported instead of retrying larger
graphs.  The deep fixture and the global twenty-three-atom pipeline are not run.

All claims of this module are runtime observations on the named fixture.  No external chemical
approval is asserted or implied.
-/

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

/-! ## Fixture data (copied verbatim with attribution)

The following five definitions are copied from
`TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures` (`momentCurvePoint`, `momentCurve`,
`expandedMolecule?`, `syntheticSpatial`, and the `interactingSmiles` fixture text).  That module is
data-only and is not imported, so its own `#eval` reporting cannot run from here. -/

/-- The `index`-th moment-curve point `(i, i², i³)`, exactly in `ℚ`. -/
private def momentCurvePoint (index : ℕ) : CartesianPoint3 :=
  { x := (index : ℚ)
    y := (index : ℚ) * (index : ℚ)
    z := (index : ℚ) * (index : ℚ) * (index : ℚ) }

/-- `count` exact moment-curve points, indexed by atom index. -/
private def momentCurve (count : ℕ) : SpatialConfiguration :=
  { positions := (List.range count).map momentCurvePoint }

/-- The hydrogen-expanded molecule of a SMILES fixture, when the certified parse succeeds. -/
private def expandedMolecule? (text : String) : Option RawMolecule :=
  match parseAndNormalizeOpenSMILESCertified text with
  | Except.error _ => none
  | Except.ok certified => some certified.result.parsed.withExplicitHydrogens

/-- Synthetic geometry with exactly one moment-curve point per hydrogen-expanded atom, the count
read from the actual certified parse. -/
private def syntheticSpatial (text : String) : SpatialConfiguration :=
  match expandedMolecule? text with
  | none => { positions := [] }
  | some molecule => momentCurve molecule.atomCount

/-- Two constitutionally identical `CH(F)(Cl)` branches around a central carbon, all atoms written
explicitly.  Written atom order: `0` H, `1` C (central), `2` C (first branch), `3` H, `4` F,
`5` Cl, `6` Br, `7` C (second branch), `8` H, `9` F, `10` Cl.  Copied verbatim from
`LocalizedNoDoubleReferenceFixtures.interactingSmiles`. -/
def interactingSmiles : String :=
  "[H][C@]([C@]([H])([F])[Cl])([Br])[C@@]([H])([F])[Cl]"

/-- The fixture geometry: the moment curve over the hydrogen-expanded atom list (eleven atoms).
Copied from `LocalizedNoDoubleReferenceFixtures.interactingSpatial`. -/
def interactingSpatial : SpatialConfiguration := syntheticSpatial interactingSmiles

/-! ## Pipeline abbreviations and admission -/

abbrev Input := LocalizedUniversalReference.Input

abbrev RuntimeCache := LocalizedUniversalReference.Cached.RuntimeCache

abbrev Facts (input : Input) := LocalizedUniversalReference.Facts input

abbrev Nodes (input : Input) := LocalizedUniversalReference.Nodes input

/-- Admit the copied interacting fixture through the actual executable OpenSMILES intake of the
universal reference pipeline. -/
def admitInteracting : IO Input := do
  match LocalizedExtendedShortCircuit.admitSmilesSpatial? interactingSmiles interactingSpatial with
  | Except.error message =>
      throw (IO.userError ("interacting: parse/normalization error: " ++ message))
  | Except.ok none =>
      throw (IO.userError "interacting: rejected by the checked executable intake")
  | Except.ok (some input) => pure input

/-- Spell one auxiliary label, preserving `none` as an explicit outcome. -/
def labelText : Option LocalizedAuxiliaryLabel → String
  | none => "none"
  | some (.chiral .R) => "R"
  | some (.chiral .S) => "S"
  | some (.pseudoasymmetric .r) => "r"
  | some (.pseudoasymmetric .s) => "s"

/-! ## Per-centre dependency and table witness -/

/-- Numeric and label summary of one interacting centre target. -/
structure CentreWitness where
  atom : Nat
  dependencies : Nat
  references : Nat
  descriptorBearing : Nat
  label : Option LocalizedAuxiliaryLabel
  deriving Repr

/-- Observe one canonical centre's final occurrence against the materialized cache and the single
produced node list.  Nothing here runs a descriptor: the label is read from the produced facts, the
dependency row from the materialized table, and the references from the produced node. -/
def centreWitness (input : Input) (cache : RuntimeCache input) (nodes : Nodes input)
    (facts : Facts input) (center : input.certified.TetrahedralCenter) :
    IO CentreWitness := do
  let fuel := LocalizedUniversalReference.carrierFuel input
  let atom := center.val.val
  let target := input.certified.localizedFinalOccurrenceExecutable fuel center
  match input.certified.localizedOccurrenceDescriptorCenter? target with
  | none =>
      note s!"CENTRE {atom}: the final occurrence has no recognized descriptor centre \
(unsupported view root); a none outcome here is an exact refusal and no positive centre \
assignment can be claimed."
  | some stored =>
      checkTest s!"interacting centre {atom}: the final occurrence stores its descriptor centre"
        (decide (stored = center))
  match input.certified.localizedNoDoubleFourLigandFrameExec? target with
  | none =>
      note s!"CENTRE {atom}: the final occurrence has no four-ligand frame; a none outcome here \
is an operational refusal and no positive centre assignment can be claimed."
  | some _ => pure ()
  let dependencies := LocalizedUniversalReference.Cached.dependenciesUsingCache input cache target
  let ranked := input.certified.localizedDependencyList fuel target
  checkTest s!"interacting centre {atom}: the cached table row is the ranked dependency list"
    (decide (dependencies = ranked))
  let dependencyInventory := dependencies.map fun dependency =>
    (dependency.1.root.val, dependency.1.address)
  note s!"CENTRE {atom}: dependencyOccurrences={repr dependencyInventory}"
  let targets := facts.map Prod.fst
  checkTest s!"interacting centre {atom}: every dependency carries a produced fact"
    (dependencies.all fun dependency => decide (dependency ∈ targets))
  let label := TetraStereo.Certificate.Dependency.lookup facts target
  match nodes.find? (fun node => decide (node.target = target)) with
  | none =>
      throw (IO.userError s!"interacting centre {atom}: no produced node at the centre target")
  | some node =>
      checkTest s!"interacting centre {atom}: the node references cover every ranked dependency"
        (decide (node.references.length = dependencies.length))
      checkTest s!"interacting centre {atom}: the node references resolve to the actual cached \
table row"
        (decide ((TetraStereo.Certificate.Dependency.referenced facts node.references).map Prod.fst
          = dependencies))
      let bearingInventory := (dependencies.filter fun dependency =>
          (TetraStereo.Certificate.Dependency.lookup facts dependency).isSome).map fun dependency =>
        (dependency.1.root.val, dependency.1.address,
          labelText (TetraStereo.Certificate.Dependency.lookup facts dependency))
      let descriptorBearing := bearingInventory.length
      note s!"CENTRE {atom}: label={labelText label}, dependencies={dependencies.length}, \
references={node.references.length}, descriptorBearingDependencies={descriptorBearing}, \
descriptorBearingOccurrences={repr bearingInventory}"
      pure { atom
             dependencies := dependencies.length
             references := node.references.length
             descriptorBearing
             label }

/-! ## The single full pipeline run -/

def main : IO Unit := do
  let start ← IO.monoMsNow
  note "== full cached universal reference pipeline: interacting 11-atom fixture =="

  -- Admission through the actual executable intake.
  let input ← admitInteracting
  let admittedAt ← IO.monoMsNow
  checkTest "interacting: the hydrogen-expanded molecule has eleven atoms"
    (input.certified.certified.input.molecule.atomCount == 11)
  checkTest "interacting: spatial evidence is present"
    input.certified.certified.input.spatial?.isSome
  let fuel := LocalizedUniversalReference.carrierFuel input
  let centers := input.certified.canonicalTetrahedralCenters
  checkTest "interacting: the canonical centres are exactly atoms 1, 2 and 7"
    (decide (centers.map (fun center => center.val.val) = [1, 2, 7]))
  note s!"ADMIT interacting: atoms={input.certified.certified.input.molecule.atomCount}, \
fuel={fuel}, centres={repr (centers.map fun center => center.val.val)}, \
{admittedAt - start}ms"

  -- One runtime cache, built once and reused for every later query.
  let cache := LocalizedUniversalReference.Cached.buildRuntimeCache input
  let builtAt ← IO.monoMsNow
  let carrier := cache.carrier
  checkTest "interacting: the materialized carrier is nonempty" (decide (0 < carrier.length))
  checkTest "interacting: the materialized carrier has the expected 121 occurrences"
    (decide (carrier.length = 121))
  note s!"CACHE interacting: carrier={carrier.length}, build={builtAt - admittedAt}ms"

  -- One ranked production over the materialized carrier.
  let nodes := LocalizedUniversalReference.Cached.nodesUsingCache input cache
  let producedAt ← IO.monoMsNow
  let facts : Facts input := nodes.map fun node => (node.target, node.outcome)
  checkTest "interacting: the production is nonempty" (decide (0 < nodes.length))
  note s!"PRODUCE interacting: nodes={nodes.length}, facts={facts.length}, \
produce={producedAt - builtAt}ms"

  -- Single cached checker call; its result is matched once and reused.
  match LocalizedUniversalReference.Cached.checkUsingCache? input cache nodes with
  | none =>
      throw (IO.userError "interacting: the cached checker rejected the produced nodes")
  | some checkedFacts =>
      let checkedAt ← IO.monoMsNow
      checkTest "interacting: the cached checker returned exactly the produced node projection"
        (decide (checkedFacts = facts))
      checkTest "interacting: the produced fact table is not the synthetic all-none table"
        (checkedFacts.any fun fact => fact.2.isSome)
      let targets := checkedFacts.map Prod.fst
      let order := input.certified.localizedCertificateOrder fuel
      checkTest "interacting: the checked facts enumerate the complete ranked certificate order"
        (decide (targets = order))
      checkTest "interacting: the checked fact targets are duplicate free"
        (decide targets.Nodup)
      checkTest "interacting: the checked facts cover every materialized carrier occurrence"
        (carrier.all fun occurrence => decide (occurrence ∈ targets))
      checkTest "interacting: the checked facts and the materialized carrier have equal length"
        (decide (checkedFacts.length = carrier.length))
      checkTest "interacting: every canonical centre final occurrence is a produced fact target"
        (centers.all fun center =>
          decide (input.certified.localizedFinalOccurrenceExecutable fuel center ∈ targets))

      -- The canonical report from the produced facts.
      let report := LocalizedUniversalReference.report input checkedFacts
      checkTest "interacting: the report lists exactly the canonical centre atoms"
        (decide (report.map Prod.fst = centers.map fun center => center.val.val))
      checkTest "interacting: every report label is the produced fact at its centre's final \
occurrence"
        (decide (report = centers.map fun center =>
          (center.val.val,
            TetraStereo.Certificate.Dependency.lookup checkedFacts
              (input.certified.localizedFinalOccurrenceExecutable fuel center))))
      let positive := (checkedFacts.filter fun fact => fact.2.isSome).length
      let positiveInventory := (checkedFacts.filter fun fact => fact.2.isSome).map fun fact =>
        (fact.1.1.root.val, fact.1.1.address, labelText fact.2)
      note s!"REPORT interacting: {repr report}"
      note s!"FACT-LABELS interacting: total={checkedFacts.length}, positive={positive}, \
none={checkedFacts.length - positive}, centreLabels={repr report}"
      checkTest "interacting: the positive-fact inventory has the positive-fact count"
        (decide (positiveInventory.length = positive))
      note s!"POSITIVE-FACTS interacting: {repr positiveInventory}"

      -- Per-centre dependency rows and actual table witnesses.
      let mut witnesses : List CentreWitness := []
      for center in centers do
        witnesses := witnesses ++ [← centreWitness input cache nodes checkedFacts center]
      let witnessedAt ← IO.monoMsNow
      checkTest "interacting: every canonical centre target is witnessed"
        (decide (witnesses.length = centers.length))
      note s!"WITNESSES interacting: {repr witnesses}"
      note s!"SUMMARY interacting: fuel={fuel}, carrier={carrier.length}, nodes={nodes.length}, \
checkedFacts={checkedFacts.length}, positiveFacts={positive}, report={repr report}, \
reportTargets={repr (report.map Prod.fst)}"
      note s!"TIMING interacting: admission={admittedAt - start}ms, cache={builtAt - admittedAt}ms, \
produce={producedAt - builtAt}ms, check={checkedAt - producedAt}ms, \
witnesses={witnessedAt - checkedAt}ms, total={witnessedAt - start}ms"
      note "SCOPE interacting: one cached production and one cached checked replay, no evaluate \
fallback and no second production.  The printed global centre labels are observations; the prior \
empty-view labels ((1,none),(2,R),(7,R)) are local-view data and are not asserted to be the global \
reference state.  No external chemical approval is claimed."
      IO.println "cached universal interacting pipeline probe complete"

end TetraStereo.Examples.LocalizedUniversalInteractingCachedProbe

#eval TetraStereo.Examples.LocalizedUniversalInteractingCachedProbe.main
