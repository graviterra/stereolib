import TetraStereo.OneCenter.LocalizedUniversalReferencePipeline

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedUniversalReferenceProbe

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.LocalizedUniversalReference

/-!
# Runtime probe for the universal reference pipeline

This module is a *runtime regression probe* for
`TetraStereo.OneCenter.LocalizedUniversalReference` (the universal descriptor certificate
pipeline).  It exercises the actual exported API `evaluate` on one admitted source, the smallest
known positive tetrahedral fixture: five-atom bromochlorofluoroiodomethane.

The probe performs exactly one ranked production:

* `referenceNodes input` is materialized once into `nodes`;
* `facts` is the target/outcome projection of that *same* list;
* every later state or report query uses `facts` (or the facts carried by the evaluated result),
  never `referenceState`/`referenceFacts`, whose standalone definitions would run a second
  production.

On that materialization it checks, as runtime observations only:

* the exported checker accepts the materialized nodes;
* the facts enumerate the complete ranked certificate order, are duplicate free, and cover the
  whole executable occurrence carrier;
* `evaluate` keeps the accepted candidate and its facts;
* the state agrees pointwise with the materialized state on every carrier occurrence, and the
  canonical report is chiral `R` at the single center (atom zero);
* a corrupt-outcome candidate is rejected by the checker gate, and the checked fallback carries
  the same facts, the same pointwise state and the same `R` report;
* the empty candidate, a one-node incomplete candidate, an out-of-range dependency reference and
  (when the fixture has a node with at least two references) reversed dependency references are
  rejected.

Nothing here is a chemical theorem.  Each `ok:` line is one runtime observation on the named
fixture; the universal claims are the existing kernel-checked theorems of
`LocalizedUniversalReferencePipeline` (`reference_check`, `reference_targets`,
`reference_state_unique`, `reference_accepted`, `checked_eq_reference`, `evaluate_state`,
`evaluate_rejected_facts`, `evaluation_positive_sound`).  This probe only runs their executable
counterparts on data.

The fixture data is copied verbatim, with attribution, from
`TetraStereo.Examples.LocalizedUniversalDescriptorProbe.halomethaneSource` (also present as
`TetraStereo.Examples.LocalizedPreparedReferenceProbe.halomethaneSource`), so this probe does not
depend on either module.
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

/-! ## Fixture: five-atom bromochlorofluoroiodomethane -/

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

/-- The smallest five-atom positive tetrahedral fixture.  Copied with attribution from the
descriptor and prepared-reference probes. -/
def halomethaneSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, fluorine, chlorine, bromine, iodine].map atom
        interactions := [bond 0 1 1, bond 0 2 1, bond 0 3 1, bond 0 4 1] }
    spatial? := some { positions :=
      [{ x := 0, y := 0, z := 0 }, { x := -1, y := -1, z := 1 },
       { x := -1, y := 1, z := -1 }, { x := 1, y := -1, z := -1 },
       { x := 1, y := 1, z := 1 }] } }

/-! ## Candidate transformations -/

/-- The facts of a materialized node list.  This is the projection the pipeline uses; it runs no
production of its own. -/
private def projectFacts {input : Input} (nodes : Nodes input) : Facts input :=
  nodes.map fun node => (node.target, node.outcome)

/-- Change the first node's outcome, preserving every other field.  Because the first node has no
dependency references, the checker rejects it immediately. -/
private def corruptOutcome {input : Input} (nodes : Nodes input) : Nodes input :=
  match nodes with
  | [] => []
  | head :: tail =>
      let changed : Option LocalizedAuxiliaryLabel :=
        if head.outcome = some (.chiral .R) then some (.chiral .S) else some (.chiral .R)
      { head with outcome := changed } :: tail

/-- Reverse the dependency references of the first node with at least two of them.  When such a
node exists its references are duplicate free and its dependency list has length at least two, so
the reversed reference list is a genuinely different (illegitimate) order. -/
private def reverseFirstLongReferences {input : Input} (nodes : Nodes input) :
    Option (Nodes input) :=
  match nodes.find? (fun node => decide (2 ≤ node.references.length)) with
  | none => none
  | some selected =>
      some (nodes.map fun node =>
        if node.target = selected.target then
          { node with references := node.references.reverse }
        else node)

/-! ## The probe -/

def main : IO Unit := do
  let start ← IO.monoMsNow

  -- One admitted input only.
  let some input := LocalizedUniversalReference.admitSource? halomethaneSource
    | throw (IO.userError "failed: halomethane admission returned none")
  checkTest "halomethane admitted" true
  checkTest "admitted molecule has five atoms"
    (input.certified.certified.input.molecule.atomCount == 5)

  let fuel := LocalizedUniversalReference.carrierFuel input
  let carrier := input.certified.localizedOccurrenceCarrier fuel
  checkTest "executable occurrence carrier is nonempty" (0 < carrier.length)

  -- Materialize the ranked production once; all facts come from this same list.
  let nodes := LocalizedUniversalReference.referenceNodes input
  let facts := projectFacts nodes
  let generatedAt ← IO.monoMsNow
  note s!"GENERATED: carrier={carrier.length}, nodes={nodes.length}, facts={facts.length}, \
{generatedAt - start}ms"
  checkTest "the generated production is nonempty" (0 < nodes.length)
  checkTest "the materialized facts are the node projection"
    (facts.length == nodes.length)

  -- Complete and unique targets.
  let order := input.certified.localizedCertificateOrder fuel
  checkTest "the facts enumerate the complete ranked certificate order"
    (decide (facts.map Prod.fst = order))
  checkTest "the generated targets are duplicate free" ((facts.map Prod.fst).Nodup)
  checkTest "the generated facts cover every carrier occurrence"
    (carrier.all fun occurrence => decide (occurrence ∈ facts.map Prod.fst))
  checkTest "the generated facts and the carrier have equal length"
    (facts.length == carrier.length)

  -- Checker acceptance of the materialized nodes.
  let checked? :=
    TetraStereo.Certificate.Dependency.check
      (LocalizedUniversalReference.runtimeSystem input)
      (LocalizedUniversalReference.dependencies input) nodes
  checkTest "the certificate checker accepts the materialized nodes"
    (decide (checked? = some facts))

  -- The exported evaluation API on the correct candidate.
  let accepted := LocalizedUniversalReference.evaluate input nodes
  checkTest "evaluate keeps the accepted candidate nodes"
    (decide (accepted.nodes = nodes))
  checkTest "evaluate reports the materialized facts"
    (decide (accepted.facts = facts))
  checkTest "evaluate agrees with the materialized state on every carrier occurrence"
    (carrier.all fun occurrence =>
      decide (TetraStereo.Certificate.Dependency.lookup accepted.facts occurrence =
        TetraStereo.Certificate.Dependency.lookup facts occurrence))

  -- The single canonical center and its final occurrence.
  let centers := input.certified.canonicalTetrahedralCenters
  checkTest "there is exactly one canonical tetrahedral center" (centers.length == 1)
  let center ← match centers with
    | [center] => pure center
    | _ => throw (IO.userError "failed: expected exactly one canonical tetrahedral center")
  checkTest "the canonical center is atom zero" (center.val.val == 0)
  let target := input.certified.localizedFinalOccurrenceExecutable fuel center
  checkTest "the final occurrence stores its descriptor center"
    (match input.certified.localizedOccurrenceDescriptorCenter? target with
     | some stored => decide (stored = center)
     | none => false)
  checkTest "the materialized facts assign chiral R at the final center"
    (decide (TetraStereo.Certificate.Dependency.lookup facts target = some (.chiral .R)))
  let canonicalReport := LocalizedUniversalReference.report input facts
  checkTest "the canonical report is chiral R at center zero"
    (decide (canonicalReport = [(0, some (.chiral .R))]))

  -- Corrupt candidate: rejected, checked fallback with identical facts, state and report.
  let corrupt := corruptOutcome nodes
  checkTest "the corrupted candidate differs from the generated nodes"
    (decide (corrupt ≠ nodes))
  checkTest "the corrupted candidate is rejected by the checker gate"
    ((LocalizedUniversalReference.checkProposals? input corrupt).isNone)
  let fallback := LocalizedUniversalReference.evaluate input corrupt
  checkTest "the checked fallback carries the materialized facts"
    (decide (fallback.facts = facts))
  checkTest "the fallback state agrees with the materialized state on every carrier occurrence"
    (carrier.all fun occurrence =>
      decide (TetraStereo.Certificate.Dependency.lookup fallback.facts occurrence =
        TetraStereo.Certificate.Dependency.lookup facts occurrence))
  checkTest "the fallback assigns chiral R at the final center"
    (decide (TetraStereo.Certificate.Dependency.lookup fallback.facts target =
      some (.chiral .R)))
  checkTest "the fallback report equals the materialized report"
    (decide (LocalizedUniversalReference.report input fallback.facts = canonicalReport))

  -- Structurally illegitimate candidates.
  checkTest "the empty candidate is rejected"
    ((LocalizedUniversalReference.checkProposals? input ([] : Nodes input)).isNone)
  checkTest "an incomplete one-node candidate is rejected"
    ((LocalizedUniversalReference.checkProposals? input (nodes.take 1)).isNone)
  match nodes with
  | [] => throw (IO.userError "failed: nonempty candidate unexpectedly empty")
  | head :: tail =>
      checkTest "an out-of-range dependency reference is rejected"
        ((LocalizedUniversalReference.checkProposals?
          input ({ head with references := [0] } :: tail)).isNone)
  match reverseFirstLongReferences nodes with
  | none =>
      note "NOTE: reversed-reference rejection is not applicable on this fixture \
(no node has at least two references)"
  | some reversed =>
      checkTest "the reversed-reference candidate differs from the accepted nodes"
        (decide (reversed ≠ nodes))
      checkTest "reversed dependency references are rejected"
        ((LocalizedUniversalReference.checkProposals? input reversed).isNone)

  let finish ← IO.monoMsNow
  note s!"TIMING: generate={generatedAt - start}ms, total={finish - start}ms"
  note s!"SUMMARY: carrier={carrier.length}, nodes={nodes.length}, facts={facts.length}, \
centers={centers.length}, report={repr canonicalReport}, \
fallbackFactsEqual={decide (fallback.facts = facts)}, \
targetsUnique={decide ((facts.map Prod.fst).Nodup)}"
  IO.println "universal reference probe complete"

#eval main

end TetraStereo.Examples.LocalizedUniversalReferenceProbe
