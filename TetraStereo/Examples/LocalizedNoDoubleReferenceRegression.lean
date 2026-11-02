import TetraStereo.OneCenter.LocalizedRerootChildrenCache
import TetraStereo.OneCenter.LocalizedNoDoubleWithChildren
import TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures
import TetraStereo.OneCenter.LocalizedNoDoubleDescriptorExecutable
import TetraStereo.OneCenter.LocalizedOccurrenceFiniteCarrier
import TetraStereo.OneCenter.LocalizedOccurrenceExecutableRoots
import TetraStereo.OneCenter.FiniteStateIteration

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedNoDoubleReferenceRegression

open OneCenter
open OneCenter.LocalizedNoDoubleReference
open TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures

/-!
# Executable regression for the localized no-double-bond reference intake

This module runs the fixtures of `LocalizedNoDoubleReferenceFixtures` through the checked intake and
asserts the *actual* outputs.  Every assertion is an `IO` runtime test: a failing one raises
`IO.userError`, which fails the module's elaboration.  No expectation is assumed, weakened or
encoded as a hypothesis; the module reads nothing but the values of its own declarations.

## Scope

* admission of the copied baseline, the coordinate-free baseline, the ring, nitrile, deep and
  interacting fixtures;
* exactness of the copied baseline geometry and of the admitted molecule;
* the coordinate/atom-count agreement advertised by `LocalizedNoDoubleReferenceInput`;
* the source-record no-double-bond restriction on every admitted input;
* fail-closed rejection of a genuine double bond, of a missing spatial channel at the descriptor
  layer (reported, see below) and of wrong coordinate counts;
* the interacting variation: exactly the branch F/Cl coordinates move, and the exchange is an
  involution;
* the descriptor layer itself: `describe` tabulates the localized occurrence carrier of each
  admitted input, iterates the no-double executable descriptor step to its fixed point, and reads
  the auxiliary label of every canonical tetrahedral candidate out of the fact table.  Every
  candidate is reported, a candidate whose label is `none` included.

## What is run here

`#eval fullRegression` executes intake, malformed input, coordinate checks, baseline descriptors,
and all four larger molecular fixtures. The evaluator binds its carrier once and passes that
carrier to every recursive child read. Runtime assertions include the central pseudoasymmetric
response to exchanging coordinates on one branch.

The `#eval` reports below print every count and every label they observe instead of only asserting
remembered numbers, so a change in hydrogen expansion or in a descriptor is visible rather than
silently absorbed.
-/

/-- Report one runtime test and fail the module when it does not hold. -/
def check (name : String) (holds : Bool) : IO Unit :=
  if holds then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed runtime test: " ++ name))

/-- Whether the checked intake returned an admitted input.  Parse errors, fail-closed rejections
and admissions are three distinct outcomes and are never conflated. -/
def admittedBool : Except ParserError (Option Input) → Bool
  | Except.error _ => false
  | Except.ok none => false
  | Except.ok (some _) => true

/-- Extract the admitted input, or fail loudly with the actual failure shape. -/
def admittedOrFail (name : String) (outcome : Except ParserError (Option Input)) : IO Input :=
  match outcome with
  | Except.error message =>
      throw (IO.userError (name ++ ": unexpected parse/normalization error: " ++ message))
  | Except.ok none =>
      throw (IO.userError (name ++ ": unexpectedly rejected by the checked intake"))
  | Except.ok (some input) => pure input

/-- Assert the invariants every admitted fixture must satisfy, independently of any remembered atom
count: the coordinate list indexes the whole hydrogen-expanded atom list, and every localized
source record has order other than two. -/
def checkAdmitted (name : String) (outcome : Except ParserError (Option Input)) : IO Input := do
  let input ← admittedOrFail name outcome
  check (name ++ ": the coordinate list indexes every hydrogen-expanded atom")
    (decide (((Input.authority input).input.spatial?).map (fun configuration =>
      configuration.positions.length) = some (Input.molecule input).atomCount))
  check (name ++ ": every localized source record has order ≠ 2")
    ((Input.molecule input).noLocalizedDoubleBondRecords?)
  IO.println (admitSummary name (Except.ok (some input)))
  pure input

/-- Two configurations differ at exactly the listed indices. -/
def differsExactlyAt (before after : SpatialConfiguration) (indices : List ℕ) : Bool :=
  before.positions.length = after.positions.length &&
    (List.range before.positions.length).all fun index =>
      decide (before.positions[index]? = after.positions[index]?) ==
        !(decide (index ∈ indices))

/-- How many localized source records carry the given bond order. -/
def recordCountWithOrder (input : Input) (order : ℕ) : ℕ :=
  ((Input.molecule input).localizedCovalentRecords.filter
    fun record => decide (record.2 = order)).length

/-- Whether the atom at the given index is an automatically detected localized tetrahedral
candidate.  Written by index rather than through `Finset.toList` because that projection is not
computable and this module must be executable. -/
def isCenter (input : Input) (index : ℕ) : Bool :=
  if below : index < (Input.molecule input).atomCount then
    decide ((⟨index, below⟩ : input.certified.Atom) ∈ input.certified.tetrahedralCenterSet)
  else false

/-- Atom indices of the automatically detected localized tetrahedral candidates, in increasing
order.  Every fixture reports this list, so a unit that receives no descriptor is visible rather
than silently dropped. -/
def centerIndices (input : Input) : List ℕ :=
  (List.range (Input.molecule input).atomCount).filter (isCenter input)

/-! ## Baseline and negative cases -/

def runBaselineAndNegative : IO Unit := do
  let baseline ← checkAdmitted "baseline halomethane" (Except.ok halomethane)
  check "baseline: admitted coordinates are exactly the copied halomethane positions"
    (decide ((Input.authority baseline).input.spatial? = halomethaneSource.spatial?))
  check "baseline: spatial evidence is present"
    ((Input.authority baseline).input.spatial?.isSome)
  check "baseline: the admitted molecule is the supplied source molecule"
    (decide ((Input.molecule baseline) = halomethaneSource.molecule))
  check "baseline: the five-atom expansion is unchanged"
    (decide ((Input.molecule baseline).atomCount = 5))
  check "baseline: exactly one tetrahedral candidate is detected"
    (decide ((centerIndices baseline).length = 1))
  check "baseline: the detected candidate is carbon at index 0"
    (decide ((centerIndices baseline) = [0]))
  let coordinateFree ← admittedOrFail "halomethane without spatial evidence"
    (Except.ok halomethaneWithoutSpatial)
  check "coordinate-free baseline: intake accepts a missing spatial channel"
    (decide ((Input.authority coordinateFree).input.spatial? = none))
  check "coordinate-free baseline: the molecule is unchanged"
    (decide ((Input.molecule coordinateFree) = halomethaneSource.molecule))
  check "double-bond source: rejected by the source-record restriction" ethene.isNone
  check "double-bond source: the rejection is not an admitted input"
    (!(admittedBool (Except.ok ethene)))
  check "short spatial configuration: rejected by the structural index agreement"
    shortSpatialHalomethane.isNone
  IO.println ("double-bond source: " ++
    (match (Except.ok ethene : Except ParserError (Option Input)) with
     | Except.error message => "error: " ++ message
     | Except.ok none => "not admitted"
     | Except.ok (some _) => "admitted"))
  IO.println ("coordinate-free baseline: intake accepts; a descriptor is a downstream question")

/-! ### Isolating the rejecting gate

`admitSource?` applies three gates in order: structural certification (`certify?`), localized CIP
graph readiness (`certifyLocalizedCIP?`) and the source-record no-double test.  A negative test only
exercises the gate it is named for when the two earlier gates succeed, so each rejection below is
reported together with the actual outcome of every gate, and the checks assert the gate that fails.
Nothing here presumes which gate rejects: the printed line carries the observed outcome. -/

/-- The localized certificate of a source, or `none` when structural certification or localized CIP
graph readiness already fails.  This is the same chain `admitSource?` walks, exposed so the
rejecting gate of a negative fixture is observable rather than inferred. -/
def localizedCertificate? (source : AuthoritativeChemicalInput) :
    Option CertifiedLocalizedCIPInput :=
  match source.certify? with
  | none => none
  | some certified => certified.certifyLocalizedCIP?

/-- The gate outcomes of one source: structural certification, localized CIP graph readiness, the
source-record no-double test, and the number of order-two records the restriction looks at. -/
def gateReport (name : String) (source : AuthoritativeChemicalInput) : String :=
  let localized := localizedCertificate? source
  name ++ ": structural certification = " ++ toString source.certify?.isSome ++
    "; localized CIP graph readiness = " ++ toString localized.isSome ++
    "; order-2 records = " ++
      toString ((localized.map (fun certificate =>
        (certificate.certified.input.molecule.localizedCovalentRecords.filter
          fun record => decide (record.2 = 2)).length)).getD 0) ++
    "; no-double source-record test = " ++
      toString ((localized.map (fun certificate =>
        certificate.certified.input.molecule.noLocalizedDoubleBondRecords?)).getD false)

def runGateIsolation : IO Unit := do
  IO.println (gateReport "double-bond source" etheneSource)
  IO.println (gateReport "short spatial configuration" shortSpatialHalomethaneSource)
  check "double-bond source: structural certification succeeds"
    etheneSource.certify?.isSome
  check "double-bond source: localized CIP graph readiness succeeds, so the two earlier gates pass"
    (localizedCertificate? etheneSource).isSome
  check "double-bond source: the source-record no-double test is the gate that rejects it"
    (decide ((localizedCertificate? etheneSource).map (fun certificate =>
      certificate.certified.input.molecule.noLocalizedDoubleBondRecords?) = some false))
  check "double-bond source: the restriction sees exactly one order-2 record"
    (decide ((localizedCertificate? etheneSource).map (fun certificate =>
      (certificate.certified.input.molecule.localizedCovalentRecords.filter
        fun record => decide (record.2 = 2)).length) = some 1))
  check "short spatial configuration: structural certification is already the failing gate"
    (decide (shortSpatialHalomethaneSource.certify? = none))

/-! ## SMILES fixtures -/

def reportFixture (name : String) (input : Input) : IO Unit :=
  IO.println (name ++ ": expanded atoms = " ++ toString (Input.molecule input).atomCount ++
    "; localized records = " ++ toString (Input.molecule input).localizedCovalentRecords.length ++
    "; order-1 records = " ++ toString (recordCountWithOrder input 1) ++
    "; order-3 records = " ++ toString (recordCountWithOrder input 3) ++
    "; detected tetrahedral candidates = " ++ toString (centerIndices input).length ++
    " at " ++ toString (centerIndices input))

def runSmilesFixtures : IO Unit := do
  let ringInput ← checkAdmitted "ring" ring.admitted
  let nitrileInput ← checkAdmitted "nitrile" nitrile.admitted
  let deepInput ← checkAdmitted "deep" deep.admitted
  let interactingInput ← checkAdmitted "interacting" interacting.admitted
  let variationInput ← checkAdmitted "interacting-variation" interactingVariation.admitted
  reportFixture "ring" ringInput
  reportFixture "nitrile" nitrileInput
  reportFixture "deep" deepInput
  reportFixture "interacting" interactingInput
  check "ring: 9 expanded atoms and 9 localized records"
    (decide ((Input.molecule ringInput).atomCount = 9 ∧
      (Input.molecule ringInput).localizedCovalentRecords.length = 9))
  check "nitrile: 14 expanded atoms and 13 localized records"
    (decide ((Input.molecule nitrileInput).atomCount = 14 ∧
      (Input.molecule nitrileInput).localizedCovalentRecords.length = 13))
  check "deep: 23 expanded atoms and 22 localized records"
    (decide ((Input.molecule deepInput).atomCount = 23 ∧
      (Input.molecule deepInput).localizedCovalentRecords.length = 22))
  check "interacting: 11 expanded atoms and 10 localized records"
    (decide ((Input.molecule interactingInput).atomCount = 11 ∧
      (Input.molecule interactingInput).localizedCovalentRecords.length = 10))
  check "ring: detected tetrahedral candidates are exactly 0, 2 and 4"
    (decide (centerIndices ringInput = [0, 2, 4]))
  check "nitrile: detected tetrahedral candidates are exactly 0, 4 and 6"
    (decide (centerIndices nitrileInput = [0, 4, 6]))
  check "deep: detected tetrahedral candidates are exactly 1, 2, 3, 4, 6, 7 and 8"
    (decide (centerIndices deepInput = [1, 2, 3, 4, 6, 7, 8]))
  check "interacting: detected tetrahedral candidates are exactly 1, 2 and 7"
    (decide (centerIndices interactingInput = [1, 2, 7]))
  check "interacting-variation: the same candidates as the interacting fixture"
    (decide (centerIndices variationInput = [1, 2, 7]))
  check "nitrile: exactly one order-3 localized record"
    (decide (recordCountWithOrder nitrileInput 3 = 1))
  check "nitrile: no order-2 localized record"
    (decide (recordCountWithOrder nitrileInput 2 = 0))
  check "deep: no order-3 localized record"
    (decide (recordCountWithOrder deepInput 3 = 0))
  check "interacting: the exchange hits exactly positions 4 and 5"
    (differsExactlyAt interactingSpatial interactingVariationSpatial [4, 5])
  check "interacting: the exchange is an involution"
    (decide (swapPositions interactingVariationSpatial 4 5 = interactingSpatial))
  check "interacting: expanded index 4 is fluorine"
    (decide (expandedElement? interactingSmiles 4 = some Element.F))
  check "interacting: expanded index 5 is chlorine"
    (decide (expandedElement? interactingSmiles 5 = some Element.Cl))
  check "interacting: expanded index 9 is fluorine"
    (decide (expandedElement? interactingSmiles 9 = some Element.F))
  check "interacting: expanded index 10 is chlorine"
    (decide (expandedElement? interactingSmiles 10 = some Element.Cl))
  check "interacting: the two admitted molecules are the same constitution"
    (decide ((Input.molecule interactingInput) = (Input.molecule variationInput)))
  check "interacting: the two admitted inputs carry different coordinates"
    (decide ((Input.authority interactingInput).input.spatial? ≠
      (Input.authority variationInput).input.spatial?))
  IO.println "interacting variation: only the branch F/Cl coordinates changed"

/-! ## Wrong coordinate count -/

/-- The certified normalization result of a SMILES text, when the checked parse succeeds. -/
def certifiedParse? (text : String) : Option CertifiedChemistryNormalizationResult :=
  match parseAndNormalizeOpenSMILESCertified text with
  | Except.error _ => none
  | Except.ok certified => some certified

/-- Whether the checked parse succeeds and the hydrogen-expanded molecule passes the structural
stereochemical admission that `admitSmilesSpatial?` applies before it looks at coordinates. -/
def expansionAdmitted? (text : String) : Bool :=
  ((certifiedParse? text).map (fun certified =>
    certified.result.expandedStereochemicalAdmissible?)).getD false

/-- Whether the hydrogen-expanded molecule of a parsed text reaches structural certification for the
given coordinates.  `false` means the coordinate index agreement rejected it. -/
def coordinatesCertified? (text : String) (spatial : SpatialConfiguration) : Bool :=
  ((certifiedParse? text).map (fun certified =>
    ((certified.result.parsed.withExplicitHydrogens.toAuthoritativeChemicalInputWithSpatial?
      spatial).bind AuthoritativeChemicalInput.certify?).isSome)).getD false

def runWrongCoordinateCount : IO Unit := do
  check "ring: the checked parse and the expansion admission succeed for the short list"
    (expansionAdmitted? ringSmiles)
  check "ring: the one-entry-short list is rejected at the coordinate index agreement, not earlier"
    (!(coordinatesCertified? ringSmiles { positions := ringSpatial.positions.drop 1 }))
  check "ring: the one-entry-long list is rejected at the coordinate index agreement"
    (!(coordinatesCertified? ringSmiles
      { positions := ringSpatial.positions ++ [momentCurvePoint 6] }))
  check "ring: a coordinate list one entry short is not admitted"
    (!(admittedBool (admitSmilesSpatial? ringSmiles
      { positions := ringSpatial.positions.drop 1 })))
  check "ring: a coordinate list one entry long is not admitted"
    (!(admittedBool (admitSmilesSpatial? ringSmiles
      { positions := ringSpatial.positions ++ [momentCurvePoint 6] })))
  check "ring: the empty coordinate list is not admitted"
    (!(admittedBool (admitSmilesSpatial? ringSmiles (momentCurve 0))))
  check "halomethane: two positions are not admitted for five atoms"
    (admitSource? { halomethaneSource with spatial? := some (momentCurve 2) }).isNone
  check "halomethane: six positions are not admitted for five atoms"
    (admitSource? { halomethaneSource with spatial? := some (momentCurve 6) }).isNone
  IO.println "wrong-coordinate-count cases: all rejected"

/-! ## Descriptor runs

The runner below is exactly the shape already running in `Examples/LocalizedNoDoublePipelineProbe`:
tabulate the localized occurrence carrier of the admitted input, iterate the no-double executable
descriptor step to its fixed point, and read the auxiliary label of every canonical tetrahedral
candidate out of the resulting fact table.  It consumes only the executable admission of this
module; no per-molecule certificate is supplied or assumed.

Every canonical candidate is reported, including one whose label is `none`: a candidate that
receives no descriptor stays visible in both the printed report and the assertions. -/

/-- The auxiliary descriptor label produced by the localized evaluation. -/
abbrev Label := CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel

/-- A descriptor run: the number of tabulated occurrences and, for every canonical tetrahedral
candidate in increasing atom order, its auxiliary label (or `none`). -/
abbrev Run := Option (Nat × List (Nat × Option Label))

/-- The descriptor run: the number of tabulated occurrences, and the auxiliary label of every
canonical tetrahedral candidate in increasing atom order. -/
def describe (input : Input) : Run := do
  let fuel := (Input.molecule input).atomCount + 1
  let carrier := input.certified.localizedOccurrenceCarrier fuel
  let facts := FiniteStateIteration.tabulatedFacts carrier
    (input.certified.localizedExecutableStep
      (CertifiedLocalizedCIPInput.WithChildren.localizedNoDoubleDescriptorExec? input.certified
        (input.certified.localizedRerootChildrenFromCarrier? carrier)))
    (fun _ => none) (fuel + 2)
  let results := input.certified.canonicalTetrahedralCenters.map fun center =>
    (center.val.val, Certificate.Dependency.lookup facts
      (input.certified.localizedFinalOccurrenceExecutable fuel center))
  some (carrier.length, results)

/-- Spell one auxiliary label, preserving `none` as an explicit outcome. -/
def labelText : Option Label → String
  | none => "none"
  | some (.chiral .R) => "R"
  | some (.chiral .S) => "S"
  | some (.pseudoasymmetric .r) => "r"
  | some (.pseudoasymmetric .s) => "s"

/-- One-line report of a descriptor run. -/
def runText (run : Run) : String :=
  match run with
  | none => "no run"
  | some (occurrences, labels) =>
      "occurrences = " ++ toString occurrences ++ "; " ++
        String.intercalate ", " (labels.map fun entry =>
          "center " ++ toString entry.1 ++ " -> " ++ labelText entry.2)

/-- The label of one canonical candidate, or `none` when the candidate is not in the run. -/
def labelAt (run : Run) (center : ℕ) : Option (Option Label) :=
  match run with
  | none => none
  | some (_, labels) =>
      match labels.find? (fun entry => entry.1 == center) with
      | none => none
      | some entry => some entry.2

/-- The descriptor actually assigned to one candidate: `none` both when the candidate is absent from
the run and when it is present with the label `none`.  Only `some` means a descriptor was produced,
so `(assignedAt run center).isSome` is exactly "this candidate received a descriptor". -/
def assignedAt (run : Run) (center : ℕ) : Option Label := (labelAt run center).join

/-- The candidates the run reports, in the run's own order.  Reported so that a candidate silently
dropped from the result list is visible instead of passing unnoticed. -/
def reportedCenters (run : Run) : List ℕ :=
  match run with
  | none => []
  | some (_, labels) => labels.map fun entry => entry.1

/-- Run the descriptor pipeline over one admitted fixture and report the actual output. -/
def descriptorRun (name : String) (outcome : Except ParserError (Option Input)) : IO Run := do
  let input ← admittedOrFail name outcome
  let result := describe input
  IO.println (name ++ ": descriptor run: " ++ runText result)
  pure result

/-- Admit one fixture, run the descriptors over the admitted input, report the detected candidates
and the whole run, and hand both back. -/
def fixtureRun (name : String) (outcome : Except ParserError (Option Input)) : IO (Input × Run) := do
  let input ← admittedOrFail name outcome
  let run := describe input
  IO.println (name ++ ": detected candidates = " ++ toString (centerIndices input) ++
    "; reported candidates = " ++ toString (reportedCenters run))
  IO.println (name ++ ": descriptor run: " ++ runText run)
  pure (input, run)

/-! ## Baseline descriptor runs

Run by `executableSubset`.  The printed line is the actual run; the assertions below state the
structure the reference pipeline is required to produce at the copied baseline. -/

def runBaselineDescriptors : IO Unit := do
  IO.println "== baseline descriptor runs =="
  let baselineRun ← descriptorRun "baseline halomethane" (Except.ok halomethane)
  check "baseline: the descriptor run reports 25 tabulated occurrences"
    (decide (baselineRun.map (fun entry => entry.1) = some 25))
  check "baseline: the run reports exactly the one detected candidate"
    (decide (reportedCenters baselineRun = [0]))
  check "baseline: the single detected centre receives the descriptor R"
    (decide (baselineRun = some (25, [(0, some (.chiral .R))])))
  let coordinateFreeRun ← descriptorRun "halomethane without spatial evidence"
    (Except.ok halomethaneWithoutSpatial)
  check "coordinate-free baseline: the candidate is still reported, with the label none"
    (decide (labelAt coordinateFreeRun 0 = some none))
  check "coordinate-free baseline: no candidate receives a descriptor"
    ((assignedAt coordinateFreeRun 0).isNone)
  IO.println "baseline descriptor runs: complete"


















def runFixtureDescriptors : IO Unit := do
  IO.println "== fixture descriptor runs =="
  let (ringInput, ringRun) ← fixtureRun "ring" ring.admitted
  check "ring: every canonical candidate is reported"
    (decide (reportedCenters ringRun = centerIndices ringInput))
  check "ring: the candidate at atom 0 receives a descriptor"
    (assignedAt ringRun 0).isSome
  let (nitrileInput, nitrileRun) ← fixtureRun "nitrile" nitrile.admitted
  check "nitrile: every canonical candidate is reported"
    (decide (reportedCenters nitrileRun = centerIndices nitrileInput))
  check "nitrile: the candidate at atom 0 receives a descriptor"
    (assignedAt nitrileRun 0).isSome
  let (deepInput, deepRun) ← fixtureRun "deep" deep.admitted
  check "deep: every canonical candidate is reported"
    (decide (reportedCenters deepRun = centerIndices deepInput))
  check "deep: the candidate at atom 1 receives a descriptor"
    (assignedAt deepRun 1).isSome
  let (interactingInput, interactingRun) ← fixtureRun "interacting" interacting.admitted
  let (variationInput, variationRun) ←
    fixtureRun "interacting-variation" interactingVariation.admitted
  check "interacting: the two admitted inputs detect the same candidates"
    (decide (centerIndices interactingInput = centerIndices variationInput))
  check "interacting: every canonical candidate is reported in both runs"
    (decide (reportedCenters interactingRun = centerIndices interactingInput ∧
      reportedCenters variationRun = centerIndices variationInput))
  check "interacting: both branch candidates 2 and 7 receive a descriptor"
    ((assignedAt interactingRun 2).isSome && (assignedAt interactingRun 7).isSome)
  check "interacting: the F/Cl exchange changes the label of branch candidate 2"
    (decide (labelAt interactingRun 2 ≠ labelAt variationRun 2))
  check "interacting: the F/Cl exchange preserves the label of the untouched branch candidate 7"
    (decide (labelAt interactingRun 7 = labelAt variationRun 7))
  IO.println ("interacting: central candidate 1: before the exchange = " ++
    ((labelAt interactingRun 1).map labelText).getD "absent" ++
    "; after the exchange = " ++ ((labelAt variationRun 1).map labelText).getD "absent")
  check "interacting: changing one branch creates the central pseudoasymmetric r descriptor"
    (decide (labelAt interactingRun 1 = some none ∧
      labelAt variationRun 1 = some (some (.pseudoasymmetric .r))))
  IO.println "fixture descriptor runs: complete"

/-! ## Entry points -/

/-- The small regression subset: intake, the negative
cases, the gate isolation and the baseline descriptor runs. -/
def executableSubset : IO Unit := do
  runBaselineAndNegative
  runGateIsolation
  runSmilesFixtures
  runWrongCoordinateCount
  runBaselineDescriptors

/-- Complete executable regression: the subset above plus every fixture descriptor run.  A failed
assertion stops elaboration.  This entry point is kept callable unchanged so that the fixture runs
can be performed later against the cached reader without editing any assertion. -/
def fullRegression : IO Unit := do
  IO.println "== localized no-double-bond reference regression =="
  executableSubset
  runFixtureDescriptors
  IO.println "== regression complete =="

#eval fullRegression

end TetraStereo.Examples.LocalizedNoDoubleReferenceRegression
