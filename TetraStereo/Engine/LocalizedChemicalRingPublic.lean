import TetraStereo.OneCenter.LocalizedReferenceInput
import TetraStereo.OneCenter.LocalizedChemicalRingJointCachedExecutable
import TetraStereo.OneCenter.LocalizedChemicalRingAllRootCancellationReport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Public opt-in route for the accumulated-reference, regenerated-context ring evaluator.
Admission checks raw stereochemical admissibility, localized covalent spelling, exact source
binding, localized graph readiness, single bonds and constant formal charge. It does not check
the independent physical coordinate calibration: physical/cancellation theorems retain that
explicit hypothesis. Existing default engine routes are unchanged. -/
namespace TetraStereo.Engine.LocalizedChemicalRing

open OneCenter CertifiedLocalizedCIPInput

/-- A distinct, explicit development profile; its policy has no normative adoption claim. -/
inductive Profile where
  | accumulatedReferencesRegenerated
  deriving DecidableEq, Repr

/-- Structurally checked input to the public ring route. -/
structure Input where
  certified : CertifiedLocalizedCIPInput
  molecule : RawMolecule
  spatial : SpatialConfiguration
  agreement : molecule.AuthoritativeStructureAgreement certified.certified.input
  spatial_eq : certified.certified.input.spatial? = some spatial
  admissible : molecule.StereochemicalAdmissible
  supported : ∀ bond ∈ molecule.bonds, bond.kind.IsLocalizedCovalent
  single : certified.moleculeGraph.SimpleBonded
  charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge certified.moleculeGraph

abbrev Report := LocalizedChemicalRingJointPreparedReport.Report

/-- An executable witness charge, including the empty molecule. -/
def referenceCharge (input : CertifiedLocalizedCIPInput) : Int :=
  if bound : 0 < input.certified.input.molecule.atomCount then
    input.moleculeGraph.formalCharge ⟨0, bound⟩
  else 0

/-- Fail-closed admission from raw structure and exact coordinates. All structural proof fields
are obtained from checks; no output equality or assumed descriptor enters admission. -/
def admitRawSpatial? (molecule : RawMolecule) (spatial : SpatialConfiguration) : Option Input :=
  if admissible : molecule.stereochemicalAdmissible? = true then
    if supported : (molecule.bonds.all fun bond => bond.kind.localizedBondOrder?.isSome) = true then
      match accepted : LocalizedReference.admitRawSpatial? molecule spatial with
      | none => none
      | some localized =>
        let input := localized.certified
        letI : Decidable input.moleculeGraph.SimpleBonded := by
          unfold MoleculeGraph.SimpleBonded
          infer_instance
        if single : input.moleculeGraph.SimpleBonded then
          if charge : ∀ atom : input.Atom,
              input.moleculeGraph.formalCharge atom = referenceCharge input then
            some {
              certified := input
              molecule := molecule
              spatial := spatial
              agreement := (LocalizedReference.admitRawSpatial?_exact molecule spatial localized accepted).1
              spatial_eq := (LocalizedReference.admitRawSpatial?_exact molecule spatial localized accepted).2
              admissible := molecule.stereochemicalAdmissible?_eq_true_iff.mp admissible
              supported := fun bond member =>
                bond.kind.localizedBondOrder?_isSome_iff.mp ((List.all_eq_true.mp supported) bond member)
              single := single
              charge := ⟨referenceCharge input, charge⟩
            }
          else none
        else none
    else none
  else none

/-- Coordinates use the hydrogen-expanded atom list of the current public parser intake. -/
def admitSmilesSpatial? (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle := []) : Except ParserError (Option Input) :=
  match parseAndNormalizeOpenSMILESCertified text cycles with
  | .error message => .error message
  | .ok normalized =>
      if normalized.result.expandedStereochemicalAdmissible? then
        .ok (admitRawSpatial? normalized.result.parsed.withExplicitHydrogens spatial)
      else .error "hydrogen-expanded molecule failed structural stereochemical admission"

/-- Explicit public development evaluator. Refusals are retained as entries. -/
def analyze (_profile : Profile) (input : Input) : Report :=
  LocalizedChemicalRingJointCachedExecutable.analyze input.certified input.molecule

theorem analyze_eq_prepared (profile : Profile) (input : Input) :
    analyze profile input =
      LocalizedChemicalRingJointPreparedReport.analyze input.certified input.molecule :=
  LocalizedChemicalRingJointCachedExecutable.analyze_eq input.certified input.molecule

def analyzeRawSpatial? (profile : Profile) (molecule : RawMolecule)
    (spatial : SpatialConfiguration) : Option Report :=
  (admitRawSpatial? molecule spatial).map (analyze profile)

def analyzeSmilesSpatial? (profile : Profile) (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle := []) : Except ParserError (Option Report) :=
  (admitSmilesSpatial? text spatial cycles).map (Option.map (analyze profile))

/-- Existing engine output vocabulary. An unassigned entry uses the conservative unresolved
bucket; this adapter does not assert a more specific cause of the optional evaluator's refusal. -/
def stereoOutcome : Option LocalizedAuxiliaryLabel → StereoOutcome
  | some (.chiral descriptor) => .tetrahedral descriptor
  | some (.pseudoasymmetric descriptor) => .pseudoTetrahedral descriptor
  | none => .refused .rankingUnresolved

def stereoAssignment (entry : Nat × Option LocalizedAuxiliaryLabel) : StereoAssignment :=
  { unit := .tetrahedral entry.1, outcome := stereoOutcome entry.2 }

/-- Preserve every candidate, including every refusal, in the current public assignment type. -/
def stereoAssignments (report : Report) : List StereoAssignment := report.map stereoAssignment

theorem stereoOutcome_refused_iff (outcome : Option LocalizedAuxiliaryLabel) :
    stereoOutcome outcome = .refused .rankingUnresolved ↔ outcome = none := by
  cases outcome with
  | none => simp [stereoOutcome]
  | some descriptor => cases descriptor <;> simp [stereoOutcome]

theorem stereoAssignments_length (report : Report) :
    (stereoAssignments report).length = report.length := by
  simp [stereoAssignments]

theorem stereoAssignments_units (report : Report) :
    (stereoAssignments report).map StereoAssignment.unit =
      report.map (fun entry => StereoUnit.tetrahedral entry.1) := by
  simp [stereoAssignments, stereoAssignment, List.map_map]

def analyzeStereo (profile : Profile) (input : Input) : List StereoAssignment :=
  stereoAssignments (analyze profile input)

def analyzeRawStereoSpatial? (profile : Profile) (molecule : RawMolecule)
    (spatial : SpatialConfiguration) : Option (List StereoAssignment) :=
  (analyzeRawSpatial? profile molecule spatial).map stereoAssignments

def analyzeSmilesStereoSpatial? (profile : Profile) (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle := []) : Except ParserError (Option (List StereoAssignment)) :=
  (analyzeSmilesSpatial? profile text spatial cycles).map (Option.map stereoAssignments)

theorem analyzeStereo_eq_prepared (profile : Profile) (input : Input) :
    analyzeStereo profile input = stereoAssignments
      (LocalizedChemicalRingJointPreparedReport.analyze input.certified input.molecule) := by
  rw [analyzeStereo, analyze_eq_prepared]

theorem analyzeRawSpatial?_eq_prepared (profile : Profile) (molecule : RawMolecule)
    (spatial : SpatialConfiguration) :
    analyzeRawSpatial? profile molecule spatial =
      (admitRawSpatial? molecule spatial).map (fun input =>
        LocalizedChemicalRingJointPreparedReport.analyze input.certified input.molecule) := by
  unfold analyzeRawSpatial?
  congr 1
  funext input
  exact analyze_eq_prepared profile input

theorem analyzeSmilesSpatial?_eq_prepared (profile : Profile) (text : String)
    (spatial : SpatialConfiguration) (cycles : List AromaticCycle) :
    analyzeSmilesSpatial? profile text spatial cycles =
      (admitSmilesSpatial? text spatial cycles).map (Option.map (fun input =>
        LocalizedChemicalRingJointPreparedReport.analyze input.certified input.molecule)) := by
  unfold analyzeSmilesSpatial?
  congr 1
  congr 1
  funext input
  exact analyze_eq_prepared profile input

theorem analyze_length (profile : Profile) (input : Input) :
    (analyze profile input).length = input.certified.tetrahedralCenterSet.card := by
  rw [analyze_eq_prepared]
  exact LocalizedChemicalRingJointPreparedReport.analyze_length input.certified input.molecule

theorem analyze_indices_nodup (profile : Profile) (input : Input) :
    ((analyze profile input).map Prod.fst).Nodup := by
  rw [analyze_eq_prepared]
  exact LocalizedChemicalRingJointPreparedReport.analyze_indices_nodup input.certified input.molecule

noncomputable section

open LocalizedChemicalRingJointPreparedSourceQueries (SourceQuery)
open LocalizedChemicalRingJointPreparedSourceModel (SourceModel profileFamily)
open LocalizedChemicalRingJointPreparedSourceModelExistence (finalQuery)
open LocalizedChemicalRingSourcePromotionCancellation (sourceCancellationDescriptor)
open LocalizedChemicalRingJointPreparedSourceStep (sourceKeysAt)
open LocalizedChemicalRingSourcePromotionApplicability (sourceAdjacent)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData observedGeometry)
open DeclarativeCIP.ProductionOccurrenceRules456 (sourceRule6Applicable rule6GroupSizes)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open MultiCenterMolecule (PairwiseProperDistinguishable)

/-- Every admitted public report is exactly the final projection of a unique independent
source model, including refusals. This basic semantic connection needs no physical calibration. -/
theorem existsUnique_report_sourceModel (profile : Profile) (input : Input) :
    ∃! candidate : LocalizedChemicalRingJointPreparedSourceModel.Profile input.certified input.molecule,
      SourceModel input.certified input.molecule input.single candidate ∧
      (∀ atom outcome, (atom, outcome) ∈ analyze profile input ↔
        ∃ center : input.certified.detectedMultiCenterMolecule.Center, center.1.val = atom ∧
          candidate (inputGeometry input.certified) []
            (finalQuery input.certified input.molecule input.agreement center) = outcome) := by
  obtain ⟨candidate, model, unique⟩ :=
    LocalizedChemicalRingJointPreparedSourceModelExistence.existsUnique_sourceModel
      input.certified input.molecule input.agreement input.admissible input.supported input.single
  refine ⟨candidate, ⟨model, ?_⟩, fun other meaning => unique other meaning.1⟩
  intro atom outcome
  rw [analyze_eq_prepared]
  exact LocalizedChemicalRingJointPreparedSourceModelExistence.mem_analyze_iff_sourceModel
    input.certified input.molecule input.agreement input.admissible input.supported input.single
    model atom outcome

/-- Independent meaning of the literal public report, including completed refusals, exact
physical lowercase classification and cancellation/applicability at every final root. -/
structure SourceMeaning (profile : Profile) (input : Input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (candidate : LocalizedChemicalRingJointPreparedSourceModel.Profile input.certified input.molecule) : Prop where
  model : SourceModel input.certified input.molecule input.single candidate
  report : ∀ atom outcome, (atom, outcome) ∈ analyze profile input ↔
    ∃ center : input.certified.detectedMultiCenterMolecule.Center, center.1.val = atom ∧
      candidate (inputGeometry input.certified) []
        (finalQuery input.certified input.molecule input.agreement center) = outcome
  physical : ∀ center : input.certified.detectedMultiCenterMolecule.Center,
    PairwiseProperDistinguishable input.certified.detectedMultiCenterMolecule cfg center →
    ∃ descriptor,
      candidate (inputGeometry input.certified) []
        (finalQuery input.certified input.molecule input.agreement center) = some descriptor ∧
      (center.1.val, some descriptor) ∈ analyze profile input ∧
      (descriptor.IsLowercase ↔
        physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg center = 1)
  rootCancellation : ∀ (query : SourceQuery input.certified input.molecule)
    (center : input.certified.detectedMultiCenterMolecule.Center)
    (_current : query.1.atom = center.1.val)
    (data : OccurrenceData input.certified input.molecule center query.1)
    (_root : data.target.1.address = []) (references : List input.certified.Atom),
    sourceCancellationDescriptor input.certified input.single
      (profileFamily input.certified input.molecule candidate query)
      data.target data.frame (inputGeometry input.certified) references =
      some (candidate (inputGeometry input.certified) references query)
  rootApplicability : ∀ (query : SourceQuery input.certified input.molecule)
    (center : input.certified.detectedMultiCenterMolecule.Center)
    (_current : query.1.atom = center.1.val)
    (data : OccurrenceData input.certified input.molecule center query.1)
    (_root : data.target.1.address = []) (references : List input.certified.Atom) (reflected : Bool),
    ¬ Function.Injective (sourceKeysAt input.certified input.single
      (profileFamily input.certified input.molecule candidate query)
      data.target data.frame (observedGeometry input.certified reflected) references) →
    sourceRule6Applicable (rule6GroupSizes (sourceAdjacent input.certified input.single
      (profileFamily input.certified input.molecule candidate query)
      data.target data.frame (observedGeometry input.certified reflected) references)) = true ∨
      candidate (inputGeometry input.certified) references query = none

/-- The public executable report has a unique independent meaning. Calibration is an explicit
physical hypothesis, not inferred from structural admission or from a successful output. -/
theorem existsUnique_sourceMeaning (profile : Profile) (input : Input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ center : input.certified.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input.certified
        input.certified.detectedMultiCenterMolecule cfg center) :
    ∃! candidate, SourceMeaning profile input cfg candidate := by
  obtain ⟨candidate, facts, _unique⟩ :=
    LocalizedChemicalRingAllRootCancellationReport.existsUnique_allRoot_cancellation_applicability_source_report
      input.certified input.single input.molecule input.agreement input.admissible input.supported
      input.charge cfg calibrated
  refine ⟨candidate, ?_, ?_⟩
  · refine ⟨facts.1, ?_, ?_, facts.2.2.2.2.2.1, facts.2.2.2.2.2.2.1⟩
    · simpa only [analyze_eq_prepared] using facts.2.1
    · simpa only [analyze_eq_prepared] using facts.2.2.1
  · intro other meaning
    exact LocalizedChemicalRingJointPreparedSourceModel.sourceModel_unique
      input.certified input.molecule input.agreement input.admissible input.supported input.single
      meaning.model facts.1

end
end TetraStereo.Engine.LocalizedChemicalRing

assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.Profile
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.Input
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.referenceCharge
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.admitRawSpatial?
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.admitSmilesSpatial?
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.analyze
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.analyze_eq_prepared
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.analyzeRawSpatial?
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.analyzeSmilesSpatial?
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.stereoOutcome
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.stereoAssignment
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.stereoAssignments
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.stereoOutcome_refused_iff
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.stereoAssignments_length
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.stereoAssignments_units
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.analyzeStereo
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.analyzeRawStereoSpatial?
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.analyzeSmilesStereoSpatial?
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.analyzeStereo_eq_prepared
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.analyzeRawSpatial?_eq_prepared
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.analyzeSmilesSpatial?_eq_prepared
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.analyze_length
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.analyze_indices_nodup
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.existsUnique_report_sourceModel
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.SourceMeaning
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.existsUnique_sourceMeaning
