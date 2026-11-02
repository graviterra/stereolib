import TetraStereo.OneCenter.IUPACRemaining71P93FullereneReviewedSemantics

set_option autoImplicit false

/-!
# Closed production semantics for the six P-93 fullerene provisions

This module composes the existing spatial, symmetry, molecular-cage, and local fullerene
analyzers.  Its production relations spell out the source envelope and consume actual analyzer
results; they do not call the reviewed `Judges` relation or either authority `ValidFor` relation.
-/

namespace TetraStereo.OneCenter

open BlueBookP93.Cyclic

namespace BlueBookP93.Cyclic

/-- Run the complete molecular fullerene analyzer after the spatial and symmetry admission
boundaries. -/
noncomputable def analyzeSpatiallyDerivedMolecularFullereneConfigurations
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (inputs : List SpatiallyDerivedMolecularFullereneConfigurationInput) :
    List FullereneConfigurationAssignment :=
  analyzeMolecularFullereneConfigurations molecule
    (validatedSymmetryDerivedMolecularFullereneConfigurationInputs molecule
      (validatedSpatiallyDerivedMolecularFullereneConfigurationInputs
        molecule spatial inputs))

/-- The composed analyzer emits exactly the independently judged assignments of the strict
spatial source family. -/
theorem mem_analyzeSpatiallyDerivedMolecularFullereneConfigurations_iff
    (molecule : RawMolecule)
    (spatial : SpatialConfiguration)
    (inputs : List SpatiallyDerivedMolecularFullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) :
    assignment ∈
        analyzeSpatiallyDerivedMolecularFullereneConfigurations molecule spatial inputs ↔
      SpatiallyDerivedMolecularFullereneConfigurationAssignmentJudgment
        molecule spatial inputs assignment := by
  rw [analyzeSpatiallyDerivedMolecularFullereneConfigurations,
    mem_analyzeMolecularFullereneConfigurations_iff,
    ← symmetryDerivedMolecularFullereneConfigurationAssignmentJudgment_iff_molecular,
    ← spatiallyDerivedMolecularFullereneConfigurationAssignmentJudgment_iff_symmetry]

end BlueBookP93.Cyclic

namespace IUPACNormativeProvision

/-- Source-only and exact-corpus facts retained by the relational production program.  Input,
local-assignment, and family-assignment judgments are intentionally absent: the executable
admission and analyzer equations below supply them independently. -/
def p93RelationalFullereneSourceEnvelope
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneAuthorityObservation policy) : Prop :=
  observation.molecule.MolecularFullereneTopologyRepresentationAgreement
      observation.selectedInput.symmetryInput.cage.carrier observation.spatial? source ∧
    policy.RawMoleculeObserved source observation.molecule ∧
    observation.inputs ≠ [] ∧
    policy.InputFamilyObserved source observation.molecule
      observation.spatial? observation.inputs ∧
    (∀ input ∈ observation.inputs,
      policy.InputObserved source observation.molecule observation.spatial? input) ∧
    (∀ input ∈ observation.inputs,
      match input.turnSource with
      | .supportingSpatial => True
      | .exterior sense =>
          policy.ExteriorFaceSenseObserved source observation.molecule input sense) ∧
    (∀ input ∈ observation.inputs,
      policy.OriginalDerivativeChiralityObserved source observation.molecule
        input.symmetryInput input.symmetryInput.evidence.originalDerivativeChiral) ∧
    (∀ input ∈ observation.inputs,
      policy.ChiralAddendsObserved source observation.molecule input.symmetryInput
        input.symmetryInput.evidence.chiralAddends) ∧
    observation.selectedInput ∈ observation.inputs ∧
    (match observation.selectedInput.turnSource with
      | .supportingSpatial => True
      | .exterior sense => policy.ExteriorFaceSenseObserved source observation.molecule
          observation.selectedInput sense) ∧
    policy.OriginalDerivativeChiralityObserved source observation.molecule
      observation.selectedInput.symmetryInput
      observation.selectedInput.symmetryInput.evidence.originalDerivativeChiral ∧
    policy.ChiralAddendsObserved source observation.molecule
      observation.selectedInput.symmetryInput
      observation.selectedInput.symmetryInput.evidence.chiralAddends ∧
    observation.addends = observation.selectedInput.symmetryInput.evidence.addends ∧
    observation.chiralAddends =
      observation.selectedInput.symmetryInput.evidence.chiralAddends ∧
    P93RelationalFullereneSubstituentCIPAssignmentsComplete policy source
      observation.molecule observation.selectedInput.symmetryInput
      observation.substituentAssignments

/-- The selected relational source record survives the exact source-orientation admission
boundary and returns its own cage. -/
def p93RelationalFullereneSelectedInputAccepted
    (policy : P93RelationalFullereneAuthorityPolicy)
    (observation : P93RelationalFullereneAuthorityObservation policy) : Prop :=
  relationalSourceOrientedMolecularFullereneConfigurationInput?
      observation.molecule observation.spatial? observation.selectedInput =
    some observation.selectedInput.symmetryInput.cage

/-- The local classifier/materializer emits the carried assignment for the selected cage. -/
def p93RelationalFullereneLocalAssignmentProduced
    (policy : P93RelationalFullereneAuthorityPolicy)
    (observation : P93RelationalFullereneAuthorityObservation policy) : Prop :=
  fullereneConfigurationAssignment?
      observation.selectedInput.symmetryInput.cage.toFullereneConfigurationInput =
    some observation.assignment

/-- The conflict-aware relational family analyzer emits the same carried assignment. -/
def p93RelationalFullereneFamilyAssignmentProduced
    (policy : P93RelationalFullereneAuthorityPolicy)
    (observation : P93RelationalFullereneAuthorityObservation policy) : Prop :=
  observation.assignment ∈
    analyzeP93RelationalFullereneAuthorityAssignments
      observation.molecule observation.spatial? observation.inputs

/-- Shared independent production core for relational cage-handedness observations. -/
def p93RelationalFullereneProductionCore
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneAuthorityObservation policy) : Prop :=
  p93RelationalFullereneSourceEnvelope policy source observation ∧
    p93RelationalFullereneSelectedInputAccepted policy observation ∧
    p93RelationalFullereneLocalAssignmentProduced policy observation ∧
    p93RelationalFullereneFamilyAssignmentProduced policy observation

/-- Closed production meaning of the printed four-way methodology.  It deliberately has no
molecule, spatial configuration, or cage assignment. -/
def p93FullereneMethodologyProductionCore
    (policy : P93FullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (_observation : P93FullereneMethodologyAuthorityObservation) : Prop :=
  policy.MethodologyRuleObserved source ∧
    P93FullereneFourWaySubstitutionDecisionRule

/-- Types 1--3 require the source-printed numbering handedness to agree literally with the
payload independently emitted by the relational molecule-bound analyzer. -/
def p93RelationalFullereneHandedProductionCore
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneHandedAuthorityObservation policy) : Prop :=
  p93RelationalFullereneProductionCore policy source observation.base ∧
    (observation.base.assignment.chiralityType = .inherentlyChiralParent ∨
      observation.base.assignment.chiralityType = .inherentlyChiralSubstitutionPattern ∨
      observation.base.assignment.chiralityType = .noninherentlyChiralSubstitutionPattern) ∧
    FullereneDescriptorPayload.cageHandedness observation.numberingKind
      observation.handedness ∈ observation.base.assignment.payloads ∧
    policy.PrintedCageHandednessObserved source observation.base.molecule
      observation.base.selectedInput observation.numberingKind observation.handedness

/-- Type 4 is produced directly from the symmetry-derived four-way test and the descriptor
materializer's CIP-only branch.  The explicit `none` equalities prevent cage handedness from
leaking into this row. -/
def p93RelationalFullereneType4ProductionCore
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneType4AuthorityObservation policy) : Prop :=
  observation.molecule.MolecularFullereneTopologyRepresentationAgreement
      observation.input.cage.carrier observation.spatial? source ∧
    policy.RawMoleculeObserved source observation.molecule ∧
    policy.Type4InputObserved source observation.molecule observation.input ∧
    policy.OriginalDerivativeChiralityObserved source observation.molecule observation.input
      observation.input.evidence.originalDerivativeChiral ∧
    policy.ChiralAddendsObserved source observation.molecule observation.input
      observation.input.evidence.chiralAddends ∧
    relationalSymmetryDerivedMolecularFullereneConfigurationInput?
      observation.molecule observation.input = some observation.input.cage ∧
    fullereneConfigurationAssignment? observation.input.cage.toFullereneConfigurationInput =
      some observation.assignment ∧
    observation.assignment.chiralityType = .chiralSubstituentsOnly ∧
    FullereneDescriptorPayload.substituentCIPComplete ∈ observation.assignment.payloads ∧
    observation.input.cage.descriptorEvidence.cageNumberingKind = none ∧
    observation.input.cage.descriptorEvidence.cageTurn = none ∧
    observation.input.evidence.chiralAddends.Nonempty ∧
    P93RelationalFullereneSubstituentCIPAssignmentsComplete policy source
      observation.molecule observation.input observation.substituentAssignments

/-- Independent production relation for the superimposed descriptor row. -/
def p93RelationalFullereneSuperimposedProductionCore
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneSuperimposedAuthorityObservation policy) : Prop :=
  p93RelationalFullereneHandedProductionCore policy source observation.handed ∧
    (observation.handed.base.assignment.chiralityType =
        .inherentlyChiralSubstitutionPattern ∨
      observation.handed.base.assignment.chiralityType =
        .noninherentlyChiralSubstitutionPattern) ∧
    observation.handed.base.selectedInput.symmetryInput.evidence.chiralAddends.Nonempty ∧
    SuperimposedFullereneConfigurationComplete true true

theorem p93RelationalFullereneProductionCore_iff_validFor
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneAuthorityObservation policy) :
    p93RelationalFullereneProductionCore policy source observation ↔
      observation.ValidFor policy source := by
  constructor
  · rintro ⟨⟨structureAgreement, moleculeObserved, inputsNonempty,
        inputFamilyObserved, inputsObserved, inputsExteriorFaceSenseObserved,
        inputsOriginalDerivativeChiralityObserved, inputsChiralAddendsObserved,
        selectedInputPresent, exteriorFaceSenseObserved,
        originalDerivativeChiralityObserved, chiralAddendsObserved, addendsExact,
        chiralAddendsExact, substituentCorpusComplete⟩,
      selectedInputAccepted, localAssignmentProduced, familyAssignmentProduced⟩
    exact
      { structureAgreement := structureAgreement
        moleculeObserved := moleculeObserved
        inputsNonempty := inputsNonempty
        inputFamilyObserved := inputFamilyObserved
        inputsObserved := inputsObserved
        inputsExteriorFaceSenseObserved := inputsExteriorFaceSenseObserved
        inputsOriginalDerivativeChiralityObserved :=
          inputsOriginalDerivativeChiralityObserved
        inputsChiralAddendsObserved := inputsChiralAddendsObserved
        selectedInputPresent := selectedInputPresent
        selectedInputJudged :=
          (relationalSourceOrientedMolecularFullereneConfigurationInput?_eq_some_iff
            observation.molecule observation.spatial? observation.selectedInput
              observation.selectedInput.symmetryInput.cage).1 selectedInputAccepted |>.1
        exteriorFaceSenseObserved := exteriorFaceSenseObserved
        originalDerivativeChiralityObserved := originalDerivativeChiralityObserved
        chiralAddendsObserved := chiralAddendsObserved
        addendsExact := addendsExact
        chiralAddendsExact := chiralAddendsExact
        localAssignmentJudged :=
          (fullereneConfigurationAssignment?_eq_some_iff
            observation.selectedInput.symmetryInput.cage.toFullereneConfigurationInput
              observation.assignment).1 localAssignmentProduced
        assignmentComplete :=
          (mem_analyzeP93RelationalFullereneAuthorityAssignments_iff
            observation.molecule observation.spatial? observation.inputs
              observation.assignment).1 familyAssignmentProduced
        substituentCorpusComplete := substituentCorpusComplete }
  · intro valid
    exact ⟨
      ⟨valid.structureAgreement, valid.moleculeObserved, valid.inputsNonempty,
        valid.inputFamilyObserved, valid.inputsObserved,
        valid.inputsExteriorFaceSenseObserved,
        valid.inputsOriginalDerivativeChiralityObserved,
        valid.inputsChiralAddendsObserved, valid.selectedInputPresent,
        valid.exteriorFaceSenseObserved, valid.originalDerivativeChiralityObserved,
        valid.chiralAddendsObserved, valid.addendsExact, valid.chiralAddendsExact,
        valid.substituentCorpusComplete⟩,
      (relationalSourceOrientedMolecularFullereneConfigurationInput?_eq_some_iff
        observation.molecule observation.spatial? observation.selectedInput
          observation.selectedInput.symmetryInput.cage).2 ⟨valid.selectedInputJudged, rfl⟩,
      (fullereneConfigurationAssignment?_eq_some_iff
        observation.selectedInput.symmetryInput.cage.toFullereneConfigurationInput
          observation.assignment).2 valid.localAssignmentJudged,
      (mem_analyzeP93RelationalFullereneAuthorityAssignments_iff
        observation.molecule observation.spatial? observation.inputs
          observation.assignment).2 valid.assignmentComplete⟩

theorem p93RelationalFullereneHandedProductionCore_iff_validFor
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneHandedAuthorityObservation policy) :
    p93RelationalFullereneHandedProductionCore policy source observation ↔
      observation.ValidFor policy source := by
  rw [p93RelationalFullereneHandedProductionCore,
    p93RelationalFullereneProductionCore_iff_validFor]
  constructor
  · rintro ⟨baseValid, handedClass, payloadPresent, printedObserved⟩
    exact ⟨baseValid, handedClass, payloadPresent, printedObserved⟩
  · intro valid
    exact ⟨valid.baseValid, valid.handedClass, valid.payloadPresent, valid.printedObserved⟩

theorem p93RelationalFullereneType4ProductionCore_iff_validFor
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneType4AuthorityObservation policy) :
    p93RelationalFullereneType4ProductionCore policy source observation ↔
      observation.ValidFor policy source := by
  constructor
  · rintro ⟨structureAgreement, moleculeObserved, inputObserved,
      originalDerivativeChiralityObserved, chiralAddendsObserved, inputAccepted,
      localAssignmentProduced, typeFour, cipPayloadPresent, numberingAbsent,
      turnAbsent, chiralAddendsNonempty, substituentCorpusComplete⟩
    exact
      { structureAgreement := structureAgreement
        moleculeObserved := moleculeObserved
        inputObserved := inputObserved
        inputJudged :=
          (relationalSymmetryDerivedMolecularFullereneConfigurationInput?_eq_some_iff
            observation.molecule observation.input observation.input.cage).1 inputAccepted |>.1
        originalDerivativeChiralityObserved := originalDerivativeChiralityObserved
        chiralAddendsObserved := chiralAddendsObserved
        localAssignmentJudged :=
          (fullereneConfigurationAssignment?_eq_some_iff
            observation.input.cage.toFullereneConfigurationInput observation.assignment).1
              localAssignmentProduced
        typeFour := typeFour
        cipPayloadPresent := cipPayloadPresent
        numberingAbsent := numberingAbsent
        turnAbsent := turnAbsent
        chiralAddendsNonempty := chiralAddendsNonempty
        substituentCorpusComplete := substituentCorpusComplete }
  · intro valid
    exact ⟨valid.structureAgreement, valid.moleculeObserved, valid.inputObserved,
      valid.originalDerivativeChiralityObserved, valid.chiralAddendsObserved,
      (relationalSymmetryDerivedMolecularFullereneConfigurationInput?_eq_some_iff
        observation.molecule observation.input observation.input.cage).2
          ⟨valid.inputJudged, rfl⟩,
      (fullereneConfigurationAssignment?_eq_some_iff
        observation.input.cage.toFullereneConfigurationInput observation.assignment).2
          valid.localAssignmentJudged,
      valid.typeFour, valid.cipPayloadPresent, valid.numberingAbsent, valid.turnAbsent,
      valid.chiralAddendsNonempty, valid.substituentCorpusComplete⟩

theorem p93RelationalFullereneSuperimposedProductionCore_iff_validFor
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RelationalFullereneSuperimposedAuthorityObservation policy) :
    p93RelationalFullereneSuperimposedProductionCore policy source observation ↔
      observation.ValidFor policy source := by
  rw [p93RelationalFullereneSuperimposedProductionCore,
    p93RelationalFullereneHandedProductionCore_iff_validFor]
  constructor
  · rintro ⟨handedValid, substitutionPatternClass, chiralAddendsNonempty, complete⟩
    exact ⟨handedValid, substitutionPatternClass, chiralAddendsNonempty, complete⟩
  · intro valid
    exact ⟨valid.handedValid, valid.substitutionPatternClass,
      valid.chiralAddendsNonempty, valid.complete⟩

namespace Remaining71P93FullereneAuthorityRow

/-- One closed family production program.  The four middle cases are projections of the same
computed assignment, not separate analyzers. -/
def ProductionJudges
    (legacy : P93FullereneAuthorityPolicy)
    (relational : P93RelationalFullereneAuthorityPolicy) :
    (row : Remaining71P93FullereneAuthorityRow) →
      AuthoritativeChemicalInput → (row.reference legacy relational).Observation → Prop
  | .generalMethodology, source, observation =>
      p93FullereneMethodologyProductionCore legacy source observation
  | .inherentParentChirality, source, observation =>
      p93RelationalFullereneHandedProductionCore relational source observation ∧
        observation.base.assignment.chiralityType = .inherentlyChiralParent
  | .inherentSubstitutionChirality, source, observation =>
      p93RelationalFullereneHandedProductionCore relational source observation ∧
        observation.base.assignment.chiralityType = .inherentlyChiralSubstitutionPattern
  | .noninherentSubstitutionChirality, source, observation =>
      p93RelationalFullereneHandedProductionCore relational source observation ∧
        observation.base.assignment.chiralityType = .noninherentlyChiralSubstitutionPattern
  | .chiralSubstituents, source, observation =>
      p93RelationalFullereneType4ProductionCore relational source observation
  | .superimposedStereogenicElements, source, observation =>
      p93RelationalFullereneSuperimposedProductionCore relational source observation

theorem production_eq_reference
    (legacy : P93FullereneAuthorityPolicy)
    (relational : P93RelationalFullereneAuthorityPolicy)
    (row : Remaining71P93FullereneAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference legacy relational).Observation) :
    row.ProductionJudges legacy relational source observation ↔
      (row.reference legacy relational).Judges source observation := by
  cases row <;>
    simp only [ProductionJudges, reference,
      p93FullereneGeneralMethodologyReference,
      p93RelationalFullereneTypeReference,
      p93RelationalFullereneType4Reference,
      p93RelationalFullereneSuperimposedReference]
  · simp only [p93FullereneMethodologyProductionCore,
      P93FullereneMethodologyAuthorityObservation.ValidFor]
  · rw [p93RelationalFullereneHandedProductionCore_iff_validFor]
    simp [P93FullereneCageHandednessType]
  · rw [p93RelationalFullereneHandedProductionCore_iff_validFor]
    simp [P93FullereneCageHandednessType]
  · rw [p93RelationalFullereneHandedProductionCore_iff_validFor]
    simp [P93FullereneCageHandednessType]
  · exact p93RelationalFullereneType4ProductionCore_iff_validFor
      relational source observation
  · exact p93RelationalFullereneSuperimposedProductionCore_iff_validFor
      relational source observation

/-- Every judged fullerene observation witnesses the existential applicability relation of its
row.  This is the provision-level bridge used when the family is installed in the global
interpreter. -/
theorem reference_applicable_of_judged
    (legacy : P93FullereneAuthorityPolicy)
    (relational : P93RelationalFullereneAuthorityPolicy)
    (row : Remaining71P93FullereneAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference legacy relational).Observation)
    (judged : (row.reference legacy relational).Judges source observation) :
    (row.reference legacy relational).Applicable source := by
  cases row with
  | generalMethodology => exact ⟨observation, judged⟩
  | inherentParentChirality => exact ⟨judged.1, observation, judged.2⟩
  | inherentSubstitutionChirality => exact ⟨judged.1, observation, judged.2⟩
  | noninherentSubstitutionChirality => exact ⟨judged.1, observation, judged.2⟩
  | chiralSubstituents => exact ⟨observation, judged⟩
  | superimposedStereogenicElements => exact ⟨observation, judged⟩

end Remaining71P93FullereneAuthorityRow
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.mem_analyzeSpatiallyDerivedMolecularFullereneConfigurations_iff
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93FullereneAuthorityRow.production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93FullereneAuthorityRow.reference_applicable_of_judged
