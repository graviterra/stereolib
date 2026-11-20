import TetraStereo.OneCenter.LocalizedChemicalRingProperRootSourceCancellation
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSelectedResolution
import TetraStereo.OneCenter.LocalizedChemicalRingRootSourceApplicability
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Cancellation at every final root of the independent source model. Operational failure
remains `none`; a completed refusal is `some none`. Physical lowercase classification retains
its explicit properly distinguishable domain. No normative reference-policy claim is made. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingAllRootCancellationReport

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingJointPreparedSourceQueries (SourceQuery)
open LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingJointPreparedSourceModelExistence
open LocalizedChemicalRingJointPreparedSourceModelPhysicalReport
open LocalizedChemicalRingJointPreparedSourceStep
open LocalizedChemicalRingSourcePromotionCancellation
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData observedGeometry rank)
open LocalizedChemicalRingJointPreparedExecution (keys)
open LocalizedChemicalRingSourcePromotionApplicability (sourceAdjacent)
open DeclarativeCIP.ProductionOccurrenceRules456 (sourceRule6Applicable rule6GroupSizes)
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingJointPreparedRootInput (root_data)
open LocalizedChemicalRingJointPreparedReport (analyze)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedGenericMarkedRecalculation (structuralDepth mirror)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open MultiCenterMolecule (PairwiseProperDistinguishable)

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

include agreement admissible supported charge calibrated in
/-- Exact source cancellation step at every root, with no strictness or resolution premise. -/
theorem rootCancellationStep_eq_sourceStep {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (query : SourceQuery input mol)
    (center : input.detectedMultiCenterMolecule.Center) (current : query.1.atom = center.1.val)
    (data : OccurrenceData input mol center query.1) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool) :
    sourceCancellationStep input single (profileFamily input mol candidate query)
      data.target data.frame (observedGeometry input reflected) references =
      some (sourceStep input single (profileFamily input mol candidate query)
        data.target data.frame (observedGeometry input reflected) references) := by
  rw [sourceModel_family_eq_generated input single mol agreement admissible supported model query]
  rw [← step_eq_source input mol single center query.1 data (structuralDepth mol query.1)
    agreement admissible supported (observedGeometry input reflected) references]
  unfold sourceCancellationStep
  have injectivity := keys_injective_iff input mol single center query.1 data
    (structuralDepth mol query.1) (observedGeometry input reflected) references
  by_cases injective : Function.Injective (keys input mol single center query.1 data
      (structuralDepth mol query.1) (observedGeometry input reflected) references)
  · rw [if_pos (injectivity.mp injective), sourceReading_eq_enumeration,
      LocalizedChemicalRingJointPreparedExecution.step_eq input mol agreement admissible supported
        single center query.1 data, if_pos injective]
    obtain ⟨descriptor, read⟩ := LocalizedChemicalRingInheritedRefusalCases.readback_some input cfg center
      (calibrated center) reflected (rank input mol center query.1 data
        (keys input mol single center query.1 data (structuralDepth mol query.1)
          (observedGeometry input reflected) references))
    rw [read]
    rfl
  · rw [if_neg (fun h => injective (injectivity.mpr h)),
      sourcePromotionOutcomes_eq_actual input single mol agreement admissible supported]
    exact LocalizedChemicalRingJointPreparedRootSelectedResolution.actualAggregate_eq_step_of_root_tied
      input mol agreement admissible supported single charge cfg calibrated center query.1 data
      query.2.1 current rootAddress references reflected injective

include agreement admissible supported charge calibrated in
/-- All final roots satisfy the independent cancellation equation, including completed refusals. -/
theorem rootSourceModel_cancellation_equation {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (query : SourceQuery input mol)
    (center : input.detectedMultiCenterMolecule.Center) (current : query.1.atom = center.1.val)
    (data : OccurrenceData input mol center query.1) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) :
    sourceCancellationDescriptor input single (profileFamily input mol candidate query)
      data.target data.frame (inputGeometry input) references =
      some (candidate (inputGeometry input) references query) := by
  have first := rootCancellationStep_eq_sourceStep input single mol agreement admissible supported
    charge cfg calibrated model query center current data rootAddress references false
  have second := rootCancellationStep_eq_sourceStep input single mol agreement admissible supported
    charge cfg calibrated model query center current data rootAddress references true
  change sourceCancellationStep input single (profileFamily input mol candidate query)
    data.target data.frame (inputGeometry input) references = _ at first
  change sourceCancellationStep input single (profileFamily input mol candidate query)
    data.target data.frame (mirror (inputGeometry input)) references = _ at second
  unfold sourceCancellationDescriptor
  rw [first, second]
  exact congrArg some (model (inputGeometry input) references query center data)


include admissible supported charge calibrated in
/-- Unique exact report with auxiliary and all-root cancellation and applicability, including
refusals. Physical classification retains the established distinguishability hypothesis. -/
theorem existsUnique_allRoot_cancellation_applicability_source_report :
    ∃! candidate : Profile input mol,
      SourceModel input mol single candidate ∧
      (∀ atom outcome, (atom, outcome) ∈ analyze input mol ↔
        ∃ center : input.detectedMultiCenterMolecule.Center, center.1.val = atom ∧
          candidate (inputGeometry input) [] (finalQuery input mol agreement center) = outcome) ∧
      (∀ center : input.detectedMultiCenterMolecule.Center,
        PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg center →
        ∃ descriptor,
          candidate (inputGeometry input) [] (finalQuery input mol agreement center) =
            some descriptor ∧
          (center.1.val, some descriptor) ∈ analyze input mol ∧
          (descriptor.IsLowercase ↔
            physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule cfg center = 1)) ∧
      (∀ (query : SourceQuery input mol) (center : input.detectedMultiCenterMolecule.Center)
        (_current : query.1.atom = center.1.val)
        (data : OccurrenceData input mol center query.1)
        (_branch : TiedRootBranch input data.target) (boundary references : List input.Atom)
        (_history : data.target.1.node.history.reverse = boundary ++ [center.1])
        (_outside : center.1 ∉ boundary),
        sourceCancellationDescriptor input single (profileFamily input mol candidate query)
          data.target data.frame (inputGeometry input) references =
          some (candidate (inputGeometry input) references query)) ∧
      (∀ (query : SourceQuery input mol) (center : input.detectedMultiCenterMolecule.Center)
        (_current : query.1.atom = center.1.val)
        (data : OccurrenceData input mol center query.1)
        (_branch : TiedRootBranch input data.target) (references : List input.Atom)
        (reflected : Bool),
        ¬ Function.Injective (sourceKeysAt input single (profileFamily input mol candidate query)
          data.target data.frame (observedGeometry input reflected) references) →
        sourceRule6Applicable (rule6GroupSizes (sourceAdjacent input single
          (profileFamily input mol candidate query) data.target data.frame
          (observedGeometry input reflected) references)) = true ∨
          candidate (inputGeometry input) references query = none) ∧
      (∀ (query : SourceQuery input mol) (center : input.detectedMultiCenterMolecule.Center)
        (_current : query.1.atom = center.1.val)
        (data : OccurrenceData input mol center query.1)
        (_rootAddress : data.target.1.address = []) (references : List input.Atom),
        sourceCancellationDescriptor input single (profileFamily input mol candidate query)
          data.target data.frame (inputGeometry input) references =
          some (candidate (inputGeometry input) references query)) ∧
      (∀ (query : SourceQuery input mol) (center : input.detectedMultiCenterMolecule.Center)
        (_current : query.1.atom = center.1.val)
        (data : OccurrenceData input mol center query.1)
        (_rootAddress : data.target.1.address = []) (references : List input.Atom)
        (reflected : Bool),
        ¬ Function.Injective (sourceKeysAt input single (profileFamily input mol candidate query)
          data.target data.frame (observedGeometry input reflected) references) →
        sourceRule6Applicable (rule6GroupSizes (sourceAdjacent input single
          (profileFamily input mol candidate query) data.target data.frame
          (observedGeometry input reflected) references)) = true ∨
          candidate (inputGeometry input) references query = none) ∧
      (∀ center : input.detectedMultiCenterMolecule.Center,
        ∃ data : OccurrenceData input mol center (canonicalCenterRoot center.1.val),
          sourceCancellationDescriptor input single
            (profileFamily input mol candidate (finalQuery input mol agreement center))
            data.target data.frame (inputGeometry input) [] =
            some (candidate (inputGeometry input) [] (finalQuery input mol agreement center))) := by
  obtain ⟨candidate, ⟨model, report, physical, auxiliaryCancel, auxiliaryApplicable⟩, unique⟩ :=
    LocalizedChemicalRingJointPreparedCancellationReport.existsUnique_cancellation_applicability_source_report
      input mol agreement admissible supported single charge cfg calibrated
  refine ⟨candidate, ⟨model, report, physical, auxiliaryCancel, auxiliaryApplicable, ?_, ?_, ?_⟩, ?_⟩
  · intro query center current data rootAddress references
    exact rootSourceModel_cancellation_equation input single mol agreement admissible supported
      charge cfg calibrated model query center current data rootAddress references
  · intro query center current data rootAddress references reflected tied
    by_cases allowed : sourceRule6Applicable (rule6GroupSizes (sourceAdjacent input single
        (profileFamily input mol candidate query) data.target data.frame
        (observedGeometry input reflected) references)) = true
    · exact Or.inl allowed
    · exact Or.inr (LocalizedChemicalRingRootSourceApplicability.sourceRoot_refuses_of_inapplicable
        input mol agreement admissible supported single charge cfg calibrated model query center
        current data rootAddress references reflected tied (Bool.eq_false_of_not_eq_true allowed))
  · intro center
    obtain ⟨data, rootAddress⟩ := root_data input mol agreement admissible supported single center
    exact ⟨data, rootSourceModel_cancellation_equation input single mol agreement admissible supported
      charge cfg calibrated model (finalQuery input mol agreement center) center rfl data rootAddress []⟩
  · intro other satisfied
    exact unique other ⟨satisfied.1, satisfied.2.1, satisfied.2.2.1, satisfied.2.2.2.1,
      satisfied.2.2.2.2.1⟩


end
end TetraStereo.OneCenter.LocalizedChemicalRingAllRootCancellationReport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAllRootCancellationReport.rootCancellationStep_eq_sourceStep
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAllRootCancellationReport.rootSourceModel_cancellation_equation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAllRootCancellationReport.existsUnique_allRoot_cancellation_applicability_source_report
