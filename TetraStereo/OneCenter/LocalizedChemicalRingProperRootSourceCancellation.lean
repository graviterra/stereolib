import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCancellationReport
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSuccess
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Source cancellation at physically properly distinguishable final roots.
Actual strictness on both geometry sides is derived, not supplied. This supplies the final-root
counterpart of the auxiliary cancellation equation on the established physical success domain.
Nonstrict final roots remain a separate problem; this theorem does not narrow their domain
or assert that source Rule 6 is unnecessary for them. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingProperRootSourceCancellation

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingJointPreparedSourceQueries (SourceQuery)
open LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingJointPreparedSourceModelExistence
open LocalizedChemicalRingJointPreparedSourceModelPhysicalReport
open LocalizedChemicalRingJointPreparedSourceStep
open LocalizedChemicalRingSourcePromotionCancellation
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData observedGeometry rank)
open LocalizedChemicalRingJointPreparedExecution (keys)
open LocalizedChemicalRingJointPreparedRootSuccess (root_tie_sourceProper)
open LocalizedChemicalRingJointPreparedRootInput (root_data)
open LocalizedChemicalRingJointPreparedReport (analyze)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedGenericMarkedRecalculation (structuralDepth mirror)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open MultiCenterMolecule (PairwiseProperDistinguishable)

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

include agreement admissible supported charge calibrated in
/-- Physical branch distinction derives the actual strict branch, on both geometry sides
and for every retained-reference context. No comparison/order/reading premise is supplied. -/
theorem properRoot_step_eq {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (query : SourceQuery input mol)
    (center : input.detectedMultiCenterMolecule.Center) (current : query.1.atom = center.1.val)
    (data : OccurrenceData input mol center query.1) (rootAddress : data.target.1.address = [])
    (properDistinct : PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg center)
    (references : List input.Atom) (reflected : Bool) :
    sourceCancellationStep input single (profileFamily input mol candidate query)
      data.target data.frame (observedGeometry input reflected) references =
      some (sourceStep input single (profileFamily input mol candidate query)
        data.target data.frame (observedGeometry input reflected) references) := by
  have injective := LocalizedChemicalRingJointPreparedRootAssignment.keys_injective input mol single
    cfg center query.1 data rootAddress current properDistinct references
    (root_tie_sourceProper input mol agreement admissible supported single charge cfg calibrated
      center query.1 data query.2.1 rootAddress references) reflected
  rw [sourceModel_family_eq_generated input single mol agreement admissible supported model query]
  rw [← step_eq_source input mol single center query.1 data (structuralDepth mol query.1)
    agreement admissible supported (observedGeometry input reflected) references]
  unfold sourceCancellationStep
  have sourceStrict := (keys_injective_iff input mol single center query.1 data
    (structuralDepth mol query.1) (observedGeometry input reflected) references).mp injective
  rw [if_pos sourceStrict, sourceReading_eq_enumeration,
    LocalizedChemicalRingJointPreparedExecution.step_eq input mol agreement admissible supported
      single center query.1 data, if_pos injective]
  obtain ⟨descriptor, read⟩ := LocalizedChemicalRingInheritedRefusalCases.readback_some input cfg center
    (calibrated center) reflected (rank input mol center query.1 data
      (keys input mol single center query.1 data (structuralDepth mol query.1)
        (observedGeometry input reflected) references))
  rw [read]
  rfl

include agreement admissible supported charge calibrated in
/-- At a properly distinguishable root, the cancellation prescription yields the exact
independent model value, with no operational failure. Its two sides regenerate their own maps. -/
theorem properRoot_cancellation_equation {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (query : SourceQuery input mol)
    (center : input.detectedMultiCenterMolecule.Center) (current : query.1.atom = center.1.val)
    (data : OccurrenceData input mol center query.1) (rootAddress : data.target.1.address = [])
    (properDistinct : PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg center)
    (references : List input.Atom) :
    sourceCancellationDescriptor input single (profileFamily input mol candidate query)
      data.target data.frame (inputGeometry input) references =
      some (candidate (inputGeometry input) references query) := by
  have first := properRoot_step_eq input mol agreement admissible supported single charge cfg
    calibrated model query center current data rootAddress properDistinct references false
  have second := properRoot_step_eq input mol agreement admissible supported single charge cfg
    calibrated model query center current data rootAddress properDistinct references true
  change sourceCancellationStep input single (profileFamily input mol candidate query)
    data.target data.frame (inputGeometry input) references = _ at first
  change sourceCancellationStep input single (profileFamily input mol candidate query)
    data.target data.frame (mirror (inputGeometry input)) references = _ at second
  unfold sourceCancellationDescriptor
  rw [first, second]
  exact congrArg some (model (inputGeometry input) references query center data)

include admissible supported charge calibrated in
/-- Construct the actual final frame and derive the cancellation reading, independent model
value, actual report entry and physical lowercase criterion together. No frame or label is
supplied by the caller. Absolute R/S is exactly the unique source-model reading. -/
theorem detected_root_cancellation_and_physical_report {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (center : input.detectedMultiCenterMolecule.Center)
    (properDistinct : PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg center) :
    ∃ (data : OccurrenceData input mol center (canonicalCenterRoot center.1.val))
      (descriptor : LocalizedTetrahedralRSPseudoDescriptor),
      sourceCancellationDescriptor input single
        (profileFamily input mol candidate (finalQuery input mol agreement center))
        data.target data.frame (inputGeometry input) [] = some (some descriptor) ∧
      candidate (inputGeometry input) [] (finalQuery input mol agreement center) = some descriptor ∧
      (center.1.val, some descriptor) ∈ analyze input mol ∧
      (descriptor.IsLowercase ↔
        physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule cfg center = 1) := by
  obtain ⟨data, rootAddress⟩ := root_data input mol agreement admissible supported single center
  obtain ⟨descriptor, source, member, lower⟩ := sourceModel_detected_entry input mol agreement
    admissible supported single charge cfg calibrated model center properDistinct
  have cancel := properRoot_cancellation_equation input mol agreement admissible supported single
    charge cfg calibrated model (finalQuery input mol agreement center) center rfl data rootAddress
    properDistinct []
  rw [source] at cancel
  exact ⟨data, descriptor, cancel, source, member, lower⟩

include admissible supported charge calibrated in
/-- Existence, uniqueness and complete detected inventory remove the model/frame/descriptor
parameters from the final-root conclusion. Every physically properly distinguishable root
gets the exact same descriptor from independent cancellation and the actual evaluator. -/
theorem existsUnique_root_cancellation_report :
    ∃! candidate : Profile input mol,
      SourceModel input mol single candidate ∧
      (∀ atom outcome, (atom, outcome) ∈ analyze input mol ↔
        ∃ center : input.detectedMultiCenterMolecule.Center, center.1.val = atom ∧
          candidate (inputGeometry input) [] (finalQuery input mol agreement center) = outcome) ∧
      (∀ center : input.detectedMultiCenterMolecule.Center,
        PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg center →
        ∃ (data : OccurrenceData input mol center (canonicalCenterRoot center.1.val))
          (descriptor : LocalizedTetrahedralRSPseudoDescriptor),
          sourceCancellationDescriptor input single
            (profileFamily input mol candidate (finalQuery input mol agreement center))
            data.target data.frame (inputGeometry input) [] = some (some descriptor) ∧
          candidate (inputGeometry input) [] (finalQuery input mol agreement center) = some descriptor ∧
          (center.1.val, some descriptor) ∈ analyze input mol ∧
          (descriptor.IsLowercase ↔
            physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule cfg center = 1)) := by
  obtain ⟨candidate, model, unique⟩ :=
    existsUnique_sourceModel input mol agreement admissible supported single
  refine ⟨candidate, ⟨model, ?_, ?_⟩, ?_⟩
  · exact mem_analyze_iff_sourceModel input mol agreement admissible supported single model
  · exact detected_root_cancellation_and_physical_report input mol agreement admissible supported
      single charge cfg calibrated model
  · intro other satisfied
    exact unique other satisfied.1

end
end TetraStereo.OneCenter.LocalizedChemicalRingProperRootSourceCancellation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingProperRootSourceCancellation.properRoot_step_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingProperRootSourceCancellation.properRoot_cancellation_equation
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingProperRootSourceCancellation.detected_root_cancellation_and_physical_report
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingProperRootSourceCancellation.existsUnique_root_cancellation_report
