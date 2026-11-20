import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelPhysicalReport
import TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionCancellation
import TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionApplicability
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The actual complete detected-center report, unique independent recursive model,
physical classification and fail-closed promotion cancellation in one theorem.
The cancellation clause retains the proved physical tied-root-branch scope. It is a
refinement to the explicit proposed-2018 aggregation, not an assertion that the accumulated
reference chronology is normative IUPAC chemistry. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCancellationReport

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingJointPreparedSourceQueries (SourceQuery)
open LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingJointPreparedSourceModelExistence
open LocalizedChemicalRingJointPreparedSourceModelPhysicalReport
open LocalizedChemicalRingJointPreparedReport
open LocalizedChemicalRingSourcePromotionCancellation
open LocalizedChemicalRingSourcePromotionApplicability
open LocalizedChemicalRingJointPreparedSourceStep (sourceKeysAt)
open DeclarativeCIP.ProductionOccurrenceRules456 (sourceRule6Applicable rule6GroupSizes)
open LocalizedChemicalRingInheritedRefusalCases (observedGeometry)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
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

include admissible supported charge calibrated in
/-- The exact actual report has a unique independent recursive meaning. At every properly
distinguishable detected center its descriptor exists and has the physical lowercase count.
Every auxiliary query in the physical branch scope satisfies the fail-closed cancellation
equation on its actual geometry and its mirror, with no supplied labels, balancing symmetry,
comparison strictness, successful sorting or desired result. -/
theorem existsUnique_cancellation_source_report :
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
          some (candidate (inputGeometry input) references query)) := by
  obtain ⟨candidate, ⟨model, report, physical⟩, unique⟩ :=
    existsUnique_sourceModel_physical_report input mol agreement admissible supported single
      charge cfg calibrated
  refine ⟨candidate, ⟨model, report, physical, ?_⟩, ?_⟩
  · intro query center current data branch boundary references history outside
    exact sourceModel_cancellation_equation input single mol agreement admissible supported
      charge cfg calibrated model query center current data branch boundary references history outside
  · intro other satisfied
    exact unique other ⟨satisfied.1, satisfied.2.1, satisfied.2.2.1⟩

include admissible supported charge calibrated in
/-- The complete report endpoint also derives the applicability gate: at every nonstrict
physical auxiliary comparison, either the independent current partition is source-applicable
or the independent model refuses. No selected-reference or partition-shape premise remains.
Final-root Rule 6 populations outside the properly-distinguishable success clause and the
normative status of the accumulated-reference chronology are not asserted here. -/
theorem existsUnique_cancellation_applicability_source_report :
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
          candidate (inputGeometry input) references query = none) := by
  obtain ⟨candidate, ⟨model, report, physical, cancellation⟩, unique⟩ :=
    existsUnique_cancellation_source_report input mol agreement admissible supported single
      charge cfg calibrated
  refine ⟨candidate, ⟨model, report, physical, cancellation, ?_⟩, ?_⟩
  · intro query center current data branch references reflected tied
    by_cases allowed : sourceRule6Applicable (rule6GroupSizes (sourceAdjacent input single
        (profileFamily input mol candidate query) data.target data.frame
        (observedGeometry input reflected) references)) = true
    · exact Or.inl allowed
    · exact Or.inr (sourceModel_refuses_of_inapplicable input single mol agreement admissible
        supported charge cfg calibrated model query center current data branch references reflected
        tied (Bool.eq_false_of_not_eq_true allowed))
  · intro other satisfied
    exact unique other ⟨satisfied.1, satisfied.2.1, satisfied.2.2.1, satisfied.2.2.2.1⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCancellationReport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCancellationReport.existsUnique_cancellation_source_report
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCancellationReport.existsUnique_cancellation_applicability_source_report
