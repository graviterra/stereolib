import TetraStereo.OneCenter.LocalizedChemicalRingRootApplicabilityFinite
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyCovariance
import TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionApplicability
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Source applicability at all final roots. A forbidden lone-pair partition forces an odd
actual molecular symmetry and hence completed refusal. Two-pair roots remain in scope.
This establishes applicability of the declared partition predicate, not source-policy fidelity. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingRootSourceApplicability

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open DeclarativeCIP.ProductionOccurrenceRules456
open LocalizedChemicalRingJointPreparedSourceQueries (SourceQuery)
open LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingJointPreparedSourceModelExistence (sourceModel_eq_actual)
open LocalizedChemicalRingJointPreparedSourceStep
open LocalizedChemicalRingSourcePromotionCancellation (sourceModel_family_eq_generated)
open LocalizedChemicalRingSourcePromotionApplicability (sourceAdjacent sourceAdjacent_eq_actual)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt observedGeometry)
open LocalizedChemicalRingJointPreparedExecution (keys)
open LocalizedChemicalRingJointMarkerFrameExecution (slotAdjacent)
open LocalizedChemicalRingJointMarkerRanking (refined_compare_lt_iff refined_compare_eq_iff)
open LocalizedChemicalRingJointPreparedRootPromotionCancellation (root_tie_boundaryProper)
open LocalizedChemicalRingJointPreparedRootPhysicalTransport (root_history)
open LocalizedChemicalRingJointPreparedRootKeyCovariance (root_current_key_action)
open LocalizedChemicalRingResidualThreeCycleRefusal (slotAction referenceAt_action center_fixed)
open LocalizedChemicalRingJointPreparedRefusalCharacterization (OddBoundarySymmetry refusal_of_oddBoundary)
open LocalizedChemicalRingRootApplicabilityFinite
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPreparedContextRecursion (preparedDescriptor?)
open LocalizedChemicalRingPhysicalSense (inputGeometry relabelOf relabelOf_val)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

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
/-- A nonstrict root outside the allowed partition shapes refuses. Every symmetry and key
preservation fact is derived from the actual current recursively generated state. -/
theorem actualRoot_refuses_of_inapplicable
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool)
    (tied : ¬ Function.Injective (keys input mol single c node data (structuralDepth mol node)
      (observedGeometry input reflected) references))
    (inapplicable : sourceRule6Applicable (rule6GroupSizes (slotAdjacent input mol single c node data
      (LocalizedChemicalRingJointPreparedCorrectionWitness.sideState input mol node
        (inputGeometry input) references reflected) references)) = false) :
    preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
      (inputGeometry input) [] (references.map Fin.val) node = none := by
  obtain ⟨left, right, tie, distinct⟩ := Function.not_injective_iff.mp tied
  obtain ⟨e, fixed, moved, keeps, proper⟩ := root_tie_boundaryProper input mol agreement admissible
    supported single charge cfg calibrated c node data reached rootAddress current references
    reflected left right distinct tie
  have rawFixed : ∀ value ∈ node.history,
      relabelOf input (e : Equiv.Perm input.Atom) value = value := by
    intro value member
    rw [← (LocalizedMarkedCarrierLookup.lookup?_sound input node data.target data.found).history] at member
    obtain ⟨atom, present, rfl⟩ := List.mem_map.mp member
    rw [relabelOf_val, fixed atom present]
  have fixedCenter := center_fixed input mol e c node reached current rawFixed
  have actionMoves : slotAction input mol e c node data left ≠ left := by
    intro equal
    have h := referenceAt_action input mol e c node data fixedCenter left
    rw [equal, moved] at h
    exact distinct (LocalizedChemicalRingProperRotationConsensus.referenceAt_injective
      input mol c node data h)
  have onlyPair := only_pair_of_inapplicable compare refined_compare_lt_iff refined_compare_eq_iff
    (keys input mol single c node data (structuralDepth mol node)
      (observedGeometry input reflected) references) left right distinct tie inapplicable
  have oddAction := lone_pair_action_odd _ (slotAction input mol e c node data) left right
    distinct actionMoves (root_current_key_action input mol agreement admissible supported single
      cfg calibrated c node data reached current rootAddress e fixed references keeps proper
      (structuralDepth mol node) reflected) onlyPair
  have odd : relativeSign input.detectedMultiCenterMolecule cfg e c = -1 := by
    rw [LocalizedChemicalRingCompletenessOrbit.relativeSign_fixed input cfg e c fixedCenter]
    have compose : slotAction input mol e c node data =
        data.ligandOf⁻¹ * input.detectedMultiCenterMolecule.ligandPermAt e c * data.ligandOf := by
      ext i
      rfl
    rw [compose, permHandedness_conj_inv] at oddAction
    exact oddAction
  have history := root_history input mol c node data rootAddress current
  apply refusal_of_oddBoundary input mol agreement admissible supported single cfg calibrated
    c node data reached current [] references (by simp [history]) (by simp)
  refine ⟨e, ?_, keeps, odd, ?_⟩
  · simpa only [List.nil_append, ← history] using fixed
  · simpa only [List.nil_append, ← history] using proper


include agreement admissible supported charge calibrated in
/-- Successful actual nonstrict root execution derives the source applicability gate. -/
theorem actualRoot_applicable_of_success
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool)
    (tied : ¬ Function.Injective (keys input mol single c node data (structuralDepth mol node)
      (observedGeometry input reflected) references))
    (success : ∃ descriptor, preparedDescriptor? mol (jointOperations input mol)
      (structuralDepth mol node) (inputGeometry input) [] (references.map Fin.val) node =
        some descriptor) :
    sourceRule6Applicable (rule6GroupSizes (slotAdjacent input mol single c node data
      (LocalizedChemicalRingJointPreparedCorrectionWitness.sideState input mol node
        (inputGeometry input) references reflected) references)) = true := by
  cases gate : sourceRule6Applicable (rule6GroupSizes (slotAdjacent input mol single c node data
      (LocalizedChemicalRingJointPreparedCorrectionWitness.sideState input mol node
        (inputGeometry input) references reflected) references)) with
  | true => rfl
  | false =>
      have refused := actualRoot_refuses_of_inapplicable input mol agreement admissible supported
        single charge cfg calibrated c node data reached current rootAddress references reflected
        tied gate
      obtain ⟨descriptor, assigned⟩ := success
      rw [assigned] at refused
      cases refused


include agreement admissible supported charge calibrated in
/-- Independent source keys at every successful nonstrict final root satisfy the exact
applicability predicate. Recursive state and actual sorting are derived from the model. -/
theorem sourceRoot_applicable_of_success {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (query : SourceQuery input mol)
    (c : input.detectedMultiCenterMolecule.Center) (current : query.1.atom = c.1.val)
    (data : OccurrenceData input mol c query.1) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool)
    (tied : ¬ Function.Injective (sourceKeysAt input single
      (profileFamily input mol candidate query) data.target data.frame
      (observedGeometry input reflected) references))
    (success : ∃ descriptor, candidate (inputGeometry input) references query = some descriptor) :
    sourceRule6Applicable (rule6GroupSizes (sourceAdjacent input single
      (profileFamily input mol candidate query) data.target data.frame
      (observedGeometry input reflected) references)) = true := by
  have actualSuccess : ∃ descriptor, preparedDescriptor? mol (jointOperations input mol)
      (structuralDepth mol query.1) (inputGeometry input) [] (references.map Fin.val) query.1 =
        some descriptor := by
    rw [sourceModel_eq_actual input mol agreement admissible supported single model] at success
    exact success
  have actualTie : ¬ Function.Injective (keys input mol single c query.1 data
      (structuralDepth mol query.1) (observedGeometry input reflected) references) := by
    intro strict
    apply tied
    rw [sourceModel_family_eq_generated input single mol agreement admissible supported model query]
    exact (keys_injective_iff input mol single c query.1 data (structuralDepth mol query.1)
      (observedGeometry input reflected) references).mp strict
  rw [sourceAdjacent_eq_actual input single mol agreement admissible supported model query c data]
  exact actualRoot_applicable_of_success input mol agreement admissible supported single charge cfg
    calibrated c query.1 data query.2.1 current rootAddress references reflected actualTie actualSuccess

include agreement admissible supported charge calibrated in
/-- Inapplicable independent source partitions force completed source-model refusal at roots. -/
theorem sourceRoot_refuses_of_inapplicable {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (query : SourceQuery input mol)
    (c : input.detectedMultiCenterMolecule.Center) (current : query.1.atom = c.1.val)
    (data : OccurrenceData input mol c query.1) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool)
    (tied : ¬ Function.Injective (sourceKeysAt input single
      (profileFamily input mol candidate query) data.target data.frame
      (observedGeometry input reflected) references))
    (inapplicable : sourceRule6Applicable (rule6GroupSizes (sourceAdjacent input single
      (profileFamily input mol candidate query) data.target data.frame
      (observedGeometry input reflected) references)) = false) :
    candidate (inputGeometry input) references query = none := by
  cases outcome : candidate (inputGeometry input) references query with
  | none => rfl
  | some descriptor =>
      have applicable := sourceRoot_applicable_of_success input mol agreement admissible supported
        single charge cfg calibrated model query c current data rootAddress references reflected
        tied ⟨descriptor, outcome⟩
      rw [applicable] at inapplicable
      cases inapplicable

end
end TetraStereo.OneCenter.LocalizedChemicalRingRootSourceApplicability

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootSourceApplicability.actualRoot_refuses_of_inapplicable

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootSourceApplicability.actualRoot_applicable_of_success

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootSourceApplicability.sourceRoot_applicable_of_success
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootSourceApplicability.sourceRoot_refuses_of_inapplicable
