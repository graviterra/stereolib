import TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionCancellation
import TetraStereo.OneCenter.LocalizedChemicalRingThreeOnePartition
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionApplicability
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelRefusal
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The independent source-key partition and its actual generated-state realization.
Source applicability is evaluated on the full current source keys, not empty-state keys.
The comparison and successful sorted order are derived from the source-model realization. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionApplicability

open CertifiedLocalizedCIPInput
open DeclarativeCIP.ProductionOccurrenceRules456
open LocalizedGenericMarkedRecalculation (Geometry structuralDepth)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedChemicalRingJointPreparedSourceQueries (SourceQuery)
open LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingJointPreparedSourceModelExistence (sourceModel_eq_actual)
open LocalizedChemicalRingJointPreparedSourceStep
open LocalizedChemicalRingSourcePromotionCancellation (sourceModel_family_eq_generated)
open LocalizedChemicalRingJointPreparedExecution (generated)
open LocalizedChemicalRingJointMarkerFrameExecution (slotAdjacent slotKeys)
open LocalizedChemicalRingJointMarkerRanking (refined_compare_lt_iff refined_compare_eq_iff)
open LocalizedChemicalRingJointPreparedCorrectionWitness (sideState)
open LocalizedChemicalRingJointPreparedPromotionApplicability
  (exists_current_third_tied_slot_of_success)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRingInheritedRefusalCases (observedGeometry)
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingPreparedContextRecursion (preparedDescriptor?)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open LocalizedMarkedRetainedOrdinaryRanking (keyOrder adjacentBy)

noncomputable section

variable (input : CertifiedLocalizedCIPInput)
  (single : input.moleculeGraph.SimpleBonded)

/-- Adjacent decisions of the independent complete source-key ordering. -/
def sourceAdjacent (family : DescriptorFamily input)
    (target : input.LocalizedCIPOccurrence
      (LocalizedMarkedRetainedMolecularSelection.retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame
      (LocalizedMarkedRetainedMolecularSelection.retainedCarrierFuel input))
    (geom : Geometry) (references : List input.Atom) : List (Option Ordering) :=
  let keys := sourceKeysAt input single family target frame geom references
  adjacentBy (fun a b => some (compare (keys a) (keys b))) (keyOrder keys (List.finRange 4))

variable (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)

include agreement admissible supported in
/-- Every actual adjacent decision is the independent source decision. This includes equality
and all positions in the sorted order; no successful sorting or key-correspondence premise. -/
theorem sourceAdjacent_eq_actual {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (query : SourceQuery input mol)
    (center : input.detectedMultiCenterMolecule.Center)
    (data : OccurrenceData input mol center query.1)
    (geom : Geometry) (references : List input.Atom) :
    sourceAdjacent input single (profileFamily input mol candidate query)
      data.target data.frame geom references =
      slotAdjacent input mol single center query.1 data
        (generated input mol (structuralDepth mol query.1) geom query.1 references) references := by
  rw [sourceModel_family_eq_generated input single mol agreement admissible supported model query]
  unfold sourceAdjacent
  dsimp only
  rw [keyOrder_source_eq input mol single center query.1 data (structuralDepth mol query.1)
    geom references]
  have compares :
      (fun a b => some (compare
        (sourceKeysAt input single (generatedFamily input mol (structuralDepth mol query.1) query.1)
          data.target data.frame geom references a)
        (sourceKeysAt input single (generatedFamily input mol (structuralDepth mol query.1) query.1)
          data.target data.frame geom references b))) =
      (fun a b => some (compare
        (slotKeys input mol single center query.1 data
          (generated input mol (structuralDepth mol query.1) geom query.1 references) references a)
        (slotKeys input mol single center query.1 data
          (generated input mol (structuralDepth mol query.1) geom query.1 references) references b))) := by
    funext a b
    exact congrArg some (keys_compare_eq input mol single center query.1 data
      (structuralDepth mol query.1) geom references a b).symm
  rw [compares]

variable (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

include agreement admissible supported charge calibrated in
/-- A successful actual nonstrict auxiliary comparison has exactly the permitted three-plus-one
partition, for its current recursively generated state, on either observed geometry side. -/
theorem actualGroupSizes_three_one_of_success
    (query : SourceQuery input mol) (center : input.detectedMultiCenterMolecule.Center)
    (current : query.1.atom = center.1.val) (data : OccurrenceData input mol center query.1)
    (branch : TiedRootBranch input data.target) (references : List input.Atom) (reflected : Bool)
    (tied : ¬ Function.Injective (slotKeys input mol single center query.1 data
      (sideState input mol query.1 (inputGeometry input) references reflected) references))
    (success : ∃ descriptor, preparedDescriptor? mol (jointOperations input mol)
      (structuralDepth mol query.1) (inputGeometry input) [] (references.map Fin.val) query.1 =
        some descriptor) :
    let sizes := rule6GroupSizes (slotAdjacent input mol single center query.1 data
      (sideState input mol query.1 (inputGeometry input) references reflected) references)
    sizes = [3, 1] ∨ sizes = [1, 3] := by
  classical
  obtain ⟨left, right, equal, distinct⟩ := Function.not_injective_iff.mp tied
  obtain ⟨parent, _third, _parentClass, _thirdLeft, _thirdRight, _thirdParent,
      _thirdKey, _rightKey, outsideEqual, separated⟩ :=
    exists_current_third_tied_slot_of_success input mol agreement admissible supported single
      charge cfg calibrated query.1 query.2.1 center current data branch references reflected
      left right distinct equal success
  exact LocalizedChemicalRingThreeOnePartition.groupSizes_three_one compare
    refined_compare_lt_iff refined_compare_eq_iff _ parent left outsideEqual separated

include agreement admissible supported charge calibrated in
/-- The independent source partition of a successful auxiliary assignment has three equal
keys and a separated singleton. Both the selected class and all generated labels are derived. -/
theorem sourceGroupSizes_three_one_of_success {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (query : SourceQuery input mol)
    (center : input.detectedMultiCenterMolecule.Center) (current : query.1.atom = center.1.val)
    (data : OccurrenceData input mol center query.1) (branch : TiedRootBranch input data.target)
    (references : List input.Atom) (reflected : Bool)
    (tied : ¬ Function.Injective (sourceKeysAt input single
      (profileFamily input mol candidate query) data.target data.frame
      (observedGeometry input reflected) references))
    (success : ∃ descriptor, candidate (inputGeometry input) references query = some descriptor) :
    let sizes := rule6GroupSizes (sourceAdjacent input single
      (profileFamily input mol candidate query) data.target data.frame
      (observedGeometry input reflected) references)
    sizes = [3, 1] ∨ sizes = [1, 3] := by
  have actualSuccess : ∃ descriptor, preparedDescriptor? mol (jointOperations input mol)
      (structuralDepth mol query.1) (inputGeometry input) [] (references.map Fin.val) query.1 =
        some descriptor := by
    rw [sourceModel_eq_actual input mol agreement admissible supported single model] at success
    exact success
  have actualTie : ¬ Function.Injective (slotKeys input mol single center query.1 data
      (sideState input mol query.1 (inputGeometry input) references reflected) references) := by
    intro strict
    apply tied
    rw [sourceModel_family_eq_generated input single mol agreement admissible supported model query]
    exact (keys_injective_iff input mol single center query.1 data (structuralDepth mol query.1)
      (observedGeometry input reflected) references).mp strict
  dsimp only
  rw [sourceAdjacent_eq_actual input single mol agreement admissible supported model query center data]
  exact actualGroupSizes_three_one_of_success input single mol agreement admissible supported
    charge cfg calibrated query center current data branch references reflected actualTie actualSuccess

include agreement admissible supported charge calibrated in
/-- Nonstrict partitions outside the proposed-2018 applicability domain cannot emit a
descriptor in the independently defined source model. This concludes refusal, not an assumed
successful output, and includes the middle-pair case. -/
theorem sourceModel_refuses_of_inapplicable {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (query : SourceQuery input mol)
    (center : input.detectedMultiCenterMolecule.Center) (current : query.1.atom = center.1.val)
    (data : OccurrenceData input mol center query.1) (branch : TiedRootBranch input data.target)
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
      have groups := sourceGroupSizes_three_one_of_success input single mol agreement admissible
        supported charge cfg calibrated model query center current data branch references reflected
        tied ⟨descriptor, outcome⟩
      rcases groups with first | second
      · rw [first, sourceRule6Applicable_threeOne] at inapplicable
        cases inapplicable
      · rw [second, sourceRule6Applicable_oneThree] at inapplicable
        cases inapplicable

include agreement admissible supported charge calibrated in
/-- A physical absence of the refusal obstruction derives success and hence source
applicability whenever the current independent keys are nonstrict. No descriptor is supplied. -/
theorem sourceApplicable_of_no_oddBoundary {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (query : SourceQuery input mol)
    (center : input.detectedMultiCenterMolecule.Center) (current : query.1.atom = center.1.val)
    (data : OccurrenceData input mol center query.1) (branch : TiedRootBranch input data.target)
    (boundary references : List input.Atom)
    (history : data.target.1.node.history.reverse = boundary ++ [center.1])
    (outside : center.1 ∉ boundary) (reflected : Bool)
    (unobstructed : ¬ LocalizedChemicalRingJointPreparedRefusalCharacterization.OddBoundarySymmetry
      input cfg center boundary references)
    (tied : ¬ Function.Injective (sourceKeysAt input single
      (profileFamily input mol candidate query) data.target data.frame
      (observedGeometry input reflected) references)) :
    sourceRule6Applicable (rule6GroupSizes (sourceAdjacent input single
      (profileFamily input mol candidate query) data.target data.frame
      (observedGeometry input reflected) references)) = true := by
  have success := (LocalizedChemicalRingJointPreparedSourceModelRefusal.sourceModel_success_iff_no_oddBoundary
    input mol agreement admissible supported single charge cfg calibrated model query center
    current data branch boundary references history outside).mpr unobstructed
  rcases sourceGroupSizes_three_one_of_success input single mol agreement admissible supported
      charge cfg calibrated model query center current data branch references reflected tied success
    with first | second
  · rw [first, sourceRule6Applicable_threeOne]
  · rw [second, sourceRule6Applicable_oneThree]

end
end TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionApplicability

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionApplicability.sourceAdjacent_eq_actual
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionApplicability.actualGroupSizes_three_one_of_success
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionApplicability.sourceGroupSizes_three_one_of_success
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionApplicability.sourceModel_refuses_of_inapplicable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionApplicability.sourceApplicable_of_no_oddBoundary
assert_closure_excludes TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionApplicability.sourceAdjacent
  [TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueryMap.actualQueryProfile,
   TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution.generated,
   TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedDescriptor?]
