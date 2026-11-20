import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionOutcomes
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionBalance
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRefusalCharacterization
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual promotion-consensus refusal has an independent physical obstruction.
This is the molecular input to the promotion cancellation proof: the refused list is the
evaluator's own selected, extended-context fallback family, at its structural recursion depth.
Both geometry sides are covered, with one obstruction in the original physical configuration.
Actual selected-population transport then proves that the existing proposed-2018 cancellation
operation agrees exactly with actual consensus, including every refusal. No balanced-population
or physical-obstruction assumption remains in that equivalence. Rule applicability and the
published status of auxiliary recalculation remain separate questions.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionCancellation

open CertifiedLocalizedCIPInput
open DeclarativeCIP.ProductionOccurrenceRules456 (promotionAggregate)
open LocalizedChemicalRingPromotionAggregation (completedAggregate_eq_consensus)
open LocalizedChemicalRingJointPreparedPromotionBalance (actualReadings_perm_swap_of_oddBoundary)
open LocalizedChemicalRingJointPreparedPromotionOutcomes
open LocalizedChemicalRingJointPreparedExecution
open LocalizedChemicalRingJointPreparedRefusalCharacterization
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData observedGeometry)
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedGenericMarkedRecalculation (consensus structuralDepth)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

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
  (center : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol center node) (reached : Reached mol node)
  (real : node.provenance = .realAtom) (current : node.atom = center.1.val)
  (branch : TiedRootBranch input data.target) (boundary references : List input.Atom)
  (history : data.target.1.node.history.reverse = boundary ++ [center.1])
  (outside : center.1 ∉ boundary) (reflected : Bool)

include agreement admissible supported single charge calibrated reached real current branch history outside in
/-- A raw refusal on either geometry yields an odd boundary symmetry of the physical molecule. -/
theorem oddBoundary_of_step_refusal
    (refused : step input mol node (structuralDepth mol node)
      (observedGeometry input reflected) references = none) :
    OddBoundarySymmetry input cfg center boundary references := by
  apply oddBoundary_of_refusal input mol agreement admissible supported single charge cfg calibrated
    center node data reached real current branch boundary references history outside
  apply (descriptor_none_iff input mol node (structuralDepth mol node)
    (inputGeometry input) references).mpr
  cases reflected with
  | false => exact Or.inl refused
  | true => exact Or.inr refused

include agreement admissible supported charge calibrated reached real current branch history outside in
/-- A refused actual tied-branch promotion population derives the physical symmetry needed
for cancellation; neither a generic symmetry oracle nor a desired auxiliary label is supplied. -/
theorem oddBoundary_of_promotion_consensus_refusal
    (tied : ¬ Function.Injective (keys input mol single center node data (structuralDepth mol node)
      (observedGeometry input reflected) references))
    (refused : consensus (actualReadings input mol single center node data (structuralDepth mol node)
      references reflected) = none) :
    OddBoundarySymmetry input cfg center boundary references := by
  apply oddBoundary_of_step_refusal input mol agreement admissible supported single charge cfg calibrated
    center node data reached real current branch boundary references history outside reflected
  rw [step_eq input mol agreement admissible supported single center node data,
    if_neg tied]
  exact refused

include agreement admissible supported charge calibrated reached real current branch history outside in
/-- On the actual molecular promotion population, proposed-2018 cancellation is precisely
consensus. The formerly missing swap-balance premise is derived from refusal, molecular
symmetry and actual selected-list transport; success uses the existing unanimous-result law. -/
theorem actualAggregate_eq_consensus_of_tied
    (tied : ¬ Function.Injective (keys input mol single center node data (structuralDepth mol node)
      (observedGeometry input reflected) references)) :
    promotionAggregate (actualOutcomes input mol single center node data (structuralDepth mol node)
      references reflected) =
      some (consensus (actualReadings input mol single center node data (structuralDepth mol node)
        references reflected)) := by
  rw [actualAggregate_eq_completed input mol single center node data (structuralDepth mol node)
    references reflected agreement admissible supported cfg (calibrated center)]
  apply completedAggregate_eq_consensus
  intro refused
  have obstruction := oddBoundary_of_promotion_consensus_refusal input mol agreement admissible
    supported single charge cfg calibrated center node data reached real current branch boundary
    references history outside reflected tied refused
  exact actualReadings_perm_swap_of_oddBoundary input mol agreement admissible supported single cfg
    calibrated center node data reached current boundary references history outside
    (structuralDepth mol node) reflected obstruction

include agreement admissible supported charge calibrated reached real current branch history outside in
/-- The actual tied raw descriptor step implements the source cancellation result exactly.
An outer `some` certifies all promotions completed; the inner optional letter is unchanged. -/
theorem actualAggregate_eq_step_of_tied
    (tied : ¬ Function.Injective (keys input mol single center node data (structuralDepth mol node)
      (observedGeometry input reflected) references)) :
    promotionAggregate (actualOutcomes input mol single center node data (structuralDepth mol node)
      references reflected) =
      some (step input mol node (structuralDepth mol node) (observedGeometry input reflected)
        references) := by
  rw [step_eq input mol agreement admissible supported single center node data,
    if_neg tied]
  exact actualAggregate_eq_consensus_of_tied input mol agreement admissible supported single charge
    cfg calibrated center node data reached real current branch boundary references history outside
    reflected tied

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionCancellation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionCancellation.oddBoundary_of_step_refusal
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionCancellation.oddBoundary_of_promotion_consensus_refusal
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionCancellation.actualAggregate_eq_consensus_of_tied
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionCancellation.actualAggregate_eq_step_of_tied
