import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootClassReadings
import TetraStereo.OneCenter.LocalizedChemicalRingFourSlotPromotionBalance
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Final-root cancellation assembly

The actual odd-boundary population, the actual four-way tied case, and finite four-slot
cancellation are assembled here. Exactly one molecular obligation remains an explicit
argument: absent odd boundary and with nonconstant current keys, every selected promoted
fallback resolves. This module does not claim that obligation is already discharged.

No balance, uniformity, cross-class reading equality or desired descriptor is assumed.
The intended consumer supplies `resolution` from actual extended-context key transport and
the finite selected-stabilizer theorem.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootCancellationAssembly

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open DeclarativeCIP.ProductionOccurrenceRules456 (promotionAggregate)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData observedGeometry)
open LocalizedChemicalRingJointPreparedExecution (keys generated fallback step step_eq)
open LocalizedChemicalRingJointMarkerFrameExecution (selectedSlots)
open LocalizedChemicalRingJointPreparedPromotionOutcomes
  (actualOutcomes actualReadings actualAggregate_eq_completed)
open LocalizedChemicalRingJointPreparedRootPromotionCancellation
open LocalizedChemicalRingJointPreparedRootClassReadings
open LocalizedChemicalRingFourSlotPromotionBalance (resolved_partner_cancellation)
open LocalizedChemicalRingJointPreparedRefusalCharacterization (OddBoundarySymmetry)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open LocalizedGenericMarkedRecalculation (consensus structuralDepth)

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
/-- The final-root cancellation equation follows from the remaining actual selected-resolution
obligation. All other cases and the within-class reading connection are derived. -/
theorem actualAggregate_eq_consensus_of_root_resolution
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool)
    (resolution : ¬ OddBoundarySymmetry input cfg c [] references →
      (¬ ∀ i, keys input mol single c node data (structuralDepth mol node)
          (observedGeometry input reflected) references i =
        keys input mol single c node data (structuralDepth mol node)
          (observedGeometry input reflected) references 0) →
      ∀ i ∈ selectedSlots input mol single c node data
          (generated input mol (structuralDepth mol node)
            (observedGeometry input reflected) node references) references,
        fallback input mol c node data (structuralDepth mol node)
          (observedGeometry input reflected) references i ≠ none) :
    promotionAggregate (actualOutcomes input mol single c node data (structuralDepth mol node)
      references reflected) =
      some (consensus (actualReadings input mol single c node data (structuralDepth mol node)
        references reflected)) := by
  by_cases odd : OddBoundarySymmetry input cfg c [] references
  · exact actualAggregate_eq_consensus_of_rootOddBoundary input mol agreement admissible supported
      single cfg calibrated c node data reached current rootAddress references reflected odd
  · by_cases constant : ∀ i, keys input mol single c node data (structuralDepth mol node)
          (observedGeometry input reflected) references i =
        keys input mol single c node data (structuralDepth mol node)
          (observedGeometry input reflected) references 0
    · exact actualAggregate_eq_consensus_of_constant_root_keys input mol agreement admissible
        supported single charge cfg calibrated c node data reached current rootAddress references
        reflected constant
    · rw [actualAggregate_eq_completed input mol single c node data (structuralDepth mol node)
        references reflected agreement admissible supported cfg (calibrated c)]
      apply resolved_partner_cancellation _ _
        (selectedSlots_nodup input mol single c node data _ references)
        (resolution odd constant)
      intro i member
      obtain ⟨j, selectedJ, distinct, sameKey⟩ := selectedSlots_partner input mol single c node
        data _ references i member
      refine ⟨j, selectedJ, distinct, ?_⟩
      exact fallback_eq_of_root_key_eq input mol agreement admissible supported single charge cfg
        calibrated c node data reached current rootAddress references reflected odd j i sameKey

include agreement admissible supported charge calibrated in
/-- The same assembly supplies equality to the actual nonstrict root step. -/
theorem actualAggregate_eq_step_of_root_resolution
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (reached : Reached mol node)
    (current : node.atom = c.1.val) (rootAddress : data.target.1.address = [])
    (references : List input.Atom) (reflected : Bool)
    (tied : ¬ Function.Injective (keys input mol single c node data (structuralDepth mol node)
      (observedGeometry input reflected) references))
    (resolution : ¬ OddBoundarySymmetry input cfg c [] references →
      (¬ ∀ i, keys input mol single c node data (structuralDepth mol node)
          (observedGeometry input reflected) references i =
        keys input mol single c node data (structuralDepth mol node)
          (observedGeometry input reflected) references 0) →
      ∀ i ∈ selectedSlots input mol single c node data
          (generated input mol (structuralDepth mol node)
            (observedGeometry input reflected) node references) references,
        fallback input mol c node data (structuralDepth mol node)
          (observedGeometry input reflected) references i ≠ none) :
    promotionAggregate (actualOutcomes input mol single c node data (structuralDepth mol node)
      references reflected) =
      some (step input mol node (structuralDepth mol node)
        (observedGeometry input reflected) references) := by
  rw [step_eq input mol agreement admissible supported single c node data, if_neg tied]
  exact actualAggregate_eq_consensus_of_root_resolution input mol agreement admissible supported
    single charge cfg calibrated c node data reached current rootAddress references reflected
    resolution

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootCancellationAssembly

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootCancellationAssembly.actualAggregate_eq_consensus_of_root_resolution
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootCancellationAssembly.actualAggregate_eq_step_of_root_resolution
