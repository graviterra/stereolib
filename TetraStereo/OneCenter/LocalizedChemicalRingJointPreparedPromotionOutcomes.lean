import TetraStereo.OneCenter.LocalizedChemicalRingPromotionAggregation
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Failure-aware source outcomes for the actual generated-context promotion family.
An actual strict-key promotion with missing geometric readback is operationalFailure;
a completed noninjective key family is unresolved. On the admitted physical domain,
`fallback_none_iff` proves the first case cannot occur. Only then may actual optional
readings be fed to the completed-outcome cancellation adapter. No source promotion is
silently discarded as an operational failure, and no cancellation/consensus equivalence
or published-rule applicability is assumed here.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionOutcomes

open CertifiedLocalizedCIPInput
open DeclarativeCIP.ProductionOccurrenceRules456
open LocalizedChemicalRingPromotionAggregation
open LocalizedChemicalRingJointPreparedExecution
open LocalizedChemicalRingJointMarkerFrameExecution (selectedSlots)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData observedGeometry referenceAt)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (center : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol center node) (depth : Nat)
  (references : List input.Atom) (reflected : Bool)

/-- One promotion retains the distinction between a completed key tie and an execution failure. -/
def promotionOutcomeAt (slot : Fin 4) : PromotionOutcome :=
  if Function.Injective (keys input mol single center node data depth
      (observedGeometry input reflected) (references ++ [referenceAt input mol center node data slot]))
  then match fallback input mol center node data depth (observedGeometry input reflected)
      references slot with
    | none => .operationalFailure
    | some descriptor => .descriptor descriptor
  else .unresolved

def actualReadings : List (Option RS) :=
  (selectedSlots input mol single center node data
    (generated input mol depth (observedGeometry input reflected) node references) references).map
      (fallback input mol center node data depth (observedGeometry input reflected) references)

def actualOutcomes : List PromotionOutcome :=
  (selectedSlots input mol single center node data
    (generated input mol depth (observedGeometry input reflected) node references) references).map
      (promotionOutcomeAt input mol single center node data depth references reflected)

variable (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg center)

include agreement admissible supported calibrated in
/-- Actual calibrated promotions complete: an absent reading means precisely a nonunique
completed comparison, so the generic completed-outcome adapter is legitimate on this input. -/
theorem promotionOutcomeAt_eq_completed (slot : Fin 4) :
    promotionOutcomeAt input mol single center node data depth references reflected slot =
      completedOutcome (fallback input mol center node data depth
        (observedGeometry input reflected) references slot) := by
  have criterion := fallback_none_iff input mol agreement admissible supported single center node data
    depth references cfg calibrated reflected slot
  unfold promotionOutcomeAt
  by_cases injective : Function.Injective (keys input mol single center node data depth
      (observedGeometry input reflected) (references ++ [referenceAt input mol center node data slot]))
  · rw [if_pos injective]
    cases observed : fallback input mol center node data depth
        (observedGeometry input reflected) references slot with
    | none => exact False.elim ((criterion.mp observed) injective)
    | some descriptor => rfl
  · rw [if_neg injective, criterion.mpr injective]
    rfl

include agreement admissible supported calibrated in
/-- No promotion in this actual family has an operational failure. -/
theorem promotionOutcomeAt_ne_failure (slot : Fin 4) :
    promotionOutcomeAt input mol single center node data depth references reflected slot ≠
      .operationalFailure := by
  rw [promotionOutcomeAt_eq_completed input mol single center node data depth references reflected
    agreement admissible supported cfg calibrated slot]
  cases fallback input mol center node data depth (observedGeometry input reflected) references slot <;>
    simp [completedOutcome]

include agreement admissible supported calibrated in
/-- The full actual selected family, including completed nonunique promotions, is preserved. -/
theorem actualOutcomes_eq_completed :
    actualOutcomes input mol single center node data depth references reflected =
      (actualReadings input mol single center node data depth references reflected).map completedOutcome := by
  unfold actualOutcomes actualReadings
  rw [List.map_map]
  apply List.map_congr_left
  intro slot _
  exact promotionOutcomeAt_eq_completed input mol single center node data depth references reflected
    agreement admissible supported cfg calibrated slot

include agreement admissible supported calibrated in
/-- Applying the existing fail-closed source aggregation to actual promotion results is exactly
the completed-reading aggregate; the absence of failures is proved, not an adapter assumption. -/
theorem actualAggregate_eq_completed :
    promotionAggregate (actualOutcomes input mol single center node data depth references reflected) =
      completedAggregate (actualReadings input mol single center node data depth references reflected) := by
  rw [actualOutcomes_eq_completed input mol single center node data depth references reflected
    agreement admissible supported cfg calibrated]
  rfl

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionOutcomes

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionOutcomes.promotionOutcomeAt_eq_completed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionOutcomes.promotionOutcomeAt_ne_failure
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionOutcomes.actualOutcomes_eq_completed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionOutcomes.actualAggregate_eq_completed
