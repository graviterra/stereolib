import TetraStereo.OneCenter.P94MolecularCoordinateFrameCompleteTransaction

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularCoordinateFrameCompleteTransactionConsistency

open CoordinateRing
open CoordinateTwistInOut
open P94CarbohydrateFiveRingTwist
open P94MolecularAuthoritativeRingSelection
open P94MolecularHybridRingSelection
open P94MolecularHybridOutcomeLedger
open P94MolecularAuditedHybridTransaction
open P94MolecularCoordinateFrameLedger
open P94MolecularCoordinateFrameCompleteTransaction

/-!
# Exact consistency of complete coordinate-frame result fields

The complete transaction carries a deduplicated public assignment report beside an occurrence-
preserving typed descriptor outcome ledger.  This module proves that those fields have exactly the
same successful descriptor semantics.  An accepted outcome supports an assignment precisely via
the existing independent P-94 conformation semantics for its evidence; a refused outcome supports
nothing.

Every public assignment is supported by some accepted outcome occurrence in the same transaction,
and every assignment supported by such an occurrence is public.  Duplicate-freedom of the public
field then turns this equivalence into exact count-one/count-zero characterizations.
-/

def DescriptorOutcomeSupportsAssignment
    (molecule : RawMolecule) (outcome : HybridMolecularOutcome Nat)
    (assignment : P94ConformationAssignment) : Prop :=
  match outcome with
  | .ringAccepted _ output =>
      IndependentP94ConformationAssignment molecule [output] assignment
  | .twistAccepted _ output =>
      IndependentP94ConformationAssignment molecule [output] assignment
  | .inOutAccepted _ output =>
      IndependentP94ConformationAssignment molecule [output] assignment
  | .carbohydrateAccepted _ output =>
      IndependentP94ConformationAssignment molecule [output] assignment
  | .refused _ => False

theorem descriptorOutcomeSupportsAssignment_refused
    (molecule : RawMolecule) (request : HybridMolecularRequest Nat)
    (assignment : P94ConformationAssignment) :
    ¬DescriptorOutcomeSupportsAssignment molecule (.refused request) assignment := by
  simp [DescriptorOutcomeSupportsAssignment]

private theorem analyzedDescriptorOutcome_mem_completeTransaction
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (request : HybridMolecularRequest Nat) (outcome : HybridMolecularOutcome Nat)
    (requestPresent : request ∈ hybridMolecularRequests certified.result.parsed
      (plan.toAuditedHybridLedgerPlan.toCompleteInOutLedgerPlan certified.result.parsed)
      external carbohydrateAuthority)
    (analyzed : analyzeHybridRequest premises certified.result.parsed plan.spatial
      carbohydrateAuthority request = outcome) :
    outcome ∈ (coordinateFrameCompleteTransaction premises certified plan external
      carbohydrateAuthority).descriptorOutcomes := by
  unfold coordinateFrameCompleteTransaction
  unfold auditedHybridMolecularOutcomes
  unfold hybridMolecularOutcomes
  exact List.mem_map.mpr ⟨request, requestPresent, analyzed⟩

theorem coordinateFrameCompleteTransaction_assignment_mem_iff_supported_descriptorOutcome
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    assignment ∈ (coordinateFrameCompleteTransaction premises certified plan external
        carbohydrateAuthority).assignments ↔
      ∃ outcome ∈ (coordinateFrameCompleteTransaction premises certified plan external
          carbohydrateAuthority).descriptorOutcomes,
        DescriptorOutcomeSupportsAssignment certified.result.parsed outcome assignment := by
  constructor
  · intro assignmentPresent
    have independent :=
      (coordinateFrameCompleteTransaction_assignments_mem_iff_independent premises certified plan
        external carbohydrateAuthority assignment).mp assignmentPresent
    rcases independent with ((ring | twist) | inOut) | carbohydrate
    · rcases ring with ⟨input, applies, output, judged, supported⟩
      have requestPresent : (.ring input : HybridMolecularRequest Nat) ∈
          hybridMolecularRequests certified.result.parsed
            (plan.toAuditedHybridLedgerPlan.toCompleteInOutLedgerPlan
              certified.result.parsed) external carbohydrateAuthority :=
        (hybridMolecularRequests_ring_mem_iff certified.result.parsed
          (plan.toAuditedHybridLedgerPlan.toCompleteInOutLedgerPlan certified.result.parsed)
          external carbohydrateAuthority input).mpr applies
      have computed := (automaticCoordinateRingEvidence?_eq_some_iff
        certified.result.parsed plan.spatial input output).mpr judged
      have analyzed : analyzeHybridRequest premises certified.result.parsed plan.spatial
          carbohydrateAuthority (.ring input : HybridMolecularRequest Nat) =
            .ringAccepted input output := by
        simp [analyzeHybridRequest, computed]
      exact ⟨.ringAccepted input output,
        analyzedDescriptorOutcome_mem_completeTransaction premises certified plan external
          carbohydrateAuthority (.ring input) (.ringAccepted input output) requestPresent analyzed,
        supported⟩
    · rcases twist with ⟨input, inputPresent, output, judged, supported⟩
      have requestPresent : (.twist input : HybridMolecularRequest Nat) ∈
          hybridMolecularRequests certified.result.parsed
            (plan.toAuditedHybridLedgerPlan.toCompleteInOutLedgerPlan
              certified.result.parsed) external carbohydrateAuthority :=
        (hybridMolecularRequests_twist_mem_iff certified.result.parsed
          (plan.toAuditedHybridLedgerPlan.toCompleteInOutLedgerPlan certified.result.parsed)
          external carbohydrateAuthority input).mpr inputPresent
      have computed := (coordinateTwistEvidence?_eq_some_iff
        certified.result.parsed input output).mpr judged
      have analyzed : analyzeHybridRequest premises certified.result.parsed plan.spatial
          carbohydrateAuthority (.twist input) = .twistAccepted input output := by
        simp [analyzeHybridRequest, computed]
      exact ⟨.twistAccepted input output,
        analyzedDescriptorOutcome_mem_completeTransaction premises certified plan external
          carbohydrateAuthority (.twist input) (.twistAccepted input output) requestPresent
          analyzed,
        supported⟩
    · rcases inOut with ⟨input, inputPresent, output, judged, supported⟩
      have requestPresent : (.inOut input : HybridMolecularRequest Nat) ∈
          hybridMolecularRequests certified.result.parsed
            (plan.toAuditedHybridLedgerPlan.toCompleteInOutLedgerPlan
              certified.result.parsed) external carbohydrateAuthority :=
        (hybridMolecularRequests_inOut_mem_iff certified.result.parsed
          (plan.toAuditedHybridLedgerPlan.toCompleteInOutLedgerPlan certified.result.parsed)
          external carbohydrateAuthority input).mpr inputPresent
      have computed := (coordinateInOutEvidence?_eq_some_iff premises
        certified.result.parsed input output).mpr judged
      have analyzed : analyzeHybridRequest premises certified.result.parsed plan.spatial
          carbohydrateAuthority (.inOut input : HybridMolecularRequest Nat) =
            .inOutAccepted input output := by
        simp [analyzeHybridRequest, computed]
      exact ⟨.inOutAccepted input output,
        analyzedDescriptorOutcome_mem_completeTransaction premises certified plan external
          carbohydrateAuthority (.inOut input) (.inOutAccepted input output) requestPresent
          analyzed,
        supported⟩
    · rcases carbohydrate with ⟨unit, applies, output, judged, supported⟩
      have requestPresent : (.carbohydrate unit : HybridMolecularRequest Nat) ∈
          hybridMolecularRequests certified.result.parsed
            (plan.toAuditedHybridLedgerPlan.toCompleteInOutLedgerPlan
              certified.result.parsed) external carbohydrateAuthority :=
        (hybridMolecularRequests_carbohydrate_mem_iff certified.result.parsed
          (plan.toAuditedHybridLedgerPlan.toCompleteInOutLedgerPlan certified.result.parsed)
          external carbohydrateAuthority unit).mpr applies
      have computed := (automaticCarbohydrateFiveRingTwistEvidence?_eq_some_iff
        carbohydrateAuthority certified.result.parsed plan.spatial unit output).mpr judged
      have analyzed : analyzeHybridRequest premises certified.result.parsed plan.spatial
          carbohydrateAuthority (.carbohydrate unit : HybridMolecularRequest Nat) =
            .carbohydrateAccepted unit output := by
        simp [analyzeHybridRequest, computed]
      exact ⟨.carbohydrateAccepted unit output,
        analyzedDescriptorOutcome_mem_completeTransaction premises certified plan external
          carbohydrateAuthority (.carbohydrate unit) (.carbohydrateAccepted unit output)
          requestPresent analyzed,
        supported⟩
  · rintro ⟨outcome, outcomePresent, supported⟩
    apply (coordinateFrameCompleteTransaction_assignments_mem_iff_independent premises certified
      plan external carbohydrateAuthority assignment).mpr
    have correct := coordinateFrameCompleteTransaction_descriptorOutcomes_all_correct premises
      certified plan external carbohydrateAuthority outcome outcomePresent
    have requestPresent := List.mem_map_of_mem
      (f := HybridMolecularOutcome.request) outcomePresent
    rw [coordinateFrameCompleteTransaction_descriptorOutcomes_map_request premises certified plan
      external carbohydrateAuthority] at requestPresent
    unfold auditedHybridMolecularRequests at requestPresent
    cases outcome with
    | ringAccepted input output =>
        have applies := (hybridMolecularRequests_ring_mem_iff certified.result.parsed
          (plan.toAuditedHybridLedgerPlan.toCompleteInOutLedgerPlan certified.result.parsed)
          external carbohydrateAuthority input).mp requestPresent
        exact Or.inl (Or.inl (Or.inl ⟨input, applies, output, correct, supported⟩))
    | twistAccepted input output =>
        have inputPresent := (hybridMolecularRequests_twist_mem_iff certified.result.parsed
          (plan.toAuditedHybridLedgerPlan.toCompleteInOutLedgerPlan certified.result.parsed)
          external carbohydrateAuthority input).mp requestPresent
        exact Or.inl (Or.inl (Or.inr ⟨input, inputPresent, output, correct, supported⟩))
    | inOutAccepted input output =>
        have inputPresent := (hybridMolecularRequests_inOut_mem_iff certified.result.parsed
          (plan.toAuditedHybridLedgerPlan.toCompleteInOutLedgerPlan certified.result.parsed)
          external carbohydrateAuthority input).mp requestPresent
        exact Or.inl (Or.inr ⟨input, inputPresent, output, correct, supported⟩)
    | carbohydrateAccepted unit output =>
        have applies := (hybridMolecularRequests_carbohydrate_mem_iff certified.result.parsed
          (plan.toAuditedHybridLedgerPlan.toCompleteInOutLedgerPlan certified.result.parsed)
          external carbohydrateAuthority unit).mp requestPresent
        exact Or.inr ⟨unit, applies, output, correct, supported⟩
    | refused request =>
        exact False.elim
          (descriptorOutcomeSupportsAssignment_refused certified.result.parsed request assignment
            supported)

def DescriptorOutcomeAccepted : HybridMolecularOutcome Nat → Prop
  | .ringAccepted _ _ => True
  | .twistAccepted _ _ => True
  | .inOutAccepted _ _ => True
  | .carbohydrateAccepted _ _ => True
  | .refused _ => False

theorem coordinateFrameCompleteTransaction_acceptedDescriptorOutcome_has_public_assignment
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (outcome : HybridMolecularOutcome Nat)
    (outcomePresent : outcome ∈
      (coordinateFrameCompleteTransaction premises certified plan external
        carbohydrateAuthority).descriptorOutcomes)
    (accepted : DescriptorOutcomeAccepted outcome) :
    ∃ assignment ∈ (coordinateFrameCompleteTransaction premises certified plan external
        carbohydrateAuthority).assignments,
      DescriptorOutcomeSupportsAssignment certified.result.parsed outcome assignment := by
  have correct := coordinateFrameCompleteTransaction_descriptorOutcomes_all_correct premises
    certified plan external carbohydrateAuthority outcome outcomePresent
  cases outcome with
  | ringAccepted input output =>
      rcases automaticCoordinateRingEvidenceJudgment_supports certified.result.parsed
        plan.spatial input output correct with ⟨valid, roles, descriptor, support⟩
      let assignment : P94ConformationAssignment :=
        { unit := output.unit, descriptor := descriptor }
      have supported : DescriptorOutcomeSupportsAssignment certified.result.parsed
          (.ringAccepted input output) assignment :=
        ⟨output, by simp, rfl, valid, roles, support⟩
      exact ⟨assignment,
        (coordinateFrameCompleteTransaction_assignment_mem_iff_supported_descriptorOutcome
          premises certified plan external carbohydrateAuthority assignment).mpr
          ⟨.ringAccepted input output, outcomePresent, supported⟩,
        supported⟩
  | twistAccepted input output =>
      rcases coordinateTwistEvidenceJudgment_supports_twist certified.result.parsed input output
        correct with ⟨valid, roles, support⟩
      let assignment : P94ConformationAssignment :=
        { unit := output.unit, descriptor := .twist }
      have supported : DescriptorOutcomeSupportsAssignment certified.result.parsed
          (.twistAccepted input output) assignment :=
        ⟨output, by simp, rfl, valid, roles, support⟩
      exact ⟨assignment,
        (coordinateFrameCompleteTransaction_assignment_mem_iff_supported_descriptorOutcome
          premises certified plan external carbohydrateAuthority assignment).mpr
          ⟨.twistAccepted input output, outcomePresent, supported⟩,
        supported⟩
  | inOutAccepted input output =>
      rcases coordinateInOutEvidenceJudgment_supports_inOut premises certified.result.parsed input
        output correct with ⟨valid, roles, support⟩
      let assignment : P94ConformationAssignment :=
        { unit := output.unit, descriptor := .inOut }
      have supported : DescriptorOutcomeSupportsAssignment certified.result.parsed
          (.inOutAccepted input output) assignment :=
        ⟨output, by simp, rfl, valid, roles, support⟩
      exact ⟨assignment,
        (coordinateFrameCompleteTransaction_assignment_mem_iff_supported_descriptorOutcome
          premises certified plan external carbohydrateAuthority assignment).mpr
          ⟨.inOutAccepted input output, outcomePresent, supported⟩,
        supported⟩
  | carbohydrateAccepted unit output =>
      rcases automaticCarbohydrateFiveRingTwistEvidenceJudgment_supports carbohydrateAuthority
        certified.result.parsed plan.spatial unit output correct with ⟨valid, roles, support⟩
      let assignment : P94ConformationAssignment :=
        { unit := output.unit, descriptor := .twist }
      have supported : DescriptorOutcomeSupportsAssignment certified.result.parsed
          (.carbohydrateAccepted unit output) assignment :=
        ⟨output, by simp, rfl, valid, roles, support⟩
      exact ⟨assignment,
        (coordinateFrameCompleteTransaction_assignment_mem_iff_supported_descriptorOutcome
          premises certified plan external carbohydrateAuthority assignment).mpr
          ⟨.carbohydrateAccepted unit output, outcomePresent, supported⟩,
        supported⟩
  | refused request =>
      exact False.elim accepted

theorem coordinateFrameCompleteTransaction_assignment_count_eq_one_iff_supported_descriptorOutcome
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    List.count assignment (coordinateFrameCompleteTransaction premises certified plan external
        carbohydrateAuthority).assignments = 1 ↔
      ∃ outcome ∈ (coordinateFrameCompleteTransaction premises certified plan external
          carbohydrateAuthority).descriptorOutcomes,
        DescriptorOutcomeSupportsAssignment certified.result.parsed outcome assignment := by
  exact (coordinateFrameCompleteTransaction_assignment_count_eq_one_iff premises certified plan
    external carbohydrateAuthority assignment).trans
    ((coordinateFrameCompleteTransaction_assignments_mem_iff_independent premises certified plan
      external carbohydrateAuthority assignment).symm.trans
      (coordinateFrameCompleteTransaction_assignment_mem_iff_supported_descriptorOutcome premises
        certified plan external carbohydrateAuthority assignment))

theorem coordinateFrameCompleteTransaction_assignment_count_eq_zero_iff_no_supported_descriptorOutcome
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    List.count assignment (coordinateFrameCompleteTransaction premises certified plan external
        carbohydrateAuthority).assignments = 0 ↔
      ¬∃ outcome ∈ (coordinateFrameCompleteTransaction premises certified plan external
          carbohydrateAuthority).descriptorOutcomes,
        DescriptorOutcomeSupportsAssignment certified.result.parsed outcome assignment := by
  apply (coordinateFrameCompleteTransaction_assignment_count_eq_zero_iff premises certified plan
    external carbohydrateAuthority assignment).trans
  apply not_congr
  exact (coordinateFrameCompleteTransaction_assignments_mem_iff_independent premises certified plan
    external carbohydrateAuthority assignment).symm.trans
    (coordinateFrameCompleteTransaction_assignment_mem_iff_supported_descriptorOutcome premises
      certified plan external carbohydrateAuthority assignment)

end BlueBookP94.P94MolecularCoordinateFrameCompleteTransactionConsistency
end TetraStereo.OneCenter
