import TetraStereo.OneCenter.IUPACP93AcyclicProductionCompleteness
import TetraStereo.OneCenter.IUPACP93MonocyclicProductionCompleteness
import TetraStereo.OneCenter.IUPACP93FusedCyclophaneProductionCompleteness
import TetraStereo.OneCenter.IUPACP93SpiroReadyProductionCompleteness
import TetraStereo.OneCenter.IUPACP93RingAssemblyProductionCompleteness
import TetraStereo.OneCenter.IUPACRemaining71P93CoupledRingChainReviewedSemantics

set_option autoImplicit false

/-!
# Closed production semantics for coupled ring/chain configurations

The P-93.6 validator composes the already proved family production relations carried by each
descriptor-evidence constructor.  The outer source core then verifies the exact reviewed printed
base name against its frozen source constitution, exhaustive stereogenic-unit coverage, citation
numbering, and multiplicative-component decision.  No reviewed provision judgment is called by
the production relation.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

def P93RingChainReviewedDescriptorEvidenceSourceCore
    {policies : P93CoupledRingChainDescriptorPolicies}
    (source : AuthoritativeChemicalInput) :
    P93RingChainReviewedDescriptorEvidence policies → Prop
  | .acyclicCenter observation =>
      Remaining71P93AcyclicAuthorityRow.ProductionJudges policies.acyclic
        .singleAcyclicCenter source observation
  | .acyclicDoubleBond observation =>
      Remaining71P93AcyclicAuthorityRow.ProductionJudges policies.acyclic
        .doubleBondEZCisTrans source observation
  | .acyclicEvenCumulene observation =>
      Remaining71P93AcyclicAuthorityRow.ProductionJudges policies.acyclic
        .evenCumulenes source observation
  | .acyclicOddCumulene observation =>
      Remaining71P93AcyclicAuthorityRow.ProductionJudges policies.acyclic
        .oddCumulenes source observation
  | .monocyclicCenter observation =>
      P93MonocyclicCenterSourceCore policies.monocyclic source observation
  | .monocyclicDoubleBond observation citation descriptor =>
      P93MonocyclicDoubleBondSourceCore policies.monocyclic source observation ∧
        observation.descriptor? = some descriptor ∧ citation.Valid
  | .fusedCIP observation =>
      P93FusedCIPSourceCore policies.fused source observation
  | .cyclophanePlane observation =>
      P93CyclophanePlaneSourceCore policies.cyclophane source observation
  | .cyclophaneCenterCIP observation context kind descriptor =>
      P93CyclophaneCenterSourceCore policies.cyclophane source observation ∧
        observation.specification = .cip context kind descriptor
  | .cyclophaneCenterRelative observation assignment =>
      P93CyclophaneCenterSourceCore policies.cyclophane source observation ∧
        ∃ candidates selected referenceSide assignments,
          observation.specification =
            .relativeRCT candidates selected referenceSide assignments ∧
          assignment ∈ assignments
  | .cyclophaneDoubleBond observation descriptor =>
      P93CyclophaneDoubleBondSourceCore policies.cyclophane source observation ∧
        observation.descriptor? = some descriptor
  | .spiroPolyhedral observation =>
      P93SpiroNontetrahedralSourceCore policies.spiro source observation
  | .ringAssemblyAxis observation assignment =>
      P93RingAssemblyAxesSourceCore policies.ringAssembly source observation ∧
        assignment ∈ observation.assignments
  | .ringAssemblyCenter observation assignment =>
      P93RingAssemblyCentersSourceCore policies.ringAssembly source observation ∧
        assignment ∈ observation.assignments
  | .ringAssemblyDoubleBond observation assignment =>
      P93RingAssemblyDoubleBondsSourceCore policies.ringAssembly source observation ∧
        assignment ∈ observation.assignments

theorem p93RingChainReviewedDescriptorEvidence_sourceCore_iff_validFor
    {policies : P93CoupledRingChainDescriptorPolicies}
    (source : AuthoritativeChemicalInput)
    (evidence : P93RingChainReviewedDescriptorEvidence policies) :
    P93RingChainReviewedDescriptorEvidenceSourceCore source evidence ↔
      evidence.ValidFor source := by
  cases evidence with
  | acyclicCenter observation =>
      exact Remaining71P93AcyclicAuthorityRow.production_eq_reference
        policies.acyclic .singleAcyclicCenter source observation
  | acyclicDoubleBond observation =>
      exact Remaining71P93AcyclicAuthorityRow.production_eq_reference
        policies.acyclic .doubleBondEZCisTrans source observation
  | acyclicEvenCumulene observation =>
      exact Remaining71P93AcyclicAuthorityRow.production_eq_reference
        policies.acyclic .evenCumulenes source observation
  | acyclicOddCumulene observation =>
      exact Remaining71P93AcyclicAuthorityRow.production_eq_reference
        policies.acyclic .oddCumulenes source observation
  | monocyclicCenter => rfl
  | monocyclicDoubleBond => rfl
  | fusedCIP observation =>
      exact p93FusedCIP_sourceCore_iff_validFor policies.fused source observation
  | cyclophanePlane observation =>
      exact p93CyclophanePlane_sourceCore_iff_validFor
        policies.cyclophane source observation
  | cyclophaneCenterCIP observation _context _kind _descriptor =>
      rw [P93RingChainReviewedDescriptorEvidenceSourceCore,
        P93RingChainReviewedDescriptorEvidence.ValidFor,
        p93CyclophaneCenter_sourceCore_iff_validFor]
  | cyclophaneCenterRelative observation _assignment =>
      rw [P93RingChainReviewedDescriptorEvidenceSourceCore,
        P93RingChainReviewedDescriptorEvidence.ValidFor,
        p93CyclophaneCenter_sourceCore_iff_validFor]
  | cyclophaneDoubleBond observation _descriptor =>
      rw [P93RingChainReviewedDescriptorEvidenceSourceCore,
        P93RingChainReviewedDescriptorEvidence.ValidFor,
        p93CyclophaneDoubleBond_sourceCore_iff_validFor]
  | spiroPolyhedral observation =>
      exact p93SpiroNontetrahedral_sourceCore_iff_validFor
        policies.spiro source observation
  | ringAssemblyAxis => rfl
  | ringAssemblyCenter => rfl
  | ringAssemblyDoubleBond => rfl

def P93RingChainDescriptorAssignmentSourceCore
    (policy : P93CoupledRingChainAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (baseName : P93RingChainBaseName)
    (assignment : P93RingChainDescriptorAssignment policy.descriptorPolicies) : Prop :=
  P93RingChainReviewedDescriptorEvidenceSourceCore source assignment.evidence ∧
    policy.StereogenicUnitEligible source baseName assignment.unit ∧
    policy.EvidenceBelongsToName source baseName assignment.evidence ∧
    match assignment.evidence.citation? with
    | none => True
    | some citation =>
        citation.Valid ∧
          policy.CitationConformsToBaseNumbering source baseName citation assignment.unit

theorem p93RingChainDescriptorAssignment_sourceCore_iff_validFor
    (policy : P93CoupledRingChainAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (baseName : P93RingChainBaseName)
    (assignment : P93RingChainDescriptorAssignment policy.descriptorPolicies) :
    P93RingChainDescriptorAssignmentSourceCore policy source baseName assignment ↔
      assignment.ValidFor policy source baseName := by
  rw [P93RingChainDescriptorAssignmentSourceCore,
    P93RingChainDescriptorAssignment.ValidFor,
    p93RingChainReviewedDescriptorEvidence_sourceCore_iff_validFor]
  rfl

def P93CoupledRingChainObservationSourceCore
    (policy : P93CoupledRingChainAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93CoupledRingChainAuthorityObservation policy) : Prop :=
  observation.reviewedBaseName.Valid ∧
    observation.baseNameCertificate.ValidFor source observation.reviewedBaseName ∧
    policy.ReviewedBaseNameMatchesSource source observation.reviewedBaseName ∧
    observation.annotatedBaseName = observation.reviewedBaseName ∧
    observation.assignments ≠ [] ∧
    (observation.assignments.map fun assignment =>
      assignment.unit.physicalIdentity).Nodup ∧
    (observation.assignments.filterMap fun assignment =>
      assignment.evidence.citation?).Nodup ∧
    (∀ assignment ∈ observation.assignments,
      P93RingChainDescriptorAssignmentSourceCore policy source
        observation.reviewedBaseName assignment) ∧
    (∀ unit,
      policy.StereogenicUnitEligible source observation.reviewedBaseName unit →
        ∃ assignment ∈ observation.assignments, assignment.unit = unit) ∧
    (observation.multiplicativeSelected = true ↔
      policy.MultiplicativeNameSelected source observation.reviewedBaseName) ∧
    policy.RepeatedComponentsObserved source observation.reviewedBaseName
      observation.repeatedComponents ∧
    P93RingChainMultiplicativeDecisionValid source observation.repeatedComponents
      observation.componentCorrespondences observation.assignments
      observation.assignmentOwnerships observation.multiplicativeSelected

theorem p93CoupledRingChainObservation_sourceCore_iff_validFor
    (policy : P93CoupledRingChainAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93CoupledRingChainAuthorityObservation policy) :
    P93CoupledRingChainObservationSourceCore policy source observation ↔
      observation.ValidFor policy source := by
  simp only [P93CoupledRingChainObservationSourceCore,
    P93CoupledRingChainAuthorityObservation.ValidFor,
    p93RingChainDescriptorAssignment_sourceCore_iff_validFor]

namespace Remaining71P93CoupledRingChainAuthorityRow

def ProductionJudges
    (policy : P93CoupledRingChainAuthorityPolicy) :
    (row : Remaining71P93CoupledRingChainAuthorityRow) →
      AuthoritativeChemicalInput → (row.reference policy).Observation → Prop
  | .configurations, source, observation =>
      P93CoupledRingChainObservationSourceCore policy source observation

theorem production_eq_reference
    (policy : P93CoupledRingChainAuthorityPolicy)
    (row : Remaining71P93CoupledRingChainAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation) :
    row.ProductionJudges policy source observation ↔
      (row.reference policy).Judges source observation := by
  cases row
  exact p93CoupledRingChainObservation_sourceCore_iff_validFor policy source observation

theorem reference_applicable_of_judged
    (policy : P93CoupledRingChainAuthorityPolicy)
    (row : Remaining71P93CoupledRingChainAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation)
    (judged : (row.reference policy).Judges source observation) :
    (row.reference policy).Applicable source := by
  cases row
  exact ⟨observation, judged⟩

end Remaining71P93CoupledRingChainAuthorityRow
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93CoupledRingChainAuthorityRow.production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93CoupledRingChainAuthorityRow.reference_applicable_of_judged
