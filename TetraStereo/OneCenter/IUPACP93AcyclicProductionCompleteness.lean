import TetraStereo.OneCenter.IUPACP93AcyclicReadyProductionCompleteness

set_option autoImplicit false

/-!
# Closed production semantics for all eleven acyclic P-93 provisions

The existing three evaluator-backed rows are joined with eight source/core rows.  Every branch
uses the common physical/assignment envelope and exposes the finite naming, placement, topology,
and numbering rules directly.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open BlueBookP93.Acyclic

def P93AcyclicAssignmentProductionCore
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assignment : P93AcyclicAuthorityAssignment policy) : Prop :=
  P93AcyclicAssignmentSourceEnvelope policy source assignment ∧
    DescriptorApplies assignment.kind assignment.descriptor

theorem p93AcyclicAssignmentProductionCore_iff_validFor
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assignment : P93AcyclicAuthorityAssignment policy) :
    P93AcyclicAssignmentProductionCore policy source assignment ↔
      assignment.ValidFor policy source :=
  (p93AcyclicAuthorityAssignment_validFor_iff_sourceEnvelope
    policy source assignment).symm

def P93AcyclicSingleCenterSourceCore
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicSingleCenterAuthorityObservation policy) : Prop :=
  P93AcyclicAssignmentProductionCore policy source observation.assignment ∧
    (observation.assignment.kind = .chiralCenter ∨
      observation.assignment.kind = .pseudoasymmetricCenter) ∧
    SingleCenterLocantConforms
      { descriptor := observation.assignment.descriptor
        locant? := observation.assignment.citation?
        centerNeedsLocantInBaseName := observation.centerNeedsLocantInBaseName } ∧
    policy.SingleCenterNamingObserved source observation.assignment.unit
      observation.assignment.citation? observation.centerNeedsLocantInBaseName
      observation.isotopicAffixPresent observation.observedAffixOrder ∧
    P93AcyclicAffixOrderConforms observation.observedAffixOrder ∧
    .stereochemical ∈ observation.observedAffixOrder ∧
    (observation.isotopicAffixPresent = true ↔ .isotopic ∈ observation.observedAffixOrder)

def P93AcyclicMultipleDescriptorsSourceCore
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicMultipleCenterDescriptorsAuthorityObservation policy) : Prop :=
  observation.assignments ≠ [] ∧
    (∀ assignment ∈ observation.assignments,
      P93AcyclicAssignmentProductionCore policy source assignment) ∧
    2 ≤ observation.assignments.length ∧
    (∀ assignment ∈ observation.assignments,
      assignment.kind = .chiralCenter ∨
        assignment.kind = .pseudoasymmetricCenter) ∧
    (observation.assignments.map fun assignment => assignment.unit).Nodup ∧
    (∀ assignment ∈ observation.assignments,
      ∃ citation, assignment.citation? = some citation) ∧
    (P93AcyclicPresentCitations observation.assignments).Nodup ∧
    (P93AcyclicPresentCitations observation.assignments).Pairwise
      P93AuthorityCitationToken.CitationLE ∧
    policy.MultipleCenterDescriptorsAuthorized source
      (P93AcyclicAssignmentTriples observation.assignments)

def P93AcyclicPrefixComponentSourceCore
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicPrefixComponentAuthorityObservation policy) : Prop :=
  P93AcyclicAssignmentProductionCore policy source observation.assignment ∧
    CorrectComponentPlacement
      { locant := observation.assignment.citation?
        component := observation.assignment.component
        kind := observation.assignment.kind
        descriptor := observation.assignment.descriptor }
      observation.observedPosition ∧
    (observation.assignment.kind = .chiralCenter ∨
      observation.assignment.kind = .pseudoasymmetricCenter)

def P93AcyclicDoubleBondSourceCore
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicDoubleBondAuthorityObservation policy) : Prop :=
  P93AcyclicAssignmentProductionCore policy source observation.assignment ∧
    observation.assignment.kind = .ordinaryDoubleBond ∧
    policy.CarbonDoubleBondContextObserved source observation.assignment.unit
      observation.carbonContext ∧
    DescriptorRecommended observation.context .ordinaryDoubleBond
      observation.assignment.descriptor ∧
    ((observation.assignment.descriptor = .cis ∨
      observation.assignment.descriptor = .trans) →
        CisTransGeneralApplicable observation.carbonContext)

def P93AcyclicMultipleDoubleBondSourceCore
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicMultipleDoubleBondAuthorityObservation policy) : Prop :=
  observation.assignments ≠ [] ∧
    (∀ assignment ∈ observation.assignments,
      P93AcyclicAssignmentProductionCore policy source assignment) ∧
    2 ≤ observation.assignments.length ∧
    (∀ assignment ∈ observation.assignments,
      assignment.kind = .ordinaryDoubleBond ∨
        assignment.kind = .heteroatomDoubleBond) ∧
    (observation.assignments.map fun assignment => assignment.unit).Nodup ∧
    (∀ assignment ∈ observation.assignments,
      ∃ citation, assignment.citation? = some citation) ∧
    (P93AcyclicPresentCitations observation.assignments).Nodup ∧
    (P93AcyclicPresentCitations observation.assignments).Pairwise
      P93AuthorityCitationToken.CitationLE ∧
    policy.MultipleDoubleBondDescriptorsAuthorized source
      (P93AcyclicAssignmentTriples observation.assignments)

def P93AcyclicMultipleUnitsSourceCore
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicMultipleUnitsAuthorityObservation policy) : Prop :=
  2 ≤ observation.assignments.length ∧
    (∀ placed ∈ observation.assignments,
      P93AcyclicAssignmentProductionCore policy source placed.assignment ∧
        ∃ citation, placed.assignment.citation? = some citation ∧
          P93AcyclicGroupedDescriptorPlacement
            { locant := citation
              component := placed.assignment.component
              kind := placed.assignment.kind
              descriptor := placed.assignment.descriptor }
            placed.observedPosition) ∧
    (observation.assignments.map fun placed => placed.assignment.unit).Nodup ∧
    (P93AcyclicPresentCitations
      (observation.assignments.map fun placed => placed.assignment)).Nodup ∧
    (P93AcyclicPresentCitations
      (observation.assignments.map fun placed => placed.assignment)).Pairwise
        P93AuthorityCitationToken.CitationLE ∧
    policy.NumberingCompetitionObserved source
      (observation.assignments.map fun placed =>
        (placed.assignment.unit, placed.assignment.citation?))
      observation.numberingCompetition ∧
    match observation.numberingCompetition with
    | .unique => True
    | .competing alternativeCitations firstDifference =>
        alternativeCitations.Nodup ∧
          alternativeCitations.Perm
            (P93AcyclicPresentCitations
              (observation.assignments.map fun placed => placed.assignment)) ∧
          alternativeCitations ≠
            P93AcyclicPresentCitations
              (observation.assignments.map fun placed => placed.assignment) ∧
          PreferredAtFirstDifference firstDifference

namespace Remaining71P93AcyclicAuthorityRow

def ProductionJudges
    (policy : P93AcyclicAuthorityPolicy) :
    (row : Remaining71P93AcyclicAuthorityRow) →
      AuthoritativeChemicalInput → (row.reference policy).Observation → Prop
  | .acyclicCenters, source, observation =>
      P93AcyclicAssignmentProductionCore policy source observation ∧
        (observation.kind = .chiralCenter ∨ observation.kind = .pseudoasymmetricCenter)
  | .singleAcyclicCenter, source, observation =>
      P93AcyclicSingleCenterSourceCore policy source observation
  | .multipleDescriptorsOneCenter, source, observation =>
      P93AcyclicMultipleDescriptorsSourceCore policy source observation
  | .prefixComponentCenters, source, observation =>
      P93AcyclicPrefixComponentSourceCore policy source observation
  | .ordinaryDoubleBonds, source, observation =>
      P93AcyclicAssignmentProductionCore policy source observation ∧
        observation.kind = .ordinaryDoubleBond
  | .doubleBondEZCisTrans, source, observation =>
      P93AcyclicDoubleBondSourceCore policy source observation
  | .multipleDoubleBonds, source, observation =>
      P93AcyclicMultipleDoubleBondSourceCore policy source observation
  | .heteroatomDoubleBonds, source, observation =>
      Remaining71P93AcyclicReadyAuthorityRow.ProductionJudges policy
        .heteroatomDoubleBonds source observation
  | .evenCumulenes, source, observation =>
      Remaining71P93AcyclicReadyAuthorityRow.ProductionJudges policy
        .evenCumulenes source observation
  | .oddCumulenes, source, observation =>
      Remaining71P93AcyclicReadyAuthorityRow.ProductionJudges policy
        .oddCumulenes source observation
  | .multipleAcyclicStereogenicUnits, source, observation =>
      P93AcyclicMultipleUnitsSourceCore policy source observation

theorem production_eq_reference
    (policy : P93AcyclicAuthorityPolicy)
    (row : Remaining71P93AcyclicAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation) :
    row.ProductionJudges policy source observation ↔
      (row.reference policy).Judges source observation := by
  cases row with
  | acyclicCenters | ordinaryDoubleBonds =>
      simp only [ProductionJudges, reference, p93AcyclicCentersReference,
        p93OrdinaryDoubleBondsReference, P93AcyclicCenterAssignmentJudged,
        P93AcyclicOrdinaryDoubleBondJudged,
        p93AcyclicAssignmentProductionCore_iff_validFor]
  | singleAcyclicCenter =>
      simp only [ProductionJudges, reference, p93SingleAcyclicCenterReference,
        P93AcyclicSingleCenterSourceCore,
        P93AcyclicSingleCenterAuthorityObservation.ValidFor,
        p93AcyclicAssignmentProductionCore_iff_validFor]
  | multipleDescriptorsOneCenter =>
      simp only [ProductionJudges, reference,
        p93MultipleDescriptorsOneCenterReference,
        P93AcyclicMultipleCenterDescriptorsJudged,
        P93AcyclicMultipleDescriptorsSourceCore,
        P93AcyclicMultipleCenterDescriptorsAuthorityObservation.ValidFor,
        P93AcyclicAssignmentsValidFor,
        p93AcyclicAssignmentProductionCore_iff_validFor]
      aesop
  | prefixComponentCenters =>
      simp only [ProductionJudges, reference, p93PrefixComponentCentersReference,
        P93AcyclicPrefixComponentCenterJudged,
        P93AcyclicPrefixComponentSourceCore,
        P93AcyclicPrefixComponentAuthorityObservation.ValidFor,
        p93AcyclicAssignmentProductionCore_iff_validFor]
      aesop
  | doubleBondEZCisTrans =>
      simp only [ProductionJudges, reference, p93DoubleBondEZCisTransReference,
        P93AcyclicDoubleBondSourceCore,
        P93AcyclicDoubleBondAuthorityObservation.ValidFor,
        p93AcyclicAssignmentProductionCore_iff_validFor]
  | multipleDoubleBonds =>
      simp only [ProductionJudges, reference, p93MultipleDoubleBondsReference,
        P93AcyclicMultipleDoubleBondSourceCore,
        P93AcyclicMultipleDoubleBondAuthorityObservation.ValidFor,
        P93AcyclicAssignmentsValidFor,
        p93AcyclicAssignmentProductionCore_iff_validFor]
      aesop
  | heteroatomDoubleBonds =>
      exact Remaining71P93AcyclicReadyAuthorityRow.production_eq_reference
        policy .heteroatomDoubleBonds source observation
  | evenCumulenes =>
      exact Remaining71P93AcyclicReadyAuthorityRow.production_eq_reference
        policy .evenCumulenes source observation
  | oddCumulenes =>
      exact Remaining71P93AcyclicReadyAuthorityRow.production_eq_reference
        policy .oddCumulenes source observation
  | multipleAcyclicStereogenicUnits =>
      simp only [ProductionJudges, reference,
        p93MultipleAcyclicStereogenicUnitsReference,
        P93AcyclicMultipleUnitsSourceCore,
        P93AcyclicMultipleUnitsAuthorityObservation.ValidFor,
        p93AcyclicAssignmentProductionCore_iff_validFor]
      tauto

theorem reference_applicable_of_judged
    (policy : P93AcyclicAuthorityPolicy)
    (row : Remaining71P93AcyclicAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation)
    (judged : (row.reference policy).Judges source observation) :
    (row.reference policy).Applicable source := by
  cases row <;>
    simp only [reference, p93AcyclicCentersReference,
      p93SingleAcyclicCenterReference, p93MultipleDescriptorsOneCenterReference,
      p93PrefixComponentCentersReference, p93OrdinaryDoubleBondsReference,
      p93DoubleBondEZCisTransReference, p93MultipleDoubleBondsReference,
      p93HeteroatomDoubleBondsReference, p93EvenCumulenesReference,
      p93OddCumulenesReference, p93MultipleAcyclicStereogenicUnitsReference,
      P93AcyclicCenterApplicable, P93AcyclicSingleCenterApplicable,
      P93AcyclicMultipleDescriptorsApplicable, P93AcyclicPrefixComponentApplicable,
      P93AcyclicOrdinaryDoubleBondApplicable,
      P93AcyclicDoubleBondEZCisTransApplicable,
      P93AcyclicMultipleDoubleBondApplicable,
      P93AcyclicHeteroDoubleBondApplicable, P93AcyclicEvenCumuleneApplicable,
      P93AcyclicOddCumuleneApplicable, P93AcyclicMultipleUnitsApplicable,
      P93AcyclicCenterAssignmentJudged,
      P93AcyclicMultipleCenterDescriptorsJudged,
      P93AcyclicPrefixComponentCenterJudged,
      P93AcyclicOrdinaryDoubleBondJudged,
      P93AcyclicHeteroDoubleBondJudged] at judged ⊢ <;>
    aesop

end Remaining71P93AcyclicAuthorityRow
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93AcyclicAuthorityRow.production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93AcyclicAuthorityRow.reference_applicable_of_judged
