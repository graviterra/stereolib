import TetraStereo.OneCenter.IUPACRemaining71P93MonocyclicReviewedSemantics

set_option autoImplicit false

/-!
# Closed production semantics for all nine monocyclic P-93 provisions

One explicit ring/source core drives all nine rows.  The production relations expose closed-cycle
evidence, physical-unit evidence, citation and policy guards, and the finite cis/trans, RCT,
monocyclic-double-bond, and exocyclic descriptor calculations directly.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open BlueBookP93
open BlueBookP93.Cyclic

def P93MonocyclicPhysicalSourceCore
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (physical : P93MonocyclicPhysicalUnit) : Prop :=
  P93AuthorityClosedCycle source physical.ringAtoms ∧
    policy.MonocyclicRingObserved source physical.ringAtoms ∧
    physical.unit.ValidFor policy.physicalObservation source ∧
    policy.UnitInRingSystemObserved source physical.ringAtoms physical.unit

def P93MonocyclicGeneralAssignmentSourceCore
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assignment : P93MonocyclicGeneralAssignment policy) : Prop :=
  P93MonocyclicPhysicalSourceCore policy source assignment.physical ∧
    assignment.citation.Valid ∧
    policy.CitationAuthorized source assignment.citation assignment.physical.unit ∧
    policy.GeneralDescriptorAuthorized source assignment.physical.unit assignment.descriptor ∧
    policy.MonocycleNotationObserved source assignment.physical.unit
      assignment.knowledge assignment.notation ∧
    assignment.notation = PreferredMonocycleNotation assignment.knowledge

def P93MonocyclicCenterSourceCore
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MonocyclicCenterAuthorityObservation policy) : Prop :=
  P93MonocyclicPhysicalSourceCore policy source observation.physical ∧
    (∃ center, observation.physical.unit = .atomCenter center ∧
      policy.CenterKindObserved source center observation.kind ∧
      policy.CenterDescriptorAuthorized source center observation.descriptor ∧
      policy.CenterConfigurationKnowledgeObserved source center observation.knowledge) ∧
    (observation.kind = .chiralCenter ∨ observation.kind = .pseudoasymmetricCenter) ∧
    BlueBookP93.Acyclic.DescriptorApplies observation.kind observation.descriptor ∧
    policy.MonocycleNotationObserved source observation.physical.unit
      observation.knowledge observation.notation ∧
    observation.notation = PreferredMonocycleNotation observation.knowledge ∧
    observation.citation.Valid ∧
    policy.CitationAuthorized source observation.citation observation.physical.unit

def P93MonocyclicCisTransSourceCore
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MonocyclicCisTransAuthorityObservation policy) : Prop :=
  P93AuthorityClosedCycle source observation.ringAtoms ∧
    policy.MonocyclicRingObserved source observation.ringAtoms ∧
    observation.firstRingPosition ∈ observation.ringAtoms ∧
    observation.secondRingPosition ∈ observation.ringAtoms ∧
    observation.firstRingPosition ≠ observation.secondRingPosition ∧
    observation.firstSubstituent ≠ observation.secondSubstituent ∧
    observation.firstSubstituent ∉ observation.ringAtoms ∧
    observation.secondSubstituent ∉ observation.ringAtoms ∧
    P93AuthorityBinaryBond source observation.firstRingPosition observation.firstSubstituent ∧
    P93AuthorityBinaryBond source observation.secondRingPosition observation.secondSubstituent ∧
    policy.RingPlaneObserved source observation.ringAtoms observation.firstRingPosition
      observation.secondRingPosition observation.plane ∧
    CisTransPlaneApplicable observation.plane ∧
    policy.RingLigandSideObserved source observation.ringAtoms
      observation.firstSubstituent observation.firstSide ∧
    policy.RingLigandSideObserved source observation.ringAtoms
      observation.secondSubstituent observation.secondSide ∧
    RelativeRingSide observation.firstSide observation.secondSide observation.descriptor

def P93MonocyclicRCTSourceCore
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MonocyclicRCTAuthorityObservation policy) : Prop :=
  P93AuthorityClosedCycle source observation.ringAtoms ∧
    policy.MonocyclicRingObserved source observation.ringAtoms ∧
    observation.candidates ≠ [] ∧
    (observation.candidates.map fun candidate =>
      (candidate.ringPosition, candidate.substituent)).Nodup ∧
    (∀ candidate ∈ observation.candidates,
      candidate.ringPosition ∈ observation.ringAtoms ∧
        candidate.substituent ∉ observation.ringAtoms ∧
        P93AuthorityBinaryBond source candidate.ringPosition candidate.substituent ∧
        candidate.citation.Valid ∧
        policy.CitationAuthorized source candidate.citation
          (.atomCenter candidate.ringPosition) ∧
        policy.RCTReferenceCandidateObserved source observation.ringAtoms
          candidate.ringPosition candidate.substituent candidate.citation
            candidate.namedAsSuffix candidate.sequencePriority) ∧
    P93MonocyclicIsRCTReference observation.candidates observation.selected ∧
    observation.referenceSide ≠ .onMeanPlane ∧
    policy.RingLigandSideObserved source observation.ringAtoms
      observation.selected.substituent observation.referenceSide ∧
    observation.assignments ≠ [] ∧
    (observation.assignments.map fun assignment =>
      (assignment.ringPosition, assignment.substituent)).Nodup ∧
    (∀ candidate ∈ observation.candidates,
      ∃ assignment ∈ observation.assignments,
        assignment.ringPosition = candidate.ringPosition ∧
          assignment.substituent = candidate.substituent) ∧
    ∀ assignment ∈ observation.assignments,
      (∃ candidate ∈ observation.candidates,
        assignment.ringPosition = candidate.ringPosition ∧
          assignment.substituent = candidate.substituent) ∧
      policy.RingLigandSideObserved source observation.ringAtoms
        assignment.substituent assignment.side ∧
      if assignment.ringPosition = observation.selected.ringPosition ∧
          assignment.substituent = observation.selected.substituent then
        assignment.side = observation.referenceSide ∧ assignment.descriptor = .reference
      else
        rctDescriptor observation.referenceSide assignment.side = some assignment.descriptor

def P93MonocyclicUnsaturationSourceCore
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MonocyclicUnsaturationAuthorityObservation policy) : Prop :=
  P93MonocyclicPhysicalSourceCore policy source observation.physical ∧
    policy.CyclicUnsaturationObserved source observation.physical.ringAtoms
      observation.physical.unit observation.topology observation.doubleBondCount ∧
    policy.ChiralCycloalkeneDescriptorAuthorized source observation.physical.unit
      observation.descriptor ∧
    policy.ChiralCycloalkeneNamingContextObserved source observation.physical.unit
      observation.contextIsPIN ∧
    (observation.contextIsPIN = true →
      PreferredChiralCycloalkeneDescriptor observation.descriptor)

def P93MonocyclicDoubleBondSourceCore
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MonocyclicDoubleBondAuthorityObservation policy) : Prop :=
  P93MonocyclicPhysicalSourceCore policy source observation.physical ∧
    (∃ first second, observation.physical.unit = .bond first second) ∧
    policy.CyclicUnsaturationObserved source observation.physical.ringAtoms
      observation.physical.unit .ordinaryCyclicDoubleBondSystem observation.doubleBondCount ∧
    policy.MonocyclicSeniorLigandGeometryObserved source observation.physical.unit
      observation.geometry ∧
    requiredMonocyclicEZDescriptor? observation.physical.ringAtoms.length
      observation.doubleBondCount observation.geometry = observation.descriptor?

def P93MonocyclicExocyclicSourceCore
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MonocyclicExocyclicAuthorityObservation policy) : Prop :=
  P93MonocyclicPhysicalSourceCore policy source observation.physical ∧
    policy.ExocyclicSystemObserved source observation.physical.ringAtoms
      observation.physical.unit observation.doubleBondCount observation.oppositePositions ∧
    ExocyclicMethodAllowed observation.contextIsPIN observation.doubleBondCount
      observation.physical.ringAtoms.length observation.oppositePositions observation.method ∧
    (match observation.method with
    | .integralParentDoubleBond | .ylideneSubstituent =>
        ∃ first second, observation.physical.unit = .bond first second
    | .wholeOddCumulene => ∃ path, observation.physical.unit = .axis path) ∧
    policy.ExocyclicNamingObservationAuthorized source observation.physical.unit
      observation.contextIsPIN observation.method observation.treatment observation.descriptor?

namespace Remaining71P93MonocyclicAuthorityRow

def ProductionJudges
    (policy : P93MonocyclicAuthorityPolicy) :
    (row : Remaining71P93MonocyclicAuthorityRow) →
      AuthoritativeChemicalInput → (row.reference policy).Observation → Prop
  | .cyclicConfigurations, source, observation =>
      P93MonocyclicGeneralAssignmentSourceCore policy source observation
  | .monocyclicAbsoluteCenters, source, observation =>
      P93MonocyclicCenterSourceCore policy source observation ∧
        observation.knowledge = .absolute
  | .monocyclicAchiralCenters, source, observation =>
      P93MonocyclicCenterSourceCore policy source observation ∧
        ∃ center, observation.physical.unit = .atomCenter center ∧
          policy.AchiralMonocyclicCenterObserved source center
  | .monocyclicCisTrans, source, observation =>
      P93MonocyclicCisTransSourceCore policy source observation
  | .monocyclicRCT, source, observation =>
      P93MonocyclicRCTSourceCore policy source observation
  | .unsaturatedMonocycles, source, observation =>
      P93MonocyclicUnsaturationSourceCore policy source observation ∧
        observation.topology = .ordinaryCyclicDoubleBondSystem
  | .cyclicDoubleBonds, source, observation =>
      P93MonocyclicDoubleBondSourceCore policy source observation
  | .exocyclicDoubleBondEZ, source, observation =>
      P93MonocyclicExocyclicSourceCore policy source observation ∧
        P93ExocyclicEZDescriptor observation.descriptor?
  | .exocyclicDoubleBondOther, source, observation =>
      P93MonocyclicExocyclicSourceCore policy source observation ∧
        P93ExocyclicOtherDescriptor observation.descriptor?

theorem production_eq_reference
    (policy : P93MonocyclicAuthorityPolicy)
    (row : Remaining71P93MonocyclicAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation) :
    row.ProductionJudges policy source observation ↔
      (row.reference policy).Judges source observation := by
  cases row <;>
    rfl

theorem reference_applicable_of_judged
    (policy : P93MonocyclicAuthorityPolicy)
    (row : Remaining71P93MonocyclicAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation)
    (judged : (row.reference policy).Judges source observation) :
    (row.reference policy).Applicable source := by
  cases row <;> exact ⟨observation, judged⟩

end Remaining71P93MonocyclicAuthorityRow
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93MonocyclicAuthorityRow.production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93MonocyclicAuthorityRow.reference_applicable_of_judged
