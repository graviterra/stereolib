import TetraStereo.OneCenter.IUPACRemaining71P93FusedCyclophaneReviewedSemantics

set_option autoImplicit false

/-!
# Closed production semantics for the fused and cyclophane P-93 family

The five observations are validated by explicit source/core relations.  The production side
expands system, physical-unit, candidate, geometry, descriptor, and citation requirements rather
than invoking a reviewed provision judgment.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open BlueBookP93
open BlueBookP93.Cyclic

def P93FusedSystemSourceCore
    (policy : P93FusedAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (system : P93AuthorityFusedSystem) : Prop :=
  system.MechanicallyValidFor source ∧ policy.SystemObserved source system

def P93FusedUnitSourceCore
    (policy : P93FusedAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (system : P93AuthorityFusedSystem) : P93FusedAuthorityUnit → Prop
  | .physical unit =>
      unit.ValidFor policy.physicalObservation source ∧
        P93FusedPhysicalUnitSupported system unit
  | .fusedAxis path =>
      2 ≤ path.length ∧ path.Nodup ∧
        P93AuthorityAtomsBounded source path ∧
        P93AuthorityCanonicalDirectedPath path ∧
        P93AuthorityConnectedPath source path ∧
        (∀ atom ∈ path, atom ∈ system.atoms) ∧
        policy.FusedAxisObserved source system path

def P93FusedNearestPairCandidateSourceCore
    (policy : P93FusedAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (system : P93AuthorityFusedSystem)
    (candidate : P93FusedNearestPairCandidate) : Prop :=
  candidate.firstFusionAtom < candidate.secondFusionAtom ∧
    P93AuthorityFusionAtom system candidate.firstFusionAtom ∧
    P93AuthorityFusionAtom system candidate.secondFusionAtom ∧
    (candidate.firstFusionAtom, candidate.firstFusionLocant) ∈ system.fusionLocants ∧
    (candidate.secondFusionAtom, candidate.secondFusionLocant) ∈ system.fusionLocants ∧
    candidate.lowerAtomLocant =
      P93FusedLocant.min candidate.firstFusionLocant candidate.secondFusionLocant ∧
    policy.FusionPairEligible source system
      candidate.firstFusionAtom candidate.secondFusionAtom ∧
    0 < candidate.graphDistance ∧
    policy.FusionPairCandidateObserved source system
      candidate.firstFusionAtom candidate.secondFusionAtom
      candidate.graphDistance candidate.lowerAtomLocant

def P93FusedCIPSourceCore
    (policy : P93FusedAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93FusedCIPAuthorityObservation policy) : Prop :=
  P93FusedSystemSourceCore policy source observation.system ∧
    P93FusedUnitSourceCore policy source observation.system observation.unit ∧
    policy.UnitInSystemObserved source observation.system observation.unit ∧
    P93FusedUnitDescriptorMatches observation.unit observation.descriptor ∧
    policy.UnitDescriptorAuthorized source observation.system observation.unit
      observation.descriptor ∧
    observation.citation.Valid ∧
    observation.citation.CitesUnit observation.system observation.unit ∧
    policy.CitationAuthorized source observation.citation observation.unit

def P93FusedRelationSourceCore
    (policy : P93FusedAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93FusedRelationAuthorityObservation policy) : Prop :=
  P93FusedSystemSourceCore policy source observation.system ∧
    observation.candidates ≠ [] ∧
    (observation.candidates.map fun candidate =>
      (candidate.firstFusionAtom, candidate.secondFusionAtom)).Nodup ∧
    (∀ candidate ∈ observation.candidates,
      P93FusedNearestPairCandidateSourceCore
        policy source observation.system candidate) ∧
    (∀ first second,
      policy.FusionPairEligible source observation.system first second →
        ∃ candidate ∈ observation.candidates,
          candidate.firstFusionAtom = first ∧ candidate.secondFusionAtom = second) ∧
    P93FusedIsUniqueSelectedNearestPair observation.candidates observation.selected ∧
    (observation.legacyDescriptor = .cisoid ∨
      observation.legacyDescriptor = .transoid) ∧
    observation.preferredDescriptor = .relCIP ∧
    PreferredFusionDescription observation.preferredDescriptor ∧
    policy.FusionRelationObserved source observation.system
      observation.selected.firstFusionAtom observation.selected.secondFusionAtom
      observation.firstJunction observation.secondJunction observation.legacyDescriptor ∧
    observation.selectedCitation.Valid ∧
    observation.selectedCitation = observation.selected.lowerAtomLocant ∧
    policy.FusionPairCitationAuthorized source observation.system
      observation.selected.firstFusionAtom observation.selected.secondFusionAtom
      observation.selectedCitation

def P93CyclophaneSystemSourceCore
    (policy : P93CyclophaneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (system : P93AuthorityCyclophaneSystem) : Prop :=
  system.MechanicallyValidFor source ∧ policy.SystemObserved source system

def P93CyclophaneRCTCandidateSourceCore
    (policy : P93CyclophaneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (system : P93AuthorityCyclophaneSystem)
    (candidate : P93CyclophaneRCTReferenceCandidate) : Prop :=
  candidate.center ∈ system.atomCarrier ∧
    (P93AuthorityPhysicalUnit.atomCenter candidate.center).ValidFor
      policy.physicalObservation source ∧
    policy.UnitInSystemObserved source system (.atomCenter candidate.center) ∧
    policy.RCTReferenceCenterEligible source system candidate.center ∧
    candidate.citation.Valid ∧
    policy.CitationAuthorized source candidate.citation (.atomCenter candidate.center) ∧
    policy.RCTReferenceCandidateObserved source system candidate.center
      candidate.citation candidate.namedAsSuffix candidate.sequencePriority

def P93CyclophanePlaneSourceCore
    (policy : P93CyclophaneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93CyclophanePlaneAuthorityObservation policy) : Prop :=
  P93CyclophaneSystemSourceCore policy source observation.system ∧
    P93CyclophaneUnitSupported observation.system observation.unit ∧
    (∃ members spatial high low highPoint lowPoint inPlanePoint outOfPlanePoint general,
      observation.unit = .plane members ∧
        observation.frame.ValidFor source members ∧
        source.spatial? = some spatial ∧
        ((high = observation.frame.record.firstReference ∧
            low = observation.frame.record.secondReference) ∨
          (high = observation.frame.record.secondReference ∧
            low = observation.frame.record.firstReference)) ∧
        policy.PlaneReferenceOrderObserved source observation.system
          observation.unit high low ∧
        BlueBookP94.CoordinateRing.SpatialPointAt spatial high highPoint ∧
        BlueBookP94.CoordinateRing.SpatialPointAt spatial low lowPoint ∧
        BlueBookP94.CoordinateRing.SpatialPointAt spatial
          observation.frame.record.inPlaneBondAtom inPlanePoint ∧
        BlueBookP94.CoordinateRing.SpatialPointAt spatial
          observation.frame.record.outOfPlaneAtom outOfPlanePoint ∧
        BlueBookP92.PlanarDerivedTetrahedron.RationalDescriptor
          highPoint lowPoint inPlanePoint outOfPlanePoint general ∧
        policy.PlaneReferenceObserved source observation.system observation.unit
          observation.reference ∧
        policy.PlaneDescriptorAuthorized source observation.system observation.unit
          observation.context observation.descriptor ∧
        observation.descriptor =
          match observation.context with
          | .preferredIUPACName =>
              CyclophanePlaneDescriptor.preferredOfGeneralPlanar general
          | .general => CyclophanePlaneDescriptor.ofGeneralPlanar general) ∧
    ValidCyclophanePlaneReference observation.reference ∧
    (observation.context = .preferredIUPACName →
      PreferredCyclophanePlaneDescriptor observation.descriptor) ∧
    policy.UnitInSystemObserved source observation.system observation.unit ∧
    observation.citation.Valid ∧
    policy.CitationAuthorized source observation.citation observation.unit

def P93CyclophaneCenterSourceCore
    (policy : P93CyclophaneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93CyclophaneCenterAuthorityObservation policy) : Prop :=
  P93CyclophaneSystemSourceCore policy source observation.system ∧
    observation.unit.ValidFor policy.physicalObservation source ∧
    P93CyclophaneUnitSupported observation.system observation.unit ∧
    policy.UnitInSystemObserved source observation.system observation.unit ∧
    observation.citation.Valid ∧
    policy.CitationAuthorized source observation.citation observation.unit ∧
    match observation.specification with
    | .cip context kind descriptor =>
        (∃ center, observation.unit = .atomCenter center ∧
          policy.CenterKindObserved source observation.system center kind ∧
          policy.CenterDescriptorAuthorized source observation.system center
            context descriptor) ∧
          (kind = .chiralCenter ∨ kind = .pseudoasymmetricCenter) ∧
          BlueBookP93.Acyclic.DescriptorApplies kind descriptor ∧
          BlueBookP93.Acyclic.DescriptorRecommended context kind descriptor
    | .relativeRCT candidates selected referenceSide assignments =>
        observation.unit = .atomCenter selected.center ∧
          observation.citation = selected.citation ∧
          candidates ≠ [] ∧
          (candidates.map fun candidate => candidate.center).Nodup ∧
          (candidates.map fun candidate => candidate.citation).Nodup ∧
          (∀ candidate ∈ candidates,
            P93CyclophaneRCTCandidateSourceCore
              policy source observation.system candidate) ∧
          (∀ center,
            policy.RCTReferenceCenterEligible source observation.system center →
              ∃ candidate ∈ candidates, candidate.center = center) ∧
          P93CyclophaneIsUniqueRCTReference candidates selected ∧
          referenceSide ≠ .onMeanPlane ∧
          policy.RCTCenterSideObserved source observation.system
            selected.center referenceSide ∧
          assignments ≠ [] ∧
          (assignments.map fun assignment => assignment.center).Nodup ∧
          (assignments.map fun assignment => assignment.citation).Nodup ∧
          (∀ candidate ∈ candidates,
            ∃ assignment ∈ assignments,
              assignment.center = candidate.center ∧
                assignment.citation = candidate.citation) ∧
          ∀ assignment ∈ assignments,
            (∃ candidate ∈ candidates,
              assignment.center = candidate.center ∧
                assignment.citation = candidate.citation) ∧
            policy.RCTCenterSideObserved source observation.system
              assignment.center assignment.side ∧
            if assignment.center = selected.center then
              assignment.side = referenceSide ∧ assignment.descriptor = .reference
            else
              rctDescriptor referenceSide assignment.side = some assignment.descriptor

def P93CyclophaneDoubleBondSourceCore
    (policy : P93CyclophaneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93CyclophaneDoubleBondAuthorityObservation policy) : Prop :=
  P93CyclophaneSystemSourceCore policy source observation.system ∧
    observation.unit.ValidFor policy.physicalObservation source ∧
    P93CyclophaneUnitSupported observation.system observation.unit ∧
    (∃ first second, observation.unit = .bond first second ∧
      first ∈ observation.ring ∧ second ∈ observation.ring) ∧
    observation.ring ∈ observation.system.rings ∧
    (observation.ring, observation.phaneRing) ∈ observation.system.ringPhaneCycles ∧
    policy.UnitInSystemObserved source observation.system observation.unit ∧
    policy.DoubleBondRingObserved source observation.system observation.unit
      observation.ring observation.phaneRing ∧
    policy.DoubleBondGeometryObserved source observation.unit observation.geometry ∧
    policy.CarbonDoubleBondContextObserved source observation.unit
      observation.carbonContext ∧
    policy.DoubleBondNamingAuthorized source observation.system observation.unit
      observation.context observation.descriptor? ∧
    P93CyclophaneDoubleBondDescriptorAllowed observation.context
      observation.geometry observation.descriptor? ∧
    ((observation.descriptor? = some .cis ∨ observation.descriptor? = some .trans) →
      BlueBookP93.Acyclic.CisTransGeneralApplicable observation.carbonContext) ∧
    (CyclophaneDoubleBondDescriptorRequired observation.system.phaneNodes.length
        observation.phaneRing.length = true →
      ∃ descriptor, observation.descriptor? = some descriptor) ∧
    (observation.context = .preferredIUPACName →
      observation.descriptor? = P93CyclophaneDoubleBondExpected
        observation.system.phaneNodes.length observation.phaneRing.length
          observation.geometry) ∧
    observation.citation.Valid ∧
    policy.CitationAuthorized source observation.citation observation.unit

theorem p93FusedCIP_sourceCore_iff_validFor
    (policy : P93FusedAuthorityPolicy) (source : AuthoritativeChemicalInput)
    (observation : P93FusedCIPAuthorityObservation policy) :
    P93FusedCIPSourceCore policy source observation ↔ observation.ValidFor policy source := by
  rfl

theorem p93FusedRelation_sourceCore_iff_validFor
    (policy : P93FusedAuthorityPolicy) (source : AuthoritativeChemicalInput)
    (observation : P93FusedRelationAuthorityObservation policy) :
    P93FusedRelationSourceCore policy source observation ↔ observation.ValidFor policy source := by
  rfl

theorem p93CyclophanePlane_sourceCore_iff_validFor
    (policy : P93CyclophaneAuthorityPolicy) (source : AuthoritativeChemicalInput)
    (observation : P93CyclophanePlaneAuthorityObservation policy) :
    P93CyclophanePlaneSourceCore policy source observation ↔ observation.ValidFor policy source := by
  rfl

theorem p93CyclophaneCenter_sourceCore_iff_validFor
    (policy : P93CyclophaneAuthorityPolicy) (source : AuthoritativeChemicalInput)
    (observation : P93CyclophaneCenterAuthorityObservation policy) :
    P93CyclophaneCenterSourceCore policy source observation ↔ observation.ValidFor policy source := by
  rfl

theorem p93CyclophaneDoubleBond_sourceCore_iff_validFor
    (policy : P93CyclophaneAuthorityPolicy) (source : AuthoritativeChemicalInput)
    (observation : P93CyclophaneDoubleBondAuthorityObservation policy) :
    P93CyclophaneDoubleBondSourceCore policy source observation ↔
      observation.ValidFor policy source := by
  rfl

namespace Remaining71P93FusedCyclophaneAuthorityRow

def ProductionJudges
    (fusedPolicy : P93FusedAuthorityPolicy)
    (cyclophanePolicy : P93CyclophaneAuthorityPolicy) :
    (row : Remaining71P93FusedCyclophaneAuthorityRow) →
      AuthoritativeChemicalInput →
      (row.reference fusedPolicy cyclophanePolicy).Observation → Prop
  | .fusedBridgedCIP, source, observation =>
      P93FusedCIPSourceCore fusedPolicy source observation
  | .cisoidTransoid, source, observation =>
      P93FusedRelationSourceCore fusedPolicy source observation
  | .cyclophanePlanes, source, observation =>
      P93CyclophanePlaneSourceCore cyclophanePolicy source observation
  | .cyclophaneCenters, source, observation =>
      P93CyclophaneCenterSourceCore cyclophanePolicy source observation
  | .cyclophaneDoubleBonds, source, observation =>
      P93CyclophaneDoubleBondSourceCore cyclophanePolicy source observation

theorem production_eq_reference
    (fusedPolicy : P93FusedAuthorityPolicy)
    (cyclophanePolicy : P93CyclophaneAuthorityPolicy)
    (row : Remaining71P93FusedCyclophaneAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference fusedPolicy cyclophanePolicy).Observation) :
    row.ProductionJudges fusedPolicy cyclophanePolicy source observation ↔
      (row.reference fusedPolicy cyclophanePolicy).Judges source observation := by
  cases row <;> rfl

theorem reference_applicable_of_judged
    (fusedPolicy : P93FusedAuthorityPolicy)
    (cyclophanePolicy : P93CyclophaneAuthorityPolicy)
    (row : Remaining71P93FusedCyclophaneAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference fusedPolicy cyclophanePolicy).Observation)
    (judged : (row.reference fusedPolicy cyclophanePolicy).Judges source observation) :
    (row.reference fusedPolicy cyclophanePolicy).Applicable source := by
  cases row <;> exact ⟨observation, judged⟩

end Remaining71P93FusedCyclophaneAuthorityRow
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93FusedCyclophaneAuthorityRow.production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93FusedCyclophaneAuthorityRow.reference_applicable_of_judged
