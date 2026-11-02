import TetraStereo.OneCenter.IUPACP93AuthorityConfigurationCarrier
import TetraStereo.OneCenter.P93CyclicConfiguration

set_option autoImplicit false

/-!
# Authority carrier for the nine monocyclic P-93 rows

This module binds the independent P-93.5.1--P-93.5.2 vocabulary to one exact closed molecular
cycle.  Ring atoms and physical stereogenic units remain graph data; decorated citations remain
nomenclature data; mean-plane, ranking, and naming observations enter through a source-indexed
audited policy.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Cyclic

def P93AuthorityClosedCycle
    (source : AuthoritativeChemicalInput) (ringAtoms : List Nat) : Prop :=
  3 ≤ ringAtoms.length ∧ ringAtoms.Nodup ∧
    P93AuthorityAtomsBounded source ringAtoms ∧
    ∃ first remaining,
      ringAtoms = first :: remaining ∧
        P93AuthorityConnectedPath source (ringAtoms ++ [first])

structure P93MonocyclicAuthorityPolicy where
  GeneralDescriptor : Type
  physicalObservation : P93AuthorityPhysicalObservationPolicy
  CitationAuthorized :
    AuthoritativeChemicalInput → P93AuthorityCitationToken →
      P93AuthorityPhysicalUnit → Prop
  MonocyclicRingObserved :
    AuthoritativeChemicalInput → List Nat → Prop
  UnitInRingSystemObserved :
    AuthoritativeChemicalInput → List Nat → P93AuthorityPhysicalUnit → Prop
  GeneralDescriptorAuthorized :
    AuthoritativeChemicalInput → P93AuthorityPhysicalUnit → GeneralDescriptor → Prop
  CenterKindObserved :
    AuthoritativeChemicalInput → Nat → BlueBookP93.Acyclic.UnitKind → Prop
  CenterDescriptorAuthorized :
    AuthoritativeChemicalInput → Nat → BlueBookP93.Acyclic.Descriptor → Prop
  CenterConfigurationKnowledgeObserved :
    AuthoritativeChemicalInput → Nat → ConfigurationKnowledge → Prop
  MonocycleNotationObserved :
    AuthoritativeChemicalInput → P93AuthorityPhysicalUnit →
      ConfigurationKnowledge → MonocycleNotation → Prop
  AchiralMonocyclicCenterObserved :
    AuthoritativeChemicalInput → Nat → Prop
  RingPlaneObserved :
    AuthoritativeChemicalInput → List Nat → Nat → Nat →
      RingPlaneObservation → Prop
  RingLigandSideObserved :
    AuthoritativeChemicalInput → List Nat → Nat → RingSide → Prop
  RCTReferenceCandidateObserved :
    AuthoritativeChemicalInput → List Nat → Nat → Nat →
      P93AuthorityCitationToken → Bool → Nat → Prop
  CyclicUnsaturationObserved :
    AuthoritativeChemicalInput → List Nat → P93AuthorityPhysicalUnit →
      CyclicUnsaturationTopology → Nat → Prop
  MonocyclicSeniorLigandGeometryObserved :
    AuthoritativeChemicalInput → P93AuthorityPhysicalUnit →
      MonocyclicSeniorLigandGeometry → Prop
  ChiralCycloalkeneDescriptorAuthorized :
    AuthoritativeChemicalInput → P93AuthorityPhysicalUnit →
      ChiralCycloalkeneDescriptor → Prop
  ChiralCycloalkeneNamingContextObserved :
    AuthoritativeChemicalInput → P93AuthorityPhysicalUnit → Bool → Prop
  ExocyclicSystemObserved :
    AuthoritativeChemicalInput → List Nat → P93AuthorityPhysicalUnit →
      Nat → Bool → Prop
  ExocyclicNamingObservationAuthorized :
    AuthoritativeChemicalInput → P93AuthorityPhysicalUnit → Bool →
      ExocyclicNamingMethod → ExocyclicSystemTreatment →
        Option BlueBookP93.Acyclic.Descriptor → Prop

structure P93MonocyclicPhysicalUnit where
  ringAtoms : List Nat
  unit : P93AuthorityPhysicalUnit
  deriving DecidableEq

def P93MonocyclicPhysicalUnit.ValidFor
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MonocyclicPhysicalUnit) : Prop :=
  P93AuthorityClosedCycle source observation.ringAtoms ∧
    policy.MonocyclicRingObserved source observation.ringAtoms ∧
    observation.unit.ValidFor policy.physicalObservation source ∧
    policy.UnitInRingSystemObserved source observation.ringAtoms observation.unit

structure P93MonocyclicGeneralAssignment
    (policy : P93MonocyclicAuthorityPolicy) where
  physical : P93MonocyclicPhysicalUnit
  citation : P93AuthorityCitationToken
  descriptor : policy.GeneralDescriptor
  knowledge : ConfigurationKnowledge
  «notation» : MonocycleNotation

def P93MonocyclicGeneralAssignment.ValidFor
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assignment : P93MonocyclicGeneralAssignment policy) : Prop :=
  assignment.physical.ValidFor policy source ∧
    assignment.citation.Valid ∧
    policy.CitationAuthorized source assignment.citation assignment.physical.unit ∧
    policy.GeneralDescriptorAuthorized source assignment.physical.unit
      assignment.descriptor ∧
    policy.MonocycleNotationObserved source assignment.physical.unit
      assignment.knowledge assignment.notation ∧
    assignment.notation = PreferredMonocycleNotation assignment.knowledge

structure P93MonocyclicCenterAuthorityObservation
    (policy : P93MonocyclicAuthorityPolicy) where
  physical : P93MonocyclicPhysicalUnit
  citation : P93AuthorityCitationToken
  kind : BlueBookP93.Acyclic.UnitKind
  descriptor : BlueBookP93.Acyclic.Descriptor
  knowledge : ConfigurationKnowledge
  «notation» : MonocycleNotation

def P93MonocyclicCenterAuthorityObservation.ValidFor
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MonocyclicCenterAuthorityObservation policy) : Prop :=
  observation.physical.ValidFor policy source ∧
    (∃ center, observation.physical.unit = .atomCenter center ∧
      policy.CenterKindObserved source center observation.kind ∧
      policy.CenterDescriptorAuthorized source center observation.descriptor ∧
      policy.CenterConfigurationKnowledgeObserved source center observation.knowledge) ∧
    (observation.kind = .chiralCenter ∨
      observation.kind = .pseudoasymmetricCenter) ∧
    BlueBookP93.Acyclic.DescriptorApplies observation.kind observation.descriptor ∧
    policy.MonocycleNotationObserved source observation.physical.unit
      observation.knowledge observation.notation ∧
    observation.notation = PreferredMonocycleNotation observation.knowledge ∧
    observation.citation.Valid ∧
    policy.CitationAuthorized source observation.citation observation.physical.unit

structure P93MonocyclicCisTransAuthorityObservation
    (policy : P93MonocyclicAuthorityPolicy) where
  ringAtoms : List Nat
  firstRingPosition : Nat
  secondRingPosition : Nat
  firstSubstituent : Nat
  secondSubstituent : Nat
  plane : RingPlaneObservation
  firstSide : RingSide
  secondSide : RingSide
  descriptor : CisTrans

def P93MonocyclicCisTransAuthorityObservation.ValidFor
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
    P93AuthorityBinaryBond source observation.firstRingPosition
      observation.firstSubstituent ∧
    P93AuthorityBinaryBond source observation.secondRingPosition
      observation.secondSubstituent ∧
    policy.RingPlaneObserved source observation.ringAtoms
      observation.firstRingPosition observation.secondRingPosition observation.plane ∧
    CisTransPlaneApplicable observation.plane ∧
    policy.RingLigandSideObserved source observation.ringAtoms
      observation.firstSubstituent observation.firstSide ∧
    policy.RingLigandSideObserved source observation.ringAtoms
      observation.secondSubstituent observation.secondSide ∧
    RelativeRingSide observation.firstSide observation.secondSide
      observation.descriptor

structure P93MonocyclicRCTReferenceCandidate where
  ringPosition : Nat
  substituent : Nat
  citation : P93AuthorityCitationToken
  namedAsSuffix : Bool
  sequencePriority : Nat
  deriving DecidableEq, Repr

def P93MonocyclicIsRCTReference
    (candidates : List P93MonocyclicRCTReferenceCandidate)
    (selected : P93MonocyclicRCTReferenceCandidate) : Prop :=
  selected ∈ candidates ∧
    ((selected.namedAsSuffix = true ∧
      ∀ other ∈ candidates, other.namedAsSuffix = true →
        selected.citation.CitationLE other.citation) ∨
    ((∀ candidate ∈ candidates, candidate.namedAsSuffix = false) ∧
      ∀ other ∈ candidates,
        selected.citation.CitationLE other.citation ∧
          (selected.citation = other.citation →
            other.sequencePriority ≤ selected.sequencePriority)))

structure P93MonocyclicRCTLocatedAssignment where
  ringPosition : Nat
  substituent : Nat
  side : RingSide
  descriptor : RCTDescriptor
  deriving DecidableEq, Repr

structure P93MonocyclicRCTAuthorityObservation
    (policy : P93MonocyclicAuthorityPolicy) where
  ringAtoms : List Nat
  candidates : List P93MonocyclicRCTReferenceCandidate
  selected : P93MonocyclicRCTReferenceCandidate
  referenceSide : RingSide
  assignments : List P93MonocyclicRCTLocatedAssignment

def P93MonocyclicRCTAuthorityObservation.ValidFor
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
          candidate.ringPosition candidate.substituent candidate.citation candidate.namedAsSuffix
          candidate.sequencePriority) ∧
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
        assignment.side = observation.referenceSide ∧
          assignment.descriptor = .reference
      else
        rctDescriptor observation.referenceSide assignment.side =
          some assignment.descriptor

structure P93MonocyclicUnsaturationAuthorityObservation
    (policy : P93MonocyclicAuthorityPolicy) where
  physical : P93MonocyclicPhysicalUnit
  topology : CyclicUnsaturationTopology
  doubleBondCount : Nat
  contextIsPIN : Bool
  descriptor : ChiralCycloalkeneDescriptor

def P93MonocyclicUnsaturationAuthorityObservation.ValidFor
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MonocyclicUnsaturationAuthorityObservation policy) : Prop :=
  observation.physical.ValidFor policy source ∧
    policy.CyclicUnsaturationObserved source observation.physical.ringAtoms
      observation.physical.unit observation.topology observation.doubleBondCount ∧
    policy.ChiralCycloalkeneDescriptorAuthorized source observation.physical.unit
      observation.descriptor ∧
    policy.ChiralCycloalkeneNamingContextObserved source observation.physical.unit
      observation.contextIsPIN ∧
    (observation.contextIsPIN = true →
      PreferredChiralCycloalkeneDescriptor observation.descriptor)

structure P93MonocyclicDoubleBondAuthorityObservation
    (policy : P93MonocyclicAuthorityPolicy) where
  physical : P93MonocyclicPhysicalUnit
  doubleBondCount : Nat
  geometry : MonocyclicSeniorLigandGeometry
  descriptor? : Option BlueBookP93.Acyclic.Descriptor

def P93MonocyclicDoubleBondAuthorityObservation.ValidFor
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MonocyclicDoubleBondAuthorityObservation policy) : Prop :=
  observation.physical.ValidFor policy source ∧
    (∃ first second, observation.physical.unit = .bond first second) ∧
    policy.CyclicUnsaturationObserved source observation.physical.ringAtoms
      observation.physical.unit .ordinaryCyclicDoubleBondSystem
      observation.doubleBondCount ∧
    policy.MonocyclicSeniorLigandGeometryObserved source observation.physical.unit
      observation.geometry ∧
    requiredMonocyclicEZDescriptor? observation.physical.ringAtoms.length
      observation.doubleBondCount observation.geometry = observation.descriptor?

structure P93MonocyclicExocyclicAuthorityObservation
    (policy : P93MonocyclicAuthorityPolicy) where
  physical : P93MonocyclicPhysicalUnit
  contextIsPIN : Bool
  doubleBondCount : Nat
  oppositePositions : Bool
  method : ExocyclicNamingMethod
  treatment : ExocyclicSystemTreatment
  descriptor? : Option BlueBookP93.Acyclic.Descriptor

def P93MonocyclicExocyclicAuthorityObservation.ValidFor
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MonocyclicExocyclicAuthorityObservation policy) : Prop :=
  observation.physical.ValidFor policy source ∧
    policy.ExocyclicSystemObserved source observation.physical.ringAtoms
      observation.physical.unit observation.doubleBondCount
      observation.oppositePositions ∧
    ExocyclicMethodAllowed observation.contextIsPIN observation.doubleBondCount
      observation.physical.ringAtoms.length observation.oppositePositions
      observation.method ∧
    (match observation.method with
    | .integralParentDoubleBond | .ylideneSubstituent =>
        ∃ first second, observation.physical.unit = .bond first second
    | .wholeOddCumulene =>
        ∃ path, observation.physical.unit = .axis path) ∧
    policy.ExocyclicNamingObservationAuthorized source observation.physical.unit
      observation.contextIsPIN observation.method observation.treatment
      observation.descriptor?

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P93AuthorityClosedCycle
assert_kernel_only TetraStereo.OneCenter.P93MonocyclicCisTransAuthorityObservation.ValidFor
assert_kernel_only TetraStereo.OneCenter.P93MonocyclicRCTAuthorityObservation.ValidFor
assert_kernel_only TetraStereo.OneCenter.P93MonocyclicDoubleBondAuthorityObservation.ValidFor
