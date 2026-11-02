import TetraStereo.OneCenter.IUPACP93AuthorityConfigurationCarrier
import TetraStereo.OneCenter.P93CyclicConfiguration

set_option autoImplicit false

/-!
# Authority carrier for the three cyclophane P-93 rows

The carrier stores the exact source-designated node set and closed rings of one cyclophane.  Plane
configuration uses the coordinate-backed generic plane unit, while center configuration has
separate CIP and general `r/c/t` branches.  Double-bond omission is controlled by both total system
nodes and nodes in the containing ring, as required by P-93.5.5.3.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Cyclic

def P93AuthorityCyclophaneClosedRing
    (source : AuthoritativeChemicalInput) (ring : List Nat) : Prop :=
  3 ≤ ring.length ∧ ring.Nodup ∧
    P93AuthorityAtomsBounded source ring ∧
    ∃ first remaining,
      ring = first :: remaining ∧
        P93AuthorityConnectedPath source (ring ++ [first])

structure P93AuthorityCyclophaneSystem where
  /-- Exact molecular atoms belonging to the cyclophane parent system. -/
  atomCarrier : List Nat
  /-- Atom carriers of the source-designated phane nomenclature nodes.  A composite node such as
  a benzene ring therefore contributes one entry here while retaining all of its atoms in
  `atomCarrier`. -/
  phaneNodes : List (Finset Nat)
  rings : List (List Nat)
  /-- For each molecular atom cycle in `rings`, the matching cycle of indices into `phaneNodes`.
  This is the source of the ring-node count in P-93.5.5.3; atom-cycle length is never reused as
  a phane-node count. -/
  ringPhaneCycles : List (List Nat × List Nat)
  deriving DecidableEq

def P93AuthorityCyclophaneSystem.MechanicallyValidFor
    (source : AuthoritativeChemicalInput)
    (system : P93AuthorityCyclophaneSystem) : Prop :=
  3 ≤ system.atomCarrier.length ∧ system.atomCarrier.Nodup ∧
    P93AuthorityAtomsBounded source system.atomCarrier ∧
    3 ≤ system.phaneNodes.length ∧ system.phaneNodes.Nodup ∧
    (∀ node ∈ system.phaneNodes,
      node.Nonempty ∧ ∀ atom ∈ node, atom ∈ system.atomCarrier) ∧
    (∀ atom ∈ system.atomCarrier,
      ∃ node ∈ system.phaneNodes, atom ∈ node) ∧
    (∀ first ∈ system.phaneNodes, ∀ second ∈ system.phaneNodes,
      first ≠ second → Disjoint first second) ∧
    system.rings ≠ [] ∧ system.rings.Nodup ∧
    (∀ ring ∈ system.rings,
      P93AuthorityCyclophaneClosedRing source ring ∧
        ∀ atom ∈ ring, atom ∈ system.atomCarrier) ∧
    (∀ atom ∈ system.atomCarrier, ∃ ring ∈ system.rings, atom ∈ ring) ∧
    system.ringPhaneCycles ≠ [] ∧
    (system.ringPhaneCycles.map Prod.fst).Nodup ∧
    ∀ mapping ∈ system.ringPhaneCycles,
      mapping.1 ∈ system.rings ∧ 3 ≤ mapping.2.length ∧ mapping.2.Nodup ∧
        ∀ nodeIndex ∈ mapping.2,
          ∃ node, system.phaneNodes[nodeIndex]? = some node ∧
            ∃ atom ∈ mapping.1, atom ∈ node

structure P93CyclophaneAuthorityPolicy where
  physicalObservation : P93AuthorityPhysicalObservationPolicy
  SystemObserved :
    AuthoritativeChemicalInput → P93AuthorityCyclophaneSystem → Prop
  UnitInSystemObserved :
    AuthoritativeChemicalInput → P93AuthorityCyclophaneSystem →
      P93AuthorityPhysicalUnit → Prop
  CitationAuthorized :
    AuthoritativeChemicalInput → P93AuthorityCitationToken →
      P93AuthorityPhysicalUnit → Prop
  PlaneReferenceObserved :
    AuthoritativeChemicalInput → P93AuthorityCyclophaneSystem →
      P93AuthorityPhysicalUnit → CyclophanePlaneReference → Prop
  PlaneReferenceOrderObserved :
    AuthoritativeChemicalInput → P93AuthorityCyclophaneSystem →
      P93AuthorityPhysicalUnit → Nat → Nat → Prop
  PlaneDescriptorAuthorized :
    AuthoritativeChemicalInput → P93AuthorityCyclophaneSystem →
      P93AuthorityPhysicalUnit → BlueBookP93.Acyclic.NomenclatureContext →
        CyclophanePlaneDescriptor → Prop
  CenterKindObserved :
    AuthoritativeChemicalInput → P93AuthorityCyclophaneSystem →
      Nat → BlueBookP93.Acyclic.UnitKind → Prop
  CenterDescriptorAuthorized :
    AuthoritativeChemicalInput → P93AuthorityCyclophaneSystem →
      Nat → BlueBookP93.Acyclic.NomenclatureContext →
        BlueBookP93.Acyclic.Descriptor → Prop
  RCTReferenceCenterEligible :
    AuthoritativeChemicalInput → P93AuthorityCyclophaneSystem → Nat → Prop
  RCTReferenceCandidateObserved :
    AuthoritativeChemicalInput → P93AuthorityCyclophaneSystem →
      Nat → P93AuthorityCitationToken → Bool → Nat → Prop
  RCTCenterSideObserved :
    AuthoritativeChemicalInput → P93AuthorityCyclophaneSystem →
      Nat → RingSide → Prop
  DoubleBondRingObserved :
    AuthoritativeChemicalInput → P93AuthorityCyclophaneSystem →
      P93AuthorityPhysicalUnit → List Nat → List Nat → Prop
  DoubleBondGeometryObserved :
    AuthoritativeChemicalInput → P93AuthorityPhysicalUnit →
      MonocyclicSeniorLigandGeometry → Prop
  CarbonDoubleBondContextObserved :
    AuthoritativeChemicalInput → P93AuthorityPhysicalUnit →
      BlueBookP93.Acyclic.CarbonDoubleBondContext → Prop
  DoubleBondNamingAuthorized :
    AuthoritativeChemicalInput → P93AuthorityCyclophaneSystem →
      P93AuthorityPhysicalUnit → BlueBookP93.Acyclic.NomenclatureContext →
        Option BlueBookP93.Acyclic.Descriptor → Prop

def P93AuthorityCyclophaneSystem.ValidFor
    (policy : P93CyclophaneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (system : P93AuthorityCyclophaneSystem) : Prop :=
  system.MechanicallyValidFor source ∧
    policy.SystemObserved source system

def P93CyclophaneUnitSupported
    (system : P93AuthorityCyclophaneSystem) : P93AuthorityPhysicalUnit → Prop
  | .atomCenter center => center ∈ system.atomCarrier
  | .bond first second => first ∈ system.atomCarrier ∧ second ∈ system.atomCarrier
  | .plane members => ∀ member ∈ members, member ∈ system.atomCarrier
  | .axis _ | .helix _ | .polyhedron _ _ => False

structure P93CyclophanePlaneAuthorityObservation
    (policy : P93CyclophaneAuthorityPolicy) where
  system : P93AuthorityCyclophaneSystem
  unit : P93AuthorityPhysicalUnit
  frame : P93AuthorityPlaneFrame
  citation : P93AuthorityCitationToken
  reference : CyclophanePlaneReference
  context : BlueBookP93.Acyclic.NomenclatureContext
  descriptor : CyclophanePlaneDescriptor

def P93CyclophanePlaneAuthorityObservation.ValidFor
    (policy : P93CyclophaneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93CyclophanePlaneAuthorityObservation policy) : Prop :=
  observation.system.ValidFor policy source ∧
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

structure P93CyclophaneRCTReferenceCandidate where
  center : Nat
  citation : P93AuthorityCitationToken
  namedAsSuffix : Bool
  sequencePriority : Nat
  deriving DecidableEq, Repr

def P93CyclophaneRCTReferenceCandidate.ValidFor
    (policy : P93CyclophaneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (system : P93AuthorityCyclophaneSystem)
    (candidate : P93CyclophaneRCTReferenceCandidate) : Prop :=
  candidate.center ∈ system.atomCarrier ∧
    (P93AuthorityPhysicalUnit.atomCenter candidate.center).ValidFor
      policy.physicalObservation source ∧
    policy.UnitInSystemObserved source system
      (P93AuthorityPhysicalUnit.atomCenter candidate.center) ∧
    policy.RCTReferenceCenterEligible source system candidate.center ∧
    candidate.citation.Valid ∧
    policy.CitationAuthorized source candidate.citation
      (P93AuthorityPhysicalUnit.atomCenter candidate.center) ∧
    policy.RCTReferenceCandidateObserved source system candidate.center
      candidate.citation candidate.namedAsSuffix candidate.sequencePriority

def P93CyclophaneRCTReferenceRule
    (candidates : List P93CyclophaneRCTReferenceCandidate)
    (selected : P93CyclophaneRCTReferenceCandidate) : Prop :=
  selected ∈ candidates ∧
    ((selected.namedAsSuffix = true ∧
      ∀ other ∈ candidates, other.namedAsSuffix = true →
        selected.citation.CitationLE other.citation) ∨
    ((∀ candidate ∈ candidates, candidate.namedAsSuffix = false) ∧
      ∀ other ∈ candidates,
        selected.citation.CitationLE other.citation ∧
          (selected.citation = other.citation →
            other.sequencePriority ≤ selected.sequencePriority)))

def P93CyclophaneIsUniqueRCTReference
    (candidates : List P93CyclophaneRCTReferenceCandidate)
    (selected : P93CyclophaneRCTReferenceCandidate) : Prop :=
  P93CyclophaneRCTReferenceRule candidates selected ∧
    ∀ other ∈ candidates,
      P93CyclophaneRCTReferenceRule candidates other → other = selected

structure P93CyclophaneRCTLocatedAssignment where
  center : Nat
  citation : P93AuthorityCitationToken
  side : RingSide
  descriptor : RCTDescriptor
  deriving DecidableEq, Repr

inductive P93CyclophaneCenterSpecification where
  | cip
      (context : BlueBookP93.Acyclic.NomenclatureContext)
      (kind : BlueBookP93.Acyclic.UnitKind)
      (descriptor : BlueBookP93.Acyclic.Descriptor)
  | relativeRCT
      (candidates : List P93CyclophaneRCTReferenceCandidate)
      (selected : P93CyclophaneRCTReferenceCandidate)
      (referenceSide : RingSide)
      (assignments : List P93CyclophaneRCTLocatedAssignment)
  deriving DecidableEq, Repr

structure P93CyclophaneCenterAuthorityObservation
    (policy : P93CyclophaneAuthorityPolicy) where
  system : P93AuthorityCyclophaneSystem
  unit : P93AuthorityPhysicalUnit
  citation : P93AuthorityCitationToken
  specification : P93CyclophaneCenterSpecification

def P93CyclophaneCenterAuthorityObservation.ValidFor
    (policy : P93CyclophaneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93CyclophaneCenterAuthorityObservation policy) : Prop :=
  observation.system.ValidFor policy source ∧
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
            candidate.ValidFor policy source observation.system) ∧
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
              assignment.side = referenceSide ∧
                assignment.descriptor = .reference
            else
              rctDescriptor referenceSide assignment.side =
                some assignment.descriptor

def P93CyclophaneDoubleBondExpected
    (totalNodes ringNodes : Nat)
    (geometry : MonocyclicSeniorLigandGeometry) :
    Option BlueBookP93.Acyclic.Descriptor :=
  if CyclophaneDoubleBondDescriptorRequired totalNodes ringNodes = true then
    match geometry with
    | .together => some .Z
    | .opposite => some .E
  else
    none

def P93CyclophaneDoubleBondDescriptorMatchesGeometry
    (geometry : MonocyclicSeniorLigandGeometry)
    (descriptor : BlueBookP93.Acyclic.Descriptor) : Prop :=
  match geometry, descriptor with
  | .together, .Z | .together, .cis
  | .opposite, .E | .opposite, .trans => True
  | _, _ => False

def P93CyclophaneDoubleBondDescriptorAllowed
    (context : BlueBookP93.Acyclic.NomenclatureContext) :
    MonocyclicSeniorLigandGeometry →
    Option BlueBookP93.Acyclic.Descriptor → Prop
  | _, none => True
  | geometry, some descriptor =>
      BlueBookP93.Acyclic.DescriptorRecommended
        context .ordinaryDoubleBond descriptor ∧
      P93CyclophaneDoubleBondDescriptorMatchesGeometry geometry descriptor

structure P93CyclophaneDoubleBondAuthorityObservation
    (policy : P93CyclophaneAuthorityPolicy) where
  system : P93AuthorityCyclophaneSystem
  unit : P93AuthorityPhysicalUnit
  ring : List Nat
  phaneRing : List Nat
  citation : P93AuthorityCitationToken
  geometry : MonocyclicSeniorLigandGeometry
  carbonContext : BlueBookP93.Acyclic.CarbonDoubleBondContext
  context : BlueBookP93.Acyclic.NomenclatureContext
  descriptor? : Option BlueBookP93.Acyclic.Descriptor

def P93CyclophaneDoubleBondAuthorityObservation.ValidFor
    (policy : P93CyclophaneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93CyclophaneDoubleBondAuthorityObservation policy) : Prop :=
  observation.system.ValidFor policy source ∧
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
    ((observation.descriptor? = some .cis ∨
        observation.descriptor? = some .trans) →
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

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P93AuthorityCyclophaneClosedRing
assert_kernel_only TetraStereo.OneCenter.P93CyclophanePlaneAuthorityObservation.ValidFor
assert_kernel_only TetraStereo.OneCenter.P93CyclophaneCenterAuthorityObservation.ValidFor
assert_kernel_only TetraStereo.OneCenter.P93CyclophaneDoubleBondAuthorityObservation.ValidFor
