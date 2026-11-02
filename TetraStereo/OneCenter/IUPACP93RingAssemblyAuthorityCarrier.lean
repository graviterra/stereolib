import TetraStereo.OneCenter.IUPACP93MonocyclicAuthorityCarrier
import TetraStereo.OneCenter.CIPObservedAxialSpatialConformance

set_option autoImplicit false

/-!
# Authority carrier for P-93.5.7 ring assemblies

One checked assembly graph supports the three source rows.  Axial assignments reuse exact
CIP-ranked rational geometry and convert `Rₐ/Sₐ` to the preferred `M/P` vocabulary.  Center
assignments carry preferred CIP descriptors and only optionally carry an equivalent `cis/trans`
general-nomenclature descriptor.  Double-bond assignments are an all-and-only corpus under the
P-91.2.2 applicability policy, strengthened so that one required descriptor in an eight-membered
ring makes every stereogenic double bond in that ring required.
-/

namespace TetraStereo.OneCenter

open BlueBookP93.Cyclic

structure P93RingAssemblyJunction where
  leftRingIndex : Nat
  rightRingIndex : Nat
  leftAtom : Nat
  rightAtom : Nat
  deriving DecidableEq, Repr

structure P93AuthorityRingAssembly where
  rings : List (List Nat)
  junctions : List P93RingAssemblyJunction
  deriving DecidableEq, Repr

def P93RingAssemblyJunction.ValidFor
    (source : AuthoritativeChemicalInput)
    (assembly : P93AuthorityRingAssembly)
    (junction : P93RingAssemblyJunction) : Prop :=
  junction.leftRingIndex < junction.rightRingIndex ∧
    ∃ leftRing rightRing,
      assembly.rings[junction.leftRingIndex]? = some leftRing ∧
        assembly.rings[junction.rightRingIndex]? = some rightRing ∧
        junction.leftAtom ∈ leftRing ∧
        junction.rightAtom ∈ rightRing ∧
        P93AuthorityBinaryBond source junction.leftAtom junction.rightAtom

def P93RingAssemblyIndicesJoined
    (assembly : P93AuthorityRingAssembly) (left right : Nat) : Prop :=
  ∃ junction ∈ assembly.junctions,
    (junction.leftRingIndex = left ∧ junction.rightRingIndex = right) ∨
      (junction.leftRingIndex = right ∧ junction.rightRingIndex = left)

def P93RingAssemblyIndexPath
    (assembly : P93AuthorityRingAssembly) : List Nat → Prop
  | [] | [_] => True
  | first :: second :: remaining =>
      P93RingAssemblyIndicesJoined assembly first second ∧
        P93RingAssemblyIndexPath assembly (second :: remaining)

def P93RingAssemblyConnected (assembly : P93AuthorityRingAssembly) : Prop :=
  ∀ first, first < assembly.rings.length →
    ∀ second, second < assembly.rings.length →
      ∃ path,
        path.Nodup ∧
          (∀ index ∈ path, index < assembly.rings.length) ∧
          path.head? = some first ∧ path.getLast? = some second ∧
          P93RingAssemblyIndexPath assembly path

def P93AuthorityRingAssembly.MechanicallyValidFor
    (source : AuthoritativeChemicalInput)
    (assembly : P93AuthorityRingAssembly) : Prop :=
  2 ≤ assembly.rings.length ∧
    (assembly.rings.map List.toFinset).Nodup ∧
    (∀ ring ∈ assembly.rings, P93AuthorityClosedCycle source ring) ∧
    (∀ (leftIndex : Nat) (leftRing : List Nat),
      assembly.rings[leftIndex]? = some leftRing →
        ∀ (rightIndex : Nat) (rightRing : List Nat),
          assembly.rings[rightIndex]? = some rightRing →
            leftIndex ≠ rightIndex →
              Disjoint leftRing.toFinset rightRing.toFinset) ∧
    assembly.junctions ≠ [] ∧ assembly.junctions.Nodup ∧
    (∀ junction ∈ assembly.junctions, junction.ValidFor source assembly) ∧
    P93RingAssemblyConnected assembly

structure P93RingAssemblyAuthorityPolicy where
  physicalObservation : P93AuthorityPhysicalObservationPolicy
  AssemblyObserved :
    AuthoritativeChemicalInput → P93AuthorityRingAssembly → Prop
  AxisEligible :
    AuthoritativeChemicalInput → P93AuthorityRingAssembly →
      P93RingAssemblyJunction → Prop
  AxisCitationAuthorized :
    AuthoritativeChemicalInput → P93AuthorityRingAssembly →
      P93RingAssemblyJunction → P93AuthorityCitationToken → Prop
  AxisDescriptorsObserved :
    AuthoritativeChemicalInput → P93AuthorityRingAssembly →
      P93RingAssemblyJunction → RingAssemblyAxisDescriptor →
        RingAssemblyAxisDescriptor → Prop
  CenterEligible :
    AuthoritativeChemicalInput → P93AuthorityRingAssembly → Nat → Prop
  CenterCitationAuthorized :
    AuthoritativeChemicalInput → P93AuthorityRingAssembly → Nat →
      P93AuthorityCitationToken → Prop
  CenterCIPDescriptorAuthorized :
    AuthoritativeChemicalInput → P93AuthorityRingAssembly → Nat →
      RingAssemblyCenterDescriptor → Prop
  CenterGeneralDescriptorEquivalent :
    AuthoritativeChemicalInput → P93AuthorityRingAssembly → Nat →
      RingAssemblyCenterDescriptor → RingAssemblyCenterDescriptor → Prop
  DoubleBondStereogenic :
    AuthoritativeChemicalInput → P93AuthorityRingAssembly →
      Nat → Nat → Nat → Prop
  DoubleBondNeedsSpecificationUnderP9122 :
    AuthoritativeChemicalInput → P93AuthorityRingAssembly →
      Nat → Nat → Nat → Prop
  DoubleBondCitationAuthorized :
    AuthoritativeChemicalInput → P93AuthorityRingAssembly →
      Nat → Nat → Nat → P93AuthorityCitationToken → Prop
  DoubleBondDescriptorAuthorized :
    AuthoritativeChemicalInput → P93AuthorityRingAssembly →
      Nat → Nat → Nat → BlueBookP93.Acyclic.Descriptor → Prop

def P93AuthorityRingAssembly.ValidFor
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assembly : P93AuthorityRingAssembly) : Prop :=
  assembly.MechanicallyValidFor source ∧ policy.AssemblyObserved source assembly

def P93RingAssemblyAxisFrameValid
    (source : AuthoritativeChemicalInput)
    (assembly : P93AuthorityRingAssembly)
    (junction : P93RingAssemblyJunction)
    (record : IndexedAxialGeometryObservation) : Prop :=
  record.axisStart = junction.leftAtom ∧
    record.axisEnd = junction.rightAtom ∧
    ∃ leftRing rightRing,
      assembly.rings[junction.leftRingIndex]? = some leftRing ∧
        assembly.rings[junction.rightRingIndex]? = some rightRing ∧
        record.startFirst ∈ leftRing ∧ record.startSecond ∈ leftRing ∧
        record.endFirst ∈ rightRing ∧ record.endSecond ∈ rightRing ∧
        record.startFirst ≠ record.startSecond ∧
        record.endFirst ≠ record.endSecond ∧
        P93AuthorityBinaryBond source record.axisStart record.startFirst ∧
        P93AuthorityBinaryBond source record.axisStart record.startSecond ∧
        P93AuthorityBinaryBond source record.axisEnd record.endFirst ∧
        P93AuthorityBinaryBond source record.axisEnd record.endSecond

def preferredRingAssemblyAxisDescriptor : AxialDescriptor → RingAssemblyAxisDescriptor
  | .Ra => .M
  | .Sa => .P

def generalRingAssemblyAxisDescriptor : AxialDescriptor → RingAssemblyAxisDescriptor
  | .Ra => .Ra
  | .Sa => .Sa

structure P93RingAssemblyAxisAssignment where
  junction : P93RingAssemblyJunction
  record : IndexedAxialGeometryObservation
  citation : P93AuthorityCitationToken
  cipDescriptor : AxialDescriptor
  preferredDescriptor : RingAssemblyAxisDescriptor
  generalDescriptor : RingAssemblyAxisDescriptor
  deriving DecidableEq, Repr

def P93RingAssemblyAxisAssignment.ValidFor
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assembly : P93AuthorityRingAssembly)
    (result : ChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (assignment : P93RingAssemblyAxisAssignment) : Prop :=
  assignment.junction ∈ assembly.junctions ∧
    policy.AxisEligible source assembly assignment.junction ∧
    P93RingAssemblyAxisFrameValid source assembly assignment.junction assignment.record ∧
    assignment.cipDescriptor = AxialDescriptor.ofSense assignment.record.sense ∧
    BlueBookP93.GeometryIngress.RationalAxialObservationJudgment
      result spatial assignment.record assignment.cipDescriptor ∧
    assignment.preferredDescriptor =
      preferredRingAssemblyAxisDescriptor assignment.cipDescriptor ∧
    assignment.generalDescriptor =
      generalRingAssemblyAxisDescriptor assignment.cipDescriptor ∧
    PreferredRingAssemblyAxisDescriptor assignment.preferredDescriptor ∧
    policy.AxisDescriptorsObserved source assembly assignment.junction
      assignment.preferredDescriptor assignment.generalDescriptor ∧
    assignment.citation.Valid ∧
    policy.AxisCitationAuthorized source assembly assignment.junction assignment.citation

structure P93RingAssemblyAxesAuthorityObservation
    (policy : P93RingAssemblyAuthorityPolicy) where
  assembly : P93AuthorityRingAssembly
  normalization : ChemistryNormalizationResult
  spatial : SpatialConfiguration
  assignments : List P93RingAssemblyAxisAssignment

def P93RingAssemblyAxesAuthorityObservation.ValidFor
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RingAssemblyAxesAuthorityObservation policy) : Prop :=
  observation.assembly.ValidFor policy source ∧
    source.spatial? = some observation.spatial ∧
    observation.normalization.parsed.AuthoritativeStructureAgreement source ∧
    observation.normalization = normalizeRawMolecule observation.normalization.parsed ∧
    observation.assignments ≠ [] ∧
    (observation.assignments.map fun assignment => assignment.junction).Nodup ∧
    (observation.assignments.map fun assignment => assignment.citation).Nodup ∧
    (∀ assignment ∈ observation.assignments,
      assignment.ValidFor policy source observation.assembly
        observation.normalization observation.spatial) ∧
    ∀ junction ∈ observation.assembly.junctions,
      policy.AxisEligible source observation.assembly junction →
        ∃ assignment ∈ observation.assignments, assignment.junction = junction

structure P93RingAssemblyCenterAssignment where
  center : Nat
  citation : P93AuthorityCitationToken
  preferredDescriptor : RingAssemblyCenterDescriptor
  generalDescriptor? : Option RingAssemblyCenterDescriptor
  deriving DecidableEq, Repr

def P93RingAssemblyGeneralCenterDescriptor : RingAssemblyCenterDescriptor → Prop
  | .cis | .trans => True
  | _ => False

def P93RingAssemblyCenterInExactlyOneRing
    (assembly : P93AuthorityRingAssembly) (center : Nat) : Prop :=
  ∃ (ringIndex : Nat) (ring : List Nat),
    assembly.rings[ringIndex]? = some ring ∧ center ∈ ring ∧
      ∀ (otherIndex : Nat) (otherRing : List Nat),
        assembly.rings[otherIndex]? = some otherRing →
          center ∈ otherRing → otherIndex = ringIndex

def P93RingAssemblyCenterAssignment.ValidFor
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assembly : P93AuthorityRingAssembly)
    (assignment : P93RingAssemblyCenterAssignment) : Prop :=
  P93RingAssemblyCenterInExactlyOneRing assembly assignment.center ∧
    (P93AuthorityPhysicalUnit.atomCenter assignment.center).ValidFor
      policy.physicalObservation source ∧
    policy.CenterEligible source assembly assignment.center ∧
    PreferredRingAssemblyCenterDescriptor assignment.preferredDescriptor ∧
    policy.CenterCIPDescriptorAuthorized source assembly assignment.center
      assignment.preferredDescriptor ∧
    assignment.citation.Valid ∧
    policy.CenterCitationAuthorized source assembly assignment.center
      assignment.citation ∧
    match assignment.generalDescriptor? with
    | none => True
    | some generalDescriptor =>
        P93RingAssemblyGeneralCenterDescriptor generalDescriptor ∧
          policy.CenterGeneralDescriptorEquivalent source assembly assignment.center
            assignment.preferredDescriptor generalDescriptor

structure P93RingAssemblyCentersAuthorityObservation
    (policy : P93RingAssemblyAuthorityPolicy) where
  assembly : P93AuthorityRingAssembly
  assignments : List P93RingAssemblyCenterAssignment

def P93RingAssemblyCentersAuthorityObservation.ValidFor
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RingAssemblyCentersAuthorityObservation policy) : Prop :=
  observation.assembly.ValidFor policy source ∧
    observation.assignments ≠ [] ∧
    (observation.assignments.map fun assignment => assignment.center).Nodup ∧
    (observation.assignments.map fun assignment => assignment.citation).Nodup ∧
    (∀ assignment ∈ observation.assignments,
      assignment.ValidFor policy source observation.assembly) ∧
    ∀ center,
      policy.CenterEligible source observation.assembly center →
        ∃ assignment ∈ observation.assignments, assignment.center = center

structure P93RingAssemblyDoubleBondAssignment where
  ringIndex : Nat
  first : Nat
  second : Nat
  citation : P93AuthorityCitationToken
  descriptor : BlueBookP93.Acyclic.Descriptor
  deriving DecidableEq, Repr

def P93RingAssemblyEZDescriptor : BlueBookP93.Acyclic.Descriptor → Prop
  | .E | .Z => True
  | _ => False

/-- Undirected adjacency in the audited named cyclic traversal of one assembly ring. -/
def P93RingAssemblyNamedCycleEdge
    (ring : List Nat) (left right : Nat) : Prop :=
  ∃ leftMember : left ∈ ring,
    ring.next left leftMember = right ∨ ring.prev left leftMember = right

def P93RingAssemblyBondInRing
    (source : AuthoritativeChemicalInput)
    (assembly : P93AuthorityRingAssembly)
    (ringIndex first second : Nat) : Prop :=
  first < second ∧
    ∃ ring,
      assembly.rings[ringIndex]? = some ring ∧
        first ∈ ring ∧ second ∈ ring ∧
        P93RingAssemblyNamedCycleEdge ring first second ∧
        P93AuthorityBinaryBond source first second

def P93RingAssemblyDoubleBondRequired
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assembly : P93AuthorityRingAssembly)
    (ringIndex first second : Nat) : Prop :=
  policy.DoubleBondStereogenic source assembly ringIndex first second ∧
    (policy.DoubleBondNeedsSpecificationUnderP9122
        source assembly ringIndex first second ∨
      ∃ ring,
        assembly.rings[ringIndex]? = some ring ∧ ring.length = 8 ∧
          ∃ triggerFirst triggerSecond,
            P93RingAssemblyBondInRing source assembly ringIndex
              triggerFirst triggerSecond ∧
            policy.DoubleBondStereogenic source assembly ringIndex
              triggerFirst triggerSecond ∧
            policy.DoubleBondNeedsSpecificationUnderP9122 source assembly ringIndex
              triggerFirst triggerSecond)

def P93RingAssemblyDoubleBondAssignment.ValidFor
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assembly : P93AuthorityRingAssembly)
    (assignment : P93RingAssemblyDoubleBondAssignment) : Prop :=
  P93RingAssemblyBondInRing source assembly assignment.ringIndex
      assignment.first assignment.second ∧
    P93RingAssemblyDoubleBondRequired policy source assembly assignment.ringIndex
      assignment.first assignment.second ∧
    P93RingAssemblyEZDescriptor assignment.descriptor ∧
    policy.DoubleBondDescriptorAuthorized source assembly assignment.ringIndex
      assignment.first assignment.second assignment.descriptor ∧
    assignment.citation.Valid ∧
    policy.DoubleBondCitationAuthorized source assembly assignment.ringIndex
      assignment.first assignment.second assignment.citation

structure P93RingAssemblyDoubleBondsAuthorityObservation
    (policy : P93RingAssemblyAuthorityPolicy) where
  assembly : P93AuthorityRingAssembly
  assignments : List P93RingAssemblyDoubleBondAssignment

def P93RingAssemblyDoubleBondsAuthorityObservation.ValidFor
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RingAssemblyDoubleBondsAuthorityObservation policy) : Prop :=
  observation.assembly.ValidFor policy source ∧
    observation.assignments ≠ [] ∧
    (observation.assignments.map fun assignment =>
      (assignment.ringIndex, assignment.first, assignment.second)).Nodup ∧
    (observation.assignments.map fun assignment => assignment.citation).Nodup ∧
    (∀ assignment ∈ observation.assignments,
      assignment.ValidFor policy source observation.assembly) ∧
    ∀ ringIndex first second,
      P93RingAssemblyBondInRing source observation.assembly ringIndex first second →
      P93RingAssemblyDoubleBondRequired policy source observation.assembly
        ringIndex first second →
        ∃ assignment ∈ observation.assignments,
          assignment.ringIndex = ringIndex ∧ assignment.first = first ∧
            assignment.second = second

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P93AuthorityRingAssembly.MechanicallyValidFor
assert_kernel_only TetraStereo.OneCenter.P93RingAssemblyAxesAuthorityObservation.ValidFor
assert_kernel_only TetraStereo.OneCenter.P93RingAssemblyCentersAuthorityObservation.ValidFor
assert_kernel_only TetraStereo.OneCenter.P93RingAssemblyDoubleBondsAuthorityObservation.ValidFor
