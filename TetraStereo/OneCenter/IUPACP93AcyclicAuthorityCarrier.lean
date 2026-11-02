import TetraStereo.OneCenter.IUPACP93AuthorityConfigurationCarrier
import TetraStereo.OneCenter.P93AcyclicConfiguration

set_option autoImplicit false

/-!
# Authority carrier for the eleven acyclic P-93 provisions

This carrier binds P-93.4's independent descriptor/naming vocabulary to exact physical units in
`AuthoritativeChemicalInput`.  Atom centers, physical double bonds, and perceived cumulene axes
remain distinct; printed citations and parent-name components are nomenclature data; topology,
geometry, and descriptor observations enter only through an explicit audited policy.
-/

namespace TetraStereo.OneCenter

open BlueBookP93.Acyclic

def P93AcyclicUnitKindMatchesPhysical :
    UnitKind → P93AuthorityPhysicalUnit → Prop
  | .chiralCenter, .atomCenter _
  | .pseudoasymmetricCenter, .atomCenter _
  | .ordinaryDoubleBond, .bond _ _
  | .heteroatomDoubleBond, .bond _ _
  | .evenDoubleBondCumulene, .axis _
  | .oddDoubleBondCumulene, .axis _ => True
  | _, _ => False

/-- Whether the audited parent-name numbering is unique or competes with another permitted
numbering whose first stereochemical difference is cis/Z or trans/E. -/
inductive P93AcyclicNumberingCompetition where
  | unique
  | competing (alternativeCitations : List P93AuthorityCitationToken)
      (firstDifference : RelativeAttachment)
  deriving DecidableEq, Repr

/-- Relative-order rule for the two affix classes represented by P-93.4.1.  It permits repeated
affixes and does not pretend that these are the only affixes in a complete name; it says only that
no stereochemical affix occurs after the isotopic block has begun. -/
def P93AcyclicAffixOrderConforms : List AffixKind → Prop
  | [] => True
  | .stereochemical :: remaining => P93AcyclicAffixOrderConforms remaining
  | .isotopic :: remaining => ∀ affix ∈ remaining, affix = .isotopic

/-- Audited acyclic facts not derivable from the decoration-free physical carrier alone. -/
structure P93AcyclicAuthorityPolicy where
  Component : Type
  physicalObservation : P93AuthorityPhysicalObservationPolicy
  CitationAuthorized :
    AuthoritativeChemicalInput → P93AuthorityCitationToken →
      P93AuthorityPhysicalUnit → Prop
  ComponentAuthorized :
    AuthoritativeChemicalInput → Component → P93AuthorityPhysicalUnit → Prop
  AcyclicUnitObserved :
    AuthoritativeChemicalInput → P93AuthorityPhysicalUnit → Prop
  UnitKindObserved :
    AuthoritativeChemicalInput → P93AuthorityPhysicalUnit → UnitKind → Prop
  DescriptorAuthorized :
    AuthoritativeChemicalInput → P93AuthorityPhysicalUnit → Descriptor → Prop
  CarbonDoubleBondContextObserved :
    AuthoritativeChemicalInput → P93AuthorityPhysicalUnit →
      CarbonDoubleBondContext → Prop
  SingleCenterNamingObserved :
    AuthoritativeChemicalInput → P93AuthorityPhysicalUnit →
      Option P93AuthorityCitationToken → Bool → Bool → List AffixKind → Prop
  OddCumuleneTerminalGeometryObserved :
    AuthoritativeChemicalInput → List Nat → OddCumuleneTerminalGeometry → Prop
  MultipleCenterDescriptorsAuthorized :
    AuthoritativeChemicalInput →
      List (P93AuthorityPhysicalUnit × UnitKind × Descriptor) → Prop
  MultipleDoubleBondDescriptorsAuthorized :
    AuthoritativeChemicalInput →
      List (P93AuthorityPhysicalUnit × UnitKind × Descriptor) → Prop
  NumberingCompetitionObserved :
    AuthoritativeChemicalInput →
      List (P93AuthorityPhysicalUnit × Option P93AuthorityCitationToken) →
        P93AcyclicNumberingCompetition → Prop

/-- One independently judged acyclic assignment.  A citation is optional because P-93.4.1.1
expressly permits omission at a single center when the base name does not need a locant. -/
structure P93AcyclicAuthorityAssignment (policy : P93AcyclicAuthorityPolicy) where
  unit : P93AuthorityPhysicalUnit
  citation? : Option P93AuthorityCitationToken
  component : policy.Component
  kind : UnitKind
  descriptor : Descriptor

def P93AcyclicAuthorityAssignment.CitationValidFor
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assignment : P93AcyclicAuthorityAssignment policy) : Prop :=
  match assignment.citation? with
  | none => True
  | some citation =>
      citation.Valid ∧ policy.CitationAuthorized source citation assignment.unit

def P93AcyclicAuthorityAssignment.ValidFor
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assignment : P93AcyclicAuthorityAssignment policy) : Prop :=
  assignment.unit.ValidFor policy.physicalObservation source ∧
    P93AcyclicUnitKindMatchesPhysical assignment.kind assignment.unit ∧
    policy.AcyclicUnitObserved source assignment.unit ∧
    policy.UnitKindObserved source assignment.unit assignment.kind ∧
    DescriptorApplies assignment.kind assignment.descriptor ∧
    policy.DescriptorAuthorized source assignment.unit assignment.descriptor ∧
    policy.ComponentAuthorized source assignment.component assignment.unit ∧
    assignment.CitationValidFor policy source

def P93AcyclicPresentCitations
    {policy : P93AcyclicAuthorityPolicy}
    (assignments : List (P93AcyclicAuthorityAssignment policy)) :
    List P93AuthorityCitationToken :=
  assignments.filterMap fun assignment => assignment.citation?

def P93AcyclicAssignmentTriples
    {policy : P93AcyclicAuthorityPolicy}
    (assignments : List (P93AcyclicAuthorityAssignment policy)) :
    List (P93AuthorityPhysicalUnit × UnitKind × Descriptor) :=
  assignments.map fun assignment =>
    (assignment.unit, assignment.kind, assignment.descriptor)

/-- P-93.4.1.2 and P-93.4.2.1.2 place grouped descriptors at the front of the
complete name, or immediately before the component to which they belong. -/
def P93AcyclicGroupedDescriptorPlacement
    {Locant Component : Type*}
    (unit : LocatedUnit Locant Component)
    (position : CitationPosition Component) : Prop :=
  match position with
  | .frontOfCompleteName => True
  | .immediatelyBeforeComponent component => component = unit.component

def P93AcyclicAssignmentsValidFor
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assignments : List (P93AcyclicAuthorityAssignment policy)) : Prop :=
  assignments ≠ [] ∧
    ∀ assignment ∈ assignments, assignment.ValidFor policy source

structure P93AcyclicSingleCenterAuthorityObservation
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : P93AcyclicAuthorityAssignment policy
  centerNeedsLocantInBaseName : Bool
  isotopicAffixPresent : Bool
  observedAffixOrder : List AffixKind

def P93AcyclicSingleCenterAuthorityObservation.ValidFor
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicSingleCenterAuthorityObservation policy) : Prop :=
  observation.assignment.ValidFor policy source ∧
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
    (observation.isotopicAffixPresent = true ↔
      .isotopic ∈ observation.observedAffixOrder)

/-- Authority observation for P-93.4.1.2.  The historical provision identifier says
"multiple descriptors one center", but the Blue Book rule concerns two or more distinct
stereogenic centers in one parent structure. -/
structure P93AcyclicMultipleCenterDescriptorsAuthorityObservation
    (policy : P93AcyclicAuthorityPolicy) where
  assignments : List (P93AcyclicAuthorityAssignment policy)

def P93AcyclicMultipleCenterDescriptorsAuthorityObservation.ValidFor
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation :
      P93AcyclicMultipleCenterDescriptorsAuthorityObservation policy) : Prop :=
  P93AcyclicAssignmentsValidFor policy source observation.assignments ∧
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

structure P93AcyclicPrefixComponentAuthorityObservation
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : P93AcyclicAuthorityAssignment policy
  observedPosition : CitationPosition policy.Component

def P93AcyclicPrefixComponentAuthorityObservation.ValidFor
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicPrefixComponentAuthorityObservation policy) : Prop :=
  observation.assignment.ValidFor policy source ∧
    CorrectComponentPlacement
      { locant := observation.assignment.citation?
        component := observation.assignment.component
        kind := observation.assignment.kind
        descriptor := observation.assignment.descriptor }
      observation.observedPosition

structure P93AcyclicDoubleBondAuthorityObservation
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : P93AcyclicAuthorityAssignment policy
  context : NomenclatureContext
  carbonContext : CarbonDoubleBondContext

def P93AcyclicDoubleBondAuthorityObservation.ValidFor
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicDoubleBondAuthorityObservation policy) : Prop :=
  observation.assignment.ValidFor policy source ∧
    observation.assignment.kind = .ordinaryDoubleBond ∧
    policy.CarbonDoubleBondContextObserved source observation.assignment.unit
      observation.carbonContext ∧
    DescriptorRecommended observation.context .ordinaryDoubleBond
      observation.assignment.descriptor ∧
    ((observation.assignment.descriptor = .cis ∨
      observation.assignment.descriptor = .trans) →
        CisTransGeneralApplicable observation.carbonContext)

structure P93AcyclicHeteroDoubleBondAuthorityObservation
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : P93AcyclicAuthorityAssignment policy
  context : NomenclatureContext

def P93AcyclicHeteroDoubleBondAuthorityObservation.ValidFor
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicHeteroDoubleBondAuthorityObservation policy) : Prop :=
  observation.assignment.ValidFor policy source ∧
    observation.assignment.kind = .heteroatomDoubleBond

structure P93AcyclicMultipleDoubleBondAuthorityObservation
    (policy : P93AcyclicAuthorityPolicy) where
  assignments : List (P93AcyclicAuthorityAssignment policy)

def P93AcyclicMultipleDoubleBondAuthorityObservation.ValidFor
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicMultipleDoubleBondAuthorityObservation policy) : Prop :=
  P93AcyclicAssignmentsValidFor policy source observation.assignments ∧
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

structure P93AcyclicEvenCumuleneAuthorityObservation
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : P93AcyclicAuthorityAssignment policy
  context : NomenclatureContext
  generalDescriptor : Descriptor
  preferredDescriptor : Descriptor

def P93AcyclicEvenCumuleneAuthorityObservation.ValidFor
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicEvenCumuleneAuthorityObservation policy) : Prop :=
  observation.assignment.ValidFor policy source ∧
    observation.assignment.kind = .evenDoubleBondCumulene ∧
    EvenCumuleneAxialDescriptorCorrespondence observation.generalDescriptor
      observation.preferredDescriptor ∧
    observation.assignment.descriptor =
      (match observation.context with
      | .preferredIUPACName => observation.preferredDescriptor
      | .general => observation.generalDescriptor) ∧
    DescriptorRecommended observation.context .evenDoubleBondCumulene
      observation.assignment.descriptor

structure P93AcyclicOddCumuleneAuthorityObservation
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : P93AcyclicAuthorityAssignment policy
  geometry : OddCumuleneTerminalGeometry

def P93AcyclicOddCumuleneAuthorityObservation.ValidFor
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicOddCumuleneAuthorityObservation policy) : Prop :=
  observation.assignment.ValidFor policy source ∧
    observation.assignment.kind = .oddDoubleBondCumulene ∧
    (∃ path, observation.assignment.unit = .axis path ∧
      policy.OddCumuleneTerminalGeometryObserved source path observation.geometry) ∧
    OddCumuleneEZAssignment observation.geometry observation.assignment.descriptor

structure P93AcyclicPlacedAssignment
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : P93AcyclicAuthorityAssignment policy
  observedPosition : CitationPosition policy.Component

structure P93AcyclicMultipleUnitsAuthorityObservation
    (policy : P93AcyclicAuthorityPolicy) where
  assignments : List (P93AcyclicPlacedAssignment policy)
  numberingCompetition : P93AcyclicNumberingCompetition

def P93AcyclicMultipleUnitsAuthorityObservation.ValidFor
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AcyclicMultipleUnitsAuthorityObservation policy) : Prop :=
  2 ≤ observation.assignments.length ∧
    (∀ placed ∈ observation.assignments,
      placed.assignment.ValidFor policy source ∧
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

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P93AcyclicAuthorityAssignment.ValidFor
assert_kernel_only
  TetraStereo.OneCenter.P93AcyclicMultipleDoubleBondAuthorityObservation.ValidFor
assert_kernel_only TetraStereo.OneCenter.P93AcyclicMultipleUnitsAuthorityObservation.ValidFor
