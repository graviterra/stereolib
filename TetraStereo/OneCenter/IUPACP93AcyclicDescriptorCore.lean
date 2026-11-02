import TetraStereo.OneCenter.IUPACP93AcyclicAuthorityCarrier

set_option autoImplicit false

/-!
# Policy-free physical core for the ready acyclic P-93 descriptor families

The three kinds in this file have source validity that is already determined by
`AuthoritativeChemicalInput`: a heteroatom double-bond unit is an actual bounded binary bond, and
an even or odd cumulene unit is an independently perceived canonical cumulene axis.  Consequently
none of their physical validity needs an audited qualitative-observation policy.

This is intentionally a one-way, forgetful boundary.  An authority assignment valid under a
supplied policy projects to this core, but the core does not recover citations, name components,
acyclic classification, nomenclature recommendations, or descriptor authorization.  In
particular, no converse to the projection theorem is claimed here.
-/

namespace TetraStereo.OneCenter

open BlueBookP93.Acyclic

/-- The acyclic descriptor kinds whose physical carriers are completely checkable from the
authoritative molecular source. -/
inductive P93AcyclicDescriptorCoreKind where
  | heteroatomDoubleBond
  | evenCumulene
  | oddCumulene
  deriving DecidableEq, Repr

namespace P93AcyclicDescriptorCoreKind

/-- The independent P-93 unit kind represented by a policy-free core kind. -/
def unitKind : P93AcyclicDescriptorCoreKind → UnitKind
  | .heteroatomDoubleBond => .heteroatomDoubleBond
  | .evenCumulene => .evenDoubleBondCumulene
  | .oddCumulene => .oddDoubleBondCumulene

/-- Direct, policy-free physical source validity for a ready acyclic descriptor kind. -/
def SourceValidFor
    (kind : P93AcyclicDescriptorCoreKind)
    (source : AuthoritativeChemicalInput)
    (unit : P93AuthorityPhysicalUnit) : Prop :=
  match kind, unit with
  | .heteroatomDoubleBond, .bond first second =>
      first < source.molecule.atomCount ∧
        second < source.molecule.atomCount ∧
        first < second ∧
        P93AuthorityBinaryBond source first second
  | .evenCumulene, .axis path =>
      P93AuthorityCanonicalEvenCumuleneAxisPerceived source path
  | .oddCumulene, .axis path =>
      P93AuthorityCanonicalOddCumuleneAxisPerceived source path
  | _, _ => False

/-- The source-checkable classification evidence not present in the kind-agnostic physical-unit
carrier.  In particular, an axis does not become even or odd merely because a policy labels it
with that kind. -/
def ClassificationValidFor
    (kind : P93AcyclicDescriptorCoreKind)
    (unit : P93AuthorityPhysicalUnit) : Prop :=
  match kind, unit with
  | .heteroatomDoubleBond, .bond _ _ => True
  | .evenCumulene, .axis path => Even (path.length - 1)
  | .oddCumulene, .axis path => Odd (path.length - 1)
  | _, _ => False

/-- Kind-agnostic physical validity plus independent kind classification yields the strengthened
source validity.  The explicit classification premise prevents an audited kind label from
laundering even/odd parity. -/
theorem sourceValidFor_of_physicalUnit_validFor
    (kind : P93AcyclicDescriptorCoreKind)
    (physicalPolicy : P93AuthorityPhysicalObservationPolicy)
    (source : AuthoritativeChemicalInput)
    (unit : P93AuthorityPhysicalUnit)
    (physicalValid : unit.ValidFor physicalPolicy source)
    (kindMatches : P93AcyclicUnitKindMatchesPhysical kind.unitKind unit)
    (classificationValid : kind.ClassificationValidFor unit) :
    kind.SourceValidFor source unit := by
  cases kind <;> cases unit <;>
    simp_all [SourceValidFor, ClassificationValidFor, unitKind,
      P93AuthorityCanonicalEvenCumuleneAxisPerceived,
      P93AuthorityCanonicalOddCumuleneAxisPerceived,
      P93AuthorityPhysicalUnit.ValidFor,
      P93AcyclicUnitKindMatchesPhysical]

end P93AcyclicDescriptorCoreKind

/-- A descriptor-bearing physical assignment with no citation, component, naming, or audited
policy payload.  Its kind is restricted by construction to the three source-checkable families. -/
structure P93AcyclicDescriptorCore where
  kind : P93AcyclicDescriptorCoreKind
  unit : P93AuthorityPhysicalUnit
  descriptor : Descriptor
  deriving DecidableEq

namespace P93AcyclicDescriptorCore

/-- All validity retained by the physical descriptor core: direct source evidence, exact
kind/carrier compatibility, and applicability of the descriptor vocabulary. -/
def ValidFor
    (source : AuthoritativeChemicalInput)
    (core : P93AcyclicDescriptorCore) : Prop :=
  core.kind.SourceValidFor source core.unit ∧
    P93AcyclicUnitKindMatchesPhysical core.kind.unitKind core.unit ∧
    DescriptorApplies core.kind.unitKind core.descriptor

end P93AcyclicDescriptorCore

namespace P93AcyclicAuthorityAssignment

/-- Forget the authority/nomenclature payload of an assignment after identifying it as one of the
three source-checkable descriptor kinds. -/
def toDescriptorCore
    {policy : P93AcyclicAuthorityPolicy}
    (assignment : P93AcyclicAuthorityAssignment policy)
    (kind : P93AcyclicDescriptorCoreKind)
    (_kindEq : assignment.kind = kind.unitKind) : P93AcyclicDescriptorCore :=
  { kind
    unit := assignment.unit
    descriptor := assignment.descriptor }

/-- A valid authority assignment of a ready kind with independently checked classification has
a valid policy-free physical core.

This implication uses only the assignment's physical-unit validity, physical kind compatibility,
independent even/odd classification, and descriptor applicability.  All policy-specific
observation, authorization, citation, and component premises are forgotten. -/
theorem toDescriptorCore_validFor
    (policy : P93AcyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (assignment : P93AcyclicAuthorityAssignment policy)
    (kind : P93AcyclicDescriptorCoreKind)
    (assignmentValid : assignment.ValidFor policy source)
    (kindEq : assignment.kind = kind.unitKind)
    (classificationValid : kind.ClassificationValidFor assignment.unit) :
    (assignment.toDescriptorCore kind kindEq).ValidFor source := by
  rcases assignmentValid with
    ⟨physicalValid, kindMatches, _acyclicObserved, _kindObserved,
      descriptorApplies, _descriptorAuthorized, _componentAuthorized, _citationValid⟩
  rw [kindEq] at kindMatches descriptorApplies
  exact
    ⟨kind.sourceValidFor_of_physicalUnit_validFor policy.physicalObservation source
        assignment.unit physicalValid kindMatches classificationValid,
      kindMatches,
      descriptorApplies⟩

end P93AcyclicAuthorityAssignment

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93AcyclicDescriptorCoreKind.sourceValidFor_of_physicalUnit_validFor
assert_kernel_only TetraStereo.OneCenter.P93AcyclicDescriptorCore.ValidFor
assert_kernel_only
  TetraStereo.OneCenter.P93AcyclicAuthorityAssignment.toDescriptorCore_validFor
