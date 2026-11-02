import TetraStereo.OneCenter.IUPACRemaining71P93GeneralReviewedSemantics
import TetraStereo.OneCenter.OrganicStereoNativeP94SourceContext
import TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress
import TetraStereo.OneCenter.OrganicStereoP93AcyclicIngress

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false





























































































namespace TetraStereo.OneCenter

namespace OrganicStereoP93GeneralAuthorityIngress

open TetraStereo.OneCenter.IUPACNormativeProvision
open TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress
open TetraStereo.OneCenter.OrganicStereoNativeP94SourceContext
open TetraStereo.OneCenter.BlueBookP93.GeneralConfiguration

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]
variable {policy : P93GeneralAuthorityPolicy}
variable {n : ℕ}

/-! ## Bounded raw units

`P93AuthorityPhysicalUnit.BoundedIn` is the only arithmetic side condition of relabelling.  The
generic name below keeps it separate from the per-observation bound predicates. -/

/-- Every raw atom reference of a P-93 physical unit lies below `n`. -/
abbrev UnitBoundedIn (n : ℕ) (unit : P93AuthorityPhysicalUnit) : Prop :=
  OrganicStereoSuppliedCitationIngress.P93AuthorityPhysicalUnit.BoundedIn n unit

/-! ## Native located assignments -/

/-- A located P-93 general-configuration assignment over native atom vertices.

The descriptor type is the *arbitrary* policy descriptor type.  This is the generic counterpart of
`OrganicStereoSuppliedCitationIngress.SuppliedLocatedAssignment`, whose descriptor is fixed to
`BlueBookP91.Descriptor` and therefore cannot carry a general P-93 policy. -/
structure NativeLocatedAssignment (policy : P93GeneralAuthorityPolicy) (V : Type*) where
  /-- The physical stereogenic unit with atom references in `V`. -/
  unit : SuppliedPhysicalUnit V
  /-- The full source citation token, copied literally. -/
  citation : P93AuthorityCitationToken
  /-- The audited policy descriptor, copied literally. -/
  descriptor : policy.Descriptor

/-- Relabel one raw assignment into `V`; unit references move, citation and descriptor do not. -/
def relabelNativeAssignment (enumeration : V ≃ Fin n)
    (assignment : P93AuthorityLocatedAssignment policy.Descriptor)
    (bounded : UnitBoundedIn n assignment.unit) :
    NativeLocatedAssignment policy V where
  unit := relabelUnit enumeration assignment.unit bounded
  citation := assignment.citation
  descriptor := assignment.descriptor

/-- Decode one native assignment to the raw P-93 carrier. -/
def unrelabelNativeAssignment (enumeration : V ≃ Fin n)
    (assignment : NativeLocatedAssignment policy V) :
    P93AuthorityLocatedAssignment policy.Descriptor where
  unit := unrelabelUnit enumeration assignment.unit
  citation := assignment.citation
  descriptor := assignment.descriptor

@[simp] theorem unrelabelNativeAssignment_citation (enumeration : V ≃ Fin n)
    (assignment : NativeLocatedAssignment policy V) :
    (unrelabelNativeAssignment enumeration assignment).citation = assignment.citation := rfl

@[simp] theorem unrelabelNativeAssignment_descriptor (enumeration : V ≃ Fin n)
    (assignment : NativeLocatedAssignment policy V) :
    (unrelabelNativeAssignment enumeration assignment).descriptor = assignment.descriptor := rfl

/-- Exact recovery of one located assignment. -/
theorem unrelabelNativeAssignment_relabelNativeAssignment (enumeration : V ≃ Fin n)
    (assignment : P93AuthorityLocatedAssignment policy.Descriptor)
    (bounded : UnitBoundedIn n assignment.unit) :
    unrelabelNativeAssignment enumeration
        (relabelNativeAssignment enumeration assignment bounded) = assignment := by
  rcases assignment with ⟨unit, citation, descriptor⟩
  simp [unrelabelNativeAssignment, relabelNativeAssignment, unrelabelUnit_relabelUnit]

/-- Relabelling a decoded assignment returns it exactly; this direction needs no source validity. -/
theorem relabelNativeAssignment_unrelabelNativeAssignment (enumeration : V ≃ Fin n)
    (assignment : NativeLocatedAssignment policy V) :
    relabelNativeAssignment enumeration (unrelabelNativeAssignment enumeration assignment)
        (unrelabelUnitBounded enumeration assignment.unit) = assignment := by
  rcases assignment with ⟨unit, citation, descriptor⟩
  simp [unrelabelNativeAssignment, relabelNativeAssignment, relabelUnit_unrelabelUnit]

/-! ## Ordered assignment lists -/

/-- Relabel an ordered list of bounded raw assignments.  Order and multiplicity are retained. -/
def relabelNativeAssignments (enumeration : V ≃ Fin n)
    (assignments : List (P93AuthorityLocatedAssignment policy.Descriptor))
    (bounded : ∀ assignment ∈ assignments, UnitBoundedIn n assignment.unit) :
    List (NativeLocatedAssignment policy V) :=
  assignments.attach.map fun assignment =>
    relabelNativeAssignment enumeration assignment.1 (bounded assignment.1 assignment.2)

/-- Decode an ordered list of native assignments. -/
def unrelabelNativeAssignments (enumeration : V ≃ Fin n)
    (assignments : List (NativeLocatedAssignment policy V)) :
    List (P93AuthorityLocatedAssignment policy.Descriptor) :=
  assignments.map (unrelabelNativeAssignment enumeration)

/-- Every decoded assignment in a list satisfies the explicit representation bounds. -/
def unrelabelNativeAssignmentsBounded (enumeration : V ≃ Fin n)
    (assignments : List (NativeLocatedAssignment policy V)) :
    ∀ assignment ∈ unrelabelNativeAssignments enumeration assignments,
      UnitBoundedIn n assignment.unit := by
  intro assignment member
  rw [unrelabelNativeAssignments, List.mem_map] at member
  rcases member with ⟨native, _nativeMember, rfl⟩
  exact unrelabelUnitBounded enumeration native.unit

@[simp] theorem relabelNativeAssignments_length (enumeration : V ≃ Fin n)
    (assignments : List (P93AuthorityLocatedAssignment policy.Descriptor))
    (bounded : ∀ assignment ∈ assignments, UnitBoundedIn n assignment.unit) :
    (relabelNativeAssignments enumeration assignments bounded).length =
      assignments.length := by
  simp [relabelNativeAssignments]

@[simp] theorem unrelabelNativeAssignments_length (enumeration : V ≃ Fin n)
    (assignments : List (NativeLocatedAssignment policy V)) :
    (unrelabelNativeAssignments enumeration assignments).length = assignments.length := by
  simp [unrelabelNativeAssignments]

/-- Exact recovery of the ordered assignment list, including order and multiplicity. -/
theorem unrelabelNativeAssignments_relabelNativeAssignments (enumeration : V ≃ Fin n)
    (assignments : List (P93AuthorityLocatedAssignment policy.Descriptor))
    (bounded : ∀ assignment ∈ assignments, UnitBoundedIn n assignment.unit) :
    unrelabelNativeAssignments enumeration
        (relabelNativeAssignments enumeration assignments bounded) = assignments := by
  unfold unrelabelNativeAssignments relabelNativeAssignments
  rw [List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact unrelabelNativeAssignment_relabelNativeAssignment enumeration assignment.1
      (bounded assignment.1 assignment.2)
  · exact List.attach_map_subtype_val assignments

/-- Relabelling a decoded list returns it exactly. -/
theorem relabelNativeAssignments_unrelabelNativeAssignments (enumeration : V ≃ Fin n)
    (assignments : List (NativeLocatedAssignment policy V)) :
    relabelNativeAssignments enumeration (unrelabelNativeAssignments enumeration assignments)
        (unrelabelNativeAssignmentsBounded enumeration assignments) = assignments := by
  unfold relabelNativeAssignments unrelabelNativeAssignments
  rw [List.attach_map, List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact relabelNativeAssignment_unrelabelNativeAssignment enumeration assignment.1
  · exact List.attach_map_subtype_val assignments

/-! ## Native scoped assignments (mixed absolute/relative row) -/

/-- One located assignment together with its P-93.1.2 scope annotation. -/
structure NativeScopedAssignment (policy : P93GeneralAuthorityPolicy) (V : Type*) where
  located : NativeLocatedAssignment policy V
  scope : AssignmentScope

/-- Relabel the located part of a scoped assignment, retaining the scope. -/
def relabelNativeScopedAssignment (enumeration : V ≃ Fin n)
    (assignment : P93GeneralScopedAuthorityAssignment policy)
    (bounded : UnitBoundedIn n assignment.located.unit) :
    NativeScopedAssignment policy V where
  located := relabelNativeAssignment enumeration assignment.located bounded
  scope := assignment.scope

/-- Decode a scoped assignment. -/
def unrelabelNativeScopedAssignment (enumeration : V ≃ Fin n)
    (assignment : NativeScopedAssignment policy V) :
    P93GeneralScopedAuthorityAssignment policy where
  located := unrelabelNativeAssignment enumeration assignment.located
  scope := assignment.scope

/-- Exact recovery of one scoped assignment. -/
theorem unrelabelNativeScopedAssignment_relabelNativeScopedAssignment
    (enumeration : V ≃ Fin n)
    (assignment : P93GeneralScopedAuthorityAssignment policy)
    (bounded : UnitBoundedIn n assignment.located.unit) :
    unrelabelNativeScopedAssignment enumeration
        (relabelNativeScopedAssignment enumeration assignment bounded) = assignment := by
  rcases assignment with ⟨located, scope⟩
  rcases located with ⟨unit, citation, descriptor⟩
  simp [unrelabelNativeScopedAssignment, relabelNativeScopedAssignment,
    unrelabelNativeAssignment, relabelNativeAssignment, unrelabelUnit_relabelUnit]

/-- Relabelling a decoded scoped assignment returns it exactly. -/
theorem relabelNativeScopedAssignment_unrelabelNativeScopedAssignment
    (enumeration : V ≃ Fin n)
    (assignment : NativeScopedAssignment policy V) :
    relabelNativeScopedAssignment enumeration
        (unrelabelNativeScopedAssignment enumeration assignment)
        (unrelabelUnitBounded enumeration assignment.located.unit) = assignment := by
  rcases assignment with ⟨located, scope⟩
  rcases located with ⟨unit, citation, descriptor⟩
  simp [unrelabelNativeScopedAssignment, relabelNativeScopedAssignment,
    unrelabelNativeAssignment, relabelNativeAssignment, relabelUnit_unrelabelUnit]

/-- Relabel an ordered list of scoped assignments. -/
def relabelNativeScopedAssignments (enumeration : V ≃ Fin n)
    (assignments : List (P93GeneralScopedAuthorityAssignment policy))
    (bounded : ∀ assignment ∈ assignments, UnitBoundedIn n assignment.located.unit) :
    List (NativeScopedAssignment policy V) :=
  assignments.attach.map fun assignment =>
    relabelNativeScopedAssignment enumeration assignment.1
      (bounded assignment.1 assignment.2)

/-- Decode an ordered list of scoped assignments. -/
def unrelabelNativeScopedAssignments (enumeration : V ≃ Fin n)
    (assignments : List (NativeScopedAssignment policy V)) :
    List (P93GeneralScopedAuthorityAssignment policy) :=
  assignments.map (unrelabelNativeScopedAssignment enumeration)

/-- Every decoded scoped assignment satisfies the explicit representation bounds. -/
def unrelabelNativeScopedAssignmentsBounded (enumeration : V ≃ Fin n)
    (assignments : List (NativeScopedAssignment policy V)) :
    ∀ assignment ∈ unrelabelNativeScopedAssignments enumeration assignments,
      UnitBoundedIn n assignment.located.unit := by
  intro assignment member
  rw [unrelabelNativeScopedAssignments, List.mem_map] at member
  rcases member with ⟨native, _nativeMember, rfl⟩
  exact unrelabelUnitBounded enumeration native.located.unit

@[simp] theorem relabelNativeScopedAssignments_length (enumeration : V ≃ Fin n)
    (assignments : List (P93GeneralScopedAuthorityAssignment policy))
    (bounded : ∀ assignment ∈ assignments, UnitBoundedIn n assignment.located.unit) :
    (relabelNativeScopedAssignments enumeration assignments bounded).length =
      assignments.length := by
  simp [relabelNativeScopedAssignments]

@[simp] theorem unrelabelNativeScopedAssignments_length (enumeration : V ≃ Fin n)
    (assignments : List (NativeScopedAssignment policy V)) :
    (unrelabelNativeScopedAssignments enumeration assignments).length = assignments.length := by
  simp [unrelabelNativeScopedAssignments]

/-- Exact recovery of the ordered scoped-assignment list. -/
theorem unrelabelNativeScopedAssignments_relabelNativeScopedAssignments
    (enumeration : V ≃ Fin n)
    (assignments : List (P93GeneralScopedAuthorityAssignment policy))
    (bounded : ∀ assignment ∈ assignments, UnitBoundedIn n assignment.located.unit) :
    unrelabelNativeScopedAssignments enumeration
        (relabelNativeScopedAssignments enumeration assignments bounded) = assignments := by
  unfold unrelabelNativeScopedAssignments relabelNativeScopedAssignments
  rw [List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact unrelabelNativeScopedAssignment_relabelNativeScopedAssignment enumeration assignment.1
      (bounded assignment.1 assignment.2)
  · exact List.attach_map_subtype_val assignments

/-- Relabelling a decoded scoped-assignment list returns it exactly. -/
theorem relabelNativeScopedAssignments_unrelabelNativeScopedAssignments
    (enumeration : V ≃ Fin n)
    (assignments : List (NativeScopedAssignment policy V)) :
    relabelNativeScopedAssignments enumeration
        (unrelabelNativeScopedAssignments enumeration assignments)
        (unrelabelNativeScopedAssignmentsBounded enumeration assignments) = assignments := by
  unfold relabelNativeScopedAssignments unrelabelNativeScopedAssignments
  rw [List.attach_map, List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact relabelNativeScopedAssignment_unrelabelNativeScopedAssignment enumeration assignment.1
  · exact List.attach_map_subtype_val assignments

/-! ## The five tagged native observation -/

/-- The native counterpart of the five reviewed P-93.1 reference records.

Every raw physical unit has been relabelled into `V`; every citation, scope, typography,
rational fraction and composition class is copied literally. -/
inductive NativeGeneralObservation (policy : P93GeneralAuthorityPolicy) (V : Type*) where
  /-- P-93.1.1: one ordered absolute configuration. -/
  | absolute (configuration : List (NativeLocatedAssignment policy V))
  /-- P-93.1.2.1: two absolute representatives of one relative configuration. -/
  | relative (first second : List (NativeLocatedAssignment policy V))

  | mixedAbsoluteRelative
      (configuration : List (NativeLocatedAssignment policy V))
      (plan : List (NativeScopedAssignment policy V))
      (observedTypography :
        List (P93AuthorityCitationToken × DescriptorTypography))
  /-- P-93.1.3: two configurations and the exact printed rational mole fraction. -/
  | racemate (first second : List (NativeLocatedAssignment policy V)) (firstFraction : ℚ)
  /-- P-93.1.4: the exact inverted citation, the two configurations and the qualitative
  composition class.  No numerical fraction is introduced. -/
  | ambo (citation : P93AuthorityCitationToken)
      (first second : List (NativeLocatedAssignment policy V))
      (composition : BinaryCompositionClass)

/-! ## The five tagged source observation -/

/-- The five reviewed P-93.1 reference observations, tagged by row.  Each constructor stores the
actual upstream observation record; no field is abstracted away or copied into a raw payload. -/
inductive SourceGeneralObservation (policy : P93GeneralAuthorityPolicy) where
  /-- P-93.1.1 absolute configuration. -/
  | absolute (observation : P93AbsoluteConfigurationAuthorityObservation policy)
  /-- P-93.1.2.1 relative configuration. -/
  | relative (observation : P93RelativeConfigurationAuthorityObservation policy)
  /-- P-93.1.2.2 mixed absolute/relative scope. -/
  | mixedAbsoluteRelative (observation : P93MixedAbsoluteRelativeAuthorityObservation policy)
  /-- P-93.1.3 racemate. -/
  | racemate
      (observation : BinaryMixture
        (P93GeneralAuthorityConfiguration policy))
  /-- P-93.1.4 `ambo` mixture. -/
  | ambo (observation : P93AmboAuthorityObservation policy)

namespace SourceGeneralObservation

/-- The actual upstream `Judged` predicate, dispatched on the five-tag row. -/
def Judged (policy : P93GeneralAuthorityPolicy)
    (source : AuthoritativeChemicalInput) :
    SourceGeneralObservation policy → Prop
  | .absolute observation => P93AbsoluteConfigurationJudged policy source observation
  | .relative observation => P93RelativeConfigurationJudged policy source observation
  | .mixedAbsoluteRelative observation =>
      P93MixedAbsoluteRelativeJudged policy source observation
  | .racemate observation => P93RacemateJudged policy source observation
  | .ambo observation => P93AmboJudged policy source observation

/-- The reviewed row of each tag. -/
def row : SourceGeneralObservation policy → Remaining71P93GeneralAuthorityRow
  | .absolute _ => .absoluteConfiguration
  | .relative _ => .relativeConfiguration
  | .mixedAbsoluteRelative _ => .mixedAbsoluteRelativeConfiguration
  | .racemate _ => .racemates
  | .ambo _ => .ambo

/-- The normative provision of each tag. -/
def provision (observation : SourceGeneralObservation policy) :
    IUPACNormativeProvision :=
  observation.row.provision

/-- The explicit unit bounds needed to relabel a source observation into `V`.

The first configuration of every row is bounded by `InputFaithful`; the second configuration is
bounded through the structural relation recorded by the corresponding reviewed predicate. -/
def BoundedIn (n : ℕ) : SourceGeneralObservation policy → Prop
  | .absolute observation =>
      ∀ assignment ∈ observation.configuration.assignments, UnitBoundedIn n assignment.unit
  | .relative observation =>
      (∀ assignment ∈ observation.first.assignments, UnitBoundedIn n assignment.unit) ∧
      (∀ assignment ∈ observation.second.assignments, UnitBoundedIn n assignment.unit)
  | .mixedAbsoluteRelative observation =>
      (∀ assignment ∈ observation.configuration.assignments, UnitBoundedIn n assignment.unit) ∧
      (∀ assignment ∈ observation.plan.assignments,
        UnitBoundedIn n assignment.located.unit)
  | .racemate observation =>
      (∀ assignment ∈ observation.first.assignments, UnitBoundedIn n assignment.unit) ∧
      (∀ assignment ∈ observation.second.assignments, UnitBoundedIn n assignment.unit)
  | .ambo observation =>
      (∀ assignment ∈ observation.mixture.first.assignments,
        UnitBoundedIn n assignment.unit) ∧
      (∀ assignment ∈ observation.mixture.second.assignments,
        UnitBoundedIn n assignment.unit)

/-- The applicability predicate of the reviewed P-93.1 family, recovered from an actual judgment.
The five reviewed judgments all begin with source-faithful input to their first configuration;
the strengthened whole-configuration authorization conjuncts are later in each conjunction and
are therefore not needed to recover structural admissibility. -/
theorem applicable_of_judged (source : AuthoritativeChemicalInput)
    (observation : SourceGeneralObservation policy)
    (judged : observation.Judged policy source) :
    P93GeneralConfigurationApplicable policy source := by
  cases observation with
  | absolute observation => exact ⟨observation.configuration, judged.1⟩
  | relative observation => exact ⟨observation.first, judged.1⟩
  | mixedAbsoluteRelative observation => exact ⟨observation.configuration, judged.1⟩
  | racemate observation => exact ⟨observation.first, judged.1⟩
  | ambo observation => exact ⟨observation.mixture.first, judged.1⟩

end SourceGeneralObservation

/-! ## Decoding native observations -/

/-- Decode a native five-tag observation to the exact raw P-93.1 records.  Citations, scopes,
typography, fractions and composition classes are recovered literally. -/
def decodeGeneralObservation (policy : P93GeneralAuthorityPolicy) (enumeration : V ≃ Fin n) :
    NativeGeneralObservation policy V → SourceGeneralObservation policy
  | .absolute configuration =>
      .absolute
        { configuration :=
            { assignments := unrelabelNativeAssignments enumeration configuration } }
  | .relative first second =>
      .relative
        { first := { assignments := unrelabelNativeAssignments enumeration first }
          second := { assignments := unrelabelNativeAssignments enumeration second } }
  | .mixedAbsoluteRelative configuration plan observedTypography =>
      .mixedAbsoluteRelative
        { configuration :=
            { assignments := unrelabelNativeAssignments enumeration configuration }
          plan :=
            { assignments := unrelabelNativeScopedAssignments enumeration plan }
          observedTypography := observedTypography }
  | .racemate first second firstFraction =>
      .racemate
        { first := { assignments := unrelabelNativeAssignments enumeration first }
          second := { assignments := unrelabelNativeAssignments enumeration second }
          firstFraction := firstFraction }
  | .ambo citation first second composition =>
      .ambo
        { citation := citation
          mixture :=
            { first := { assignments := unrelabelNativeAssignments enumeration first }
              second := { assignments := unrelabelNativeAssignments enumeration second }
              composition := composition } }

/-- The representation bounds of a decoded native observation are exactly the
`unrelabelUnitBounded` facts; no source validity is assumed. -/
def decodeGeneralObservationBounded (policy : P93GeneralAuthorityPolicy)
    (enumeration : V ≃ Fin n) :
    (observation : NativeGeneralObservation policy V) →
      (decodeGeneralObservation policy enumeration observation).BoundedIn n
  | .absolute configuration =>
      unrelabelNativeAssignmentsBounded enumeration configuration
  | .relative first second =>
      ⟨unrelabelNativeAssignmentsBounded enumeration first,
        unrelabelNativeAssignmentsBounded enumeration second⟩
  | .mixedAbsoluteRelative configuration plan _observedTypography =>
      ⟨unrelabelNativeAssignmentsBounded enumeration configuration,
        unrelabelNativeScopedAssignmentsBounded enumeration plan⟩
  | .racemate first second _firstFraction =>
      ⟨unrelabelNativeAssignmentsBounded enumeration first,
        unrelabelNativeAssignmentsBounded enumeration second⟩
  | .ambo _citation first second _composition =>
      ⟨unrelabelNativeAssignmentsBounded enumeration first,
        unrelabelNativeAssignmentsBounded enumeration second⟩

/-! ## Encoding source observations -/

/-- Encode a raw five-tag observation into `V`, given the explicit representation bounds. -/
def encodeGeneralObservation (policy : P93GeneralAuthorityPolicy) (enumeration : V ≃ Fin n) :
    (observation : SourceGeneralObservation policy) →
      observation.BoundedIn n → NativeGeneralObservation policy V
  | .absolute observation, bounded =>
      .absolute
        (relabelNativeAssignments enumeration observation.configuration.assignments bounded)
  | .relative observation, bounded =>
      .relative
        (relabelNativeAssignments enumeration observation.first.assignments bounded.1)
        (relabelNativeAssignments enumeration observation.second.assignments bounded.2)
  | .mixedAbsoluteRelative observation, bounded =>
      .mixedAbsoluteRelative
        (relabelNativeAssignments enumeration observation.configuration.assignments bounded.1)
        (relabelNativeScopedAssignments enumeration observation.plan.assignments bounded.2)
        observation.observedTypography
  | .racemate observation, bounded =>
      .racemate
        (relabelNativeAssignments enumeration observation.first.assignments bounded.1)
        (relabelNativeAssignments enumeration observation.second.assignments bounded.2)
        observation.firstFraction
  | .ambo observation, bounded =>
      .ambo observation.citation
        (relabelNativeAssignments enumeration observation.mixture.first.assignments bounded.1)
        (relabelNativeAssignments enumeration observation.mixture.second.assignments bounded.2)
        observation.mixture.composition

/-- **Every branch inverse, native side.**  Decoding then encoding a native observation returns
the exact native record, including ordered lists, duplicates, scopes, typography, the racemate
fraction and the `ambo` composition class. -/
theorem encodeGeneralObservation_decodeGeneralObservation
    (policy : P93GeneralAuthorityPolicy) (enumeration : V ≃ Fin n)
    (observation : NativeGeneralObservation policy V) :
    encodeGeneralObservation policy enumeration
        (decodeGeneralObservation policy enumeration observation)
        (decodeGeneralObservationBounded policy enumeration observation) = observation := by
  cases observation with
  | absolute configuration =>
      simp only [decodeGeneralObservation, encodeGeneralObservation,
        decodeGeneralObservationBounded,
        relabelNativeAssignments_unrelabelNativeAssignments]
  | relative first second =>
      simp only [decodeGeneralObservation, encodeGeneralObservation,
        decodeGeneralObservationBounded,
        relabelNativeAssignments_unrelabelNativeAssignments]
  | mixedAbsoluteRelative configuration plan observedTypography =>
      simp only [decodeGeneralObservation, encodeGeneralObservation,
        decodeGeneralObservationBounded,
        relabelNativeAssignments_unrelabelNativeAssignments,
        relabelNativeScopedAssignments_unrelabelNativeScopedAssignments]
  | racemate first second firstFraction =>
      simp only [decodeGeneralObservation, encodeGeneralObservation,
        decodeGeneralObservationBounded,
        relabelNativeAssignments_unrelabelNativeAssignments]
  | ambo citation first second composition =>
      simp only [decodeGeneralObservation, encodeGeneralObservation,
        decodeGeneralObservationBounded,
        relabelNativeAssignments_unrelabelNativeAssignments]





theorem decodeGeneralObservation_encodeGeneralObservation
    (policy : P93GeneralAuthorityPolicy) (enumeration : V ≃ Fin n)
    (observation : SourceGeneralObservation policy)
    (bounded : observation.BoundedIn n) :
    decodeGeneralObservation policy enumeration
        (encodeGeneralObservation policy enumeration observation bounded) = observation := by
  cases observation with
  | absolute observation =>
      cases observation with
      | mk configuration =>
          simp only [decodeGeneralObservation, encodeGeneralObservation,
            unrelabelNativeAssignments_relabelNativeAssignments]
  | relative observation =>
      cases observation with
      | mk first second =>
          simp only [decodeGeneralObservation, encodeGeneralObservation,
            unrelabelNativeAssignments_relabelNativeAssignments]
  | mixedAbsoluteRelative observation =>
      cases observation with
      | mk configuration plan observedTypography =>
          cases plan with
          | mk assignments =>
              simp only [decodeGeneralObservation, encodeGeneralObservation,
                unrelabelNativeAssignments_relabelNativeAssignments,
                unrelabelNativeScopedAssignments_relabelNativeScopedAssignments]
  | racemate observation =>
      cases observation with
      | mk first second firstFraction =>
          simp only [decodeGeneralObservation, encodeGeneralObservation,
            unrelabelNativeAssignments_relabelNativeAssignments]
  | ambo observation =>
      cases observation with
      | mk citation mixture =>
          cases mixture with
          | mk first second composition =>
              simp only [decodeGeneralObservation, encodeGeneralObservation,
                unrelabelNativeAssignments_relabelNativeAssignments]

/-- The observation codec is injective on the source side: the exact left inverse forces equal
raw observations.  This is the list/order-level injectivity of the five-tag encoding. -/
theorem encodeGeneralObservation_injective
    (policy : P93GeneralAuthorityPolicy) (enumeration : V ≃ Fin n)
    (first second : SourceGeneralObservation policy)
    (firstBounded : first.BoundedIn n) (secondBounded : second.BoundedIn n)
    (equal : encodeGeneralObservation policy enumeration first firstBounded =
      encodeGeneralObservation policy enumeration second secondBounded) :
    first = second := by
  rw [← decodeGeneralObservation_encodeGeneralObservation policy enumeration first firstBounded,
    equal, decodeGeneralObservation_encodeGeneralObservation policy enumeration second secondBounded]

/-- The observation codec is injective on the native side: the exact right inverse forces equal
native observations, including order, duplicates, scopes and optional typography. -/
theorem decodeGeneralObservation_injective
    (policy : P93GeneralAuthorityPolicy) (enumeration : V ≃ Fin n)
    (first second : NativeGeneralObservation policy V)
    (equal : decodeGeneralObservation policy enumeration first =
      decodeGeneralObservation policy enumeration second) :
    first = second := by
  rw [← encodeGeneralObservation_decodeGeneralObservation policy enumeration first]
  simp only [equal]
  exact encodeGeneralObservation_decodeGeneralObservation policy enumeration second

/-! ## Bounds from the reviewed predicates -/

/-- All unit bounds of a source-faithful configuration, derived from the actual
`P93AuthorityPhysicalUnit.ValidFor` facts in `InputFaithful`.  The polyhedral case uses the
certified spatial-length fact through `OrganicStereoP93AcyclicIngress`. -/
theorem assignments_bounded_of_inputFaithful
    (source : AuthoritativeChemicalInput)
    (policy : P93GeneralAuthorityPolicy)
    (configuration : P93GeneralAuthorityConfiguration policy)
    (faithful : P93GeneralConfigurationInputFaithful policy source configuration)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    ∀ assignment ∈ configuration.assignments,
      UnitBoundedIn source.molecule.atomCount assignment.unit := by
  intro assignment member
  exact OrganicStereoP93AcyclicIngress.physicalUnitBoundedIn_of_validFor
    source policy.physicalObservation assignment.unit
    ((faithful.1.2.2.2 assignment member).1) spatialWellFormed

/-- Global mirroring changes only descriptors: the ordered unit list is untouched. -/
theorem globallyMirrored_unitList {Descriptor : Type*}
    (action : P93AuthorityConfiguration.MirrorAction Descriptor)
    (configuration : P93AuthorityConfiguration Descriptor) :
    ((configuration.globallyMirrored action).assignments.map
        fun assignment => assignment.unit) =
      configuration.assignments.map fun assignment => assignment.unit := by
  simp [P93AuthorityConfiguration.globallyMirrored, List.map_map, Function.comp_def]

/-- Global mirroring changes only descriptors: the ordered citation list is untouched. -/
theorem globallyMirrored_citationList {Descriptor : Type*}
    (action : P93AuthorityConfiguration.MirrorAction Descriptor)
    (configuration : P93AuthorityConfiguration Descriptor) :
    ((configuration.globallyMirrored action).assignments.map
        fun assignment => assignment.citation) =
      configuration.assignments.map fun assignment => assignment.citation := by
  simp [P93AuthorityConfiguration.globallyMirrored, List.map_map, Function.comp_def]

/-- Global mirroring sends the descriptor list to the pointwise mirror action. -/
theorem globallyMirrored_descriptorList {Descriptor : Type*}
    (action : P93AuthorityConfiguration.MirrorAction Descriptor)
    (configuration : P93AuthorityConfiguration Descriptor) :
    ((configuration.globallyMirrored action).assignments.map
        fun assignment => assignment.descriptor) =
      configuration.assignments.map fun assignment => action.mirror assignment.descriptor := by
  simp [P93AuthorityConfiguration.globallyMirrored, List.map_map, Function.comp_def]

/-- Unit bounds survive global mirroring. -/
theorem boundedIn_globallyMirrored {Descriptor : Type*}
    (action : P93AuthorityConfiguration.MirrorAction Descriptor)
    (configuration : P93AuthorityConfiguration Descriptor)
    (bounded : ∀ assignment ∈ configuration.assignments,
      UnitBoundedIn n assignment.unit) :
    ∀ assignment ∈ (configuration.globallyMirrored action).assignments,
      UnitBoundedIn n assignment.unit := by
  intro assignment member
  simp only [P93AuthorityConfiguration.globallyMirrored, List.mem_map] at member
  rcases member with ⟨source, sourceMember, rfl⟩
  exact bounded source sourceMember

/-- The second representative of a relative configuration is either the first or its global
mirror, so it inherits the same unit bounds. -/
theorem boundedIn_relativeSecond
    (action : P93AuthorityConfiguration.MirrorAction policy.Descriptor)
    (first second : P93GeneralAuthorityConfiguration policy)
    (relative : P93AuthorityConfiguration.RelativeEquivalent action first second)
    (bounded : ∀ assignment ∈ first.assignments, UnitBoundedIn n assignment.unit) :
    ∀ assignment ∈ second.assignments, UnitBoundedIn n assignment.unit := by
  rcases relative with same | mirrored
  · rw [same]
    exact bounded
  · rw [mirrored]
    exact boundedIn_globallyMirrored action first bounded

/-! ### The `ambo` inversion preserves units

The upstream inversion helper is private, so this module supplies its own definitionally
identical copy.  The copy expresses exactly the same `if`, and `rfl` identifies each mapped
assignment with the upstream one: both sides unfold to the *same* stuck conditional.  The unit
projection of the copy is then proved by cases on the citation. -/

/-- Local, definitionally identical copy of the upstream `ambo` inversion-at-one-citation map. -/
private def nativeInvertAssignmentAtCitation
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (assignment : P93AuthorityLocatedAssignment policy.Descriptor) :
    P93AuthorityLocatedAssignment policy.Descriptor :=
  if assignment.citation = target then
    { assignment with
      descriptor := policy.localAction.mirror assignment.descriptor }
  else assignment

/-- The public upstream inversion is the ordered map of the local copy.  Proved pointwise, so
the head definitions match before the conditional is ever evaluated. -/
theorem p93GeneralConfigurationInvertedAtCitation_assignments
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (configuration : P93GeneralAuthorityConfiguration policy) :
    (p93GeneralConfigurationInvertedAtCitation policy target configuration).assignments =
      configuration.assignments.map (nativeInvertAssignmentAtCitation policy target) := by
  simp only [p93GeneralConfigurationInvertedAtCitation]
  apply List.map_congr_left
  intro assignment _
  rfl

/-- The local `ambo` inversion retains the physical unit of every assignment. -/
theorem nativeInvertAssignmentAtCitation_unit
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (assignment : P93AuthorityLocatedAssignment policy.Descriptor) :
    (nativeInvertAssignmentAtCitation policy target assignment).unit = assignment.unit := by
  unfold nativeInvertAssignmentAtCitation
  by_cases changed : assignment.citation = target <;> simp [changed]

/-- Inverting the descriptor at one citation preserves all physical unit bounds.  Only the
descriptor may change; the unit and citation are never renumbered. -/
theorem boundedIn_invertedAtCitation
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (configuration : P93GeneralAuthorityConfiguration policy)
    (bounded : ∀ assignment ∈ configuration.assignments,
      UnitBoundedIn n assignment.unit) :
    ∀ assignment ∈
      (p93GeneralConfigurationInvertedAtCitation policy target configuration).assignments,
      UnitBoundedIn n assignment.unit := by
  intro assignment member
  rw [p93GeneralConfigurationInvertedAtCitation_assignments, List.mem_map] at member
  rcases member with ⟨source, sourceMember, rfl⟩
  rw [nativeInvertAssignmentAtCitation_unit]
  exact bounded source sourceMember















theorem SourceGeneralObservation.boundedIn_of_judged
    (policy : P93GeneralAuthorityPolicy)
    (certified : CertifiedAuthoritativeChemicalInput)
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph_eq : certified.input.molecule = graph.encode enumeration)
    (observation : SourceGeneralObservation policy)
    (judged : observation.Judged policy certified.input) :
    observation.BoundedIn (Fintype.card V) := by
  have spatialWellFormed : certified.input.SpatialIndicesWellFormed :=
    certified.structurallyWellFormed.2.1
  have countEq : certified.input.molecule.atomCount = Fintype.card V :=
    atomCount_eq_of_graph_eq graph enumeration certified graph_eq
  cases observation with
  | absolute observation =>
      obtain ⟨faithful, _authorized⟩ := judged
      simpa only [countEq] using
        assignments_bounded_of_inputFaithful certified.input policy observation.configuration
          faithful spatialWellFormed
  | relative observation =>
      obtain ⟨faithful, _canonical, relative, _authFirst, _authSecond⟩ := judged
      have firstBounded :=
        assignments_bounded_of_inputFaithful certified.input policy observation.first
          faithful spatialWellFormed
      have secondBounded :=
        boundedIn_relativeSecond policy.mirrorAction observation.first observation.second
          relative firstBounded
      exact ⟨by simpa only [countEq] using firstBounded,
        by simpa only [countEq] using secondBounded⟩
  | mixedAbsoluteRelative observation =>
      obtain ⟨faithful, planEq, _mixed, _nontrivial, _typography, _authorized⟩ := judged
      have configurationBounded :=
        assignments_bounded_of_inputFaithful certified.input policy observation.configuration
          faithful spatialWellFormed
      refine ⟨by simpa only [countEq] using configurationBounded, ?_⟩
      intro assignment member
      have locatedMember : assignment.located ∈ observation.configuration.assignments := by
        have mapped :
            assignment.located ∈
              observation.plan.assignments.map (fun assignment => assignment.located) :=
          List.mem_map.mpr ⟨assignment, member, rfl⟩
        rwa [planEq] at mapped
      exact by
        simpa only [countEq] using configurationBounded assignment.located locatedMember
  | racemate observation =>
      obtain ⟨faithful, _canonical, racemate, _authFirst, _authSecond⟩ := judged
      have firstBounded :=
        assignments_bounded_of_inputFaithful certified.input policy observation.first
          faithful spatialWellFormed
      have secondBounded :
          ∀ assignment ∈ observation.second.assignments,
            UnitBoundedIn certified.input.molecule.atomCount assignment.unit := by
        rw [racemate.2.1]
        exact boundedIn_globallyMirrored policy.mirrorAction observation.first firstBounded
      exact ⟨by simpa only [countEq] using firstBounded,
        by simpa only [countEq] using secondBounded⟩
  | ambo observation =>
      obtain ⟨faithful, ambo, _authFirst, _authSecond⟩ := judged
      have firstBounded :=
        assignments_bounded_of_inputFaithful certified.input policy observation.mixture.first
          faithful spatialWellFormed
      have secondBounded :
          ∀ assignment ∈ observation.mixture.second.assignments,
            UnitBoundedIn certified.input.molecule.atomCount assignment.unit := by
        rw [ambo.2.2.1]
        exact boundedIn_invertedAtCitation policy observation.citation
          observation.mixture.first firstBounded
      exact ⟨by simpa only [countEq] using firstBounded,
        by simpa only [countEq] using secondBounded⟩

/-! ## The native authority packet and its exact codec -/

/-- The native P-93.1 packet.  It stores exactly:

* the source-free `NativeSourceContext` (shared graph plus native optional channels);
* the five-tag native observation; and
* an actual `Judged` proof for the *decoded* observation at the reconstructed source.

No whole certified source, raw observation, or encoding inverse hypothesis is stored. -/
structure NativeGeneralAuthorityPacket (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (policy : P93GeneralAuthorityPolicy) where
  /-- The source-free native context: coordinates and drawing channel only. -/
  context : NativeSourceContext graph enumeration
  /-- The native five-tag observation with all physical units relabelled into `V`. -/
  observation : NativeGeneralObservation policy V
  /-- The reviewed judgment of the decoded observation at the reconstructed original source. -/
  judged : (decodeGeneralObservation policy enumeration observation).Judged policy
    (decodeSourceContext graph enumeration context).input

/-- The source reconstructed by a native packet. -/
def NativeGeneralAuthorityPacket.source
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (packet : NativeGeneralAuthorityPacket graph enumeration policy) :
    CertifiedAuthoritativeChemicalInput :=
  decodeSourceContext graph enumeration packet.context

/-- The raw observation decoded from a native packet. -/
def NativeGeneralAuthorityPacket.toObservation
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (packet : NativeGeneralAuthorityPacket graph enumeration policy) :
    SourceGeneralObservation policy :=
  decodeGeneralObservation policy enumeration packet.observation

/-- The packet's judgment is an actual judgment of its decoded observation at its own
reconstructed source. -/
theorem NativeGeneralAuthorityPacket.judgedForSource
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (packet : NativeGeneralAuthorityPacket graph enumeration policy) :
    (packet.toObservation graph enumeration).Judged policy
      (packet.source graph enumeration).input :=
  packet.judged

/-- A recovered source, observation and judgment triple. -/
structure RecoveredGeneralAuthority (policy : P93GeneralAuthorityPolicy) where
  source : CertifiedAuthoritativeChemicalInput
  observation : SourceGeneralObservation policy
  judged : observation.Judged policy source.input

/-- **Decode** a native packet: reconstruct the certified source from the shared graph and the
native channels, decode the five-tag observation, and return the stored actual judgment. -/
def decodeGeneralAuthority (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (packet : NativeGeneralAuthorityPacket graph enumeration policy) :
    RecoveredGeneralAuthority policy where
  source := packet.source graph enumeration
  observation := packet.toObservation graph enumeration
  judged := packet.judged

/-- **Encode** an actual raw source, graph tie, five-tag observation and judgment into a native
packet.  The certified source is replaced by the native context; unit bounds are derived from the
reviewed predicates; the stored judgment is the actual judgment of the decoded observation at the
reconstructed source. -/
def encodeGeneralAuthority (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (certified : CertifiedAuthoritativeChemicalInput)
    (graph_eq : certified.input.molecule = graph.encode enumeration)
    (observation : SourceGeneralObservation policy)
    (judged : observation.Judged policy certified.input) :
    NativeGeneralAuthorityPacket graph enumeration policy :=
  let bounds := SourceGeneralObservation.boundedIn_of_judged policy certified graph enumeration
    graph_eq observation judged
  { context := encodeSourceContext graph enumeration certified graph_eq
    observation := encodeGeneralObservation policy enumeration observation bounds
    judged := by
      rw [decode_encodeSourceContext graph enumeration certified graph_eq]
      rw [decodeGeneralObservation_encodeGeneralObservation policy enumeration observation bounds]
      exact judged }

/-- **Exact inverse.**  Encoding an actual source/observation/judgment and then decoding returns
the exact certified source (including `none`/`some` for both optional channels) and the exact raw
five-tag observation (including ordered lists, duplicates, typography, rational and composition
data).

The source half is the `NativeSourceContext` inverse `decode_encodeSourceContext`; the observation
half is the per-branch representation inverse above.  No validity is transported across a
renumbering. -/
theorem decodeGeneralAuthority_encodeGeneralAuthority
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (certified : CertifiedAuthoritativeChemicalInput)
    (graph_eq : certified.input.molecule = graph.encode enumeration)
    (observation : SourceGeneralObservation policy)
    (judged : observation.Judged policy certified.input) :
    let decoded := decodeGeneralAuthority graph enumeration
      (encodeGeneralAuthority graph enumeration certified graph_eq observation judged)
    decoded.source = certified ∧ decoded.observation = observation := by
  constructor
  · exact decode_encodeSourceContext graph enumeration certified graph_eq
  · exact decodeGeneralObservation_encodeGeneralObservation policy enumeration observation
      (SourceGeneralObservation.boundedIn_of_judged policy certified graph enumeration graph_eq
        observation judged)

/-- The recovered source component of the exact inverse. -/
theorem decodeGeneralAuthority_encodeGeneralAuthority_source
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (certified : CertifiedAuthoritativeChemicalInput)
    (graph_eq : certified.input.molecule = graph.encode enumeration)
    (observation : SourceGeneralObservation policy)
    (judged : observation.Judged policy certified.input) :
    (decodeGeneralAuthority graph enumeration
      (encodeGeneralAuthority graph enumeration certified graph_eq observation judged)).source =
        certified :=
  (decodeGeneralAuthority_encodeGeneralAuthority graph enumeration certified graph_eq
    observation judged).1

/-- The recovered observation component of the exact inverse. -/
theorem decodeGeneralAuthority_encodeGeneralAuthority_observation
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (certified : CertifiedAuthoritativeChemicalInput)
    (graph_eq : certified.input.molecule = graph.encode enumeration)
    (observation : SourceGeneralObservation policy)
    (judged : observation.Judged policy certified.input) :
    (decodeGeneralAuthority graph enumeration
      (encodeGeneralAuthority graph enumeration certified graph_eq observation judged)).observation =
        observation :=
  (decodeGeneralAuthority_encodeGeneralAuthority graph enumeration certified graph_eq
    observation judged).2

/-- The exact inverse preserves a `none` spatial channel as `none` and a present channel as the
same present channel. -/
@[simp] theorem decodeGeneralAuthority_encodeGeneralAuthority_spatial?
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (certified : CertifiedAuthoritativeChemicalInput)
    (graph_eq : certified.input.molecule = graph.encode enumeration)
    (observation : SourceGeneralObservation policy)
    (judged : observation.Judged policy certified.input) :
    ((decodeGeneralAuthority graph enumeration
      (encodeGeneralAuthority graph enumeration certified graph_eq observation judged)).source.input.spatial?) =
        certified.input.spatial? := by
  rw [decodeGeneralAuthority_encodeGeneralAuthority_source]

/-- The exact inverse preserves a `none` drawing channel as `none` and a present channel as the
same present channel, including its ordered bond and parity lists. -/
@[simp] theorem decodeGeneralAuthority_encodeGeneralAuthority_diagram?
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (certified : CertifiedAuthoritativeChemicalInput)
    (graph_eq : certified.input.molecule = graph.encode enumeration)
    (observation : SourceGeneralObservation policy)
    (judged : observation.Judged policy certified.input) :
    ((decodeGeneralAuthority graph enumeration
      (encodeGeneralAuthority graph enumeration certified graph_eq observation judged)).source.input.diagram?) =
        certified.input.diagram? := by
  rw [decodeGeneralAuthority_encodeGeneralAuthority_source]

/-- The decoded packet is judged at the decoded source. -/
theorem decodeGeneralAuthority_judged
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (packet : NativeGeneralAuthorityPacket graph enumeration policy) :
    (decodeGeneralAuthority graph enumeration packet).observation.Judged policy
      (decodeGeneralAuthority graph enumeration packet).source.input :=
  (decodeGeneralAuthority graph enumeration packet).judged

/-- The decoded packet is applicable at the decoded source. -/
theorem decodeGeneralAuthority_applicable
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (packet : NativeGeneralAuthorityPacket graph enumeration policy) :
    P93GeneralConfigurationApplicable policy
      (decodeGeneralAuthority graph enumeration packet).source.input :=
  SourceGeneralObservation.applicable_of_judged _
    (decodeGeneralAuthority graph enumeration packet).observation
    (decodeGeneralAuthority_judged graph enumeration packet)

/-! ## Nonvacuous fixtures

A small concrete molecule, a concrete general policy, and actual `Judged` witnesses for all five
rows.  These fixtures use only the imported modules and are not part of any completeness claim.

The fixture policy's `ConfigurationAuthorized` field is **not** `True` and is **not** a pointwise
union over assignments: it is membership of the *complete* ordered configuration in an explicit
three-element class of whole fixture configurations.  Every entry is a whole
`P93AuthorityConfiguration`, and nonvacuity plus strictness of the class are proved below. -/

namespace Fixture

/-- A carbon atom with the default non-isotopic, neutral semantic decoration. -/
def carbon : SemanticAtom :=
  { element := ⟨6, by decide, by decide⟩ }

/-- Six carbon atoms. -/
def molecule : SemanticMolecule :=
  { atoms := [carbon, carbon, carbon, carbon, carbon, carbon]
    interactions :=
      [ { participants := [1, 2], kind := .covalent 1 }
      , { participants := [2, 3], kind := .covalent 1 }
      , { participants := [4, 5], kind := .covalent 1 }
      ] }

/-- The fixture authoritative input. -/
def source : AuthoritativeChemicalInput :=
  { molecule := molecule }

/-- The fixture input is structurally well formed. -/
theorem source_structurallyWellFormed : source.StructurallyWellFormed := by
  refine ⟨?_, trivial, trivial⟩
  simp [source, molecule, SemanticMolecule.StructurallyWellFormed,
    SemanticMolecule.atomCount, SemanticInteraction.wellFormed?]

/-- The certified fixture source. -/
def certified : CertifiedAuthoritativeChemicalInput :=
  { input := source, structurallyWellFormed := source_structurallyWellFormed }

/-- The fixture descriptor type. -/
abbrev Descriptor := BlueBookP93.GeneralConfiguration.Descriptor

/-- One citation token `1`. -/
def citationOne : P93AuthorityCitationToken :=
  { components := [{ value := 1 }] }

/-- One citation token `2`. -/
def citationTwo : P93AuthorityCitationToken :=
  { components := [{ value := 2 }] }

/-- One citation token `3`. -/
def citationThree : P93AuthorityCitationToken :=
  { components := [{ value := 3 }] }

/-- The binary bond unit `1-2`. -/
def bondOneTwo : P93AuthorityPhysicalUnit := .bond 1 2

/-- The binary bond unit `2-3`. -/
def bondTwoThree : P93AuthorityPhysicalUnit := .bond 2 3

/-- The binary bond unit `4-5`. -/
def bondFourFive : P93AuthorityPhysicalUnit := .bond 4 5

/-- Assignment `1-2 : R`. -/
def assignmentOne : P93AuthorityLocatedAssignment Descriptor :=
  { unit := bondOneTwo, citation := citationOne, descriptor := .capitalR }

/-- Assignment `2-3 : S`. -/
def assignmentTwo : P93AuthorityLocatedAssignment Descriptor :=
  { unit := bondTwoThree, citation := citationTwo, descriptor := .capitalS }

/-- Assignment `4-5 : R`. -/
def assignmentThree : P93AuthorityLocatedAssignment Descriptor :=
  { unit := bondFourFive, citation := citationThree, descriptor := .capitalR }

/-- The fixture global molecular mirror action.  It is defined before the policy so that the
whole-configuration authorization class can name complete configurations without a cycle.

The action is the repaired `Descriptor.enantiomer`: it exchanges `R`/`S` (and `Ra`/`Sa`,
`M`/`P`) but fixes the pseudoasymmetric/relative `r`/`s` descriptors.  The local `ambo` action is
the distinct `Descriptor.invert`, which swaps every pair including `r ↔ s`. -/
abbrev fixtureMirrorAction : P93AuthorityConfiguration.MirrorAction Descriptor where
  mirror := BlueBookP93.GeneralConfiguration.Descriptor.enantiomer
  involutive := BlueBookP93.GeneralConfiguration.Descriptor.enantiomer_involutive

/-- Local inversion exchanges the two ligands at the stated unit, including lowercase r/s. -/
abbrev fixtureLocalAction : P93AuthorityConfiguration.MirrorAction Descriptor where
  mirror := BlueBookP93.GeneralConfiguration.Descriptor.invert
  involutive := BlueBookP93.GeneralConfiguration.Descriptor.invert_involutive

/-- The fixture global mirror fixes lower-case `r`.  This is a direct regression check that the
whole-molecule action is not the local epimer action. -/
@[simp] theorem fixtureMirrorAction_lowercaseR :
    fixtureMirrorAction.mirror Descriptor.lowercaseR = Descriptor.lowercaseR := rfl

/-- The fixture global mirror fixes lower-case `s`. -/
@[simp] theorem fixtureMirrorAction_lowercaseS :
    fixtureMirrorAction.mirror Descriptor.lowercaseS = Descriptor.lowercaseS := rfl

/-- The fixture global mirror exchanges the capital `R`/`S` pair used by the fixture. -/
@[simp] theorem fixtureMirrorAction_capitalR :
    fixtureMirrorAction.mirror Descriptor.capitalR = Descriptor.capitalS := rfl

/-- The fixture global mirror exchanges the capital `S`/`R` pair used by the fixture. -/
@[simp] theorem fixtureMirrorAction_capitalS :
    fixtureMirrorAction.mirror Descriptor.capitalS = Descriptor.capitalR := rfl

/-- The local epimer operation on the fixture descriptor type exchanges `r` and `s`. -/
@[simp] theorem fixtureLocalInversion_lowercaseR :
    Descriptor.lowercaseR.invert = Descriptor.lowercaseS := rfl

/-- The local epimer operation on the fixture descriptor type exchanges `s` and `r`. -/
@[simp] theorem fixtureLocalInversion_lowercaseS :
    Descriptor.lowercaseS.invert = Descriptor.lowercaseR := rfl

/-- The local epimer operation is involutive. -/
theorem fixtureLocalInversion_involutive (descriptor : Descriptor) :
    descriptor.invert.invert = descriptor :=
  BlueBookP93.GeneralConfiguration.Descriptor.invert_involutive descriptor

/-- On the capital descriptors used by this fixture, the local epimer action and the global
mirror agree; this is why the fixture's capital-only `ambo` construction is unchanged by the
split. -/
theorem fixtureLocalInversion_eq_mirror_of_capital (descriptor : Descriptor)
    (capital : descriptor = .capitalR ∨ descriptor = .capitalS) :
    descriptor.invert = fixtureMirrorAction.mirror descriptor := by
  rcases capital with rfl | rfl <;> rfl

/-- The ordered fixture assignment list shared by every whole fixture configuration. -/
abbrev fixtureAssignments : List (P93AuthorityLocatedAssignment Descriptor) :=
  [assignmentOne, assignmentTwo, assignmentThree]

/-- The base whole fixture configuration. -/
abbrev fixtureBaseConfiguration : P93AuthorityConfiguration Descriptor :=
  { assignments := fixtureAssignments }

/-- The whole fixture configuration obtained by the certified global mirror. -/
abbrev fixtureMirroredConfiguration : P93AuthorityConfiguration Descriptor :=
  P93AuthorityConfiguration.globallyMirrored fixtureMirrorAction fixtureBaseConfiguration

/-- The whole fixture configuration obtained by inverting exactly the descriptor named by
citation `1`.  This is definitionally the upstream `ambo` inversion at the same citation. -/
abbrev fixtureInvertedConfiguration : P93AuthorityConfiguration Descriptor :=
  { assignments := fixtureAssignments.map fun assignment =>
      if assignment.citation = citationOne then
        { assignment with
          descriptor := fixtureLocalAction.mirror assignment.descriptor }
      else assignment }

/-- The explicit finite class of **whole** fixture configurations authorized by the fixture
policy.  Each element is a complete `P93AuthorityConfiguration`; there is no per-assignment
predicate and no `True` fallback. -/
def fixtureAuthorizedConfigurations : List (P93AuthorityConfiguration Descriptor) :=
  [ fixtureBaseConfiguration
  , fixtureMirroredConfiguration
  , fixtureInvertedConfiguration
  ]

/-- Fixture whole-configuration authorization, bound to the exact fixture molecule: the *entire*
configuration must be one of the three explicit whole configurations above.  A production
compiler must construct genuine source-bound authorization; this fixture class is only for the
concrete fixture below. -/
def fixtureConfigurationAuthorized
    (source : AuthoritativeChemicalInput)
    (configuration : P93AuthorityConfiguration Descriptor) : Prop :=
  source.molecule = molecule ∧ configuration ∈ fixtureAuthorizedConfigurations

/-- A concrete general P-93.1 policy over the eight P-93 configuration descriptors.  The physical
observation boundary is permissive because all fixture units are binary bonds, for which
`ValidFor` never consults the policy.

`ConfigurationAuthorized` is the explicit whole-configuration class defined above; it is not
`True` and not a pointwise union over assignments.

`RepresentativeEligible` is the closed P-93 representative language: it excludes the fixed
pseudoasymmetric `r`/`s` descriptors, exactly as the canonical `P93CanonicalDescriptor` policy
does.  `mirrorPreferredAtLowest` is therefore the eligibility-conditioned polarity flip, not the
former universal (and false) statement. -/
abbrev fixturePolicy : P93GeneralAuthorityPolicy where
  Descriptor := BlueBookP93.GeneralConfiguration.Descriptor
  mirrorAction := fixtureMirrorAction
  localAction := fixtureLocalAction
  RepresentativeEligible :=
    BlueBookP93.GeneralConfiguration.Descriptor.RepresentativeEligible
  representativeEligible_mirror_iff :=
    BlueBookP93.GeneralConfiguration.Descriptor.enantiomer_representativeEligible_iff
  PreferredAtLowest := BlueBookP93.GeneralConfiguration.Descriptor.PreferredAtLowest
  mirrorPreferredAtLowest := by
    intro descriptor eligible _mirrorNe
    exact BlueBookP93.GeneralConfiguration.Descriptor.enantiomer_preferredAtLowest_iff_of_eligible
      descriptor eligible
  physicalObservation :=
    { HelixIdentified := fun _ _ _ => True
      PlanarRestrictionAndAsymmetryObserved := fun _ _ _ => True
      PolyhedralQualitativeFrameObserved := fun _ _ _ _ _ => True }
  CitationAuthorized := fun _ _ _ => True
  DescriptorAuthorized := fun _ _ _ => True
  descriptorAuthorized_mirror_iff := by intro source unit descriptor; simp
  ConfigurationAuthorized := fixtureConfigurationAuthorized

theorem bondOneTwo_valid :
    bondOneTwo.ValidFor fixturePolicy.physicalObservation source := by
  simp only [bondOneTwo, P93AuthorityPhysicalUnit.ValidFor]
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  exact ⟨{ participants := [1, 2], kind := .covalent 1 }, by simp [source, molecule],
    by simp [P93AuthorityBinaryInteractionKind]⟩

theorem bondTwoThree_valid :
    bondTwoThree.ValidFor fixturePolicy.physicalObservation source := by
  simp only [bondTwoThree, P93AuthorityPhysicalUnit.ValidFor]
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  exact ⟨{ participants := [2, 3], kind := .covalent 1 }, by simp [source, molecule],
    by simp [P93AuthorityBinaryInteractionKind]⟩

theorem bondFourFive_valid :
    bondFourFive.ValidFor fixturePolicy.physicalObservation source := by
  simp only [bondFourFive, P93AuthorityPhysicalUnit.ValidFor]
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  exact ⟨{ participants := [4, 5], kind := .covalent 1 }, by simp [source, molecule],
    by simp [P93AuthorityBinaryInteractionKind]⟩

theorem citationOne_valid : citationOne.Valid := by
  simp [citationOne, P93AuthorityCitationToken.Valid]

theorem citationTwo_valid : citationTwo.Valid := by
  simp [citationTwo, P93AuthorityCitationToken.Valid]

theorem citationThree_valid : citationThree.Valid := by
  simp [citationThree, P93AuthorityCitationToken.Valid]

theorem assignmentOne_valid :
    assignmentOne.unit.ValidFor fixturePolicy.physicalObservation source := by
  simpa [assignmentOne] using bondOneTwo_valid

theorem assignmentTwo_valid :
    assignmentTwo.unit.ValidFor fixturePolicy.physicalObservation source := by
  simpa [assignmentTwo] using bondTwoThree_valid

theorem assignmentThree_valid :
    assignmentThree.unit.ValidFor fixturePolicy.physicalObservation source := by
  simpa [assignmentThree] using bondFourFive_valid

/-- The fixture three-assignment configuration is source faithful.  Unit equality is constructor
equality on the raw `Nat` references, so the three distinct bonds are distinct units. -/
theorem configuration_inputFaithful :
    P93GeneralConfigurationInputFaithful fixturePolicy source
      ({ assignments := [assignmentOne, assignmentTwo, assignmentThree] } :
        P93GeneralAuthorityConfiguration fixturePolicy) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp
  · simp [assignmentOne, assignmentTwo, assignmentThree, bondOneTwo, bondTwoThree, bondFourFive]
  · simp [assignmentOne, assignmentTwo, assignmentThree, citationOne, citationTwo, citationThree]
  · intro assignment member
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨assignmentOne_valid, citationOne_valid, trivial⟩
    · exact ⟨assignmentTwo_valid, citationTwo_valid, trivial⟩
    · exact ⟨assignmentThree_valid, citationThree_valid, trivial⟩
  · intro assignment _member
    trivial

/-- The fixture configuration. -/
def configuration : P93GeneralAuthorityConfiguration fixturePolicy :=
  fixtureBaseConfiguration

theorem configuration_faithful :
    P93GeneralConfigurationInputFaithful fixturePolicy source configuration :=
  configuration_inputFaithful

/-! ### Nonvacuity and strictness of the whole-configuration class -/

/-- The base whole fixture configuration is authorized at the fixture source.  This is a genuine
membership proof: the predicate is not `True`. -/
theorem configuration_authorized :
    fixturePolicy.ConfigurationAuthorized source configuration := by
  change fixtureConfigurationAuthorized source configuration
  unfold fixtureConfigurationAuthorized
  exact ⟨rfl, by
    simp [fixtureAuthorizedConfigurations, configuration, fixtureBaseConfiguration]⟩

/-- The globally mirrored whole fixture configuration is authorized. -/
theorem mirroredConfiguration_authorized :
    fixturePolicy.ConfigurationAuthorized source
      (configuration.globallyMirrored fixturePolicy.mirrorAction) := by
  have normalForm : configuration.globallyMirrored fixturePolicy.mirrorAction =
      fixtureMirroredConfiguration := rfl
  change fixtureConfigurationAuthorized source
    (configuration.globallyMirrored fixturePolicy.mirrorAction)
  unfold fixtureConfigurationAuthorized
  refine ⟨rfl, ?_⟩
  rw [normalForm]
  simp [fixtureAuthorizedConfigurations, fixtureMirroredConfiguration,
    fixtureBaseConfiguration, fixtureAssignments]

/-- The whole fixture configuration obtained by the exact `ambo` inversion at citation `1` is
authorized. -/
theorem invertedConfiguration_authorized :
    fixturePolicy.ConfigurationAuthorized source
      (p93GeneralConfigurationInvertedAtCitation fixturePolicy citationOne configuration) := by
  have normalForm :
      p93GeneralConfigurationInvertedAtCitation fixturePolicy citationOne configuration =
        fixtureInvertedConfiguration := rfl
  change fixtureConfigurationAuthorized source
    (p93GeneralConfigurationInvertedAtCitation fixturePolicy citationOne configuration)
  unfold fixtureConfigurationAuthorized
  refine ⟨rfl, ?_⟩
  rw [normalForm]
  simp [fixtureAuthorizedConfigurations, fixtureInvertedConfiguration,
    fixtureBaseConfiguration, fixtureAssignments]

/-- Every authorized whole configuration has exactly the three fixture assignments.  This
characterizes the class structurally and rules out treating it as an arbitrary predicate. -/
theorem authorizedConfiguration_length
    {configuration : P93AuthorityConfiguration Descriptor}
    (authorized : fixturePolicy.ConfigurationAuthorized source configuration) :
    configuration.assignments.length = 3 := by
  change fixtureConfigurationAuthorized source configuration at authorized
  unfold fixtureConfigurationAuthorized at authorized
  have membership := authorized.2
  simp only [fixtureAuthorizedConfigurations, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at membership
  rcases membership with equal | equal | equal
  · rw [equal]
    simp [fixtureBaseConfiguration, fixtureAssignments]
  · rw [equal]
    simp [fixtureMirroredConfiguration, fixtureBaseConfiguration, fixtureAssignments,
      P93AuthorityConfiguration.globallyMirrored]
  · rw [equal]
    simp [fixtureInvertedConfiguration, fixtureAssignments]

/-- The authorization class is inhabited: the base whole configuration is authorized. -/
theorem authorizedConfigurations_nonempty :
    ∃ authorizedConfiguration : P93AuthorityConfiguration Descriptor,
      fixturePolicy.ConfigurationAuthorized source authorizedConfiguration :=
  ⟨configuration, configuration_authorized⟩

/-- The fixture class is not the universal predicate: the empty configuration is not authorized.
Together with nonvacuity this shows the class is a genuine restriction to complete fixture
configurations. -/
theorem emptyConfiguration_not_authorized :
    ¬ fixturePolicy.ConfigurationAuthorized source
      ({ assignments := [] } : P93AuthorityConfiguration Descriptor) := by
  intro authorized
  have lengths := authorizedConfiguration_length authorized
  change 0 = 3 at lengths
  omega

theorem configuration_canonical :
    P93GeneralIsCanonicalNamedRepresentative fixturePolicy configuration := by
  refine ⟨assignmentOne, by simp [configuration, fixtureBaseConfiguration, fixtureAssignments],
    ?_, ?_, ?_, ?_⟩
  · simpa [fixturePolicy, assignmentOne] using
      BlueBookP93.GeneralConfiguration.Descriptor.representativeEligible_capitalR
  · simpa [fixturePolicy, assignmentOne] using
      BlueBookP93.GeneralConfiguration.Descriptor.enantiomer_ne_of_eligible
        BlueBookP93.GeneralConfiguration.Descriptor.capitalR
        (by simp [BlueBookP93.GeneralConfiguration.Descriptor.RepresentativeEligible])
  · intro assignment member _eligible _mirrorNe
    simp only [configuration, fixtureBaseConfiguration, fixtureAssignments, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · simp [assignmentOne, assignmentTwo, assignmentThree,
        P93AuthorityCitationToken.CitationLE,
        P93AuthorityCitationToken.key, P93AuthorityNatListLexLE, citationOne, citationTwo,
        citationThree]
    · simp [assignmentOne, assignmentTwo, assignmentThree,
        P93AuthorityCitationToken.CitationLE,
        P93AuthorityCitationToken.key, P93AuthorityNatListLexLE, citationOne, citationTwo,
        citationThree]
    · simp [assignmentOne, assignmentTwo, assignmentThree,
        P93AuthorityCitationToken.CitationLE,
        P93AuthorityCitationToken.key, P93AuthorityNatListLexLE, citationOne, citationTwo,
        citationThree]
  · simpa [fixturePolicy, assignmentOne,
      BlueBookP93.GeneralConfiguration.Descriptor.PreferredAtLowest]

/-- The absolute fixture observation. -/
def absoluteObservation : P93AbsoluteConfigurationAuthorityObservation fixturePolicy :=
  { configuration := configuration }

/-- The absolute fixture is actually judged: source faithfulness **and** authorization of the
whole configuration. -/
theorem absolute_judged :
    P93AbsoluteConfigurationJudged fixturePolicy source absoluteObservation :=
  ⟨configuration_faithful, configuration_authorized⟩

/-- The relative fixture observation: the second representative is the global mirror. -/
def relativeObservation : P93RelativeConfigurationAuthorityObservation fixturePolicy :=
  { first := configuration
    second := configuration.globallyMirrored fixturePolicy.mirrorAction }

/-- The relative fixture is actually judged: source faithfulness, canonical representative, the
certified global mirror equivalence, and authorization of **both** whole configurations. -/
theorem relative_judged :
    P93RelativeConfigurationJudged fixturePolicy source relativeObservation := by
  refine ⟨configuration_faithful, configuration_canonical, ?_, ?_, ?_⟩
  · exact Or.inr rfl
  · exact configuration_authorized
  · exact mirroredConfiguration_authorized



def mixedObservation : P93MixedAbsoluteRelativeAuthorityObservation fixturePolicy :=
  { configuration := configuration
    plan :=
      { assignments :=
          [ { located := assignmentOne, scope := .absolute }
          , { located := assignmentTwo, scope := .relative 0 }
          , { located := assignmentThree, scope := .relative 0 } ] }
    observedTypography :=
      [ (citationOne, .plain), (citationTwo, .starred), (citationThree, .starred) ] }




theorem mixed_judged :
    P93MixedAbsoluteRelativeJudged fixturePolicy source mixedObservation := by
  refine ⟨configuration_faithful, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · refine ⟨⟨{ located := assignmentOne, scope := .absolute }, ?_, rfl⟩,
      ⟨{ located := assignmentTwo, scope := .relative 0 }, ?_, 0, rfl⟩⟩
    · simp [mixedObservation]
    · simp [mixedObservation]
  · intro group present
    rcases present with ⟨assignment, member, scope⟩
    simp only [mixedObservation, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl
    · cases scope
    · have groupZero : group = 0 := by simpa using (scope.symm)
      rw [groupZero]
      refine ⟨by simp [mixedObservation], ?_⟩
      exact ⟨{ located := assignmentTwo, scope := .relative 0 }, by simp [mixedObservation],
        rfl, by
          simpa [fixturePolicy, assignmentTwo] using
            BlueBookP93.GeneralConfiguration.Descriptor.enantiomer_ne_of_eligible
              BlueBookP93.GeneralConfiguration.Descriptor.capitalS
              (by simp [BlueBookP93.GeneralConfiguration.Descriptor.RepresentativeEligible])⟩
    · have groupZero : group = 0 := by simpa using (scope.symm)
      rw [groupZero]
      refine ⟨by simp [mixedObservation], ?_⟩
      exact ⟨{ located := assignmentThree, scope := .relative 0 }, by simp [mixedObservation],
        rfl, by
          simpa [fixturePolicy, assignmentThree] using
            BlueBookP93.GeneralConfiguration.Descriptor.enantiomer_ne_of_eligible
              BlueBookP93.GeneralConfiguration.Descriptor.capitalR
              (by simp [BlueBookP93.GeneralConfiguration.Descriptor.RepresentativeEligible])⟩
  · rfl
  · exact configuration_authorized

/-- The descriptor list of the fixture configuration, in assignment order. -/
theorem configuration_descriptorList :
    configuration.assignments.map (fun assignment => assignment.descriptor) =
      [ BlueBookP93.GeneralConfiguration.Descriptor.capitalR
      , BlueBookP93.GeneralConfiguration.Descriptor.capitalS
      , BlueBookP93.GeneralConfiguration.Descriptor.capitalR
      ] := rfl

/-- The descriptor list after the exact `ambo` inversion at citation `1`. -/
theorem inverted_descriptorList :
    (p93GeneralConfigurationInvertedAtCitation fixturePolicy citationOne configuration).assignments.map
        (fun assignment => assignment.descriptor) =
      [ BlueBookP93.GeneralConfiguration.Descriptor.capitalS
      , BlueBookP93.GeneralConfiguration.Descriptor.capitalS
      , BlueBookP93.GeneralConfiguration.Descriptor.capitalR
      ] := rfl

/-- The descriptor list after the certified global mirror. -/
theorem mirrored_descriptorList :
    (configuration.globallyMirrored fixturePolicy.mirrorAction).assignments.map
        (fun assignment => assignment.descriptor) =
      [ BlueBookP93.GeneralConfiguration.Descriptor.capitalS
      , BlueBookP93.GeneralConfiguration.Descriptor.capitalR
      , BlueBookP93.GeneralConfiguration.Descriptor.capitalS
      ] := rfl

/-- The racemate fixture. -/
def racemateObservation :
    BinaryMixture (P93GeneralAuthorityConfiguration fixturePolicy) :=
  { first := configuration
    second := configuration.globallyMirrored fixturePolicy.mirrorAction
    firstFraction := (1 : ℚ) / 2 }

/-- The racemate fixture is actually judged.  The original equimolar/mirror/distinctness/arithmetic
components are retained and authorization of both whole configurations is appended at the end. -/
theorem racemate_judged :
    P93RacemateJudged fixturePolicy source racemateObservation := by
  refine ⟨configuration_faithful, configuration_canonical, ?_, ?_, ?_⟩
  refine ⟨by norm_num [racemateObservation, BinaryMixture.Valid], rfl, ?_, rfl⟩
  intro equal
  have descriptorEq := congrArg
    (fun configuration : P93GeneralAuthorityConfiguration fixturePolicy =>
      configuration.assignments.map fun assignment => assignment.descriptor) equal
  change configuration.assignments.map (fun assignment => assignment.descriptor) =
    (configuration.globallyMirrored fixturePolicy.mirrorAction).assignments.map
      (fun assignment => assignment.descriptor) at descriptorEq
  rw [configuration_descriptorList, mirrored_descriptorList] at descriptorEq
  simp at descriptorEq
  -- Authorization of both whole configurations (appended conjuncts).
  exact configuration_authorized
  exact mirroredConfiguration_authorized

/-- The `ambo` fixture: invert the descriptor cited as `1` and keep the qualitative
non-equimolar composition printed by P-93.1.4. -/
def amboObservation : P93AmboAuthorityObservation fixturePolicy :=
  { citation := citationOne
    mixture :=
      { first := configuration
        second := p93GeneralConfigurationInvertedAtCitation fixturePolicy citationOne configuration
        composition := .nonEquimolar } }

/-- The stated citation really occurs in the fixture configuration with a mirror-sensitive
descriptor. -/
theorem ambo_changed :
    ∃ assignment ∈ configuration.assignments,
      assignment.citation = citationOne ∧
        fixturePolicy.localAction.mirror assignment.descriptor ≠ assignment.descriptor := by
  refine ⟨assignmentOne, by simp [configuration, fixtureBaseConfiguration, fixtureAssignments],
    rfl, ?_⟩
  simpa [fixturePolicy, assignmentOne] using
    BlueBookP93.GeneralConfiguration.Descriptor.enantiomer_ne_of_eligible
      BlueBookP93.GeneralConfiguration.Descriptor.capitalR
      (by simp [BlueBookP93.GeneralConfiguration.Descriptor.RepresentativeEligible])

/-- The `ambo` fixture is actually judged.  The second configuration is exactly the upstream
inversion, not a copy of the first or a new numerical mixture; authorization of both whole
configurations is appended at the end. -/
theorem ambo_judged :
    P93AmboJudged fixturePolicy source amboObservation := by
  refine ⟨configuration_faithful, ?_, ?_, ?_⟩
  · refine ⟨rfl, ambo_changed, rfl, ?_, ?_⟩
    · intro relative
      rcases relative with same | mirrored
      · have descriptorEq := congrArg
          (fun configuration : P93GeneralAuthorityConfiguration fixturePolicy =>
            configuration.assignments.map fun assignment => assignment.descriptor) same
        change
          (p93GeneralConfigurationInvertedAtCitation fixturePolicy citationOne
            configuration).assignments.map (fun assignment => assignment.descriptor) =
            configuration.assignments.map (fun assignment => assignment.descriptor) at descriptorEq
        rw [inverted_descriptorList, configuration_descriptorList] at descriptorEq
        simp at descriptorEq
      · have descriptorEq := congrArg
          (fun configuration : P93GeneralAuthorityConfiguration fixturePolicy =>
            configuration.assignments.map fun assignment => assignment.descriptor) mirrored
        change
          (p93GeneralConfigurationInvertedAtCitation fixturePolicy citationOne
            configuration).assignments.map (fun assignment => assignment.descriptor) =
            (configuration.globallyMirrored fixturePolicy.mirrorAction).assignments.map
              (fun assignment => assignment.descriptor) at descriptorEq
        rw [inverted_descriptorList, mirrored_descriptorList] at descriptorEq
        simp at descriptorEq
    · intro equal
      have descriptorEq := congrArg
        (fun configuration : P93GeneralAuthorityConfiguration fixturePolicy =>
          configuration.assignments.map fun assignment => assignment.descriptor) equal
      change configuration.assignments.map (fun assignment => assignment.descriptor) =
        (p93GeneralConfigurationInvertedAtCitation fixturePolicy citationOne
          configuration).assignments.map (fun assignment => assignment.descriptor) at descriptorEq
      rw [configuration_descriptorList, inverted_descriptorList] at descriptorEq
      simp at descriptorEq
  · exact configuration_authorized
  · exact invertedConfiguration_authorized

/-- The five fixture tags, all actually judged at the fixture source. -/
def allObservations : List (SourceGeneralObservation fixturePolicy) :=
  [ .absolute absoluteObservation
  , .relative relativeObservation
  , .mixedAbsoluteRelative mixedObservation
  , .racemate racemateObservation
  , .ambo amboObservation
  ]

/-- The list has exactly five entries, one per reviewed row. -/
@[simp] theorem allObservations_length : allObservations.length = 5 := rfl

/-- Every fixture tag is nonvacuously judged at the same structurally certified source. -/
theorem allObservations_judged :
    ∀ observation ∈ allObservations,
      observation.Judged fixturePolicy source := by
  intro observation member
  simp only [allObservations, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact absolute_judged
  · exact relative_judged
  · exact mixed_judged
  · exact racemate_judged
  · exact ambo_judged

/-- The fixture rows are exactly the five reviewed P-93.1 rows. -/
theorem allObservations_rows :
    allObservations.map SourceGeneralObservation.row =
      [ .absoluteConfiguration
      , .relativeConfiguration
      , .mixedAbsoluteRelativeConfiguration
      , .racemates
      , .ambo
      ] := rfl

end Fixture

end

end OrganicStereoP93GeneralAuthorityIngress

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93GeneralAuthorityIngress.decodeGeneralObservation_encodeGeneralObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93GeneralAuthorityIngress.encodeGeneralObservation_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93GeneralAuthorityIngress.decodeGeneralObservation_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93GeneralAuthorityIngress.encodeGeneralObservation_decodeGeneralObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93GeneralAuthorityIngress.SourceGeneralObservation.boundedIn_of_judged
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93GeneralAuthorityIngress.decodeGeneralAuthority_encodeGeneralAuthority
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93GeneralAuthorityIngress.Fixture.allObservations_judged
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93GeneralAuthorityIngress.Fixture.configuration_authorized
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93GeneralAuthorityIngress.Fixture.authorizedConfigurations_nonempty
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93GeneralAuthorityIngress.Fixture.emptyConfiguration_not_authorized
