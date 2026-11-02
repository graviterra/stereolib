import TetraStereo.OneCenter.IUPACRemaining71ProvisionInventory
import TetraStereo.OneCenter.IUPACP93AuthorityConfigurationCarrier
import TetraStereo.OneCenter.P93GeneralConfiguration

set_option autoImplicit false

/-!
# Reviewed P-93.1 general-configuration reference family

This module turns the five already independent P-93.1 semantic relations into one typed authority
family.  The row enumeration owns the provision projection, semantic kind, dependent observation
type, and judgment relation.  Consequently the global compiler can consume five audited rows from
one family table rather than treating them as five unrelated proof projects.

The reference program remains independent of the production descriptor pipeline: it is expressed
only through `BlueBookP93.GeneralConfiguration` configurations, scope plans, and mixtures.

P-93.1 pairs a whole configuration with its authority evidence.  Each `Judged` relation below
therefore requires `policy.ConfigurationAuthorized` for the whole configuration (and for both
members of a correlation), not merely per-unit descriptor authorization.  This is what prevents a
flattened `(R,S)`/`(S,R)` list from passing as arbitrary `(R,R)`/`(S,S)` evidence while keeping
`P93GeneralConfigurationInputFaithful` structurally unchanged.

## Global mirror versus local inversion

Two distinct certified involutions are carried by the policy:

* `mirrorAction` is the **global** reflection of the whole molecular entity.  It is the relation
  used by relative configuration and racemates.  In the canonical descriptor vocabulary it fixes
  pseudoasymmetric `r/s` descriptors (P-9: reflection exchanges the two enantiomorphic ligands
  together with the ligand priorities, so the pseudoasymmetric sense is unchanged).
* `localAction` is the involutive **local** descriptor inversion obtained by exchanging the two
  ligands at one stated stereogenic unit.  At a pseudoasymmetric centre this exchange reverses the
  pseudoasymmetric sense, so `localAction` swaps `r/s` while `mirrorAction` fixes it.

P-93.1.4's `ambo` construction inverts exactly one stated citation, so it is a local operation and
uses `localAction`.  The changed-target gate and the citation inversion below therefore consult the
local action, while the `¬ RelativeEquivalent policy.mirrorAction ...` condition that distinguishes
the epimer from the global enantiomer continues to use the global mirror.

`localAction` is a descriptor operation on the stated configuration.  It is not a claim that
physically inverting an arbitrary molecular centre leaves remote CIP descriptors unchanged; source
applicability, physical observation evidence, and CIP assignment remain separate obligations.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open BlueBookP93

/-- Audited P-93.1 reference boundary.  The descriptor language is itself authority data, so one
family definition covers every physical-unit family instead of hard-coding tetrahedral or axial
constructors.

`mirrorAction` is the certified **global** reflection: it may fix descriptors such as `E/Z` and
pseudoasymmetric `r/s` while exchanging enantiomorphic pairs.  `localAction` is the distinct
involutive **local** inversion used by P-93.1.4 `ambo` and by any operation that epimerizes one
stated stereogenic unit; it is required data, with no default and no `True` fallback.  The canonical
producer supplies a table that exchanges pseudoasymmetric `r/s` (which global reflection fixes).

`ConfigurationAuthorized` is a required whole-configuration source relation.  It has no fallback
value, no `True` instance, and no mirror-closure postulate: the actual canonical producer must
construct it from one typed source entry containing the whole configuration.  In particular it is
evidence about paired configuration correlation, not a proof of spatial geometry or CIP handedness
by itself; `physicalObservation`, `DescriptorAuthorized`, and the family geometry conformance
relations remain separate obligations. -/
structure P93GeneralAuthorityPolicy where
  Descriptor : Type
  mirrorAction : P93AuthorityConfiguration.MirrorAction Descriptor
  /-- The involutive **local** descriptor action.  This is not `mirrorAction`: inverting the
  configuration at one stated stereogenic unit exchanges two ligands at that unit, which reverses
  a pseudoasymmetric `r/s` descriptor even though a global reflection fixes it. -/
  localAction : P93AuthorityConfiguration.MirrorAction Descriptor
  RepresentativeEligible : Descriptor → Prop
  representativeEligible_mirror_iff : ∀ descriptor,
    RepresentativeEligible (mirrorAction.mirror descriptor) ↔
      RepresentativeEligible descriptor
  PreferredAtLowest : Descriptor → Prop
  mirrorPreferredAtLowest : ∀ descriptor,
    RepresentativeEligible descriptor →
      mirrorAction.mirror descriptor ≠ descriptor →
      (PreferredAtLowest (mirrorAction.mirror descriptor) ↔
        ¬PreferredAtLowest descriptor)
  physicalObservation : P93AuthorityPhysicalObservationPolicy
  CitationAuthorized :
    AuthoritativeChemicalInput → P93AuthorityCitationToken →
      P93AuthorityPhysicalUnit → Prop
  DescriptorAuthorized :
    AuthoritativeChemicalInput → P93AuthorityPhysicalUnit → Descriptor → Prop
  descriptorAuthorized_mirror_iff : ∀ source unit descriptor,
    DescriptorAuthorized source unit (mirrorAction.mirror descriptor) ↔
      DescriptorAuthorized source unit descriptor
  /-- Source-bound authority evidence for one whole configuration.  Different configurations
  with the same per-unit descriptor multiset (for example `(R,S)` and `(S,R)`) must be
  distinguished by this relation.  It is a trust parameter of the generic policy, not a claim
  that the configuration is spatially correct. -/
  ConfigurationAuthorized :
    AuthoritativeChemicalInput → P93AuthorityConfiguration Descriptor → Prop

abbrev P93GeneralAuthorityConfiguration (policy : P93GeneralAuthorityPolicy) :=
  P93AuthorityConfiguration policy.Descriptor

/-- A source-faithful absolute configuration contains distinct physical units and distinct actual
citation tokens, and every descriptor is authorized for the corresponding unit by the audited
reference policy.

This definition is deliberately unchanged by whole-configuration authorization: it remains the
structural, per-assignment admissibility relation used by applicability. -/
def P93GeneralConfigurationInputFaithful
    (policy : P93GeneralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (configuration : P93GeneralAuthorityConfiguration policy) : Prop :=
  P93AuthorityConfiguration.InputFaithful source policy.physicalObservation
      (policy.CitationAuthorized source) configuration ∧
    ∀ assignment ∈ configuration.assignments,
      policy.DescriptorAuthorized source assignment.unit assignment.descriptor

def P93GeneralConfigurationApplicable
    (policy : P93GeneralAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ configuration, P93GeneralConfigurationInputFaithful policy source configuration

/-- Lowest-citation selection ignores descriptors outside the representative language and
mirror-invariant local descriptors, then selects the first eligible enantiomorphic descriptor.
This allows complete configurations containing `E/Z`-like assignments without allowing them to
decide the `rel`/`rac` representative.

The check remains a **global** check: `RepresentativeEligible` excludes pseudoasymmetric `r/s`
descriptors, so `mirrorAction` is the correct action here and `localAction` plays no role. -/
def P93GeneralIsCanonicalNamedRepresentative
    (policy : P93GeneralAuthorityPolicy)
    (configuration : P93GeneralAuthorityConfiguration policy) : Prop :=
  ∃ leading ∈ configuration.assignments,
    policy.RepresentativeEligible leading.descriptor ∧
    policy.mirrorAction.mirror leading.descriptor ≠ leading.descriptor ∧
    (∀ assignment ∈ configuration.assignments,
      policy.RepresentativeEligible assignment.descriptor →
      policy.mirrorAction.mirror assignment.descriptor ≠ assignment.descriptor →
        leading.citation.CitationLE assignment.citation) ∧
    policy.PreferredAtLowest leading.descriptor

/-- Evidence presented to the absolute-configuration clause. -/
structure P93AbsoluteConfigurationAuthorityObservation
    (policy : P93GeneralAuthorityPolicy) where
  configuration : P93GeneralAuthorityConfiguration policy

def P93AbsoluteConfigurationJudged
    (policy : P93GeneralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AbsoluteConfigurationAuthorityObservation policy) : Prop :=
  P93GeneralConfigurationInputFaithful policy source observation.configuration ∧
    policy.ConfigurationAuthorized source observation.configuration

/-- Two absolute representatives whose relationship is judged by the policy's certified global
mirror equivalence.  Both whole configurations need source-bound authorization; the mirror
relation itself is not used to synthesize authorization for the second configuration. -/
structure P93RelativeConfigurationAuthorityObservation
    (policy : P93GeneralAuthorityPolicy) where
  first : P93GeneralAuthorityConfiguration policy
  second : P93GeneralAuthorityConfiguration policy

def P93RelativeConfigurationJudged
    (policy : P93GeneralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93RelativeConfigurationAuthorityObservation policy) : Prop :=
  P93GeneralConfigurationInputFaithful policy source observation.first ∧
    P93GeneralIsCanonicalNamedRepresentative policy observation.first ∧
    (P93AuthorityConfiguration.RelativeEquivalent policy.mirrorAction
        observation.first observation.second ∧
      (policy.ConfigurationAuthorized source observation.first ∧
        policy.ConfigurationAuthorized source observation.second))

/-- Scope evidence retains the entire located assignment, so typography cannot be transferred
between equal-looking citations belonging to different physical units. -/
structure P93GeneralScopedAuthorityAssignment
    (policy : P93GeneralAuthorityPolicy) where
  located : P93AuthorityLocatedAssignment policy.Descriptor
  scope : GeneralConfiguration.AssignmentScope

structure P93GeneralAuthorityScopePlan
    (policy : P93GeneralAuthorityPolicy) where
  assignments : List (P93GeneralScopedAuthorityAssignment policy)

def P93GeneralAuthorityScopePlan.HasAbsolute
    {policy : P93GeneralAuthorityPolicy}
    (plan : P93GeneralAuthorityScopePlan policy) : Prop :=
  ∃ assignment ∈ plan.assignments, assignment.scope = .absolute

def P93GeneralAuthorityScopePlan.HasRelative
    {policy : P93GeneralAuthorityPolicy}
    (plan : P93GeneralAuthorityScopePlan policy) : Prop :=
  ∃ assignment ∈ plan.assignments, ∃ group,
    assignment.scope = .relative group

def P93GeneralAuthorityScopePlan.MixedAbsoluteRelative
    {policy : P93GeneralAuthorityPolicy}
    (plan : P93GeneralAuthorityScopePlan policy) : Prop :=
  plan.HasAbsolute ∧ plan.HasRelative

def P93GeneralMixedTypography
    {policy : P93GeneralAuthorityPolicy}
    (assignment : P93GeneralScopedAuthorityAssignment policy) :
    GeneralConfiguration.DescriptorTypography :=
  match assignment.scope with
  | .absolute => .plain
  | .relative _ => .starred

/-- A mixed-scope observation retains actual typography and the exact absolute configuration to
which every scope annotation belongs. -/
structure P93MixedAbsoluteRelativeAuthorityObservation
    (policy : P93GeneralAuthorityPolicy) where
  configuration : P93GeneralAuthorityConfiguration policy
  plan : P93GeneralAuthorityScopePlan policy
  observedTypography : List
    (P93AuthorityCitationToken × GeneralConfiguration.DescriptorTypography)

def P93MixedRelativeGroupsNontrivial
    {policy : P93GeneralAuthorityPolicy}
    (plan : P93GeneralAuthorityScopePlan policy) : Prop :=
  ∀ group,
    (∃ assignment ∈ plan.assignments,
      assignment.scope = .relative group) →
    2 ≤ (plan.assignments.filter fun assignment =>
      decide (assignment.scope = .relative group)).length ∧
    ∃ assignment ∈ plan.assignments,
      assignment.scope = .relative group ∧
        policy.mirrorAction.mirror assignment.located.descriptor ≠
          assignment.located.descriptor

def P93MixedAbsoluteRelativeJudged
    (policy : P93GeneralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MixedAbsoluteRelativeAuthorityObservation policy) : Prop :=
  P93GeneralConfigurationInputFaithful policy source observation.configuration ∧
    observation.plan.assignments.map (fun assignment => assignment.located) =
      observation.configuration.assignments ∧
    observation.plan.MixedAbsoluteRelative ∧
    P93MixedRelativeGroupsNontrivial observation.plan ∧
    observation.observedTypography = observation.plan.assignments.map (fun assignment =>
      (assignment.located.citation, P93GeneralMixedTypography assignment)) ∧
    policy.ConfigurationAuthorized source observation.configuration

/-- An equimolar mixture of two distinct authority configurations related by the certified global
descriptor mirror action.  A racemate is a whole-molecule (global) notion, so this definition
continues to use `mirrorAction`. -/
def P93GeneralIsRacemate
    (policy : P93GeneralAuthorityPolicy)
    (mixture : GeneralConfiguration.BinaryMixture
      (P93GeneralAuthorityConfiguration policy)) : Prop :=
  mixture.Valid ∧
    mixture.second = mixture.first.globallyMirrored policy.mirrorAction ∧
    mixture.first ≠ mixture.second ∧
    mixture.firstFraction = (1 : ℚ) / 2

def P93RacemateJudged
    (policy : P93GeneralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : GeneralConfiguration.BinaryMixture
      (P93GeneralAuthorityConfiguration policy)) : Prop :=
  P93GeneralConfigurationInputFaithful policy source observation.first ∧
    P93GeneralIsCanonicalNamedRepresentative policy observation.first ∧
    P93GeneralIsRacemate policy observation ∧
    (policy.ConfigurationAuthorized source observation.first ∧
      policy.ConfigurationAuthorized source observation.second)

/-- Invert exactly the descriptor carried by the named source citation, using the policy's
**local** descriptor action.  The physical unit and the full decorated citation token are retained.
The operation is a descriptor operation on the stated configuration: it says nothing about remote
CIP descriptors of a physically re-prepared molecule, and it is not a source-applicability
certificate. -/
def p93GeneralInvertAssignmentAtCitation
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (assignment : P93AuthorityLocatedAssignment policy.Descriptor) :
    P93AuthorityLocatedAssignment policy.Descriptor :=
  if assignment.citation = target then
    { assignment with
      descriptor := policy.localAction.mirror assignment.descriptor }
  else assignment

/-- The citation of an assignment is never changed by local inversion. -/
@[simp] theorem p93GeneralInvertAssignmentAtCitation_citation
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (assignment : P93AuthorityLocatedAssignment policy.Descriptor) :
    (p93GeneralInvertAssignmentAtCitation policy target assignment).citation =
      assignment.citation := by
  unfold p93GeneralInvertAssignmentAtCitation
  by_cases same : assignment.citation = target <;> simp [same]

/-- The physical unit of an assignment is never changed by local inversion. -/
@[simp] theorem p93GeneralInvertAssignmentAtCitation_unit
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (assignment : P93AuthorityLocatedAssignment policy.Descriptor) :
    (p93GeneralInvertAssignmentAtCitation policy target assignment).unit =
      assignment.unit := by
  unfold p93GeneralInvertAssignmentAtCitation
  by_cases same : assignment.citation = target <;> simp [same]

/-- Local inversion is the identity at every citation other than the selected one. -/
theorem p93GeneralInvertAssignmentAtCitation_eq_self_of_ne
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (assignment : P93AuthorityLocatedAssignment policy.Descriptor)
    (different : assignment.citation ≠ target) :
    p93GeneralInvertAssignmentAtCitation policy target assignment = assignment := by
  simp [p93GeneralInvertAssignmentAtCitation, different]

/-- At the selected citation, local inversion applies exactly the policy's local unit action. -/
theorem p93GeneralInvertAssignmentAtCitation_at
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (assignment : P93AuthorityLocatedAssignment policy.Descriptor)
    (same : assignment.citation = target) :
    p93GeneralInvertAssignmentAtCitation policy target assignment =
      { assignment with
        descriptor := policy.localAction.mirror assignment.descriptor } := by
  simp [p93GeneralInvertAssignmentAtCitation, same]

/-- One local inversion is an involution at the assignment level. -/
theorem p93GeneralInvertAssignmentAtCitation_involutive
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (assignment : P93AuthorityLocatedAssignment policy.Descriptor) :
    p93GeneralInvertAssignmentAtCitation policy target
      (p93GeneralInvertAssignmentAtCitation policy target assignment) = assignment := by
  by_cases same : assignment.citation = target
  · rw [p93GeneralInvertAssignmentAtCitation_at policy target assignment same]
    have citationSame :
        ({ assignment with
          descriptor := policy.localAction.mirror assignment.descriptor } :
            P93AuthorityLocatedAssignment policy.Descriptor).citation = target := by
      simp [same]
    rw [p93GeneralInvertAssignmentAtCitation_at policy target
      { assignment with
        descriptor := policy.localAction.mirror assignment.descriptor } citationSame]
    simp [policy.localAction.involutive]
  · simp [p93GeneralInvertAssignmentAtCitation, same]

/-- Invert exactly the descriptor carried by the named source citation, retaining its physical
unit and the full decorated citation token.  The inversion uses the policy's **local** descriptor
action, not the global mirror. -/
def p93GeneralConfigurationInvertedAtCitation
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (configuration : P93GeneralAuthorityConfiguration policy) :
    P93GeneralAuthorityConfiguration policy where
  assignments := configuration.assignments.map
    (p93GeneralInvertAssignmentAtCitation policy target)

/-- The ordered assignment list of the inverted configuration. -/
theorem p93GeneralConfigurationInvertedAtCitation_assignments
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (configuration : P93GeneralAuthorityConfiguration policy) :
    (p93GeneralConfigurationInvertedAtCitation policy target configuration).assignments =
      configuration.assignments.map
        (p93GeneralInvertAssignmentAtCitation policy target) :=
  rfl

/-- Local inversion leaves the ordered physical-unit list unchanged. -/
theorem p93GeneralConfigurationInvertedAtCitation_unitList
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (configuration : P93GeneralAuthorityConfiguration policy) :
    ((p93GeneralConfigurationInvertedAtCitation policy target configuration).assignments.map
        fun assignment => assignment.unit) =
      configuration.assignments.map fun assignment => assignment.unit := by
  simp only [p93GeneralConfigurationInvertedAtCitation, List.map_map]
  apply List.map_congr_left
  intro assignment _
  exact p93GeneralInvertAssignmentAtCitation_unit policy target assignment

/-- Local inversion leaves the ordered citation list unchanged.  In particular every citation
other than the selected one carries an untouched descriptor. -/
theorem p93GeneralConfigurationInvertedAtCitation_citationList
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (configuration : P93GeneralAuthorityConfiguration policy) :
    ((p93GeneralConfigurationInvertedAtCitation policy target configuration).assignments.map
        fun assignment => assignment.citation) =
      configuration.assignments.map fun assignment => assignment.citation := by
  simp only [p93GeneralConfigurationInvertedAtCitation, List.map_map]
  apply List.map_congr_left
  intro assignment _
  exact p93GeneralInvertAssignmentAtCitation_citation policy target assignment

/-- Performing the same local inversion twice returns the original configuration. -/
theorem p93GeneralConfigurationInvertedAtCitation_involutive
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (configuration : P93GeneralAuthorityConfiguration policy) :
    p93GeneralConfigurationInvertedAtCitation policy target
      (p93GeneralConfigurationInvertedAtCitation policy target configuration) =
        configuration := by
  apply P93AuthorityConfiguration.ext
  simp only [p93GeneralConfigurationInvertedAtCitation, List.map_map]
  trans configuration.assignments.map id
  · apply List.map_congr_left
    intro assignment _
    exact p93GeneralInvertAssignmentAtCitation_involutive policy target assignment
  · exact List.map_id configuration.assignments

/-- A list whose pointwise map is the identity fixes every member. -/
private theorem list_map_eq_self_apply
    {α : Type*} {action : α → α} {values : List α}
    (same : values.map action = values) :
    ∀ value ∈ values, action value = value := by
  induction values with
  | nil =>
      intro value member
      simp at member
  | cons head tail inductionHypothesis =>
      intro value member
      simp only [List.map_cons, List.cons.injEq] at same
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact same.1
      · exact inductionHypothesis same.2 value tailMember

/-- **The `ambo` gate reflects the local action.**  If some assignment carries the selected
citation and its descriptor is moved by `policy.localAction`, then inverting at that citation
changes the configuration.  This is the property the P-93.1.4 changed-target gate relies on: a
descriptor fixed by the local action cannot justify an `ambo` mixture. -/
theorem p93GeneralConfigurationInvertedAtCitation_ne_self_of_localChange
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (configuration : P93GeneralAuthorityConfiguration policy)
    (localChange : ∃ assignment ∈ configuration.assignments,
      assignment.citation = target ∧
        policy.localAction.mirror assignment.descriptor ≠ assignment.descriptor) :
    p93GeneralConfigurationInvertedAtCitation policy target configuration ≠
      configuration := by
  intro same
  have listSame :
      (p93GeneralConfigurationInvertedAtCitation policy target configuration).assignments =
        configuration.assignments :=
    congrArg P93AuthorityConfiguration.assignments same
  have listSame' :
      configuration.assignments.map
          (p93GeneralInvertAssignmentAtCitation policy target) =
        configuration.assignments := by
    simpa [p93GeneralConfigurationInvertedAtCitation] using listSame
  rcases localChange with ⟨assignment, member, citationSame, moved⟩
  have fixed := list_map_eq_self_apply listSame' assignment member
  have descriptorSame := congrArg
    (fun located : P93AuthorityLocatedAssignment policy.Descriptor =>
      located.descriptor) fixed
  exact moved (by
    simpa [p93GeneralInvertAssignmentAtCitation, citationSame] using descriptorSame)

/-- If the local action fixes every descriptor at the selected citation, one-citation local
inversion is the identity.  This is the converse of the changed-target gate: a citation at which
no descriptor changes cannot manufacture an `ambo` epimer. -/
theorem p93GeneralConfigurationInvertedAtCitation_eq_self_of_no_localChange
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (configuration : P93GeneralAuthorityConfiguration policy)
    (noChange : ∀ assignment ∈ configuration.assignments,
      assignment.citation = target →
        policy.localAction.mirror assignment.descriptor = assignment.descriptor) :
    p93GeneralConfigurationInvertedAtCitation policy target configuration =
      configuration := by
  apply P93AuthorityConfiguration.ext
  simp only [p93GeneralConfigurationInvertedAtCitation]
  trans configuration.assignments.map id
  · apply List.map_congr_left
    intro assignment member
    by_cases same : assignment.citation = target
    · rw [p93GeneralInvertAssignmentAtCitation_at policy target assignment same]
      rw [noChange assignment member same]
      rfl
    · exact p93GeneralInvertAssignmentAtCitation_eq_self_of_ne policy target assignment same
  · exact List.map_id configuration.assignments

/-- **The changed-target gate is exactly local change.**  The one-citation inversion differs from
the original configuration if and only if some assignment at the selected citation carries a
descriptor that the policy's local action moves.  Descriptors fixed by the local action cannot
satisfy the P-93.1.4 gate.  Conversely, a pseudoasymmetric `r/s` descriptor, which the global
mirror fixes, does satisfy the gate whenever the local action swaps it, as the canonical table
does. -/
theorem p93GeneralConfigurationInvertedAtCitation_ne_self_iff_localChange
    (policy : P93GeneralAuthorityPolicy)
    (target : P93AuthorityCitationToken)
    (configuration : P93GeneralAuthorityConfiguration policy) :
    p93GeneralConfigurationInvertedAtCitation policy target configuration ≠ configuration ↔
      ∃ assignment ∈ configuration.assignments,
        assignment.citation = target ∧
          policy.localAction.mirror assignment.descriptor ≠ assignment.descriptor := by
  constructor
  · intro different
    by_contra absent
    apply different
    apply p93GeneralConfigurationInvertedAtCitation_eq_self_of_no_localChange
    intro assignment member citationSame
    by_contra moved
    exact absent ⟨assignment, member, citationSame, moved⟩
  · exact p93GeneralConfigurationInvertedAtCitation_ne_self_of_localChange
      policy target configuration

/-- P-93.1.4's non-equimolar epimer mixture.  The citation must actually occur in the stated
configuration and its descriptor must actually be moved by the **local** action, rather than
becoming a no-op request for an absent locant or a descriptor fixed by the local action. -/
def P93GeneralIsAmboAt
    (policy : P93GeneralAuthorityPolicy)
    (citation : P93AuthorityCitationToken)
    (mixture : GeneralConfiguration.QualitativeBinaryMixture
      (P93GeneralAuthorityConfiguration policy)) : Prop :=
  mixture.composition = .nonEquimolar ∧
    (∃ assignment ∈ mixture.first.assignments,
      assignment.citation = citation ∧
        policy.localAction.mirror assignment.descriptor ≠ assignment.descriptor) ∧
    mixture.second =
      p93GeneralConfigurationInvertedAtCitation policy citation mixture.first ∧
    ¬P93AuthorityConfiguration.RelativeEquivalent policy.mirrorAction
      mixture.first mixture.second ∧
    mixture.first ≠ mixture.second

/-- The changed-target witness of the `ambo` clause is exactly a witness for the local action. -/
theorem p93GeneralIsAmboAt_localChange
    (policy : P93GeneralAuthorityPolicy)
    (citation : P93AuthorityCitationToken)
    (mixture : GeneralConfiguration.QualitativeBinaryMixture
      (P93GeneralAuthorityConfiguration policy))
    (ambo : P93GeneralIsAmboAt policy citation mixture) :
    ∃ assignment ∈ mixture.first.assignments,
      assignment.citation = citation ∧
        policy.localAction.mirror assignment.descriptor ≠ assignment.descriptor :=
  ambo.2.1

/-- The second member of an `ambo` mixture is exactly the one-citation local inversion. -/
theorem p93GeneralIsAmboAt_second
    (policy : P93GeneralAuthorityPolicy)
    (citation : P93AuthorityCitationToken)
    (mixture : GeneralConfiguration.QualitativeBinaryMixture
      (P93GeneralAuthorityConfiguration policy))
    (ambo : P93GeneralIsAmboAt policy citation mixture) :
    mixture.second =
      p93GeneralConfigurationInvertedAtCitation policy citation mixture.first :=
  ambo.2.2.1

/-- The one-citation local inversion of the first member is nontrivial whenever the `ambo` gate
holds. -/
theorem p93GeneralIsAmboAt_inversion_ne_self
    (policy : P93GeneralAuthorityPolicy)
    (citation : P93AuthorityCitationToken)
    (mixture : GeneralConfiguration.QualitativeBinaryMixture
      (P93GeneralAuthorityConfiguration policy))
    (ambo : P93GeneralIsAmboAt policy citation mixture) :
    p93GeneralConfigurationInvertedAtCitation policy citation mixture.first ≠
      mixture.first :=
  p93GeneralConfigurationInvertedAtCitation_ne_self_of_localChange policy citation
    mixture.first (p93GeneralIsAmboAt_localChange policy citation mixture ambo)

/-- The full citation token is part of the observation because `ambo` inverts one stated physical
unit rather than the whole configuration. -/
structure P93AmboAuthorityObservation
    (policy : P93GeneralAuthorityPolicy) where
  citation : P93AuthorityCitationToken
  mixture : GeneralConfiguration.QualitativeBinaryMixture
    (P93GeneralAuthorityConfiguration policy)

def P93AmboJudged
    (policy : P93GeneralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AmboAuthorityObservation policy) : Prop :=
  P93GeneralConfigurationInputFaithful policy source observation.mixture.first ∧
    P93GeneralIsAmboAt policy observation.citation observation.mixture ∧
    (policy.ConfigurationAuthorized source observation.mixture.first ∧
      policy.ConfigurationAuthorized source observation.mixture.second)

def p93AbsoluteConfigurationReference
    (policy : P93GeneralAuthorityPolicy) : ProvisionReference where
  Observation := P93AbsoluteConfigurationAuthorityObservation policy
  Applicable := P93GeneralConfigurationApplicable policy
  Judges := P93AbsoluteConfigurationJudged policy

def p93RelativeConfigurationReference
    (policy : P93GeneralAuthorityPolicy) : ProvisionReference where
  Observation := P93RelativeConfigurationAuthorityObservation policy
  Applicable := P93GeneralConfigurationApplicable policy
  Judges := P93RelativeConfigurationJudged policy

def p93MixedAbsoluteRelativeConfigurationReference
    (policy : P93GeneralAuthorityPolicy) : ProvisionReference where
  Observation := P93MixedAbsoluteRelativeAuthorityObservation policy
  Applicable := P93GeneralConfigurationApplicable policy
  Judges := P93MixedAbsoluteRelativeJudged policy

def p93RacematesReference
    (policy : P93GeneralAuthorityPolicy) : ProvisionReference where
  Observation := GeneralConfiguration.BinaryMixture
    (P93GeneralAuthorityConfiguration policy)
  Applicable := P93GeneralConfigurationApplicable policy
  Judges := P93RacemateJudged policy

def p93AmboReference
    (policy : P93GeneralAuthorityPolicy) : ProvisionReference where
  Observation := P93AmboAuthorityObservation policy
  Applicable := P93GeneralConfigurationApplicable policy
  Judges := P93AmboJudged policy

/-- The closed P-93.1 authority language.  Adding or removing a provision requires changing this
enumeration and re-establishing the exact projection theorem below. -/
inductive Remaining71P93GeneralAuthorityRow where
  | absoluteConfiguration
  | relativeConfiguration
  | mixedAbsoluteRelativeConfiguration
  | racemates
  | ambo
  deriving DecidableEq, Repr

namespace Remaining71P93GeneralAuthorityRow

def all : List Remaining71P93GeneralAuthorityRow :=
  [ .absoluteConfiguration
  , .relativeConfiguration
  , .mixedAbsoluteRelativeConfiguration
  , .racemates
  , .ambo
  ]

def provision : Remaining71P93GeneralAuthorityRow → IUPACNormativeProvision
  | .absoluteConfiguration => .p93AbsoluteConfiguration
  | .relativeConfiguration => .p93RelativeConfiguration
  | .mixedAbsoluteRelativeConfiguration => .p93MixedAbsoluteRelativeConfiguration
  | .racemates => .p93Racemates
  | .ambo => .p93Ambo

def kind (_row : Remaining71P93GeneralAuthorityRow) : ProvisionKind :=
  .spatialDescriptor

def reference (policy : P93GeneralAuthorityPolicy) :
    Remaining71P93GeneralAuthorityRow → ProvisionReference
  | .absoluteConfiguration => p93AbsoluteConfigurationReference policy
  | .relativeConfiguration => p93RelativeConfigurationReference policy
  | .mixedAbsoluteRelativeConfiguration =>
      p93MixedAbsoluteRelativeConfigurationReference policy
  | .racemates => p93RacematesReference policy
  | .ambo => p93AmboReference policy

def semantics (policy : P93GeneralAuthorityPolicy)
    (row : Remaining71P93GeneralAuthorityRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := reference policy row

@[simp] theorem all_length : all.length = 5 := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem all_provisions_exact :
    all.map provision = p93GeneralSemanticsSlice := by
  rfl

set_option maxRecDepth 16384 in
@[simp] theorem classifier_exact (row : Remaining71P93GeneralAuthorityRow) :
    globalProvisionKind row.provision = row.kind := by
  cases row <;> decide

end Remaining71P93GeneralAuthorityRow

theorem remaining71P93General_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93GeneralSemanticsSlice) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : p93GeneralSemanticsSlice.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem exists_remaining71P93GeneralAuthorityRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93GeneralSemanticsSlice) :
    ∃ row, row ∈ Remaining71P93GeneralAuthorityRow.all ∧ row.provision = provision := by
  rw [← Remaining71P93GeneralAuthorityRow.all_provisions_exact] at member
  simpa only [List.mem_map] using member

noncomputable def remaining71P93GeneralAuthorityRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93GeneralSemanticsSlice) :
    Remaining71P93GeneralAuthorityRow :=
  Classical.choose (exists_remaining71P93GeneralAuthorityRow member)

theorem remaining71P93GeneralAuthorityRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93GeneralSemanticsSlice) :
    (remaining71P93GeneralAuthorityRowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_remaining71P93GeneralAuthorityRow member)).2

/-- Exact five-row reviewed batch consumed by the remaining-71 compiler. -/
structure Remaining71P93GeneralReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch p93GeneralSemanticsSlice.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ p93GeneralSemanticsSlice.toFinset),
      (reviewed.row provision member).kind = globalProvisionKind provision

noncomputable def remaining71P93GeneralReviewedSemantics
    (policy : P93GeneralAuthorityPolicy) :
    Remaining71P93GeneralReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        Remaining71P93GeneralAuthorityRow.semantics policy
          (remaining71P93GeneralAuthorityRowOf provision (by simpa using member))
      sourceAudited := by
        intro provision member
        exact remaining71P93General_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := remaining71P93GeneralAuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      remaining71P93GeneralAuthorityRowOf_provision provision (by simpa using member)
    have classified := Remaining71P93GeneralAuthorityRow.classifier_exact row
    change row.kind = globalProvisionKind provision
    simpa [rowProvision] using classified.symm

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93GeneralAuthorityRow.all_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93GeneralAuthorityRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71P93General_sourceAuditComplete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93GeneralInvertAssignmentAtCitation_involutive
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93GeneralConfigurationInvertedAtCitation_involutive
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93GeneralConfigurationInvertedAtCitation_ne_self_of_localChange
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93GeneralConfigurationInvertedAtCitation_eq_self_of_no_localChange
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93GeneralIsAmboAt_inversion_ne_self
