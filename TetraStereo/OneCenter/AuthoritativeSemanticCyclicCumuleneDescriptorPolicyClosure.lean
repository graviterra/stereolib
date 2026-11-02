import TetraStereo.OneCenter.AuthoritativeSemanticMancudeConcreteRepresentedPipelineCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Honest closure boundary for fully cyclic cumulene descriptor policy

The checked P-9 authority represented in this project classifies an all-double closed component
as a P-31 fully cyclic cumulene and proves that the P-93 *open-terminal* cumulene descriptor
schema does not apply.  It does not yet state a nonterminal/inherent-chirality descriptor policy
for that topology.

This module closes all remaining list and transport plumbing without inventing that missing
chemical premise.  A caller supplies an independent semantic relation between a perceived
component and a policy-specific descriptor type.  The relation is not an executable result.
Classical choice is used only to expose its unique witness through a noncomputable specification
analyzer.  Under the explicit functionality premise, descriptor emission is equivalent to the
semantic relation, every eligible component emits exactly once, every ineligible component keeps
one P-31 boundary record, and the existing five-branch public result is transported injectively.
-/

/-- An independently stated nonterminal descriptor policy for fully cyclic cumulenes.  The
descriptor type is deliberately abstract: the currently checked source does not justify choosing
`E/Z`, `M/P`, `Rₐ/Sₐ`, or any other family for this topology. -/
abbrev AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy
    (source : AuthoritativeChemicalInput) (PolicyDescriptor : Type*) :=
  source.AromaticCanonicalCyclicCumuleneComponent → PolicyDescriptor → Prop

/-- Exact-once descriptor output requires a naming context in which the independent policy has
at most one descriptor for each genuinely perceived component.  Existence is intentionally not
required: an ineligible component remains an authority-boundary result. -/
def AromaticCanonicalFullyCyclicCumuleneDescriptorPolicyFunctional
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor) :
    Prop :=
  ∀ component,
    source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component →
      ∀ left right, policy component left → policy component right → left = right

/-- Independent component-level eligibility.  Both topology and a policy witness are visible;
neither is inferred from success of the analyzer below. -/
def DeclarativeAromaticCanonicalFullyCyclicCumuleneDescriptorEligible
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (component : source.AromaticCanonicalCyclicCumuleneComponent) : Prop :=
  source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component ∧
    ∃ descriptor, policy component descriptor

/-- Specification-level exposure of a semantic policy witness.  This is deliberately
noncomputable and therefore does not pretend that the missing chemical policy has been parsed into
an executable production rule. -/
noncomputable def aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (component : source.AromaticCanonicalCyclicCumuleneComponent) :
    Option PolicyDescriptor := by
  classical
  exact if witness : ∃ descriptor, policy component descriptor then
    some witness.choose
  else
    none

/-- The specification analyzer emits a named descriptor exactly when the independent semantic
policy assigns that descriptor.  Functionality, rather than analyzer success, is the premise that
makes the selected witness unique. -/
theorem aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?_eq_some_iff
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (functional :
      source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicyFunctional policy)
    (component : source.AromaticCanonicalCyclicCumuleneComponent)
    (derived : source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component)
    (descriptor : PolicyDescriptor) :
    source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor? policy component =
        some descriptor ↔
      policy component descriptor := by
  classical
  unfold aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?
  split
  next witness =>
    constructor
    · intro selected
      have identity : witness.choose = descriptor := Option.some.inj selected
      rw [← identity]
      exact witness.choose_spec
    · intro applies
      exact congrArg some
        (functional component derived witness.choose descriptor witness.choose_spec applies)
  next absent =>
    constructor
    · intro impossible
      contradiction
    · intro applies
      exact (absent ⟨descriptor, applies⟩).elim

/-- Refusal of the specification analyzer is exactly absence of any semantic policy witness. -/
theorem aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?_eq_none_iff
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (component : source.AromaticCanonicalCyclicCumuleneComponent) :
    source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor? policy component = none ↔
      ¬∃ descriptor, policy component descriptor := by
  classical
  unfold aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?
  split <;> simp_all

/-- A descriptor-bearing cyclic-policy result retains the physical component identity. -/
structure AromaticCanonicalFullyCyclicCumulenePolicyAssignment
    (source : AuthoritativeChemicalInput) (PolicyDescriptor : Type*) where
  component : source.AromaticCanonicalCyclicCumuleneComponent
  descriptor : PolicyDescriptor
  deriving DecidableEq

/-- Public result obtained by resolving the old P-31 boundary through an independent policy.
Prior descriptor-bearing families are unchanged.  A fully cyclic component has exactly one of two
constructor-disjoint outcomes: an honest no-policy boundary or a policy descriptor. -/
inductive AromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy
    (source : AuthoritativeChemicalInput) (PolicyDescriptor : Type*) where
  | prior : source.AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes →
      source.AromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy PolicyDescriptor
  | fullyCyclicCumuleneBoundary : source.AromaticCanonicalCyclicCumuleneComponent →
      source.AromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy PolicyDescriptor
  | fullyCyclicCumuleneDescriptor :
      source.AromaticCanonicalFullyCyclicCumulenePolicyAssignment PolicyDescriptor →
      source.AromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy PolicyDescriptor
  deriving DecidableEq

/-- Resolve one perceived cyclic component by the independent semantic policy. -/
noncomputable def resolveAromaticCanonicalFullyCyclicCumulenePolicy
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (component : source.AromaticCanonicalCyclicCumuleneComponent) :
    source.AromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy PolicyDescriptor :=
  match source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor? policy component with
  | none => .fullyCyclicCumuleneBoundary component
  | some descriptor => .fullyCyclicCumuleneDescriptor { component, descriptor }

/-- Descriptor resolution is exact for each independently perceived component. -/
theorem resolveAromaticCanonicalFullyCyclicCumulenePolicy_eq_descriptor_iff
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (functional :
      source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicyFunctional policy)
    (component : source.AromaticCanonicalCyclicCumuleneComponent)
    (derived : source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component)
    (descriptor : PolicyDescriptor) :
    source.resolveAromaticCanonicalFullyCyclicCumulenePolicy policy component =
        .fullyCyclicCumuleneDescriptor { component, descriptor } ↔
      policy component descriptor := by
  classical
  unfold resolveAromaticCanonicalFullyCyclicCumulenePolicy
  cases selected : source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?
      policy component with
  | none =>
      constructor
      · intro impossible
        contradiction
      · intro applies
        have :=
          (source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?_eq_some_iff
            policy functional component derived descriptor).mpr applies
        rw [selected] at this
        contradiction
  | some selectedDescriptor =>
      have selectedApplies :=
        (source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?_eq_some_iff
          policy functional component derived selectedDescriptor).mp selected
      constructor
      · intro equal
        have descriptorIdentity : selectedDescriptor = descriptor := by
          cases equal
          rfl
        rwa [← descriptorIdentity]
      · intro applies
        have descriptorIdentity : selectedDescriptor = descriptor :=
          functional component derived selectedDescriptor descriptor selectedApplies applies
        subst descriptorIdentity
        rfl

/-- Boundary resolution is exact: it occurs precisely when the independent relation has no
descriptor witness. -/
theorem resolveAromaticCanonicalFullyCyclicCumulenePolicy_eq_boundary_iff
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (component : source.AromaticCanonicalCyclicCumuleneComponent) :
    source.resolveAromaticCanonicalFullyCyclicCumulenePolicy policy component =
        .fullyCyclicCumuleneBoundary component ↔
      ¬∃ descriptor, policy component descriptor := by
  classical
  constructor
  · intro resolved
    have selectedNone :
        source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor? policy component = none := by
      cases selected : source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?
          policy component with
      | none => rfl
      | some descriptor =>
          simp [resolveAromaticCanonicalFullyCyclicCumulenePolicy, selected] at resolved
    exact
      (source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?_eq_none_iff
        policy component).mp selectedNone
  · intro absent
    have selectedNone :=
      (source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?_eq_none_iff
        policy component).mpr absent
    simp [resolveAromaticCanonicalFullyCyclicCumulenePolicy, selectedNone]

/-- Transport one old five-branch result.  The four descriptor families are definitionally
unchanged; the P-31 record alone is resolved into one of the two policy outcomes. -/
noncomputable def transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor) :
    source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes →
      source.AromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy PolicyDescriptor
  | .prior prior => .prior prior
  | .fullyCyclicCumuleneParent component =>
      source.resolveAromaticCanonicalFullyCyclicCumulenePolicy policy component

/-- Forgetting policy resolution recovers the old public result. -/
def forgetAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*} :
    source.AromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy PolicyDescriptor →
      source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes
  | .prior prior => .prior prior
  | .fullyCyclicCumuleneBoundary component => .fullyCyclicCumuleneParent component
  | .fullyCyclicCumuleneDescriptor assignment =>
      .fullyCyclicCumuleneParent assignment.component

/-- Forgetting is a left inverse of policy transport. -/
theorem forget_transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (result : source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes) :
    source.forgetAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy
      (source.transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy
        policy result) = result := by
  classical
  cases result with
  | prior prior => rfl
  | fullyCyclicCumuleneParent component =>
      cases selected : source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?
          policy component with
      | none =>
          simp [transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy,
            resolveAromaticCanonicalFullyCyclicCumulenePolicy, selected,
            forgetAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy]
      | some descriptor =>
          simp [transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy,
            resolveAromaticCanonicalFullyCyclicCumulenePolicy, selected,
            forgetAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy]

/-- Policy resolution never merges two old public results because every cyclic outcome retains
its canonical component. -/
theorem transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy_injective
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor) :
    Function.Injective
      (source.transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy policy) := by
  exact Function.LeftInverse.injective
    (source.forget_transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy policy)

/-- Equality with a descriptor outcome retains the source component identity. -/
theorem resolveAromaticCanonicalFullyCyclicCumulenePolicy_descriptor_component
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (oldComponent component : source.AromaticCanonicalCyclicCumuleneComponent)
    (descriptor : PolicyDescriptor)
    (equal : source.resolveAromaticCanonicalFullyCyclicCumulenePolicy policy oldComponent =
      .fullyCyclicCumuleneDescriptor { component, descriptor }) :
    oldComponent = component := by
  classical
  unfold resolveAromaticCanonicalFullyCyclicCumulenePolicy at equal
  split at equal
  · contradiction
  · cases equal
    rfl

/-- Equality with a boundary outcome retains the source component identity. -/
theorem resolveAromaticCanonicalFullyCyclicCumulenePolicy_boundary_component
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (oldComponent component : source.AromaticCanonicalCyclicCumuleneComponent)
    (equal : source.resolveAromaticCanonicalFullyCyclicCumulenePolicy policy oldComponent =
      .fullyCyclicCumuleneBoundary component) :
    oldComponent = component := by
  classical
  unfold resolveAromaticCanonicalFullyCyclicCumulenePolicy at equal
  split at equal
  · cases equal
    rfl
  · contradiction

/-- Policy-resolved public analysis is exactly an injective map of the existing five-branch
analysis. -/
noncomputable def analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat) :
    List (source.AromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy
      PolicyDescriptor) :=
  (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
    carrierFuel ruleFuel).map
      (source.transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy policy)

/-- Exact descriptor membership in the public list. -/
theorem mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_descriptor_iff
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (functional :
      source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicyFunctional policy)
    (carrierFuel ruleFuel : Nat)
    (component : source.AromaticCanonicalCyclicCumuleneComponent)
    (descriptor : PolicyDescriptor) :
    (.fullyCyclicCumuleneDescriptor { component, descriptor } :
        source.AromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy PolicyDescriptor) ∈
        source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
          policy carrierFuel ruleFuel ↔
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component ∧
        policy component descriptor := by
  classical
  rw [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy, List.mem_map]
  constructor
  · rintro ⟨old, oldPresent, transported⟩
    cases old with
    | prior prior =>
        simp [transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy] at transported
    | fullyCyclicCumuleneParent oldComponent =>
        have oldDerived :=
          (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes_iff
            carrierFuel ruleFuel (.fullyCyclicCumuleneParent oldComponent)).mp oldPresent
        have componentIdentity : oldComponent = component :=
          source.resolveAromaticCanonicalFullyCyclicCumulenePolicy_descriptor_component
            policy oldComponent component descriptor (by
              simpa [transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy]
                using transported)
        subst oldComponent
        have oldApplies :=
          (source.resolveAromaticCanonicalFullyCyclicCumulenePolicy_eq_descriptor_iff
            policy functional component oldDerived descriptor).mp (by
              simpa [transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy]
                using transported)
        exact ⟨oldDerived, oldApplies⟩
  · rintro ⟨derived, applies⟩
    refine ⟨.fullyCyclicCumuleneParent component, ?_, ?_⟩
    · exact
        (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes_iff
          carrierFuel ruleFuel (.fullyCyclicCumuleneParent component)).mpr derived
    · simpa [transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy] using
        (source.resolveAromaticCanonicalFullyCyclicCumulenePolicy_eq_descriptor_iff
          policy functional component derived descriptor).mpr applies

/-- Exact boundary membership in the public list. -/
theorem mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_boundary_iff
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat)
    (component : source.AromaticCanonicalCyclicCumuleneComponent) :
    (.fullyCyclicCumuleneBoundary component :
        source.AromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy PolicyDescriptor) ∈
        source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
          policy carrierFuel ruleFuel ↔
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component ∧
        ¬∃ descriptor, policy component descriptor := by
  classical
  rw [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy, List.mem_map]
  constructor
  · rintro ⟨old, oldPresent, transported⟩
    cases old with
    | prior prior =>
        simp [transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy] at transported
    | fullyCyclicCumuleneParent oldComponent =>
        have oldDerived :=
          (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes_iff
            carrierFuel ruleFuel (.fullyCyclicCumuleneParent oldComponent)).mp oldPresent
        have componentIdentity : oldComponent = component :=
          source.resolveAromaticCanonicalFullyCyclicCumulenePolicy_boundary_component
            policy oldComponent component (by
              simpa [transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy]
                using transported)
        subst oldComponent
        have noPolicy :=
          (source.resolveAromaticCanonicalFullyCyclicCumulenePolicy_eq_boundary_iff
            policy component).mp (by
              simpa [transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy]
                using transported)
        exact ⟨oldDerived, noPolicy⟩
  · rintro ⟨derived, noPolicy⟩
    refine ⟨.fullyCyclicCumuleneParent component, ?_, ?_⟩
    · exact
        (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes_iff
          carrierFuel ruleFuel (.fullyCyclicCumuleneParent component)).mpr derived
    · simpa [transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy] using
        (source.resolveAromaticCanonicalFullyCyclicCumulenePolicy_eq_boundary_iff
          policy component).mpr noPolicy

/-- Component eligibility is equivalent to existence of a public descriptor emission for that
same physical component. -/
theorem exists_mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_descriptor_iff_eligible
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (functional :
      source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicyFunctional policy)
    (carrierFuel ruleFuel : Nat)
    (component : source.AromaticCanonicalCyclicCumuleneComponent) :
    (∃ descriptor,
      (.fullyCyclicCumuleneDescriptor { component, descriptor } :
        source.AromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy PolicyDescriptor) ∈
        source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
          policy carrierFuel ruleFuel) ↔
      source.DeclarativeAromaticCanonicalFullyCyclicCumuleneDescriptorEligible
        policy component := by
  simp only [DeclarativeAromaticCanonicalFullyCyclicCumuleneDescriptorEligible,
    source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_descriptor_iff
      policy functional carrierFuel ruleFuel component]
  aesop

/-- Every eligible policy assignment occurs literally once in the public list. -/
theorem count_fullyCyclicCumuleneDescriptor_in_analyzeWithCyclicPolicy_eq_one
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    [DecidableEq PolicyDescriptor]
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (functional :
      source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicyFunctional policy)
    (carrierFuel ruleFuel : Nat)
    (component : source.AromaticCanonicalCyclicCumuleneComponent)
    (derived : source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component)
    (descriptor : PolicyDescriptor)
    (applies : policy component descriptor) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
      policy carrierFuel ruleFuel).count
        (.fullyCyclicCumuleneDescriptor { component, descriptor }) = 1 := by
  rw [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy]
  have resolved :=
    (source.resolveAromaticCanonicalFullyCyclicCumulenePolicy_eq_descriptor_iff
      policy functional component derived descriptor).mpr applies
  have transportedResolved :
      source.transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy policy
          (.fullyCyclicCumuleneParent component) =
        .fullyCyclicCumuleneDescriptor { component, descriptor } := by
    simpa [transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy] using resolved
  rw [← transportedResolved]
  rw [List.count_map_of_injective _ _
    (source.transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy_injective
      policy)]
  exact
    source.count_fullyCyclicCumuleneParent_in_analyzeAromaticCanonicalConcreteStereochemistry_eq_one
      carrierFuel ruleFuel component derived

/-- Every perceived component to which the independent policy assigns no descriptor retains its
boundary record literally once. -/
theorem count_fullyCyclicCumuleneBoundary_in_analyzeWithCyclicPolicy_eq_one
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    [DecidableEq PolicyDescriptor]
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat)
    (component : source.AromaticCanonicalCyclicCumuleneComponent)
    (derived : source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component)
    (noPolicy : ¬∃ descriptor, policy component descriptor) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
      policy carrierFuel ruleFuel).count
        (.fullyCyclicCumuleneBoundary component) = 1 := by
  rw [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy]
  have resolved :=
    (source.resolveAromaticCanonicalFullyCyclicCumulenePolicy_eq_boundary_iff
      policy component).mpr noPolicy
  have transportedResolved :
      source.transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy policy
          (.fullyCyclicCumuleneParent component) =
        .fullyCyclicCumuleneBoundary component := by
    simpa [transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy] using resolved
  rw [← transportedResolved]
  rw [List.count_map_of_injective _ _
    (source.transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy_injective
      policy)]
  exact
    source.count_fullyCyclicCumuleneParent_in_analyzeAromaticCanonicalConcreteStereochemistry_eq_one
      carrierFuel ruleFuel component derived

/-- Strong public transport: the literal multiplicity of every old result is preserved at its
policy-resolved image, not only the multiplicity of cyclic components. -/
theorem count_transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    [DecidableEq PolicyDescriptor]
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
      policy carrierFuel ruleFuel).count
        (source.transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy
          policy result) =
      (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
        carrierFuel ruleFuel).count result := by
  rw [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy]
  exact List.count_map_of_injective _ _
    (source.transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy_injective
      policy) result

/-- Injective public transport preserves duplicate-freedom for arbitrary fuel and arbitrary
independent policies. -/
theorem analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_nodup
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    [DecidableEq PolicyDescriptor]
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
      policy carrierFuel ruleFuel).Nodup := by
  rw [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy]
  exact
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes_nodup
      carrierFuel ruleFuel).map
      (source.transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy_injective
        policy)

/-- Resolving the cyclic policy neither loses nor adds a public record. -/
theorem length_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_eq_prior
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
      policy carrierFuel ruleFuel).length =
      (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
        carrierFuel ruleFuel).length := by
  simp [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy]

/-- Any policy-resolved cyclic outcome retains the independently proved P-31 parent topology and
remains outside every P-93 open-terminal cumulene descriptor branch.  Thus the new semantic policy
is necessarily additional authority, never a disguised reuse of the inapplicable terminal rule. -/
theorem mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_cyclic_authority
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    [DecidableEq PolicyDescriptor]
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (functional :
      source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicyFunctional policy)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy
      PolicyDescriptor)
    (present : result ∈
      source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
        policy carrierFuel ruleFuel) :
    match result with
    | .prior _ => True
    | .fullyCyclicCumuleneBoundary component =>
        BlueBookP93.Cyclic.P31FullyCyclicCumuleneParentApplies .fullyCyclicCumulene ∧
          (∀ parity descriptor,
            ¬BlueBookP93.Cyclic.OpenTerminalCumuleneDescriptorApplies
              .fullyCyclicCumulene parity descriptor) ∧
          ¬∃ descriptor, policy component descriptor
    | .fullyCyclicCumuleneDescriptor assignment =>
        BlueBookP93.Cyclic.P31FullyCyclicCumuleneParentApplies .fullyCyclicCumulene ∧
          (∀ parity descriptor,
            ¬BlueBookP93.Cyclic.OpenTerminalCumuleneDescriptorApplies
              .fullyCyclicCumulene parity descriptor) ∧
          policy assignment.component assignment.descriptor := by
  cases result with
  | prior prior => trivial
  | fullyCyclicCumuleneBoundary component =>
      have exactMember :=
        (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_boundary_iff
          policy carrierFuel ruleFuel component).mp present
      exact ⟨BlueBookP93.Cyclic.fully_cyclic_cumulene_is_P31_parent_topology,
        fun parity descriptor =>
          BlueBookP93.Cyclic.fully_cyclic_cumulene_has_no_open_terminal_descriptor
            parity descriptor,
        exactMember.2⟩
  | fullyCyclicCumuleneDescriptor assignment =>
      have exactMember :=
        (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_descriptor_iff
          policy functional carrierFuel ruleFuel assignment.component assignment.descriptor).mp
          present
      exact ⟨BlueBookP93.Cyclic.fully_cyclic_cumulene_is_P31_parent_topology,
        fun parity descriptor =>
          BlueBookP93.Cyclic.fully_cyclic_cumulene_has_no_open_terminal_descriptor
            parity descriptor,
        exactMember.2⟩

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
