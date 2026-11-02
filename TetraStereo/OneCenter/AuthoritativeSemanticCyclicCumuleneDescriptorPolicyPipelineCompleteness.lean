import TetraStereo.OneCenter.AuthoritativeSemanticCyclicCumuleneDescriptorPolicyClosure

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Complete public specification for the cyclic-cumulene policy layer

The policy-closure module proves the two fully cyclic constructors exactly.  This module closes
the remaining public-list seam: it states one exhaustive executable membership relation for all
three result constructors, gives every emitted result its independent chemical meaning, and lifts
the represented-pipeline finite-bound completeness theorem through the injective policy
transport.
-/

/-- Exhaustive result-level specification for the policy-resolved public list.  The prior branch
retains the already proved four-family executable judgment.  The two cyclic branches are stated
only in terms of independently perceived topology and the independent descriptor policy. -/
def AromaticCanonicalConcreteStereochemicalWithCyclicPolicyExecutableMember
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy
      PolicyDescriptor) : Prop :=
  match result with
  | .prior prior =>
      source.AromaticCanonicalConcreteStereochemicalWithOpenCumulenesExecutableMember
        carrierFuel ruleFuel prior
  | .fullyCyclicCumuleneBoundary component =>
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component ∧
        ¬∃ descriptor, policy component descriptor
  | .fullyCyclicCumuleneDescriptor assignment =>
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponent assignment.component ∧
        policy assignment.component assignment.descriptor

/-- Exact preservation of the pre-existing four descriptor-bearing families by policy
transport. -/
theorem mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_prior_iff
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat)
    (prior : source.AromaticCanonicalConcreteStereochemicalAssignmentWithOpenCumulenes) :
    (.prior prior :
        source.AromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy PolicyDescriptor) ∈
        source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
          policy carrierFuel ruleFuel ↔
      source.AromaticCanonicalConcreteStereochemicalWithOpenCumulenesExecutableMember
        carrierFuel ruleFuel prior := by
  classical
  rw [analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy]
  constructor
  · intro present
    obtain ⟨old, oldPresent, transported⟩ := List.mem_map.mp present
    have oldIdentity : old =
        (AromaticCanonicalConcreteStereochemicalResultWithCyclicCumulenes.prior prior) := by
      apply source.transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy_injective
        policy
      simpa [transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy] using
        transported
    subst old
    exact
      (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes_iff
        carrierFuel ruleFuel (.prior prior)).mp oldPresent
  · intro executable
    apply List.mem_map.mpr
    refine ⟨.prior prior, ?_, ?_⟩
    · exact
        (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes_iff
          carrierFuel ruleFuel (.prior prior)).mpr executable
    · simp [transportAromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy]

/-- One flattened `iff` covers every constructor of the policy-resolved public result. -/
theorem mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_iff
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (functional :
      source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicyFunctional policy)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy
      PolicyDescriptor) :
    result ∈ source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
        policy carrierFuel ruleFuel ↔
      source.AromaticCanonicalConcreteStereochemicalWithCyclicPolicyExecutableMember
        policy carrierFuel ruleFuel result := by
  cases result with
  | prior prior =>
      exact source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_prior_iff
        policy carrierFuel ruleFuel prior
  | fullyCyclicCumuleneBoundary component =>
      exact source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_boundary_iff
        policy carrierFuel ruleFuel component
  | fullyCyclicCumuleneDescriptor assignment =>
      exact
        source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_descriptor_iff
          policy functional carrierFuel ruleFuel assignment.component assignment.descriptor

/-- Independent chemical meaning of every policy-resolved public result. -/
def DeclarativeAromaticCanonicalConcreteStereochemicalWithCyclicPolicyMember
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy
      PolicyDescriptor) : Prop :=
  match result with
  | .prior prior =>
      source.DeclarativeAromaticCanonicalConcreteStereochemicalWithOpenCumulenesMember
        carrierFuel ruleFuel prior
  | .fullyCyclicCumuleneBoundary component =>
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component ∧
        BlueBookP93.Cyclic.P31FullyCyclicCumuleneParentApplies .fullyCyclicCumulene ∧
        (∀ parity descriptor,
          ¬BlueBookP93.Cyclic.OpenTerminalCumuleneDescriptorApplies
            .fullyCyclicCumulene parity descriptor) ∧
        ¬∃ descriptor, policy component descriptor
  | .fullyCyclicCumuleneDescriptor assignment =>
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponent assignment.component ∧
        BlueBookP93.Cyclic.P31FullyCyclicCumuleneParentApplies .fullyCyclicCumulene ∧
        (∀ parity descriptor,
          ¬BlueBookP93.Cyclic.OpenTerminalCumuleneDescriptorApplies
            .fullyCyclicCumulene parity descriptor) ∧
        policy assignment.component assignment.descriptor

/-- Every public member has its pre-existing independent descriptor proof or the exact P-31,
open-terminal-exclusion, and policy proof appropriate to a fully cyclic component. -/
theorem analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_member_sound
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
    source.DeclarativeAromaticCanonicalConcreteStereochemicalWithCyclicPolicyMember
      policy carrierFuel ruleFuel result := by
  cases result with
  | prior prior =>
      have executable :=
        (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_prior_iff
          policy carrierFuel ruleFuel prior).mp present
      exact
        source.analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes_member_sound
          carrierFuel ruleFuel prior
          ((source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithOpenCumulenes_iff_executableMember
            carrierFuel ruleFuel prior).mpr executable)
  | fullyCyclicCumuleneBoundary component =>
      have authority :=
        source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_cyclic_authority
          policy functional carrierFuel ruleFuel (.fullyCyclicCumuleneBoundary component) present
      have derived :=
        (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_boundary_iff
          policy carrierFuel ruleFuel component).mp present
      exact ⟨derived.1, authority.1, authority.2.1, authority.2.2⟩
  | fullyCyclicCumuleneDescriptor assignment =>
      have authority :=
        source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_cyclic_authority
          policy functional carrierFuel ruleFuel (.fullyCyclicCumuleneDescriptor assignment)
            present
      have derived :=
        (source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_descriptor_iff
          policy functional carrierFuel ruleFuel assignment.component assignment.descriptor).mp
            present
      exact ⟨derived.1, authority.1, authority.2.1, authority.2.2⟩

/-- Every emitted result occurs literally once in the policy-resolved public list. -/
theorem every_mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_count_eq_one
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    [DecidableEq PolicyDescriptor]
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalConcreteStereochemicalResultWithCyclicPolicy
      PolicyDescriptor)
    (present : result ∈
      source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
        policy carrierFuel ruleFuel) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
      policy carrierFuel ruleFuel).count result = 1 := by
  exact List.count_eq_one_of_mem
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_nodup
      policy carrierFuel ruleFuel) present

/-- The policy transport preserves the represented-pipeline exact cardinality at the uniform
finite bound: every canonical physical unit still contributes exactly one public record. -/
theorem length_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_eq_units_at_bound
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel : Nat)
    (ready : source.AromaticCanonicalRepresentedPipelineReadyAtBound carrierFuel) :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
      policy carrierFuel (2 * (carrierFuel + 1))).length =
        source.aromaticCanonicalTetrahedralCenters.length +
          source.aromaticCanonicalIndividualDoubleBondCarriers.length +
          source.aromaticCanonicalOddOpenCumuleneUnits.length +
          source.aromaticCanonicalEvenOpenCumuleneUnits.length +
          source.aromaticCanonicalCyclicCumuleneComponents.length := by
  rw [source.length_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_eq_prior]
  exact
    source.length_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes_eq_units_at_bound
      carrierFuel ready

/-- Single end-to-end certificate for the policy-resolved represented pipeline. -/
structure AromaticCanonicalRepresentedPipelineWithCyclicPolicyCompleteAtBound
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel : Nat) : Prop where
  membershipExact : ∀ result,
    result ∈ source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
        policy carrierFuel (2 * (carrierFuel + 1)) ↔
      source.AromaticCanonicalConcreteStereochemicalWithCyclicPolicyExecutableMember
        policy carrierFuel (2 * (carrierFuel + 1)) result
  emittedSound : ∀ result,
    result ∈ source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
        policy carrierFuel (2 * (carrierFuel + 1)) →
      source.DeclarativeAromaticCanonicalConcreteStereochemicalWithCyclicPolicyMember
        policy carrierFuel (2 * (carrierFuel + 1)) result
  outputNodup :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
      policy carrierFuel (2 * (carrierFuel + 1))).Nodup
  lengthExact :
    (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy
      policy carrierFuel (2 * (carrierFuel + 1))).length =
        source.aromaticCanonicalTetrahedralCenters.length +
          source.aromaticCanonicalIndividualDoubleBondCarriers.length +
          source.aromaticCanonicalOddOpenCumuleneUnits.length +
          source.aromaticCanonicalEvenOpenCumuleneUnits.length +
          source.aromaticCanonicalCyclicCumuleneComponents.length

/-- Functional policy plus the existing four-family readiness theorem constructs the complete
policy-resolved public certificate. -/
theorem analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_complete_at_bound
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    [DecidableEq PolicyDescriptor]
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (functional :
      source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicyFunctional policy)
    (carrierFuel : Nat)
    (ready : source.AromaticCanonicalRepresentedPipelineReadyAtBound carrierFuel) :
    source.AromaticCanonicalRepresentedPipelineWithCyclicPolicyCompleteAtBound
      policy carrierFuel := by
  constructor
  · intro result
    exact source.mem_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_iff
      policy functional carrierFuel (2 * (carrierFuel + 1)) result
  · intro result present
    exact source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_member_sound
      policy functional carrierFuel (2 * (carrierFuel + 1)) result present
  · exact source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_nodup
      policy carrierFuel (2 * (carrierFuel + 1))
  · exact
      source.length_analyzeAromaticCanonicalConcreteStereochemistryWithCyclicPolicy_eq_units_at_bound
        policy carrierFuel ready

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
