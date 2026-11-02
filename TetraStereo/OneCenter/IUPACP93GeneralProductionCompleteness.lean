import TetraStereo.OneCenter.IUPACRemaining71P93GeneralReviewedSemantics

set_option autoImplicit false

/-!
# Closed production semantics for all five general P-93 provisions

The producer validates source-bound physical units, citations, mirror actions, scope plans,
mixture arithmetic, and whole-configuration authority directly.  The family theorem relates that
explicit program to the independent P-93.1 reference without invoking a reviewed `Judges` field.

Whole-configuration authorization is appended explicitly at the end of the affected production
cores.  The definitions below spell out the production checks themselves; they are not aliases for
the reference `Judges` predicates.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open BlueBookP93

def P93GeneralConfigurationSourceCore
    (policy : P93GeneralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (configuration : P93GeneralAuthorityConfiguration policy) : Prop :=
  P93AuthorityConfiguration.InputFaithful source policy.physicalObservation
      (policy.CitationAuthorized source) configuration ∧
    ∀ assignment ∈ configuration.assignments,
      policy.DescriptorAuthorized source assignment.unit assignment.descriptor

def P93GeneralCanonicalRepresentativeCore
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

def P93GeneralMixedScopeProductionCore
    (policy : P93GeneralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MixedAbsoluteRelativeAuthorityObservation policy) : Prop :=
  P93GeneralConfigurationSourceCore policy source observation.configuration ∧
    observation.plan.assignments.map (fun assignment => assignment.located) =
      observation.configuration.assignments ∧
    observation.plan.MixedAbsoluteRelative ∧
    P93MixedRelativeGroupsNontrivial observation.plan ∧
    observation.observedTypography = observation.plan.assignments.map (fun assignment =>
      (assignment.located.citation, P93GeneralMixedTypography assignment)) ∧
    policy.ConfigurationAuthorized source observation.configuration

def P93GeneralRacemateProductionCore
    (policy : P93GeneralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (mixture : GeneralConfiguration.BinaryMixture
      (P93GeneralAuthorityConfiguration policy)) : Prop :=
  P93GeneralConfigurationSourceCore policy source mixture.first ∧
    P93GeneralCanonicalRepresentativeCore policy mixture.first ∧
    ((mixture.Valid ∧
      mixture.second = mixture.first.globallyMirrored policy.mirrorAction ∧
      mixture.first ≠ mixture.second ∧
      mixture.firstFraction = (1 : ℚ) / 2) ∧
      (policy.ConfigurationAuthorized source mixture.first ∧
        policy.ConfigurationAuthorized source mixture.second))

def P93GeneralAmboProductionCore
    (policy : P93GeneralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93AmboAuthorityObservation policy) : Prop :=
  P93GeneralConfigurationSourceCore policy source observation.mixture.first ∧
    ((observation.mixture.composition = .nonEquimolar ∧
      (∃ assignment ∈ observation.mixture.first.assignments,
        assignment.citation = observation.citation ∧
          policy.localAction.mirror assignment.descriptor ≠ assignment.descriptor) ∧
      observation.mixture.second =
        p93GeneralConfigurationInvertedAtCitation policy observation.citation
          observation.mixture.first ∧
      ¬P93AuthorityConfiguration.RelativeEquivalent policy.mirrorAction
        observation.mixture.first observation.mixture.second ∧
      observation.mixture.first ≠ observation.mixture.second) ∧
      (policy.ConfigurationAuthorized source observation.mixture.first ∧
        policy.ConfigurationAuthorized source observation.mixture.second))

namespace Remaining71P93GeneralAuthorityRow

def ProductionJudges
    (policy : P93GeneralAuthorityPolicy) :
    (row : Remaining71P93GeneralAuthorityRow) →
      AuthoritativeChemicalInput → (row.reference policy).Observation → Prop
  | .absoluteConfiguration, source, observation =>
      P93GeneralConfigurationSourceCore policy source observation.configuration ∧
        policy.ConfigurationAuthorized source observation.configuration
  | .relativeConfiguration, source, observation =>
      P93GeneralConfigurationSourceCore policy source observation.first ∧
        P93GeneralCanonicalRepresentativeCore policy observation.first ∧
        (P93AuthorityConfiguration.RelativeEquivalent policy.mirrorAction
            observation.first observation.second ∧
          (policy.ConfigurationAuthorized source observation.first ∧
            policy.ConfigurationAuthorized source observation.second))
  | .mixedAbsoluteRelativeConfiguration, source, observation =>
      P93GeneralMixedScopeProductionCore policy source observation
  | .racemates, source, observation =>
      P93GeneralRacemateProductionCore policy source observation
  | .ambo, source, observation =>
      P93GeneralAmboProductionCore policy source observation

theorem production_eq_reference
    (policy : P93GeneralAuthorityPolicy)
    (row : Remaining71P93GeneralAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation) :
    row.ProductionJudges policy source observation ↔
      (row.reference policy).Judges source observation := by
  cases row <;>
    rfl

theorem reference_applicable_of_judged
    (policy : P93GeneralAuthorityPolicy)
    (row : Remaining71P93GeneralAuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation)
    (judged : (row.reference policy).Judges source observation) :
    (row.reference policy).Applicable source := by
  cases row with
  | absoluteConfiguration => exact ⟨observation.configuration, judged.1⟩
  | relativeConfiguration => exact ⟨observation.first, judged.1⟩
  | mixedAbsoluteRelativeConfiguration => exact ⟨observation.configuration, judged.1⟩
  | racemates => exact ⟨observation.first, judged.1⟩
  | ambo => exact ⟨observation.mixture.first, judged.1⟩

end Remaining71P93GeneralAuthorityRow
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93GeneralAuthorityRow.production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93GeneralAuthorityRow.reference_applicable_of_judged
