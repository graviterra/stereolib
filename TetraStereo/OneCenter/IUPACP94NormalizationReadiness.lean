import TetraStereo.OneCenter.IUPACP94NormalizationReadinessCore
import TetraStereo.OneCenter.IUPACRemaining71P94AuthorityProductionAdapter

set_option autoImplicit false

/-!
# P-94 normalization readiness at the reviewed-policy boundary

The policy-free molecular iff lives upstream in `IUPACP94NormalizationReadinessCore`.  This file
states the exact remaining policy-level frontier without weakening the independently reviewed
P-94 domain: fixed normalization is total precisely when every valid observation satisfies that
policy-free readiness condition.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

theorem p94RemainingFixedNormalizationTotality_of_every_valid_ready
    (policy : P94AuthorityPolicy)
    (ready : ∀ (source : AuthoritativeChemicalInput)
      (observation : P94AuthorityObservation policy),
        observation.ValidFor policy source →
          observation.molecule.P94NormalizationReady) :
    P94RemainingFixedNormalizationTotality policy := by
  intro source observation valid
  exact
    RawMolecule.normalizeRawMoleculeCertified?_exists_parsed_eq_of_p94NormalizationReady
      observation.molecule (ready source observation valid)

theorem p94RemainingFixedNormalizationTotality_iff_every_valid_ready
    (policy : P94AuthorityPolicy) :
    P94RemainingFixedNormalizationTotality policy ↔
      ∀ (source : AuthoritativeChemicalInput)
        (observation : P94AuthorityObservation policy),
          observation.ValidFor policy source →
            observation.molecule.P94NormalizationReady := by
  constructor
  · intro totality source observation valid
    exact
      (RawMolecule.normalizeRawMoleculeCertified?_exists_parsed_eq_iff_p94NormalizationReady
        observation.molecule).mp (totality source observation valid)
  · exact p94RemainingFixedNormalizationTotality_of_every_valid_ready policy

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p94RemainingFixedNormalizationTotality_iff_every_valid_ready
