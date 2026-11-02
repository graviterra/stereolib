import TetraStereo.OneCenter.LocalizedDescriptorBearingFixedPointAffineInvariance
import TetraStereo.OneCenter.LocalizedEvenCumuleneAxialAnalysis

/-!
# Affine invariance of the production descriptor scheduler state

This is the executable fixed-point boundary.  The actual state decoded from the causal scheduler
for an affinely mapped molecule equals the occurrence-wise transport of the scheduler state for
the source molecule.  The proof uses the certified-model theorem for each scheduler result and
the separately proved uniqueness/transport theorem; it does not rely on scheduler enumeration.
-/

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- The complete production Rules-1a--5 auxiliary state is invariant under every exact rational
orientation-preserving affine coordinate change, modulo the canonical occurrence transport. -/
theorem localizedDescriptorBearingRule3Through5SchedulerState_affine
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (transform : RationalAffineFrameTransform)
    (orientationPreserving : 0 < transform.determinant) :
    (input.mapSpatialPoints transform.applyPoint
      |>.localizedDescriptorBearingRule3Through5SchedulerState fuel) =
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel).mapSpatialPoints
        transform.applyPoint := by
  let sourceState := input.localizedDescriptorBearingRule3Through5SchedulerState fuel
  let mappedInput := input.mapSpatialPoints transform.applyPoint
  let mappedState := mappedInput.localizedDescriptorBearingRule3Through5SchedulerState fuel
  exact input.uniqueLocalizedOccurrenceDescriptorBearingRule3Through5Model_affine
    sourceState
    (input.localizedDescriptorBearingRule3Through5SchedulerState_cipModel fuel)
    transform mappedState
    (mappedInput.localizedDescriptorBearingRule3Through5SchedulerState_cipModel fuel)
    orientationPreserving

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
