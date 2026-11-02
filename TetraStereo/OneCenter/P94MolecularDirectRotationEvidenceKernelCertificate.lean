import TetraStereo.OneCenter.P94MolecularDirectRotationEvidence
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
RED-first target for molecule-bound P-94 direct-rotation evidence.  A supplied state transition
must name an actual saturated single-bond record on the same valid six-ring carrier, bound both
states to complete molecule-sized coordinates, and remain sound after scheduling and unoriented
`DirectRotationStep` closure.
-/

assert_kernel_only
  BlueBookP94.P94MolecularDirectRotationEvidence.molecularDirectRotationAssertion_validFor_iff
assert_kernel_only
  BlueBookP94.P94MolecularDirectRotationEvidence.rotationAboutMolecularSingleBond_iff
assert_kernel_only
  BlueBookP94.P94MolecularDirectRotationEvidence.rotationAboutMolecularSingleBond_sound
assert_kernel_only
  BlueBookP94.P94MolecularDirectRotationEvidence.directRotationStep_aboutMolecularSingleBond_sound
assert_kernel_only
  BlueBookP94.P94MolecularDirectRotationEvidence.scheduledAuditedCoordinateTwistInput_rotation_sound

end TetraStereo.OneCenter
