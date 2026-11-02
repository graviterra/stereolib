import TetraStereo.OneCenter.P94MolecularAuditedTwistOutcomeSoundness
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
RED-first target for accepted final twist provenance.  Every bounded direct step and every edge of
both ordered legs in an accepted audited hybrid twist outcome must transport to the molecule-bound
single-bond soundness relation.
-/

assert_kernel_only
  BlueBookP94.P94MolecularAuditedTwistOutcomeSoundness.scheduledAuditedCoordinateTwistInput_boundedDirectRotationStep_sound
assert_kernel_only
  BlueBookP94.P94MolecularAuditedTwistOutcomeSoundness.scheduledAuditedCoordinateTwistInput_directedRotationPath_sound
assert_kernel_only
  BlueBookP94.P94MolecularAuditedTwistOutcomeSoundness.auditedHybridTwistAccepted_paths_sound

end TetraStereo.OneCenter
