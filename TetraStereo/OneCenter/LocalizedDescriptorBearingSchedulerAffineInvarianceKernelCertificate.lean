import TetraStereo.OneCenter.LocalizedDescriptorBearingSchedulerAffineInvariance
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Kernel-only certificate for affine invariance of the production scheduler state. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDescriptorBearingRule3Through5SchedulerState_affine
