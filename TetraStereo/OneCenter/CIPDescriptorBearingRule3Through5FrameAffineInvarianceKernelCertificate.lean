import TetraStereo.OneCenter.CIPDescriptorBearingRule3Through5FrameAffineInvariance
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Kernel-only certificate for the production descriptor-bearing Rules-1a--5 key frame. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?_affine
