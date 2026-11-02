import TetraStereo.OneCenter.CIPRule3Through5FrameAffineInvariance
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Kernel-only certificate for joined Rules-1a--5 frame naturality

The closure covers transport of the common four-ligand cursor frame, transport of the assembled
canonical Rules-1a--5 key frame, and exact commutation of its two compiler passes under every
invertible rational affine coordinate change.
-/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedOccurrenceFourLigandFrame.mapSpatialPoints
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedOccurrenceRule3Through5KeyFrame.mapSpatialPoints
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedOccurrenceRule3Through5KeyFrame?_affine
