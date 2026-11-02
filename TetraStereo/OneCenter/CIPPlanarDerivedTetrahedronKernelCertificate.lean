import TetraStereo.OneCenter.CIPPlanarDerivedTetrahedronConformance
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Kernel-only certificate for planar derived-tetrahedron geometry

This certificate starts only after the chemical roles `a>b>y>z` have been independently
established.  It certifies the exact P-92 geometric/family conversion, not upstream planar-unit
perception.
-/

assert_kernel_only TetraStereo.OneCenter.planarDescriptorOfDerivedTetrahedron?_via_tetrahedral_chirality
assert_kernel_only TetraStereo.OneCenter.planarDescriptorOfDerivedTetrahedron?_eq_some_iff
assert_kernel_only TetraStereo.OneCenter.planarDescriptorOfDerivedTetrahedron?_eq_none_iff
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.orientedVolume_swap_first_second
assert_kernel_only TetraStereo.OneCenter.planarDerivedTetrahedron_rationalDescriptor_swap_ab
assert_kernel_only TetraStereo.OneCenter.planarDescriptorOfDerivedTetrahedron?_swap_ab
