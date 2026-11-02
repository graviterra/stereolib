import TetraStereo.OneCenter.CIPAuthoritativeBranchDiscoveryTotality
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Kernel-only certificate for authoritative branch-discovery totality

This certificate checks the executable bridge from molecule-derived chemical applicability to a
complete width-unbounded canonical branch key.  In particular, successful sorting is derived from
complete child keys, and branch compilation is derived from finite generated-tree structure,
bonding-number-six, and exact uncapped Rule-1a support.
-/

assert_kernel_only TetraStereo.OneCenter.RawMolecule.compareCanonicalBranchKeys?_exists_of_complete
assert_kernel_only TetraStereo.OneCenter.RawMolecule.sortCanonicalKeys?_exists_of_all_complete
assert_kernel_only TetraStereo.OneCenter.RawMolecule.buildCanonicalBranchKeyAuthoritative_exists_complete_of_centerDescendant
assert_kernel_only TetraStereo.OneCenter.RawMolecule.branchCanonicalKeyAuthoritative?_exists_complete_of_chemical_applicability
