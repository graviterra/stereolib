import TetraStereo.OneCenter.P93MolecularFullereneConfiguration
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Kernel-only certificate: molecule-bound P-93.5.6 fullerene configuration

RED-first target for replacing the opaque fullerene cage key by a canonical atom carrier and a
finite checked fullerene face map on the normalized molecular graph.  The same source-backed
judgment must characterize local admission, refusal, family membership, and every emitted
descriptor obligation.
-/

assert_kernel_only TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneConfigurationInput?_eq_some_iff
assert_kernel_only TetraStereo.OneCenter.BlueBookP93.Cyclic.molecularFullereneConfigurationInput?_eq_none_iff
assert_kernel_only TetraStereo.OneCenter.BlueBookP93.Cyclic.mem_validatedMolecularFullereneConfigurationInputs_iff
assert_kernel_only TetraStereo.OneCenter.BlueBookP93.Cyclic.mem_analyzeMolecularFullereneConfigurations_iff
assert_kernel_only TetraStereo.OneCenter.BlueBookP93.Cyclic.MolecularFullereneConfigurationAssignmentJudgment.requirements_exact
