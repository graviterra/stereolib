import TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Empty generated auxiliary states have no dependency readings, irrespective of detection
and depth predicates. These identities remove their noncomputable decisions analytically. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyReader

open CertifiedLocalizedCIPInput
open LocalizedMarkedRetainedStateReader

 theorem rawStateView_nil (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) :
    rawStateView input [] target = fun _ _ => none := by
  funext source dependency
  simp [rawStateView, rawStateLabel?, rawStateFact?]

 theorem dependencyReader_nil (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) :
    input.localizedDependencyLabel target (rawStateView input [] target) = fun _ => none := by
  rw [rawStateView_nil]
  funext cursor
  simp [localizedDependencyLabel]

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyReader

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyReader.rawStateView_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyReader.dependencyReader_nil
