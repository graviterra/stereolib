import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyReader
import TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedKey
import TetraStereo.OneCenter.LocalizedRuleMajorCompoundReadback
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyOrdinary

open CertifiedLocalizedCIPInput
open LocalizedMarkedRetainedStateReader (rawStateView)
open LocalizedMarkedRetainedPromotedKey (ordinaryKey?)
open LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyReader (dependencyReader_nil)

/-- The actual ordinary prefix on an empty auxiliary state has the uniform absent-label
reader at every stage. This removes every detection/dependency test before key inspection. -/
theorem ordinaryKey_nil (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (cursor : input.LocalizedRerootCursor fuel) :
    ordinaryKey? input target (rawStateView input [] target) cursor =
      input.buildRuleMajorCompoundRule45KeyWith?
        (fun stage position => input.buildRuleMajorCumulativeWithRead? stage
          (fun _ => none) (2 * (fuel + 1)) position) cursor := by
  unfold ordinaryKey?
  rw [input.buildActualRuleMajorCompoundRule45KeyExec?_eq,
    input.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
  simp only [dependencyReader_nil]

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyOrdinary

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyOrdinary.ordinaryKey_nil
