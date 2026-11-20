import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPriorTie
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootSelection
import TetraStereo.OneCenter.LocalizedChemicalRingRuleMajorLabelCoherence
import TetraStereo.OneCenter.LocalizedChemicalRingRuleMajorSingletonReadback
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The actual oxygen comparison is decided by the nearest chiral observations. Physical
mirror transport supplies the prior tie; no complete key is reduced to prove this result. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrderPin

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier (input)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame (target frame)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice (reader)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootData
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootSelection
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefix
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootPriorTie (compound_prior_tie)
open LocalizedMarkedRetainedStateReader (rawStateView rawStateView_eq_molecularView)
open LocalizedMarkedRetainedPromotedKey (ordinaryKey?)

abbrev twoFacts := LocalizedChemicalRingJointPreparedDoubleC3ExactRootFacts.twoFacts

noncomputable section

abbrev compound := (execution twoFacts).compounds

theorem compound_built (i : Fin 4) :
    input.buildRuleMajorCompoundRule45KeyWith? compiler (frame.cursorAt i) = some (compound i) := by
  have actual : ordinaryKey? input data.target (rawStateView input twoFacts data.target)
      ((execution twoFacts).frame.cursorAt i) = some (compound i) := by
    unfold ordinaryKey?
    rw [rawStateView_eq_molecularView]
    exact (execution twoFacts).compoundBuilt i
  rw [execution_frame, data_target] at actual
  change LocalizedChemicalRingJointPreparedDoubleC3ExactRootReader.prior twoFacts
    (frame.cursorAt i) = some (compound i)
  rw [LocalizedChemicalRingJointPreparedDoubleC3ExactRootReader.prior_eq,
    LocalizedChemicalRingCachedOperations.compound_eq]
  exact actual

theorem commonR_gt : input.compareLocalizedRerootCompoundRule5Readings .R
    (compound 2).rule5Readings (compound 3).rule5Readings = .gt := by
  have builtL := compound_built 2
  have builtR := compound_built 3
  have aL := (input.buildRuleMajorCompoundRule45KeyWith?_readback compiler
    (frame.cursorAt 2) builtL).1
  have aR := (input.buildRuleMajorCompoundRule45KeyWith?_readback compiler
    (frame.cursorAt 3) builtR).1
  obtain ⟨left, leftList, _, leftR, _⟩ :=
    input.buildRuleMajorCompoundRule45KeyWith?_singleton_readback compiler
      (frame.cursorAt 2) (compound 2) .R builtL (oxygen4_references _ aL)
  obtain ⟨right, rightList, _, rightR, _⟩ :=
    input.buildRuleMajorCompoundRule45KeyWith?_singleton_readback compiler
      (frame.cursorAt 3) (compound 3) .S builtR (oxygen15_references _ aR)
  change LocalizedChemicalRingCachedOperations.cumulative input reader (.rule5 .R .R)
    read 54 (frame.cursorAt 2) = some left.commonR at leftR
  change LocalizedChemicalRingCachedOperations.cumulative input reader (.rule5 .S .R)
    read 54 (frame.cursorAt 3) = some right.commonR at rightR
  have comparison := commonR_descriptor_gt left.commonR right.commonR
    (oxygen4_prefix _ _ leftR) (oxygen15_prefix _ _ rightR)
    (LocalizedChemicalRingCachedOperations.cumulative_descriptor_eq_labels_projection
      input reader _ read 54 _ _ leftR)
    (LocalizedChemicalRingCachedOperations.cumulative_descriptor_eq_labels_projection
      input reader _ read 54 _ _ rightR)
  rw [leftList, rightList]
  simpa only [compareLocalizedRerootCompoundRule5Readings, List.compareLex_cons_cons,
    Ordering.byKey, localizedRerootRule5Descriptor, comparison] using
    (show Ordering.gt.then .eq = .gt from rfl)

theorem compound_order_gt :
    (input.compareLocalizedRerootCompoundThroughRule5 (compound 2) (compound 3)).ordering = .gt := by
  simp only [compareLocalizedRerootCompoundThroughRule5, compound_prior_tie, commonR_gt]
  rfl

def rootOComparison : Option Ordering :=
  LocalizedChemicalRingJointPreparedDoubleC3ExactRootReader.before twoFacts 2 3

theorem root_O_before : rootOComparison = some .gt := by
  unfold rootOComparison LocalizedChemicalRingJointPreparedDoubleC3ExactRootReader.before
  change (do
    let left ← input.buildRuleMajorCompoundRule45KeyWith? compiler (frame.cursorAt 2)
    let right ← input.buildRuleMajorCompoundRule45KeyWith? compiler (frame.cursorAt 3)
    some (localizedOccurrenceRule45ComparisonRecord
      (input.compareLocalizedRerootCompoundThroughRule5 left right))).map
        ConstitutionalDescriptorHierarchyComparison.ordering = some .gt
  rw [compound_built, compound_built]
  change some (input.compareLocalizedRerootCompoundThroughRule5 (compound 2) (compound 3)).ordering = _
  rw [compound_order_gt]

theorem actual_root_O_before :
    LocalizedMarkedRetainedOrdinaryRanking.rawStateBefore input twoFacts target frame 2 3 =
      some .gt := by
  rw [← LocalizedChemicalRingCachedOperations.before_eq input reader twoFacts target frame]
  exact (LocalizedChemicalRingJointPreparedDoubleC3ExactRootReader.before_eq twoFacts 2 3).symm.trans
    root_O_before

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrderPin

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrderPin.compound_built
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrderPin.commonR_gt
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrderPin.compound_order_gt
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrderPin.root_O_before
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrderPin.actual_root_O_before
