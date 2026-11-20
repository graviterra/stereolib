import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerSingleton
import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! At an actual detected frame, the guarded singleton joint comparator is exactly the
accepted scalar sparse comparator. The ordinary guard introduces no extra hypothesis. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactSingletonFrame

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedPromotedKey (ordinaryKey? compareAt?_preserves_ordinary)
open LocalizedMarkedRetainedSparsePromotedKey (sparseCompareAt?_eq)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseBefore)
open LocalizedChemicalRingJointMarkerOperations (jointBefore)
open LocalizedChemicalRingJointMarkerSingleton (compareJoint_singleton_eq_sparse)
open LocalizedMarkedRetainedPromotedRanking (slot_valid)
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)

noncomputable section

theorem jointBefore_singleton_eq_sparseBefore (input : CertifiedLocalizedCIPInput)
    (single : input.moleculeGraph.SimpleBonded) (state : OccurrenceAuxState)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (real : target.1.node.provenance = .realAtom) (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (reference : input.Atom) (W D : Nat) (left right : Fin 4) :
    jointBefore input state target
        (rawStateFrames input single state target real unit targetUnit).frame [reference] W D left right =
      sparseBefore input state target reference W D
        (rawStateFrames input single state target real unit targetUnit).frame left right := by
  let execution := rawStateFrames input single state target real unit targetUnit
  have full := execution.fullOrdering (rawStateDescriptorMap_tetrahedral input state)
    single unit targetUnit left right
  have ordinary := rawStateBefore_eq_keys input single state target real unit targetUnit left right
  change rawStateBefore input state target execution.frame left right =
    some (compare (execution.retainedKeys unit left) (execution.retainedKeys unit right)) at ordinary
  rw [← full] at ordinary
  have built (slot : Fin 4) : ordinaryKey? input target (rawStateView input state target)
      (execution.frame.cursorAt slot) = some (execution.compounds slot) := by
    unfold ordinaryKey?
    rw [rawStateView_eq_molecularView]
    exact execution.compoundBuilt slot
  unfold jointBefore sparseBefore
  rw [ordinary]
  change (if (input.compareLocalizedRerootCompoundThroughRule5
      (execution.compounds left) (execution.compounds right)).ordering = Ordering.eq then
    LocalizedChemicalRingJointMarkerKey.compareJointAt? input target (rawStateView input state target)
      [reference] W D (execution.frame.cursorAt left) (execution.frame.cursorAt right)
    else some (input.compareLocalizedRerootCompoundThroughRule5
      (execution.compounds left) (execution.compounds right)).ordering) =
    LocalizedMarkedRetainedSparsePromotedKey.sparseCompareAt? input target
      (rawStateView input state target) reference W D
      (execution.frame.cursorAt left) (execution.frame.cursorAt right)
  by_cases tied : (input.compareLocalizedRerootCompoundThroughRule5
      (execution.compounds left) (execution.compounds right)).ordering = Ordering.eq
  · rw [if_pos tied]
    exact compareJoint_singleton_eq_sparse input target (rawStateView input state target)
      reference W D _ _
  · rw [if_neg tied, sparseCompareAt?_eq]
    exact (compareAt?_preserves_ordinary input target (rawStateView input state target)
      reference W D _ _ (slot_valid input single state target real unit targetUnit left)
      (slot_valid input single state target real unit targetUnit right)
      (execution.compounds left) (execution.compounds right) (built left) (built right) tied).symm

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactSingletonFrame

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactSingletonFrame.jointBefore_singleton_eq_sparseBefore
