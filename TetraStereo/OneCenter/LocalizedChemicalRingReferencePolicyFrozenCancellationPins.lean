import TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-! Actual scalar nonunique outcomes for every eligible near-cage promotion. Cancellation needs
all of these results; a failed first reference alone only suffices for consensus. These are
focused ranking-call pins, not recursive state evaluation or supplied auxiliary labels. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationPins

open LocalizedGenericMarkedRecalculation
open LocalizedHiddenParityMarkedProbe hiding frameAtoms?
open LocalizedHiddenParityPromotedReadback hiding rankedAtoms?
open LocalizedGenericMarkedRecalculationCage

theorem nearA6_nonunique :
    (marked? cageRaw 16 [] nearA 6).map (·.unique) = some false := by decide +kernel

theorem nearA7_nonunique :
    (marked? cageRaw 16 [] nearA 7).map (·.unique) = some false := by decide +kernel

theorem nearB12_nonunique :
    (marked? cageRaw 16 [] nearB 12).map (·.unique) = some false := by decide +kernel

theorem nearB13_nonunique :
    (marked? cageRaw 16 [] nearB 13).map (·.unique) = some false := by decide +kernel

/-- Exhaustive actual nonuniqueness; no eligible reference is inferred from another's result. -/
theorem nearA_all_nonunique (reference : Nat) (member : reference ∈ [5,6,7]) :
    (marked? cageRaw 16 [] nearA reference).map (·.unique) = some false := by
  have choices : reference = 5 ∨ reference = 6 ∨ reference = 7 := by simpa using member
  rcases choices with rfl | rfl | rfl
  · rw [marked_eq_tracked]
    change (tracked? nearA 5).map (·.unique) = some false
    rw [near_mark5_tracked_output]
    rfl
  · exact nearA6_nonunique
  · exact nearA7_nonunique

theorem nearB_all_nonunique (reference : Nat) (member : reference ∈ [11,12,13]) :
    (marked? cageRaw 16 [] nearB reference).map (·.unique) = some false := by
  have choices : reference = 11 ∨ reference = 12 ∨ reference = 13 := by simpa using member
  rcases choices with rfl | rfl | rfl
  · rw [marked_eq_tracked]
    change (tracked? nearB 11).map (·.unique) = some false
    rw [nearB_mark11_empty]
    rfl
  · exact nearB12_nonunique
  · exact nearB13_nonunique

theorem nearA_selected_list :
    eligibleOf [0,5,6,7] [1,2,3,0] [some .eq,some .eq,some .gt] = [5,6,7] := rfl

theorem nearB_selected_list :
    eligibleOf [0,11,12,13] [1,2,3,0] [some .eq,some .eq,some .gt] = [11,12,13] := rfl

end TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationPins

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationPins.nearA6_nonunique
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationPins.nearA7_nonunique
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationPins.nearB12_nonunique
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationPins.nearB13_nonunique
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationPins.nearA_all_nonunique
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationPins.nearB_all_nonunique
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationPins.nearA_selected_list
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationPins.nearB_selected_list
