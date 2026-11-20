import TetraStereo.OneCenter.LocalizedChemicalRingPromotionAggregation
import TetraStereo.KernelOnly
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Four-slot cancellation without a supplied balance

If every selected slot resolves, and each has a distinct selected partner with the same
reading, a population of at most four distinct slots satisfies cancellation = consensus.
Two different readings must each occur twice. A molecular consumer derives the partner from
the original key tie and same-class even transport, and resolution from the actual promoted
keys. No prescribed reading list, key partition or signed-balance assumption occurs here.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingFourSlotPromotionBalance

open DeclarativeCIP.ProductionOccurrenceRules456
open LocalizedChemicalRingPromotionAggregation
open LocalizedChemicalRingSenseTransport (consensus_perm)
open LocalizedGenericMarkedRecalculation (consensus)

private instance rsFintype : Fintype RS where
  elems := {.R, .S}
  complete := by intro value; cases value <;> simp


set_option synthInstance.maxSize 512 in
/-- Finite four-slot algebra, with every possible selected subset and optional reading checked. -/
theorem filtered_resolved_partner_cancellation
    (selected : Fin 4 → Bool) (read : Fin 4 → Option RS)
    (resolved : ∀ i, selected i = true → read i ≠ none)
    (partner : ∀ i, selected i = true →
      ∃ j, selected j = true ∧ j ≠ i ∧ read j = read i) :
    completedAggregate (((List.finRange 4).filter selected).map read) =
      some (consensus (((List.finRange 4).filter selected).map read)) := by
  have finite : ∀ (s : Fin 4 → Bool) (r : Fin 4 → Option RS),
      (∀ i, s i = true → r i ≠ none) →
      (∀ i, s i = true → ∃ j, s j = true ∧ j ≠ i ∧ r j = r i) →
      completedAggregate (((List.finRange 4).filter s).map r) =
        some (consensus (((List.finRange 4).filter s).map r)) := by
    decide +kernel
  exact finite selected read resolved partner

/-- Completed cancellation is insensitive to ordering, but keeps all multiplicities. -/
theorem completedAggregate_perm {a b : List (Option RS)} (permutation : a.Perm b) :
    completedAggregate a = completedAggregate b := by
  simp only [completedAggregate, promotionAggregate, completed_balance]
  rw [readingBalance_perm permutation]

/-- The executable selected list may have any order. Distinct slots, resolved readings and
same-reading partners suffice; no equality between different key classes is needed. -/
theorem resolved_partner_cancellation (selected : List (Fin 4)) (read : Fin 4 → Option RS)
    (unique : selected.Nodup)
    (resolved : ∀ i ∈ selected, read i ≠ none)
    (partner : ∀ i ∈ selected, ∃ j ∈ selected, j ≠ i ∧ read j = read i) :
    completedAggregate (selected.map read) = some (consensus (selected.map read)) := by
  let mask : Fin 4 → Bool := fun i => decide (i ∈ selected)
  have mask_iff (i : Fin 4) : mask i = true ↔ i ∈ selected := by simp [mask]
  have permutation : selected.Perm ((List.finRange 4).filter mask) := by
    apply (List.perm_ext_iff_of_nodup unique ((List.nodup_finRange 4).filter mask)).mpr
    intro i
    simp [List.mem_filter, mask_iff]
  have result := filtered_resolved_partner_cancellation mask read
    (fun i hi => resolved i ((mask_iff i).mp hi))
    (by
      intro i hi
      obtain ⟨j, member, different, same⟩ := partner i ((mask_iff i).mp hi)
      exact ⟨j, (mask_iff j).mpr member, different, same⟩)
  rw [← completedAggregate_perm (permutation.map read),
    ← consensus_perm (permutation.map read)] at result
  exact result

end TetraStereo.OneCenter.LocalizedChemicalRingFourSlotPromotionBalance

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFourSlotPromotionBalance.filtered_resolved_partner_cancellation
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFourSlotPromotionBalance.completedAggregate_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFourSlotPromotionBalance.resolved_partner_cancellation
