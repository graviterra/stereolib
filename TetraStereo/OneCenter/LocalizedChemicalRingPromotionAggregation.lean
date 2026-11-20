import TetraStereo.OneCenter.Rule6Proposed2018PromotionFidelity
import TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Adapter for completed molecular promotion readings and proposed-2018 cancellation.
An absent reading here means a completed nonunique promotion, not an operational failure.
Molecular consumers must prove that interpretation using their actual frame, total comparison
and calibrated geometry theorems. This module only supplies the finite aggregation algebra;
the physical selected-population covariance is a separate obligation.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingPromotionAggregation

open DeclarativeCIP.ProductionOccurrenceRules456
open LocalizedGenericMarkedRecalculation (consensus)
open LocalizedChemicalRingSenseTransport (consensus_eq_some_iff)

/-- Interpret an already completed optional reading; do not use for an operational failure. -/
def completedOutcome : Option RS → PromotionOutcome
  | none => .unresolved
  | some descriptor => .descriptor descriptor

def readingScore : Option RS → Int
  | none => 0
  | some .R => 1
  | some .S => -1

def readingBalance (readings : List (Option RS)) : Int := (readings.map readingScore).sum

def completedAggregate (readings : List (Option RS)) : Option (Option RS) :=
  promotionAggregate (readings.map completedOutcome)

theorem completed_balance (readings : List (Option RS)) :
    promotionBalance (readings.map completedOutcome) = some (readingBalance readings) := by
  induction readings with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | none => simpa [completedOutcome, promotionBalance, readingBalance, readingScore] using ih
      | some descriptor =>
          cases descriptor <;>
            simp [completedOutcome, readingBalance, readingScore, ih, Int.add_comm,
              sub_eq_add_neg]

theorem readingBalance_perm {left right : List (Option RS)} (permutation : left.Perm right) :
    readingBalance left = readingBalance right := (permutation.map readingScore).sum_eq

theorem readingBalance_swap (readings : List (Option RS)) :
    readingBalance (readings.map (Option.map RS.swap)) = -readingBalance readings := by
  induction readings with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | none => simpa [readingBalance, readingScore] using ih
      | some descriptor =>
          cases descriptor <;>
            simp only [List.map_cons, Option.map_some, RS.swap, readingBalance,
              List.sum_cons, readingScore] at * <;> omega

/-- A symmetry pairing the actual multiset with its R/S swap forces exact cancellation. -/
theorem completedAggregate_eq_none_of_swap_perm (readings : List (Option RS))
    (permutation : readings.Perm (readings.map (Option.map RS.swap))) :
    completedAggregate readings = some none := by
  have balanceEq := readingBalance_perm permutation
  rw [readingBalance_swap] at balanceEq
  have zero : readingBalance readings = 0 := by omega
  simp [completedAggregate, promotionAggregate, completed_balance, zero]

/-- An accepted actual consensus survives the proposed cancellation unchanged. -/
theorem completedAggregate_of_consensus (readings : List (Option RS)) (descriptor : RS)
    (accepted : consensus readings = some descriptor) :
    completedAggregate readings = some (some descriptor) := by
  obtain ⟨nonempty, all⟩ := (consensus_eq_some_iff readings descriptor).mp accepted
  apply promotionAggregate_all_descriptor
  · intro outcome member
    obtain ⟨reading, present, rfl⟩ := List.mem_map.mp member
    rw [all reading present]
    rfl
  · intro empty
    exact nonempty (List.map_eq_nil_iff.mp empty)

/-- Integration lemma: the molecular theorem must supply swap symmetry on every refused
actual population. No restriction to lists of at most two readings is needed. -/
theorem completedAggregate_eq_consensus (readings : List (Option RS))
    (refusalBalanced : consensus readings = none →
      readings.Perm (readings.map (Option.map RS.swap))) :
    completedAggregate readings = some (consensus readings) := by
  cases observed : consensus readings with
  | none => exact completedAggregate_eq_none_of_swap_perm readings (refusalBalanced observed)
  | some descriptor => exact completedAggregate_of_consensus readings descriptor observed

end TetraStereo.OneCenter.LocalizedChemicalRingPromotionAggregation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotionAggregation.completed_balance
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotionAggregation.readingBalance_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotionAggregation.readingBalance_swap
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotionAggregation.completedAggregate_eq_none_of_swap_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotionAggregation.completedAggregate_of_consensus
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotionAggregation.completedAggregate_eq_consensus
