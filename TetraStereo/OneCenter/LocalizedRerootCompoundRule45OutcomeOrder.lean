import TetraStereo.OneCenter.LocalizedRerootCompoundRule4bcOutcomeOrder
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Outcome-ordered alternatives through Rule 5

The Rule-5 reading list of a compound key is built per Rule-4b/4c alternative, so the proposed
ordering of alternatives (`LocalizedRerootCompoundRule4bcOutcomeOrder`) carries over to the
through-Rule-5 key by ordering the Rule-5 readings by their `prior` alternative with the same
complete-reading comparator.  This module records:

* `outcomeOrdered45_eq_self_of_length_le_one` — keys with at most one alternative are unchanged;
* `outcomeOrdered45_prior` — the prior of the ordered key is the ordered prior;
* `outcomeOrdered45_reflect_pseudo` — for a key whose two alternatives are *strictly* ordered, the
  through-Rule-5 comparison of the ordered key against its ordered uppercase reflection has the
  prior tie, and its `pseudo` flag is exactly "the ordering is strict": the common-S comparison
  is the swap of the common-R comparison, so a Rule-5 decision between an arm and its mirror
  image is always marked enantiomorphic.

The fully tied case (equal Rule-4b and Rule-4c tables of the two alternatives) keeps the builder
order on both sides; it is left outside this theorem and recorded as a source question.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput)

/-- Order at most two Rule-5 readings by the complete reading of their prior alternatives. -/
def rankRule5Readings :
    List input.LocalizedRerootRule5Reading → List input.LocalizedRerootRule5Reading
  | [first, second] =>
      if input.compareRule4bcReadingsComplete first.prior second.prior = .lt then [second, first]
      else [first, second]
  | readings => readings

/-- The proposed through-Rule-5 key: ordered prior and correspondingly ordered Rule-5 readings. -/
def outcomeOrdered45 (key : input.LocalizedRerootCompoundRule45Key) :
    input.LocalizedRerootCompoundRule45Key :=
  { prior := input.outcomeOrdered key.prior
    rule5Readings := input.rankRule5Readings key.rule5Readings }

theorem outcomeOrdered45_prior (key : input.LocalizedRerootCompoundRule45Key) :
    (input.outcomeOrdered45 key).prior = input.outcomeOrdered key.prior := rfl

/-- The prior alternatives of the ordered Rule-5 readings are the ordered alternatives: ordering
the Rule-5 list by prior and ordering the prior list agree, so a builder that applies
`rankReadings` to the compound key and then builds Rule-5 readings per alternative produces
exactly `rankRule5Readings`. -/
theorem rankRule5Readings_map_prior (readings : List input.LocalizedRerootRule5Reading) :
    (input.rankRule5Readings readings).map (·.prior) =
      input.rankReadings (readings.map (·.prior)) := by
  match readings with
  | [] => rfl
  | [a] => rfl
  | [a, b] =>
      simp only [rankRule5Readings, rankReadings, List.map_cons, List.map_nil]
      split <;> simp_all
  | _ :: _ :: _ :: _ => rfl

theorem outcomeOrdered45_eq_self_of_length_le_one (key : input.LocalizedRerootCompoundRule45Key)
    (shortPrior : key.prior.readings.length ≤ 1) (short : key.rule5Readings.length ≤ 1) :
    input.outcomeOrdered45 key = key := by
  unfold outcomeOrdered45
  rw [input.outcomeOrdered_eq_self_of_length_le_one key.prior shortPrior]
  match key, short with
  | ⟨_, []⟩, _ => rfl
  | ⟨_, [_]⟩, _ => rfl
  | ⟨_, _ :: _ :: _⟩, h => exact absurd h (by simp)

/-! ## Rule-5 readings of mirror images -/

/-- Reflecting a Rule-5 reading exchanges its common channels: probing the reflection at common
reference `R` reads the original common-`S` table. -/
theorem localizedRerootRule5Descriptor_R_compoundUppercase
    (reading : input.LocalizedRerootRule5Reading) :
    input.localizedRerootRule5Descriptor .R (compoundUppercaseRule5Reading input reading) =
      input.localizedRerootRule5Descriptor .S reading := rfl

theorem localizedRerootRule5Descriptor_S_compoundUppercase
    (reading : input.LocalizedRerootRule5Reading) :
    input.localizedRerootRule5Descriptor .S (compoundUppercaseRule5Reading input reading) =
      input.localizedRerootRule5Descriptor .R reading := rfl

/-- Elementwise Rule-5 comparator. -/
private def byRule5 (commonReference : RS) :
    input.LocalizedRerootRule5Reading → input.LocalizedRerootRule5Reading → Ordering :=
  Ordering.byKey (input.localizedRerootRule5Descriptor commonReference)
    (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)

private theorem compareSparseLayers_transCmp :
    Std.TransCmp (OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority) := by
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  unfold compareLocalizedCumulativeRule45Priority OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareSparseEntry
  infer_instance

/-- At common `S`, a reading against its own reflection is the swap of the same comparison at
common `R`: the reflection exchanges the two channels. -/
private theorem byRule5_S_reflect_swap (a : input.LocalizedRerootRule5Reading) :
    byRule5 input .S a (compoundUppercaseRule5Reading input a) =
      (byRule5 input .R a (compoundUppercaseRule5Reading input a)).swap := by
  letI := compareSparseLayers_transCmp
  simp only [byRule5, Ordering.byKey, localizedRerootRule5Descriptor_S_compoundUppercase,
    localizedRerootRule5Descriptor_R_compoundUppercase]
  exact Std.OrientedCmp.eq_swap

/-- For an aligned list of readings against their reflections, the common-S comparison is the
swap of the common-R comparison. -/
private theorem compareRule5_aligned_swap :
    ∀ readings : List input.LocalizedRerootRule5Reading,
      input.compareLocalizedRerootCompoundRule5Readings .S readings
          (readings.map (compoundUppercaseRule5Reading input)) =
        (input.compareLocalizedRerootCompoundRule5Readings .R readings
          (readings.map (compoundUppercaseRule5Reading input))).swap
  | [] => rfl
  | a :: rest => by
      have ih := compareRule5_aligned_swap rest
      unfold compareLocalizedRerootCompoundRule5Readings at ih ⊢
      simp only [List.map_cons, List.compareLex_cons_cons]
      rw [show (Ordering.byKey (input.localizedRerootRule5Descriptor .S)
          (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority) a
          (compoundUppercaseRule5Reading input a)) = byRule5 input .S a
            (compoundUppercaseRule5Reading input a) from rfl,
        show (Ordering.byKey (input.localizedRerootRule5Descriptor .R)
          (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority) a
          (compoundUppercaseRule5Reading input a)) = byRule5 input .R a
            (compoundUppercaseRule5Reading input a) from rfl,
        byRule5_S_reflect_swap, ih, Ordering.swap_then]

/-- The ordered Rule-5 readings of a key and of its reflection are aligned (the reflection of
each original reading sits at the same position) whenever the two alternatives are strictly
ordered or there is at most one. -/
private theorem rankRule5Readings_reflect_aligned
    (readings : List input.LocalizedRerootRule5Reading)
    (bounded : readings.length ≤ 2)
    (strict : ∀ a b, readings = [a, b] →
      input.compareRule4bcReadingsComplete a.prior b.prior ≠ .eq) :
    input.rankRule5Readings ((readings.map (compoundUppercaseRule5Reading input)).reverse) =
      (input.rankRule5Readings readings).map (compoundUppercaseRule5Reading input) := by
  letI : Std.TransCmp input.compareRule4bcReadingsComplete :=
    input.compareRule4bcReadingsComplete_transCmp
  match readings, bounded, strict with
  | [], _, _ => rfl
  | [a], _, _ => rfl
  | [a, b], _, strict =>
      simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.singleton_append, rankRule5Readings]
      have swap : input.compareRule4bcReadingsComplete
          (compoundUppercaseRule5Reading input b).prior
          (compoundUppercaseRule5Reading input a).prior =
            (input.compareRule4bcReadingsComplete a.prior b.prior).swap := by
        show input.compareRule4bcReadingsComplete
          (compoundUppercaseRule4bcReading input b.prior)
          (compoundUppercaseRule4bcReading input a.prior) = _
        rw [compareRule4bcReadingsComplete_compoundUppercase_left,
          compareRule4bcReadingsComplete_compoundUppercase_right]
        exact Std.OrientedCmp.eq_swap
      rw [swap]
      rcases hab : input.compareRule4bcReadingsComplete a.prior b.prior with _ | _ | _
      · simp
      · exact absurd hab (strict a b rfl)
      · simp
  | _ :: _ :: _ :: _, h, _ => exact absurd h (by simp)

/-- **Mirror images are enantiomorphic under the ordered through-Rule-5 comparison.**  For a key
with at most two alternatives, strictly ordered, the prior comparison of the ordered key against
its ordered reflection ties, and the result's `pseudo` flag is exactly "the ordering is strict". -/
theorem outcomeOrdered45_reflect_pseudo (key : input.LocalizedRerootCompoundRule45Key)
    (priorBounded : key.prior.readings.length ≤ 2)
    (bounded : key.rule5Readings.length ≤ 2)
    (strict : ∀ a b, key.rule5Readings = [a, b] →
      input.compareRule4bcReadingsComplete a.prior b.prior ≠ .eq) :
    (input.compareLocalizedRerootCompoundThroughRule5 (input.outcomeOrdered45 key)
        (input.outcomeOrdered45 (compoundUppercaseCompoundRule45Key input key))).pseudo =
      decide ((input.compareLocalizedRerootCompoundThroughRule5 (input.outcomeOrdered45 key)
        (input.outcomeOrdered45 (compoundUppercaseCompoundRule45Key input key))).ordering ≠ .eq) := by
  have priorTie := input.outcomeOrdered_reflect_tie key.prior priorBounded
  have aligned := input.rankRule5Readings_reflect_aligned key.rule5Readings bounded strict
  have swap := input.compareRule5_aligned_swap (input.rankRule5Readings key.rule5Readings)
  unfold compareLocalizedRerootCompoundThroughRule5
  simp only [outcomeOrdered45, compoundUppercaseCompoundRule45Key] at priorTie aligned ⊢
  rw [aligned]
  simp only [priorTie, bne_self_eq_false, Bool.false_eq_true, if_false]
  rw [swap]
  rcases input.compareLocalizedRerootCompoundRule5Readings .R
      (input.rankRule5Readings key.rule5Readings)
      ((input.rankRule5Readings key.rule5Readings).map (compoundUppercaseRule5Reading input)) with
    _ | _ | _ <;> rfl

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outcomeOrdered45
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outcomeOrdered45_eq_self_of_length_le_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outcomeOrdered45_reflect_pseudo
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rankRule5Readings_map_prior
