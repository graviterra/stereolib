import TetraStereo.OneCenter.LocalizedCompoundUppercaseReflection
import TetraStereo.KernelOnly

set_option autoImplicit false

























namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput)

/-- Complete-reading comparator of one alternative: Rule-4b table, then Rule-4c table. -/
def compareRule4bcReadingsComplete :
    input.LocalizedRerootRule4bcReading → input.LocalizedRerootRule4bcReading → Ordering :=
  compareLex input.compareLocalizedRerootRule4bcReadingsByRule4b
    (Ordering.byKey (fun reading => reading.rule4cKey.descriptor)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority))

theorem compareRule4bcReadingsComplete_transCmp :
    Std.TransCmp input.compareRule4bcReadingsComplete := by
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  unfold compareRule4bcReadingsComplete
    compareLocalizedRerootRule4bcReadingsByRule4b
    compareLocalizedCumulativeRule45Priority
    OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer
    OfficialRuleMajorKey.compareSparseEntry
  infer_instance

/-- Order at most two alternatives by their complete readings, better reading first. -/
def rankReadings :
    List input.LocalizedRerootRule4bcReading → List input.LocalizedRerootRule4bcReading
  | [first, second] =>
      if input.compareRule4bcReadingsComplete first second = .lt then [second, first]
      else [first, second]
  | readings => readings

/-- The proposed compound key: the actual key with outcome-ordered alternatives. -/
def outcomeOrdered (key : input.LocalizedRerootCompoundRule4bcKey) :
    input.LocalizedRerootCompoundRule4bcKey :=
  { key with readings := input.rankReadings key.readings }

/-- Keys with at most one alternative are unchanged. -/
theorem outcomeOrdered_eq_self_of_length_le_one (key : input.LocalizedRerootCompoundRule4bcKey)
    (short : key.readings.length ≤ 1) : input.outcomeOrdered key = key := by
  unfold outcomeOrdered rankReadings
  match key, short with
  | ⟨_, _, _, []⟩, _ => rfl
  | ⟨_, _, _, [_]⟩, _ => rfl
  | ⟨_, _, _, _ :: _ :: _⟩, h => simp at h

/-! ## Reflection invariance of the proposed prior comparator -/

/-- Reflecting a reading fixes both descriptor tables, hence every complete-reading comparison. -/
theorem compareRule4bcReadingsComplete_compoundUppercase_left
    (left right : input.LocalizedRerootRule4bcReading) :
    input.compareRule4bcReadingsComplete (compoundUppercaseRule4bcReading input left) right =
      input.compareRule4bcReadingsComplete left right := rfl

theorem compareRule4bcReadingsComplete_compoundUppercase_right
    (left right : input.LocalizedRerootRule4bcReading) :
    input.compareRule4bcReadingsComplete left (compoundUppercaseRule4bcReading input right) =
      input.compareRule4bcReadingsComplete left right := rfl

theorem compareLocalizedRerootRule4bcReadingsByRule4b_compoundUppercase_right
    (left right : input.LocalizedRerootRule4bcReading) :
    input.compareLocalizedRerootRule4bcReadingsByRule4b left
        (compoundUppercaseRule4bcReading input right) =
      input.compareLocalizedRerootRule4bcReadingsByRule4b left right := rfl

/-- The Rule-4a key of a reflected compound key ties with the original. -/
theorem rule4aKey_reflect_tie (key : input.LocalizedRerootCompoundRule4bcKey) :
    input.compareLocalizedRerootCumulativeRule45Keys key.rule4aKey
      (compoundUppercaseCompoundRule4bcKey input key).rule4aKey = .eq := by
  letI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
    input.compareLocalizedRerootCumulativeRule45Keys_transCmp
  have : input.compareLocalizedRerootCumulativeRule45Keys key.rule4aKey
      (compoundUppercaseCompoundRule4bcKey input key).rule4aKey =
      input.compareLocalizedRerootCumulativeRule45Keys key.rule4aKey key.rule4aKey := rfl
  rw [this]
  exact Std.ReflCmp.compare_self

/-- Two-element reading lists with pairwise equal descriptor tables tie under both reading-list
comparators. -/
private theorem readingLists_tie {a b a' b' : input.LocalizedRerootRule4bcReading}
    (h4b₁ : input.compareLocalizedRerootRule4bcReadingsByRule4b a a' = .eq)
    (h4b₂ : input.compareLocalizedRerootRule4bcReadingsByRule4b b b' = .eq)
    (h4c₁ : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      a.rule4cKey.descriptor a'.rule4cKey.descriptor = .eq)
    (h4c₂ : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      b.rule4cKey.descriptor b'.rule4cKey.descriptor = .eq) :
    input.compareLocalizedRerootCompoundRule4bReadings [a, b] [a', b'] = .eq ∧
      input.compareLocalizedRerootCompoundRule4cReadings [a, b] [a', b'] = .eq := by
  constructor
  · simp [compareLocalizedRerootCompoundRule4bReadings, List.compareLex, h4b₁, h4b₂]
  · simp [compareLocalizedRerootCompoundRule4cReadings, List.compareLex, Ordering.byKey, h4c₁, h4c₂]

private theorem self_tie_4b (a : input.LocalizedRerootRule4bcReading) :
    input.compareLocalizedRerootRule4bcReadingsByRule4b a a = .eq := by
  letI : Std.TransCmp input.compareLocalizedRerootRule4bcReadingsByRule4b :=
    input.compareLocalizedRerootRule4bcReadingsByRule4b_transCmp
  exact Std.ReflCmp.compare_self

private theorem self_tie_4c (a : input.LocalizedRerootRule4bcReading) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      a.rule4cKey.descriptor a.rule4cKey.descriptor = .eq := by
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  letI : Std.TransCmp (OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority) := by
    unfold compareLocalizedCumulativeRule45Priority OfficialRuleMajorKey.compareSparseLayers
      OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareSparseEntry
    infer_instance
  exact Std.ReflCmp.compare_self

/-- A complete-reading tie is a Rule-4b tie and a Rule-4c tie. -/
private theorem complete_eq_split {a b : input.LocalizedRerootRule4bcReading}
    (h : input.compareRule4bcReadingsComplete a b = .eq) :
    input.compareLocalizedRerootRule4bcReadingsByRule4b a b = .eq ∧
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        a.rule4cKey.descriptor b.rule4cKey.descriptor = .eq := by
  unfold compareRule4bcReadingsComplete at h
  rw [compareLex_eq_eq] at h
  exact ⟨h.1, h.2⟩

/-- **The outcome-ordered prior comparator is reflection-invariant.**  For every actual compound
key with at most two alternatives, the key and its uppercase reflection tie. -/
theorem outcomeOrdered_reflect_tie (key : input.LocalizedRerootCompoundRule4bcKey)
    (bounded : key.readings.length ≤ 2) :
    input.compareLocalizedRerootCompoundRule4bcKeys (input.outcomeOrdered key)
      (input.outcomeOrdered (compoundUppercaseCompoundRule4bcKey input key)) = .eq := by
  letI : Std.TransCmp input.compareRule4bcReadingsComplete :=
    input.compareRule4bcReadingsComplete_transCmp
  rw [compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff]
  refine ⟨input.rule4aKey_reflect_tie key, Std.ReflCmp.compare_self, ?_⟩
  -- the reading lists
  show input.compareLocalizedRerootCompoundRule4bReadings (input.rankReadings key.readings)
        (input.rankReadings ((key.readings.map (compoundUppercaseRule4bcReading input)).reverse)) =
      .eq ∧
    input.compareLocalizedRerootCompoundRule4cReadings (input.rankReadings key.readings)
        (input.rankReadings ((key.readings.map (compoundUppercaseRule4bcReading input)).reverse)) =
      .eq
  match key.readings, bounded with
  | [], _ => exact ⟨rfl, rfl⟩
  | [a], _ =>
      simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
        rankReadings]
      constructor
      · simp [compareLocalizedRerootCompoundRule4bReadings, List.compareLex,
          compareLocalizedRerootRule4bcReadingsByRule4b_compoundUppercase_right, self_tie_4b]
      · simp [compareLocalizedRerootCompoundRule4cReadings, List.compareLex, Ordering.byKey,
          compoundUppercaseRule4bcReading, self_tie_4c]
  | [a, b], _ =>
      simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, rankReadings,
        compareRule4bcReadingsComplete_compoundUppercase_left,
        compareRule4bcReadingsComplete_compoundUppercase_right]
      have swap : input.compareRule4bcReadingsComplete b a =
          (input.compareRule4bcReadingsComplete a b).swap :=
        Std.OrientedCmp.eq_swap
      rcases hab : input.compareRule4bcReadingsComplete a b with _ | _ | _
      · -- a < b : sorted [b, a] on both sides
        have hba : input.compareRule4bcReadingsComplete b a = .gt := by rw [swap, hab]; rfl
        simp only [hba, if_true, reduceCtorEq, if_false]
        exact input.readingLists_tie (self_tie_4b input b) (self_tie_4b input a) (self_tie_4c input b) (self_tie_4c input a)
      · -- tie: [a, b] against [b', a'], all tables equal
        have hba : input.compareRule4bcReadingsComplete b a = .eq := by rw [swap, hab]; rfl
        simp only [hba, reduceCtorEq, if_false]
        obtain ⟨h4b, h4c⟩ := input.complete_eq_split hab
        obtain ⟨h4b', h4c'⟩ := input.complete_eq_split hba
        exact input.readingLists_tie h4b h4b' h4c h4c'
      · -- a > b : sorted [a, b] on both sides
        have hba : input.compareRule4bcReadingsComplete b a = .lt := by rw [swap, hab]; rfl
        simp only [hba, if_true, reduceCtorEq, if_false]
        exact input.readingLists_tie (self_tie_4b input a) (self_tie_4b input b) (self_tie_4c input a) (self_tie_4c input b)
  | _ :: _ :: _ :: _, h => exact absurd h (by simp)

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outcomeOrdered
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outcomeOrdered_eq_self_of_length_le_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule4aKey_reflect_tie
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outcomeOrdered_reflect_tie
