import TetraStereo.OneCenter.LocalizedRuleMajorActualReadingShape
import TetraStereo.OneCenter.LocalizedCompoundRankConvexity
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! A complete prior tie has at most two Rule-5 observable possibilities. This is a consequence
of actual alternative shapes and the proved Rule-5 relabelling, not a physical symmetry premise.
Under distinct full priorities it discharges the sort's class-size and cross-reading conditions. -/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open LocalizedRule5SwapAndSignal

variable {input : CertifiedLocalizedCIPInput}

def ruleMajorReadingColor (key : input.LocalizedRerootCompoundRule45Key) : Bool :=
  (key.prior.readings.map (fun reading => reading.reference?)).headD none == some RS.S

private theorem tags_eq_of_color_eq
    {left right : input.LocalizedRerootCompoundRule45Key}
    (shL : input.RuleMajorReadingShape left) (shR : input.RuleMajorReadingShape right)
    (count : left.prior.referenceCountPriority = right.prior.referenceCountPriority)
    (color : ruleMajorReadingColor left = ruleMajorReadingColor right) :
    left.prior.readings.map (fun r => r.reference?) =
      right.prior.readings.map (fun r => r.reference?) := by
  rcases shL.alternatives with ⟨cL, tL⟩ | ⟨cL, tL⟩ | ⟨cL, tL⟩ | ⟨cL, tL⟩ | ⟨cL, tL⟩ <;>
    rcases shR.alternatives with ⟨cR, tR⟩ | ⟨cR, tR⟩ | ⟨cR, tR⟩ | ⟨cR, tR⟩ | ⟨cR, tR⟩
  all_goals
    simp only [ruleMajorReadingColor, tL, tR, List.headD_cons] at color
    have count' := cL.symm.trans (count.trans cR)
    rw [tL, tR] <;> first | rfl | (exfalso; revert color count'; decide)

private theorem tags_swap_of_color_ne
    {left right : input.LocalizedRerootCompoundRule45Key}
    (shL : input.RuleMajorReadingShape left) (shR : input.RuleMajorReadingShape right)
    (count : left.prior.referenceCountPriority = right.prior.referenceCountPriority)
    (color : ruleMajorReadingColor left ≠ ruleMajorReadingColor right) :
    left.prior.readings.map (fun r => r.reference?.map RS.swap) =
      right.prior.readings.map (fun r => r.reference?) := by
  have mapped : left.prior.readings.map (fun r => r.reference?.map RS.swap) =
      (left.prior.readings.map (fun r => r.reference?)).map (Option.map RS.swap) := by
    simp only [List.map_map, Function.comp_def]
  rw [mapped]
  rcases shL.alternatives with ⟨cL, tL⟩ | ⟨cL, tL⟩ | ⟨cL, tL⟩ | ⟨cL, tL⟩ | ⟨cL, tL⟩ <;>
    rcases shR.alternatives with ⟨cR, tR⟩ | ⟨cR, tR⟩ | ⟨cR, tR⟩ | ⟨cR, tR⟩ | ⟨cR, tR⟩
  all_goals
    simp only [ruleMajorReadingColor, tL, tR, List.headD_cons] at color
    have count' := cL.symm.trans (count.trans cR)
    rw [tL, tR]
    first | rfl | (exfalso; revert color count'; decide)

private theorem cTables_eq_of_tie (left right : List input.LocalizedRerootRule4bcReading)
    (tie : input.compareLocalizedRerootCompoundRule4cReadings left right = .eq) :
    left.map (fun r => r.rule4cKey.descriptor) = right.map (fun r => r.rule4cKey.descriptor) := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons b bs => cases tie
  | cons a as ih =>
      cases right with
      | nil => cases tie
      | cons b bs =>
          simp only [compareLocalizedRerootCompoundRule4cReadings, List.compareLex_cons_cons,
            Ordering.then_eq_eq, Ordering.byKey] at tie
          simp only [List.map_cons, List.cons.injEq]
          exact ⟨(compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mp
            tie.1, ih bs tie.2⟩

private theorem reading_common_eq (left right : input.LocalizedRerootRule4bcReading)
    (tag : left.reference? = right.reference?)
    (table : left.rule4cKey.descriptor = right.rule4cKey.descriptor) (common : RS) :
    input.localizedRerootRule5Descriptor common (input.ruleMajorExpectedRule5Reading left) =
      input.localizedRerootRule5Descriptor common (input.ruleMajorExpectedRule5Reading right) := by
  cases common <;>
    simp [localizedRerootRule5Descriptor, ruleMajorExpectedRule5Reading, rule5LiftKey, tag, table]

private theorem reading_mirror (left right : input.LocalizedRerootRule4bcReading)
    (tag : left.reference?.map RS.swap = right.reference?)
    (table : left.rule4cKey.descriptor = right.rule4cKey.descriptor) :
    MirrorReading input (input.ruleMajorExpectedRule5Reading left)
      (input.ruleMajorExpectedRule5Reading right) := by
  cases ref : left.reference? with
  | none =>
      simp only [ref, Option.map_none] at tag
      simp [MirrorReading, ruleMajorExpectedRule5Reading, rule5LiftKey, ref, ← tag, table]
  | some own =>
      cases own <;>
        simp [MirrorReading, ruleMajorExpectedRule5Reading, rule5LiftKey, ref, ← tag,
          RS.swap, table] <;> intro a ha <;> rfl

private theorem commonLists_eq (common : RS)
    (left right : List input.LocalizedRerootRule4bcReading)
    (tags : left.map (fun r => r.reference?) = right.map (fun r => r.reference?))
    (tables : left.map (fun r => r.rule4cKey.descriptor) =
      right.map (fun r => r.rule4cKey.descriptor)) :
    (left.map input.ruleMajorExpectedRule5Reading).map (input.localizedRerootRule5Descriptor common) =
      (right.map input.ruleMajorExpectedRule5Reading).map (input.localizedRerootRule5Descriptor common) := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons a as ih =>
      cases right with
      | nil => simp at tags
      | cons b bs =>
          simp only [List.map_cons, List.cons.injEq] at tags tables ⊢
          exact ⟨reading_common_eq a b tags.1 tables.1 common, ih bs tags.2 tables.2⟩

private theorem mirrorLists (left right : List input.LocalizedRerootRule4bcReading)
    (tags : left.map (fun r => r.reference?.map RS.swap) = right.map (fun r => r.reference?))
    (tables : left.map (fun r => r.rule4cKey.descriptor) =
      right.map (fun r => r.rule4cKey.descriptor)) :
    MirrorReadings input (left.map input.ruleMajorExpectedRule5Reading)
      (right.map input.ruleMajorExpectedRule5Reading) := by
  induction left generalizing right with
  | nil => cases right <;> simp_all [MirrorReadings]
  | cons a as ih =>
      cases right with
      | nil => simp at tags
      | cons b bs =>
          simp only [List.map_cons, List.cons.injEq] at tags tables
          exact List.Forall₂.cons (reading_mirror a b tags.1 tables.1) (ih bs tags.2 tables.2)

theorem ruleMajor_commonR_eq_of_priorTie_color
    {left right : input.LocalizedRerootCompoundRule45Key}
    (shL : input.RuleMajorReadingShape left) (shR : input.RuleMajorReadingShape right)
    (tie : input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior = .eq)
    (color : ruleMajorReadingColor left = ruleMajorReadingColor right) :
    input.compareLocalizedRerootCompoundRule5Readings .R left.rule5Readings right.rule5Readings = .eq := by
  have parts := (input.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff _ _).mp tie
  have tags := tags_eq_of_color_eq shL shR (compare_eq_iff_eq.mp parts.2.1) color
  have tables := cTables_eq_of_tie _ _ parts.2.2.2
  have same := commonLists_eq .R _ _ tags tables
  rw [shL.rule5, shR.rule5]
  unfold compareLocalizedRerootCompoundRule5Readings
  rw [compareLex_byKey_eq, same]
  haveI : Std.ReflCmp (OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority) :=
    ⟨fun {value} => (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mpr rfl⟩
  exact Std.ReflCmp.compare_self

theorem ruleMajor_mirrorReadings_of_priorTie_color_ne
    {left right : input.LocalizedRerootCompoundRule45Key}
    (shL : input.RuleMajorReadingShape left) (shR : input.RuleMajorReadingShape right)
    (tie : input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior = .eq)
    (color : ruleMajorReadingColor left ≠ ruleMajorReadingColor right) :
    MirrorReadings input left.rule5Readings right.rule5Readings := by
  have parts := (input.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff _ _).mp tie
  rw [shL.rule5, shR.rule5]
  exact mirrorLists _ _ (tags_swap_of_color_ne shL shR (compare_eq_iff_eq.mp parts.2.1) color)
    (cTables_eq_of_tie _ _ parts.2.2.2)

theorem ruleMajor_priorTie_dataCore (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (shaped : ∀ i, input.RuleMajorReadingShape (keys i))
    (strict : input.CompoundKeyOffDiagonalStrict keys) :
    input.PriorTieClassAtMostTwo keys ∧ input.PriorTieMirrorReadings keys := by
  have differentColor : ∀ i j, i ≠ j → priorKeyTie input keys i j →
      ruleMajorReadingColor (keys i) ≠ ruleMajorReadingColor (keys j) := by
    intro i j different tie same
    exact input.compoundThroughRule5_commonR_ne_of_priorTie keys strict different tie
      (ruleMajor_commonR_eq_of_priorTie_color (shaped i) (shaped j) tie same)
  refine ⟨?_, ?_⟩
  · intro i j k ij ik
    by_cases ji : j = i
    · exact Or.inr (Or.inl ji)
    by_cases ki : k = i
    · exact Or.inr (Or.inr ki)
    by_cases jk : j = k
    · exact Or.inl jk
    have cij := differentColor i j (Ne.symm ji) ij
    have cik := differentColor i k (Ne.symm ki) ik
    haveI : Std.TransCmp input.compareLocalizedRerootCompoundRule4bcKeys :=
      input.compareLocalizedRerootCompoundRule4bcKeys_transCmp
    have jiTie : priorKeyTie input keys j i := by
      unfold priorKeyTie
      rw [compareLocalizedRerootCompoundRule4bcKeys_eq_swap, ij]
      rfl
    have cjk := differentColor j k jk (Std.TransCmp.eq_trans jiTie ik)
    have impossible (a b c : Bool) : a ≠ b → a ≠ c → b ≠ c → False := by
      cases a <;> cases b <;> cases c <;> decide
    exact (impossible _ _ _ cij cik cjk).elim
  · intro i j different tie
    exact ruleMajor_mirrorReadings_of_priorTie_color_ne (shaped i) (shaped j) tie
      (differentColor i j different tie)

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajor_commonR_eq_of_priorTie_color
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajor_mirrorReadings_of_priorTie_color_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajor_priorTie_dataCore
