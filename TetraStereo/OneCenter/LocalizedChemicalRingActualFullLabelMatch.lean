import TetraStereo.OneCenter.LocalizedChemicalRingPromotedStereoReadback
import TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Complete ordinary-key ties determine actual reader labels

This module applies the existing common-reference label decoder to the current rule-major
compound builder, with arbitrary readers, cursors and successful fuels on either side.
Nonempty readings and their actual stage builds are derived from the compound construction.
No chosen reference, label correspondence, acyclicity or physical transport is supplied.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingActualFullLabelMatch

open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree
open LocalizedCyclicMatchedReadingDecode LocalizedChemicalRingPromotedStereoReadback
open LocalizedChemicalRingPromotedConstitutionReadback RetainedConstitutionalReaderIndependence

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
  (fuelL fuelR : Nat) (cursorL cursorR : input.LocalizedRerootCursor carrierFuel)
  (left right : input.LocalizedRerootCompoundRule45Key)
  (builtL : input.buildRuleMajorCompoundRule45KeyWith?
    (fun stage => input.buildRuleMajorCumulativeWithRead? stage readL fuelL) cursorL = some left)
  (builtR : input.buildRuleMajorCompoundRule45KeyWith?
    (fun stage => input.buildRuleMajorCumulativeWithRead? stage readR fuelR) cursorR = some right)
  (tie : (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering = .eq)

include builtL builtR tie in
theorem full_tie_matched_traces :
    ∃ (headL headR : input.LocalizedRerootRule5Reading)
      (treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel),
      LocalizedRuleMajorSortTrace input (localizedRule5StageFor headL.prior.reference? .R)
        readL fuelL treeL headL.commonR ∧
      LocalizedRuleMajorSortTrace input (localizedRule5StageFor headR.prior.reference? .R)
        readR fuelR treeR headR.commonR ∧
      treeL.source = cursorL ∧ treeR.source = cursorR ∧
      headL.commonR.descriptor = headR.commonR.descriptor := by
  obtain ⟨headL, tailL, consL⟩ := List.exists_cons_of_ne_nil
    (compound_rule5Readings_ne_nil _ _ builtL)
  obtain ⟨headR, tailR, consR⟩ := List.exists_cons_of_ne_nil
    (compound_rule5Readings_ne_nil _ _ builtR)
  obtain ⟨_, _, _, _, readingsL⟩ := compound_components _ _ builtL
  obtain ⟨_, _, _, _, readingsR⟩ := compound_components _ _ builtR
  have commonL := rule5Readings_commonR_built _ _ _ _ readingsL headL (by rw [consL]; simp)
  have commonR := rule5Readings_commonR_built _ _ _ _ readingsR headR (by rw [consR]; simp)
  rw [input.compareLocalizedRerootCompoundThroughRule5_ordering] at tie
  have comparisons := compoundRule45Tie_prior_readings input left right tie
  rw [consL, consR] at comparisons
  have same := compareLocalizedRerootCompoundRule5Readings_heads_descriptor_eq input .R
    headL headR tailL tailR comparisons.2
  obtain ⟨treeL, sourceL, traceL⟩ := exists_ruleMajorTrace_of_buildWithRead input _ readL fuelL
    cursorL headL.commonR commonL
  obtain ⟨treeR, sourceR, traceR⟩ := exists_ruleMajorTrace_of_buildWithRead input _ readR fuelR
    cursorR headR.commonR commonR
  exact ⟨headL, headR, treeL, treeR, traceL, traceR, sourceL, sourceR, same⟩

include builtL builtR tie in
/-- A complete comparison tie forces the actual root reader labels to match, including R/S
and r/s. The readers may differ and no reference population restriction is needed. -/
theorem full_tie_root_labels : readL cursorL = readR cursorR := by
  obtain ⟨headL, headR, treeL, treeR, traceL, traceR, sourceL, sourceR, same⟩ :=
    full_tie_matched_traces readL readR fuelL fuelR cursorL cursorR left right builtL builtR tie
  have priority := headCommonR_priority_eq_of_descriptor_eq _ _
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace traceL).tableMatch
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace traceR).tableMatch same
  have labels := fullTie_priority_injective headL.prior.reference? headR.prior.reference? .R
    treeL.label treeR.label priority
  have labelL := subtreeAt?_node_label_eq_read (LocalizedRuleMajorSortTrace.realizes_of_trace traceL)
    (subtreeAt?_nil treeL)
  have labelR := subtreeAt?_node_label_eq_read (LocalizedRuleMajorSortTrace.realizes_of_trace traceR)
    (subtreeAt?_nil treeR)
  rw [sourceL] at labelL
  rw [sourceR] at labelR
  exact labelL.symm.trans (labels.trans labelR)

include builtL builtR tie in
/-- Complete tied keys produce actual common-reference trees with equal fully decorated
observations. The common addresses here are the reading trees' addresses. -/
theorem full_tie_same_observations :
    ∃ (treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel),
      treeL.source = cursorL ∧ treeR.source = cursorR ∧
      LocalizedCumulativeTreeRealizes input readL treeL ∧
      LocalizedCumulativeTreeRealizes input readR treeR ∧
      observation treeL = observation treeR := by
  obtain ⟨headL, headR, treeL, treeR, traceL, traceR, sourceL, sourceR, same⟩ :=
    full_tie_matched_traces readL readR fuelL fuelR cursorL cursorR left right builtL builtR tie
  have aBuiltL := (compound_components _ _ builtL).1
  have aBuiltR := (compound_components _ _ builtR).1
  obtain ⟨aL, aSourceL, aTraceL⟩ := exists_ruleMajorTrace_of_buildWithRead input .rule4a readL
    fuelL cursorL left.prior.rule4aKey aBuiltL
  obtain ⟨aR, aSourceR, aTraceR⟩ := exists_ruleMajorTrace_of_buildWithRead input .rule4a readR
    fuelR cursorR right.prior.rule4aKey aBuiltR
  have constL := ruleMajorSortTrace_constitutionalObservable_eq traceL aTraceL
    (sourceL.trans aSourceL.symm)
  have constR := ruleMajorSortTrace_constitutionalObservable_eq traceR aTraceR
    (sourceR.trans aSourceR.symm)
  have columns := cumulativeRule45Tie_constitutional_columns input _ _
    (rule4a_eq_of_full_eq left right tie)
  have matchL := (LocalizedRuleMajorSortTrace.fullMatch_of_trace traceL).tableMatch
  have matchR := (LocalizedRuleMajorSortTrace.fullMatch_of_trace traceR).tableMatch
  have one : (treeL.tables (localizedRule5StageFor headL.prior.reference? .R)).rule1a =
      (treeR.tables (localizedRule5StageFor headR.prior.reference? .R)).rule1a := by
    rw [matchL.1, matchR.1]
    exact (congrArg (fun x => x.rule1a) constL).trans
      (columns.1.trans (congrArg (fun x => x.rule1a) constR).symm)
  have duplicate : (treeL.tables (localizedRule5StageFor headL.prior.reference? .R)).rule1b =
      (treeR.tables (localizedRule5StageFor headR.prior.reference? .R)).rule1b := by
    rw [matchL.2.1, matchR.2.1]
    exact (congrArg (fun x => x.rule1b) constL).trans
      (columns.2.1.trans (congrArg (fun x => x.rule1b) constR).symm)
  have mass : (treeL.tables (localizedRule5StageFor headL.prior.reference? .R)).rule2 =
      (treeR.tables (localizedRule5StageFor headR.prior.reference? .R)).rule2 := by
    rw [matchL.2.2.1, matchR.2.2.1]
    exact (congrArg (fun x => x.rule2) constL).trans
      (columns.2.2.trans (congrArg (fun x => x.rule2) constR).symm)
  have desc : (treeL.tables (localizedRule5StageFor headL.prior.reference? .R)).descriptor =
      (treeR.tables (localizedRule5StageFor headR.prior.reference? .R)).descriptor := by
    rw [matchL.2.2.2, matchR.2.2.2, same]
  have priority := headCommonR_priority_eq_of_descriptor_eq _ _ matchL matchR same
  refine ⟨treeL, treeR, sourceL, sourceR, LocalizedRuleMajorSortTrace.realizes_of_trace traceL,
    LocalizedRuleMajorSortTrace.realizes_of_trace traceR, ?_⟩
  cases refL : headL.prior.reference? with
  | none =>
      cases refR : headR.prior.reference? with
      | none =>
          exact table_observation_eq_of_rule5NoRule4bReference_columns_eq .R treeL treeR
            (by simpa [refL, refR, localizedRule5StageFor] using one)
            (by simpa [refL, refR, localizedRule5StageFor] using duplicate)
            (by simpa [refL, refR, localizedRule5StageFor] using mass)
            (by simpa [refL, refR, localizedRule5StageFor] using desc)
      | some own =>
          have impossible := congrArg List.length priority
          simp [refL, refR, localizedRule5StageFor, localizedCumulativeRule45Priority] at impossible
  | some own =>
      cases refR : headR.prior.reference? with
      | none =>
          have impossible := congrArg List.length priority
          simp [refL, refR, localizedRule5StageFor, localizedCumulativeRule45Priority] at impossible
      | some own' =>
          exact table_observation_eq_of_rule5_commonReference_columns_eq own own' .R treeL treeR
            (by simpa [refL, refR, localizedRule5StageFor] using one)
            (by simpa [refL, refR, localizedRule5StageFor] using duplicate)
            (by simpa [refL, refR, localizedRule5StageFor] using mass)
            (by simpa [refL, refR, localizedRule5StageFor] using desc)

end TetraStereo.OneCenter.LocalizedChemicalRingActualFullLabelMatch

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualFullLabelMatch.full_tie_matched_traces
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualFullLabelMatch.full_tie_root_labels
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualFullLabelMatch.full_tie_same_observations
