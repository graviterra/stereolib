import TetraStereo.OneCenter.LocalizedChemicalRingStageReplay
import TetraStereo.OneCenter.LocalizedRuleMajorCompoundReadback
import TetraStereo.OneCenter.LocalizedActualOrderedRootMirrorPriorTie
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Compound rebuilding preserves complete comparisons

Equal stage observations and equal actual Rule-4a selections transport the current compound
builder. The alternative ordering transports both descriptor tables AND each own reference;
therefore the subsequent common-R and common-S Rule-5 stage calls agree. No fixed alternative
count is assumed and hidden source metadata need not match.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingCompoundReplay

open CertifiedLocalizedCIPInput LocalizedCyclicMatchedReadingDecode

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

def MatchedPrior (left right : input.LocalizedRerootRule4bcReading) : Prop :=
  left.reference? = right.reference? ∧ ReadingTablesEq left right

theorem rankReadings_matched {left right : List input.LocalizedRerootRule4bcReading}
    (matched : List.Forall₂ MatchedPrior left right) :
    List.Forall₂ MatchedPrior (input.rankReadings left) (input.rankReadings right) := by
  match left, right, matched with
  | [], [], .nil => exact .nil
  | [a], [b], .cons h .nil => exact .cons h .nil
  | [a, b], [a', b'], .cons ha (.cons hb .nil) =>
      have comparisons := input.compareRule4bcReadingsComplete_congr ha.2 hb.2
      simp only [rankReadings, comparisons]
      split_ifs
      · exact .cons hb (.cons ha .nil)
      · exact .cons ha (.cons hb .nil)
  | a :: b :: c :: rest, a' :: b' :: c' :: rest', .cons ha (.cons hb (.cons hc tail)) =>
      exact .cons ha (.cons hb (.cons hc tail))

theorem matched_prior_lists_tie {left right : List input.LocalizedRerootRule4bcReading}
    (matched : List.Forall₂ MatchedPrior left right) :
    input.compareLocalizedRerootCompoundRule4bReadings left right = .eq ∧
      input.compareLocalizedRerootCompoundRule4cReadings left right = .eq := by
  induction matched with
  | nil => exact ⟨rfl, rfl⟩
  | cons h _ ih =>
      constructor
      · simpa only [compareLocalizedRerootCompoundRule4bReadings, List.compareLex_cons_cons,
          input.compareByRule4b_eq_of_tablesEq h.2, Ordering.eq_then] using ih.1
      · simpa only [compareLocalizedRerootCompoundRule4cReadings, List.compareLex_cons_cons,
          Ordering.byKey, input.compare4cDescriptor_eq_of_tablesEq h.2, Ordering.eq_then] using ih.2

section Compiler

variable (compileL compileR : input.RuleMajorCompoundStageCompiler carrierFuel)
  (x y : input.LocalizedRerootCursor carrierFuel)
  (stages : ∀ stage keyL keyR, compileL stage x = some keyL → compileR stage y = some keyR →
    input.localizedRerootCumulativeRule45Observable keyL =
      input.localizedRerootCumulativeRule45Observable keyR)

include stages in
theorem prior_reading_matched (reference : Option RS) (left right : input.LocalizedRerootRule4bcReading)
    (builtL : input.buildRuleMajorCompoundRule4bcReadingWith? compileL x reference = some left)
    (builtR : input.buildRuleMajorCompoundRule4bcReadingWith? compileR y reference = some right) :
    MatchedPrior left right := by
  obtain ⟨bL, cL, hbL, hcL, refL, eqbL, eqcL⟩ :=
    (input.buildRuleMajorCompoundRule4bcReadingWith?_eq_some_iff_stageBuilds _ _ _ _).mp builtL
  obtain ⟨bR, cR, hbR, hcR, refR, eqbR, eqcR⟩ :=
    (input.buildRuleMajorCompoundRule4bcReadingWith?_eq_some_iff_stageBuilds _ _ _ _).mp builtR
  refine ⟨refL.trans refR.symm, ?_, ?_⟩
  · rw [eqbL, eqbR]
    cases reference <;>
      exact congrArg LocalizedCumulativeRule45Observable.descriptor (stages _ _ _ hbL hbR)
  · rw [eqcL, eqcR]
    cases reference <;>
      exact congrArg LocalizedCumulativeRule45Observable.descriptor (stages _ _ _ hcL hcR)

include stages in
theorem prior_readings_matched : ∀ references left right,
    input.buildRuleMajorCompoundRule4bcReadingsWith? compileL x references = some left →
    input.buildRuleMajorCompoundRule4bcReadingsWith? compileR y references = some right →
    List.Forall₂ MatchedPrior left right := by
  intro references
  induction references with
  | nil => intro left right hl hr; simp [buildRuleMajorCompoundRule4bcReadingsWith?] at hl hr; subst hl; subst hr; exact .nil
  | cons reference references ih =>
      intro left right hl hr
      unfold buildRuleMajorCompoundRule4bcReadingsWith? at hl hr
      obtain ⟨a, ha, moreL⟩ := Option.bind_eq_some_iff.mp hl
      obtain ⟨b, hb, moreR⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨as, has, resultL⟩ := Option.bind_eq_some_iff.mp moreL
      obtain ⟨bs, hbs, resultR⟩ := Option.bind_eq_some_iff.mp moreR
      cases Option.some.inj resultL
      cases Option.some.inj resultR
      exact .cons (prior_reading_matched compileL compileR x y stages reference a b ha hb)
        (ih as bs has hbs)

include stages in
theorem rule5_reading_matched (priorL priorR : input.LocalizedRerootRule4bcReading)
    (matched : MatchedPrior priorL priorR) (left right : input.LocalizedRerootRule5Reading)
    (builtL : input.buildRuleMajorCompoundRule5ReadingWith? compileL x priorL = some left)
    (builtR : input.buildRuleMajorCompoundRule5ReadingWith? compileR y priorR = some right) :
    left.commonR.descriptor = right.commonR.descriptor ∧
      left.commonS.descriptor = right.commonS.descriptor := by
  obtain ⟨_, rL, sL⟩ := rule5Reading_components compileL x builtL
  obtain ⟨_, rR, sR⟩ := rule5Reading_components compileR y builtR
  rw [matched.1] at rL sL
  exact ⟨congrArg LocalizedCumulativeRule45Observable.descriptor (stages _ _ _ rL rR),
    congrArg LocalizedCumulativeRule45Observable.descriptor (stages _ _ _ sL sR)⟩

include stages in
theorem rule5_readings_matched {priorsL priorsR : List input.LocalizedRerootRule4bcReading}
    (matched : List.Forall₂ MatchedPrior priorsL priorsR) : ∀ left right,
    input.buildRuleMajorCompoundRule5ReadingsWith? compileL x priorsL = some left →
    input.buildRuleMajorCompoundRule5ReadingsWith? compileR y priorsR = some right →
    List.Forall₂ (fun a b : input.LocalizedRerootRule5Reading =>
      a.commonR.descriptor = b.commonR.descriptor ∧ a.commonS.descriptor = b.commonS.descriptor) left right := by
  induction matched with
  | nil => intro left right hl hr; simp [buildRuleMajorCompoundRule5ReadingsWith?] at hl hr; subst hl; subst hr; exact .nil
  | @cons p q ps qs h _ ih =>
      intro left right hl hr
      unfold buildRuleMajorCompoundRule5ReadingsWith? at hl hr
      obtain ⟨a, ha, moreL⟩ := Option.bind_eq_some_iff.mp hl
      obtain ⟨b, hb, moreR⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨as, has, resultL⟩ := Option.bind_eq_some_iff.mp moreL
      obtain ⟨bs, hbs, resultR⟩ := Option.bind_eq_some_iff.mp moreR
      cases Option.some.inj resultL
      cases Option.some.inj resultR
      exact .cons (rule5_reading_matched compileL compileR x y stages p q h a b ha hb)
        (ih as bs has hbs)

include stages in
/-- Complete successful compound rebuilds tie, with no enantiomorphic signal. The selector
premise here is discharged from decoded actual observations in the successor module. -/
theorem compound_replay
    (selectors : ∀ keyL keyR, compileL .rule4a x = some keyL → compileR .rule4a y = some keyR →
      localizedRule4bReferencesFromRankedLabels keyL.rankedLabels =
        localizedRule4bReferencesFromRankedLabels keyR.rankedLabels)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (builtL : input.buildRuleMajorCompoundRule45KeyWith? compileL x = some left)
    (builtR : input.buildRuleMajorCompoundRule45KeyWith? compileR y = some right) :
    input.compareLocalizedRerootCompoundThroughRule5 left right = ⟨.eq, false⟩ := by
  obtain ⟨aL, refL, countL, rawL, rawBuiltL, rankedL, rule5L⟩ :=
    input.buildRuleMajorCompoundRule45KeyWith?_readback compileL x builtL
  obtain ⟨aR, refR, countR, rawR, rawBuiltR, rankedR, rule5R⟩ :=
    input.buildRuleMajorCompoundRule45KeyWith?_readback compileR y builtR
  have references := refL.trans ((selectors _ _ aL aR).trans refR.symm)
  have count : left.prior.referenceCountPriority = right.prior.referenceCountPriority := by
    rw [countL, countR, references]
  have aTie := (input.compareLocalizedRerootCumulativeRule45Keys_eq_iff_observable_eq _ _).mpr
    (stages _ _ _ aL aR)
  rw [references] at rawBuiltL
  have rawMatched := prior_readings_matched compileL compileR x y stages _ _ _ rawBuiltL rawBuiltR
  have rankedMatched : List.Forall₂ MatchedPrior left.prior.readings right.prior.readings := by
    rw [rankedL, rankedR]
    exact rankReadings_matched rawMatched
  have priorTables := matched_prior_lists_tie rankedMatched
  have priorTie : input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior = .eq := by
    simp only [compareLocalizedRerootCompoundRule4bcKeys, compareLex, Ordering.byKey,
      aTie, priorTables.1, priorTables.2, Ordering.eq_then,
      (compare_eq_iff_eq.mpr count : compare left.prior.referenceCountPriority right.prior.referenceCountPriority = .eq)]
  have rule5Matched := rule5_readings_matched compileL compileR x y stages rankedMatched _ _ rule5L rule5R
  have rTie := compareLocalizedRerootCompoundRule5Readings_eq_of_forall₂ input .R
    (rule5Matched.imp (fun _ _ h => h.1))
  simp only [compareLocalizedRerootCompoundThroughRule5, priorTie, rTie]
  rfl

end Compiler
end TetraStereo.OneCenter.LocalizedChemicalRingCompoundReplay

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompoundReplay.rankReadings_matched
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompoundReplay.prior_reading_matched
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompoundReplay.rule5_reading_matched
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompoundReplay.compound_replay
