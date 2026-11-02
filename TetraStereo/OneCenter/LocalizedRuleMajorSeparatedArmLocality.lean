import TetraStereo.OneCenter.LocalizedActualFrameChildClassification
import TetraStereo.OneCenter.LocalizedCompoundParentNoninterference
import TetraStereo.OneCenter.LocalizedConstitutionalRootSeparation
import TetraStereo.OneCenter.LocalizedCyclicContextFrameCompilation
import TetraStereo.OneCenter.LocalizedFullCompoundTieLabelDecoding
import TetraStereo.OneCenter.LocalizedRule5SwapAndSignal
import TetraStereo.OneCenter.LocalizedRuleMajorDependencyLocality
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Descriptor locality for one constitutionally separated arm

The approved locality theorem needs agreement on every arm the frame reads.
When one arm is strictly separated at Rule 1a from every other arm, its later
stereo tables are not inspected: each pair against it is the constitutional
ordering with `pseudo = false`, and the remaining pairs use the approved
locality theorem. Fuel success at `2 * (carrierFuel + 1)` is derived from
path validity of the actual frame cursors.

`ArmConstitutionalRule1aSeparated` is the case premise for the rootward
cut-cardinality argument. It is not a physical-domain restriction, and this
file does not finish descriptor covariance or a mirror theorem.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

open DeclarativeCIP

/-- Every cursor of a computed four-ligand frame is an executable child of the
target-start cursor, hence path-valid. -/
theorem frameCursor_valid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (index : Fin 4) :
    input.LocalizedRerootCursorValid (frame.cursorAt index) := by
  let parent : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := none }
  have cursorsEq :=
    input.localizedOccurrenceFourLigandFrame_cursors_eq_executable target frame computed
  have present : frame.cursorAt index ∈ input.executableLocalizedRerootChildren parent := by
    rw [← cursorsEq]
    unfold LocalizedOccurrenceFourLigandFrame.cursorAt
    exact List.get_mem _ _
  exact input.localizedRerootChild_valid parent (frame.cursorAt index)
    (input.executableLocalizedRerootChildren parent)
    (input.executableLocalizedRerootChildren_declarative parent) present

/-- The actual compound builder succeeds at the evaluation fuel for every view. -/
theorem frameCursor_actualCompound_at_evaluationFuel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (index : Fin 4) :
    ∃ compound, input.buildActualRuleMajorCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt index) =
        some compound := by
  obtain ⟨compound, built⟩ :=
    input.exists_buildActualRuleMajorCompoundRule45Key_at_twice target view
      (frame.cursorAt index) (input.frameCursor_valid target frame computed index)
  refine ⟨compound, ?_⟩
  simpa [localizedOccurrenceRerootEvaluationFuel] using built

/-- Rule 1a of the label-free `.rule4a` build separates `distinguished` from
every other frame cursor. Success of that build is not assumed: a failing build
makes the implication vacuously true, and the descriptor proof derives success
before using the inequality. -/
def ArmConstitutionalRule1aSeparated
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (distinguished : Fin 4) : Prop :=
  ∀ other : Fin 4, other ≠ distinguished →
    ∀ keyD keyO : input.LocalizedRerootCumulativeRule45Key,
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
          (fun _ => none) (2 * (carrierFuel + 1)) (frame.cursorAt distinguished) =
            some keyD →
        input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
            (fun _ => none) (2 * (carrierFuel + 1)) (frame.cursorAt other) =
              some keyO →
          OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
              keyD.constitutional.rule1a keyO.constitutional.rule1a ≠
            Ordering.eq

private theorem compoundWith_rule4aKey
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {compound : input.LocalizedRerootCompoundRule45Key}
    (built : input.buildRuleMajorCompoundRule45KeyWith? compileStage cursor = some compound) :
    ∃ key, compileStage .rule4a cursor = some key ∧ compound.prior.rule4aKey = key := by
  unfold buildRuleMajorCompoundRule45KeyWith? at built
  rcases Option.eq_none_or_eq_some (compileStage .rule4a cursor) with h4a | ⟨key, h4a⟩
  · rw [h4a] at built
    simp [Option.bind_eq_bind, Option.bind_none] at built
  · rw [h4a] at built
    simp only [Option.bind_eq_bind, Option.bind_some] at built
    rcases Option.eq_none_or_eq_some
        (input.buildRuleMajorCompoundRule4bcReadingsWith? compileStage cursor
          (localizedRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels key.rankedLabels))) with
      hr | ⟨readings, hr⟩
    · rw [hr] at built
      simp [Option.bind_eq_bind, Option.bind_none] at built
    · rw [hr] at built
      simp only [Option.bind_eq_bind, Option.bind_some] at built
      rcases Option.eq_none_or_eq_some
          (input.buildRuleMajorCompoundRule5ReadingsWith? compileStage cursor
            (input.rankReadings readings)) with
        h5 | ⟨rule5, h5⟩
      · rw [h5] at built
        simp [Option.bind_eq_bind, Option.bind_none] at built
      · rw [h5] at built
        simp only [Option.bind_eq_bind, Option.bind_some, Option.some_inj] at built
        exact ⟨key, h4a, by rw [← built]⟩

private theorem actualCompound_rule4aKey
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    {compound : input.LocalizedRerootCompoundRule45Key}
    (built : input.buildActualRuleMajorCompoundRule45Key? target view fuel cursor =
      some compound) :
    input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel cursor =
      some compound.prior.rule4aKey := by
  unfold buildActualRuleMajorCompoundRule45Key? buildRuleMajorCompoundRule45Key? at built
  obtain ⟨key, hkey, eqKey⟩ :=
    input.compoundWith_rule4aKey
      (input.ruleMajorCompoundStageCompiler target view
        (input.localizedDependencyLabel target view) fuel)
      cursor built
  simp only [ruleMajorCompoundStageCompiler] at hkey
  simpa [eqKey] using hkey

/-- A strict Rule-1a comparison of the stored Rule-4a keys decides the
through-Rule-5 record. Later descriptor columns, reference readings, and both
Rule-5 readings are not inspected, and the enantiomorphic flag is false. -/
theorem compareLocalizedRerootCompoundThroughRule5_eq_rule1a_of_decisive
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.prior.rule4aKey.constitutional.rule1a
      right.prior.rule4aKey.constitutional.rule1a ≠ Ordering.eq) :
    input.compareLocalizedRerootCompoundThroughRule5 left right =
      { ordering := OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          left.prior.rule4aKey.constitutional.rule1a
          right.prior.rule4aKey.constitutional.rule1a
        pseudo := false } := by
  have constEq := OfficialRuleMajorKey.compare_eq_rule1a_of_decisive
    (left := left.prior.rule4aKey.constitutional)
    (right := right.prior.rule4aKey.constitutional) decisive
  have constNe : OfficialRuleMajorKey.compare left.prior.rule4aKey.constitutional
      right.prior.rule4aKey.constitutional ≠ Ordering.eq := by
    rw [constEq]
    exact decisive
  have cumulativeEq : input.compareLocalizedRerootCumulativeRule45Keys
      left.prior.rule4aKey right.prior.rule4aKey =
      OfficialRuleMajorKey.compare left.prior.rule4aKey.constitutional
        right.prior.rule4aKey.constitutional := by
    unfold compareLocalizedRerootCumulativeRule45Keys
    refine ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq _ _ _ _ ?_
    simpa [Ordering.byKey] using constNe
  have cumulativeNe : input.compareLocalizedRerootCumulativeRule45Keys
      left.prior.rule4aKey right.prior.rule4aKey ≠ Ordering.eq := by
    rw [cumulativeEq]
    exact constNe
  rw [input.compareLocalizedRerootCompoundThroughRule5_eq_of_rule4a_ne_eq
      left right cumulativeNe, cumulativeEq, constEq]

private theorem noneReader_rule4a
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      (fun _ => none) (2 * (carrierFuel + 1)) cursor = some key :=
  WholeStateCumulativeLabels.exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice
    input .rule4a (fun _ => none) cursor valid

private theorem actual_rule4a_observable_eq_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    {compound : input.LocalizedRerootCompoundRule45Key}
    (built : input.buildActualRuleMajorCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor = some compound)
    {noneKey : input.LocalizedRerootCumulativeRule45Key}
    (noneBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      (fun _ => none) (2 * (carrierFuel + 1)) cursor = some noneKey) :
    compound.prior.rule4aKey.constitutional.rule1a = noneKey.constitutional.rule1a := by
  have rule4aBuilt := input.actualCompound_rule4aKey target view
    (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor built
  have withRead : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      (fun cursor => input.localizedDependencyLabel target view cursor)
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor =
      some compound.prior.rule4aKey := by
    exact
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
        .rule4a target view (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor).trans
        rule4aBuilt
  have observable :=
    buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_observable_equal
      input cursor (leftComputed := withRead) (rightComputed := noneBuilt)
  exact congrArg LocalizedConstitutionalObservable.rule1a observable

private theorem compareAt_of_compoundKeys
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (left right : Fin 4)
    {cmp : ConstitutionalRule5Comparison}
    {leftKey rightKey : input.LocalizedRerootCompoundRule45Key}
    (leftBuilt : input.buildActualRuleMajorCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt left) =
        some leftKey)
    (rightBuilt : input.buildActualRuleMajorCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt right) =
        some rightKey)
    (compared : input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey = cmp) :
    input.compareRuleMajorOccurrenceAt? target view frame left right =
      some (localizedOccurrenceRule45ComparisonRecord cmp) := by
  unfold compareRuleMajorOccurrenceAt?
  change (do
      let leftResult ← input.buildActualRuleMajorCompoundRule45Key? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt left)
      let rightResult ← input.buildActualRuleMajorCompoundRule45Key? target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt right)
      some (localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 leftResult rightResult))) = _
  rw [leftBuilt, rightBuilt]
  simp only [Option.bind_eq_bind, Option.bind_some, compared]

private theorem rule1a_ne_swap
    {left right : List (List (OfficialSparseEntry Nat))}
    (decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left right ≠ Ordering.eq) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      right left ≠ Ordering.eq := by
  intro swapped
  have swapEq :=
    @LocalizedRule5SwapAndSignal.compareSparseLayers_eq_swap Nat
      OfficialRuleMajorKey.compareNat
      (by
        unfold OfficialRuleMajorKey.compareNat
        infer_instance)
      left right
  rw [swapped] at swapEq
  exact decisive swapEq

private theorem compareRuleMajorOccurrenceAt?_constitutional_of_separatedArm
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (distinguished : Fin 4)
    (separated : input.ArmConstitutionalRule1aSeparated frame distinguished)
    (right : Fin 4)
    (rightOther : right ≠ distinguished) :
    input.compareRuleMajorOccurrenceAt? target (input.molecularView map₁ target) frame
        distinguished right =
      input.compareRuleMajorOccurrenceAt? target (input.molecularView map₂ target) frame
        distinguished right := by
  let view₁ := input.molecularView map₁ target
  let view₂ := input.molecularView map₂ target
  have validD := input.frameCursor_valid target frame computed distinguished
  have validO := input.frameCursor_valid target frame computed right
  obtain ⟨noneD, noneDBuilt⟩ := input.noneReader_rule4a (frame.cursorAt distinguished) validD
  obtain ⟨noneO, noneOBuilt⟩ := input.noneReader_rule4a (frame.cursorAt right) validO
  have decisive := separated right rightOther noneD noneO noneDBuilt noneOBuilt
  obtain ⟨compound₁D, built₁D⟩ := input.frameCursor_actualCompound_at_evaluationFuel target
    view₁ frame computed distinguished
  obtain ⟨compound₁O, built₁O⟩ := input.frameCursor_actualCompound_at_evaluationFuel target
    view₁ frame computed right
  obtain ⟨compound₂D, built₂D⟩ := input.frameCursor_actualCompound_at_evaluationFuel target
    view₂ frame computed distinguished
  obtain ⟨compound₂O, built₂O⟩ := input.frameCursor_actualCompound_at_evaluationFuel target
    view₂ frame computed right
  have rule₁D := input.actual_rule4a_observable_eq_none target view₁
    (frame.cursorAt distinguished) validD built₁D noneDBuilt
  have rule₁O := input.actual_rule4a_observable_eq_none target view₁
    (frame.cursorAt right) validO built₁O noneOBuilt
  have rule₂D := input.actual_rule4a_observable_eq_none target view₂
    (frame.cursorAt distinguished) validD built₂D noneDBuilt
  have rule₂O := input.actual_rule4a_observable_eq_none target view₂
    (frame.cursorAt right) validO built₂O noneOBuilt
  have decisive₁ : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      compound₁D.prior.rule4aKey.constitutional.rule1a
      compound₁O.prior.rule4aKey.constitutional.rule1a ≠ Ordering.eq := by
    rw [rule₁D, rule₁O]
    exact decisive
  have decisive₂ : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      compound₂D.prior.rule4aKey.constitutional.rule1a
      compound₂O.prior.rule4aKey.constitutional.rule1a ≠ Ordering.eq := by
    rw [rule₂D, rule₂O]
    exact decisive
  have record₁ := input.compareLocalizedRerootCompoundThroughRule5_eq_rule1a_of_decisive
    compound₁D compound₁O decisive₁
  have record₂ := input.compareLocalizedRerootCompoundThroughRule5_eq_rule1a_of_decisive
    compound₂D compound₂O decisive₂
  have sameOrder : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      compound₁D.prior.rule4aKey.constitutional.rule1a
      compound₁O.prior.rule4aKey.constitutional.rule1a =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        compound₂D.prior.rule4aKey.constitutional.rule1a
        compound₂O.prior.rule4aKey.constitutional.rule1a := by
    rw [rule₁D, rule₁O, rule₂D, rule₂O]
  rw [input.compareAt_of_compoundKeys target view₁ frame distinguished right built₁D built₁O record₁,
    input.compareAt_of_compoundKeys target view₂ frame distinguished right built₂D built₂O record₂,
    sameOrder]

private theorem compareRuleMajorOccurrenceAt?_constitutional_swap_of_separatedArm
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (distinguished : Fin 4)
    (separated : input.ArmConstitutionalRule1aSeparated frame distinguished)
    (left : Fin 4)
    (leftOther : left ≠ distinguished) :
    input.compareRuleMajorOccurrenceAt? target (input.molecularView map₁ target) frame
        left distinguished =
      input.compareRuleMajorOccurrenceAt? target (input.molecularView map₂ target) frame
        left distinguished := by
  let view₁ := input.molecularView map₁ target
  let view₂ := input.molecularView map₂ target
  have validD := input.frameCursor_valid target frame computed distinguished
  have validO := input.frameCursor_valid target frame computed left
  obtain ⟨noneD, noneDBuilt⟩ := input.noneReader_rule4a (frame.cursorAt distinguished) validD
  obtain ⟨noneO, noneOBuilt⟩ := input.noneReader_rule4a (frame.cursorAt left) validO
  have decisive := rule1a_ne_swap (separated left leftOther noneD noneO noneDBuilt noneOBuilt)
  obtain ⟨compound₁D, built₁D⟩ := input.frameCursor_actualCompound_at_evaluationFuel target
    view₁ frame computed distinguished
  obtain ⟨compound₁O, built₁O⟩ := input.frameCursor_actualCompound_at_evaluationFuel target
    view₁ frame computed left
  obtain ⟨compound₂D, built₂D⟩ := input.frameCursor_actualCompound_at_evaluationFuel target
    view₂ frame computed distinguished
  obtain ⟨compound₂O, built₂O⟩ := input.frameCursor_actualCompound_at_evaluationFuel target
    view₂ frame computed left
  have rule₁D := input.actual_rule4a_observable_eq_none target view₁
    (frame.cursorAt distinguished) validD built₁D noneDBuilt
  have rule₁O := input.actual_rule4a_observable_eq_none target view₁
    (frame.cursorAt left) validO built₁O noneOBuilt
  have rule₂D := input.actual_rule4a_observable_eq_none target view₂
    (frame.cursorAt distinguished) validD built₂D noneDBuilt
  have rule₂O := input.actual_rule4a_observable_eq_none target view₂
    (frame.cursorAt left) validO built₂O noneOBuilt
  have decisive₁ : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      compound₁O.prior.rule4aKey.constitutional.rule1a
      compound₁D.prior.rule4aKey.constitutional.rule1a ≠ Ordering.eq := by
    rw [rule₁O, rule₁D]
    exact decisive
  have decisive₂ : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      compound₂O.prior.rule4aKey.constitutional.rule1a
      compound₂D.prior.rule4aKey.constitutional.rule1a ≠ Ordering.eq := by
    rw [rule₂O, rule₂D]
    exact decisive
  have record₁ := input.compareLocalizedRerootCompoundThroughRule5_eq_rule1a_of_decisive
    compound₁O compound₁D decisive₁
  have record₂ := input.compareLocalizedRerootCompoundThroughRule5_eq_rule1a_of_decisive
    compound₂O compound₂D decisive₂
  have sameOrder : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      compound₁O.prior.rule4aKey.constitutional.rule1a
      compound₁D.prior.rule4aKey.constitutional.rule1a =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        compound₂O.prior.rule4aKey.constitutional.rule1a
        compound₂D.prior.rule4aKey.constitutional.rule1a := by
    rw [rule₁O, rule₁D, rule₂O, rule₂D]
  rw [input.compareAt_of_compoundKeys target view₁ frame left distinguished built₁O built₁D record₁,
    input.compareAt_of_compoundKeys target view₂ frame left distinguished built₂O built₂D record₂,
    sameOrder]

private theorem compareRuleMajorOccurrenceAt?_eq_of_otherArms
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (distinguished : Fin 4)
    (agree : ∀ index, index ≠ distinguished →
      ∀ unit, input.ReachableArmDescriptorConsult target (frame.cursorAt index) unit →
        map₁ unit = map₂ unit)
    (left right : Fin 4)
    (leftOther : left ≠ distinguished)
    (rightOther : right ≠ distinguished) :
    input.compareRuleMajorOccurrenceAt? target (input.molecularView map₁ target) frame left right =
      input.compareRuleMajorOccurrenceAt? target (input.molecularView map₂ target)
        frame left right := by
  have leftKeys := input.buildActualRuleMajorCompoundRule45Key?_eq_of_molecularConsult target
    map₁ map₂ (frame.cursorAt left) (agree left leftOther)
    (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt left)
    Relation.ReflTransGen.refl
  have rightKeys := input.buildActualRuleMajorCompoundRule45Key?_eq_of_molecularConsult target
    map₁ map₂ (frame.cursorAt right) (agree right rightOther)
    (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt right)
    Relation.ReflTransGen.refl
  unfold compareRuleMajorOccurrenceAt?
  change (do
      let leftKey ← input.buildActualRuleMajorCompoundRule45Key? target
        (input.molecularView map₁ target) (localizedOccurrenceRerootEvaluationFuel carrierFuel)
        (frame.cursorAt left)
      let rightKey ← input.buildActualRuleMajorCompoundRule45Key? target
        (input.molecularView map₁ target) (localizedOccurrenceRerootEvaluationFuel carrierFuel)
        (frame.cursorAt right)
      some (localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey))) = _
  rw [leftKeys, rightKeys]

/-- Pairs that meet the distinguished arm are the Rule-1a decision with
`pseudo = false`. Self-pairs are `eq` and non-pseudo. Every other pair follows
from agreement on those arms' consult sets. -/
theorem compareRuleMajorOccurrenceAt?_eq_of_separatedArm
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (distinguished : Fin 4)
    (separated : input.ArmConstitutionalRule1aSeparated frame distinguished)
    (agree : ∀ index, index ≠ distinguished →
      ∀ unit, input.ReachableArmDescriptorConsult target (frame.cursorAt index) unit →
        map₁ unit = map₂ unit)
    (left right : Fin 4) :
    input.compareRuleMajorOccurrenceAt? target (input.molecularView map₁ target) frame left right =
      input.compareRuleMajorOccurrenceAt? target (input.molecularView map₂ target)
        frame left right := by
  by_cases sameCursor : left = right
  · subst sameCursor
    obtain ⟨key₁, built₁⟩ := input.frameCursor_actualCompound_at_evaluationFuel target
      (input.molecularView map₁ target) frame computed left
    obtain ⟨key₂, built₂⟩ := input.frameCursor_actualCompound_at_evaluationFuel target
      (input.molecularView map₂ target) frame computed left
    have leftRecord := input.compareAt_of_compoundKeys target (input.molecularView map₁ target)
      frame left left built₁ built₁ (input.compareLocalizedRerootCompoundThroughRule5_self key₁)
    have rightRecord := input.compareAt_of_compoundKeys target (input.molecularView map₂ target)
      frame left left built₂ built₂ (input.compareLocalizedRerootCompoundThroughRule5_self key₂)
    rw [leftRecord, rightRecord]
  · by_cases leftSeparated : left = distinguished
    · subst leftSeparated
      have rightOther : right ≠ left := by
        intro same
        exact sameCursor same.symm
      exact input.compareRuleMajorOccurrenceAt?_constitutional_of_separatedArm target
        map₁ map₂ frame computed left separated right rightOther
    · by_cases rightSeparated : right = distinguished
      · subst rightSeparated
        exact input.compareRuleMajorOccurrenceAt?_constitutional_swap_of_separatedArm target
          map₁ map₂ frame computed right separated left leftSeparated
      · exact input.compareRuleMajorOccurrenceAt?_eq_of_otherArms target map₁ map₂ frame
          computed distinguished agree left right leftSeparated rightSeparated

theorem ruleMajorSpatialEvidence?_eq_of_compiledSeparatedArm
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (distinguished : Fin 4)
    (separated : input.ArmConstitutionalRule1aSeparated frame distinguished)
    (agree : ∀ index, index ≠ distinguished →
      ∀ unit, input.ReachableArmDescriptorConsult target (frame.cursorAt index) unit →
        map₁ unit = map₂ unit) :
    input.ruleMajorSpatialEvidence? target (input.molecularView map₁ target) =
      input.ruleMajorSpatialEvidence? target (input.molecularView map₂ target) := by
  unfold ruleMajorSpatialEvidence?
  cases hcenter : input.localizedOccurrenceDescriptorCenter? target with
  | none =>
      simp only [instMonadOption, hcenter, Option.bind_none]
  | some center =>
      simp only [instMonadOption, hcenter, computed, Option.bind_some]
      have horder : safeTrackedOrderOf (input.compareRuleMajorOccurrenceAt? target
            (input.molecularView map₁ target) frame) =
          safeTrackedOrderOf (input.compareRuleMajorOccurrenceAt? target
            (input.molecularView map₂ target) frame) := by
        congr 1
        funext left right
        exact input.compareRuleMajorOccurrenceAt?_eq_of_separatedArm target map₁ map₂ frame
          computed distinguished separated agree left right
      rw [horder]

/-- Bare descriptor. A missing center, a refused tracked order, or a missing
coordinate gives the same `none` on both maps. -/
theorem ruleMajorDescriptor?_eq_of_compiledSeparatedArm
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (distinguished : Fin 4)
    (separated : input.ArmConstitutionalRule1aSeparated frame distinguished)
    (agree : ∀ index, index ≠ distinguished →
      ∀ unit, input.ReachableArmDescriptorConsult target (frame.cursorAt index) unit →
        map₁ unit = map₂ unit) :
    input.ruleMajorDescriptor? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptor? target (input.molecularView map₂ target) := by
  unfold ruleMajorDescriptor?
  rw [input.ruleMajorSpatialEvidence?_eq_of_compiledSeparatedArm target map₁ map₂ frame
    computed distinguished separated agree]

theorem ruleMajorDescriptorExec?_eq_of_compiledSeparatedArm
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (distinguished : Fin 4)
    (separated : input.ArmConstitutionalRule1aSeparated frame distinguished)
    (agree : ∀ index, index ≠ distinguished →
      ∀ unit, input.ReachableArmDescriptorConsult target (frame.cursorAt index) unit →
        map₁ unit = map₂ unit) :
    input.ruleMajorDescriptorExec? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptorExec? target (input.molecularView map₂ target) := by
  rw [input.ruleMajorDescriptorExec?_eq target (input.molecularView map₁ target),
    input.ruleMajorDescriptorExec?_eq target (input.molecularView map₂ target)]
  exact input.ruleMajorDescriptor?_eq_of_compiledSeparatedArm target map₁ map₂ frame
    computed distinguished separated agree

theorem ruleMajorDescriptor?_eq_of_absentFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (absent : input.localizedOccurrenceFourLigandFrame? target = none) :
    input.ruleMajorDescriptor? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptor? target (input.molecularView map₂ target) := by
  unfold ruleMajorDescriptor? ruleMajorSpatialEvidence?
  cases hcenter : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp only [instMonadOption, hcenter, Option.bind_none]
  | some center => simp only [instMonadOption, hcenter, absent, Option.bind_none, Option.bind_some]

theorem ruleMajorDescriptorExec?_eq_of_absentFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (absent : input.localizedOccurrenceFourLigandFrame? target = none) :
    input.ruleMajorDescriptorExec? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptorExec? target (input.molecularView map₂ target) := by
  rw [input.ruleMajorDescriptorExec?_eq target (input.molecularView map₁ target),
    input.ruleMajorDescriptorExec?_eq target (input.molecularView map₂ target)]
  exact input.ruleMajorDescriptor?_eq_of_absentFrame target map₁ map₂ absent

end CertifiedLocalizedCIPInput

namespace LocalizedRuleMajorReference

open CertifiedLocalizedCIPInput DeclarativeCIP

/-- The cyclic frame compiler supplies the actual frame. `SimpleBonded` and the
real detected unit are the source hypotheses of that compiler. Rule-1a
separation remains the case premise. -/
theorem ruleMajorDescriptor?_eq_of_cyclicSeparatedArm
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedCIPOccurrence (carrierFuel input))
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (distinguished : Fin 4)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph))
    (separated : ∀ frame, input.certified.localizedNoDoubleFourLigandFrameExec? target =
        some frame → input.certified.ArmConstitutionalRule1aSeparated frame distinguished)
    (agree : ∀ frame, input.certified.localizedNoDoubleFourLigandFrameExec? target = some frame →
      ∀ index, index ≠ distinguished →
        ∀ unit, input.certified.ReachableArmDescriptorConsult target (frame.cursorAt index) unit →
          map₁ unit = map₂ unit) :
    input.certified.ruleMajorDescriptor? target (input.certified.molecularView map₁ target) =
      input.certified.ruleMajorDescriptor? target (input.certified.molecularView map₂ target) := by
  let compilation := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
  have frameComputed : input.certified.localizedOccurrenceFourLigandFrame? target =
      some compilation.frame := by
    rw [← input.certified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
      target]
    exact compilation.frameComputed
  exact input.certified.ruleMajorDescriptor?_eq_of_compiledSeparatedArm target map₁ map₂
    compilation.frame frameComputed distinguished
    (separated compilation.frame compilation.frameComputed)
    (agree compilation.frame compilation.frameComputed)

theorem ruleMajorDescriptorExec?_eq_of_cyclicSeparatedArm
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedCIPOccurrence (carrierFuel input))
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (distinguished : Fin 4)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph))
    (separated : ∀ frame, input.certified.localizedNoDoubleFourLigandFrameExec? target =
        some frame → input.certified.ArmConstitutionalRule1aSeparated frame distinguished)
    (agree : ∀ frame, input.certified.localizedNoDoubleFourLigandFrameExec? target = some frame →
      ∀ index, index ≠ distinguished →
        ∀ unit, input.certified.ReachableArmDescriptorConsult target (frame.cursorAt index) unit →
          map₁ unit = map₂ unit) :
    input.certified.ruleMajorDescriptorExec? target (input.certified.molecularView map₁ target) =
      input.certified.ruleMajorDescriptorExec? target
        (input.certified.molecularView map₂ target) := by
  rw [input.certified.ruleMajorDescriptorExec?_eq target
      (input.certified.molecularView map₁ target),
    input.certified.ruleMajorDescriptorExec?_eq target
      (input.certified.molecularView map₂ target)]
  exact ruleMajorDescriptor?_eq_of_cyclicSeparatedArm input singleBonded target real unit
    targetUnit distinguished map₁ map₂ separated agree

end LocalizedRuleMajorReference

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameCursor_valid
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.frameCursor_actualCompound_at_evaluationFuel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ArmConstitutionalRule1aSeparated
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_eq_rule1a_of_decisive
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareRuleMajorOccurrenceAt?_eq_of_separatedArm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorSpatialEvidence?_eq_of_compiledSeparatedArm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptor?_eq_of_compiledSeparatedArm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptorExec?_eq_of_compiledSeparatedArm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptor?_eq_of_absentFrame
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptorExec?_eq_of_absentFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ruleMajorDescriptor?_eq_of_cyclicSeparatedArm
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ruleMajorDescriptorExec?_eq_of_cyclicSeparatedArm
