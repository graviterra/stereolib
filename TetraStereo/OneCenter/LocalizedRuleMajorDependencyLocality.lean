import TetraStereo.OneCenter.LocalizedRetainedDependencyLocality
import TetraStereo.OneCenter.LocalizedRuleMajorReferencePipeline
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Rule-major locality on the actual arm support

The approved reader locality says that `molecularReader` and the old cumulative
builder depend only on `ReachableArmDescriptorConsult`. This module ports that
congruence to `buildRuleMajorCumulativeWithRead?`, then through the hybrid
rule-major compound compiler and the actual bare and executable descriptors.

`.rule4a` stays on `buildLocalizedRerootCumulativeRule45Key?` of
`molecularView`. Later stages use `buildRuleMajorCumulativeWithRead?` of
`molecularReader` for the same map. The start cursor is arbitrary, including a
rootward cursor. Agreement on the reachable consult set is enough at every
fuel; that set may be broader than the cursors one fuel is forced to read.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

open DeclarativeCIP

/-- Two readers that agree on every executable child reachable from `start`
build the same rule-major `Option` key at every fuel. Equal child results are
sorted by the same `sortRuleMajorCumulativeKeys` and assembled by the same
`localizedCumulativeRule45StepKey`. -/
theorem buildRuleMajorCumulativeWithRead?_eq_of_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (first second : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (agree : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      Relation.ReflTransGen (E input) start cursor → first cursor = second cursor) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) start cursor →
      input.buildRuleMajorCumulativeWithRead? stage first fuel cursor =
        input.buildRuleMajorCumulativeWithRead? stage second fuel cursor
  | 0, cursor, reachable => by
      unfold buildRuleMajorCumulativeWithRead?
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp
      | some children =>
          by_cases terminal : children = []
          · have cursorAgree := agree cursor reachable
            simp [terminal, cursorAgree]
          · simp [terminal]
  | fuel + 1, cursor, reachable => by
      unfold buildRuleMajorCumulativeWithRead?
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp
      | some children =>
          by_cases terminal : children = []
          · have cursorAgree := agree cursor reachable
            simp [terminal, cursorAgree]
          · have childrenEq : children = input.executableLocalizedRerootChildren cursor := by
              rw [input.localizedRerootChildren?_eq_some_executable cursor] at childrenComputed
              exact (Option.some.inj childrenComputed).symm
            have mapCongr : children.mapM
                  (input.buildRuleMajorCumulativeWithRead? stage first fuel) =
                children.mapM
                  (input.buildRuleMajorCumulativeWithRead? stage second fuel) := by
              refine list_mapM_congr_on
                (input.buildRuleMajorCumulativeWithRead? stage first fuel)
                (input.buildRuleMajorCumulativeWithRead? stage second fuel)
                children ?_
              intro child childPresent
              have childEdge : E input cursor child := by
                unfold E
                rwa [← childrenEq]
              have childReach : Relation.ReflTransGen (E input) cursor child :=
                Relation.ReflTransGen.single childEdge
              exact buildRuleMajorCumulativeWithRead?_eq_of_reachable
                input stage first second start agree fuel child (reachable.trans childReach)
            have cursorAgree := agree cursor reachable
            simp [terminal, cursorAgree, mapCongr]

/-- The executable rule-major builder agrees on the same reachable cursors,
by `buildRuleMajorCumulativeWithReadExec_eq`. -/
theorem buildRuleMajorCumulativeWithReadExec?_eq_of_reachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (first second : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (agree : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      Relation.ReflTransGen (E input) start cursor → first cursor = second cursor)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor) :
    input.buildRuleMajorCumulativeWithReadExec? stage first fuel cursor =
      input.buildRuleMajorCumulativeWithReadExec? stage second fuel cursor := by
  rw [input.buildRuleMajorCumulativeWithReadExec_eq stage first fuel cursor,
    input.buildRuleMajorCumulativeWithReadExec_eq stage second fuel cursor]
  exact input.buildRuleMajorCumulativeWithRead?_eq_of_reachable
    stage first second start agree fuel cursor reachable

private theorem buildLocalizedRerootCumulativeRule45Key?_eq_molecularReader
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRerootCumulativeRule45Key? .rule4a target
        (input.molecularView map target) fuel cursor =
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
        (input.molecularReader map target) fuel cursor := by
  rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
    .rule4a target (input.molecularView map target) fuel cursor]
  unfold molecularReader
  rfl

private theorem buildRuleMajorCumulativeWithRead?_eq_of_molecularConsult
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (agree : ∀ unit, input.ReachableArmDescriptorConsult target start unit →
      map₁ unit = map₂ unit)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor) :
    input.buildRuleMajorCumulativeWithRead? stage (input.molecularReader map₁ target)
        fuel cursor =
      input.buildRuleMajorCumulativeWithRead? stage (input.molecularReader map₂ target)
        fuel cursor :=
  input.buildRuleMajorCumulativeWithRead?_eq_of_reachable stage
    (input.molecularReader map₁ target) (input.molecularReader map₂ target) start
    (fun reached reachedFromStart =>
      input.molecularReader_eq_of_reachableArmDescriptorConsult
        target start map₁ map₂ agree reached reachedFromStart)
    fuel cursor reachable

/-- Hybrid compiler. Rule 4a is the old builder on each map's `molecularView`.
Later stages are the revised builder on each map's `molecularReader`. -/
theorem ruleMajorCompoundStageCompiler_eq_of_molecularConsult
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (start : input.LocalizedRerootCursor carrierFuel)
    (agree : ∀ unit, input.ReachableArmDescriptorConsult target start unit →
      map₁ unit = map₂ unit)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor) :
    ∀ stage,
      input.ruleMajorCompoundStageCompiler target (input.molecularView map₁ target)
          (input.molecularReader map₁ target) fuel stage cursor =
        input.ruleMajorCompoundStageCompiler target (input.molecularView map₂ target)
          (input.molecularReader map₂ target) fuel stage cursor := by
  intro stage
  unfold ruleMajorCompoundStageCompiler
  cases stage with
  | rule4a =>
      calc
        input.buildLocalizedRerootCumulativeRule45Key? .rule4a target
            (input.molecularView map₁ target) fuel cursor
          = input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
              (input.molecularReader map₁ target) fuel cursor :=
            input.buildLocalizedRerootCumulativeRule45Key?_eq_molecularReader
              target map₁ fuel cursor
        _ = input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
              (input.molecularReader map₂ target) fuel cursor :=
            input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_of_reachableArmDescriptorConsult
              .rule4a target start map₁ map₂ agree fuel cursor reachable
        _ = input.buildLocalizedRerootCumulativeRule45Key? .rule4a target
              (input.molecularView map₂ target) fuel cursor :=
            (input.buildLocalizedRerootCumulativeRule45Key?_eq_molecularReader
              target map₂ fuel cursor).symm
  | rule4b reference =>
      exact input.buildRuleMajorCumulativeWithRead?_eq_of_molecularConsult
        (.rule4b reference) target start map₁ map₂ agree fuel cursor reachable
  | rule4cNoReference =>
      exact input.buildRuleMajorCumulativeWithRead?_eq_of_molecularConsult
        .rule4cNoReference target start map₁ map₂ agree fuel cursor reachable
  | rule4c reference =>
      exact input.buildRuleMajorCumulativeWithRead?_eq_of_molecularConsult
        (.rule4c reference) target start map₁ map₂ agree fuel cursor reachable
  | rule5NoRule4bReference reference =>
      exact input.buildRuleMajorCumulativeWithRead?_eq_of_molecularConsult
        (.rule5NoRule4bReference reference) target start map₁ map₂ agree fuel cursor reachable
  | rule5 reference common =>
      exact input.buildRuleMajorCumulativeWithRead?_eq_of_molecularConsult
        (.rule5 reference common) target start map₁ map₂ agree fuel cursor reachable

theorem ruleMajorCompoundStageCompilerExec_eq_of_molecularConsult
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (start : input.LocalizedRerootCursor carrierFuel)
    (agree : ∀ unit, input.ReachableArmDescriptorConsult target start unit →
      map₁ unit = map₂ unit)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor) :
    ∀ stage,
      input.ruleMajorCompoundStageCompilerExec target (input.molecularView map₁ target)
          (input.molecularReader map₁ target) fuel stage cursor =
        input.ruleMajorCompoundStageCompilerExec target (input.molecularView map₂ target)
          (input.molecularReader map₂ target) fuel stage cursor := by
  intro stage
  rw [← input.ruleMajorCompoundStageCompiler_exec_eq target
      (input.molecularView map₁ target) (input.molecularReader map₁ target) fuel cursor stage,
    ← input.ruleMajorCompoundStageCompiler_exec_eq target
      (input.molecularView map₂ target) (input.molecularReader map₂ target) fuel cursor stage]
  exact input.ruleMajorCompoundStageCompiler_eq_of_molecularConsult
    target map₁ map₂ start agree fuel cursor reachable stage

/-- Stage agreement gives the same compound, including the references derived from
the Rule-4a key and the `rankReadings` order. A `none` stage stays `none`. -/
theorem buildRuleMajorCompoundRule45Key?_eq_of_molecularConsult
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (start : input.LocalizedRerootCursor carrierFuel)
    (agree : ∀ unit, input.ReachableArmDescriptorConsult target start unit →
      map₁ unit = map₂ unit)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor) :
    input.buildRuleMajorCompoundRule45Key? target (input.molecularView map₁ target)
        (input.molecularReader map₁ target) fuel cursor =
      input.buildRuleMajorCompoundRule45Key? target (input.molecularView map₂ target)
        (input.molecularReader map₂ target) fuel cursor := by
  unfold buildRuleMajorCompoundRule45Key?
  exact input.buildRuleMajorCompoundRule45KeyWith?_eq
    (input.ruleMajorCompoundStageCompiler target (input.molecularView map₁ target)
      (input.molecularReader map₁ target) fuel)
    (input.ruleMajorCompoundStageCompiler target (input.molecularView map₂ target)
      (input.molecularReader map₂ target) fuel)
    cursor
    (fun stage => input.ruleMajorCompoundStageCompiler_eq_of_molecularConsult
      target map₁ map₂ start agree fuel cursor reachable stage)

theorem buildActualRuleMajorCompoundRule45Key?_eq_of_molecularConsult
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (start : input.LocalizedRerootCursor carrierFuel)
    (agree : ∀ unit, input.ReachableArmDescriptorConsult target start unit →
      map₁ unit = map₂ unit)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor) :
    input.buildActualRuleMajorCompoundRule45Key? target (input.molecularView map₁ target)
        fuel cursor =
      input.buildActualRuleMajorCompoundRule45Key? target (input.molecularView map₂ target)
        fuel cursor := by
  unfold buildActualRuleMajorCompoundRule45Key?
  exact input.buildRuleMajorCompoundRule45Key?_eq_of_molecularConsult
    target map₁ map₂ start agree fuel cursor reachable

theorem buildActualRuleMajorCompoundRule45KeyExec?_eq_of_molecularConsult
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (start : input.LocalizedRerootCursor carrierFuel)
    (agree : ∀ unit, input.ReachableArmDescriptorConsult target start unit →
      map₁ unit = map₂ unit)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor) :
    input.buildActualRuleMajorCompoundRule45KeyExec? target (input.molecularView map₁ target)
        fuel cursor =
      input.buildActualRuleMajorCompoundRule45KeyExec? target (input.molecularView map₂ target)
        fuel cursor := by
  rw [input.buildActualRuleMajorCompoundRule45KeyExec?_eq target
      (input.molecularView map₁ target) fuel cursor,
    input.buildActualRuleMajorCompoundRule45KeyExec?_eq target
      (input.molecularView map₂ target) fuel cursor]
  exact input.buildActualRuleMajorCompoundRule45Key?_eq_of_molecularConsult
    target map₁ map₂ start agree fuel cursor reachable

/-- Pairwise rule-major comparison at the evaluation fuel. The hypothesis is the
union of the two arm supports, with no comparison-success assumption. -/
theorem compareRuleMajorOccurrenceAt?_eq_of_armConsult
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (left right : Fin 4)
    (agree : ∀ unit,
      input.ReachableArmDescriptorConsult target (frame.cursorAt left) unit ∨
        input.ReachableArmDescriptorConsult target (frame.cursorAt right) unit →
      map₁ unit = map₂ unit) :
    input.compareRuleMajorOccurrenceAt? target (input.molecularView map₁ target) frame left right =
      input.compareRuleMajorOccurrenceAt? target (input.molecularView map₂ target)
        frame left right := by
  unfold compareRuleMajorOccurrenceAt?
  have leftBuilt :=
    input.buildActualRuleMajorCompoundRule45Key?_eq_of_molecularConsult target map₁ map₂
      (frame.cursorAt left)
      (fun unit consulted => agree unit (Or.inl consulted))
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (frame.cursorAt left) Relation.ReflTransGen.refl
  have rightBuilt :=
    input.buildActualRuleMajorCompoundRule45Key?_eq_of_molecularConsult target map₁ map₂
      (frame.cursorAt right)
      (fun unit consulted => agree unit (Or.inr consulted))
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      (frame.cursorAt right) Relation.ReflTransGen.refl
  change (do
      let leftKey ← input.buildActualRuleMajorCompoundRule45Key? target
        (input.molecularView map₁ target) (localizedOccurrenceRerootEvaluationFuel carrierFuel)
        (frame.cursorAt left)
      let rightKey ← input.buildActualRuleMajorCompoundRule45Key? target
        (input.molecularView map₁ target) (localizedOccurrenceRerootEvaluationFuel carrierFuel)
        (frame.cursorAt right)
      some (localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey))) = _
  rw [leftBuilt, rightBuilt]

theorem compareRuleMajorOccurrenceExecAt?_eq_of_armConsult
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (left right : Fin 4)
    (agree : ∀ unit,
      input.ReachableArmDescriptorConsult target (frame.cursorAt left) unit ∨
        input.ReachableArmDescriptorConsult target (frame.cursorAt right) unit →
      map₁ unit = map₂ unit) :
    input.compareRuleMajorOccurrenceExecAt? target (input.molecularView map₁ target)
        frame left right =
      input.compareRuleMajorOccurrenceExecAt? target (input.molecularView map₂ target)
        frame left right := by
  rw [input.compareRuleMajorOccurrenceExecAt?_eq target (input.molecularView map₁ target)
      frame left right,
    input.compareRuleMajorOccurrenceExecAt?_eq target (input.molecularView map₂ target)
      frame left right]
  exact input.compareRuleMajorOccurrenceAt?_eq_of_armConsult
    target map₁ map₂ frame left right agree

/-- Detected occurrences consulted from any of the four actual frame cursors. -/
def FrameArmDescriptorConsult
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (unit : DetectedOccurrence input.moleculeGraph) : Prop :=
  ∃ index : Fin 4, input.ReachableArmDescriptorConsult target (frame.cursorAt index) unit

private theorem ruleMajorSpatialEvidence?_eq_of_frameArmConsult
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (agree : ∀ frame unit,
      input.localizedOccurrenceFourLigandFrame? target = some frame →
        input.FrameArmDescriptorConsult target frame unit →
          map₁ unit = map₂ unit) :
    input.ruleMajorSpatialEvidence? target (input.molecularView map₁ target) =
      input.ruleMajorSpatialEvidence? target (input.molecularView map₂ target) := by
  unfold ruleMajorSpatialEvidence?
  cases hcenter : input.localizedOccurrenceDescriptorCenter? target with
  | none =>
      simp only [instMonadOption, hcenter, Option.bind_none]
  | some center =>
      cases hframe : input.localizedOccurrenceFourLigandFrame? target with
      | none =>
          simp only [instMonadOption, hcenter, hframe, Option.bind_none, Option.bind_some]
      | some frame =>
          have horder :
              safeTrackedOrderOf (input.compareRuleMajorOccurrenceAt? target
                  (input.molecularView map₁ target) frame) =
                safeTrackedOrderOf (input.compareRuleMajorOccurrenceAt? target
                  (input.molecularView map₂ target) frame) := by
            congr 1
            funext left right
            exact input.compareRuleMajorOccurrenceAt?_eq_of_armConsult target map₁ map₂
              frame left right
              (fun unit consulted => by
                cases consulted with
                | inl leftConsulted =>
                    exact agree frame unit hframe ⟨left, leftConsulted⟩
                | inr rightConsulted =>
                    exact agree frame unit hframe ⟨right, rightConsulted⟩)
          simp only [instMonadOption, hcenter, hframe, Option.bind_some]
          rw [horder]

/-- Bare `ruleMajorDescriptor?` on the two molecular views. The support is the
union of the computed frame's arm consults. -/
theorem ruleMajorDescriptor?_eq_of_frameArmConsult
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (agree : ∀ frame unit,
      input.localizedOccurrenceFourLigandFrame? target = some frame →
        input.FrameArmDescriptorConsult target frame unit →
          map₁ unit = map₂ unit) :
    input.ruleMajorDescriptor? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptor? target (input.molecularView map₂ target) := by
  unfold ruleMajorDescriptor?
  rw [input.ruleMajorSpatialEvidence?_eq_of_frameArmConsult target map₁ map₂ agree]

/-- Executable descriptor, including the noDouble frame path inside
`ruleMajorSpatialEvidenceExec?`, by `ruleMajorDescriptorExec?_eq`. -/
theorem ruleMajorDescriptorExec?_eq_of_frameArmConsult
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (agree : ∀ frame unit,
      input.localizedOccurrenceFourLigandFrame? target = some frame →
        input.FrameArmDescriptorConsult target frame unit →
          map₁ unit = map₂ unit) :
    input.ruleMajorDescriptorExec? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptorExec? target (input.molecularView map₂ target) := by
  rw [input.ruleMajorDescriptorExec?_eq target (input.molecularView map₁ target),
    input.ruleMajorDescriptorExec?_eq target (input.molecularView map₂ target)]
  exact input.ruleMajorDescriptor?_eq_of_frameArmConsult target map₁ map₂ agree

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?_eq_of_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithReadExec?_eq_of_reachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorCompoundStageCompiler_eq_of_molecularConsult
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorCompoundStageCompilerExec_eq_of_molecularConsult
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule45Key?_eq_of_molecularConsult
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildActualRuleMajorCompoundRule45Key?_eq_of_molecularConsult
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildActualRuleMajorCompoundRule45KeyExec?_eq_of_molecularConsult
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareRuleMajorOccurrenceAt?_eq_of_armConsult
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareRuleMajorOccurrenceExecAt?_eq_of_armConsult
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.FrameArmDescriptorConsult
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptor?_eq_of_frameArmConsult
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptorExec?_eq_of_frameArmConsult
