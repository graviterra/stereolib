import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeBuilder
import TetraStereo.OneCenter.LocalizedRerootCompoundOrderedBuilder
import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Executable
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! A compound Rules-4b/4c/5 assembly parameterized by its cumulative stage compiler.
The actual specialization retains the existing Rule-4a compiler for reference selection and
uses the rule-major cumulative compiler for Rules 4b, 4c, and 5. The two Rule-4b alternatives
are ordered by the existing full-vector `rankReadings` comparator. This module proves construction
and totality, not canonicality of that comparator or correctness of the compound comparison. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

abbrev RuleMajorCompoundStageCompiler (input : CertifiedLocalizedCIPInput)
    (carrierFuel : Nat) :=
  LocalizedCumulativeRule45Stage → input.LocalizedRerootCursor carrierFuel →
    Option input.LocalizedRerootCumulativeRule45Key

def buildRuleMajorCompoundRule4bcReadingWith?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS) : Option input.LocalizedRerootRule4bcReading := do
  match reference with
  | none =>
      let rule4bKey ← compileStage .rule4a cursor
      let rule4cKey ← compileStage .rule4cNoReference cursor
      some { reference? := none, rule4bKey := rule4bKey, rule4cKey := rule4cKey }
  | some reference =>
      let rule4bKey ← compileStage (.rule4b reference) cursor
      let rule4cKey ← compileStage (.rule4c reference) cursor
      some { reference? := some reference, rule4bKey := rule4bKey, rule4cKey := rule4cKey }

def buildRuleMajorCompoundRule4bcReadingsWith?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    List (Option RS) → Option (List input.LocalizedRerootRule4bcReading)
  | [] => some []
  | reference :: references => do
      let reading ← input.buildRuleMajorCompoundRule4bcReadingWith?
        compileStage cursor reference
      let readings ← input.buildRuleMajorCompoundRule4bcReadingsWith?
        compileStage cursor references
      some (reading :: readings)

def buildRuleMajorCompoundRule5ReadingWith?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading) :
    Option input.LocalizedRerootRule5Reading := do
  let commonR ← compileStage (localizedRule5StageFor prior.reference? .R) cursor
  let commonS ← compileStage (localizedRule5StageFor prior.reference? .S) cursor
  some { prior := prior, commonR := commonR, commonS := commonS }

def buildRuleMajorCompoundRule5ReadingsWith?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    List input.LocalizedRerootRule4bcReading →
      Option (List input.LocalizedRerootRule5Reading)
  | [] => some []
  | prior :: priors => do
      let reading ← input.buildRuleMajorCompoundRule5ReadingWith?
        compileStage cursor prior
      let readings ← input.buildRuleMajorCompoundRule5ReadingsWith?
        compileStage cursor priors
      some (reading :: readings)

/-- Generic proof-facing compound assembly.  It uses the caller's stage compiler for every
stage, retains the standard P-92 reference extraction and ranks the alternatives with the
existing `rankReadings` before Rule 5 is built. -/
def buildRuleMajorCompoundRule45KeyWith?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootCompoundRule45Key := do
  let rule4aKey ← compileStage .rule4a cursor
  let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
  let alternatives := localizedRule4bcReferenceAlternatives references
  let readings ← input.buildRuleMajorCompoundRule4bcReadingsWith?
    compileStage cursor alternatives
  let prior : input.LocalizedRerootCompoundRule4bcKey :=
    { rule4aKey := rule4aKey
      references := references
      referenceCountPriority := constitutionalRule4bReferenceCountPriority references
      readings := input.rankReadings readings }
  let rule5Readings ← input.buildRuleMajorCompoundRule5ReadingsWith?
    compileStage cursor prior.readings
  some { prior := prior, rule5Readings := rule5Readings }

theorem buildRuleMajorCompoundRule4bcReadingWith?_total
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (stageTotal : ∀ stage, ∃ key, compileStage stage cursor = some key) :
    ∀ reference, ∃ reading,
      input.buildRuleMajorCompoundRule4bcReadingWith? compileStage cursor reference = some reading := by
  intro reference
  cases reference with
  | none =>
      obtain ⟨key4b, h4b⟩ := stageTotal .rule4a
      obtain ⟨key4c, h4c⟩ := stageTotal .rule4cNoReference
      exact ⟨{ reference? := none, rule4bKey := key4b, rule4cKey := key4c }, by
        simp [buildRuleMajorCompoundRule4bcReadingWith?, h4b, h4c]⟩
  | some reference =>
      obtain ⟨key4b, h4b⟩ := stageTotal (.rule4b reference)
      obtain ⟨key4c, h4c⟩ := stageTotal (.rule4c reference)
      exact ⟨{ reference? := some reference, rule4bKey := key4b, rule4cKey := key4c }, by
        simp [buildRuleMajorCompoundRule4bcReadingWith?, h4b, h4c]⟩

theorem buildRuleMajorCompoundRule4bcReadingsWith?_total
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (stageTotal : ∀ stage, ∃ key, compileStage stage cursor = some key) :
    ∀ references, ∃ readings,
      input.buildRuleMajorCompoundRule4bcReadingsWith? compileStage cursor references =
        some readings := by
  intro references
  induction references with
  | nil => exact ⟨[], rfl⟩
  | cons reference references ih =>
      obtain ⟨reading, hreading⟩ :=
        input.buildRuleMajorCompoundRule4bcReadingWith?_total compileStage cursor stageTotal reference
      obtain ⟨readings, hreadings⟩ := ih
      exact ⟨reading :: readings, by
        simp [buildRuleMajorCompoundRule4bcReadingsWith?, hreading, hreadings]⟩

theorem buildRuleMajorCompoundRule5ReadingWith?_total
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (stageTotal : ∀ stage, ∃ key, compileStage stage cursor = some key)
    (prior : input.LocalizedRerootRule4bcReading) :
    ∃ reading, input.buildRuleMajorCompoundRule5ReadingWith? compileStage cursor prior =
      some reading := by
  obtain ⟨commonR, hR⟩ := stageTotal (localizedRule5StageFor prior.reference? .R)
  obtain ⟨commonS, hS⟩ := stageTotal (localizedRule5StageFor prior.reference? .S)
  exact ⟨{ prior := prior, commonR := commonR, commonS := commonS }, by
    simp [buildRuleMajorCompoundRule5ReadingWith?, hR, hS]⟩

theorem buildRuleMajorCompoundRule5ReadingsWith?_total
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (stageTotal : ∀ stage, ∃ key, compileStage stage cursor = some key) :
    ∀ priors, ∃ readings,
      input.buildRuleMajorCompoundRule5ReadingsWith? compileStage cursor priors =
        some readings := by
  intro priors
  induction priors with
  | nil => exact ⟨[], rfl⟩
  | cons prior priors ih =>
      obtain ⟨reading, hreading⟩ :=
        input.buildRuleMajorCompoundRule5ReadingWith?_total compileStage cursor stageTotal prior
      obtain ⟨readings, hreadings⟩ := ih
      exact ⟨reading :: readings, by
        simp [buildRuleMajorCompoundRule5ReadingsWith?, hreading, hreadings]⟩

theorem buildRuleMajorCompoundRule45KeyWith?_total
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (stageTotal : ∀ stage, ∃ key, compileStage stage cursor = some key) :
    ∃ compound, input.buildRuleMajorCompoundRule45KeyWith? compileStage cursor =
      some compound := by
  obtain ⟨rule4aKey, h4a⟩ := stageTotal .rule4a
  let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
  let alternatives := localizedRule4bcReferenceAlternatives references
  obtain ⟨readings, hreadings⟩ :=
    input.buildRuleMajorCompoundRule4bcReadingsWith?_total compileStage cursor stageTotal alternatives
  let prior : input.LocalizedRerootCompoundRule4bcKey :=
    { rule4aKey := rule4aKey
      references := references
      referenceCountPriority := constitutionalRule4bReferenceCountPriority references
      readings := input.rankReadings readings }
  obtain ⟨rule5Readings, hrule5⟩ :=
    input.buildRuleMajorCompoundRule5ReadingsWith?_total compileStage cursor stageTotal prior.readings
  refine ⟨{ prior := prior, rule5Readings := rule5Readings }, ?_⟩
  simp [buildRuleMajorCompoundRule45KeyWith?, h4a, hreadings, hrule5, prior,
    references, alternatives]

theorem buildRuleMajorCompoundRule4bcReadingWith?_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (left right : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (same : ∀ stage, left stage cursor = right stage cursor) :
    ∀ reference,
      input.buildRuleMajorCompoundRule4bcReadingWith? left cursor reference =
        input.buildRuleMajorCompoundRule4bcReadingWith? right cursor reference := by
  intro reference
  cases reference <;> simp [buildRuleMajorCompoundRule4bcReadingWith?, same]

theorem buildRuleMajorCompoundRule4bcReadingsWith?_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (left right : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (same : ∀ stage, left stage cursor = right stage cursor) :
    ∀ references,
      input.buildRuleMajorCompoundRule4bcReadingsWith? left cursor references =
        input.buildRuleMajorCompoundRule4bcReadingsWith? right cursor references := by
  intro references
  induction references with
  | nil => rfl
  | cons reference references ih =>
      simp [buildRuleMajorCompoundRule4bcReadingsWith?,
        input.buildRuleMajorCompoundRule4bcReadingWith?_eq left right cursor same reference,
        ih]

theorem buildRuleMajorCompoundRule5ReadingWith?_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (left right : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (same : ∀ stage, left stage cursor = right stage cursor)
    (prior : input.LocalizedRerootRule4bcReading) :
    input.buildRuleMajorCompoundRule5ReadingWith? left cursor prior =
      input.buildRuleMajorCompoundRule5ReadingWith? right cursor prior := by
  simp [buildRuleMajorCompoundRule5ReadingWith?, same]

theorem buildRuleMajorCompoundRule5ReadingsWith?_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (left right : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (same : ∀ stage, left stage cursor = right stage cursor) :
    ∀ priors,
      input.buildRuleMajorCompoundRule5ReadingsWith? left cursor priors =
        input.buildRuleMajorCompoundRule5ReadingsWith? right cursor priors := by
  intro priors
  induction priors with
  | nil => rfl
  | cons prior priors ih =>
      simp [buildRuleMajorCompoundRule5ReadingsWith?,
        input.buildRuleMajorCompoundRule5ReadingWith?_eq left right cursor same prior,
        ih]

theorem buildRuleMajorCompoundRule45KeyWith?_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (left right : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (same : ∀ stage, left stage cursor = right stage cursor) :
    input.buildRuleMajorCompoundRule45KeyWith? left cursor =
      input.buildRuleMajorCompoundRule45KeyWith? right cursor := by
  unfold buildRuleMajorCompoundRule45KeyWith?
  rw [same .rule4a]
  cases h : right .rule4a cursor with
  | none => rfl
  | some rule4aKey =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [input.buildRuleMajorCompoundRule4bcReadingsWith?_eq left right cursor same]
      cases hr : input.buildRuleMajorCompoundRule4bcReadingsWith? right cursor
          (localizedRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
      | none => rfl
      | some readings =>
          simp only [Option.bind_some]
          rw [input.buildRuleMajorCompoundRule5ReadingsWith?_eq
            left right cursor same (input.rankReadings readings)]

/-! ## Production and executable stage callbacks -/

noncomputable def ruleMajorCompoundStageCompiler
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) : input.RuleMajorCompoundStageCompiler carrierFuel :=
  fun stage cursor => match stage with
    | .rule4a => input.buildLocalizedRerootCumulativeRule45Key?
        .rule4a target view fuel cursor
    | other => input.buildRuleMajorCumulativeWithRead? other read fuel cursor

def ruleMajorCompoundStageCompilerExec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) : input.RuleMajorCompoundStageCompiler carrierFuel :=
  fun stage cursor => match stage with
    | .rule4a => input.buildLocalizedRerootCumulativeRule45KeyExec?
        .rule4a target view fuel cursor
    | other => input.buildRuleMajorCumulativeWithReadExec? other read fuel cursor

theorem ruleMajorCompoundStageCompiler_exec_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ stage,
      input.ruleMajorCompoundStageCompiler target view read fuel stage cursor =
        input.ruleMajorCompoundStageCompilerExec target view read fuel stage cursor := by
  intro stage
  cases stage with
  | rule4a =>
      exact (input.buildLocalizedRerootCumulativeRule45KeyExec?_eq_build
        .rule4a target view fuel cursor).symm
  | rule4b reference =>
      exact (input.buildRuleMajorCumulativeWithReadExec_eq (.rule4b reference) read fuel cursor).symm
  | rule4cNoReference =>
      exact (input.buildRuleMajorCumulativeWithReadExec_eq .rule4cNoReference read fuel cursor).symm
  | rule4c reference =>
      exact (input.buildRuleMajorCumulativeWithReadExec_eq (.rule4c reference) read fuel cursor).symm
  | rule5NoRule4bReference reference =>
      exact (input.buildRuleMajorCumulativeWithReadExec_eq
        (.rule5NoRule4bReference reference) read fuel cursor).symm
  | rule5 reference common =>
      exact (input.buildRuleMajorCumulativeWithReadExec_eq
        (.rule5 reference common) read fuel cursor).symm

noncomputable def buildRuleMajorCompoundRule45Key?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootCompoundRule45Key :=
  input.buildRuleMajorCompoundRule45KeyWith?
    (input.ruleMajorCompoundStageCompiler target view read fuel) cursor

def buildRuleMajorCompoundRule45KeyExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootCompoundRule45Key :=
  input.buildRuleMajorCompoundRule45KeyWith?
    (input.ruleMajorCompoundStageCompilerExec target view read fuel) cursor

theorem buildRuleMajorCompoundRule45KeyExec?_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildRuleMajorCompoundRule45KeyExec? target view read fuel cursor =
      input.buildRuleMajorCompoundRule45Key? target view read fuel cursor := by
  exact (input.buildRuleMajorCompoundRule45KeyWith?_eq
    (input.ruleMajorCompoundStageCompiler target view read fuel)
    (input.ruleMajorCompoundStageCompilerExec target view read fuel)
    cursor (input.ruleMajorCompoundStageCompiler_exec_eq target view read fuel cursor)).symm

theorem ruleMajorCompoundStageCompiler_total_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∀ stage, ∃ key,
      input.ruleMajorCompoundStageCompiler target view read
        (2 * (carrierFuel + 1)) stage cursor = some key := by
  intro stage
  cases stage with
  | rule4a =>
      exact input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
        .rule4a target view cursor valid
  | rule4b reference =>
      exact input.exists_buildRuleMajorCumulativeWithRead_at_twice
        (.rule4b reference) read cursor valid
  | rule4cNoReference =>
      exact input.exists_buildRuleMajorCumulativeWithRead_at_twice
        .rule4cNoReference read cursor valid
  | rule4c reference =>
      exact input.exists_buildRuleMajorCumulativeWithRead_at_twice
        (.rule4c reference) read cursor valid
  | rule5NoRule4bReference reference =>
      exact input.exists_buildRuleMajorCumulativeWithRead_at_twice
        (.rule5NoRule4bReference reference) read cursor valid
  | rule5 reference common =>
      exact input.exists_buildRuleMajorCumulativeWithRead_at_twice
        (.rule5 reference common) read cursor valid

theorem exists_buildRuleMajorCompoundRule45Key_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ compound, input.buildRuleMajorCompoundRule45Key?
      target view read (2 * (carrierFuel + 1)) cursor = some compound := by
  exact input.buildRuleMajorCompoundRule45KeyWith?_total
    (input.ruleMajorCompoundStageCompiler target view read (2 * (carrierFuel + 1)))
    cursor (input.ruleMajorCompoundStageCompiler_total_at_twice
      target view read cursor valid)

/-! ## Reader-consistent production entry points -/

/-- Actual compound entry point. The reader is fixed to the same localized dependency view used
by the original Rule-4a reference selector, so the P-92 reference population and later rule-major
readings observe one consistent input. Alternative ordering continues to use `rankReadings`; this
entry point establishes construction and totality, not canonicality under the new comparator. -/
noncomputable def buildActualRuleMajorCompoundRule45Key?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootCompoundRule45Key :=
  input.buildRuleMajorCompoundRule45Key? target view
    (input.localizedDependencyLabel target view) fuel cursor

/-- Executable actual compound entry point, with the same reader consistency as the proof-facing
entry point. -/
def buildActualRuleMajorCompoundRule45KeyExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootCompoundRule45Key :=
  input.buildRuleMajorCompoundRule45KeyExec? target view
    (input.localizedDependencyLabel target view) fuel cursor

theorem buildActualRuleMajorCompoundRule45KeyExec?_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildActualRuleMajorCompoundRule45KeyExec? target view fuel cursor =
      input.buildActualRuleMajorCompoundRule45Key? target view fuel cursor :=
  input.buildRuleMajorCompoundRule45KeyExec?_eq target view
    (input.localizedDependencyLabel target view) fuel cursor

theorem exists_buildActualRuleMajorCompoundRule45Key_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ compound, input.buildActualRuleMajorCompoundRule45Key? target view
      (2 * (carrierFuel + 1)) cursor = some compound :=
  input.exists_buildRuleMajorCompoundRule45Key_at_twice target view
    (input.localizedDependencyLabel target view) cursor valid

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorCompoundStageCompiler
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule4bcReadingWith?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule4bcReadingsWith?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule5ReadingWith?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule5ReadingsWith?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule45KeyWith?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule4bcReadingWith?_total
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule4bcReadingsWith?_total
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule5ReadingWith?_total
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule5ReadingsWith?_total
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule45KeyWith?_total
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule4bcReadingWith?_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule4bcReadingsWith?_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule5ReadingWith?_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule5ReadingsWith?_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule45KeyWith?_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorCompoundStageCompiler
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorCompoundStageCompilerExec
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorCompoundStageCompiler_exec_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule45Key?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule45KeyExec?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule45KeyExec?_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorCompoundStageCompiler_total_at_twice
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildActualRuleMajorCompoundRule45Key?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildActualRuleMajorCompoundRule45KeyExec?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildActualRuleMajorCompoundRule45KeyExec?_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_buildActualRuleMajorCompoundRule45Key_at_twice
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule45KeyExec?_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_buildRuleMajorCompoundRule45Key_at_twice
