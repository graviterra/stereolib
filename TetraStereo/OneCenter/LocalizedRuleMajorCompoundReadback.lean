import TetraStereo.OneCenter.LocalizedRuleMajorCompoundBuilder
import TetraStereo.OneCenter.LocalizedRuleMajorRule4aAgreement
import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Exact success inversion for the generic whole-rule compound builder. A successful compound
key records the same Rule-4a key selected by the stage compiler, the exact P-92 references and
count, the actual unranked alternatives returned by the readings builder, and the actual Rule-5
readings builder result. Single Rule-4b/4c alternative readback identifies the exact stage calls
used for either a reference or the no-reference case. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

private theorem buildRuleMajorCompoundRule4bcReadingWith?_of_stageBuilds
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS)
    (rule4bKey rule4cKey : input.LocalizedRerootCumulativeRule45Key)
    (rule4bBuilt :
      (match reference with
        | none => compileStage .rule4a cursor
        | some selected => compileStage (.rule4b selected) cursor) = some rule4bKey)
    (rule4cBuilt :
      (match reference with
        | none => compileStage .rule4cNoReference cursor
        | some selected => compileStage (.rule4c selected) cursor) = some rule4cKey) :
    input.buildRuleMajorCompoundRule4bcReadingWith? compileStage cursor reference =
      some (LocalizedRerootRule4bcReading.mk reference rule4bKey rule4cKey) := by
  cases reference with
  | none =>
      change compileStage .rule4a cursor = some rule4bKey at rule4bBuilt
      change compileStage .rule4cNoReference cursor = some rule4cKey at rule4cBuilt
      simp [buildRuleMajorCompoundRule4bcReadingWith?, rule4bBuilt, rule4cBuilt]
  | some selected =>
      change compileStage (.rule4b selected) cursor = some rule4bKey at rule4bBuilt
      change compileStage (.rule4c selected) cursor = some rule4cKey at rule4cBuilt
      simp [buildRuleMajorCompoundRule4bcReadingWith?, rule4bBuilt, rule4cBuilt]

/-- A successful single alternative is exactly the pair of stage builds used to construct it.
For `none`, Rule 4b is the original `.rule4a` key and Rule 4c is `.rule4cNoReference`; for a
selected reference, the builders use the matching `.rule4b` and `.rule4c` stages. -/
theorem buildRuleMajorCompoundRule4bcReadingWith?_eq_some_iff_stageBuilds
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS)
    (reading : input.LocalizedRerootRule4bcReading) :
    input.buildRuleMajorCompoundRule4bcReadingWith? compileStage cursor reference =
        some reading ↔
      ∃ rule4bKey rule4cKey,
        ((match reference with
          | none => compileStage .rule4a cursor
          | some selected => compileStage (.rule4b selected) cursor) = some rule4bKey) ∧
        ((match reference with
          | none => compileStage .rule4cNoReference cursor
          | some selected => compileStage (.rule4c selected) cursor) = some rule4cKey) ∧
        reading.reference? = reference ∧
        reading.rule4bKey = rule4bKey ∧
        reading.rule4cKey = rule4cKey := by
  cases reference with
  | none =>
      constructor
      · intro computed
        unfold buildRuleMajorCompoundRule4bcReadingWith? at computed
        obtain ⟨rule4bKey, rule4bComputed, tail⟩ :=
          Option.bind_eq_some_iff.mp computed
        obtain ⟨rule4cKey, rule4cComputed, result⟩ :=
          Option.bind_eq_some_iff.mp tail
        have readingEq := Option.some.inj result
        cases reading with
        | mk readingReference readingRule4bKey readingRule4cKey =>
            simp only [LocalizedRerootRule4bcReading.mk.injEq] at readingEq
            exact ⟨rule4bKey, rule4cKey, rule4bComputed, rule4cComputed,
              readingEq.1.symm, readingEq.2.1.symm, readingEq.2.2.symm⟩
      · rintro ⟨rule4bKey, rule4cKey, rule4bComputed, rule4cComputed,
          referenceEq, rule4bEq, rule4cEq⟩
        have build := buildRuleMajorCompoundRule4bcReadingWith?_of_stageBuilds
          input compileStage cursor none rule4bKey rule4cKey rule4bComputed rule4cComputed
        have readingEq : reading =
            LocalizedRerootRule4bcReading.mk none rule4bKey rule4cKey := by
          cases reading with
          | mk readingReference readingRule4bKey readingRule4cKey =>
            simp at referenceEq rule4bEq rule4cEq
            cases referenceEq
            cases rule4bEq
            cases rule4cEq
            rfl
        rw [readingEq]
        exact build
  | some selected =>
      constructor
      · intro computed
        unfold buildRuleMajorCompoundRule4bcReadingWith? at computed
        obtain ⟨rule4bKey, rule4bComputed, tail⟩ :=
          Option.bind_eq_some_iff.mp computed
        obtain ⟨rule4cKey, rule4cComputed, result⟩ :=
          Option.bind_eq_some_iff.mp tail
        have readingEq := Option.some.inj result
        cases reading with
        | mk readingReference readingRule4bKey readingRule4cKey =>
            simp only [LocalizedRerootRule4bcReading.mk.injEq] at readingEq
            exact ⟨rule4bKey, rule4cKey, rule4bComputed, rule4cComputed,
              readingEq.1.symm, readingEq.2.1.symm, readingEq.2.2.symm⟩
      · rintro ⟨rule4bKey, rule4cKey, rule4bComputed, rule4cComputed,
          referenceEq, rule4bEq, rule4cEq⟩
        have build := buildRuleMajorCompoundRule4bcReadingWith?_of_stageBuilds
          input compileStage cursor (some selected) rule4bKey rule4cKey
          rule4bComputed rule4cComputed
        have readingEq : reading =
            LocalizedRerootRule4bcReading.mk (some selected) rule4bKey rule4cKey := by
          cases reading with
          | mk readingReference readingRule4bKey readingRule4cKey =>
            simp at referenceEq rule4bEq rule4cEq
            cases referenceEq
            cases rule4bEq
            cases rule4cEq
            rfl
        rw [readingEq]
        exact build

/-- Invert a successful generic compound build into its exact Rule-4a selection, P-92 data,
raw alternative readings, and Rule-5 readings. The `rawReadings` witness is before the existing
`rankReadings` permutation; the compound stores exactly that ranked list. -/
theorem buildRuleMajorCompoundRule45KeyWith?_readback
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {compound : input.LocalizedRerootCompoundRule45Key}
    (built : input.buildRuleMajorCompoundRule45KeyWith? compileStage cursor =
      some compound) :
    compileStage .rule4a cursor = some compound.prior.rule4aKey ∧
      compound.prior.references =
        localizedRule4bReferencesFromRankedLabels compound.prior.rule4aKey.rankedLabels ∧
      compound.prior.referenceCountPriority =
        constitutionalRule4bReferenceCountPriority compound.prior.references ∧
      ∃ rawReadings,
        input.buildRuleMajorCompoundRule4bcReadingsWith? compileStage cursor
          (localizedRule4bcReferenceAlternatives compound.prior.references) =
            some rawReadings ∧
          compound.prior.readings = input.rankReadings rawReadings ∧
          input.buildRuleMajorCompoundRule5ReadingsWith? compileStage cursor
            compound.prior.readings = some compound.rule5Readings := by
  unfold buildRuleMajorCompoundRule45KeyWith? at built
  obtain ⟨rule4aKey, rule4aBuilt, continuation⟩ :=
    Option.bind_eq_some_iff.mp built
  let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
  let alternatives := localizedRule4bcReferenceAlternatives references
  change (do
    let readings ← input.buildRuleMajorCompoundRule4bcReadingsWith?
      compileStage cursor alternatives
    let prior : input.LocalizedRerootCompoundRule4bcKey :=
      { rule4aKey := rule4aKey
        references := references
        referenceCountPriority := constitutionalRule4bReferenceCountPriority references
        readings := input.rankReadings readings }
    let rule5Readings ← input.buildRuleMajorCompoundRule5ReadingsWith?
      compileStage cursor prior.readings
    some { prior := prior, rule5Readings := rule5Readings }) = some compound at continuation
  obtain ⟨rawReadings, rawBuilt, afterRaw⟩ :=
    Option.bind_eq_some_iff.mp continuation
  let prior : input.LocalizedRerootCompoundRule4bcKey :=
    { rule4aKey := rule4aKey
      references := references
      referenceCountPriority := constitutionalRule4bReferenceCountPriority references
      readings := input.rankReadings rawReadings }
  change (do
    let rule5Readings ← input.buildRuleMajorCompoundRule5ReadingsWith?
      compileStage cursor prior.readings
    some { prior := prior, rule5Readings := rule5Readings }) = some compound at afterRaw
  obtain ⟨rule5Readings, rule5Built, result⟩ :=
    Option.bind_eq_some_iff.mp afterRaw
  have compoundEq :
      ({ prior := prior, rule5Readings := rule5Readings } :
        input.LocalizedRerootCompoundRule45Key) = compound :=
    Option.some.inj result
  cases compoundEq
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [prior] using rule4aBuilt
  · rfl
  · rfl
  · exact ⟨rawReadings, by simpa [alternatives, prior] using rawBuilt, rfl,
      by simpa [prior] using rule5Built⟩

/-- The actual compound entry point is exactly the generic compound builder whose stage callback
uses the whole-rule builder at every stage. The existing hybrid callback uses the original
Rule-4a production builder only for the first stage; the arbitrary-reader Rule-4a agreement and
reader-specialization theorem identify it with the uniform callback. -/
theorem buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildActualRuleMajorCompoundRule45Key? target view fuel cursor =
      input.buildRuleMajorCompoundRule45KeyWith?
        (fun stage position =>
          input.buildRuleMajorCumulativeWithRead? stage
            (fun source => input.localizedDependencyLabel target view source) fuel position)
        cursor := by
  let reader : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel :=
    fun source => input.localizedDependencyLabel target view source
  let productionCompiler := input.ruleMajorCompoundStageCompiler target view reader fuel
  let uniformCompiler : input.RuleMajorCompoundStageCompiler carrierFuel :=
    fun stage position => input.buildRuleMajorCumulativeWithRead? stage reader fuel position
  have same : ∀ stage, productionCompiler stage cursor = uniformCompiler stage cursor := by
    intro stage
    cases stage with
    | rule4a =>
        change input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel cursor =
          input.buildRuleMajorCumulativeWithRead? .rule4a reader fuel cursor
        calc
          input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel cursor =
              input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
                reader fuel cursor :=
            (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
              .rule4a target view fuel cursor).symm
          _ = input.buildRuleMajorCumulativeWithRead? .rule4a reader fuel cursor :=
            (input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized reader fuel cursor).symm
    | rule4b reference => rfl
    | rule4cNoReference => rfl
    | rule4c reference => rfl
    | rule5NoRule4bReference reference => rfl
    | rule5 reference common => rfl
  change input.buildRuleMajorCompoundRule45KeyWith? productionCompiler cursor =
    input.buildRuleMajorCompoundRule45KeyWith? uniformCompiler cursor
  exact input.buildRuleMajorCompoundRule45KeyWith?_eq
    productionCompiler uniformCompiler cursor same

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule4bcReadingWith?_eq_some_iff_stageBuilds
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule45KeyWith?_readback
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor
