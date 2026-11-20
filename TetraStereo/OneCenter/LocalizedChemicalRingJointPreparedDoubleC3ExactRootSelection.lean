import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefix
import TetraStereo.OneCenter.LocalizedRuleMajorRule4aAgreement
import TetraStereo.OneCenter.LocalizedUniqueNearestRule4bReference
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootSelection

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier (input)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootFrame (target frame)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootSlice (reader)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootReader (factFirstView)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootFacts (twoFacts)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootPrefix (read oxygen4_prefix oxygen15_prefix)

abbrev view := factFirstView input twoFacts target
abbrev compiler : input.RuleMajorCompoundStageCompiler 26 :=
  LocalizedChemicalRingCachedOperations.stageCompiler input reader target view read 54

/-- The actual Rule4a compiler and cached recurrence agree exactly, including failures. -/
theorem rule4a_eq (cursor : input.LocalizedRerootCursor 26) :
    compiler .rule4a cursor =
      LocalizedChemicalRingCachedOperations.cumulative input reader .rule4a read 54 cursor := by
  change WithChildren.buildLocalizedRerootCumulativeRule45KeyExec? input reader.readChildren
      .rule4a target view 54 cursor = _
  rw [WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?_eq_original input
    reader.readChildren reader.readChildren_eq]
  rw [input.buildLocalizedRerootCumulativeRule45KeyExec?_eq_build]
  rw [LocalizedChemicalRingCachedOperations.cumulative_eq]
  exact (input.buildRuleMajorCumulativeWithReadExec?_rule4a_eq_localizedDependencyLabel
    target view 54 cursor).symm

private theorem references_from_prefix (key : input.LocalizedRerootCumulativeRule45Key)
    (cursor : input.LocalizedRerootCursor 26) (descriptor : RS)
    (computed : compiler .rule4a cursor = some key)
    (labelPrefix : ∃ tail, key.labels = [([], none)] :: [([0], some (.chiral descriptor))] :: tail) :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels = [descriptor] := by
  have oldBuilt : input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view 54 cursor =
      some key := by
    change WithChildren.buildLocalizedRerootCumulativeRule45KeyExec? input reader.readChildren
      .rule4a target view 54 cursor = some key at computed
    rw [WithChildren.buildLocalizedRerootCumulativeRule45KeyExec?_eq_original input
      reader.readChildren reader.readChildren_eq,
      input.buildLocalizedRerootCumulativeRule45KeyExec?_eq_build] at computed
    exact computed
  obtain ⟨tail, rows⟩ := labelPrefix
  apply input.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_singleton_of_first_uniqueChiral
    .rule4a target view 54 cursor key 1 descriptor oldBuilt
  · intro earlier bound
    have zero : earlier = 0 := by omega
    subst earlier
    simp [rows, localizedRule4bChiralObservationsInLayer]
  · simp [rows, localizedRule4bChiralObservationsInLayer]

/-- Actual O4 Rule4a selects the unique nearest R auxiliary, with no supplied selector result. -/
theorem oxygen4_references (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : compiler .rule4a (frame.cursorAt 2) = some key) :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels = [.R] := by
  apply references_from_prefix key (frame.cursorAt 2) .R computed
  apply oxygen4_prefix .rule4a key
  rw [← rule4a_eq]
  exact computed

/-- Actual O15 Rule4a selects the unique nearest S auxiliary. -/
theorem oxygen15_references (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : compiler .rule4a (frame.cursorAt 3) = some key) :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels = [.S] := by
  apply references_from_prefix key (frame.cursorAt 3) .S computed
  apply oxygen15_prefix .rule4a key
  rw [← rule4a_eq]
  exact computed

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootSelection

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootSelection.rule4a_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootSelection.oxygen4_references
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootSelection.oxygen15_references
