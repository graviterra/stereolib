import TetraStereo.OneCenter.LocalizedContextBranchStages
import TetraStereo.OneCenter.LocalizedContextCompoundReferenceSelection
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Exact compound stage provenance at arbitrary actual auxiliary targets. The generated
reference population determines all alternatives. Each alternative retains precisely the
Rule-4b and Rule-4c stage keys built at the same cursor, including the empty-reference case. -/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open DeclarativeCIP Rule4aTableBridge LocalizedCumulativeDecoratedTree
noncomputable section

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
  {cursor : input.LocalizedRerootCursor carrierFuel}

def contextStageReading (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (reference : Option RS) : input.LocalizedRerootRule4bcReading :=
  match reference with
  | none => ⟨none, stages.a.key, stages.noReference.key⟩
  | some selected => ⟨some selected, (stages.b selected).key, (stages.c selected).key⟩

theorem contextStageReading_build
    (stages : input.RuleMajorContextStages carrierFuel read cursor) (reference : Option RS) :
    input.buildRuleMajorCompoundRule4bcReadingWith?
      (fun stage position => input.buildRuleMajorCumulativeWithRead? stage read
        (2 * (carrierFuel + 1)) position) cursor reference =
      some (contextStageReading stages reference) := by
  cases reference with
  | none =>
      simp [buildRuleMajorCompoundRule4bcReadingWith?, contextStageReading,
        stages.a.built, stages.noReference.built]
  | some selected =>
      simp [buildRuleMajorCompoundRule4bcReadingWith?, contextStageReading,
        (stages.b selected).built, (stages.c selected).built]

theorem contextStageReadings_build
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (references : List (Option RS)) :
    input.buildRuleMajorCompoundRule4bcReadingsWith?
      (fun stage position => input.buildRuleMajorCumulativeWithRead? stage read
        (2 * (carrierFuel + 1)) position) cursor references =
      some (references.map (contextStageReading stages)) := by
  induction references with
  | nil => rfl
  | cons reference references ih =>
      simp only [buildRuleMajorCompoundRule4bcReadingsWith?, Option.bind_eq_bind,
        contextStageReading_build stages reference, ih, Option.bind_some]
      rfl

/-- Uniform compound execution preserves the exact successful stage keys. This structural
identity does not yet identify outcome ordering with the independent complete readings. -/
theorem contextStages_compound_readback
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    {compound : input.LocalizedRerootCompoundRule45Key}
    (built : input.buildRuleMajorCompoundRule45KeyWith?
      (fun stage position => input.buildRuleMajorCumulativeWithRead? stage read
        (2 * (carrierFuel + 1)) position) cursor = some compound) :
    compound.prior.rule4aKey = stages.a.key ∧
      compound.prior.references = localizedRule4bReferencesFromRankedLabels stages.a.key.rankedLabels ∧
      compound.prior.referenceCountPriority =
        constitutionalRule4bReferenceCountPriority compound.prior.references ∧
      compound.prior.readings = input.rankReadings
        ((localizedRule4bcReferenceAlternatives compound.prior.references).map
          (contextStageReading stages)) := by
  obtain ⟨aBuilt, refs, count, raw, rawBuilt, ranked, _rule5Built⟩ :=
    input.buildRuleMajorCompoundRule45KeyWith?_readback _ cursor built
  have aEq : compound.prior.rule4aKey = stages.a.key :=
    Option.some.inj (aBuilt.symm.trans stages.a.built)
  refine ⟨aEq, ?_, count, ?_⟩
  · simpa only [aEq] using refs
  · have rawEq := Option.some.inj
      (rawBuilt.symm.trans (contextStageReadings_build stages _))
    exact ranked.trans (congrArg input.rankReadings rawEq)

/-- Both compound execution and all six stage executions are derived. The alternative list
and count are exactly the independent contextual selection, with no reference-count premise. -/
theorem exists_generatedContextStages_compound_readback
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursor : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (rootChild : cursor ∈ input.certified.executableLocalizedRerootChildren target) :
    let read := input.certified.localizedDependencyLabel target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)
    ∃ (stages : input.certified.RuleMajorContextStages
        (input.certified.certified.input.molecule.atomCount + 1) read cursor)
      (compound : input.certified.LocalizedRerootCompoundRule45Key),
      input.certified.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)
        (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) cursor = some compound ∧
      compound.prior.rule4aKey = stages.a.key ∧
      let selection := contextualReferenceSelection input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph stages.a.tree)
      compound.prior.references = toReferenceList selection ∧
      compound.prior.referenceCountPriority = selection.countPriority ∧
      compound.prior.readings = input.certified.rankReadings
        ((localizedRule4bcReferenceAlternatives (toReferenceList selection)).map
          (contextStageReading stages)) := by
  let view := input.certified.localizedDependencyView
    (LocalizedRuleMajorReference.referenceState input) target.occurrence
  let read := input.certified.localizedDependencyLabel target.occurrence view
  obtain ⟨stages⟩ := input.certified.exists_ruleMajorContextStages_at_actualChild
    _ read target cursor rootChild
  have valid := input.certified.localizedRerootChild_valid target cursor _
    (input.certified.executableLocalizedRerootChildren_declarative target) rootChild
  obtain ⟨compound, built⟩ :=
    input.certified.exists_buildActualRuleMajorCompoundRule45Key_at_twice
      target.occurrence view cursor valid
  have uniformBuilt := built
  rw [input.certified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor] at uniformBuilt
  obtain ⟨aEq, refs, count, readings⟩ := contextStages_compound_readback stages uniformBuilt
  have selected := ContextReferenceBridge.generatedContextTree_references_eq_selection
    input singleBonded acyclic target unit targetUnit stages.a.tree stages.a.trace
      (by simpa only [stages.a.sourceEq] using rootChild)
  have references := refs.trans selected
  refine ⟨stages, compound, ?_, aEq, references, ?_, ?_⟩
  · rw [input.certified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact built
  · rw [count, references]
    cases selection : contextualReferenceSelection input.certified.moleculeGraph
      (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph stages.a.tree) with
    | empty => rfl
    | one sense => cases sense <;> rfl
    | both => rfl
  · simpa only [references] using readings

end
end TetraStereo.OneCenter.CertifiedLocalizedCIPInput

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.contextStageReading
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.contextStageReading_build
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.contextStageReadings_build
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.contextStages_compound_readback
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_generatedContextStages_compound_readback
