import TetraStereo.OneCenter.LocalizedContextCompleteReadingOrder
import TetraStereo.OneCenter.LocalizedContextCompoundRule5Readback
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual compound provenance and ordered independent reading observations. The generated
facade derives the reference selection, readback, and stage isomorphisms. The `tags` field describes
the actual Rule-5 reading list; numerical stream comparisons are connected separately by the
contextual comparison modules. -/

/-! Independent contextual readback for every field of an actual compound record. The prior
reading keys are tied to their source stages, while complete reading values and Rule-5 tags are
checked against the contextual semantics on the shared Rule-4a graph. -/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open CertifiedLocalizedCIPInput DeclarativeCIP LocalizedCumulativeDecoratedTree
noncomputable section

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
  {cursor : input.LocalizedRerootCursor carrierFuel}

/-- All prior and Rule-5 outputs of an actual contextual compound agree with independent
contextual selection and reading order at the `.rule4a` stage graph. -/
structure ContextCompoundReadbackData
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (compound : input.LocalizedRerootCompoundRule45Key) (W D : Nat) : Prop where
  aKey : compound.prior.rule4aKey = stages.a.key
  references : compound.prior.references = toReferenceList
    (contextualReferenceSelection input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph stages.a.tree))
  count : compound.prior.referenceCountPriority =
    (contextualReferenceSelection input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph stages.a.tree)).countPriority
  readingStages : ∀ reading ∈ compound.prior.readings,
    match reading.reference? with
    | none => reading.rule4bKey = stages.a.key ∧
        reading.rule4cKey = stages.noReference.key
    | some reference => reading.rule4bKey = (stages.b reference).key ∧
        reading.rule4cKey = (stages.c reference).key
  readingEmpty : ∀ reading ∈ compound.prior.readings,
    reading.reference? = none ↔
      contextualReferenceSelection input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) = .empty
  observations : compound.prior.readings.map (fun reading =>
      contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) W D
        (reading.reference?.map senseOf)) =
    contextualCompleteReadingsAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph stages.a.tree) W D
  tags : compound.rule5Readings.map (fun reading => reading.prior.reference?.map senseOf) =
    contextualTaggedAlternativeReferencesAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph stages.a.tree) W D

/-- Construct the independent readback data from a uniform successful build. The contextual
selection equality connects the builder's ranked label selection to the independent graph
selection; the R/S comparator transport supplies both value ordering and stable tag ordering. -/
theorem contextStages_compound_independentReadback
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) {W D : Nat}
    (width : stages.widthBound ≤ W) (depth : stages.depthBound ≤ D)
    (readbacks : RuleMajorContextReadingReadbacks stages descriptorMap unit)
    (isomorphisms : RuleMajorContextStageGraphIsoBundle stages)
    {compound : input.LocalizedRerootCompoundRule45Key}
    (built : input.buildRuleMajorCompoundRule45KeyWith?
      (fun stage position => input.buildRuleMajorCumulativeWithRead? stage read
        (2 * (carrierFuel + 1)) position) cursor = some compound)
    (referencesEq : compound.prior.references = toReferenceList
      (contextualReferenceSelection input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree))) :
    ContextCompoundReadbackData stages descriptorMap unit compound W D := by
  obtain ⟨aEq, _builderReferences, countEq, readingsEq⟩ :=
    input.contextStages_compound_readback stages built
  have aKey : compound.prior.rule4aKey = stages.a.key := aEq
  have count : compound.prior.referenceCountPriority =
      (contextualReferenceSelection input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree)).countPriority := by
    rw [countEq, referencesEq]
    cases selection : contextualReferenceSelection input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) with
    | empty => rfl
    | one sense => cases sense <;> rfl
    | both => rfl
  have readingsEqSelection : compound.prior.readings = input.rankReadings
      (ruleMajorContextBranchReadings stages descriptorMap unit) := by
    rw [readingsEq, referencesEq]
    rfl
  have emptyReadingsEq (selection : contextualReferenceSelection input.moleculeGraph
      descriptorMap unit (ruleMajorTreeGraph stages.a.tree) = .empty) :
      compound.prior.readings = [contextStageReading stages none] := by
    rw [readingsEqSelection]
    simp [ruleMajorContextBranchReadings, ruleMajorContextBranchReading,
      localizedRule4bcReferenceAlternatives, toReferenceList, rankReadings, selection]
  have seniorReadingsEq (selection : contextualReferenceSelection input.moleculeGraph
      descriptorMap unit (ruleMajorTreeGraph stages.a.tree) = .one .senior) :
      compound.prior.readings = [contextStageReading stages (some .R)] := by
    rw [readingsEqSelection]
    simp [ruleMajorContextBranchReadings, ruleMajorContextBranchReading,
      localizedRule4bcReferenceAlternatives, toReferenceList, rankReadings, selection]
  have juniorReadingsEq (selection : contextualReferenceSelection input.moleculeGraph
      descriptorMap unit (ruleMajorTreeGraph stages.a.tree) = .one .junior) :
      compound.prior.readings = [contextStageReading stages (some .S)] := by
    rw [readingsEqSelection]
    simp [ruleMajorContextBranchReadings, ruleMajorContextBranchReading,
      localizedRule4bcReferenceAlternatives, toReferenceList, rankReadings, selection]
  have bothReadingsEq (selection : contextualReferenceSelection input.moleculeGraph
      descriptorMap unit (ruleMajorTreeGraph stages.a.tree) = .both) :
      compound.prior.readings = input.rankReadings
        [contextStageReading stages (some .R), contextStageReading stages (some .S)] := by
    rw [readingsEqSelection]
    simp [ruleMajorContextBranchReadings, ruleMajorContextBranchReading,
      localizedRule4bcReferenceAlternatives, toReferenceList, selection]
  have readingStages : ∀ reading ∈ compound.prior.readings,
      match reading.reference? with
      | none => reading.rule4bKey = stages.a.key ∧
          reading.rule4cKey = stages.noReference.key
      | some reference => reading.rule4bKey = (stages.b reference).key ∧
          reading.rule4cKey = (stages.c reference).key := by
    intro reading present
    cases selection : contextualReferenceSelection input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) with
    | empty =>
        rw [emptyReadingsEq selection] at present
        have equal := List.mem_singleton.mp present
        subst reading
        simp [contextStageReading]
    | one sense =>
        cases sense with
        | senior =>
            rw [seniorReadingsEq selection] at present
            have equal := List.mem_singleton.mp present
            subst reading
            simp [contextStageReading]
        | junior =>
            rw [juniorReadingsEq selection] at present
            have equal := List.mem_singleton.mp present
            subst reading
            simp [contextStageReading]
    | both =>
        rw [bothReadingsEq selection] at present
        simp only [rankReadings] at present
        split at present <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at present
        all_goals
          rcases present with referenceR | referenceS
          · cases referenceR
            simp [contextStageReading]
          · cases referenceS
            simp [contextStageReading]
  have readingEmpty : ∀ reading ∈ compound.prior.readings,
      reading.reference? = none ↔
        contextualReferenceSelection input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph stages.a.tree) = .empty := by
    intro reading present
    constructor
    · intro readingNone
      cases selection : contextualReferenceSelection input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph stages.a.tree) with
      | empty => rfl
      | one sense =>
          cases sense with
          | senior =>
              rw [seniorReadingsEq selection] at present
              have equal := List.mem_singleton.mp present
              subst reading
              simp [contextStageReading] at readingNone
          | junior =>
              rw [juniorReadingsEq selection] at present
              have equal := List.mem_singleton.mp present
              subst reading
              simp [contextStageReading] at readingNone
      | both =>
          rw [bothReadingsEq selection] at present
          simp only [rankReadings] at present
          split at present <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at present
          all_goals
            rcases present with referenceR | referenceS
            · cases referenceR
              simp [contextStageReading] at readingNone
            · cases referenceS
              simp [contextStageReading] at readingNone
    · intro selectionEmpty
      rw [emptyReadingsEq selectionEmpty] at present
      have equal := List.mem_singleton.mp present
      subst reading
      simp [contextStageReading]
  have observations : compound.prior.readings.map (fun reading =>
      contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) W D (reading.reference?.map senseOf)) =
      contextualCompleteReadingsAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) W D := by
    rw [readingsEqSelection]
    exact ruleMajorContextStages_rankReadings_observations singleBonded stages descriptorMap unit
      width depth readbacks isomorphisms
  have tags : compound.rule5Readings.map
      (fun reading => reading.prior.reference?.map senseOf) =
      contextualTaggedAlternativeReferencesAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) W D := by
    rw [input.contextStages_compound_rule5Readings_eq_map stages built]
    simp only [List.map_map]
    change (compound.prior.readings.map
        (fun reading => (input.ruleMajorExpectedRule5Reading reading).prior.reference?.map senseOf)) = _
    simp only [ruleMajorExpectedRule5Reading]
    rw [readingsEqSelection]
    exact ruleMajorContextStages_rankedReferenceTags singleBonded stages descriptorMap unit
      readbacks isomorphisms width depth
  exact {
    aKey := aKey
    references := referencesEq
    count := count
    readingStages := readingStages
    readingEmpty := readingEmpty
    observations := observations
    tags := tags }

/-- At an actual generated child, the fixed supplied stage family and successful executable
compound build already determine the independent readback. No reference selection, stage
readback, or stage-graph isomorphism is supplied to this theorem. -/
theorem generatedContextCompound_independentReadback
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursor : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (cursorChild : cursor ∈ input.certified.executableLocalizedRerootChildren target)
    (stages : input.certified.RuleMajorContextStages
      (input.certified.certified.input.molecule.atomCount + 1)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursor)
    {compound : input.certified.LocalizedRerootCompoundRule45Key}
    {W D : Nat} (width : stages.widthBound ≤ W) (depth : stages.depthBound ≤ D)
    (built : input.certified.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)
      (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) cursor =
        some compound) :
    ContextCompoundReadbackData stages (LocalizedRuleMajorReference.descriptorMap input)
      unit compound W D := by
  let view := input.certified.localizedDependencyView
    (LocalizedRuleMajorReference.referenceState input) target.occurrence
  let read := input.certified.localizedDependencyLabel target.occurrence view
  let fuel := 2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)
  have uniformBuilt : input.certified.buildRuleMajorCompoundRule45KeyWith?
      (fun stage position => input.certified.buildRuleMajorCumulativeWithRead? stage read fuel position)
      cursor = some compound := by
    rw [← input.certified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
    rw [← input.certified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact built
  obtain ⟨_aKey, rankedReferences, _count, _readings⟩ :=
    input.certified.contextStages_compound_readback stages uniformBuilt
  have selectionReferences := ContextReferenceBridge.generatedContextTree_references_eq_selection
    input singleBonded acyclic target unit targetUnit stages.a.tree stages.a.trace
      (by simpa only [stages.a.sourceEq] using cursorChild)
  have referencesEq : compound.prior.references = toReferenceList
      (contextualReferenceSelection input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph stages.a.tree)) :=
    rankedReferences.trans selectionReferences
  let readbacks := ruleMajorContextReadingReadbacks_of_generatedActualChild input
    singleBonded acyclic target unit targetUnit cursor cursorChild stages
  let isomorphisms := ruleMajorContextStageGraphIsoBundle_of_generatedActualChild input
    singleBonded acyclic target cursor cursorChild stages
  exact contextStages_compound_independentReadback singleBonded stages
    (LocalizedRuleMajorReference.descriptorMap input) unit width depth readbacks isomorphisms
    uniformBuilt referencesEq

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ContextCompoundReadbackData
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextStages_compound_independentReadback
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.generatedContextCompound_independentReadback
