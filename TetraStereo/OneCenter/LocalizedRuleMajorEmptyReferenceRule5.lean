import TetraStereo.OneCenter.LocalizedRuleMajorRule4aAgreement
import TetraStereo.OneCenter.LocalizedRuleMajorNoReferenceRule5
import TetraStereo.OneCenter.LocalizedRuleMajorNoReferenceRule4cTableBridge
import TetraStereo.OneCenter.LocalizedRuleMajorRule4cPriorTie
import TetraStereo.OneCenter.LocalizedRuleMajorStagePrefix
import TetraStereo.OneCenter.LocalizedEmptyRule4bReferenceDecoding
import TetraStereo.OneCenter.LocalizedUniqueNearestRule4bReference
import TetraStereo.OneCenter.LocalizedSparseAddressReconstruction
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! An empty Rule-4b reference selection made from the original Rule-4a key rules out uppercase
labels in the new whole-rule no-reference Rule-4c key as well. The bridge keeps the callback
arbitrary: the old ranked-label selector is transported to the old key's exact label table,
Rule-4a builder agreement and the stage-prefix theorem identify the first descriptor columns,
and actual rule-major traces identify those columns with the entrywise Rule-4a priority tables.
The existing no-reference Rule-5 result then gives the exact zero lift, with no assumption about
reader values at cursors outside the successful build. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open OfficialRuleMajorKey
open LocalizedCumulativeDecoratedTree

private theorem scalar4a_eq_projectZero
    {input : CertifiedLocalizedCIPInput}
    (key : input.LocalizedRerootCumulativeRule45Key) :
    Rule4aTableBridge.scalar4a key = projectCumulative 0 key.descriptor := by
  unfold Rule4aTableBridge.scalar4a Rule4aTableBridge.sparseEntryMap projectCumulative
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro entry _
  cases entry.2 <;> rfl

private theorem rule4aPriorityMap_eq_of_chiralFreeTransfer
    {first second : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))}
    (same : Rule4cObservationBridge.mapLabelTable localizedRule4aPriority first =
      Rule4cObservationBridge.mapLabelTable localizedRule4aPriority second)
    (firstFree : LocalizedLabelLayersChiralFree first) :
    LocalizedLabelLayersChiralFree second := by
  have same' :
      first.map (List.map (Rule4aTableBridge.sparseEntryMap localizedRule4aPriority)) =
        second.map (List.map (Rule4aTableBridge.sparseEntryMap localizedRule4aPriority)) := by
    simpa [Rule4cObservationBridge.mapLabelTable] using same
  intro layer layerPresent entry entryPresent descriptor chiral
  have mappedLayerPresent :
      layer.map (Rule4aTableBridge.sparseEntryMap localizedRule4aPriority) ∈
        second.map (List.map (Rule4aTableBridge.sparseEntryMap localizedRule4aPriority)) := by
    exact List.mem_map.mpr ⟨layer, layerPresent, rfl⟩
  rw [← same'] at mappedLayerPresent
  obtain ⟨sourceLayer, sourceLayerPresent, sourceLayerEq⟩ :=
    List.mem_map.mp mappedLayerPresent
  have mappedEntryPresent :
      Rule4aTableBridge.sparseEntryMap localizedRule4aPriority entry ∈
        sourceLayer.map (Rule4aTableBridge.sparseEntryMap localizedRule4aPriority) := by
    rw [sourceLayerEq]
    exact List.mem_map.mpr ⟨entry, entryPresent, rfl⟩
  obtain ⟨sourceEntry, sourceEntryPresent, sourceEntryEq⟩ :=
    List.mem_map.mp mappedEntryPresent
  have priorityEq : localizedRule4aPriority sourceEntry.2 =
      localizedRule4aPriority entry.2 := by
    simpa [Rule4aTableBridge.sparseEntryMap] using congrArg Prod.snd sourceEntryEq
  have targetPriority : localizedRule4aPriority entry.2 = 2 := by
    rw [chiral]
    rfl
  obtain ⟨sourceDescriptor, sourceChiral⟩ :=
    exists_chiral_of_rule4aPriority_eq_two sourceEntry.2 (priorityEq.trans targetPriority)
  exact firstFree sourceLayer sourceLayerPresent sourceEntry sourceEntryPresent
    sourceDescriptor sourceChiral

private theorem ruleMajorKey_priorityMap_eq_scalar4a_of_trace
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {cursor : input.LocalizedRerootCursor carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (computed : input.buildRuleMajorCumulativeWithRead? stage read fuel cursor = some key) :
    Rule4cObservationBridge.mapLabelTable localizedRule4aPriority key.labels =
      Rule4aTableBridge.scalar4a key := by
  obtain ⟨tree, _, trace⟩ :=
    exists_ruleMajorTrace_of_buildWithRead input stage read fuel cursor key computed
  let fullMatch := LocalizedRuleMajorSortTrace.fullMatch_of_trace trace
  calc
    Rule4cObservationBridge.mapLabelTable localizedRule4aPriority key.labels =
        Rule4cObservationBridge.mapLabelTable localizedRule4aPriority tree.labelTable := by
      rw [← fullMatch.labelMatch]
    _ = table (fun node => localizedRule4aPriority node.label) tree :=
      Rule4cObservationBridge.mapLabelTable_labelTable localizedRule4aPriority tree
    _ = Rule4aTableBridge.scalar4a key := by
      rw [Rule4cObservationBridge.scalar4a_eq_table_anyStage fullMatch.tableMatch]
      rfl

/-- A successful arbitrary-reader old Rule-4a build with an empty ranked-label reference
selection has chiral-free labels in its key. This is the selector inversion plus the actual
address-forgetting invariant, stated without specializing the reader to a dependency view. -/
theorem localizedRuleMajorRule4a_labels_chiralFree_of_referenceSelection_eq_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      read fuel cursor = some key)
    (selection : localizedRule4bReferencesFromRankedLabels key.rankedLabels = []) :
    LocalizedLabelLayersChiralFree key.labels := by
  have addressInvariant :=
    input.buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_rankedLabels_forgetAddresses
      .rule4a read fuel cursor key computed
  have rankedFree : LocalizedLabelLayersChiralFree key.rankedLabels :=
    (localizedRule4bReferencesFromRankedLabels_eq_nil_iff key.rankedLabels).mp selection
  exact localizedLabelLayers_forall_of_map_snd_eq addressInvariant.2.symm
    (fun label => ∀ descriptor : RS, label ≠ some (.chiral descriptor)) rankedFree

/-- The empty original Rule-4a selection makes the actual new no-reference Rule-4c key
chiral-free. The old and new Rule-4a keys agree for every reader; the new Rule-4a and no-reference
Rule-4c keys have the same first complete rule-major descriptor column. -/
theorem buildRuleMajorCumulativeWithRead?_rule4cNoReference_labels_chiralFree_of_rule4aSelection_eq_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (rule4aKey : input.LocalizedRerootCumulativeRule45Key)
    (rule4aComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      read fuel cursor = some rule4aKey)
    (selection : localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels = [])
    (noReference4cKey : input.LocalizedRerootCumulativeRule45Key)
    (noReference4cComputed : input.buildRuleMajorCumulativeWithRead? .rule4cNoReference
      read fuel cursor = some noReference4cKey) :
    LocalizedLabelLayersChiralFree noReference4cKey.labels := by
  have rule4aMajorComputed : input.buildRuleMajorCumulativeWithRead? .rule4a
      read fuel cursor = some rule4aKey := by
    rw [input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized read fuel cursor]
    exact rule4aComputed
  have prefixAgreement := input.buildRuleMajorCumulativeWithRead_rule4a_rule4cNoReference_prefix
    read fuel cursor rule4aKey noReference4cKey rule4aMajorComputed noReference4cComputed
  have columnEquality : input.ruleMajorCumulativeColumns 1 rule4aKey =
      input.ruleMajorCumulativeColumns 1 noReference4cKey :=
    congrArg RuleMajorPrefixObservable.columns prefixAgreement
  have firstColumn : projectCumulative 0 rule4aKey.descriptor =
      projectCumulative 0 noReference4cKey.descriptor := by
    simpa [CertifiedLocalizedCIPInput.ruleMajorCumulativeColumns] using columnEquality
  have scalarEquality : Rule4aTableBridge.scalar4a rule4aKey =
      Rule4aTableBridge.scalar4a noReference4cKey := by
    calc
      Rule4aTableBridge.scalar4a rule4aKey = projectCumulative 0 rule4aKey.descriptor :=
        scalar4a_eq_projectZero rule4aKey
      _ = projectCumulative 0 noReference4cKey.descriptor := firstColumn
      _ = Rule4aTableBridge.scalar4a noReference4cKey :=
        (scalar4a_eq_projectZero noReference4cKey).symm
  have firstChiralFree := localizedRuleMajorRule4a_labels_chiralFree_of_referenceSelection_eq_nil
    input read fuel cursor rule4aKey rule4aComputed selection
  have mapTablesEqual :
      Rule4cObservationBridge.mapLabelTable localizedRule4aPriority rule4aKey.labels =
        Rule4cObservationBridge.mapLabelTable localizedRule4aPriority noReference4cKey.labels := by
    calc
      Rule4cObservationBridge.mapLabelTable localizedRule4aPriority rule4aKey.labels =
          Rule4aTableBridge.scalar4a rule4aKey := by
        exact ruleMajorKey_priorityMap_eq_scalar4a_of_trace rule4aMajorComputed
      _ = Rule4aTableBridge.scalar4a noReference4cKey := scalarEquality
      _ = Rule4cObservationBridge.mapLabelTable localizedRule4aPriority
          noReference4cKey.labels := by
        exact (ruleMajorKey_priorityMap_eq_scalar4a_of_trace noReference4cComputed).symm
  exact rule4aPriorityMap_eq_of_chiralFreeTransfer mapTablesEqual firstChiralFree

/-- With no original Rule-4a reference selected, the whole-rule Rule-5 no-reference builder is
exactly the false Rule-5 lift of the actual whole-rule no-reference Rule-4c key. -/
theorem buildRuleMajorCumulativeWithRead?_rule5NoReference_of_rule4aSelection_eq_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (probe : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (rule4aKey : input.LocalizedRerootCumulativeRule45Key)
    (rule4aComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      read fuel cursor = some rule4aKey)
    (selection : localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels = [])
    (noReference4cKey : input.LocalizedRerootCumulativeRule45Key)
    (noReference4cComputed : input.buildRuleMajorCumulativeWithRead? .rule4cNoReference
      read fuel cursor = some noReference4cKey) :
    input.buildRuleMajorCumulativeWithRead?
        (.rule5NoRule4bReference probe) read fuel cursor =
      some (input.rule5LiftKey false noReference4cKey) := by
  have labelsFree :=
    buildRuleMajorCumulativeWithRead?_rule4cNoReference_labels_chiralFree_of_rule4aSelection_eq_nil
      input read fuel cursor rule4aKey rule4aComputed selection
      noReference4cKey noReference4cComputed
  rw [buildRuleMajorCumulativeWithRead?_rule5NoReference_of_keyChiralFree
    input probe read fuel cursor noReference4cKey noReference4cComputed labelsFree,
    noReference4cComputed]
  rfl

/-- Once the original Rule-4a selector is empty, the whole-rule no-reference Rule-5 output is
independent of which candidate is used to instantiate that stage. -/
theorem buildRuleMajorCumulativeWithRead?_rule5NoReference_same_for_allReferences_of_rule4aSelection_eq_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (leftReference rightReference : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (rule4aKey : input.LocalizedRerootCumulativeRule45Key)
    (rule4aComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      read fuel cursor = some rule4aKey)
    (selection : localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels = [])
    (noReference4cKey : input.LocalizedRerootCumulativeRule45Key)
    (noReference4cComputed : input.buildRuleMajorCumulativeWithRead? .rule4cNoReference
      read fuel cursor = some noReference4cKey) :
    input.buildRuleMajorCumulativeWithRead?
        (.rule5NoRule4bReference leftReference) read fuel cursor =
      input.buildRuleMajorCumulativeWithRead?
        (.rule5NoRule4bReference rightReference) read fuel cursor := by
  rw [buildRuleMajorCumulativeWithRead?_rule5NoReference_of_rule4aSelection_eq_nil
      input leftReference read fuel cursor rule4aKey rule4aComputed selection
      noReference4cKey noReference4cComputed,
    buildRuleMajorCumulativeWithRead?_rule5NoReference_of_rule4aSelection_eq_nil
      input rightReference read fuel cursor rule4aKey rule4aComputed selection
      noReference4cKey noReference4cComputed]

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRuleMajorRule4a_labels_chiralFree_of_referenceSelection_eq_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?_rule4cNoReference_labels_chiralFree_of_rule4aSelection_eq_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?_rule5NoReference_of_rule4aSelection_eq_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?_rule5NoReference_same_for_allReferences_of_rule4aSelection_eq_nil
