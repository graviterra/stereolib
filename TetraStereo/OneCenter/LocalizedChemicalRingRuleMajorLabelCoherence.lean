import TetraStereo.OneCenter.LocalizedRule4bSparseLabelDecoding
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeOrder
import TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

private theorem localized_list_mapM_member {α β : Type*} (reader : α → Option β) :
    ∀ (values : List α) (results : List β),
      values.mapM reader = some results →
      ∀ result, result ∈ results →
        ∃ value, value ∈ values ∧ reader value = some result
  | [], results, computed, result, present => by
      simp at computed
      subst results
      simp at present
  | value :: values, results, computed, result, present => by
      rw [List.mapM_cons] at computed
      cases headComputed : reader value with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : values.mapM reader with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst results
              rcases List.mem_cons.mp present with same | tailPresent
              · subst result
                exact ⟨value, by simp, headComputed⟩
              · rcases localized_list_mapM_member reader values tail tailComputed result tailPresent with
                  ⟨source, sourcePresent, sourceComputed⟩
                exact ⟨source, List.mem_cons_of_mem value sourcePresent, sourceComputed⟩

private theorem foldl_max_length_eq {α : Type*}
    (first second : α → Nat) (values : List α) (initial : Nat)
    (same : ∀ value, value ∈ values → first value = second value) :
    values.foldl (fun longest value => max longest (first value)) initial =
      values.foldl (fun longest value => max longest (second value)) initial := by
  induction values generalizing initial with
  | nil => rfl
  | cons value values inductionHypothesis =>
      rw [List.foldl_cons, List.foldl_cons, same value (by simp)]
      exact inductionHypothesis _ (fun observed present => same observed (by simp [present]))

/-- If every child has descriptor and label spheres of equal extent, the actual descriptor and
label merges use the same sphere count. -/
private theorem localizedRerootDescriptorChildLayerCount_eq_labelChildLayerCount
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (lengths : ∀ child, child ∈ children →
      child.descriptor.length = child.labels.length) :
    input.localizedRerootDescriptorChildLayerCount children =
      input.localizedRerootLabelChildLayerCount children := by
  unfold localizedRerootDescriptorChildLayerCount localizedRerootLabelChildLayerCount
  exact foldl_max_length_eq (fun child => child.descriptor.length)
    (fun child => child.labels.length) children 0 lengths

/-- **Descriptor/label coherence of one actual sibling merge.**  If every child's addressed
descriptor is its addressed label table read through `localizedCumulativeRule45Priority stage`,
the actual descriptor merge is the actual label merge read through the same priority. -/
private theorem mergeLocalizedRerootDescriptorChildren_eq_mapSourceLayers
    (input : CertifiedLocalizedCIPInput) (stage : LocalizedCumulativeRule45Stage)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (coherent : ∀ child, child ∈ children →
      child.descriptor = OfficialRuleMajorKey.mapSourceLayers
        (localizedCumulativeRule45Priority stage) child.labels) :
    input.mergeLocalizedRerootDescriptorChildren children =
      OfficialRuleMajorKey.mapSourceLayers
        (localizedCumulativeRule45Priority stage)
        (input.mergeLocalizedRerootLabelChildren children) := by
  unfold mergeLocalizedRerootDescriptorChildren mergeLocalizedRerootLabelChildren
  rw [localizedRerootDescriptorChildLayerCount_eq_labelChildLayerCount input children
    (fun child present => by
      rw [coherent child present]
      simp [OfficialRuleMajorKey.mapSourceLayers])]
  dsimp only
  rw [OfficialRuleMajorKey.mapSourceLayers, List.map_map]
  apply List.map_congr_left
  intro depth _
  simp only [Function.comp_apply]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro child childPresent
  have childCoherent : child.1.descriptor = OfficialRuleMajorKey.mapSourceLayers
      (localizedCumulativeRule45Priority stage) child.1.labels :=
    coherent child.1 (List.fst_mem_of_mem_zipIdx childPresent)
  rw [childCoherent, OfficialRuleMajorKey.mapSourceLayers_getD,
    OfficialRuleMajorKey.prefixLayer_mapObservation]

theorem buildRuleMajorCumulativeWithRead?_descriptor_eq_labels_projection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildRuleMajorCumulativeWithRead? stage read fuel cursor = some key →
      key.descriptor =
        OfficialRuleMajorKey.mapSourceLayers
          (localizedCumulativeRule45Priority stage) key.labels
  | 0, cursor, key, computed => by
      unfold buildRuleMajorCumulativeWithRead? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            rfl
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildRuleMajorCumulativeWithRead? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            rfl
          · cases childKeysComputed : children.mapM
                (input.buildRuleMajorCumulativeWithRead? stage read fuel) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
                subst key
                dsimp only
                rw [OfficialRuleMajorKey.mapSourceLayers]
                simp only [List.map_cons, List.map_nil,
                  OfficialRuleMajorKey.mapObservation, List.cons_append, List.nil_append]
                congr 1
                exact mergeLocalizedRerootDescriptorChildren_eq_mapSourceLayers
                    input stage
                    (input.sortRuleMajorCumulativeKeys stage childKeys)
                    (fun child childPresent => by
                      have sourcePresent : child ∈ childKeys :=
                        (sortKeysBy_perm (input.compareRuleMajorCumulativeDescriptor (ruleMajorStageWidth stage)) childKeys).mem_iff.mp
                          childPresent
                      rcases localized_list_mapM_member
                          (input.buildRuleMajorCumulativeWithRead?
                            stage read fuel)
                          children childKeys childKeysComputed child sourcePresent with
                        ⟨childCursor, _childCursorPresent, childComputed⟩
                      exact
                        buildRuleMajorCumulativeWithRead?_descriptor_eq_labels_projection
                          input stage read fuel childCursor child childComputed)

end CertifiedLocalizedCIPInput

namespace LocalizedChemicalRingCachedOperations
open CertifiedLocalizedCIPInput
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)

theorem cumulative_descriptor_eq_labels_projection
    (input : CertifiedLocalizedCIPInput)
    (cache : input.LocalizedRerootChildReader (retainedCarrierFuel input))
    (stage : LocalizedCumulativeRule45Stage)
    (read : Cursor input → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : Cursor input)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (built : cumulative input cache stage read fuel cursor = some key) :
    key.descriptor = OfficialRuleMajorKey.mapSourceLayers
      (localizedCumulativeRule45Priority stage) key.labels := by
  apply input.buildRuleMajorCumulativeWithRead?_descriptor_eq_labels_projection
    stage read fuel cursor key
  have same := congrFun (cumulative_eq input cache stage read fuel) cursor
  rw [input.buildRuleMajorCumulativeWithReadExec_eq stage read fuel cursor] at same
  exact same.symm.trans built

end LocalizedChemicalRingCachedOperations
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?_descriptor_eq_labels_projection
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCachedOperations.cumulative_descriptor_eq_labels_projection
