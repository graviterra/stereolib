import TetraStereo.OneCenter.LocalizedRankedProjectionTransport
import TetraStereo.OneCenter.LocalizedActualParentComparisonSeparation
import TetraStereo.KernelOnly

set_option autoImplicit false




































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## Reading the restricted dependency view -/

/-- Outside a strict depth dependency `localizedDependencyLabel` reads no state at all. -/
theorem localizedDependencyLabel_eq_none_of_not_dependency
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel)
    (notDependency : ¬ input.LocalizedDepthDependency cursor.occurrence target) :
    input.localizedDependencyLabel target view cursor = none := by
  unfold localizedDependencyLabel
  rw [dif_neg notDependency]

/-- `localizedDependencyLabel` returns `some label` exactly at a strict depth dependency. -/
theorem localizedDependencyLabel_eq_some_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel)
    (label : LocalizedAuxiliaryLabel) :
    input.localizedDependencyLabel target view cursor = some label ↔
      ∃ dependency : input.LocalizedDepthDependency cursor.occurrence target,
        view cursor.occurrence dependency = some label := by
  unfold localizedDependencyLabel
  by_cases dependency : input.LocalizedDepthDependency cursor.occurrence target
  · rw [dif_pos dependency]
    constructor
    · intro computed
      exact ⟨dependency, computed⟩
    · rintro ⟨_dependency, computed⟩
      exact computed
  · rw [dif_neg dependency]
    constructor
    · intro impossible
      simp at impossible
    · rintro ⟨other, _computed⟩
      exact (dependency other).elim

/-- A source whose address is a prefix of the target address is never a strict depth
dependency: it is not deeper than the target.  This is the address-level form of "ancestors are
not dependency sources". -/
theorem not_localizedDepthDependency_of_address_prefix
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {source target : input.LocalizedCIPOccurrence fuel}
    (addressPrefix : source.1.address <+: target.1.address) :
    ¬ input.LocalizedDepthDependency source target := by
  rintro ⟨_sameRoot, deeper⟩
  have lengthLe : source.1.address.length ≤ target.1.address.length :=
    List.IsPrefix.length_le addressPrefix
  omega

/-- Ancestor occurrences (addresses prefixing the target) read as `none`. -/
theorem localizedDependencyLabel_eq_none_of_address_prefix
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel)
    (addressPrefix : cursor.occurrence.1.address <+: target.1.address) :
    input.localizedDependencyLabel target view cursor = none :=
  input.localizedDependencyLabel_eq_none_of_not_dependency target view cursor
    (input.not_localizedDepthDependency_of_address_prefix addressPrefix)

/-- The actual carrier parent of a non-root occurrence is not a dependency source. -/
theorem parentCursor_not_localizedDepthDependency
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (certificate : input.LocalizedParentFrameHistory target) :
    ¬ input.LocalizedDepthDependency certificate.parent target := by
  rintro ⟨_sameRoot, deeper⟩
  have step := certificate.parent_address_length input
  omega

/-- The parent-side cursor reads no label: the actual parent is shallower than the target. -/
theorem rule4b_parentCursor_dependencyLabel_eq_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (certificate : input.LocalizedParentFrameHistory target)
    (view : input.LocalizedDependencyView target) :
    input.localizedDependencyLabel target view
      ({ occurrence := certificate.parent, previous? := some target } :
        input.LocalizedRerootCursor carrierFuel) = none := by
  apply input.localizedDependencyLabel_eq_none_of_address_prefix target view
  show certificate.parent.1.address <+: target.1.address
  rw [certificate.parent_address]
  exact List.dropLast_prefix target.1.address

/-! ## Dependency provenance of the ranked-label stack -/

/-- Every label stored in a ranked-label layer is obtained from the restricted view at a strict
depth dependency of the descriptor target. -/
def RankedLabelsDependencySourced
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) : Prop :=
  ∀ (layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))),
    layer ∈ layers →
      ∀ (entry : OfficialSparseEntry (Option LocalizedAuxiliaryLabel)),
        entry ∈ layer →
          ∀ label : LocalizedAuxiliaryLabel,
            entry.2 = some label →
              ∃ source : input.LocalizedCIPOccurrence carrierFuel,
                ∃ dependency : input.LocalizedDepthDependency source target,
                  view source dependency = some label

/-- The underlying key of a ranked child is one of the sibling keys.  Local copy needed because
the corresponding lemma in `LocalizedRankedPopulationMerge` is private. -/
private theorem fst_mem_of_mem_localizedRerootRankedChildTail_audit
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    ∀ (previous : input.LocalizedRerootCumulativeRule45Key) (rank : Nat)
      {pair : input.LocalizedRerootCumulativeRule45Key × Nat},
      pair ∈ input.localizedRerootRankedChildTail previous rank children →
        pair.1 ∈ children := by
  induction children with
  | nil =>
      intro previous rank pair present
      simp [localizedRerootRankedChildTail] at present
  | cons child rest ih =>
      intro previous rank pair present
      rw [localizedRerootRankedChildTail_cons input previous child rank rest] at present
      rcases List.mem_cons.mp present with same | tailPresent
      · rw [same]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem child
          (ih child
            (if input.compareLocalizedRerootCumulativeRule45Keys child previous =
                Ordering.eq then rank else rank + 1)
            tailPresent)

/-- The underlying key of a ranked child is one of the sibling keys. -/
private theorem fst_mem_of_mem_localizedRerootRankedChildren_audit
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    ∀ {pair : input.LocalizedRerootCumulativeRule45Key × Nat},
      pair ∈ input.localizedRerootRankedChildren children → pair.1 ∈ children := by
  induction children with
  | nil =>
      intro pair present
      simp [localizedRerootRankedChildren] at present
  | cons child rest ih =>
      intro pair present
      rw [localizedRerootRankedChildren_cons input child rest] at present
      rcases List.mem_cons.mp present with same | tailPresent
      · rw [same]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem child
          (fst_mem_of_mem_localizedRerootRankedChildTail_audit input rest child 0 tailPresent)

/-- The ranked-label merge is a `range`-indexed `map`; membership exposes the sphere depth. -/
private theorem mem_mergeLocalizedRerootRankedLabelChildren_exists_depth
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    {layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))}
    (member : layer ∈ input.mergeLocalizedRerootRankedLabelChildren children) :
    ∃ depth : Nat,
      layer = (input.localizedRerootRankedChildren children).flatMap
        (fun child =>
          OfficialRuleMajorKey.prefixLayer child.2
            (child.1.rankedLabels.getD depth [])) := by
  unfold mergeLocalizedRerootRankedLabelChildren at member
  dsimp only at member
  rcases List.mem_map.mp member with ⟨depth, _depthMem, depthEq⟩
  exact ⟨depth, depthEq.symm⟩

/-- `prefixLayer` membership exposes the child entry it prefixes. -/
private theorem mem_prefixLayer_forward {α : Type*} {slot : Nat}
    {layer : List (OfficialSparseEntry α)} {entry : OfficialSparseEntry α}
    (member : entry ∈ OfficialRuleMajorKey.prefixLayer slot layer) :
    ∃ source ∈ layer, entry.1 = slot :: source.1 ∧ entry.2 = source.2 := by
  unfold OfficialRuleMajorKey.prefixLayer at member
  rcases List.mem_map.mp member with ⟨source, sourceMem, sourceEq⟩
  subst entry
  exact ⟨source, sourceMem, rfl, rfl⟩

/-- A member of a padded sphere lies in one of the stack's layers. -/
private theorem exists_layer_mem_of_mem_getD {α : Type*}
    {l : List (List α)} {depth : Nat} {x : α}
    (member : x ∈ l.getD depth []) :
    ∃ layer, layer ∈ l ∧ x ∈ layer := by
  rw [List.getD_eq_getElem?_getD] at member
  cases observed : l[depth]? with
  | none =>
      rw [observed] at member
      simp at member
  | some layer =>
      rw [observed] at member
      simp only [Option.getD_some] at member
      exact ⟨layer, List.mem_of_getElem? observed, member⟩

/-- The `mapM` child-key computation returns, for every produced key, the cursor that produced
it.  Local copy needed because the corresponding lemma in
`LocalizedRerootCumulativeRule45Key` is private. -/
private theorem mapM_buildLocalizedRerootCumulativeRule45Key?_member_audit
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys : List input.LocalizedRerootCumulativeRule45Key),
      cursors.mapM (input.buildLocalizedRerootCumulativeRule45Key?
        stage target view fuel) = some keys →
      ∀ key, key ∈ keys →
        ∃ cursor, cursor ∈ cursors ∧
          input.buildLocalizedRerootCumulativeRule45Key?
            stage target view fuel cursor = some key
  | [], keys, computed, key, present => by
      simp at computed
      subst keys
      simp at present
  | cursor :: cursors, keys, computed, key, present => by
      rw [List.mapM_cons] at computed
      cases headComputed : input.buildLocalizedRerootCumulativeRule45Key?
          stage target view fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (input.buildLocalizedRerootCumulativeRule45Key?
                stage target view fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              rcases List.mem_cons.mp present with rfl | tailPresent
              · exact ⟨cursor, by simp, headComputed⟩
              · rcases input.mapM_buildLocalizedRerootCumulativeRule45Key?_member_audit
                    stage target view cursors tail tailComputed key tailPresent with
                  ⟨source, sourcePresent, sourceComputed⟩
                exact ⟨source, List.mem_cons_of_mem cursor sourcePresent, sourceComputed⟩

/-- **Provenance invariant.**  Every label in the `rankedLabels` stack of a successfully built
cumulative key is the restricted-view reading of a strict depth dependency of the target.
Neither the constitutional nor the descriptor component participates in this statement. -/
theorem buildLocalizedRerootCumulativeRule45Key?_rankedLabels_dependencySourced
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel cursor = some key →
      RankedLabelsDependencySourced input target view key.rankedLabels := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor key computed
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            unfold RankedLabelsDependencySourced
            intro layer hlayer entry hentry label hlabel
            dsimp only at hlayer hlabel
            have layerEq : layer =
                [([], input.localizedDependencyLabel target view cursor)] := by
              simpa using (List.mem_singleton.mp hlayer)
            subst layer
            have entryEq : entry =
                ([], input.localizedDependencyLabel target view cursor) := by
              simpa using (List.mem_singleton.mp hentry)
            subst entry
            have hlabel' : input.localizedDependencyLabel target view cursor = some label := by
              simpa using hlabel
            by_cases dependency : input.LocalizedDepthDependency cursor.occurrence target
            · exact ⟨cursor.occurrence, dependency, by
                unfold localizedDependencyLabel at hlabel'
                rw [dif_pos dependency] at hlabel'
                exact hlabel'⟩
            · have noneEq :=
                input.localizedDependencyLabel_eq_none_of_not_dependency
                  target view cursor dependency
              rw [noneEq] at hlabel'
              simp at hlabel'
          · simp [childrenComputed, terminal] at computed
  | succ fuel ih =>
      intro cursor key computed
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            unfold RankedLabelsDependencySourced
            intro layer hlayer entry hentry label hlabel
            dsimp only at hlayer hlabel
            have layerEq : layer =
                [([], input.localizedDependencyLabel target view cursor)] := by
              simpa using (List.mem_singleton.mp hlayer)
            subst layer
            have entryEq : entry =
                ([], input.localizedDependencyLabel target view cursor) := by
              simpa using (List.mem_singleton.mp hentry)
            subst entry
            have hlabel' : input.localizedDependencyLabel target view cursor = some label := by
              simpa using hlabel
            by_cases dependency : input.LocalizedDepthDependency cursor.occurrence target
            · exact ⟨cursor.occurrence, dependency, by
                unfold localizedDependencyLabel at hlabel'
                rw [dif_pos dependency] at hlabel'
                exact hlabel'⟩
            · have noneEq :=
                input.localizedDependencyLabel_eq_none_of_not_dependency
                  target view cursor dependency
              rw [noneEq] at hlabel'
              simp at hlabel'
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedRerootCumulativeRule45Key?
                  stage target view fuel) with
            | none => simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
                subst key
                unfold RankedLabelsDependencySourced
                intro layer hlayer entry hentry label hlabel
                dsimp only at hlayer hlabel
                rcases List.mem_cons.mp hlayer with headLayer | mergedLayer
                · have layerEq : layer =
                      [([], input.localizedDependencyLabel target view cursor)] := headLayer
                  subst layer
                  have entryEq : entry =
                      ([], input.localizedDependencyLabel target view cursor) := by
                    simpa using (List.mem_singleton.mp hentry)
                  subst entry
                  have hlabel' :
                      input.localizedDependencyLabel target view cursor = some label := by
                    simpa using hlabel
                  by_cases dependency : input.LocalizedDepthDependency cursor.occurrence target
                  · exact ⟨cursor.occurrence, dependency, by
                      unfold localizedDependencyLabel at hlabel'
                      rw [dif_pos dependency] at hlabel'
                      exact hlabel'⟩
                  · have noneEq :=
                      input.localizedDependencyLabel_eq_none_of_not_dependency
                        target view cursor dependency
                    rw [noneEq] at hlabel'
                    simp at hlabel'
                · obtain ⟨depth, layerEq⟩ :=
                    mem_mergeLocalizedRerootRankedLabelChildren_exists_depth input
                      (input.sortLocalizedRerootCumulativeRule45Keys childKeys) mergedLayer
                  subst layer
                  rcases List.mem_flatMap.mp hentry with ⟨pair, pairMem, entryMem⟩
                  rcases mem_prefixLayer_forward entryMem with
                    ⟨sourceEntry, sourceEntryMem, _entryAddress, entryLabel⟩
                  have pairInSorted : pair.1 ∈
                      input.sortLocalizedRerootCumulativeRule45Keys childKeys :=
                    fst_mem_of_mem_localizedRerootRankedChildren_audit input
                      (input.sortLocalizedRerootCumulativeRule45Keys childKeys) pairMem
                  have pairInChildKeys : pair.1 ∈ childKeys :=
                    (input.sortLocalizedRerootCumulativeRule45Keys_perm childKeys).mem_iff.mp
                      pairInSorted
                  rcases input.mapM_buildLocalizedRerootCumulativeRule45Key?_member_audit
                      stage target view children childKeys childKeysComputed
                      pair.1 pairInChildKeys with
                    ⟨childCursor, _childCursorMem, childBuilt⟩
                  have sourced := ih childCursor pair.1 childBuilt
                  obtain ⟨sourceLayer, sourceLayerMem, sourceEntryInLayer⟩ :=
                    exists_layer_mem_of_mem_getD sourceEntryMem
                  have sourceLabel : sourceEntry.2 = some label :=
                    entryLabel.symm.trans hlabel
                  exact sourced sourceLayer sourceLayerMem sourceEntry sourceEntryInLayer
                    label sourceLabel

/-- **Ancestor exclusion.**  Any label that reaches a successful key's `rankedLabels` comes
from a strictly deeper source whose address is not a prefix of the target address.  In
particular no actual carrier ancestor contributes a label. -/
theorem buildLocalizedRerootCumulativeRule45Key?_labeled_entry_witness
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (built : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel cursor = some key)
    {layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))}
    {entry : OfficialSparseEntry (Option LocalizedAuxiliaryLabel)}
    (layerMem : layer ∈ key.rankedLabels)
    (entryMem : entry ∈ layer)
    {label : LocalizedAuxiliaryLabel}
    (entryLabel : entry.2 = some label) :
    ∃ source : input.LocalizedCIPOccurrence carrierFuel,
      ∃ dependency : input.LocalizedDepthDependency source target,
        view source dependency = some label ∧
          ¬ source.1.address <+: target.1.address := by
  have sourced := input.buildLocalizedRerootCumulativeRule45Key?_rankedLabels_dependencySourced
    stage target view fuel cursor key built
  obtain ⟨source, dependency, observed⟩ :=
    sourced layer layerMem entry entryMem label entryLabel
  refine ⟨source, dependency, observed, ?_⟩
  intro addressPrefix
  have lengthLe : source.1.address.length ≤ target.1.address.length :=
    List.IsPrefix.length_le addressPrefix
  have deeper := dependency.2
  omega

/-! ## Descriptor population of the Rule-4b selector -/

/-- Every descriptor extracted at a fixed rank path is the payload of a chiral observation at
that path. -/
theorem mem_localizedChiralDescriptorsAtRank_implies_entry
    (rank : List Nat) :
    ∀ (observations : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))
      (descriptor : RS),
      descriptor ∈ localizedChiralDescriptorsAtRank rank observations →
      ∃ entry, entry ∈ observations ∧ entry.2 = some (.chiral descriptor)
  | [], _descriptor, member => by
      simp [localizedChiralDescriptorsAtRank] at member
  | (observedRank, label) :: observations, descriptor, member => by
      cases label with
      | none =>
          simp only [localizedChiralDescriptorsAtRank] at member
          split at member
          · obtain ⟨entry, entryMem, entryLabel⟩ :=
              mem_localizedChiralDescriptorsAtRank_implies_entry rank observations
                descriptor member
            exact ⟨entry, List.mem_cons_of_mem _ entryMem, entryLabel⟩
          · obtain ⟨entry, entryMem, entryLabel⟩ :=
              mem_localizedChiralDescriptorsAtRank_implies_entry rank observations
                descriptor member
            exact ⟨entry, List.mem_cons_of_mem _ entryMem, entryLabel⟩
      | some label =>
          cases label with
          | pseudoasymmetric _pseudo =>
              simp only [localizedChiralDescriptorsAtRank] at member
              split at member
              · obtain ⟨entry, entryMem, entryLabel⟩ :=
                  mem_localizedChiralDescriptorsAtRank_implies_entry rank observations
                    descriptor member
                exact ⟨entry, List.mem_cons_of_mem _ entryMem, entryLabel⟩
              · obtain ⟨entry, entryMem, entryLabel⟩ :=
                  mem_localizedChiralDescriptorsAtRank_implies_entry rank observations
                    descriptor member
                exact ⟨entry, List.mem_cons_of_mem _ entryMem, entryLabel⟩
          | chiral chiralDescriptor =>
              simp only [localizedChiralDescriptorsAtRank] at member
              split at member
              · rcases List.mem_cons.mp member with same | tailMember
                · subst descriptor
                  exact ⟨(observedRank, some (.chiral chiralDescriptor)),
                    List.mem_cons_self, rfl⟩
                · obtain ⟨entry, entryMem, entryLabel⟩ :=
                    mem_localizedChiralDescriptorsAtRank_implies_entry rank observations
                      descriptor tailMember
                  exact ⟨entry, List.mem_cons_of_mem _ entryMem, entryLabel⟩
              · obtain ⟨entry, entryMem, entryLabel⟩ :=
                  mem_localizedChiralDescriptorsAtRank_implies_entry rank observations
                    descriptor member
                exact ⟨entry, List.mem_cons_of_mem _ entryMem, entryLabel⟩

/-- Every descriptor in the first chiral rank population of a layer is the payload of a chiral
observation in that layer. -/
theorem mem_localizedFirstChiralRankPopulationInLayer_implies_entry :
    ∀ (layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))
      (descriptors : List RS),
      localizedFirstChiralRankPopulationInLayer layer = some descriptors →
      ∀ descriptor : RS, descriptor ∈ descriptors →
      ∃ entry, entry ∈ layer ∧ entry.2 = some (.chiral descriptor)
  | [], _descriptors, computed, _descriptor, _member => by
      simp [localizedFirstChiralRankPopulationInLayer] at computed
  | (rank, label) :: observations, descriptors, computed, descriptor, member => by
      cases label with
      | none =>
          have computed' :
              localizedFirstChiralRankPopulationInLayer observations = some descriptors := by
            simpa [localizedFirstChiralRankPopulationInLayer] using computed
          obtain ⟨entry, entryMem, entryLabel⟩ :=
            mem_localizedFirstChiralRankPopulationInLayer_implies_entry
              observations descriptors computed' descriptor member
          exact ⟨entry, List.mem_cons_of_mem (rank, none) entryMem, entryLabel⟩
      | some label =>
          cases label with
          | pseudoasymmetric _pseudo =>
              have computed' :
                  localizedFirstChiralRankPopulationInLayer observations = some descriptors := by
                simpa [localizedFirstChiralRankPopulationInLayer] using computed
              obtain ⟨entry, entryMem, entryLabel⟩ :=
                mem_localizedFirstChiralRankPopulationInLayer_implies_entry
                  observations descriptors computed' descriptor member
              exact ⟨entry, List.mem_cons_of_mem
                (rank, some (.pseudoasymmetric _pseudo)) entryMem, entryLabel⟩
          | chiral chiralDescriptor =>
              have computed' :
                  some (chiralDescriptor ::
                    localizedChiralDescriptorsAtRank rank observations) = some descriptors := by
                simpa [localizedFirstChiralRankPopulationInLayer] using computed
              have descriptorsEq : descriptors =
                  chiralDescriptor :: localizedChiralDescriptorsAtRank rank observations := by
                simpa using computed'.symm
              subst descriptors
              rcases List.mem_cons.mp member with same | tailMember
              · subst descriptor
                exact ⟨(rank, some (.chiral chiralDescriptor)), List.mem_cons_self, rfl⟩
              · obtain ⟨entry, entryMem, entryLabel⟩ :=
                  mem_localizedChiralDescriptorsAtRank_implies_entry rank observations
                    descriptor tailMember
                exact ⟨entry, List.mem_cons_of_mem (rank, some (.chiral chiralDescriptor))
                  entryMem, entryLabel⟩

/-- Every descriptor in the first chiral rank population of a ranked-label stack is the payload
of a chiral observation in one of the stack's layers. -/
theorem mem_localizedFirstChiralRankPopulation_implies_entry :
    ∀ (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))),
      ∀ descriptor : RS, descriptor ∈ localizedFirstChiralRankPopulation layers →
      ∃ layer, layer ∈ layers ∧ ∃ entry, entry ∈ layer ∧
        entry.2 = some (.chiral descriptor)
  | [], descriptor, member => by
      simp [localizedFirstChiralRankPopulation] at member
  | layer :: layers, descriptor, member => by
      unfold localizedFirstChiralRankPopulation at member
      cases observed : localizedFirstChiralRankPopulationInLayer layer with
      | some descriptors =>
          have member' : descriptor ∈ descriptors := by
            simpa [observed] using member
          obtain ⟨entry, entryMem, entryLabel⟩ :=
            mem_localizedFirstChiralRankPopulationInLayer_implies_entry
              layer descriptors observed descriptor member'
          exact ⟨layer, List.mem_cons_self, entry, entryMem, entryLabel⟩
      | none =>
          have member' : descriptor ∈ localizedFirstChiralRankPopulation layers := by
            simpa [observed] using member
          obtain ⟨inner, innerMem, entry, entryMem, entryLabel⟩ :=
            mem_localizedFirstChiralRankPopulation_implies_entry layers descriptor member'
          exact ⟨inner, List.mem_cons_of_mem layer innerMem, entry, entryMem, entryLabel⟩

/-! ### Majority membership in the selected reference population -/

/-- A positive filtered length exhibits a member satisfying the filter. -/
private theorem exists_mem_of_filter_length_pos {α : Type*}
    (l : List α) (p : α → Bool) (positive : 0 < (l.filter p).length) :
    ∃ a, a ∈ l ∧ p a = true := by
  obtain ⟨a, member⟩ := List.exists_mem_of_length_pos positive
  exact ⟨a, (List.mem_filter.mp member).1, (List.mem_filter.mp member).2⟩

/-- Positive `R` count yields an `R` member. -/
private theorem eq_R_mem_of_filter_length_pos {descriptors : List RS}
    (positive : 0 < (descriptors.filter fun d => d == RS.R).length) :
    RS.R ∈ descriptors := by
  obtain ⟨a, aMem, aBeq⟩ := exists_mem_of_filter_length_pos descriptors
    (fun d => d == RS.R) positive
  have same : a = RS.R := by simpa using aBeq
  subst a
  exact aMem

/-- Positive `S` count yields an `S` member. -/
private theorem eq_S_mem_of_filter_length_pos {descriptors : List RS}
    (positive : 0 < (descriptors.filter fun d => d == RS.S).length) :
    RS.S ∈ descriptors := by
  obtain ⟨a, aMem, aBeq⟩ := exists_mem_of_filter_length_pos descriptors
    (fun d => d == RS.S) positive
  have same : a = RS.S := by simpa using aBeq
  subst a
  exact aMem

/-- Under a tied nonempty population, `R` occurs. -/
private theorem eq_R_of_mem_of_tied_nonempty {descriptors : List RS}
    (nonempty : descriptors ≠ [])
    (tied : (descriptors.filter fun d => d == RS.R).length =
      (descriptors.filter fun d => d == RS.S).length) :
    RS.R ∈ descriptors := by
  by_contra notMember
  have filterR : (descriptors.filter fun d => d == RS.R) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    cases a with
    | R => exact (notMember ha).elim
    | S => simp
  have rZero : (descriptors.filter fun d => d == RS.R).length = 0 := by
    rw [filterR]
    rfl
  have sZero : (descriptors.filter fun d => d == RS.S).length = 0 := by
    rw [← tied, rZero]
  have filterS : (descriptors.filter fun d => d == RS.S) = [] :=
    List.eq_nil_of_length_eq_zero sZero
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil descriptors nonempty
  have rFail : (a == RS.R) = false := by
    cases rBeq : (a == RS.R) with
    | false => rfl
    | true =>
        have memberFilter : a ∈ descriptors.filter (fun d => d == RS.R) :=
          List.mem_filter.mpr ⟨ha, rBeq⟩
        rw [filterR] at memberFilter
        simp at memberFilter
  have sFail : (a == RS.S) = false := by
    cases sBeq : (a == RS.S) with
    | false => rfl
    | true =>
        have memberFilter : a ∈ descriptors.filter (fun d => d == RS.S) :=
          List.mem_filter.mpr ⟨ha, sBeq⟩
        rw [filterS] at memberFilter
        simp at memberFilter
  cases a <;> simp at rFail sFail

/-- Under a tied nonempty population, `S` occurs. -/
private theorem eq_S_of_mem_of_tied_nonempty {descriptors : List RS}
    (nonempty : descriptors ≠ [])
    (tied : (descriptors.filter fun d => d == RS.R).length =
      (descriptors.filter fun d => d == RS.S).length) :
    RS.S ∈ descriptors := by
  by_contra notMember
  have filterS : (descriptors.filter fun d => d == RS.S) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    cases a with
    | R => simp
    | S => exact (notMember ha).elim
  have sZero : (descriptors.filter fun d => d == RS.S).length = 0 := by
    rw [filterS]
    rfl
  have rZero : (descriptors.filter fun d => d == RS.R).length = 0 := by
    rw [tied, sZero]
  have filterR : (descriptors.filter fun d => d == RS.R) = [] :=
    List.eq_nil_of_length_eq_zero rZero
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil descriptors nonempty
  have rFail : (a == RS.R) = false := by
    cases rBeq : (a == RS.R) with
    | false => rfl
    | true =>
        have memberFilter : a ∈ descriptors.filter (fun d => d == RS.R) :=
          List.mem_filter.mpr ⟨ha, rBeq⟩
        rw [filterR] at memberFilter
        simp at memberFilter
  have sFail : (a == RS.S) = false := by
    cases sBeq : (a == RS.S) with
    | false => rfl
    | true =>
        have memberFilter : a ∈ descriptors.filter (fun d => d == RS.S) :=
          List.mem_filter.mpr ⟨ha, sBeq⟩
        rw [filterS] at memberFilter
        simp at memberFilter
  cases a <;> simp at rFail sFail

/-- Every selected Rule-4b descriptor belongs to the population it was selected from. -/
theorem mem_localizedRule4bReferencesFromPopulation_implies_mem
    (descriptors : List RS) (descriptor : RS)
    (member : descriptor ∈ localizedRule4bReferencesFromPopulation descriptors) :
    descriptor ∈ descriptors := by
  have derived :=
    (localizedRule4bReferencesFromPopulation_eq_iff descriptors
      (localizedRule4bReferencesFromPopulation descriptors)).mp rfl
  unfold DeclarativeLocalizedRule4bReferencesFromPopulation at derived
  rcases derived with ⟨_empty, outputEq⟩ | ⟨notEmpty, majorCases⟩
  · rw [outputEq] at member
    simp at member
  · rcases majorCases with ⟨rMajor, outputEq⟩ | ⟨sMajor, outputEq⟩ | ⟨tied, outputEq⟩
    · rw [outputEq] at member
      simp at member
      subst descriptor
      exact eq_R_mem_of_filter_length_pos
        (Nat.lt_of_le_of_lt (Nat.zero_le _) rMajor)
    · rw [outputEq] at member
      simp at member
      subst descriptor
      exact eq_S_mem_of_filter_length_pos
        (Nat.lt_of_le_of_lt (Nat.zero_le _) sMajor)
    · rw [outputEq] at member
      simp at member
      rcases member with same | same
      · subst descriptor
        exact eq_R_of_mem_of_tied_nonempty notEmpty tied
      · subst descriptor
        exact eq_S_of_mem_of_tied_nonempty notEmpty tied

/-- Every selected Rule-4b descriptor occurs as a chiral label entry in the ranked-label stack. -/
theorem mem_localizedRule4bReferencesFromRankedLabels_implies_entry
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (descriptor : RS)
    (member : descriptor ∈ localizedRule4bReferencesFromRankedLabels layers) :
    ∃ layer, layer ∈ layers ∧ ∃ entry, entry ∈ layer ∧
      entry.2 = some (.chiral descriptor) := by
  unfold localizedRule4bReferencesFromRankedLabels at member
  exact mem_localizedFirstChiralRankPopulation_implies_entry layers descriptor
    (mem_localizedRule4bReferencesFromPopulation_implies_mem
      (localizedFirstChiralRankPopulation layers) descriptor member)

/-- **Reference selection reads only dependency-sourced labels.**  Every descriptor selected by
`localizedRule4bReferencesFromRankedLabels` is the restricted view at a strict depth dependency
of the target. -/
theorem localizedRule4bReferencesFromRankedLabels_dependencySourced
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (sourced : RankedLabelsDependencySourced input target view layers)
    (descriptor : RS)
    (member : descriptor ∈ localizedRule4bReferencesFromRankedLabels layers) :
    ∃ source : input.LocalizedCIPOccurrence carrierFuel,
      ∃ dependency : input.LocalizedDepthDependency source target,
        view source dependency = some (.chiral descriptor) := by
  obtain ⟨layer, layerMem, entry, entryMem, entryLabel⟩ :=
    mem_localizedRule4bReferencesFromRankedLabels_implies_entry layers descriptor member
  exact sourced layer layerMem entry entryMem (.chiral descriptor) entryLabel

/-- **End-to-end provenance for the Rule-4b selector on a built key.** -/
theorem buildLocalizedRerootCumulativeRule45Key?_rule4bReferences_dependencySourced
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (built : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel cursor = some key)
    (descriptor : RS)
    (member : descriptor ∈ localizedRule4bReferencesFromRankedLabels key.rankedLabels) :
    ∃ source : input.LocalizedCIPOccurrence carrierFuel,
      ∃ dependency : input.LocalizedDepthDependency source target,
        view source dependency = some (.chiral descriptor) :=
  localizedRule4bReferencesFromRankedLabels_dependencySourced input target view
    key.rankedLabels
    (input.buildLocalizedRerootCumulativeRule45Key?_rankedLabels_dependencySourced
      stage target view fuel cursor key built)
    descriptor member

/-- **Reference provenance for the unary Rule-4c wrapper.**  The reference selected by
`buildLocalizedRerootUniqueReferenceRule4cKey?` comes from a strict depth dependency of the
target, never from a shallower ancestor. -/
theorem buildLocalizedRerootUniqueReferenceRule4cKey?_reference_dependencySourced
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootUniqueReferenceRule4cKey)
    (computed : input.buildLocalizedRerootUniqueReferenceRule4cKey?
      target view fuel cursor = some key) :
    ∃ source : input.LocalizedCIPOccurrence carrierFuel,
      ∃ dependency : input.LocalizedDepthDependency source target,
        view source dependency = some (.chiral key.reference) := by
  unfold buildLocalizedRerootUniqueReferenceRule4cKey? at computed
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45Key?
      .rule4a target view fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      cases referencesComputed :
          localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels with
      | nil => simp [rule4aComputed, referencesComputed] at computed
      | cons reference references =>
          cases references with
          | nil =>
              cases rule4cComputed :
                  input.buildLocalizedRerootCumulativeRule45Key?
                    (.rule4c reference) target view fuel cursor with
              | none =>
                  simp [rule4aComputed, referencesComputed, rule4cComputed] at computed
              | some rule4cKey =>
                  simp [rule4aComputed, referencesComputed, rule4cComputed] at computed
                  subst key
                  have member : reference ∈
                      localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels := by
                    rw [referencesComputed]
                    exact List.mem_cons_self
                  exact input.buildLocalizedRerootCumulativeRule45Key?_rule4bReferences_dependencySourced
                    .rule4a target view cursor rule4aKey rule4aComputed reference member
          | cons second rest =>
              simp [rule4aComputed, referencesComputed] at computed

/-! ## The comparator does not read `rankedLabels` -/

/-- **Data independence.**  `compareLocalizedRerootCumulativeRule45Keys` depends only on
`constitutional` and `descriptor`.  Replacing `rankedLabels` on either side changes nothing, so
the 2018 constitutional-strictness theorem cannot by itself constrain which labels the Rule-4b
selector sees. -/
theorem compareLocalizedRerootCumulativeRule45Keys_rankedLabels_irrel
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (leftRankedLabels rightRankedLabels :
      List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    input.compareLocalizedRerootCumulativeRule45Keys
        { left with rankedLabels := leftRankedLabels }
        { right with rankedLabels := rightRankedLabels } =
      input.compareLocalizedRerootCumulativeRule45Keys left right := by
  unfold compareLocalizedRerootCumulativeRule45Keys
  rfl

/-- **Key-level sensitivity witness.**  For any base key there are two keys with the same
constitutional and descriptor components, hence equal under the cumulative comparator, whose
`rankedLabels` select opposite unique Rule-4b references.  This is a witness about the key data
type and the pure selector, not a molecule-backed frame. -/
theorem exists_referenceSensitive_keys
    (input : CertifiedLocalizedCIPInput)
    (base : input.LocalizedRerootCumulativeRule45Key) :
    ∃ left right : input.LocalizedRerootCumulativeRule45Key,
      left.constitutional = right.constitutional ∧
      left.descriptor = right.descriptor ∧
      input.compareLocalizedRerootCumulativeRule45Keys left right = Ordering.eq ∧
      localizedRule4bReferencesFromRankedLabels left.rankedLabels = [RS.R] ∧
      localizedRule4bReferencesFromRankedLabels right.rankedLabels = [RS.S] := by
  have baseRefl : input.compareLocalizedRerootCumulativeRule45Keys base base = Ordering.eq := by
    haveI : Std.TransCmp input.compareLocalizedRerootCumulativeRule45Keys :=
      input.compareLocalizedRerootCumulativeRule45Keys_transCmp
    exact Std.ReflCmp.compare_self
  refine ⟨{ base with rankedLabels := [[([], some (.chiral RS.R))]] },
    { base with rankedLabels := [[([], some (.chiral RS.S))]] }, rfl, rfl, ?_, ?_, ?_⟩
  · rw [compareLocalizedRerootCumulativeRule45Keys_rankedLabels_irrel]
    exact baseRefl
  · show localizedRule4bReferencesFromRankedLabels
      [[([], some (.chiral RS.R))]] = [RS.R]
    decide
  · show localizedRule4bReferencesFromRankedLabels
      [[([], some (.chiral RS.S))]] = [RS.S]
    decide

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDependencyLabel_eq_none_of_not_dependency
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDependencyLabel_eq_some_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.not_localizedDepthDependency_of_address_prefix
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDependencyLabel_eq_none_of_address_prefix
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.parentCursor_not_localizedDepthDependency
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule4b_parentCursor_dependencyLabel_eq_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_rankedLabels_dependencySourced
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_labeled_entry_witness
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedChiralDescriptorsAtRank_implies_entry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedFirstChiralRankPopulationInLayer_implies_entry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedFirstChiralRankPopulation_implies_entry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedRule4bReferencesFromPopulation_implies_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedRule4bReferencesFromRankedLabels_implies_entry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4bReferencesFromRankedLabels_dependencySourced
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_rule4bReferences_dependencySourced
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootUniqueReferenceRule4cKey?_reference_dependencySourced
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCumulativeRule45Keys_rankedLabels_irrel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_referenceSensitive_keys
