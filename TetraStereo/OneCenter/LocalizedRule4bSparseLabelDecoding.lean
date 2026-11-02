import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.OneCenter.LocalizedCumulativeUppercaseReflection
import TetraStereo.OneCenter.LocalizedConstitutionalObservable
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-!
# Relative label decoding on the sparse Rule-4b domain, and cumulative stage alignment

This module connects the *actual* cumulative Rules-4a--5 builders of
`LocalizedParametricCumulativeLabels` to the exact relative uppercase-label content that those
keys retain.

## What is proved here

1. **Scalar decoder of the Rule-4b priority vector.**  On the domain where every observation is
   either `none` (no recorded label) or an uppercase `.chiral` descriptor, the two-component
   cumulative vector of `.rule4b r` and `.rule4b s` is an exact encoding of the pair
   `(r, label)` up to the reflection rule
   `if r = s then label else reflectUppercaseOptionalLabel label`.  The domain restriction is
   essential: a lowercase `.pseudoasymmetric` label receives Rule-4a priority `1` and Rule-4b
   priority `0`, so `pseudo r` and `pseudo s` share the vector `[1, 0]` and cannot be decoded.

2. **Descriptor/label coherence of the actual builder.**  For the *actual*
   `buildLocalizedRerootCumulativeRule45KeyWithRead?`, success at any stage and fuel implies
   `key.descriptor = key.labels` mapped entrywise through
   `localizedCumulativeRule45Priority stage`, preserving every sorted sibling-slot address.  The
   proof follows the actual recursion (the frame reader, the cumulative sibling sort, and the
   descriptor/label merges); no extraction certificate is assumed.  In particular `key.labels`
   — not `rankedLabels` — is the sorted-address table, so the decoded positions are genuine slot
   addresses rather than equivalence-class prefixes.

3. **Address-preserving reflection of full label layers.**  Equality of the addressed sparse
   descriptors at stages `.rule4b r` and `.rule4b s`, together with coherence and the
   `none`/chiral-only reader discipline, forces
   `right.labels = if r = s then left.labels else reflectUppercaseRankedLabels left.labels`.
   Every sphere, address and entry is preserved; only the uppercase descriptors are swapped when
   the two references differ.

4. **Simultaneous constitutional and relative-label alignment at one stage-4b isomorphism.**
   Given actual `.rule4a` keys and actual `.rule4b` keys built on the *same* cursors and readers
   (fuels may differ), a Rule-4a comparison tie and a Rule-4b descriptor tie make the complete
   comparison-visible observables of the two Rule-4b keys equal.  This uses
   `buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative`,
   `declarative_constitutional_observable_unique` and
   `compareLocalizedRerootCumulativeRule45Keys_eq_iff_observable_eq`; no second comparator or
   alternate sort is introduced.  Combining it with items 2 and 3 yields one sorted-address
   correspondence that simultaneously preserves the constitutional data and the relative
   uppercase labels.

## Scope

`none` is the structural "no label observation at this cursor" value already consumed by the
cumulative priority vectors.  It is not identified with chemical nonstereogenicity, and no
physical reader is constructed here.  All statements are about the actual structural builders and
their actual tables.
-/

/-! ## The sparse (None / uppercase chiral) label domain -/

/-- Labels on which the Rule-4b priority vector decodes the reference/label pair: either no
recorded observation, or an uppercase chiral descriptor.  Lowercase pseudoasymmetric labels are
deliberately excluded. -/
def LocalizedRule4bSparseLabel (label : Option LocalizedAuxiliaryLabel) : Prop :=
  label = none ∨ ∃ descriptor : RS, label = some (.chiral descriptor)

@[simp] theorem localizedRule4bSparseLabel_none :
    LocalizedRule4bSparseLabel none :=
  Or.inl rfl

@[simp] theorem localizedRule4bSparseLabel_chiral (descriptor : RS) :
    LocalizedRule4bSparseLabel (some (.chiral descriptor)) :=
  Or.inr ⟨descriptor, rfl⟩

/-- A lowercase pseudoasymmetric observation is outside the sparse domain. -/
@[simp] theorem not_localizedRule4bSparseLabel_pseudoasymmetric (descriptor : PseudoRS) :
    ¬ LocalizedRule4bSparseLabel (some (.pseudoasymmetric descriptor)) := by
  rintro (same | ⟨chiral, same⟩)
  · cases same
  · cases same

/-- Uppercase reflection preserves the sparse domain. -/
theorem localizedRule4bSparseLabel_reflectUppercase {label : Option LocalizedAuxiliaryLabel}
    (sparse : LocalizedRule4bSparseLabel label) :
    LocalizedRule4bSparseLabel (reflectUppercaseOptionalLabel label) := by
  rcases sparse with rfl | ⟨descriptor, rfl⟩
  · exact localizedRule4bSparseLabel_none
  · exact localizedRule4bSparseLabel_chiral (RS.swap descriptor)

/-- Uppercase reflection is an involution on the whole observation alphabet (it fixes lowercase
pseudoasymmetric labels and swaps the two uppercase descriptors). -/
@[simp] theorem reflectUppercaseOptionalLabel_involutive
    (label : Option LocalizedAuxiliaryLabel) :
    reflectUppercaseOptionalLabel (reflectUppercaseOptionalLabel label) = label := by
  cases label with
  | none => rfl
  | some label =>
      cases label with
      | pseudoasymmetric descriptor => rfl
      | chiral descriptor => cases descriptor <;> rfl

/-! ## Scalar decoding of the Rule-4b priority vector -/

/-- **Scalar Rule-4b decoder.**  On the `none`/uppercase-chiral domain the cumulative Rule-4b
priority vector determines the observed label exactly up to the reflection rule: two vectors at
references `r` and `s` agree exactly when the second label is the first one, reflected when the
references differ.

The domain restriction cannot be dropped: `pseudo r` and `pseudo s` both encode as `[1, 0]`. -/
theorem localizedCumulativeRule45Priority_rule4b_eq_iff
    (leftReference rightReference : RS)
    (left right : Option LocalizedAuxiliaryLabel)
    (leftSparse : LocalizedRule4bSparseLabel left)
    (rightSparse : LocalizedRule4bSparseLabel right) :
    (localizedCumulativeRule45Priority (.rule4b leftReference) left =
      localizedCumulativeRule45Priority (.rule4b rightReference) right) ↔
      right = if leftReference = rightReference then left
        else reflectUppercaseOptionalLabel left := by
  rcases leftSparse with hleft | ⟨ld, hleft⟩
  · -- The left observation is absent.
    rcases rightSparse with hright | ⟨rd, hright⟩
    · subst hleft
      subst hright
      rcases leftReference with _ | _ <;> rcases rightReference with _ | _ <;>
        simp [localizedCumulativeRule45Priority, localizedRule4aPriority,
          localizedRule4bPriority, reflectUppercaseOptionalLabel]
    · subst hleft
      subst hright
      rcases leftReference with _ | _ <;> rcases rightReference with _ | _ <;>
        rcases rd with _ | _ <;>
        simp [localizedCumulativeRule45Priority, localizedRule4aPriority,
          localizedRule4bPriority, reflectUppercaseOptionalLabel, beq_iff_eq]
  · -- The left observation is an uppercase chiral descriptor.
    rcases rightSparse with hright | ⟨rd, hright⟩
    · subst hleft
      subst hright
      rcases leftReference with _ | _ <;> rcases rightReference with _ | _ <;>
        rcases ld with _ | _ <;>
        simp [localizedCumulativeRule45Priority, localizedRule4aPriority,
          localizedRule4bPriority, reflectUppercaseOptionalLabel, reflectUppercaseAuxiliaryLabel,
          beq_iff_eq]
    · subst hleft
      subst hright
      rcases leftReference with _ | _ <;> rcases rightReference with _ | _ <;>
        rcases ld with _ | _ <;> rcases rd with _ | _ <;>
        simp [localizedCumulativeRule45Priority, localizedRule4aPriority,
          localizedRule4bPriority, reflectUppercaseOptionalLabel, reflectUppercaseAuxiliaryLabel,
          RS.swap, beq_iff_eq]

/-- The Rule-4a priority component of a cumulative Rule-4b vector is its head entry. -/
theorem localizedRule4aPriority_eq_of_cumulativeRule4b_eq
    (leftReference rightReference : RS)
    (left right : Option LocalizedAuxiliaryLabel)
    (equal : localizedCumulativeRule45Priority (.rule4b leftReference) left =
      localizedCumulativeRule45Priority (.rule4b rightReference) right) :
    localizedRule4aPriority left = localizedRule4aPriority right := by
  have headEqual := congrArg (fun vector : List Nat => vector.head?) equal
  simpa [localizedCumulativeRule45Priority] using headEqual

/-- Matching Rule-4a priority components transfer the sparse domain to the second observation.
The first component is `0` exactly for `none` and `2` exactly for an uppercase chiral label, so
a pseudoasymmetric right observation can never match a sparse left observation. -/
theorem localizedRule4bSparseLabel_of_priority_eq
    {left right : Option LocalizedAuxiliaryLabel}
    (leftSparse : LocalizedRule4bSparseLabel left)
    (headEqual : localizedRule4aPriority left = localizedRule4aPriority right) :
    LocalizedRule4bSparseLabel right := by
  rcases leftSparse with hleft | ⟨ld, hleft⟩
  · subst hleft
    cases right with
    | none => exact Or.inl rfl
    | some label =>
        cases label with
        | pseudoasymmetric descriptor => simp [localizedRule4aPriority] at headEqual
        | chiral descriptor => simp [localizedRule4aPriority] at headEqual
  · subst hleft
    cases right with
    | none => simp [localizedRule4aPriority] at headEqual
    | some label =>
        cases label with
        | pseudoasymmetric descriptor => simp [localizedRule4aPriority] at headEqual
        | chiral descriptor => exact Or.inr ⟨descriptor, rfl⟩

/-- Decoding direction used by the list lifting: only the *left* label is required to be on the
sparse domain.  A right label outside the domain can never produce an equal vector, so the same
conclusion holds and, in particular, the decoded right label is again on the domain. -/
theorem localizedCumulativeRule45Priority_rule4b_eq_imp
    (leftReference rightReference : RS)
    (left right : Option LocalizedAuxiliaryLabel)
    (leftSparse : LocalizedRule4bSparseLabel left)
    (equal : localizedCumulativeRule45Priority (.rule4b leftReference) left =
      localizedCumulativeRule45Priority (.rule4b rightReference) right) :
    right = if leftReference = rightReference then left
      else reflectUppercaseOptionalLabel left := by
  have headEqual :=
    localizedRule4aPriority_eq_of_cumulativeRule4b_eq leftReference rightReference left right equal
  have rightSparse := localizedRule4bSparseLabel_of_priority_eq leftSparse headEqual
  exact (localizedCumulativeRule45Priority_rule4b_eq_iff leftReference rightReference left right
    leftSparse rightSparse).1 equal

/-! ## Descriptor/label coherence of the actual label-callback builder -/

/-- Every recorded observation in every label sphere lies on the sparse domain. -/
def LocalizedLabelLayersSparse
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) : Prop :=
  ∀ layer, layer ∈ layers → ∀ entry, entry ∈ layer →
    LocalizedRule4bSparseLabel entry.2

/-- Every successful `List.mapM` result element comes from some source element.  (The same fact is
private in `LocalizedParametricCumulativeLabels`; it is restated here because private names are not
importable.) -/
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

/-- An entry of a sphere selected by `getD` lies in one of the source spheres. -/
private theorem exists_mem_of_mem_getD {α : Type*}
    {layers : List (List α)} {depth : Nat} {entry : α}
    (present : entry ∈ layers.getD depth []) :
    ∃ layer, layer ∈ layers ∧ entry ∈ layer := by
  rw [List.getD_eq_getElem?_getD] at present
  cases looked : layers[depth]? with
  | none =>
      rw [looked] at present
      simp at present
  | some layer =>
      rw [looked] at present
      exact ⟨layer, List.mem_of_getElem? looked, present⟩

/-- A `foldl` of pointwise-equal sphere lengths over a list gives equal maxima. -/
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

/-- **Actual builder descriptor/label coherence.**  Any key produced by the label-callback
builder at any stage, fuel and cursor has its addressed sparse descriptor equal to its addressed
exact-label table read entrywise through the cumulative priority.  In particular the addresses in
`key.labels` are the actual sorted sibling slots, not equivalence-class rank prefixes. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_descriptor_eq_labels_projection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel cursor = some key →
      key.descriptor =
        OfficialRuleMajorKey.mapSourceLayers
          (localizedCumulativeRule45Priority stage) key.labels
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            rfl
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            rfl
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
                subst key
                dsimp only
                rw [OfficialRuleMajorKey.mapSourceLayers]
                simp only [List.map_cons, List.map_nil]
                congr 1
                exact mergeLocalizedRerootDescriptorChildren_eq_mapSourceLayers
                    input stage
                    (input.sortLocalizedRerootCumulativeRule45Keys childKeys)
                    (fun child childPresent => by
                      have sourcePresent : child ∈ childKeys :=
                        (input.sortLocalizedRerootCumulativeRule45Keys_perm childKeys).mem_iff.mp
                          childPresent
                      rcases localized_list_mapM_member
                          (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                            stage read fuel)
                          children childKeys childKeysComputed child sourcePresent with
                        ⟨childCursor, _childCursorPresent, childComputed⟩
                      exact
                        buildLocalizedRerootCumulativeRule45KeyWithRead?_descriptor_eq_labels_projection
                          input stage read fuel childCursor child childComputed)

/-- The coherence result in the requested pointwise form: the actual descriptor table is the
actual label table with every observation replaced by its cumulative priority vector, keeping each
sorted sibling-slot address. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_descriptor_eq_labels
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      stage read fuel cursor = some key) :
    key.descriptor =
      key.labels.map (List.map fun entry =>
        (entry.1, localizedCumulativeRule45Priority stage entry.2)) := by
  simpa [OfficialRuleMajorKey.mapSourceLayers, OfficialRuleMajorKey.mapObservation]
    using input.buildLocalizedRerootCumulativeRule45KeyWithRead?_descriptor_eq_labels_projection
      stage read fuel cursor key computed

/-- Membership lifting through the actual exact-label merge. -/
private theorem localizedLabelLayersSparse_mergeLocalizedRerootLabelChildren
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (sparse : ∀ child, child ∈ children → LocalizedLabelLayersSparse child.labels) :
    LocalizedLabelLayersSparse (input.mergeLocalizedRerootLabelChildren children) := by
  intro layer layerPresent entry entryPresent
  unfold mergeLocalizedRerootLabelChildren at layerPresent
  dsimp only at layerPresent
  rw [List.mem_map] at layerPresent
  rcases layerPresent with ⟨depth, _depthPresent, rfl⟩
  rw [List.mem_flatMap] at entryPresent
  rcases entryPresent with ⟨child, childPresent, entryPresent⟩
  unfold OfficialRuleMajorKey.prefixLayer at entryPresent
  rw [List.mem_map] at entryPresent
  rcases entryPresent with ⟨innerEntry, innerEntryPresent, rfl⟩
  have childSource : child.1 ∈ children := List.fst_mem_of_mem_zipIdx childPresent
  rcases exists_mem_of_mem_getD innerEntryPresent with
    ⟨innerLayer, innerLayerPresent, innerEntryInLayer⟩
  exact sparse child.1 childSource innerLayer innerLayerPresent innerEntry innerEntryInLayer

/-- **Sparse reader transfer.**  If the callback never returns a lowercase pseudoasymmetric
observation, then every observation recorded anywhere in `key.labels` by the actual builder is
again either absent or uppercase chiral. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_sparse
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (readerSparse : ∀ cursor, LocalizedRule4bSparseLabel (read cursor)) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel cursor = some key →
      LocalizedLabelLayersSparse key.labels
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            intro layer layerPresent entry entryPresent
            simp at layerPresent
            subst layer
            simp at entryPresent
            subst entry
            exact readerSparse cursor
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            intro layer layerPresent entry entryPresent
            simp at layerPresent
            subst layer
            simp at entryPresent
            subst entry
            exact readerSparse cursor
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
                subst key
                intro layer layerPresent entry entryPresent
                dsimp only at layerPresent
                have headSparse : LocalizedLabelLayersSparse [[([], read cursor)]] := by
                  intro headLayer headLayerPresent headEntry headEntryPresent
                  simp at headLayerPresent
                  subst headLayer
                  simp at headEntryPresent
                  subst headEntry
                  exact readerSparse cursor
                have mergeSparse : LocalizedLabelLayersSparse
                    (input.mergeLocalizedRerootLabelChildren
                      (input.sortLocalizedRerootCumulativeRule45Keys childKeys)) :=
                  localizedLabelLayersSparse_mergeLocalizedRerootLabelChildren input
                    (input.sortLocalizedRerootCumulativeRule45Keys childKeys)
                    (fun child childPresent => by
                      have sourcePresent : child ∈ childKeys :=
                        (input.sortLocalizedRerootCumulativeRule45Keys_perm childKeys).mem_iff.mp
                          childPresent
                      rcases localized_list_mapM_member
                          (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                            stage read fuel)
                          children childKeys childKeysComputed child sourcePresent with
                        ⟨childCursor, _childCursorPresent, childComputed⟩
                      exact buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_sparse
                        input stage read readerSparse fuel childCursor child childComputed)
                rcases List.mem_cons.mp layerPresent with same | mergeLayer
                · subst layer
                  exact headSparse [([], read cursor)] (by simp) entry entryPresent
                · exact mergeSparse layer mergeLayer entry entryPresent

/-! ## Lifting the scalar decoder to addressed label layers -/

/-- Entrywise decoding at a fixed reference: equal addressed priority spheres force their exact
label spheres to coincide.  Only the left sphere needs to lie on the sparse domain. -/
private theorem localizedSparseLayer_eq_of_priority_layer_eq
    (leftReference : RS) :
    ∀ (leftLayer rightLayer :
        List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))),
      (∀ entry, entry ∈ leftLayer → LocalizedRule4bSparseLabel entry.2) →
      leftLayer.map (fun entry => (entry.1,
        localizedCumulativeRule45Priority (.rule4b leftReference) entry.2)) =
      rightLayer.map (fun entry => (entry.1,
        localizedCumulativeRule45Priority (.rule4b leftReference) entry.2)) →
      rightLayer = leftLayer
  | [], rightLayer, _sparse, mapped => by
      cases rightLayer with
      | nil => rfl
      | cons head tail => simp at mapped
  | leftHead :: leftTail, rightLayer, sparse, mapped => by
      cases rightLayer with
      | nil => simp at mapped
      | cons rightHead rightTail =>
          simp only [List.map_cons] at mapped
          injection mapped with headMapped tailMapped
          have addressEqual : rightHead.1 = leftHead.1 :=
            (congrArg Prod.fst headMapped).symm
          have priorityEqual :
              localizedCumulativeRule45Priority (.rule4b leftReference) leftHead.2 =
                localizedCumulativeRule45Priority (.rule4b leftReference) rightHead.2 :=
            congrArg Prod.snd headMapped
          have labelEqual : rightHead.2 = leftHead.2 := by
            have decoded := localizedCumulativeRule45Priority_rule4b_eq_imp
              leftReference leftReference leftHead.2 rightHead.2
              (sparse leftHead (by simp)) priorityEqual
            simpa using decoded
          have headEqual : rightHead = leftHead := Prod.ext addressEqual labelEqual
          have tailEqual : rightTail = leftTail :=
            localizedSparseLayer_eq_of_priority_layer_eq leftReference leftTail rightTail
              (fun entry present => sparse entry (List.mem_cons_of_mem leftHead present))
              tailMapped
          rw [headEqual, tailEqual]

/-- Entrywise decoding at two different references: equal addressed priority spheres force the
right exact-label sphere to be the uppercase reflection of the left one. -/
private theorem localizedSparseLayer_eq_map_reflect_of_priority_layer_eq
    (leftReference rightReference : RS) (different : leftReference ≠ rightReference) :
    ∀ (leftLayer rightLayer :
        List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))),
      (∀ entry, entry ∈ leftLayer → LocalizedRule4bSparseLabel entry.2) →
      leftLayer.map (fun entry => (entry.1,
        localizedCumulativeRule45Priority (.rule4b leftReference) entry.2)) =
      rightLayer.map (fun entry => (entry.1,
        localizedCumulativeRule45Priority (.rule4b rightReference) entry.2)) →
      rightLayer = leftLayer.map reflectUppercaseRankedEntry
  | [], rightLayer, _sparse, mapped => by
      cases rightLayer with
      | nil => rfl
      | cons head tail => simp at mapped
  | leftHead :: leftTail, rightLayer, sparse, mapped => by
      cases rightLayer with
      | nil => simp at mapped
      | cons rightHead rightTail =>
          simp only [List.map_cons] at mapped
          injection mapped with headMapped tailMapped
          have addressEqual : rightHead.1 = leftHead.1 :=
            (congrArg Prod.fst headMapped).symm
          have priorityEqual :
              localizedCumulativeRule45Priority (.rule4b leftReference) leftHead.2 =
                localizedCumulativeRule45Priority (.rule4b rightReference) rightHead.2 :=
            congrArg Prod.snd headMapped
          have labelEqual : rightHead.2 = reflectUppercaseOptionalLabel leftHead.2 := by
            have decoded := localizedCumulativeRule45Priority_rule4b_eq_imp
              leftReference rightReference leftHead.2 rightHead.2
              (sparse leftHead (by simp)) priorityEqual
            simpa [different] using decoded
          have headEqual : rightHead = reflectUppercaseRankedEntry leftHead := by
            refine Prod.ext ?_ ?_
            · simpa [reflectUppercaseRankedEntry] using addressEqual
            · simpa [reflectUppercaseRankedEntry] using labelEqual
          have tailEqual : rightTail = leftTail.map reflectUppercaseRankedEntry :=
            localizedSparseLayer_eq_map_reflect_of_priority_layer_eq leftReference rightReference
              different leftTail rightTail
              (fun entry present => sparse entry (List.mem_cons_of_mem leftHead present))
              tailMapped
          rw [List.map_cons, headEqual, tailEqual]

/-- Sphere-level decoding at a fixed reference. -/
private theorem localizedSparseLayers_eq_of_priority_layers_eq
    (leftReference : RS) :
    ∀ (leftLayers rightLayers :
        List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))),
      LocalizedLabelLayersSparse leftLayers →
      leftLayers.map (List.map (fun entry => (entry.1,
        localizedCumulativeRule45Priority (.rule4b leftReference) entry.2))) =
      rightLayers.map (List.map (fun entry => (entry.1,
        localizedCumulativeRule45Priority (.rule4b leftReference) entry.2))) →
      rightLayers = leftLayers
  | [], rightLayers, _sparse, mapped => by
      cases rightLayers with
      | nil => rfl
      | cons layer layers => simp at mapped
  | leftLayer :: leftLayers, rightLayers, sparse, mapped => by
      cases rightLayers with
      | nil => simp at mapped
      | cons rightLayer rightLayers =>
          simp only [List.map_cons] at mapped
          injection mapped with headMapped tailMapped
          have headEqual : rightLayer = leftLayer :=
            localizedSparseLayer_eq_of_priority_layer_eq leftReference leftLayer rightLayer
              (fun entry present => sparse leftLayer (by simp) entry present) headMapped
          have tailEqual : rightLayers = leftLayers :=
            localizedSparseLayers_eq_of_priority_layers_eq leftReference leftLayers rightLayers
              (fun layer present entry entryPresent =>
                sparse layer (List.mem_cons_of_mem leftLayer present) entry entryPresent)
              tailMapped
          rw [headEqual, tailEqual]

/-- Sphere-level decoding at two different references. -/
private theorem localizedSparseLayers_eq_map_reflect_of_priority_layers_eq
    (leftReference rightReference : RS) (different : leftReference ≠ rightReference) :
    ∀ (leftLayers rightLayers :
        List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))),
      LocalizedLabelLayersSparse leftLayers →
      leftLayers.map (List.map (fun entry => (entry.1,
        localizedCumulativeRule45Priority (.rule4b leftReference) entry.2))) =
      rightLayers.map (List.map (fun entry => (entry.1,
        localizedCumulativeRule45Priority (.rule4b rightReference) entry.2))) →
      rightLayers = reflectUppercaseRankedLabels leftLayers
  | [], rightLayers, _sparse, mapped => by
      cases rightLayers with
      | nil => rfl
      | cons layer layers => simp at mapped
  | leftLayer :: leftLayers, rightLayers, sparse, mapped => by
      cases rightLayers with
      | nil => simp at mapped
      | cons rightLayer rightLayers =>
          simp only [List.map_cons] at mapped
          injection mapped with headMapped tailMapped
          have headEqual : rightLayer = leftLayer.map reflectUppercaseRankedEntry :=
            localizedSparseLayer_eq_map_reflect_of_priority_layer_eq leftReference rightReference
              different leftLayer rightLayer
              (fun entry present => sparse leftLayer (by simp) entry present) headMapped
          have tailEqual : rightLayers = reflectUppercaseRankedLabels leftLayers :=
            localizedSparseLayers_eq_map_reflect_of_priority_layers_eq leftReference rightReference
              different leftLayers rightLayers
              (fun layer present entry entryPresent =>
                sparse layer (List.mem_cons_of_mem leftLayer present) entry entryPresent)
              tailMapped
          rw [headEqual, tailEqual]
          unfold reflectUppercaseRankedLabels
          rw [List.map_cons]

/-- **Address-preserving full-layer decoding.**  Equality of the addressed sparse priority tables
at `.rule4b r` and `.rule4b s`, with the left table on the `none`/uppercase-chiral domain, forces
the right exact-label table to be the left one, reflected entrywise when the references differ.
Every sphere and every sorted sibling-slot address is preserved. -/
theorem localizedLabelLayers_eq_or_reflect_of_priority_map_eq
    (leftReference rightReference : RS)
    (leftLabels rightLabels :
      List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (sparse : LocalizedLabelLayersSparse leftLabels)
    (mapped :
      leftLabels.map (List.map (fun entry => (entry.1,
        localizedCumulativeRule45Priority (.rule4b leftReference) entry.2))) =
      rightLabels.map (List.map (fun entry => (entry.1,
        localizedCumulativeRule45Priority (.rule4b rightReference) entry.2)))) :
    rightLabels = if leftReference = rightReference then leftLabels
      else reflectUppercaseRankedLabels leftLabels := by
  by_cases same : leftReference = rightReference
  · subst leftReference
    have equal := localizedSparseLayers_eq_of_priority_layers_eq rightReference
      leftLabels rightLabels sparse mapped
    simp [equal]
  · have reflected := localizedSparseLayers_eq_map_reflect_of_priority_layers_eq
      leftReference rightReference same leftLabels rightLabels sparse mapped
    rw [if_neg same]
    exact reflected

/-- **Key-level sparse label decoding.**  For actual keys whose addressed sparse descriptor is
their addressed label table read through the cumulative priority, equality of the descriptors at
`.rule4b r` and `.rule4b s` determines the exact labels up to uppercase reflection. -/
theorem localizedLabelLayers_eq_or_reflect_of_descriptor_eq
    (input : CertifiedLocalizedCIPInput)
    (leftReference rightReference : RS)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (leftCoherent : left.descriptor = left.labels.map (List.map fun entry =>
      (entry.1, localizedCumulativeRule45Priority (.rule4b leftReference) entry.2)))
    (rightCoherent : right.descriptor = right.labels.map (List.map fun entry =>
      (entry.1, localizedCumulativeRule45Priority (.rule4b rightReference) entry.2)))
    (sparse : LocalizedLabelLayersSparse left.labels)
    (descriptorEqual : left.descriptor = right.descriptor) :
    right.labels = if leftReference = rightReference then left.labels
      else reflectUppercaseRankedLabels left.labels := by
  refine localizedLabelLayers_eq_or_reflect_of_priority_map_eq leftReference rightReference
    left.labels right.labels sparse ?_
  rw [← leftCoherent, descriptorEqual, rightCoherent]

/-- **Actual builder label decoding.**  Applying the key-level decoder to two successful runs of
the actual label-callback builder, one at `.rule4b r` and one at `.rule4b s` (possibly different
cursors and recursion budgets), with a `none`/uppercase-chiral reader discipline. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_eq_or_reflect
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (readerSparse : ∀ cursor, LocalizedRule4bSparseLabel (read cursor))
    (leftReference rightReference : RS)
    (leftFuel rightFuel : Nat)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (leftComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b leftReference) read leftFuel leftCursor = some left)
    (rightComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b rightReference) read rightFuel rightCursor = some right)
    (descriptorEqual : left.descriptor = right.descriptor) :
    right.labels = if leftReference = rightReference then left.labels
      else reflectUppercaseRankedLabels left.labels :=
  localizedLabelLayers_eq_or_reflect_of_descriptor_eq input leftReference rightReference
    left right
    (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_descriptor_eq_labels
      (.rule4b leftReference) read leftFuel leftCursor left leftComputed)
    (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_descriptor_eq_labels
      (.rule4b rightReference) read rightFuel rightCursor right rightComputed)
    (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_sparse
      (.rule4b leftReference) read readerSparse leftFuel leftCursor left leftComputed)
    descriptorEqual

/-! ## Actual stage constitutional alignment -/

/-- Equality of the comparison-visible observables restricts to the constitutional projection. -/
theorem constitutionalObservable_eq_of_observable_eq
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (equal : input.localizedRerootCumulativeRule45Observable left =
      input.localizedRerootCumulativeRule45Observable right) :
    constitutionalObservable left.constitutional =
      constitutionalObservable right.constitutional := by
  have rule1aEqual : left.constitutional.rule1a = right.constitutional.rule1a :=
    congrArg LocalizedCumulativeRule45Observable.rule1a equal
  have rule1bEqual : left.constitutional.rule1b = right.constitutional.rule1b :=
    congrArg LocalizedCumulativeRule45Observable.rule1b equal
  have rule2Equal : left.constitutional.rule2 = right.constitutional.rule2 :=
    congrArg LocalizedCumulativeRule45Observable.rule2 equal
  simp only [constitutionalObservable, rule1aEqual, rule1bEqual, rule2Equal]

/-- Equality of the constitutional projection and of the sparse descriptor gives equality of the
full comparison-visible observables. -/
theorem observable_eq_of_constitutional_descriptor
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (constitutional :
      constitutionalObservable left.constitutional =
        constitutionalObservable right.constitutional)
    (descriptor : left.descriptor = right.descriptor) :
    input.localizedRerootCumulativeRule45Observable left =
      input.localizedRerootCumulativeRule45Observable right := by
  have rule1aEqual : left.constitutional.rule1a = right.constitutional.rule1a :=
    congrArg LocalizedConstitutionalObservable.rule1a constitutional
  have rule1bEqual : left.constitutional.rule1b = right.constitutional.rule1b :=
    congrArg LocalizedConstitutionalObservable.rule1b constitutional
  have rule2Equal : left.constitutional.rule2 = right.constitutional.rule2 :=
    congrArg LocalizedConstitutionalObservable.rule2 constitutional
  simp only [localizedRerootCumulativeRule45Observable, rule1aEqual, rule1bEqual, rule2Equal,
    descriptor]

/-- **Actual stage constitutional alignment.**  Two actual Rule-4b keys, built on the same
respective cursors and with the same reader as actual Rule-4a keys (the recursion budgets may
differ), have equal comparison-visible observables as soon as the Rule-4a keys tie and the Rule-4b
sparse descriptors tie.  The constitutional datum is transferred through the actual declarative
derivations (`buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative` and
`declarative_constitutional_observable_unique`); the descriptor datum is transferred through the
actual sparse-layer comparator (`compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff`).
No second comparator, alternate sort or selector is introduced. -/
theorem localizedRerootCumulativeRule45Observable_eq_of_actual_stage_alignment
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (rule4aLeftFuel rule4aRightFuel rule4bLeftFuel rule4bRightFuel : Nat)
    (leftReference rightReference : RS)
    (aL aR bL bR : input.LocalizedRerootCumulativeRule45Key)
    (aLComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a read rule4aLeftFuel leftCursor = some aL)
    (aRComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a read rule4aRightFuel rightCursor = some aR)
    (bLComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b leftReference) read rule4bLeftFuel leftCursor = some bL)
    (bRComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b rightReference) read rule4bRightFuel rightCursor = some bR)
    (rule4aTie : input.compareLocalizedRerootCumulativeRule45Keys aL aR = Ordering.eq)
    (descriptorTie : OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority bL.descriptor bR.descriptor = Ordering.eq) :
    input.localizedRerootCumulativeRule45Observable bL =
      input.localizedRerootCumulativeRule45Observable bR := by
  have rule4aObservable :=
    (input.compareLocalizedRerootCumulativeRule45Keys_eq_iff_observable_eq aL aR).mp rule4aTie
  have rule4aConstitutional :=
    constitutionalObservable_eq_of_observable_eq input aL aR rule4aObservable
  have leftConstitutional :=
    declarative_constitutional_observable_unique input rule4aLeftFuel rule4bLeftFuel
      leftCursor aL.constitutional bL.constitutional
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
        .rule4a read rule4aLeftFuel leftCursor aL aLComputed)
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
        (.rule4b leftReference) read rule4bLeftFuel leftCursor bL bLComputed)
  have rightConstitutional :=
    declarative_constitutional_observable_unique input rule4aRightFuel rule4bRightFuel
      rightCursor aR.constitutional bR.constitutional
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
        .rule4a read rule4aRightFuel rightCursor aR aRComputed)
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
        (.rule4b rightReference) read rule4bRightFuel rightCursor bR bRComputed)
  have constitutional : constitutionalObservable bL.constitutional =
      constitutionalObservable bR.constitutional :=
    leftConstitutional.symm.trans (rule4aConstitutional.trans rightConstitutional)
  have descriptor : bL.descriptor = bR.descriptor :=
    (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff
      bL.descriptor bR.descriptor).mp descriptorTie
  exact observable_eq_of_constitutional_descriptor input bL bR constitutional descriptor

/-- **One stage-4b sorted-slot correspondence preserves both alignments.**  Under the hypotheses of
`localizedRerootCumulativeRule45Observable_eq_of_actual_stage_alignment` and a `none`/uppercase
reader discipline, the two actual Rule-4b keys have equal comparison-visible observables *and*
their exact-label tables are related by the scalar rule: the right table is the left one when the
two references coincide and its uppercase reflection when they differ.  The decoded labels keep
every sphere and every sorted sibling-slot address, so a single stage-4b sorted-address
isomorphism witnesses both the constitutional alignment and the relative-label relation. -/
theorem actual_stage_alignment_capstone
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (readerSparse : ∀ cursor, LocalizedRule4bSparseLabel (read cursor))
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (rule4aLeftFuel rule4aRightFuel rule4bLeftFuel rule4bRightFuel : Nat)
    (leftReference rightReference : RS)
    (aL aR bL bR : input.LocalizedRerootCumulativeRule45Key)
    (aLComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a read rule4aLeftFuel leftCursor = some aL)
    (aRComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a read rule4aRightFuel rightCursor = some aR)
    (bLComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b leftReference) read rule4bLeftFuel leftCursor = some bL)
    (bRComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b rightReference) read rule4bRightFuel rightCursor = some bR)
    (rule4aTie : input.compareLocalizedRerootCumulativeRule45Keys aL aR = Ordering.eq)
    (descriptorTie : OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority bL.descriptor bR.descriptor = Ordering.eq) :
    (input.localizedRerootCumulativeRule45Observable bL =
        input.localizedRerootCumulativeRule45Observable bR) ∧
      bR.labels = if leftReference = rightReference then bL.labels
        else reflectUppercaseRankedLabels bL.labels := by
  have descriptor : bL.descriptor = bR.descriptor :=
    (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff
      bL.descriptor bR.descriptor).mp descriptorTie
  refine ⟨?_, ?_⟩
  · exact localizedRerootCumulativeRule45Observable_eq_of_actual_stage_alignment
      input read leftCursor rightCursor rule4aLeftFuel rule4aRightFuel
      rule4bLeftFuel rule4bRightFuel leftReference rightReference
      aL aR bL bR aLComputed aRComputed bLComputed bRComputed rule4aTie descriptorTie
  · exact buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_eq_or_reflect
      input read readerSparse leftReference rightReference
      rule4bLeftFuel rule4bRightFuel leftCursor rightCursor bL bR
      bLComputed bRComputed descriptor

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule4bSparseLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4bSparseLabel_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4bSparseLabel_chiral
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.not_localizedRule4bSparseLabel_pseudoasymmetric
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4bSparseLabel_reflectUppercase
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel_involutive
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCumulativeRule45Priority_rule4b_eq_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4aPriority_eq_of_cumulativeRule4b_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4bSparseLabel_of_priority_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCumulativeRule45Priority_rule4b_eq_imp
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedLabelLayersSparse
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_descriptor_eq_labels_projection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_descriptor_eq_labels
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_sparse
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedLabelLayers_eq_or_reflect_of_priority_map_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedLabelLayers_eq_or_reflect_of_descriptor_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_eq_or_reflect
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.constitutionalObservable_eq_of_observable_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.observable_eq_of_constitutional_descriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCumulativeRule45Observable_eq_of_actual_stage_alignment
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actual_stage_alignment_capstone

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
