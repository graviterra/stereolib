import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.OneCenter.LocalizedRerootCompoundRule4bcKey
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput









































/-! ## Chiral observations in one sparse sphere -/

/-- Uppercase auxiliary chiral descriptors occurring in one sparse observation sphere, in list
order and with positional addresses forgotten.  Multiplicity is preserved: this is exactly the
observation multiset consumed by the Rule-4b reference selection. -/
def localizedRule4bChiralObservationsInLayer
    (layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) : List RS :=
  layer.filterMap fun entry =>
    match entry.2 with
    | some (.chiral descriptor) => some descriptor
    | none | some (.pseudoasymmetric _) => none

/-- Label-only form of the chiral observation extraction, used to transport observations across
address-preserving maps. -/
private def localizedRule4bChiralObservationsOfLabels :
    List (Option LocalizedAuxiliaryLabel) → List RS
  | [] => []
  | none :: rest => localizedRule4bChiralObservationsOfLabels rest
  | some (.pseudoasymmetric _) :: rest =>
      localizedRule4bChiralObservationsOfLabels rest
  | some (.chiral descriptor) :: rest =>
      descriptor :: localizedRule4bChiralObservationsOfLabels rest

private theorem localizedRule4bChiralObservationsInLayer_eq_of_labels
    (layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :
    localizedRule4bChiralObservationsInLayer layer =
      localizedRule4bChiralObservationsOfLabels (layer.map Prod.snd) := by
  induction layer with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      rcases head with ⟨address, label⟩
      cases label with
      | none =>
          simpa [localizedRule4bChiralObservationsInLayer,
            localizedRule4bChiralObservationsOfLabels] using inductionHypothesis
      | some label =>
          cases label with
          | pseudoasymmetric descriptor =>
              simpa [localizedRule4bChiralObservationsInLayer,
                localizedRule4bChiralObservationsOfLabels] using inductionHypothesis
          | chiral descriptor =>
              show descriptor :: localizedRule4bChiralObservationsInLayer rest =
                descriptor :: localizedRule4bChiralObservationsOfLabels (rest.map Prod.snd)
              rw [inductionHypothesis]

/-- Forgetting addresses preserves the extracted upper-case chiral observation list.  This is the
transport used to read a `labels`-sphere observation from the corresponding `rankedLabels`-sphere,
or conversely. -/
theorem localizedRule4bChiralObservationsInLayer_eq_of_forgetAddresses
    {first second : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))}
    (forgotten : first.map Prod.snd = second.map Prod.snd) :
    localizedRule4bChiralObservationsInLayer first =
      localizedRule4bChiralObservationsInLayer second := by
  rw [localizedRule4bChiralObservationsInLayer_eq_of_labels first,
    localizedRule4bChiralObservationsInLayer_eq_of_labels second, forgotten]

/-! ## Generic list, prefix and rank facts -/

/-- Prefixing a sparse sphere never changes its label sequence. -/
private theorem prefixLayer_map_snd {α : Type*} (slot : Nat)
    (layer : List (OfficialSparseEntry α)) :
    (OfficialRuleMajorKey.prefixLayer slot layer).map Prod.snd = layer.map Prod.snd := by
  unfold OfficialRuleMajorKey.prefixLayer
  rw [List.map_map]
  exact List.map_congr_left fun _ _ => rfl

/-- Two `flatMap`s over sibling-address lists with equal first projections agree, provided the
batches agree on every first component.  The address (second) components may differ: the exact
merge uses unique `zipIdx` slots while the hierarchy-ranked merge uses rank prefixes, which may be
shared.  This is why the address-forgetting equality is not a statement about addresses. -/
private theorem flatMap_fst_congr_two {α β : Type*}
    (leftBatch rightBatch : α → List β)
    (left right : List (α × Nat))
    (fstEq : left.map Prod.fst = right.map Prod.fst)
    (agrees : ∀ value ∈ left.map Prod.fst, leftBatch value = rightBatch value) :
    left.flatMap (fun entry => leftBatch entry.1) =
      right.flatMap (fun entry => rightBatch entry.1) := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail => simp at fstEq
  | cons head tail inductionHypothesis =>
      cases right with
      | nil => simp at fstEq
      | cons rightHead rightTail =>
          simp only [List.map_cons, List.cons.injEq] at fstEq
          obtain ⟨headEq, tailEq⟩ := fstEq
          have headValueEq : head.1 = rightHead.1 := by simpa using headEq
          have agreesTail : ∀ value ∈ tail.map Prod.fst,
              leftBatch value = rightBatch value := by
            intro value present
            exact agrees value (List.mem_cons_of_mem head.1 present)
          simp only [List.flatMap_cons]
          rw [← headValueEq, agrees head.1 (by simp)]
          rw [inductionHypothesis rightTail tailEq agreesTail]

/-- Definitional unfolding of the rank assignment at a nonempty sibling list. -/
private theorem localizedRerootRankedChildTail_cons_def
    (input : CertifiedLocalizedCIPInput)
    (previous child : input.LocalizedRerootCumulativeRule45Key)
    (rank : Nat)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.localizedRerootRankedChildTail previous rank (child :: children) =
      (child,
          (if input.compareLocalizedRerootCumulativeRule45Keys child previous =
              Ordering.eq then rank else rank + 1)) ::
        input.localizedRerootRankedChildTail child
          (if input.compareLocalizedRerootCumulativeRule45Keys child previous =
              Ordering.eq then rank else rank + 1) children :=
  rfl

/-- Definitional unfolding of the rank assignment at a nonempty sibling list. -/
private theorem localizedRerootRankedChildren_cons_def
    (input : CertifiedLocalizedCIPInput)
    (child : input.LocalizedRerootCumulativeRule45Key)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.localizedRerootRankedChildren (child :: children) =
      (child, 0) :: input.localizedRerootRankedChildTail child 0 children :=
  rfl

/-- The hierarchy-rank assignment keeps the underlying sibling list. -/
private theorem localizedRerootRankedChildTail_fst
    (input : CertifiedLocalizedCIPInput) :
    ∀ (previous : input.LocalizedRerootCumulativeRule45Key) (rank : Nat)
      (children : List input.LocalizedRerootCumulativeRule45Key),
      (input.localizedRerootRankedChildTail previous rank children).map Prod.fst = children
  | previous, rank, [] => rfl
  | previous, rank, child :: children => by
      rw [localizedRerootRankedChildTail_cons_def input previous child rank children]
      simp only [List.map_cons]
      rw [localizedRerootRankedChildTail_fst input child
        (if input.compareLocalizedRerootCumulativeRule45Keys child previous = Ordering.eq
          then rank else rank + 1) children]

/-- The hierarchy-rank assignment keeps the underlying sibling list. -/
private theorem localizedRerootRankedChildren_fst
    (input : CertifiedLocalizedCIPInput) :
    ∀ children : List input.LocalizedRerootCumulativeRule45Key,
      (input.localizedRerootRankedChildren children).map Prod.fst = children
  | [] => rfl
  | child :: children => by
      rw [localizedRerootRankedChildren_cons_def input child children]
      simp only [List.map_cons]
      rw [localizedRerootRankedChildTail_fst input child 0 children]

/-- A folded maximum is unchanged by pointwise-equal measures. -/
private theorem foldl_max_eq_of_pointwise {β : Type*}
    (first second : β → Nat) :
    ∀ (values : List β), (∀ value ∈ values, first value = second value) →
      ∀ accumulator,
        values.foldl (fun longest value => max longest (first value)) accumulator =
          values.foldl (fun longest value => max longest (second value)) accumulator
  | [], _, accumulator => rfl
  | head :: tail, agrees, accumulator => by
      simp only [List.foldl_cons]
      rw [agrees head (by simp)]
      exact foldl_max_eq_of_pointwise first second tail
        (fun value present => agrees value (List.mem_cons_of_mem head present))
        (max accumulator (second head))

/-- Layerwise equality of address-forgotten stacks determines every `getD` sphere. -/
private theorem getD_map_eq_of_map_eq {α β : Type*} (forget : α → β) :
    ∀ (first second : List (List α)),
      first.map (List.map forget) = second.map (List.map forget) →
      ∀ depth, (first.getD depth []).map forget = (second.getD depth []).map forget
  | [], [], _ => by
      intro depth
      rfl
  | [], _ :: _, impossible => by
      simp at impossible
  | _ :: _, [], impossible => by
      simp at impossible
  | head :: tail, other :: others, stacked => by
      simp only [List.map_cons, List.cons.injEq] at stacked
      obtain ⟨headEq, tailEq⟩ := stacked
      intro depth
      cases depth with
      | zero => simpa using headEq
      | succ depth => simpa using getD_map_eq_of_map_eq forget tail others tailEq depth

/-! ## The actual label merge preserves every observation and its depth -/

/-- The actual exact-label merge and the actual hierarchy-ranked merge produce the same
address-forgotten label stack, provided the children already agree sphere by sphere and have the
same depth.  Prefix choice is irrelevant because `prefixLayer` only rewrites addresses. -/
private theorem mergeLocalizedRerootLabelChildren_forgetAddresses_eq
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (lengths : ∀ child ∈ children,
      child.labels.length = child.rankedLabels.length)
    (observations : ∀ child ∈ children, ∀ depth,
      (child.labels.getD depth []).map Prod.snd =
        (child.rankedLabels.getD depth []).map Prod.snd) :
    (input.mergeLocalizedRerootLabelChildren children).map (List.map Prod.snd) =
      (input.mergeLocalizedRerootRankedLabelChildren children).map
        (List.map Prod.snd) := by
  have countEq :
      input.localizedRerootLabelChildLayerCount children =
        input.localizedRerootRankedLabelChildLayerCount children := by
    unfold localizedRerootLabelChildLayerCount localizedRerootRankedLabelChildLayerCount
    exact foldl_max_eq_of_pointwise (fun child => child.labels.length)
      (fun child => child.rankedLabels.length) children lengths 0
  unfold mergeLocalizedRerootLabelChildren mergeLocalizedRerootRankedLabelChildren
  dsimp only
  rw [countEq]
  simp only [List.map_map]
  apply List.map_congr_left
  intro depth _
  simp only [Function.comp_apply]
  rw [List.map_flatMap, List.map_flatMap]
  simp only [prefixLayer_map_snd]
  refine flatMap_fst_congr_two
    (fun child => (child.labels.getD depth []).map Prod.snd)
    (fun child => (child.rankedLabels.getD depth []).map Prod.snd)
    children.zipIdx (input.localizedRerootRankedChildren children) ?_ ?_
  · rw [List.zipIdx_map_fst, localizedRerootRankedChildren_fst input]
  · intro child present
    exact observations child (by simpa using present) depth

/-! ## The actual builder invariant -/

/-- Every successful `List.mapM` result element comes from some source element. -/
private theorem mapM_buildWithRead?_member
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys : List input.LocalizedRerootCumulativeRule45Key),
      cursors.mapM (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        stage read fuel) = some keys →
      ∀ key, key ∈ keys →
        ∃ cursor, cursor ∈ cursors ∧
          input.buildLocalizedRerootCumulativeRule45KeyWithRead?
            stage read fuel cursor = some key
  | [], keys, computed, key, present => by
      simp at computed
      subst keys
      simp at present
  | cursor :: cursors, keys, computed, key, present => by
      rw [List.mapM_cons] at computed
      cases headComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          stage read fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                stage read fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              rcases List.mem_cons.mp present with same | tailPresent
              · subst key
                exact ⟨cursor, by simp, headComputed⟩
              · obtain ⟨source, sourcePresent, sourceComputed⟩ :=
                  mapM_buildWithRead?_member input stage read cursors tail
                    tailComputed key tailPresent
                exact ⟨source, List.mem_cons_of_mem cursor sourcePresent, sourceComputed⟩

/-- Every successful actual parametric cumulative compilation has `labels` and `rankedLabels`
stacks of equal depth, with identical address-forgotten label sequences in every sphere. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_rankedLabels_forgetAddresses
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel cursor = some key →
      key.labels.length = key.rankedLabels.length ∧
        key.labels.map (List.map Prod.snd) =
          key.rankedLabels.map (List.map Prod.snd)
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            exact ⟨rfl, rfl⟩
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            exact ⟨rfl, rfl⟩
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                  stage read fuel) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
                subst key
                dsimp only
                have childInvariant : ∀ child ∈ childKeys,
                    child.labels.length = child.rankedLabels.length ∧
                      child.labels.map (List.map Prod.snd) =
                        child.rankedLabels.map (List.map Prod.snd) := by
                  intro child present
                  obtain ⟨source, _sourcePresent, sourceComputed⟩ :=
                    mapM_buildWithRead?_member input stage read children childKeys
                      childKeysComputed child present
                  exact
                    buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_rankedLabels_forgetAddresses
                      input stage read fuel source child sourceComputed
                have sortedInvariant :
                    ∀ child ∈ input.sortLocalizedRerootCumulativeRule45Keys childKeys,
                      child.labels.length = child.rankedLabels.length ∧
                        child.labels.map (List.map Prod.snd) =
                          child.rankedLabels.map (List.map Prod.snd) := by
                  intro child present
                  exact childInvariant child
                    ((input.sortLocalizedRerootCumulativeRule45Keys_perm
                      childKeys).mem_iff.mp present)
                have lengthAgreement :
                    ∀ child ∈ input.sortLocalizedRerootCumulativeRule45Keys childKeys,
                      child.labels.length = child.rankedLabels.length :=
                  fun child present => (sortedInvariant child present).1
                have observationAgreement :
                    ∀ child ∈ input.sortLocalizedRerootCumulativeRule45Keys childKeys,
                      ∀ depth,
                        (child.labels.getD depth []).map Prod.snd =
                          (child.rankedLabels.getD depth []).map Prod.snd :=
                  fun child present depth =>
                    getD_map_eq_of_map_eq Prod.snd child.labels child.rankedLabels
                      (sortedInvariant child present).2 depth
                have merged :=
                  mergeLocalizedRerootLabelChildren_forgetAddresses_eq input
                    (input.sortLocalizedRerootCumulativeRule45Keys childKeys)
                    lengthAgreement observationAgreement
                constructor
                · unfold mergeLocalizedRerootLabelChildren
                    mergeLocalizedRerootRankedLabelChildren
                  dsimp only
                  simp only [List.length_cons, List.length_map, List.length_range]
                  have countEq :
                      input.localizedRerootLabelChildLayerCount
                          (input.sortLocalizedRerootCumulativeRule45Keys childKeys) =
                        input.localizedRerootRankedLabelChildLayerCount
                          (input.sortLocalizedRerootCumulativeRule45Keys childKeys) := by
                    unfold localizedRerootLabelChildLayerCount
                      localizedRerootRankedLabelChildLayerCount
                    exact foldl_max_eq_of_pointwise (fun child => child.labels.length)
                      (fun child => child.rankedLabels.length)
                      (input.sortLocalizedRerootCumulativeRule45Keys childKeys)
                      lengthAgreement 0
                  rw [countEq]
                · simp only [List.map_cons, List.map_nil]
                  rw [merged]

/-- The production cumulative builder (`localizedDependencyLabel` reader) inherits the same
invariant, in particular for the actual `.rule4a` key used by the compound builder. -/
theorem buildLocalizedRerootCumulativeRule45Key?_labels_rankedLabels_forgetAddresses
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel cursor = some key →
      key.labels.length = key.rankedLabels.length ∧
        key.labels.map (List.map Prod.snd) =
          key.rankedLabels.map (List.map Prod.snd) := by
  intro fuel cursor key computed
  rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
    stage target view fuel cursor] at computed
  exact
    buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_rankedLabels_forgetAddresses
      input stage (fun cursor => input.localizedDependencyLabel target view cursor)
      fuel cursor key computed

/-- Per-sphere form of the actual-builder invariant: every sphere has the same label sequence
with addresses forgotten, therefore the same label multiset. -/
theorem buildLocalizedRerootCumulativeRule45Key?_labels_rankedLabels_sameLabelsAtDepth
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel cursor = some key)
    (depth : Nat) :
    (key.labels.getD depth []).map Prod.snd =
      (key.rankedLabels.getD depth []).map Prod.snd :=
  getD_map_eq_of_map_eq Prod.snd key.labels key.rankedLabels
    (buildLocalizedRerootCumulativeRule45Key?_labels_rankedLabels_forgetAddresses
      input stage target view fuel cursor key computed).2 depth

/-- Multiset form of the per-sphere invariant. -/
theorem buildLocalizedRerootCumulativeRule45Key?_labels_rankedLabels_labelMultisetAtDepth
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel cursor = some key)
    (depth : Nat) :
    ((key.labels.getD depth []).map Prod.snd).Perm
      ((key.rankedLabels.getD depth []).map Prod.snd) := by
  rw [buildLocalizedRerootCumulativeRule45Key?_labels_rankedLabels_sameLabelsAtDepth
    input stage target view fuel cursor key computed depth]

/-! ## A unique first chiral observation selects itself -/

/-- If a sphere contains no chiral observation, its first-ranked population is absent. -/
theorem localizedFirstChiralRankPopulationInLayer_eq_none_of_chiralObservations_nil
    (layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))
    (empty : localizedRule4bChiralObservationsInLayer layer = []) :
    localizedFirstChiralRankPopulationInLayer layer = none := by
  induction layer with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      rcases head with ⟨rank, label⟩
      cases label with
      | none =>
          have emptyTail : localizedRule4bChiralObservationsInLayer rest = [] := by
            simpa [localizedRule4bChiralObservationsInLayer] using empty
          have tailNone := inductionHypothesis emptyTail
          show localizedFirstChiralRankPopulationInLayer rest = none
          exact tailNone
      | some label =>
          cases label with
          | pseudoasymmetric descriptor =>
              have emptyTail : localizedRule4bChiralObservationsInLayer rest = [] := by
                simpa [localizedRule4bChiralObservationsInLayer] using empty
              have tailNone := inductionHypothesis emptyTail
              show localizedFirstChiralRankPopulationInLayer rest = none
              exact tailNone
          | chiral descriptor =>
              simp [localizedRule4bChiralObservationsInLayer] at empty

/-- A sphere with no chiral observation contributes no fixed-rank population either. -/
private theorem localizedChiralDescriptorsAtRank_eq_nil_of_chiralObservations_nil
    (rank : List Nat) :
    ∀ observations,
      localizedRule4bChiralObservationsInLayer observations = [] →
      localizedChiralDescriptorsAtRank rank observations = []
  | [] => by
      intro _
      rfl
  | (observedRank, label) :: observations => by
      intro empty
      cases label with
      | none =>
          have emptyTail : localizedRule4bChiralObservationsInLayer observations = [] := by
            simpa [localizedRule4bChiralObservationsInLayer] using empty
          have tailNil :=
            localizedChiralDescriptorsAtRank_eq_nil_of_chiralObservations_nil
              rank observations emptyTail
          simp only [localizedChiralDescriptorsAtRank, tailNil]
          split <;> rfl
      | some label =>
          cases label with
          | pseudoasymmetric descriptor =>
              have emptyTail : localizedRule4bChiralObservationsInLayer observations = [] := by
                simpa [localizedRule4bChiralObservationsInLayer] using empty
              have tailNil :=
                localizedChiralDescriptorsAtRank_eq_nil_of_chiralObservations_nil
                  rank observations emptyTail
              simp only [localizedChiralDescriptorsAtRank, tailNil]
              split <;> rfl
          | chiral descriptor =>
              simp [localizedRule4bChiralObservationsInLayer] at empty

/-- A sphere with exactly one chiral observation `descriptor` has first-ranked population the
singleton `[descriptor]`. -/
theorem localizedFirstChiralRankPopulationInLayer_eq_some_singleton_of_chiralObservations_singleton
    (layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))
    (descriptor : RS)
    (unique : localizedRule4bChiralObservationsInLayer layer = [descriptor]) :
    localizedFirstChiralRankPopulationInLayer layer = some [descriptor] := by
  induction layer with
  | nil => simp [localizedRule4bChiralObservationsInLayer] at unique
  | cons head rest inductionHypothesis =>
      rcases head with ⟨rank, label⟩
      cases label with
      | none =>
          have uniqueTail : localizedRule4bChiralObservationsInLayer rest = [descriptor] := by
            simpa [localizedRule4bChiralObservationsInLayer] using unique
          have tailSome := inductionHypothesis uniqueTail
          show localizedFirstChiralRankPopulationInLayer rest = some [descriptor]
          exact tailSome
      | some label =>
          cases label with
          | pseudoasymmetric observed =>
              have uniqueTail : localizedRule4bChiralObservationsInLayer rest = [descriptor] := by
                simpa [localizedRule4bChiralObservationsInLayer] using unique
              have tailSome := inductionHypothesis uniqueTail
              show localizedFirstChiralRankPopulationInLayer rest = some [descriptor]
              exact tailSome
          | chiral observed =>
              have singletonHead :
                  observed :: localizedRule4bChiralObservationsInLayer rest =
                    descriptor :: [] := by
                simpa [localizedRule4bChiralObservationsInLayer] using unique
              simp only [List.cons.injEq] at singletonHead
              obtain ⟨observedEq, restEmpty⟩ := singletonHead
              subst observed
              have restDescriptors : localizedChiralDescriptorsAtRank rank rest = [] :=
                localizedChiralDescriptorsAtRank_eq_nil_of_chiralObservations_nil
                  rank rest restEmpty
              simp [localizedFirstChiralRankPopulationInLayer, restDescriptors]

/-- Scanning from the bottom, if every sphere before `depth` is chiral-free and sphere `depth`
has exactly one chiral observation `descriptor`, the actual first-ranked population is
`[descriptor]`. -/
theorem localizedFirstChiralRankPopulation_eq_singleton_of_first_uniqueChiral
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (depth : Nat) (descriptor : RS)
    (before : ∀ earlier < depth,
      localizedRule4bChiralObservationsInLayer (layers.getD earlier []) = [])
    (atDepth : localizedRule4bChiralObservationsInLayer (layers.getD depth []) =
      [descriptor]) :
    localizedFirstChiralRankPopulation layers = [descriptor] := by
  induction layers generalizing depth with
  | nil =>
      simp [localizedRule4bChiralObservationsInLayer] at atDepth
  | cons layer rest inductionHypothesis =>
      cases depth with
      | zero =>
          have atLayer : localizedRule4bChiralObservationsInLayer layer = [descriptor] := by
            simpa using atDepth
          have population :=
            localizedFirstChiralRankPopulationInLayer_eq_some_singleton_of_chiralObservations_singleton
              layer descriptor atLayer
          simp [localizedFirstChiralRankPopulation, population]
      | succ depth =>
          have layerEmpty : localizedRule4bChiralObservationsInLayer layer = [] := by
            simpa using before 0 (Nat.zero_lt_succ depth)
          have populationEmpty :=
            localizedFirstChiralRankPopulationInLayer_eq_none_of_chiralObservations_nil
              layer layerEmpty
          have beforeRest : ∀ earlier < depth,
              localizedRule4bChiralObservationsInLayer (rest.getD earlier []) = [] := by
            intro earlier bound
            have observed := before (earlier + 1) (Nat.succ_lt_succ bound)
            simpa using observed
          have atRest : localizedRule4bChiralObservationsInLayer (rest.getD depth []) =
              [descriptor] := by
            simpa using atDepth
          have result := inductionHypothesis depth beforeRest atRest
          simp [localizedFirstChiralRankPopulation, populationEmpty, result]

/-- The executable majority/tie selector on a singleton population returns exactly that
descriptor. -/
theorem localizedRule4bReferencesFromPopulation_singleton (descriptor : RS) :
    localizedRule4bReferencesFromPopulation [descriptor] = [descriptor] := by
  cases descriptor <;> decide

/-- If the first populated sphere contains exactly one chiral observation `descriptor`, the actual
executable Rule-4b selector returns `[descriptor]`.  No alternative selector and no assumed
multiplicity are used. -/
theorem localizedRule4bReferencesFromRankedLabels_eq_singleton_of_first_uniqueChiral
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (depth : Nat) (descriptor : RS)
    (before : ∀ earlier < depth,
      localizedRule4bChiralObservationsInLayer (layers.getD earlier []) = [])
    (atDepth : localizedRule4bChiralObservationsInLayer (layers.getD depth []) =
      [descriptor]) :
    localizedRule4bReferencesFromRankedLabels layers = [descriptor] := by
  unfold localizedRule4bReferencesFromRankedLabels
  rw [localizedFirstChiralRankPopulation_eq_singleton_of_first_uniqueChiral
    layers depth descriptor before atDepth,
    localizedRule4bReferencesFromPopulation_singleton]

/-- The actual production cumulative key's selector is determined by the observations recorded in
its sorted-slot `labels` spheres: a first unique chiral observation `descriptor` makes the selector
on `rankedLabels` the singleton `[descriptor]`. -/
theorem buildLocalizedRerootCumulativeRule45Key?_referenceSelection_singleton_of_first_uniqueChiral
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (depth : Nat) (descriptor : RS)
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel cursor = some key)
    (before : ∀ earlier < depth,
      localizedRule4bChiralObservationsInLayer (key.labels.getD earlier []) = [])
    (atDepth : localizedRule4bChiralObservationsInLayer (key.labels.getD depth []) =
      [descriptor]) :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels = [descriptor] := by
  have invariant :=
    buildLocalizedRerootCumulativeRule45Key?_labels_rankedLabels_forgetAddresses
      input stage target view fuel cursor key computed
  have rankedBefore : ∀ earlier < depth,
      localizedRule4bChiralObservationsInLayer (key.rankedLabels.getD earlier []) = [] := by
    intro earlier bound
    rw [← localizedRule4bChiralObservationsInLayer_eq_of_forgetAddresses
      (getD_map_eq_of_map_eq Prod.snd key.labels key.rankedLabels invariant.2 earlier)]
    exact before earlier bound
  have rankedAt : localizedRule4bChiralObservationsInLayer
        (key.rankedLabels.getD depth []) = [descriptor] := by
    rw [← localizedRule4bChiralObservationsInLayer_eq_of_forgetAddresses
      (getD_map_eq_of_map_eq Prod.snd key.labels key.rankedLabels invariant.2 depth)]
    exact atDepth
  exact localizedRule4bReferencesFromRankedLabels_eq_singleton_of_first_uniqueChiral
    key.rankedLabels depth descriptor rankedBefore rankedAt

/-! ## The actual compound builder reading -/

/-- The actual compound builder derives its reference list from exactly the executable selector on
the Rule-4a key's hierarchy-ranked labels. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_references_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key) :
    key.references =
      localizedRule4bReferencesFromRankedLabels key.rule4aKey.rankedLabels := by
  unfold buildLocalizedRerootCompoundRule4bcKey? at computed
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45Key?
      .rule4a target view fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      let references :=
        localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
      let alternatives := localizedRule4bcReferenceAlternatives references
      cases readingsComputed : input.buildLocalizedRerootRule4bcReadings?
          target view fuel cursor alternatives with
      | none =>
          simp [rule4aComputed, references, alternatives, readingsComputed] at computed
      | some readings =>
          simp [rule4aComputed, references, alternatives, readingsComputed] at computed
          subst key
          rfl

/-- The Rule-4a key retained by a successful compound build is exactly the successful actual
Rule-4a compilation on the same cursor. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_rule4aKey
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key) :
    input.buildLocalizedRerootCumulativeRule45Key?
      .rule4a target view fuel cursor = some key.rule4aKey := by
  unfold buildLocalizedRerootCompoundRule4bcKey? at computed
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45Key?
      .rule4a target view fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      let references :=
        localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
      let alternatives := localizedRule4bcReferenceAlternatives references
      cases readingsComputed : input.buildLocalizedRerootRule4bcReadings?
          target view fuel cursor alternatives with
      | none =>
          simp [rule4aComputed, references, alternatives, readingsComputed] at computed
      | some readings =>
          simp [rule4aComputed, references, alternatives, readingsComputed] at computed
          subst key
          rfl

/-- A successful singleton `buildLocalizedRerootRule4bcReadings?` call exposes its one reading and
that reading's successful single-reference compilation. -/
private theorem buildLocalizedRerootRule4bcReadings?_singleton
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS) (readings : List input.LocalizedRerootRule4bcReading)
    (computed : input.buildLocalizedRerootRule4bcReadings?
      target view fuel cursor [reference] = some readings) :
    ∃ single : input.LocalizedRerootRule4bcReading,
      readings = [single] ∧
        input.buildLocalizedRerootRule4bcReading?
          target view fuel cursor reference = some single := by
  unfold buildLocalizedRerootRule4bcReadings? at computed
  cases headComputed : input.buildLocalizedRerootRule4bcReading?
      target view fuel cursor reference with
  | none => simp [headComputed] at computed
  | some reading =>
      have computed' :
          some (reading :: ([] : List input.LocalizedRerootRule4bcReading)) =
            some readings := by
        simpa only [buildLocalizedRerootRule4bcReadings?, headComputed,
          Option.bind_some] using computed
      have readingsEq : readings = [reading] := by
        simpa only [Option.some.injEq] using computed'.symm
      rw [readingsEq]
      exact ⟨reading, rfl, rfl⟩

/-- A successful single-reference reading carries exactly the requested reference. -/
private theorem buildLocalizedRerootRule4bcReading?_reference?_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS) (reading : input.LocalizedRerootRule4bcReading)
    (computed : input.buildLocalizedRerootRule4bcReading?
      target view fuel cursor reference = some reading) :
    reading.reference? = reference := by
  cases reference with
  | none =>
      unfold buildLocalizedRerootRule4bcReading? at computed
      cases rule4bComputed : input.buildLocalizedRerootCumulativeRule45Key?
          .rule4a target view fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          cases rule4cComputed : input.buildLocalizedRerootCumulativeRule45Key?
              .rule4cNoReference target view fuel cursor with
          | none => simp [rule4bComputed, rule4cComputed] at computed
          | some rule4cKey =>
              simp [rule4bComputed, rule4cComputed] at computed
              subst reading
              rfl
  | some reference =>
      unfold buildLocalizedRerootRule4bcReading? at computed
      cases rule4bComputed : input.buildLocalizedRerootCumulativeRule45Key?
          (.rule4b reference) target view fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          cases rule4cComputed : input.buildLocalizedRerootCumulativeRule45Key?
              (.rule4c reference) target view fuel cursor with
          | none => simp [rule4bComputed, rule4cComputed] at computed
          | some rule4cKey =>
              simp [rule4bComputed, rule4cComputed] at computed
              subst reading
              rfl

/-- A singleton reference list produces a singleton actual compound reading list, whose
`reference?` is exactly that reference. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_references_singleton
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey) (descriptor : RS)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key)
    (references : key.references = [descriptor]) :
    ∃ reading : input.LocalizedRerootRule4bcReading,
      key.readings = [reading] ∧ reading.reference? = some descriptor := by
  unfold buildLocalizedRerootCompoundRule4bcKey? at computed
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45Key?
      .rule4a target view fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      let references' :=
        localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
      let alternatives := localizedRule4bcReferenceAlternatives references'
      cases readingsComputed : input.buildLocalizedRerootRule4bcReadings?
          target view fuel cursor alternatives with
      | none =>
          simp [rule4aComputed, references', alternatives, readingsComputed] at computed
      | some readings =>
          simp [rule4aComputed, references', alternatives, readingsComputed] at computed
          subst key
          have referencesEq : references' = [descriptor] := references
          have alternativesEq : alternatives = [some descriptor] := by
            simp [alternatives, referencesEq, localizedRule4bcReferenceAlternatives]
          rw [alternativesEq] at readingsComputed
          obtain ⟨reading, readingsEq, readingComputed⟩ :=
            buildLocalizedRerootRule4bcReadings?_singleton input target view fuel cursor
              (some descriptor) readings readingsComputed
          exact ⟨reading, readingsEq,
            buildLocalizedRerootRule4bcReading?_reference?_eq input target view fuel cursor
              (some descriptor) reading readingComputed⟩

/-- If the executable selector on the actual Rule-4a key's ranked labels is a singleton, the
actual compound builder has a singleton reading with that reference. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_referenceSelection_singleton
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey) (descriptor : RS)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key)
    (selection : localizedRule4bReferencesFromRankedLabels key.rule4aKey.rankedLabels =
      [descriptor]) :
    ∃ reading : input.LocalizedRerootRule4bcReading,
      key.readings = [reading] ∧ reading.reference? = some descriptor := by
  have references : key.references = [descriptor] := by
    rw [buildLocalizedRerootCompoundRule4bcKey?_references_eq
      input target view fuel cursor key computed, selection]
  exact buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_references_singleton
    input target view fuel cursor key descriptor computed references

/-- **Actual construction endpoint.**  If the actual `.rule4a` key retained by a successful
compound build has no chiral observation before sphere `depth` and exactly one chiral observation
`descriptor` in sphere `depth`, then the actual compound reading list is a singleton whose
reference is `some descriptor`.

The two observation hypotheses are the precise physical seam: deriving them from a unique nearest
constitutionally rigid center is not part of this module (see the module header). -/
theorem buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_first_uniqueChiral
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (depth : Nat) (descriptor : RS)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key)
    (before : ∀ earlier < depth,
      localizedRule4bChiralObservationsInLayer
        (key.rule4aKey.labels.getD earlier []) = [])
    (atDepth : localizedRule4bChiralObservationsInLayer
      (key.rule4aKey.labels.getD depth []) = [descriptor]) :
    ∃ reading : input.LocalizedRerootRule4bcReading,
      key.readings = [reading] ∧ reading.reference? = some descriptor := by
  have rule4aComputed :=
    buildLocalizedRerootCompoundRule4bcKey?_rule4aKey
      input target view fuel cursor key computed
  have selection :=
    buildLocalizedRerootCumulativeRule45Key?_referenceSelection_singleton_of_first_uniqueChiral
      input .rule4a target view fuel cursor key.rule4aKey depth descriptor
      rule4aComputed before atDepth
  exact
    buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_referenceSelection_singleton
      input target view fuel cursor key descriptor computed selection

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4bChiralObservationsInLayer
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4bChiralObservationsInLayer_eq_of_forgetAddresses
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_labels_rankedLabels_forgetAddresses
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_labels_rankedLabels_forgetAddresses
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_labels_rankedLabels_sameLabelsAtDepth
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_labels_rankedLabels_labelMultisetAtDepth
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedFirstChiralRankPopulationInLayer_eq_none_of_chiralObservations_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedFirstChiralRankPopulationInLayer_eq_some_singleton_of_chiralObservations_singleton
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedFirstChiralRankPopulation_eq_singleton_of_first_uniqueChiral
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4bReferencesFromPopulation_singleton
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule4bReferencesFromRankedLabels_eq_singleton_of_first_uniqueChiral
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_singleton_of_first_uniqueChiral
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKey?_references_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKey?_rule4aKey
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_references_singleton
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_referenceSelection_singleton
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_first_uniqueChiral
