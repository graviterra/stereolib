import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter

/-!
# Uppercase/label reflection naturality of the localized cumulative Rules-4a--5 builder

`LocalizedParametricCumulativeLabels` separates *label reading* from the production cumulative
key construction: `buildLocalizedRerootCumulativeRule45KeyWithRead?` consumes an arbitrary total
`read : cursor → Option LocalizedAuxiliaryLabel` at the same actual reroot cursor and otherwise
performs the production construction (`localizedRerootChildren?`, the cumulative sibling sort, the
descriptor/label/ranked-label merges, `officialRuleMajorRootKey` and
`OfficialRuleMajorKey.assemble`).

This module proves that the *same* actual builder commutes with simultaneous reflection of

* the cumulative stage (every uppercase Rule-4b/Rule-5 reference is swapped), and
* the label reader (only uppercase `.chiral` descriptors are swapped; lowercase
  `.pseudoasymmetric` observations are invariant),

for every fuel and every actual cursor, with `none` preserved.  The equality is a full
`Option.map` equality: a failed compilation stays `none`, and a successful compilation is mapped
through the key reflection that fixes the constitutional and descriptor projections and reflects
`labels` and `rankedLabels`.

The reflection acts on values only.  The cursor, the child frame reader and all structural
decisions operate at the *same actual cursor*; no reflected cursor, molecule or occurrence is
introduced, and none is hypothesized.

## Main results

* `reflectLocalizedCumulativeRule45Stage` and
  `localizedCumulativeRule45Priority_reflectLocalizedCumulativeRule45Stage` — the cumulative
  priority vector is invariant when *both* the stage references and the label observation are
  reflected (all six stage constructors, including `rule4cNoReference` and
  `rule5NoRule4bReference`).
* `LocalizedRerootCumulativeRule45UppercaseReflection` /
  `reflectLocalizedRerootCumulativeRule45Key` — the key reflection relation and its canonical
  function: constitutional and descriptor fields are fixed, `labels` and `rankedLabels` are
  reflected entrywise at unchanged rank addresses.
* `compareLocalizedRerootCumulativeRule45Keys_congr_reflection` — the actual cumulative comparator
  is invariant under the reflection relation.
* `insertLocalizedRerootCumulativeRule45Key_reflect` and
  `sortLocalizedRerootCumulativeRule45Keys_reflect` — the actual insertion sort commutes with key
  reflection.
* `mergeLocalizedRerootDescriptorChildren_reflect`,
  `mergeLocalizedRerootLabelChildren_reflect`,
  `localizedRerootRankedChildren_reflect`,
  `mergeLocalizedRerootRankedLabelChildren_reflect` — the actual child merges commute with key
  reflection (descriptor merge is fixed; label and ranked-label merges are reflected).
* `buildLocalizedRerootCumulativeRule45KeyWithRead?_reflectUppercase` — the headline actual-builder
  naturality statement, by induction on the actual builder fuel.

## Scope

This is a same-cursor value-reflection result.  It does *not* claim that a physical molecular
mirror operation induces the reflected label reading; that reading is supplied as the reflected
callback, and its chemical interpretation is a separate obligation.  It also does not build a
second evaluator: every structural step is the production construction.
-/

namespace CertifiedLocalizedCIPInput

/-! ## Stage reflection and cumulative priority naturality -/

/-- Reflect a cumulative Rule-4a--5 stage together with every uppercase reference, including the
no-Rule-4b-reference Rule-5 stage. -/
def reflectLocalizedCumulativeRule45Stage :
    LocalizedCumulativeRule45Stage → LocalizedCumulativeRule45Stage
  | .rule4a => .rule4a
  | .rule4b reference => .rule4b (RS.swap reference)
  | .rule4cNoReference => .rule4cNoReference
  | .rule4c reference => .rule4c (RS.swap reference)
  | .rule5NoRule4bReference rule5Reference =>
      .rule5NoRule4bReference (RS.swap rule5Reference)
  | .rule5 rule4bReference rule5Reference =>
      .rule5 (RS.swap rule4bReference) (RS.swap rule5Reference)

/-- The Rule-5 senior/junior bit is invariant under simultaneous reflection of its reference and
the observed uppercase label. -/
theorem localizedRule5Priority_reflectUppercase
    (reference : RS) (label : Option LocalizedAuxiliaryLabel) :
    localizedRule5Priority (RS.swap reference) (reflectUppercaseOptionalLabel label) =
      localizedRule5Priority reference label := by
  cases reference <;> cases label with
  | none => rfl
  | some label =>
      cases label with
      | pseudoasymmetric descriptor => rfl
      | chiral descriptor => cases descriptor <;> rfl

/-- The full cumulative priority vector is invariant when both the stage references and the
observed label are reflected.  This covers every stage constructor, including
`rule4cNoReference`, `rule5NoRule4bReference` and the two-reference `rule5`. -/
@[simp] theorem localizedCumulativeRule45Priority_reflectLocalizedCumulativeRule45Stage
    (stage : LocalizedCumulativeRule45Stage)
    (label : Option LocalizedAuxiliaryLabel) :
    localizedCumulativeRule45Priority (reflectLocalizedCumulativeRule45Stage stage)
        (reflectUppercaseOptionalLabel label) =
      localizedCumulativeRule45Priority stage label := by
  cases stage <;>
    simp [reflectLocalizedCumulativeRule45Stage, localizedCumulativeRule45Priority,
      localizedRule5Priority_reflectUppercase]

/-! ## Key reflection -/

/-- Comparator-visible uppercase reflection of cumulative keys: the constitutional and descriptor
projections agree, while the exact and hierarchy-rank-addressed label projections are the
uppercase reflections of the left key's. -/
structure LocalizedRerootCumulativeRule45UppercaseReflection
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key) : Prop where
  constitutional : left.constitutional = right.constitutional
  descriptor : left.descriptor = right.descriptor
  labels : right.labels = reflectUppercaseRankedLabels left.labels
  rankedLabels : right.rankedLabels = reflectUppercaseRankedLabels left.rankedLabels

/-- Canonical reflected cumulative key.  The comparator-visible projections are fixed; the
label projections are reflected at unchanged rank addresses. -/
def reflectLocalizedRerootCumulativeRule45Key
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    input.LocalizedRerootCumulativeRule45Key where
  constitutional := key.constitutional
  descriptor := key.descriptor
  labels := reflectUppercaseRankedLabels key.labels
  rankedLabels := reflectUppercaseRankedLabels key.rankedLabels

/-- The canonical reflected key satisfies the reflection relation. -/
theorem reflectLocalizedRerootCumulativeRule45Key_reflection
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    LocalizedRerootCumulativeRule45UppercaseReflection input key
      (reflectLocalizedRerootCumulativeRule45Key input key) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The actual cumulative comparator is invariant under uppercase reflection. -/
theorem compareLocalizedRerootCumulativeRule45Keys_congr_reflection
    (input : CertifiedLocalizedCIPInput)
    {left left' right right' : input.LocalizedRerootCumulativeRule45Key}
    (leftReflected : LocalizedRerootCumulativeRule45UppercaseReflection input left left')
    (rightReflected : LocalizedRerootCumulativeRule45UppercaseReflection input right right') :
    input.compareLocalizedRerootCumulativeRule45Keys left right =
      input.compareLocalizedRerootCumulativeRule45Keys left' right' := by
  unfold compareLocalizedRerootCumulativeRule45Keys
  simp [compareLex, Ordering.byKey,
    leftReflected.constitutional, leftReflected.descriptor,
    rightReflected.constitutional, rightReflected.descriptor]

/-- Comparator congruence in canonical-function form. -/
theorem compareLocalizedRerootCumulativeRule45Keys_reflect
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key) :
    input.compareLocalizedRerootCumulativeRule45Keys
        (reflectLocalizedRerootCumulativeRule45Key input left)
        (reflectLocalizedRerootCumulativeRule45Key input right) =
      input.compareLocalizedRerootCumulativeRule45Keys left right :=
  (input.compareLocalizedRerootCumulativeRule45Keys_congr_reflection
    (reflectLocalizedRerootCumulativeRule45Key_reflection input left)
    (reflectLocalizedRerootCumulativeRule45Key_reflection input right)).symm

/-! ## Actual insertion sort -/

/-- The actual cumulative insertion commutes with canonical key reflection. -/
theorem insertLocalizedRerootCumulativeRule45Key_reflect
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key,
      input.insertLocalizedRerootCumulativeRule45Key
          (reflectLocalizedRerootCumulativeRule45Key input key)
          (keys.map (reflectLocalizedRerootCumulativeRule45Key input)) =
        (input.insertLocalizedRerootCumulativeRule45Key key keys).map
          (reflectLocalizedRerootCumulativeRule45Key input)
  | [] => rfl
  | head :: tail => by
      simp only [List.map_cons, insertLocalizedRerootCumulativeRule45Key]
      rw [compareLocalizedRerootCumulativeRule45Keys_reflect]
      cases comparison : input.compareLocalizedRerootCumulativeRule45Keys key head with
      | lt =>
          rw [insertLocalizedRerootCumulativeRule45Key_reflect input key tail]
          rfl
      | eq => rfl
      | gt => rfl

/-- The actual cumulative sibling sort commutes with canonical key reflection. -/
theorem sortLocalizedRerootCumulativeRule45Keys_reflect
    (input : CertifiedLocalizedCIPInput) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key,
      input.sortLocalizedRerootCumulativeRule45Keys
          (keys.map (reflectLocalizedRerootCumulativeRule45Key input)) =
        (input.sortLocalizedRerootCumulativeRule45Keys keys).map
          (reflectLocalizedRerootCumulativeRule45Key input)
  | [] => rfl
  | key :: keys => by
      rw [List.map_cons]
      simp only [sortLocalizedRerootCumulativeRule45Keys]
      rw [sortLocalizedRerootCumulativeRule45Keys_reflect input keys]
      exact insertLocalizedRerootCumulativeRule45Key_reflect input key
        (input.sortLocalizedRerootCumulativeRule45Keys keys)

/-! ## Projection and list helpers -/

/-- The canonical reflection fixes the constitutional projection. -/
@[simp] theorem reflectLocalizedRerootCumulativeRule45Key_constitutional
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    (reflectLocalizedRerootCumulativeRule45Key input key).constitutional =
      key.constitutional := rfl

/-- The constitutional projection, as a function, is fixed by key reflection. -/
private theorem constitutional_comp_reflect (input : CertifiedLocalizedCIPInput) :
    (fun key : input.LocalizedRerootCumulativeRule45Key => key.constitutional) ∘
        reflectLocalizedRerootCumulativeRule45Key input =
      fun key => key.constitutional := by
  funext key
  rfl

/-- The canonical reflection fixes the cumulative descriptor projection. -/
@[simp] theorem reflectLocalizedRerootCumulativeRule45Key_descriptor
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    (reflectLocalizedRerootCumulativeRule45Key input key).descriptor =
      key.descriptor := rfl

/-- The canonical reflection reflects the exact-label projection. -/
@[simp] theorem reflectLocalizedRerootCumulativeRule45Key_labels
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    (reflectLocalizedRerootCumulativeRule45Key input key).labels =
      reflectUppercaseRankedLabels key.labels := rfl

/-- The canonical reflection reflects the hierarchy-rank-addressed label projection. -/
@[simp] theorem reflectLocalizedRerootCumulativeRule45Key_rankedLabels
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    (reflectLocalizedRerootCumulativeRule45Key input key).rankedLabels =
      reflectUppercaseRankedLabels key.rankedLabels := rfl

/-- Entrywise label reflection preserves the number of observed spheres. -/
@[simp] theorem length_reflectUppercaseRankedLabels
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    (reflectUppercaseRankedLabels layers).length = layers.length := by
  simp [reflectUppercaseRankedLabels]

/-- The sphere-indexed `getD` projection commutes with entrywise label reflection. -/
theorem reflectUppercaseRankedLabels_getD
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (depth : Nat) :
    (reflectUppercaseRankedLabels layers).getD depth [] =
      (layers.getD depth []).map reflectUppercaseRankedEntry := by
  induction layers generalizing depth with
  | nil => cases depth <;> rfl
  | cons layer layers inductionHypothesis =>
      cases depth with
      | zero => rfl
      | succ depth => exact inductionHypothesis depth

/-- `prefixLayer` commutes with the entrywise label reflection. -/
theorem prefixLayer_reflectUppercaseRankedEntry (slot : Nat)
    (layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :
    OfficialRuleMajorKey.prefixLayer slot (layer.map reflectUppercaseRankedEntry) =
      (OfficialRuleMajorKey.prefixLayer slot layer).map
        reflectUppercaseRankedEntry := by
  unfold OfficialRuleMajorKey.prefixLayer
  rw [List.map_map, List.map_map]
  rfl

private theorem flatMap_congr_reflect {α β : Type*} (values : List α)
    {first second : α → List β} (agrees : ∀ value, first value = second value) :
    values.flatMap first = values.flatMap second := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp [agrees value, inductionHypothesis]

/-! ## Child layer counts -/

private theorem foldl_descriptor_length_reflect
    (input : CertifiedLocalizedCIPInput) :
    ∀ (children : List input.LocalizedRerootCumulativeRule45Key) (accumulator : Nat),
      (children.map (reflectLocalizedRerootCumulativeRule45Key input)).foldl
          (fun longest child => max longest child.descriptor.length) accumulator =
        children.foldl
          (fun longest child => max longest child.descriptor.length) accumulator
  | [], accumulator => rfl
  | child :: children, accumulator => by
      simp only [List.map_cons, List.foldl_cons]
      exact foldl_descriptor_length_reflect input children _

private theorem foldl_label_length_reflect
    (input : CertifiedLocalizedCIPInput) :
    ∀ (children : List input.LocalizedRerootCumulativeRule45Key) (accumulator : Nat),
      (children.map (reflectLocalizedRerootCumulativeRule45Key input)).foldl
          (fun longest child => max longest child.labels.length) accumulator =
        children.foldl
          (fun longest child => max longest child.labels.length) accumulator
  | [], accumulator => rfl
  | child :: children, accumulator => by
      simp only [List.map_cons, List.foldl_cons,
        reflectLocalizedRerootCumulativeRule45Key_labels]
      rw [length_reflectUppercaseRankedLabels]
      exact foldl_label_length_reflect input children _

private theorem foldl_rankedLabel_length_reflect
    (input : CertifiedLocalizedCIPInput) :
    ∀ (children : List input.LocalizedRerootCumulativeRule45Key) (accumulator : Nat),
      (children.map (reflectLocalizedRerootCumulativeRule45Key input)).foldl
          (fun longest child => max longest child.rankedLabels.length) accumulator =
        children.foldl
          (fun longest child => max longest child.rankedLabels.length) accumulator
  | [], accumulator => rfl
  | child :: children, accumulator => by
      simp only [List.map_cons, List.foldl_cons,
        reflectLocalizedRerootCumulativeRule45Key_rankedLabels]
      rw [length_reflectUppercaseRankedLabels]
      exact foldl_rankedLabel_length_reflect input children _

theorem localizedRerootDescriptorChildLayerCount_reflect
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.localizedRerootDescriptorChildLayerCount
        (children.map (reflectLocalizedRerootCumulativeRule45Key input)) =
      input.localizedRerootDescriptorChildLayerCount children :=
  foldl_descriptor_length_reflect input children 0

theorem localizedRerootLabelChildLayerCount_reflect
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.localizedRerootLabelChildLayerCount
        (children.map (reflectLocalizedRerootCumulativeRule45Key input)) =
      input.localizedRerootLabelChildLayerCount children :=
  foldl_label_length_reflect input children 0

theorem localizedRerootRankedLabelChildLayerCount_reflect
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.localizedRerootRankedLabelChildLayerCount
        (children.map (reflectLocalizedRerootCumulativeRule45Key input)) =
      input.localizedRerootRankedLabelChildLayerCount children :=
  foldl_rankedLabel_length_reflect input children 0

/-! ## Cumulative descriptor merge -/

/-- Merging cumulative descriptor spheres is literally invariant under key reflection. -/
theorem mergeLocalizedRerootDescriptorChildren_reflect
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.mergeLocalizedRerootDescriptorChildren
        (children.map (reflectLocalizedRerootCumulativeRule45Key input)) =
      input.mergeLocalizedRerootDescriptorChildren children := by
  unfold mergeLocalizedRerootDescriptorChildren
  rw [localizedRerootDescriptorChildLayerCount_reflect]
  apply List.map_congr_left
  intro depth _
  rw [List.zipIdx_map, List.flatMap_map]
  apply flatMap_congr_reflect
  rintro ⟨child, slot⟩
  rfl

/-! ## Exact-label merge -/

/-- Merging exact-label spheres reflects entrywise. -/
theorem mergeLocalizedRerootLabelChildren_reflect
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.mergeLocalizedRerootLabelChildren
        (children.map (reflectLocalizedRerootCumulativeRule45Key input)) =
      reflectUppercaseRankedLabels
        (input.mergeLocalizedRerootLabelChildren children) := by
  unfold mergeLocalizedRerootLabelChildren
  unfold reflectUppercaseRankedLabels
  rw [localizedRerootLabelChildLayerCount_reflect, List.map_map]
  apply List.map_congr_left
  intro depth _
  simp only [Function.comp_apply]
  rw [List.zipIdx_map, List.flatMap_map, List.map_flatMap]
  apply flatMap_congr_reflect
  rintro ⟨child, slot⟩
  simp only [reflectLocalizedRerootCumulativeRule45Key_labels,
    reflectUppercaseRankedLabels_getD, prefixLayer_reflectUppercaseRankedEntry,
    Prod.map_fst, Prod.map_snd, id]

/-! ## Hierarchy-rank children -/

/-- Equal-rank continuation reflects: reflection preserves the actual cumulative comparator, hence
the rank decision. -/
theorem localizedRerootRankedChildTail_reflect
    (input : CertifiedLocalizedCIPInput)
    (previous : input.LocalizedRerootCumulativeRule45Key) (rank : Nat) :
    ∀ children : List input.LocalizedRerootCumulativeRule45Key,
      input.localizedRerootRankedChildTail
          (reflectLocalizedRerootCumulativeRule45Key input previous) rank
          (children.map (reflectLocalizedRerootCumulativeRule45Key input)) =
        (input.localizedRerootRankedChildTail previous rank children).map
          (Prod.map (reflectLocalizedRerootCumulativeRule45Key input) id)
  | [] => rfl
  | child :: children => by
      simp only [List.map_cons, localizedRerootRankedChildTail]
      rw [compareLocalizedRerootCumulativeRule45Keys_reflect]
      by_cases same : input.compareLocalizedRerootCumulativeRule45Keys child previous =
        Ordering.eq
      · rw [if_pos same]
        rw [localizedRerootRankedChildTail_reflect input child rank children]
        rfl
      · rw [if_neg same]
        rw [localizedRerootRankedChildTail_reflect input child (rank + 1) children]
        rfl

/-- The rank assignment over a child list reflects together with the keys. -/
theorem localizedRerootRankedChildren_reflect
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.localizedRerootRankedChildren
        (children.map (reflectLocalizedRerootCumulativeRule45Key input)) =
      (input.localizedRerootRankedChildren children).map
        (Prod.map (reflectLocalizedRerootCumulativeRule45Key input) id) := by
  cases children with
  | nil => rfl
  | cons child children =>
      simp only [List.map_cons, localizedRerootRankedChildren]
      rw [localizedRerootRankedChildTail_reflect input child 0 children]
      rfl

/-! ## Hierarchy-rank-addressed label merge -/

/-- Merging rank-addressed label spheres reflects entrywise. -/
theorem mergeLocalizedRerootRankedLabelChildren_reflect
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.mergeLocalizedRerootRankedLabelChildren
        (children.map (reflectLocalizedRerootCumulativeRule45Key input)) =
      reflectUppercaseRankedLabels
        (input.mergeLocalizedRerootRankedLabelChildren children) := by
  unfold mergeLocalizedRerootRankedLabelChildren
  unfold reflectUppercaseRankedLabels
  rw [localizedRerootRankedLabelChildLayerCount_reflect, List.map_map]
  rw [localizedRerootRankedChildren_reflect]
  apply List.map_congr_left
  intro depth _
  simp only [Function.comp_apply]
  rw [List.flatMap_map, List.map_flatMap]
  apply flatMap_congr_reflect
  rintro ⟨child, rank⟩
  simp only [reflectLocalizedRerootCumulativeRule45Key_rankedLabels,
    reflectUppercaseRankedLabels_getD, prefixLayer_reflectUppercaseRankedEntry,
    Prod.map_fst, Prod.map_snd, id]

/-! ## The actual builder commutes with simultaneous stage and label reflection -/

/-- **Cumulative builder reflection.**  At every actual fuel and every actual cursor, the
production builder driven by the reflected reader and stage equals the key reflection of the
production builder driven by the original reader and stage.  The equality is a full `Option`
equality, so a fail-closed `none` is preserved and a successful compilation reflects through the
key reflection at unchanged rank addresses. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_reflectUppercase
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (reflectLocalizedCumulativeRule45Stage stage)
          (fun cursor => reflectUppercaseOptionalLabel (read cursor)) fuel cursor =
        Option.map (reflectLocalizedRerootCumulativeRule45Key input)
          (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel cursor)
  | 0, cursor => by
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead?
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed]
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal, reflectLocalizedRerootCumulativeRule45Key,
              reflectUppercaseRankedEntry, reflectUppercaseRankedLabels]
          · simp [childrenComputed, terminal]
  | fuel + 1, cursor => by
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead?
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed]
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal, reflectLocalizedRerootCumulativeRule45Key,
              reflectUppercaseRankedEntry, reflectUppercaseRankedLabels]
          · have mapMReflection :
                ∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
                  cursors.mapM (fun child =>
                      input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                        (reflectLocalizedCumulativeRule45Stage stage)
                        (fun cursor => reflectUppercaseOptionalLabel (read cursor))
                        fuel child) =
                    (cursors.mapM (fun child =>
                      input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                        stage read fuel child)).map
                      (List.map (reflectLocalizedRerootCumulativeRule45Key input)) := by
              intro cursors
              induction cursors with
              | nil => rfl
              | cons child children inductionHypothesis =>
                  rw [List.mapM_cons, List.mapM_cons,
                    buildLocalizedRerootCumulativeRule45KeyWithRead?_reflectUppercase
                      input stage read fuel child]
                  cases computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                      stage read fuel child with
                  | none => simp [computed]
                  | some childKey =>
                      cases remaining : List.mapM (fun child =>
                          input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                            stage read fuel child) children with
                      | none => simp [computed, remaining, inductionHypothesis]
                      | some tails => simp [computed, remaining, inductionHypothesis]
            cases childKeysComputed : children.mapM (fun child =>
                input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                  stage read fuel child) with
            | none =>
                have reflectedNone : children.mapM (fun child =>
                    input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                      (reflectLocalizedCumulativeRule45Stage stage)
                      (fun cursor => reflectUppercaseOptionalLabel (read cursor))
                      fuel child) = none := by
                  rw [mapMReflection, childKeysComputed]
                  rfl
                simp [childrenComputed, terminal, childKeysComputed, reflectedNone]
            | some childKeys =>
                have reflectedSome : children.mapM (fun child =>
                    input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                      (reflectLocalizedCumulativeRule45Stage stage)
                      (fun cursor => reflectUppercaseOptionalLabel (read cursor))
                      fuel child) =
                    some (childKeys.map (reflectLocalizedRerootCumulativeRule45Key input)) := by
                  rw [mapMReflection, childKeysComputed]
                  rfl
                simp [reflectedSome, childKeysComputed, terminal,
                  reflectLocalizedRerootCumulativeRule45Key,
                  reflectUppercaseRankedLabels, reflectUppercaseRankedEntry,
                  Function.comp_apply, constitutional_comp_reflect input,
                  sortLocalizedRerootCumulativeRule45Keys_reflect,
                  mergeLocalizedRerootDescriptorChildren_reflect,
                  mergeLocalizedRerootLabelChildren_reflect,
                  mergeLocalizedRerootRankedLabelChildren_reflect,
                  List.map_append, List.map_cons, List.map_nil, List.map_map]

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.reflectLocalizedCumulativeRule45Stage
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule5Priority_reflectUppercase
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCumulativeRule45Priority_reflectLocalizedCumulativeRule45Stage
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRerootCumulativeRule45UppercaseReflection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.reflectLocalizedRerootCumulativeRule45Key
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.reflectLocalizedRerootCumulativeRule45Key_reflection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCumulativeRule45Keys_congr_reflection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCumulativeRule45Keys_reflect
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.insertLocalizedRerootCumulativeRule45Key_reflect
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sortLocalizedRerootCumulativeRule45Keys_reflect
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.reflectLocalizedRerootCumulativeRule45Key_constitutional
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.reflectLocalizedRerootCumulativeRule45Key_descriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.reflectLocalizedRerootCumulativeRule45Key_labels
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.reflectLocalizedRerootCumulativeRule45Key_rankedLabels
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.length_reflectUppercaseRankedLabels
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.reflectUppercaseRankedLabels_getD
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.prefixLayer_reflectUppercaseRankedEntry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootDescriptorChildLayerCount_reflect
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootLabelChildLayerCount_reflect
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootRankedLabelChildLayerCount_reflect
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mergeLocalizedRerootDescriptorChildren_reflect
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mergeLocalizedRerootLabelChildren_reflect
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootRankedChildTail_reflect
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootRankedChildren_reflect
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mergeLocalizedRerootRankedLabelChildren_reflect
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_reflectUppercase

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
