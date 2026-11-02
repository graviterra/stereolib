import TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Key
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Parametric label reading for cumulative occurrence-reroot keys

`LocalizedRerootCumulativeRule45Key` compiles cumulative Rules-4a--5 keys over exact reroot
cursors, but every node label is read through one restricted dependency view
(`localizedDependencyLabel target view`).  That makes it impossible to compare the *same* key
construction driven by a different label source: two restricted views of one target are not a
meaningful external reading.

This module separates the reading of labels from the construction of the key.
`buildLocalizedRerootCumulativeRule45KeyWithRead?` takes an arbitrary total callback

`read : cursor → Option LocalizedAuxiliaryLabel`

and otherwise performs exactly the production construction: it reuses the actual
`localizedRerootChildren?` frame reader, the actual cumulative sibling sort
`sortLocalizedRerootCumulativeRule45Keys`, the actual descriptor/label/ranked-label merges, the
actual `officialRuleMajorRootKey` root projections and the actual
`OfficialRuleMajorKey.assemble` branching.  Only the label observation is supplied by `read`.

## Main results

* `buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel` — specializing
  the callback to the existing `localizedDependencyLabel target view` reproduces the existing
  `buildLocalizedRerootCumulativeRule45Key?` *exactly*, for every fuel and every cursor (proved by
  induction on fuel, with no assumed equality).
* `buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative` — every
  successful parametric compilation has a constitutional projection satisfying the existing,
  label-independent `DeclarativeLocalizedRerootRuleMajorKey` derivation.  This is the comparison
  seam: keys built from arbitrary (even different) label callbacks are compared through their
  constitutionally derived projections, not by assuming old/new projected-key equality.
* `buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_complete` — those
  constitutional projections are complete, hence `OfficialRuleMajorKey.compare?` is total on any
  two of them
  (`buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_compare?_isSome`).

## Scope

The callback is a total function into `Option LocalizedAuxiliaryLabel`.  The value `none` is the
structural "no label observation at this cursor" value that the cumulative priority vectors in
`LocalizedRerootCumulativeRule45Key` already consume; it is *not* identified with, and carries no
claim about, any unavailable physical input or any particular chemical configuration.  This module
proves structural mathematics only.  It does not add a solver, an evaluator or a production path.
-/

namespace CertifiedLocalizedCIPInput

/-- Label-callback form of the cumulative reroot builder.  `read` is total; `none` is the
structural absence of a label observation, exactly as consumed by the cumulative priority
vectors.  Everything except the label source is the production construction. -/
noncomputable def buildLocalizedRerootCumulativeRule45KeyWithRead?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    Nat → input.LocalizedRerootCursor carrierFuel →
      Option input.LocalizedRerootCumulativeRule45Key
  | 0, cursor => do
      let children ← input.localizedRerootChildren? cursor
      if children = [] then
        let label := read cursor
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
      else none
  | fuel + 1, cursor => do
      let children ← input.localizedRerootChildren? cursor
      let label := read cursor
      if children = [] then
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
      else
        let childKeys ← children.mapM
          (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel)
        let sorted := input.sortLocalizedRerootCumulativeRule45Keys childKeys
        some
          { constitutional := OfficialRuleMajorKey.assemble
              (input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            descriptor :=
              [[([], localizedCumulativeRule45Priority stage label)]] ++
                input.mergeLocalizedRerootDescriptorChildren sorted
            labels := [[([], label)]] ++
              input.mergeLocalizedRerootLabelChildren sorted
            rankedLabels := [[([], label)]] ++
              input.mergeLocalizedRerootRankedLabelChildren sorted }

/-! ## Generic `mapM` facts -/

/-- Pointwise agreement of two `Option`-valued functions lifts through `List.mapM`. -/
private theorem list_mapM_congr {α β : Type*} {first second : α → Option β}
    (agrees : ∀ value, first value = second value) :
    ∀ values : List α, values.mapM first = values.mapM second
  | [] => rfl
  | value :: values => by
      simp [List.mapM_cons, agrees value, list_mapM_congr agrees values]

/-- Every successful `List.mapM` result element comes from some source element. -/
private theorem list_mapM_member {α β : Type*} (reader : α → Option β) :
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
              · rcases list_mapM_member reader values tail tailComputed result tailPresent with
                  ⟨source, sourcePresent, sourceComputed⟩
                exact ⟨source, List.mem_cons_of_mem value sourcePresent, sourceComputed⟩

/-! ## Recovery of the production builder -/

/-- Specializing the callback to the existing restricted dependency reader reproduces the
existing cumulative builder exactly, for every fuel and cursor. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor =
      input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel cursor
  | 0, cursor => by
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead?
        buildLocalizedRerootCumulativeRule45Key?
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp
      | some children =>
          by_cases terminal : children = []
          · simp [terminal]
          · simp [terminal]
  | fuel + 1, cursor => by
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead?
        buildLocalizedRerootCumulativeRule45Key?
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp
      | some children =>
          by_cases terminal : children = []
          · simp [terminal]
          · have congruence :
                children.mapM (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                    stage (fun cursor =>
                      input.localizedDependencyLabel target view cursor) fuel) =
                  children.mapM (input.buildLocalizedRerootCumulativeRule45Key?
                    stage target view fuel) :=
              list_mapM_congr
                (fun child =>
                  buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
                    input stage target view fuel child)
                children
            simp [terminal, congruence]

/-! ## Constitutional projection of arbitrary label readings -/

/-- The cumulative comparator inspects the constitutional component first: a non-`lt` cumulative
comparison forces a non-`lt` constitutional comparison. -/
theorem compareLocalizedRerootCumulativeRule45Keys_constitutional_ne_lt
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (notLt : input.compareLocalizedRerootCumulativeRule45Keys left right ≠ Ordering.lt) :
    OfficialRuleMajorKey.compare left.constitutional right.constitutional ≠ Ordering.lt := by
  intro constitutionalLt
  apply notLt
  unfold compareLocalizedRerootCumulativeRule45Keys
  simp [compareLex, Ordering.byKey, constitutionalLt]

/-- A descending cumulative sibling list stays descending when projected to the constitutional
component.  Labels are irrelevant to this projection. -/
theorem LocalizedRerootCumulativeRule45KeysDescending.constitutionalImage
    (input : CertifiedLocalizedCIPInput)
    {keys : List input.LocalizedRerootCumulativeRule45Key}
    (descending : input.LocalizedRerootCumulativeRule45KeysDescending keys) :
    OfficialRuleMajorKey.Descending (keys.map fun key => key.constitutional) := by
  unfold LocalizedRerootCumulativeRule45KeysDescending at descending
  unfold OfficialRuleMajorKey.Descending
  refine List.Pairwise.map (S := fun left right =>
    OfficialRuleMajorKey.compare left right ≠ Ordering.lt)
    (fun key => key.constitutional) ?_ descending
  intro left right notLt
  exact input.compareLocalizedRerootCumulativeRule45Keys_constitutional_ne_lt
    left right notLt

private theorem mapM_buildWithRead?_constitutional_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (sound : ∀ (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        stage read fuel cursor = some key →
      input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key.constitutional) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys : List input.LocalizedRerootCumulativeRule45Key),
      cursors.mapM (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        stage read fuel) = some keys →
      input.DeclarativeLocalizedRerootRuleMajorKeyList fuel cursors
        (keys.map fun key => key.constitutional)
  | [], keys, computed => by
      simp at computed
      subst keys
      exact DeclarativeLocalizedRerootRuleMajorKeyList.nil fuel
  | cursor :: cursors, keys, computed => by
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
              exact DeclarativeLocalizedRerootRuleMajorKeyList.cons
                (sound cursor head headComputed)
                (mapM_buildWithRead?_constitutional_declarative
                  input stage read sound cursors tail tailComputed)

/-- Every successful parametric compilation has a constitutional projection satisfying the
existing independent `DeclarativeLocalizedRerootRuleMajorKey` derivation.  The derivation is
label-independent, so it holds for arbitrary and even differing label callbacks; in particular no
equality of projected keys or of old and new builds is assumed. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel cursor = some key →
      input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key.constitutional
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            exact DeclarativeLocalizedRerootRuleMajorKey.terminal
              (input.localizedRerootChildren?_sound cursor children childrenComputed)
              terminal
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            exact DeclarativeLocalizedRerootRuleMajorKey.terminal
              (input.localizedRerootChildren?_sound cursor children childrenComputed)
              terminal
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                  stage read fuel) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
                subst key
                exact DeclarativeLocalizedRerootRuleMajorKey.branch
                  (input.localizedRerootChildren?_sound
                    cursor children childrenComputed)
                  terminal
                  (mapM_buildWithRead?_constitutional_declarative input stage read
                    (fun child childKey childComputed =>
                      buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
                        input stage read fuel child childKey childComputed)
                    children childKeys childKeysComputed)
                  (List.Perm.map (fun key => key.constitutional)
                    (input.sortLocalizedRerootCumulativeRule45Keys_perm childKeys))
                  (LocalizedRerootCumulativeRule45KeysDescending.constitutionalImage input
                    (input.sortLocalizedRerootCumulativeRule45Keys_descending childKeys))

/-- The constitutional projection of a successful parametric compilation is complete, whatever
the label callback is. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel cursor = some key →
      key.constitutional.complete = true
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
                (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                  stage read fuel) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
                subst key
                unfold OfficialRuleMajorKey.assemble
                rw [List.all_eq_true]
                intro child childPresent
                rw [List.mem_map] at childPresent
                rcases childPresent with ⟨childKey, childSortedPresent, rfl⟩
                have childSourcePresent : childKey ∈ childKeys :=
                  (input.sortLocalizedRerootCumulativeRule45Keys_perm
                    childKeys).mem_iff.mp childSortedPresent
                rcases list_mapM_member
                    (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                      stage read fuel) children childKeys childKeysComputed
                    childKey childSourcePresent with
                  ⟨childCursor, _cursorPresent, childComputed⟩
                exact input.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_complete
                  stage read fuel childCursor childKey childComputed

/-- Explicit comparison seam: two successful parametric compilations at the same cursor, with
possibly different stages and label callbacks, both satisfy the same independent constitutional
relation.  This is what makes their constitutional projections comparable without assuming any
label equality. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_seam
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (firstStage secondStage : LocalizedCumulativeRule45Stage)
    (firstRead secondRead : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (firstKey secondKey : input.LocalizedRerootCumulativeRule45Key)
    (firstComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      firstStage firstRead fuel cursor = some firstKey)
    (secondComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      secondStage secondRead fuel cursor = some secondKey) :
    input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor firstKey.constitutional ∧
      input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor secondKey.constitutional :=
  ⟨input.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
      firstStage firstRead fuel cursor firstKey firstComputed,
    input.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
      secondStage secondRead fuel cursor secondKey secondComputed⟩

/-- Any two successful parametric compilations, however their labels, stages, cursors or carrier
fuels differ, have a total safe comparison of their constitutional projections. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_compare?_isSome
    (input : CertifiedLocalizedCIPInput)
    {firstCarrierFuel secondCarrierFuel : Nat}
    (firstStage secondStage : LocalizedCumulativeRule45Stage)
    (firstRead : input.LocalizedRerootCursor firstCarrierFuel →
      Option LocalizedAuxiliaryLabel)
    (secondRead : input.LocalizedRerootCursor secondCarrierFuel →
      Option LocalizedAuxiliaryLabel)
    (firstFuel : Nat) (firstCursor : input.LocalizedRerootCursor firstCarrierFuel)
    (secondFuel : Nat) (secondCursor : input.LocalizedRerootCursor secondCarrierFuel)
    (firstKey secondKey : input.LocalizedRerootCumulativeRule45Key)
    (firstComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      firstStage firstRead firstFuel firstCursor = some firstKey)
    (secondComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      secondStage secondRead secondFuel secondCursor = some secondKey) :
    (OfficialRuleMajorKey.compare? firstKey.constitutional secondKey.constitutional).isSome =
      true :=
  OfficialRuleMajorKey.compare?_isSome_of_complete firstKey.constitutional
    secondKey.constitutional
    (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_complete
      firstStage firstRead firstFuel firstCursor firstKey firstComputed)
    (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_complete
      secondStage secondRead secondFuel secondCursor secondKey secondComputed)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards

The guarded declarations are the parametric builder itself and its seven public
recovery/coherence theorems.  `assert_kernel_only` permits exactly `propext`,
`Classical.choice` and `Quot.sound`, and rejects `sorryAx`, project axioms and native/compiler
trust. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCumulativeRule45Keys_constitutional_ne_lt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRerootCumulativeRule45KeysDescending.constitutionalImage
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_complete
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_seam
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_compare?_isSome
