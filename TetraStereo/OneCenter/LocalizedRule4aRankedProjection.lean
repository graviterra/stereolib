import TetraStereo.OneCenter.LocalizedCumulativeAssemblyRecovery
import TetraStereo.OneCenter.LocalizedCumulativeChildShapeRecovery
import TetraStereo.OneCenter.LocalizedRankedProjectionTransport

set_option autoImplicit false

/-!
# Ranked label projections are determined by the cumulative Rule-4a observable

A cumulative Rule-4a key carries four components.  The comparison-visible observable records the
constitutional Rule-1a/1b/2 projections and the cumulative descriptor projection, but not the exact
`labels` or the rank-addressed `rankedLabels`.  Two *independently derived* keys at possibly
different reroot cursors and with the same fuel can nevertheless have equal observables.

This module proves the closed cross-cursor invariant

```
observable key1 = observable key2 →
  key1.rankedLabels.map projectRule4aLayer = key2.rankedLabels.map projectRule4aLayer
```

for Rule-4a derivations at a common fuel.  The projection `projectRule4aLayer` discards the exact
`R`/`S` descriptor and retains only the unit-kind Rule-4a priority, so equal observables do *not*
imply equal `rankedLabels`; only their Rule-4a projections agree.

The proof is a structural induction on the fuel, generalizing both cursors and both keys.  At the
zero level only terminal derivations exist.  At a branch the parent descriptor root fixes the
parent priority, the assembled constitutional projection fixes the child count, and the
physical-slot prefix merge is inverted slot by slot to recover the child observables.  The sibling
lists are aligned pointwise, their hierarchy ranks are transported through the observable
comparison, the induction hypothesis is applied to corresponding children (which may sit at
different molecular cursors), and the projected rank-addressed merge is transported by
`projectRule4aLabelLayers_mergeLocalizedRerootRankedLabelChildren_eq_of_map_eq`.

No exact-rank payload, sibling identity or desired invariant is assumed.  The generic
rank/projection transport is taken from `LocalizedRankedProjectionTransport`; this module adds only
the derivation-level cross-cursor argument.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

open CumulativeAssembly

/-! ## Elementary list fact -/

/-- A layer list of length one is the singleton of its first layer. -/
theorem rule4aEqSingletonOfLengthOne {α : Type*} {layers : List (List α)}
    (length : layers.length = 1) :
    layers = [layers.getD 0 []] := by
  cases layers with
  | nil => simp at length
  | cons layer rest =>
      cases rest with
      | nil => rfl
      | cons second tail => simp at length

/-! ## Derivation-backed children of a sorted sibling list -/

/-- Every key of a pointwise derived child list is derived at some cursor of that list. -/
theorem rule4aDeclarativeKeyList_member
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys : List input.LocalizedRerootCumulativeRule45Key),
      input.DeclarativeLocalizedRerootCumulativeRule45KeyList
          stage target view fuel cursors keys →
        ∀ key ∈ keys, ∃ cursor ∈ cursors,
          input.DeclarativeLocalizedRerootCumulativeRule45Key
            stage target view fuel cursor key := by
  intro cursors
  induction cursors with
  | nil =>
      intro keys derived key present
      cases derived with
      | nil => simp at present
  | cons cursor cursors inductionHypothesis =>
      intro keys derived key present
      cases derived with
      | cons head tail =>
          rcases List.mem_cons.mp present with same | inTail
          · subst same
            exact ⟨cursor, by simp, head⟩
          · rcases inductionHypothesis _ tail key inTail with ⟨source, sourceMem, sourceDerived⟩
            exact ⟨source, List.mem_cons_of_mem cursor sourceMem, sourceDerived⟩

/-- Any member of a descending reordering of derived child keys is derived at some cursor of the
original cursor list. -/
theorem rule4aSortedMemberDerivation
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {children : List (input.LocalizedRerootCursor carrierFuel)}
    {childKeys sorted : List input.LocalizedRerootCumulativeRule45Key}
    (childDerivations : input.DeclarativeLocalizedRerootCumulativeRule45KeyList
      stage target view fuel children childKeys)
    (ranking : sorted.Perm childKeys) :
    ∀ key, key ∈ sorted →
      ∃ cursor, input.DeclarativeLocalizedRerootCumulativeRule45Key
        stage target view fuel cursor key := by
  intro key present
  rcases input.rule4aDeclarativeKeyList_member stage target view children childKeys
      childDerivations key (ranking.mem_iff.mp present) with ⟨cursor, _cursorMem, derived⟩
  exact ⟨cursor, derived⟩

/-! ## Replacing the assembled root by an observably equal one -/

/-- The observable of an assembled parent depends on the root only through its three rule
projections. -/
theorem rule4aObservableAssembledRootCongr
    (input : CertifiedLocalizedCIPInput)
    (rootLeft rootRight : OfficialRuleMajorKey input.Atom)
    (rule1a : rootLeft.rule1a = rootRight.rule1a)
    (rule1b : rootLeft.rule1b = rootRight.rule1b)
    (rule2 : rootLeft.rule2 = rootRight.rule2)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (descriptorRoot : List (List (OfficialSparseEntry (List Nat))))
    (labels rankedLabels :
      List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    input.localizedRerootCumulativeRule45Observable
      { constitutional := OfficialRuleMajorKey.assemble rootLeft
          (children.map fun child => child.constitutional)
        descriptor := descriptorRoot ++
          input.mergeLocalizedRerootDescriptorChildren children
        labels := labels
        rankedLabels := rankedLabels } =
      input.localizedRerootCumulativeRule45Observable
        { constitutional := OfficialRuleMajorKey.assemble rootRight
            (children.map fun child => child.constitutional)
          descriptor := descriptorRoot ++
            input.mergeLocalizedRerootDescriptorChildren children
          labels := labels
          rankedLabels := rankedLabels } := by
  simp only [localizedRerootCumulativeRule45Observable, OfficialRuleMajorKey.assemble]
  rw [rule1a, rule1b, rule2]

/-! ## Terminal keys -/

/-- Two terminal Rule-4a keys with equal observables have equal projected ranked labels.  The
exact labels may differ (`R` versus `S`); only the unit-kind priority is retained. -/
theorem rule4aTerminalRankedProjectionEq
    (input : CertifiedLocalizedCIPInput)
    (rootLeft rootRight : OfficialRuleMajorKey input.Atom)
    (labelLeft labelRight : Option LocalizedAuxiliaryLabel)
    (observableEq :
      input.localizedRerootCumulativeRule45Observable
        { constitutional := rootLeft
          descriptor := [[([], localizedCumulativeRule45Priority .rule4a labelLeft)]]
          labels := [[([], labelLeft)]]
          rankedLabels := [[([], labelLeft)]] } =
      input.localizedRerootCumulativeRule45Observable
        { constitutional := rootRight
          descriptor := [[([], localizedCumulativeRule45Priority .rule4a labelRight)]]
          labels := [[([], labelRight)]]
          rankedLabels := [[([], labelRight)]] }) :
    ([[(([], labelLeft))]] :
        List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))).map
          projectRule4aLayer =
      ([[(([], labelRight))]] : List
        (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))).map
          projectRule4aLayer := by
  have descriptorEq :
      ([[([], localizedCumulativeRule45Priority .rule4a labelLeft)]] :
          List (List (OfficialSparseEntry (List Nat)))) =
        [[([], localizedCumulativeRule45Priority .rule4a labelRight)]] :=
    congrArg LocalizedCumulativeRule45Observable.descriptor observableEq
  have priorityEq :
      localizedCumulativeRule45Priority .rule4a labelLeft =
        localizedCumulativeRule45Priority .rule4a labelRight := by
    have reading := congrArg (fun layers => layers.getD 0 []) descriptorEq
    simpa using reading
  simp [projectRule4aLayer, projectRule4aEntry, priorityEq]

/-! ## The cross-cursor branch step -/

/-- The branch step of the cross-cursor induction.  Both derivations are genuine Rule-4a branch
derivations at the same fuel; their sorted child lists may differ and are compared slot by slot
through the physical-prefix merge inverse, then merged through the hierarchy-rank transport. -/
theorem rule4aBranchRankedProjectionEq
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor1 cursor2 : input.LocalizedRerootCursor carrierFuel)
    {label1 label2 : Option LocalizedAuxiliaryLabel}
    {children1 children2 : List (input.LocalizedRerootCursor carrierFuel)}
    {childKeys1 childKeys2 sorted1 sorted2 :
      List input.LocalizedRerootCumulativeRule45Key}
    (frame1 : input.DeclarativeLocalizedRerootChildren cursor1 children1)
    (nonempty1 : children1 ≠ [])
    (observed1 : input.DeclarativeLocalizedDependencyLabel target view cursor1 label1)
    (childDerivations1 : input.DeclarativeLocalizedRerootCumulativeRule45KeyList
      .rule4a target view fuel children1 childKeys1)
    (ranking1 : sorted1.Perm childKeys1)
    (descending1 : input.LocalizedRerootCumulativeRule45KeysDescending sorted1)
    (frame2 : input.DeclarativeLocalizedRerootChildren cursor2 children2)
    (nonempty2 : children2 ≠ [])
    (observed2 : input.DeclarativeLocalizedDependencyLabel target view cursor2 label2)
    (childDerivations2 : input.DeclarativeLocalizedRerootCumulativeRule45KeyList
      .rule4a target view fuel children2 childKeys2)
    (ranking2 : sorted2.Perm childKeys2)
    (descending2 : input.LocalizedRerootCumulativeRule45KeysDescending sorted2)
    (parentObservable :
      input.localizedRerootCumulativeRule45Observable
        { constitutional := OfficialRuleMajorKey.assemble
            (input.moleculeGraph.officialRuleMajorRootKey
              cursor1.occurrence.1.node false)
            (sorted1.map fun child => child.constitutional)
          descriptor := [[([], localizedCumulativeRule45Priority .rule4a label1)]] ++
            input.mergeLocalizedRerootDescriptorChildren sorted1
          labels := [[([], label1)]] ++ input.mergeLocalizedRerootLabelChildren sorted1
          rankedLabels := [[([], label1)]] ++
            input.mergeLocalizedRerootRankedLabelChildren sorted1 } =
      input.localizedRerootCumulativeRule45Observable
        { constitutional := OfficialRuleMajorKey.assemble
            (input.moleculeGraph.officialRuleMajorRootKey
              cursor2.occurrence.1.node false)
            (sorted2.map fun child => child.constitutional)
          descriptor := [[([], localizedCumulativeRule45Priority .rule4a label2)]] ++
            input.mergeLocalizedRerootDescriptorChildren sorted2
          labels := [[([], label2)]] ++ input.mergeLocalizedRerootLabelChildren sorted2
          rankedLabels := [[([], label2)]] ++
            input.mergeLocalizedRerootRankedLabelChildren sorted2 })
    (childRankedProjection : ∀ (childKey1 childKey2 :
        input.LocalizedRerootCumulativeRule45Key)
        (childCursor1 childCursor2 : input.LocalizedRerootCursor carrierFuel),
      input.DeclarativeLocalizedRerootCumulativeRule45Key .rule4a target view fuel
        childCursor1 childKey1 →
      input.DeclarativeLocalizedRerootCumulativeRule45Key .rule4a target view fuel
        childCursor2 childKey2 →
      input.localizedRerootCumulativeRule45Observable childKey1 =
          input.localizedRerootCumulativeRule45Observable childKey2 →
      childKey1.rankedLabels.map projectRule4aLayer =
        childKey2.rankedLabels.map projectRule4aLayer) :
    (([[(([], label1))]] ++
        input.mergeLocalizedRerootRankedLabelChildren sorted1).map projectRule4aLayer) =
      (([[(([], label2))]] ++
        input.mergeLocalizedRerootRankedLabelChildren sorted2).map projectRule4aLayer) := by
  -- Name the two root keys.  They are definitionally the roots appearing in the observed keys.
  let root1 : OfficialRuleMajorKey input.Atom :=
    input.moleculeGraph.officialRuleMajorRootKey cursor1.occurrence.1.node false
  let root2 : OfficialRuleMajorKey input.Atom :=
    input.moleculeGraph.officialRuleMajorRootKey cursor2.occurrence.1.node false
  have root1Rule1aLength :
      (input.moleculeGraph.officialRuleMajorRootKey
        cursor1.occurrence.1.node false).rule1a.length = 1 := by
    simp
  have root1Rule1bLength :
      (input.moleculeGraph.officialRuleMajorRootKey
        cursor1.occurrence.1.node false).rule1b.length = 1 := by
    simp
  have root1Rule2Length :
      (input.moleculeGraph.officialRuleMajorRootKey
        cursor1.occurrence.1.node false).rule2.length = 1 := by
    simp
  have root2Rule1aLength :
      (input.moleculeGraph.officialRuleMajorRootKey
        cursor2.occurrence.1.node false).rule1a.length = 1 := by
    simp
  have root2Rule1bLength :
      (input.moleculeGraph.officialRuleMajorRootKey
        cursor2.occurrence.1.node false).rule1b.length = 1 := by
    simp
  have root2Rule2Length :
      (input.moleculeGraph.officialRuleMajorRootKey
        cursor2.occurrence.1.node false).rule2.length = 1 := by
    simp
  -- The parent descriptor roots fix the two parent priorities.
  have descriptorEq :
      ([[([], localizedCumulativeRule45Priority .rule4a label1)]] ++
          input.mergeLocalizedRerootDescriptorChildren sorted1 :
          List (List (OfficialSparseEntry (List Nat)))) =
        [[([], localizedCumulativeRule45Priority .rule4a label2)]] ++
          input.mergeLocalizedRerootDescriptorChildren sorted2 :=
    congrArg LocalizedCumulativeRule45Observable.descriptor parentObservable
  have priorityEq :
      localizedCumulativeRule45Priority .rule4a label1 =
        localizedCumulativeRule45Priority .rule4a label2 := by
    have reading := congrArg (fun layers => layers.getD 0 []) descriptorEq
    simpa using reading
  -- Reconstruct both derivations so that child-shape recovery applies.
  have childLengthEq : children1.length = children2.length :=
    input.childCount_eq_of_observable_eq .rule4a target view
      (DeclarativeLocalizedRerootCumulativeRule45Key.branch
        frame1 nonempty1 observed1 childDerivations1 ranking1 descending1)
      (DeclarativeLocalizedRerootCumulativeRule45Key.branch
        frame2 nonempty2 observed2 childDerivations2 ranking2 descending2)
      frame1 frame2 parentObservable
  have sortedLengthEq : sorted1.length = sorted2.length := by
    rw [ranking1.length_eq, ranking2.length_eq,
      input.declarativeCumulativeKeyList_length .rule4a target view children1 childKeys1
        childDerivations1,
      input.declarativeCumulativeKeyList_length .rule4a target view children2 childKeys2
        childDerivations2,
      childLengthEq]
  -- Every sorted child carries nonempty comparison-visible layers.
  have sortedNonempty1 : ∀ child ∈ sorted1, LocalizedKeyLayersNonempty input child := by
    intro child childMem
    rcases input.rule4aSortedMemberDerivation .rule4a target view
      childDerivations1 ranking1 child childMem with ⟨childCursor, childDerived⟩
    exact localizedKeyLayersNonempty_of_declarative input .rule4a target view fuel
      childCursor child childDerived
  have sortedNonempty2 : ∀ child ∈ sorted2, LocalizedKeyLayersNonempty input child := by
    intro child childMem
    rcases input.rule4aSortedMemberDerivation .rule4a target view
      childDerivations2 ranking2 child childMem with ⟨childCursor, childDerived⟩
    exact localizedKeyLayersNonempty_of_declarative input .rule4a target view fuel
      childCursor child childDerived
  -- Root projections agree, because the assembled observable records them.
  have root1a : root1.rule1a = root2.rule1a := by
    show (input.moleculeGraph.officialRuleMajorRootKey
        cursor1.occurrence.1.node false).rule1a =
      (input.moleculeGraph.officialRuleMajorRootKey
        cursor2.occurrence.1.node false).rule1a
    have assembled := congrArg LocalizedCumulativeRule45Observable.rule1a parentObservable
    simp only [localizedRerootCumulativeRule45Observable_rule1a,
      OfficialRuleMajorKey.assemble] at assembled
    have reading := congrArg (fun layers => layers.getD 0 []) assembled
    have getDReading :
        (input.moleculeGraph.officialRuleMajorRootKey
            cursor1.occurrence.1.node false).rule1a.getD 0 [] =
          (input.moleculeGraph.officialRuleMajorRootKey
            cursor2.occurrence.1.node false).rule1a.getD 0 [] := by
      simpa [List.getD_append, root1Rule1aLength, root2Rule1aLength] using reading
    rw [rule4aEqSingletonOfLengthOne root1Rule1aLength,
      rule4aEqSingletonOfLengthOne root2Rule1aLength, getDReading]
  have root1b : root1.rule1b = root2.rule1b := by
    show (input.moleculeGraph.officialRuleMajorRootKey
        cursor1.occurrence.1.node false).rule1b =
      (input.moleculeGraph.officialRuleMajorRootKey
        cursor2.occurrence.1.node false).rule1b
    have assembled := congrArg LocalizedCumulativeRule45Observable.rule1b parentObservable
    simp only [localizedRerootCumulativeRule45Observable_rule1b,
      OfficialRuleMajorKey.assemble] at assembled
    have reading := congrArg (fun layers => layers.getD 0 []) assembled
    have getDReading :
        (input.moleculeGraph.officialRuleMajorRootKey
            cursor1.occurrence.1.node false).rule1b.getD 0 [] =
          (input.moleculeGraph.officialRuleMajorRootKey
            cursor2.occurrence.1.node false).rule1b.getD 0 [] := by
      simpa [List.getD_append, root1Rule1bLength, root2Rule1bLength] using reading
    rw [rule4aEqSingletonOfLengthOne root1Rule1bLength,
      rule4aEqSingletonOfLengthOne root2Rule1bLength, getDReading]
  have root2Eq : root1.rule2 = root2.rule2 := by
    show (input.moleculeGraph.officialRuleMajorRootKey
        cursor1.occurrence.1.node false).rule2 =
      (input.moleculeGraph.officialRuleMajorRootKey
        cursor2.occurrence.1.node false).rule2
    have assembled := congrArg LocalizedCumulativeRule45Observable.rule2 parentObservable
    simp only [localizedRerootCumulativeRule45Observable_rule2,
      OfficialRuleMajorKey.assemble] at assembled
    have reading := congrArg (fun layers => layers.getD 0 []) assembled
    have getDReading :
        (input.moleculeGraph.officialRuleMajorRootKey
            cursor1.occurrence.1.node false).rule2.getD 0 [] =
          (input.moleculeGraph.officialRuleMajorRootKey
            cursor2.occurrence.1.node false).rule2.getD 0 [] := by
      simpa [List.getD_append, root1Rule2Length, root2Rule2Length] using reading
    rw [rule4aEqSingletonOfLengthOne root1Rule2Length,
      rule4aEqSingletonOfLengthOne root2Rule2Length, getDReading]
  -- Rewrite the second descriptor root to the first priority, then bridge the two roots.
  rw [← priorityEq] at parentObservable
  have bridge := rule4aObservableAssembledRootCongr input root1 root2
    root1a root1b root2Eq sorted2
    [[([], localizedCumulativeRule45Priority .rule4a label1)]]
    ([[([], label2)]] ++ input.mergeLocalizedRerootLabelChildren sorted2)
    ([[([], label2)]] ++ input.mergeLocalizedRerootRankedLabelChildren sorted2)
  have combined := parentObservable.trans bridge.symm
  have childObservable : ∀ (slot : Nat) (leftBound : slot < sorted1.length)
      (rightBound : slot < sorted2.length),
      input.localizedRerootCumulativeRule45Observable (sorted1[slot]'leftBound) =
        input.localizedRerootCumulativeRule45Observable (sorted2[slot]'rightBound) := by
    intro slot leftBound rightBound
    exact child_observable_eq_of_assembled_parent_observable_eq input _
      root1Rule1aLength root1Rule1bLength root1Rule2Length
      [[([], localizedCumulativeRule45Priority .rule4a label1)]] (by simp)
      sorted1 sorted2 sortedLengthEq sortedNonempty1 sortedNonempty2
      ([[([], label1)]] ++ input.mergeLocalizedRerootLabelChildren sorted1)
      ([[([], label1)]] ++ input.mergeLocalizedRerootRankedLabelChildren sorted1)
      ([[([], label2)]] ++ input.mergeLocalizedRerootLabelChildren sorted2)
      ([[([], label2)]] ++ input.mergeLocalizedRerootRankedLabelChildren sorted2)
      combined slot leftBound
  -- The sorted child lists have equal observable sequences.
  have observablesEq : sorted1.map input.localizedRerootCumulativeRule45Observable =
      sorted2.map input.localizedRerootCumulativeRule45Observable := by
    apply List.ext_getElem
    · simpa using sortedLengthEq
    · intro index leftBound rightBound
      simp only [List.getElem_map]
      exact childObservable index (by simpa using leftBound) (by simpa using rightBound)
  -- Apply the induction hypothesis to corresponding children.
  have childProjection : ∀ (slot : Nat) (leftBound : slot < sorted1.length)
      (rightBound : slot < sorted2.length),
      (sorted1[slot]'leftBound).rankedLabels.map projectRule4aLayer =
        (sorted2[slot]'rightBound).rankedLabels.map projectRule4aLayer := by
    intro slot leftBound rightBound
    rcases input.rule4aSortedMemberDerivation .rule4a target view
      childDerivations1 ranking1 _ (List.getElem_mem leftBound) with
      ⟨childCursor1, childDerived1⟩
    rcases input.rule4aSortedMemberDerivation .rule4a target view
      childDerivations2 ranking2 _ (List.getElem_mem rightBound) with
      ⟨childCursor2, childDerived2⟩
    exact childRankedProjection _ _ childCursor1 childCursor2 childDerived1 childDerived2
      (childObservable slot leftBound rightBound)
  -- The projected whole-stack sequences of the children agree.
  have projectedEq :
      sorted1.map (fun key => projectRule4aLabelLayers key.rankedLabels) =
        sorted2.map (fun key => projectRule4aLabelLayers key.rankedLabels) := by
    apply List.ext_getElem
    · simpa using sortedLengthEq
    · intro index leftBound rightBound
      simp only [List.getElem_map]
      simpa [projectRule4aLabelLayers] using
        childProjection index (by simpa using leftBound) (by simpa using rightBound)
  -- Transport the projected rank-addressed merge.
  have mergedEq :
      (input.mergeLocalizedRerootRankedLabelChildren sorted1).map projectRule4aLayer =
        (input.mergeLocalizedRerootRankedLabelChildren sorted2).map projectRule4aLayer :=
    input.projectRule4aLabelLayers_mergeLocalizedRerootRankedLabelChildren_eq_of_map_eq
      sorted1 sorted2 observablesEq projectedEq
  rw [List.map_append, List.map_append, mergedEq]
  congr 1
  simp [projectRule4aLayer, projectRule4aEntry, priorityEq]

/-! ## The closed cross-cursor invariant -/

/-- **Closed Rule-4a invariant A.** Two independently derived cumulative Rule-4a keys at a common
fuel, possibly at different reroot cursors, whose comparison-visible observables agree have equal
Rule-4a-projected `rankedLabels`.  The cursors, keys and hidden exact labels remain independent;
only the unit-kind priority layers are compared. -/
theorem declarative_rule4a_rankedLabels_projection_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat)
      (cursor1 cursor2 : input.LocalizedRerootCursor carrierFuel)
      (key1 key2 : input.LocalizedRerootCumulativeRule45Key),
      input.DeclarativeLocalizedRerootCumulativeRule45Key .rule4a target view fuel
        cursor1 key1 →
      input.DeclarativeLocalizedRerootCumulativeRule45Key .rule4a target view fuel
        cursor2 key2 →
      input.localizedRerootCumulativeRule45Observable key1 =
        input.localizedRerootCumulativeRule45Observable key2 →
      key1.rankedLabels.map projectRule4aLayer =
        key2.rankedLabels.map projectRule4aLayer := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor1 cursor2 key1 key2 derived1 derived2 observableEq
      cases derived1 with
      | terminal frame1 empty1 observed1 =>
          cases derived2 with
          | terminal frame2 empty2 observed2 =>
              exact rule4aTerminalRankedProjectionEq input _ _ _ _ observableEq
  | succ fuel inductionHypothesis =>
      intro cursor1 cursor2 key1 key2 derived1 derived2 observableEq
      cases derived1 with
      | terminal frame1 empty1 observed1 =>
          cases derived2 with
          | terminal frame2 empty2 observed2 =>
              exact rule4aTerminalRankedProjectionEq input _ _ _ _ observableEq
          | branch frame2 nonempty2 observed2 childDerivations2 ranking2 descending2 =>
              exact absurd observableEq.symm
                (input.observable_ne_of_nonempty_nil_frames .rule4a target view
                  (DeclarativeLocalizedRerootCumulativeRule45Key.branch
                    frame2 nonempty2 observed2 childDerivations2 ranking2 descending2)
                  (DeclarativeLocalizedRerootCumulativeRule45Key.terminal (fuel := fuel)
                    frame1 empty1 observed1)
                  frame2 (empty1 ▸ frame1) nonempty2)
      | branch frame1 nonempty1 observed1 childDerivations1 ranking1 descending1 =>
          cases derived2 with
          | terminal frame2 empty2 observed2 =>
              exact absurd observableEq
                (input.observable_ne_of_nonempty_nil_frames .rule4a target view
                  (DeclarativeLocalizedRerootCumulativeRule45Key.branch
                    frame1 nonempty1 observed1 childDerivations1 ranking1 descending1)
                  (DeclarativeLocalizedRerootCumulativeRule45Key.terminal (fuel := fuel)
                    frame2 empty2 observed2)
                  frame1 (empty2 ▸ frame2) nonempty1)
          | branch frame2 nonempty2 observed2 childDerivations2 ranking2 descending2 =>
              exact rule4aBranchRankedProjectionEq input target view cursor1 cursor2
                frame1 nonempty1 observed1 childDerivations1 ranking1 descending1
                frame2 nonempty2 observed2 childDerivations2 ranking2 descending2
                observableEq
                (fun childKey1 childKey2 childCursor1 childCursor2 childDerived1 childDerived2
                  childObservableEq =>
                  inductionHypothesis childCursor1 childCursor2 childKey1 childKey2
                    childDerived1 childDerived2 childObservableEq)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
