import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableUnique
import TetraStereo.OneCenter.LocalizedRankedPopulationMerge
import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false

/-!
# Rule-4a hierarchy-rank population invariance for independent cumulative keys

`LocalizedCumulativeKeyObservableUnique` proves that two independent
`DeclarativeLocalizedRerootCumulativeRule45Key` derivations of the same cursor share their
comparison-visible observation.  That observation does not pin down the `rankedLabels` field: the
declarative relation admits arbitrary *descending* permutations of comparator-equivalent children.
At a fixed cursor the terminal label is in fact determined by the shared dependency view (the
executable exact-label reading is sound and complete); the remaining ambiguity lies in how
comparator-tied children are ordered, and, across different cursors, in differing `R`/`S` payloads.

This module proves the **population invariant (B)** needed by Rule 4b.  For two independent
derivations of the same cursor, at **every** sphere depth and hierarchy rank path, the uppercase
chiral-descriptor populations

`localizedChiralDescriptorsAtRank rank (key.rankedLabels.getD depth [])`

are related by `List.Perm`.  No equality of exact label payloads is assumed and the argument is
independent of the cross-cursor Rule-4a projection agreement `(A)`.

## Proof shape

The two derivations of one cursor are matched structurally.

* Terminal nodes are matched directly: the executable exact-label reading is sound and complete, so
  the two unique labels are equal.
* Branch nodes share their physical child frame (the executable frame is functional) and their
  unique label.  Each physical child is matched by the induction hypothesis.

At a branch, the left descending representative is transported to the right *original* child-key
list with `List.perm_comp_forall₂`, using the induction hypothesis as the refining relation
`R = observable-equality ∧ all-depth/all-rank population permutation`.  The generic
`localizedRerootRankedChildren_forall₂_of_relation` then assigns equal hierarchy ranks to matched
children.  Two applications of the already-proved generic merge transport
`LocalizedRankedPopulationMerge` finish the job:

* `mergeLocalizedRerootRankedLabelChildren_population_perm_of_forall₂` transports the left sorted
  list to the aligned middle list;
* `mergeLocalizedRerootRankedLabelChildren_population_perm_of_perm_of_descending` reorders that
  middle list to the right descending representative.

The middle list is descending because the comparator is exactly observable comparison and `R`
refines observable equality.

## Main public results

* `declarative_rule4a_rankedPopulationAgrees` — the packaged invariant for two independent
  derivations at a common fuel and cursor;
* `declarative_rule4a_rankedLabels_population_perm` — the per-depth/per-rank `List.Perm`
  corollary, which is exactly the Rule-4b population agreement `(B)`.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## The invariant -/

/-- Two independently derived cumulative keys of the same cursor agree on:

* their comparison-visible observable; and
* at every sphere depth and hierarchy rank path, the multiset (up to `List.Perm`) of uppercase
  chiral descriptors.

The first component is what makes comparator transport and the middle-list descending proof
usable; the second is the Rule-4b population agreement itself.  No equality of `rankedLabels`
layer counts or of exact label payloads is required: the padded merge transport handles depths
beyond a child's own stack. -/
def LocalizedRule4aRankedPopulationAgrees
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key) : Prop :=
  input.localizedRerootCumulativeRule45Observable left =
      input.localizedRerootCumulativeRule45Observable right ∧
    ∀ (depth : Nat) (rank : List Nat),
      (localizedChiralDescriptorsAtRank rank (left.rankedLabels.getD depth [])).Perm
        (localizedChiralDescriptorsAtRank rank (right.rankedLabels.getD depth []))

/-! ## Pointwise alignment of child-key lists -/

/-- Pointwise derivations of a common cursor list yield pointwise population agreement. -/
private theorem declarativeKeyList_forall₂_agrees
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (step : ∀ (cursor : input.LocalizedRerootCursor carrierFuel)
        (left right : input.LocalizedRerootCumulativeRule45Key),
      input.DeclarativeLocalizedRerootCumulativeRule45Key
        .rule4a target view fuel cursor left →
      input.DeclarativeLocalizedRerootCumulativeRule45Key
        .rule4a target view fuel cursor right →
      LocalizedRule4aRankedPopulationAgrees input left right) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keysLeft keysRight : List input.LocalizedRerootCumulativeRule45Key),
      input.DeclarativeLocalizedRerootCumulativeRule45KeyList
        .rule4a target view fuel cursors keysLeft →
      input.DeclarativeLocalizedRerootCumulativeRule45KeyList
        .rule4a target view fuel cursors keysRight →
      List.Forall₂
        (fun left right => LocalizedRule4aRankedPopulationAgrees input left right)
        keysLeft keysRight := by
  intro cursors
  induction cursors with
  | nil =>
      intro keysLeft keysRight derivedLeft derivedRight
      cases derivedLeft
      cases derivedRight
      exact List.Forall₂.nil
  | cons cursor cursors ih =>
      intro keysLeft keysRight derivedLeft derivedRight
      cases derivedLeft with
      | cons headLeft tailLeft =>
          cases derivedRight with
          | cons headRight tailRight =>
              exact List.Forall₂.cons (step cursor _ _ headLeft headRight)
                (ih _ _ tailLeft tailRight)

/-- Pointwise population agreement induces equality of the observation sequences. -/
private theorem map_observable_eq_of_forall₂_agrees
    (input : CertifiedLocalizedCIPInput)
    {left right : List input.LocalizedRerootCumulativeRule45Key}
    (aligned : List.Forall₂
      (fun left right => LocalizedRule4aRankedPopulationAgrees input left right) left right) :
    left.map input.localizedRerootCumulativeRule45Observable =
      right.map input.localizedRerootCumulativeRule45Observable := by
  induction aligned with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, head.1, ih]

/-! ## Physical child frames and exact labels are functional -/

/-- The executable child frame is functional: two derivations of the same cursor have the same
physical child list. -/
private theorem localizedRerootChildren_unique
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {left right : List (input.LocalizedRerootCursor carrierFuel)}
    (hl : input.DeclarativeLocalizedRerootChildren cursor left)
    (hr : input.DeclarativeLocalizedRerootChildren cursor right) : left = right :=
  Option.some.inj (((input.localizedRerootChildren?_eq_some_iff cursor left).mpr hl).symm.trans
    ((input.localizedRerootChildren?_eq_some_iff cursor right).mpr hr))

/-- A terminal derivation cannot share its cursor with a branch derivation. -/
private theorem false_of_terminal_branch
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {childrenLeft childrenRight : List (input.LocalizedRerootCursor carrierFuel)}
    (frameLeft : input.DeclarativeLocalizedRerootChildren cursor childrenLeft)
    (emptyLeft : childrenLeft = [])
    (frameRight : input.DeclarativeLocalizedRerootChildren cursor childrenRight)
    (nonemptyRight : childrenRight ≠ []) : False := by
  have childrenEq := localizedRerootChildren_unique input cursor frameLeft frameRight
  exact nonemptyRight (childrenEq ▸ emptyLeft)

/-- A branch derivation cannot share its cursor with a terminal derivation. -/
private theorem false_of_branch_terminal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {childrenLeft childrenRight : List (input.LocalizedRerootCursor carrierFuel)}
    (frameLeft : input.DeclarativeLocalizedRerootChildren cursor childrenLeft)
    (nonemptyLeft : childrenLeft ≠ [])
    (frameRight : input.DeclarativeLocalizedRerootChildren cursor childrenRight)
    (emptyRight : childrenRight = []) : False := by
  have childrenEq := localizedRerootChildren_unique input cursor frameLeft frameRight
  exact nonemptyLeft (childrenEq.symm ▸ emptyRight)

/-! ## Terminal nodes -/

/-- Two independent terminal derivations of the same cursor satisfy the population invariant. -/
private theorem rule4aTerminalRankedPopulationAgrees
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {labelLeft labelRight : Option LocalizedAuxiliaryLabel}
    (observedLeft : input.DeclarativeLocalizedDependencyLabel target view cursor labelLeft)
    (observedRight : input.DeclarativeLocalizedDependencyLabel target view cursor labelRight) :
    LocalizedRule4aRankedPopulationAgrees input
      { constitutional := input.moleculeGraph.officialRuleMajorRootKey
          cursor.occurrence.1.node true
        descriptor := [[([], localizedCumulativeRule45Priority .rule4a labelLeft)]]
        labels := [[([], labelLeft)]]
        rankedLabels := [[([], labelLeft)]] }
      { constitutional := input.moleculeGraph.officialRuleMajorRootKey
          cursor.occurrence.1.node true
        descriptor := [[([], localizedCumulativeRule45Priority .rule4a labelRight)]]
        labels := [[([], labelRight)]]
        rankedLabels := [[([], labelRight)]] } := by
  have labelEq : labelLeft = labelRight :=
    ((input.localizedDependencyLabel_eq_iff target view cursor labelLeft).mpr
        observedLeft).symm.trans
      ((input.localizedDependencyLabel_eq_iff target view cursor labelRight).mpr observedRight)
  cases labelEq
  refine ⟨rfl, ?_⟩
  intro depth rank
  cases depth with
  | zero =>
      simp only [List.getD_cons_zero]
      exact List.Perm.refl _
  | succ depth =>
      simp only [List.getD_cons_succ]
      exact List.Perm.refl []

/-! ## Branch nodes -/

/-- Two independent branch derivations of the same cursor satisfy the population invariant.  The
two physical child frames are the same list, each child is matched by `childAgrees`, and the
left descending representative is transported first to the right original child-key list and then
to the right descending representative. -/
private theorem rule4aBranchRankedPopulationAgrees
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {childrenLeft childrenRight : List (input.LocalizedRerootCursor carrierFuel)}
    {labelLeft labelRight : Option LocalizedAuxiliaryLabel}
    {childKeysLeft childKeysRight sortedLeft sortedRight :
      List input.LocalizedRerootCumulativeRule45Key}
    (frameLeft : input.DeclarativeLocalizedRerootChildren cursor childrenLeft)
    (nonemptyLeft : childrenLeft ≠ [])
    (observedLeft : input.DeclarativeLocalizedDependencyLabel target view cursor labelLeft)
    (childDerivationsLeft : input.DeclarativeLocalizedRerootCumulativeRule45KeyList
      .rule4a target view fuel childrenLeft childKeysLeft)
    (rankingLeft : sortedLeft.Perm childKeysLeft)
    (descendingLeft : input.LocalizedRerootCumulativeRule45KeysDescending sortedLeft)
    (frameRight : input.DeclarativeLocalizedRerootChildren cursor childrenRight)
    (nonemptyRight : childrenRight ≠ [])
    (observedRight : input.DeclarativeLocalizedDependencyLabel target view cursor labelRight)
    (childDerivationsRight : input.DeclarativeLocalizedRerootCumulativeRule45KeyList
      .rule4a target view fuel childrenRight childKeysRight)
    (rankingRight : sortedRight.Perm childKeysRight)
    (descendingRight : input.LocalizedRerootCumulativeRule45KeysDescending sortedRight)
    (childAgrees : ∀ (childCursor : input.LocalizedRerootCursor carrierFuel)
        (left right : input.LocalizedRerootCumulativeRule45Key),
      input.DeclarativeLocalizedRerootCumulativeRule45Key
        .rule4a target view fuel childCursor left →
      input.DeclarativeLocalizedRerootCumulativeRule45Key
        .rule4a target view fuel childCursor right →
      LocalizedRule4aRankedPopulationAgrees input left right) :
    LocalizedRule4aRankedPopulationAgrees input
      { constitutional := OfficialRuleMajorKey.assemble
          (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false)
          (sortedLeft.map fun child => child.constitutional)
        descriptor := [[([], localizedCumulativeRule45Priority .rule4a labelLeft)]] ++
          input.mergeLocalizedRerootDescriptorChildren sortedLeft
        labels := [[([], labelLeft)]] ++
          input.mergeLocalizedRerootLabelChildren sortedLeft
        rankedLabels := [[([], labelLeft)]] ++
          input.mergeLocalizedRerootRankedLabelChildren sortedLeft }
      { constitutional := OfficialRuleMajorKey.assemble
          (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false)
          (sortedRight.map fun child => child.constitutional)
        descriptor := [[([], localizedCumulativeRule45Priority .rule4a labelRight)]] ++
          input.mergeLocalizedRerootDescriptorChildren sortedRight
        labels := [[([], labelRight)]] ++
          input.mergeLocalizedRerootLabelChildren sortedRight
        rankedLabels := [[([], labelRight)]] ++
          input.mergeLocalizedRerootRankedLabelChildren sortedRight } := by
  have childrenEq : childrenLeft = childrenRight :=
    localizedRerootChildren_unique input cursor frameLeft frameRight
  cases childrenEq
  have labelEq : labelLeft = labelRight :=
    ((input.localizedDependencyLabel_eq_iff target view cursor labelLeft).mpr
        observedLeft).symm.trans
      ((input.localizedDependencyLabel_eq_iff target view cursor labelRight).mpr observedRight)
  cases labelEq
  have keyAligned :
      List.Forall₂
        (fun left right => LocalizedRule4aRankedPopulationAgrees input left right)
        childKeysLeft childKeysRight :=
    declarativeKeyList_forall₂_agrees input target view childAgrees
      childrenLeft childKeysLeft childKeysRight childDerivationsLeft childDerivationsRight
  obtain ⟨middle, middleAligned, middlePermChildKeysRight⟩ :=
    List.perm_comp_forall₂
      (r := fun left right => LocalizedRule4aRankedPopulationAgrees input left right)
      rankingLeft keyAligned
  have middlePermRight : middle.Perm sortedRight :=
    middlePermChildKeysRight.trans rankingRight.symm
  have middleDescending : input.LocalizedRerootCumulativeRule45KeysDescending middle := by
    unfold LocalizedRerootCumulativeRule45KeysDescending
    have observablePairwise :
        (middle.map input.localizedRerootCumulativeRule45Observable).Pairwise
          (fun left right =>
            compareLocalizedCumulativeRule45Observable left right ≠ Ordering.lt) := by
      rw [← map_observable_eq_of_forall₂_agrees input middleAligned]
      exact input.observable_pairwise_of_descending sortedLeft descendingLeft
    rw [List.pairwise_map] at observablePairwise
    exact observablePairwise.imp
      (fun {left right} related => by
        rw [input.compareLocalizedRerootCumulativeRule45Keys_eq_compareObservable left right]
        exact related)
  have mergeLeftMiddle :=
    input.mergeLocalizedRerootRankedLabelChildren_population_perm_of_forall₂_population
      sortedLeft middle middleAligned
  have mergeMiddleRight :
      ∀ (depth : Nat) (rank : List Nat),
        (localizedChiralDescriptorsAtRank rank
          ((input.mergeLocalizedRerootRankedLabelChildren middle).getD depth [])).Perm
        (localizedChiralDescriptorsAtRank rank
          ((input.mergeLocalizedRerootRankedLabelChildren sortedRight).getD depth [])) :=
    input.mergeLocalizedRerootRankedLabelChildren_population_perm_of_perm_of_descending
      middlePermRight middleDescending descendingRight
  have mergeLeftRight : ∀ (depth : Nat) (rank : List Nat),
      (localizedChiralDescriptorsAtRank rank
        ((input.mergeLocalizedRerootRankedLabelChildren sortedLeft).getD depth [])).Perm
        (localizedChiralDescriptorsAtRank rank
          ((input.mergeLocalizedRerootRankedLabelChildren sortedRight).getD depth [])) :=
    fun depth rank => (mergeLeftMiddle depth rank).trans (mergeMiddleRight depth rank)
  have observationsEq : input.localizedRerootCumulativeRule45Observable
        { constitutional := OfficialRuleMajorKey.assemble
            (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false)
            (sortedLeft.map fun child => child.constitutional)
          descriptor := [[([], localizedCumulativeRule45Priority .rule4a labelLeft)]] ++
            input.mergeLocalizedRerootDescriptorChildren sortedLeft
          labels := [[([], labelLeft)]] ++
            input.mergeLocalizedRerootLabelChildren sortedLeft
          rankedLabels := [[([], labelLeft)]] ++
            input.mergeLocalizedRerootRankedLabelChildren sortedLeft } =
      input.localizedRerootCumulativeRule45Observable
        { constitutional := OfficialRuleMajorKey.assemble
            (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false)
            (sortedRight.map fun child => child.constitutional)
          descriptor := [[([], localizedCumulativeRule45Priority .rule4a labelLeft)]] ++
            input.mergeLocalizedRerootDescriptorChildren sortedRight
          labels := [[([], labelLeft)]] ++
            input.mergeLocalizedRerootLabelChildren sortedRight
          rankedLabels := [[([], labelLeft)]] ++
            input.mergeLocalizedRerootRankedLabelChildren sortedRight } :=
    input.declarative_cumulative_key_observable_unique .rule4a target view (fuel + 1) cursor
      _
      _
      (DeclarativeLocalizedRerootCumulativeRule45Key.branch
        frameLeft nonemptyLeft observedLeft childDerivationsLeft rankingLeft descendingLeft)
      (DeclarativeLocalizedRerootCumulativeRule45Key.branch
        frameRight nonemptyRight observedRight childDerivationsRight rankingRight descendingRight)
  refine ⟨observationsEq, ?_⟩
  intro depth rank
  cases depth with
  | zero =>
      simp only [List.singleton_append, List.getD_cons_zero]
      exact List.Perm.refl _
  | succ depth =>
      simp only [List.singleton_append, List.getD_cons_succ]
      exact mergeLeftRight depth rank

/-! ## Main induction -/

/-- **Rule-4a hierarchy-rank population invariance.**  Two independent declarative cumulative-key
derivations of the same Rule-4a cursor at the same fuel satisfy
`LocalizedRule4aRankedPopulationAgrees`.  The only freedom is the independent ordering of
comparator-tied children; the same-cursor terminal label is fixed by the shared dependency view. -/
theorem declarative_rule4a_rankedPopulationAgrees
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (left right : input.LocalizedRerootCumulativeRule45Key),
      input.DeclarativeLocalizedRerootCumulativeRule45Key
        .rule4a target view fuel cursor left →
      input.DeclarativeLocalizedRerootCumulativeRule45Key
        .rule4a target view fuel cursor right →
      LocalizedRule4aRankedPopulationAgrees input left right := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor left right derivedLeft derivedRight
      cases derivedLeft with
      | terminal _ _ observedLeft =>
          cases derivedRight with
          | terminal _ _ observedRight =>
              exact rule4aTerminalRankedPopulationAgrees input target view cursor
                observedLeft observedRight
  | succ fuel ih =>
      intro cursor left right derivedLeft derivedRight
      cases derivedLeft with
      | terminal frameLeft emptyLeft observedLeft =>
          cases derivedRight with
          | terminal _ _ observedRight =>
              exact rule4aTerminalRankedPopulationAgrees input target view cursor
                observedLeft observedRight
          | branch frameRight nonemptyRight observedRight childDerivationsRight
              rankingRight descendingRight =>
              exact False.elim
                (false_of_terminal_branch input frameLeft emptyLeft frameRight nonemptyRight)
      | branch frameLeft nonemptyLeft observedLeft childDerivationsLeft
          rankingLeft descendingLeft =>
          cases derivedRight with
          | terminal frameRight emptyRight observedRight =>
              exact False.elim
                (false_of_branch_terminal input frameLeft nonemptyLeft frameRight emptyRight)
          | branch frameRight nonemptyRight observedRight childDerivationsRight
              rankingRight descendingRight =>
              exact rule4aBranchRankedPopulationAgrees input target view cursor
                frameLeft nonemptyLeft observedLeft childDerivationsLeft
                rankingLeft descendingLeft
                frameRight nonemptyRight observedRight childDerivationsRight
                rankingRight descendingRight
                (fun childCursor childLeft childRight childDerivedLeft childDerivedRight =>
                  ih childCursor childLeft childRight childDerivedLeft childDerivedRight)

/-- **Rule-4a hierarchy-rank population agreement `(B)`.**  For any common fuel and cursor, two
independent Rule-4a declarative derivations have `List.Perm`-related uppercase chiral populations at
every sphere depth and hierarchy rank path.  The two derivations may choose arbitrary independent
descending tie orders; their terminal label is fixed by the shared dependency view and cursor. -/
theorem declarative_rule4a_rankedLabels_population_perm
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    {left right : input.LocalizedRerootCumulativeRule45Key}
    (leftDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor left)
    (rightDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor right) :
    ∀ (depth : Nat) (rank : List Nat),
      (localizedChiralDescriptorsAtRank rank (left.rankedLabels.getD depth [])).Perm
        (localizedChiralDescriptorsAtRank rank (right.rankedLabels.getD depth [])) :=
  (input.declarative_rule4a_rankedPopulationAgrees target view fuel cursor left right
    leftDerived rightDerived).2

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
