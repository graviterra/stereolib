import TetraStereo.OneCenter.LocalizedCumulativeCursorTransport
import TetraStereo.OneCenter.LocalizedRule4aRankedProjection
import TetraStereo.OneCenter.LocalizedRankedPopulationMerge
import TetraStereo.OneCenter.LocalizedRule4bReferenceAgreement
import Mathlib.Data.List.Perm.Basic
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Mirror transport of the Rule-4a ranked-label populations

`LocalizedCumulativeCursorTransport` transports the comparison-visible observable of the actual
cumulative builder along any cursor relation `R` whose reader law is the uppercase reflection
(`readR y = reflectUppercaseOptionalLabel (readL x)` on related cursors).  The observable omits
the `rankedLabels` field, so the P-92.5.2.1 reference selection
`localizedRule4bReferencesFromRankedLabels`, which reads that field, is not covered.

This module closes that gap for the Rule-4a stage.  Under the same four structural clauses and the
reflected reader law, two successful Rule-4a builds at related cursors satisfy

```
RankedChiralAgrees (reflectUppercaseRankedLabels keyL.rankedLabels) keyR.rankedLabels
```

* invariant (A), the Rule-4a projection, is reflection-invariant and is transported across
  cursors by the closed observable-determined projection theorem
  `declarative_rule4a_rankedLabels_projection_eq`;
* invariant (B), the per-depth/per-rank uppercase populations, is proved here by the same fuel
  induction as the observable transport: at a terminal the single root label is reflected, at a
  branch the left descending sibling list is aligned pointwise with a descending permutation of
  the right one (`List.perm_comp_forall₂`), the pointwise merge transport carries the swapped
  populations, and the descending-permutation merge transport reorders to the right
  representative.

The consequence for the selector is `references_reflect_of_mirror_related`: the right selection
is the canonical reflection `reflectSelectedRule4bReferences` of the left selection.  In
particular a tied `[R, S]` selection stays `[R, S]`.

No key equality, label equality or desired selection is assumed; the only inputs are the cursor
relation, its structural clauses, the reflected reader law and the two successful builds.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## List plumbing -/

/-- Option `mapM` at one cons. -/
private theorem mapM_cons_option {α β : Type*} (f : α → Option β) (head : α)
    (rest : List α) :
    (head :: rest).mapM f =
      f head >>= fun value => (rest.mapM f).map fun tail => value :: tail := by
  rw [List.mapM_cons]
  cases rest.mapM f with
  | none => rfl
  | some tail => rfl

/-- A successful Option `mapM` is exactly a pointwise successful evaluation. -/
theorem mapM_eq_some_iff_forall₂ {α β : Type*} (f : α → Option β) :
    ∀ (l : List α) (ks : List β),
      l.mapM f = some ks ↔ List.Forall₂ (fun a k => f a = some k) l ks
  | [], ks => by
      constructor
      · intro h
        simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
        subst h
        exact List.Forall₂.nil
      · intro h
        rw [List.forall₂_nil_left_iff.mp h]
        simp only [List.mapM_nil, Option.pure_def]
  | a :: l, ks => by
      rw [mapM_cons_option f a l]
      cases h : f a with
      | none =>
          change (none : Option (List β)) = some ks ↔ _
          constructor
          · intro h'
            cases h'
          · intro h'
            rcases List.forall₂_cons_left_iff.mp h' with ⟨k, ks', hk, _, _⟩
            rw [h] at hk
            cases hk
      | some b =>
          change (l.mapM f).map (fun tail => b :: tail) = some ks ↔ _
          constructor
          · intro h'
            rcases Option.map_eq_some_iff.mp h' with ⟨tail, htail, rfl⟩
            exact List.Forall₂.cons h ((mapM_eq_some_iff_forall₂ f l tail).mp htail)
          · intro h'
            rcases List.forall₂_cons_left_iff.mp h' with ⟨k, ks', hk, htail, rfl⟩
            rw [h] at hk
            cases hk
            rw [(mapM_eq_some_iff_forall₂ f l ks').mpr htail]
            rfl

/-- Permuting the input of a successful Option `mapM` permutes its output. -/
theorem exists_mapM_some_of_perm {α β : Type*} (f : α → Option β) {l l' : List α}
    (permutation : l.Perm l') {ks : List β} (computed : l.mapM f = some ks) :
    ∃ ks', l'.mapM f = some ks' ∧ ks.Perm ks' := by
  obtain ⟨ks', aligned, perm⟩ :=
    List.perm_comp_forall₂ permutation.symm ((mapM_eq_some_iff_forall₂ f l ks).mp computed)
  exact ⟨ks', (mapM_eq_some_iff_forall₂ f l' ks').mpr aligned, perm.symm⟩

/-- Pointwise related inputs with pointwise related successful evaluations give pointwise related
successful `mapM` outputs. -/
theorem forall₂_of_mapM_some {α β γ : Type*} {f : α → Option β} {g : α → Option γ}
    {R : α → α → Prop} {S : β → γ → Prop}
    (pointwise : ∀ a b, R a b → ∀ ka kb, f a = some ka → g b = some kb → S ka kb) :
    ∀ {l m : List α} {ks : List β} {ks' : List γ}, List.Forall₂ R l m →
      l.mapM f = some ks → m.mapM g = some ks' → List.Forall₂ S ks ks' := by
  intro l m ks ks' related computedL computedR
  have alignedL := (mapM_eq_some_iff_forall₂ f l ks).mp computedL
  have alignedR := (mapM_eq_some_iff_forall₂ g m ks').mp computedR
  clear computedL computedR
  induction related generalizing ks ks' with
  | nil =>
      cases alignedL
      cases alignedR
      exact List.Forall₂.nil
  | cons hab _ ih =>
      rcases List.forall₂_cons_left_iff.mp alignedL with ⟨ka, kas, hka, hkas, rfl⟩
      rcases List.forall₂_cons_left_iff.mp alignedR with ⟨kb, kbs, hkb, hkbs, rfl⟩
      exact List.Forall₂.cons (pointwise _ _ hab ka kb hka hkb) (ih hkas hkbs)

/-- Two pointwise relations sharing their left list compose into a relation on the right lists. -/
theorem forall₂_comp_left {α β γ : Type*} {P : α → β → Prop} {Q : α → γ → Prop} :
    ∀ {l : List α} {rs : List β} {rs' : List γ}, List.Forall₂ P l rs → List.Forall₂ Q l rs' →
      List.Forall₂ (fun r r' => ∃ a, P a r ∧ Q a r') rs rs' := by
  intro l rs rs' h₁ h₂
  induction h₁ generalizing rs' with
  | nil =>
      cases h₂
      exact List.Forall₂.nil
  | cons hp _ ih =>
      rcases List.forall₂_cons_left_iff.mp h₂ with ⟨r', rest', hq, hrest, rfl⟩
      exact List.Forall₂.cons ⟨_, hp, hq⟩ (ih hrest)

/-- Pointwise `Perm`-aligned `flatMap` chunks produce `Perm`-related concatenations. -/
theorem flatMap_perm_of_forall₂ {α β γ : Type*} (f : α → List γ) (g : β → List γ) :
    ∀ {left : List α} {right : List β},
      List.Forall₂ (fun a b => (f a).Perm (g b)) left right →
        (left.flatMap f).Perm (right.flatMap g) := by
  intro left right aligned
  induction aligned with
  | nil => exact List.Perm.refl []
  | cons h _ ih =>
      rw [List.flatMap_cons, List.flatMap_cons]
      exact h.append ih

/-! ## Reflection of ranked-label stacks -/

theorem getD_reflectUppercaseRankedLabels
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    ∀ depth : Nat, (reflectUppercaseRankedLabels layers).getD depth [] =
      (layers.getD depth []).map reflectUppercaseRankedEntry := by
  induction layers with
  | nil =>
      intro depth
      simp [reflectUppercaseRankedLabels]
  | cons layer rest ih =>
      intro depth
      cases depth with
      | zero => rfl
      | succ depth => exact ih depth

/-- The population of a reflected stack at any depth and rank is the swapped population. -/
theorem localizedChiralDescriptorsAtRank_reflect_getD (rank : List Nat)
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (depth : Nat) :
    localizedChiralDescriptorsAtRank rank
        ((reflectUppercaseRankedLabels layers).getD depth []) =
      (localizedChiralDescriptorsAtRank rank (layers.getD depth [])).map RS.swap := by
  rw [getD_reflectUppercaseRankedLabels, localizedChiralDescriptorsAtRank_reflectUppercase]

/-- The Rule-4a projection ignores the uppercase reflection. -/
theorem projectRule4aLayer_map_reflectUppercaseRankedEntry
    (layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :
    projectRule4aLayer (layer.map reflectUppercaseRankedEntry) = projectRule4aLayer layer := by
  unfold projectRule4aLayer
  rw [List.map_map]
  apply List.map_congr_left
  intro entry _
  rcases entry with ⟨address, label⟩
  simp [Function.comp, projectRule4aEntry, reflectUppercaseRankedEntry,
    localizedCumulativeRule45Priority]

/-- Invariant (A) is reflection-invariant. -/
theorem rankedLabelProjection_reflectUppercaseRankedLabels
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    rankedLabelProjection (reflectUppercaseRankedLabels layers) =
      rankedLabelProjection layers := by
  unfold rankedLabelProjection reflectUppercaseRankedLabels
  rw [List.map_map]
  apply List.map_congr_left
  intro layer _
  exact projectRule4aLayer_map_reflectUppercaseRankedEntry layer

/-! ## Swapped population transport through the ranked merge -/

/-- Pointwise swapped-population transport through the hierarchy-rank merge: the mirror image of
`mergeLocalizedRerootRankedLabelChildren_population_perm_of_forall₂`. -/
theorem mergeLocalizedRerootRankedLabelChildren_population_swap_perm_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    (R : input.LocalizedRerootCumulativeRule45Key →
      input.LocalizedRerootCumulativeRule45Key → Prop)
    (observable_eq : ∀ left right, R left right →
      input.localizedRerootCumulativeRule45Observable left =
        input.localizedRerootCumulativeRule45Observable right)
    (population_perm : ∀ left right, R left right →
      ∀ (depth : Nat) (rank : List Nat),
        ((localizedChiralDescriptorsAtRank rank
            (left.rankedLabels.getD depth [])).map RS.swap).Perm
          (localizedChiralDescriptorsAtRank rank
            (right.rankedLabels.getD depth [])))
    (left right : List input.LocalizedRerootCumulativeRule45Key)
    (aligned : List.Forall₂ R left right) :
    ∀ (depth : Nat) (rank : List Nat),
      ((localizedChiralDescriptorsAtRank rank
          ((input.mergeLocalizedRerootRankedLabelChildren left).getD depth [])).map
            RS.swap).Perm
        (localizedChiralDescriptorsAtRank rank
          ((input.mergeLocalizedRerootRankedLabelChildren right).getD depth [])) := by
  intro depth rank
  rw [input.getD_mergeLocalizedRerootRankedLabelChildren left depth,
    input.getD_mergeLocalizedRerootRankedLabelChildren right depth,
    localizedChiralDescriptorsAtRank_flatMap,
    localizedChiralDescriptorsAtRank_flatMap,
    List.map_flatMap]
  refine flatMap_perm_of_forall₂ _ _ ?_
  refine List.Forall₂.imp (fun first second related => ?_)
    (input.localizedRerootRankedChildren_forall₂_of_relation R observable_eq
      left right aligned)
  rcases related with ⟨rankEq, rel⟩
  show ((localizedChiralDescriptorsAtRank rank
      (OfficialRuleMajorKey.prefixLayer first.2
        (first.1.rankedLabels.getD depth []))).map RS.swap).Perm
    (localizedChiralDescriptorsAtRank rank
      (OfficialRuleMajorKey.prefixLayer second.2
        (second.1.rankedLabels.getD depth [])))
  cases rank with
  | nil =>
      rw [localizedChiralDescriptorsAtRank_prefixLayer_nil,
        localizedChiralDescriptorsAtRank_prefixLayer_nil]
      exact List.Perm.refl []
  | cons head tail =>
      rw [localizedChiralDescriptorsAtRank_prefixLayer_cons,
        localizedChiralDescriptorsAtRank_prefixLayer_cons]
      by_cases sameRank : first.2 = head
      · rw [if_pos sameRank, if_pos (rankEq ▸ sameRank)]
        exact population_perm first.1 second.1 rel depth tail
      · rw [if_neg sameRank, if_neg (fun h => sameRank (rankEq ▸ h))]
        exact List.Perm.refl []

/-! ## The branch step -/

/-- The pointwise relation carried through the fuel induction: equal observables and swapped
`Perm`-related uppercase populations at every depth and rank path. -/
def MirrorPopulationRelated (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key) : Prop :=
  input.localizedRerootCumulativeRule45Observable left =
      input.localizedRerootCumulativeRule45Observable right ∧
    ∀ (depth : Nat) (rank : List Nat),
      ((localizedChiralDescriptorsAtRank rank (left.rankedLabels.getD depth [])).map
          RS.swap).Perm
        (localizedChiralDescriptorsAtRank rank (right.rankedLabels.getD depth []))

private theorem map_observable_eq_of_forall₂_related (input : CertifiedLocalizedCIPInput)
    {left right : List input.LocalizedRerootCumulativeRule45Key}
    (aligned : List.Forall₂ (MirrorPopulationRelated input) left right) :
    left.map input.localizedRerootCumulativeRule45Observable =
      right.map input.localizedRerootCumulativeRule45Observable := by
  induction aligned with
  | nil => rfl
  | cons head _ ih => simp only [List.map_cons, head.1, ih]

/-- Reflecting the single root label swaps the root population. -/
private theorem terminal_population_swap (label : Option LocalizedAuxiliaryLabel)
    (rank : List Nat) :
    ((localizedChiralDescriptorsAtRank rank [(([] : List Nat), label)]).map RS.swap).Perm
      (localizedChiralDescriptorsAtRank rank
        [(([] : List Nat), reflectUppercaseOptionalLabel label)]) := by
  rw [show [(([] : List Nat), reflectUppercaseOptionalLabel label)] =
      [(([] : List Nat), label)].map reflectUppercaseRankedEntry from rfl,
    localizedChiralDescriptorsAtRank_reflectUppercase]

private theorem singleton_population_swap (label : Option LocalizedAuxiliaryLabel)
    (depth : Nat) (rank : List Nat) :
    ((localizedChiralDescriptorsAtRank rank
        (([[(([] : List Nat), label)]] :
          List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))).getD depth [])).map
          RS.swap).Perm
      (localizedChiralDescriptorsAtRank rank
        (([[(([] : List Nat), reflectUppercaseOptionalLabel label)]] :
          List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))).getD depth [])) := by
  cases depth with
  | zero => exact terminal_population_swap label rank
  | succ depth => simp [localizedChiralDescriptorsAtRank_eq_filterMap]

/-- Branch step: the left sorted sibling list is aligned with a descending permutation of the right
sorted sibling list, then reordered. -/
private theorem branch_population_swap (input : CertifiedLocalizedCIPInput)
    {leftKeys rightKeys relatedKeys : List input.LocalizedRerootCumulativeRule45Key}
    (permutation : leftKeys.Perm relatedKeys)
    (aligned : List.Forall₂ (MirrorPopulationRelated input) relatedKeys rightKeys)
    (depth : Nat) (rank : List Nat) :
    ((localizedChiralDescriptorsAtRank rank
        ((input.mergeLocalizedRerootRankedLabelChildren
          (input.sortLocalizedRerootCumulativeRule45Keys leftKeys)).getD depth [])).map
          RS.swap).Perm
      (localizedChiralDescriptorsAtRank rank
        ((input.mergeLocalizedRerootRankedLabelChildren
          (input.sortLocalizedRerootCumulativeRule45Keys rightKeys)).getD depth [])) := by
  have sortedLPerm : (input.sortLocalizedRerootCumulativeRule45Keys leftKeys).Perm relatedKeys :=
    (input.sortLocalizedRerootCumulativeRule45Keys_perm leftKeys).trans permutation
  obtain ⟨middle, middleAligned, middlePermRight⟩ := List.perm_comp_forall₂ sortedLPerm aligned
  have middlePermSorted : middle.Perm (input.sortLocalizedRerootCumulativeRule45Keys rightKeys) :=
    middlePermRight.trans (input.sortLocalizedRerootCumulativeRule45Keys_perm rightKeys).symm
  have middleDescending : input.LocalizedRerootCumulativeRule45KeysDescending middle := by
    unfold LocalizedRerootCumulativeRule45KeysDescending
    have observablePairwise :
        (middle.map input.localizedRerootCumulativeRule45Observable).Pairwise
          (fun left right =>
            compareLocalizedCumulativeRule45Observable left right ≠ Ordering.lt) := by
      rw [← map_observable_eq_of_forall₂_related input middleAligned]
      exact input.observable_pairwise_of_descending _
        (input.sortLocalizedRerootCumulativeRule45Keys_descending leftKeys)
    rw [List.pairwise_map] at observablePairwise
    exact observablePairwise.imp
      (fun {left right} related => by
        rw [input.compareLocalizedRerootCumulativeRule45Keys_eq_compareObservable left right]
        exact related)
  have leftMiddle :=
    input.mergeLocalizedRerootRankedLabelChildren_population_swap_perm_of_forall₂
      (MirrorPopulationRelated input) (fun _ _ h => h.1) (fun _ _ h => h.2)
      _ middle middleAligned depth rank
  have middleRight :=
    input.mergeLocalizedRerootRankedLabelChildren_population_perm_of_perm_of_descending
      middlePermSorted middleDescending
      (input.sortLocalizedRerootCumulativeRule45Keys_descending rightKeys) depth rank
  exact leftMiddle.trans middleRight

private theorem branch_population_swap_full (input : CertifiedLocalizedCIPInput)
    {leftKeys rightKeys relatedKeys : List input.LocalizedRerootCumulativeRule45Key}
    (permutation : leftKeys.Perm relatedKeys)
    (aligned : List.Forall₂ (MirrorPopulationRelated input) relatedKeys rightKeys)
    (label : Option LocalizedAuxiliaryLabel) (depth : Nat) (rank : List Nat) :
    ((localizedChiralDescriptorsAtRank rank
        (([[(([] : List Nat), label)]] ++
          input.mergeLocalizedRerootRankedLabelChildren
            (input.sortLocalizedRerootCumulativeRule45Keys leftKeys)).getD depth [])).map
          RS.swap).Perm
      (localizedChiralDescriptorsAtRank rank
        (([[(([] : List Nat), reflectUppercaseOptionalLabel label)]] ++
          input.mergeLocalizedRerootRankedLabelChildren
            (input.sortLocalizedRerootCumulativeRule45Keys rightKeys)).getD depth [])) := by
  cases depth with
  | zero =>
      simp only [List.singleton_append, List.getD_cons_zero]
      exact terminal_population_swap label rank
  | succ depth =>
      simp only [List.singleton_append, List.getD_cons_succ]
      exact branch_population_swap input permutation aligned depth rank

/-! ## Unfolding equations for the actual builder -/

private theorem buildWithRead_zero_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read 0 cursor =
      (if input.executableLocalizedRerootChildren cursor = [] then
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage (read cursor))]]
            labels := [[([], read cursor)]]
            rankedLabels := [[([], read cursor)]] }
      else none) := by
  unfold buildLocalizedRerootCumulativeRule45KeyWithRead?
  rw [input.localizedRerootChildren?_eq_some_executable]
  rfl

private theorem buildWithRead_succ_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read (Nat.succ fuel) cursor =
      (if input.executableLocalizedRerootChildren cursor = [] then
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage (read cursor))]]
            labels := [[([], read cursor)]]
            rankedLabels := [[([], read cursor)]] }
      else
        (input.executableLocalizedRerootChildren cursor).mapM
            (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel) >>=
          fun childKeys =>
            let sorted := input.sortLocalizedRerootCumulativeRule45Keys childKeys
            some
              { constitutional := OfficialRuleMajorKey.assemble
                  (input.moleculeGraph.officialRuleMajorRootKey
                    cursor.occurrence.1.node false)
                  (sorted.map fun child => child.constitutional)
                descriptor := [[([], localizedCumulativeRule45Priority stage (read cursor))]] ++
                  input.mergeLocalizedRerootDescriptorChildren sorted
                labels := [[([], read cursor)]] ++
                  input.mergeLocalizedRerootLabelChildren sorted
                rankedLabels := [[([], read cursor)]] ++
                  input.mergeLocalizedRerootRankedLabelChildren sorted }) := by
  unfold buildLocalizedRerootCumulativeRule45KeyWithRead?
  rw [input.localizedRerootChildren?_eq_some_executable]
  rfl

private theorem perm_forall₂_nil_iff {α : Type*} {R : α → α → Prop}
    {left middle right : List α}
    (permutation : left.Perm middle) (related : List.Forall₂ R middle right) :
    left = [] ↔ right = [] := by
  constructor
  · intro leftEmpty
    cases leftEmpty
    have middleEmpty : middle = [] := permutation.symm.eq_nil
    cases middleEmpty
    exact List.forall₂_nil_left_iff.mp related
  · intro rightEmpty
    cases rightEmpty
    have middleEmpty : middle = [] := List.forall₂_nil_right_iff.mp related
    cases middleEmpty
    exact permutation.eq_nil

/-! ## The mirror population transport -/

/-- **Swapped population transport for the actual Rule-4a builder.**  Under the four structural
clauses of the cursor relation `R` and the reflected reader law, two successful Rule-4a builds at
related cursors have, at every sphere depth and hierarchy rank path, uppercase populations related
by `List.Perm` after swapping the left one. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_rule4a_population_swap_perm_of_related
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (R : input.LocalizedRerootCursor carrierFuel →
      input.LocalizedRerootCursor carrierFuel → Prop)
    (atomLabel : ∀ x y, R x y →
      input.moleculeGraph.officialNodeAtomLabel x.occurrence.1.node =
        input.moleculeGraph.officialNodeAtomLabel y.occurrence.1.node)
    (rootDistance : ∀ x y, R x y →
      x.occurrence.1.node.rule1bRootDistance =
        y.occurrence.1.node.rule1bRootDistance)
    (children : ∀ x y, R x y →
      ∃ related,
        (input.executableLocalizedRerootChildren x).Perm related ∧
          List.Forall₂ R related (input.executableLocalizedRerootChildren y))
    (readerReflect : ∀ x y, R x y →
      readR y = reflectUppercaseOptionalLabel (readL x)) :
    ∀ (fuel : Nat) (x y : input.LocalizedRerootCursor carrierFuel), R x y →
      ∀ {keyL keyR : input.LocalizedRerootCumulativeRule45Key},
        input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a readL fuel x =
            some keyL →
          input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a readR fuel y =
              some keyR →
            ∀ (depth : Nat) (rank : List Nat),
              ((localizedChiralDescriptorsAtRank rank
                  (keyL.rankedLabels.getD depth [])).map RS.swap).Perm
                (localizedChiralDescriptorsAtRank rank
                  (keyR.rankedLabels.getD depth [])) := by
  have observable : ∀ (fuel : Nat) (x y : input.LocalizedRerootCursor carrierFuel), R x y →
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a readL fuel x).map
          input.localizedRerootCumulativeRule45Observable =
        (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a readR fuel y).map
          input.localizedRerootCumulativeRule45Observable :=
    input.buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_related_reflectUppercase
      .rule4a readL readR R atomLabel rootDistance children readerReflect
  intro fuel
  induction fuel with
  | zero =>
      intro x y related keyL keyR builtL builtR depth rank
      rw [buildWithRead_zero_eq] at builtL builtR
      rcases children x y related with ⟨relatedChildren, permutation, forall₂⟩
      have terminalIff := perm_forall₂_nil_iff permutation forall₂
      by_cases emptyLeft : input.executableLocalizedRerootChildren x = []
      · rw [if_pos emptyLeft] at builtL
        rw [if_pos (terminalIff.mp emptyLeft)] at builtR
        cases Option.some.inj builtL
        cases Option.some.inj builtR
        rw [readerReflect x y related]
        exact singleton_population_swap (readL x) depth rank
      · rw [if_neg emptyLeft] at builtL
        cases builtL
  | succ fuel ih =>
      intro x y related keyL keyR builtL builtR depth rank
      rw [buildWithRead_succ_eq] at builtL builtR
      rcases children x y related with ⟨relatedChildren, permutation, forall₂⟩
      have terminalIff := perm_forall₂_nil_iff permutation forall₂
      by_cases emptyLeft : input.executableLocalizedRerootChildren x = []
      · rw [if_pos emptyLeft] at builtL
        rw [if_pos (terminalIff.mp emptyLeft)] at builtR
        cases Option.some.inj builtL
        cases Option.some.inj builtR
        rw [readerReflect x y related]
        exact singleton_population_swap (readL x) depth rank
      · have nonemptyRight : input.executableLocalizedRerootChildren y ≠ [] :=
          fun emptyRight => emptyLeft (terminalIff.mpr emptyRight)
        rw [if_neg emptyLeft] at builtL
        rw [if_neg nonemptyRight] at builtR
        cases leftMap : (input.executableLocalizedRerootChildren x).mapM
            (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a readL fuel) with
        | none =>
            rw [leftMap] at builtL
            cases builtL
        | some leftKeys =>
            cases rightMap : (input.executableLocalizedRerootChildren y).mapM
                (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a readR fuel) with
            | none =>
                rw [rightMap] at builtR
                cases builtR
            | some rightKeys =>
                rw [leftMap] at builtL
                rw [rightMap] at builtR
                cases Option.some.inj builtL
                cases Option.some.inj builtR
                obtain ⟨relatedKeys, relatedMap, keysPerm⟩ :=
                  exists_mapM_some_of_perm _ permutation leftMap
                have aligned : List.Forall₂ (MirrorPopulationRelated input)
                    relatedKeys rightKeys :=
                  forall₂_of_mapM_some
                    (fun x' y' rel ka kb hka hkb =>
                      ⟨by
                        have h := observable fuel x' y' rel
                        rw [hka, hkb] at h
                        simpa using h,
                        ih x' y' rel hka hkb⟩)
                    forall₂ relatedMap rightMap
                rw [readerReflect x y related]
                exact branch_population_swap_full input keysPerm aligned (readL x) depth rank

/-! ## Production corollaries: ranked chiral agreement and selector covariance -/

/-- **Mirror ranked chiral agreement for production Rule-4a builds.**  Under the structural clauses
of `R` and the reflected production reader law, the reflected left `rankedLabels` and the right
`rankedLabels` satisfy `RankedChiralAgrees`.  Invariant (A) is the closed observable-determined
projection; invariant (B) is the swapped population transport above. -/
theorem rankedChiralAgrees_reflect_of_mirror_related
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (R : input.LocalizedRerootCursor carrierFuel →
      input.LocalizedRerootCursor carrierFuel → Prop)
    (atomLabel : ∀ x y, R x y →
      input.moleculeGraph.officialNodeAtomLabel x.occurrence.1.node =
        input.moleculeGraph.officialNodeAtomLabel y.occurrence.1.node)
    (rootDistance : ∀ x y, R x y →
      x.occurrence.1.node.rule1bRootDistance =
        y.occurrence.1.node.rule1bRootDistance)
    (children : ∀ x y, R x y →
      ∃ related,
        (input.executableLocalizedRerootChildren x).Perm related ∧
          List.Forall₂ R related (input.executableLocalizedRerootChildren y))
    (readerReflect : ∀ x y, R x y →
      input.localizedDependencyLabel target view y =
        reflectUppercaseOptionalLabel (input.localizedDependencyLabel target view x))
    (fuel : Nat) {x y : input.LocalizedRerootCursor carrierFuel} (related : R x y)
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (builtL : input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel x =
      some keyL)
    (builtR : input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel y =
      some keyR) :
    RankedChiralAgrees (reflectUppercaseRankedLabels keyL.rankedLabels) keyR.rankedLabels := by
  have builtL' : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      (fun cursor => input.localizedDependencyLabel target view cursor) fuel x = some keyL := by
    rw [input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel]
    exact builtL
  have builtR' : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      (fun cursor => input.localizedDependencyLabel target view cursor) fuel y = some keyR := by
    rw [input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel]
    exact builtR
  have observableEq : input.localizedRerootCumulativeRule45Observable keyL =
      input.localizedRerootCumulativeRule45Observable keyR := by
    have h :=
      input.buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_related_reflectUppercase
        .rule4a (fun cursor => input.localizedDependencyLabel target view cursor)
        (fun cursor => input.localizedDependencyLabel target view cursor)
        R atomLabel rootDistance children readerReflect fuel x y related
    have builtR'' : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        (reflectLocalizedCumulativeRule45Stage .rule4a)
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel y = some keyR :=
      builtR'
    rw [builtL', builtR''] at h
    simpa using h
  refine ⟨?_, ?_⟩
  · rw [rankedLabelProjection_reflectUppercaseRankedLabels]
    exact input.declarative_rule4a_rankedLabels_projection_eq target view fuel x y keyL keyR
      (input.buildLocalizedRerootCumulativeRule45Key?_sound .rule4a target view fuel x keyL builtL)
      (input.buildLocalizedRerootCumulativeRule45Key?_sound .rule4a target view fuel y keyR builtR)
      observableEq
  · intro depth rank
    rw [localizedChiralDescriptorsAtRank_reflect_getD]
    exact input.buildLocalizedRerootCumulativeRule45KeyWithRead?_rule4a_population_swap_perm_of_related
      (fun cursor => input.localizedDependencyLabel target view cursor)
      (fun cursor => input.localizedDependencyLabel target view cursor)
      R atomLabel rootDistance children readerReflect fuel x y related builtL' builtR' depth rank

/-- **Selector covariance under reflection.**  The right production selection is the canonical
reflection of the left one: a unique reference is swapped, an empty or tied `[R, S]` selection is
unchanged. -/
theorem references_reflect_of_mirror_related
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (R : input.LocalizedRerootCursor carrierFuel →
      input.LocalizedRerootCursor carrierFuel → Prop)
    (atomLabel : ∀ x y, R x y →
      input.moleculeGraph.officialNodeAtomLabel x.occurrence.1.node =
        input.moleculeGraph.officialNodeAtomLabel y.occurrence.1.node)
    (rootDistance : ∀ x y, R x y →
      x.occurrence.1.node.rule1bRootDistance =
        y.occurrence.1.node.rule1bRootDistance)
    (children : ∀ x y, R x y →
      ∃ related,
        (input.executableLocalizedRerootChildren x).Perm related ∧
          List.Forall₂ R related (input.executableLocalizedRerootChildren y))
    (readerReflect : ∀ x y, R x y →
      input.localizedDependencyLabel target view y =
        reflectUppercaseOptionalLabel (input.localizedDependencyLabel target view x))
    (fuel : Nat) {x y : input.LocalizedRerootCursor carrierFuel} (related : R x y)
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (builtL : input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel x =
      some keyL)
    (builtR : input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel y =
      some keyR) :
    localizedRule4bReferencesFromRankedLabels keyR.rankedLabels =
      reflectSelectedRule4bReferences
        (localizedRule4bReferencesFromRankedLabels keyL.rankedLabels) := by
  rw [← localizedRule4bReferencesFromRankedLabels_reflectUppercase]
  exact (localizedRule4bReferencesFromRankedLabels_eq_of_rankedChiralAgrees'
    (input.rankedChiralAgrees_reflect_of_mirror_related target view R atomLabel rootDistance
      children readerReflect fuel related builtL builtR)).symm

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mapM_eq_some_iff_forall₂
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mergeLocalizedRerootRankedLabelChildren_population_swap_perm_of_forall₂
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_rule4a_population_swap_perm_of_related
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rankedChiralAgrees_reflect_of_mirror_related
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.references_reflect_of_mirror_related
