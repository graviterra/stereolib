import TetraStereo.OneCenter.LocalizedRule4bPopulationInvariance
import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder

set_option autoImplicit false

/-!
# Rule-4a projection transport through ranked cumulative-key merging

`mergeLocalizedRerootRankedLabelChildren` merges the exact `rankedLabels` stacks of a descending
sibling list beneath hierarchy-equivalence ranks.  A downstream Rule-4a projection therefore needs
to know that this merge, after projection, is a function of

* the comparison-visible observable of every child, and
* the Rule-4a projection of every child's whole `rankedLabels` stack.

This module establishes exactly that transport.  No sortedness hypothesis is used: the child lists
need only be *pointwise aligned*.

The proof has three steps.

1. Adjacent comparison outcomes are transported through
   `compareLocalizedRerootCumulativeRule45Keys_eq_compareObservable`.  This is isolated once as a
   *generic* relation transport: any relation `R` refining observable equality carries through the
   rank assignment.  The concrete observable and projected-label instances are corollaries, so
   downstream consumers (for example one using a per-rank population permutation relation) can
   reuse the same induction instead of duplicating it.
2. The single-layer Rule-4a projection commutes with `OfficialRuleMajorKey.prefixLayer`
   (`projectRule4aLayer_prefixLayer`), hence it commutes with the `flatMap` merge.
3. The merged layer count is the `foldl max` of the children's `rankedLabels` lengths, so equal
   projected stacks give equal counts and the two `List.range` collapses agree.

The main public statement is
`projectRule4aLabelLayers_mergeLocalizedRerootRankedLabelChildren_eq_of_map_eq`; a pointwise
`List.Forall₂` form is also provided.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## The whole-stack Rule-4a projection -/

/-- Apply the Rule-4a single-layer projection to every layer of a whole exact-label stack. -/
def projectRule4aLabelLayers
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    List (List (OfficialSparseEntry (List Nat))) :=
  layers.map projectRule4aLayer

/-- The Rule-4a projection of one layer preserves its length. -/
theorem length_projectRule4aLayer
    (layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :
    (projectRule4aLayer layer).length = layer.length := by
  simp [projectRule4aLayer]

/-- The whole-stack Rule-4a projection preserves the number of layers. -/
theorem length_projectRule4aLabelLayers
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    (projectRule4aLabelLayers layers).length = layers.length := by
  simp [projectRule4aLabelLayers]

/-- Extracting a layer and then projecting agrees with projecting the whole stack and then
extracting the layer (with the empty layer as default). -/
theorem projectRule4aLayer_getD
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    ∀ depth : Nat,
      projectRule4aLayer (layers.getD depth []) =
        (projectRule4aLabelLayers layers).getD depth [] := by
  induction layers with
  | nil =>
      intro depth
      rfl
  | cons layer layers ih =>
      intro depth
      cases depth with
      | zero => rfl
      | succ depth => exact ih depth

/-- Equal projected stacks give equal projected layers at every depth. -/
theorem projectRule4aLayer_getD_eq
    (left right : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (depth : Nat)
    (equal : projectRule4aLabelLayers left = projectRule4aLabelLayers right) :
    projectRule4aLayer (left.getD depth []) =
      projectRule4aLayer (right.getD depth []) := by
  rw [projectRule4aLayer_getD left depth, projectRule4aLayer_getD right depth, equal]

/-! ## Generic list helpers -/

/-- Two pointwise-equal mapped lists are pointwise related by equality of the mapped values. -/
private theorem forall₂_of_map_eq_map {α β : Type*} (f : α → β) :
    ∀ {left right : List α}, left.map f = right.map f →
      List.Forall₂ (fun left right => f left = f right) left right
  | [], [], _ => List.Forall₂.nil
  | [], _ :: _, equal => by cases equal
  | _ :: _, [], equal => by cases equal
  | head :: tail, other :: rest, equal => by
      simp only [List.map_cons, List.cons.injEq] at equal
      exact List.Forall₂.cons equal.1 (forall₂_of_map_eq_map f equal.2)

/-- Simultaneous pointwise equality of two mapped lists gives a single `Forall₂` carrying both
mapped equalities. -/
private theorem forall₂_and_of_map_eq_map {α β γ : Type*} (f : α → β) (g : α → γ) :
    ∀ {left right : List α}, left.map f = right.map f → left.map g = right.map g →
      List.Forall₂ (fun left right => f left = f right ∧ g left = g right) left right
  | [], [], _, _ => List.Forall₂.nil
  | [], _ :: _, equalF, _ => by cases equalF
  | _ :: _, [], equalF, _ => by cases equalF
  | head :: tail, other :: rest, equalF, equalG => by
      simp only [List.map_cons, List.cons.injEq] at equalF equalG
      exact List.Forall₂.cons ⟨equalF.1, equalG.1⟩
        (forall₂_and_of_map_eq_map f g equalF.2 equalG.2)

/-- A pointwise-`snd`-equal aligned list pair has equal `snd` sequences. -/
private theorem map_snd_eq_of_forall₂_snd_eq {α β : Type*} {R : α × β → α × β → Prop} :
    ∀ {left right : List (α × β)},
      List.Forall₂ (fun left right => left.2 = right.2 ∧ R left right) left right →
      left.map Prod.snd = right.map Prod.snd := by
  intro left right aligned
  induction aligned with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨rankEq, _related⟩
      simp only [List.map_cons]
      rw [rankEq, ih]

/-- `foldl` of the maximal ranked-label length only depends on pointwise lengths. -/
private theorem foldl_max_rankedLabels_length_eq_of_forall₂ {Key : Type*}
    (rankedLabels : Key → List (List
      (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    ∀ {left right : List Key},
      List.Forall₂ (fun left right =>
        (rankedLabels left).length = (rankedLabels right).length) left right →
      ∀ start : Nat,
        left.foldl (fun longest child => max longest (rankedLabels child).length) start =
          right.foldl (fun longest child => max longest (rankedLabels child).length) start := by
  intro left right aligned
  induction aligned with
  | nil => intro start; rfl
  | cons head tail ih =>
      intro start
      simp only [List.foldl_cons]
      rw [head]
      exact ih _

/-! ## Transport of the comparator along the observable projection -/

/-- Equal observables transport comparison outcomes.  This is the executable bridge from a
pointwise observable alignment to the adjacent-comparison outcomes that assign hierarchy
ranks. -/
theorem compareLocalizedRerootCumulativeRule45Keys_eq_of_observable_eq
    (input : CertifiedLocalizedCIPInput)
    {left right left' right' : input.LocalizedRerootCumulativeRule45Key}
    (leftEqual : input.localizedRerootCumulativeRule45Observable left =
      input.localizedRerootCumulativeRule45Observable left')
    (rightEqual : input.localizedRerootCumulativeRule45Observable right =
      input.localizedRerootCumulativeRule45Observable right') :
    input.compareLocalizedRerootCumulativeRule45Keys left right =
      input.compareLocalizedRerootCumulativeRule45Keys left' right' := by
  rw [input.compareLocalizedRerootCumulativeRule45Keys_eq_compareObservable left right,
    input.compareLocalizedRerootCumulativeRule45Keys_eq_compareObservable left' right',
    leftEqual, rightEqual]

/-! ## One-step unfolding lemmas for the rank assignment -/

/-- Definitional unfolding of the rank tail at a nonempty sibling list. -/
theorem localizedRerootRankedChildTail_cons
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
theorem localizedRerootRankedChildren_cons
    (input : CertifiedLocalizedCIPInput)
    (child : input.LocalizedRerootCumulativeRule45Key)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.localizedRerootRankedChildren (child :: children) =
      (child, 0) :: input.localizedRerootRankedChildTail child 0 children :=
  rfl

/-! ## Generic rank transport in an arbitrary refining relation -/

/-- **Generic rank-annotation transport.**  Let `R` be any relation on cumulative keys that refines
equality of the comparison-visible observable.  Then pointwise `R`-aligned sibling tails receive
pointwise equal ranks *and* remain related by `R` at the corresponding positions.

This is the single adjacent-comparison induction used by this module; concrete observable,
projected-label and per-rank-population consumers should instantiate `R` rather than replicate
it. -/
theorem localizedRerootRankedChildTail_forall₂_of_relation
    (input : CertifiedLocalizedCIPInput)
    (R : input.LocalizedRerootCumulativeRule45Key →
      input.LocalizedRerootCumulativeRule45Key → Prop)
    (observable_eq : ∀ left right, R left right →
      input.localizedRerootCumulativeRule45Observable left =
        input.localizedRerootCumulativeRule45Observable right) :
    ∀ (left right : List input.LocalizedRerootCumulativeRule45Key),
      List.Forall₂ R left right →
      ∀ (previousLeft previousRight : input.LocalizedRerootCumulativeRule45Key)
        (rank : Nat),
        R previousLeft previousRight →
        List.Forall₂
          (fun (left right : input.LocalizedRerootCumulativeRule45Key × Nat) =>
            left.2 = right.2 ∧ R left.1 right.1)
          (input.localizedRerootRankedChildTail previousLeft rank left)
          (input.localizedRerootRankedChildTail previousRight rank right) := by
  intro left
  induction left with
  | nil =>
      intro right aligned previousLeft previousRight rank previousRelated
      rw [List.forall₂_nil_left_iff.mp aligned]
      exact List.Forall₂.nil
  | cons child rest ih =>
      intro right aligned previousLeft previousRight rank previousRelated
      rcases List.forall₂_cons_left_iff.mp aligned with
        ⟨other, rest', headRelated, restAligned, rfl⟩
      have compareEq :
          input.compareLocalizedRerootCumulativeRule45Keys child previousLeft =
            input.compareLocalizedRerootCumulativeRule45Keys other previousRight :=
        input.compareLocalizedRerootCumulativeRule45Keys_eq_of_observable_eq
          (observable_eq child other headRelated)
          (observable_eq previousLeft previousRight previousRelated)
      have chosenRankEq :
          (if input.compareLocalizedRerootCumulativeRule45Keys child previousLeft =
              Ordering.eq then rank else rank + 1) =
            (if input.compareLocalizedRerootCumulativeRule45Keys other previousRight =
              Ordering.eq then rank else rank + 1) := by
        rw [compareEq]
      rw [localizedRerootRankedChildTail_cons, localizedRerootRankedChildTail_cons,
        chosenRankEq]
      refine List.Forall₂.cons ⟨rfl, headRelated⟩ ?_
      exact ih rest' restAligned child other _ headRelated

/-- Generic rank-annotation transport for whole sibling lists.  This is the form consumed by
downstream modules: `R` may additionally carry, for example, a per-rank population permutation. -/
theorem localizedRerootRankedChildren_forall₂_of_relation
    (input : CertifiedLocalizedCIPInput)
    (R : input.LocalizedRerootCumulativeRule45Key →
      input.LocalizedRerootCumulativeRule45Key → Prop)
    (observable_eq : ∀ left right, R left right →
      input.localizedRerootCumulativeRule45Observable left =
        input.localizedRerootCumulativeRule45Observable right) :
    ∀ (left right : List input.LocalizedRerootCumulativeRule45Key),
      List.Forall₂ R left right →
      List.Forall₂
        (fun (left right : input.LocalizedRerootCumulativeRule45Key × Nat) =>
          left.2 = right.2 ∧ R left.1 right.1)
        (input.localizedRerootRankedChildren left)
        (input.localizedRerootRankedChildren right) := by
  intro left
  induction left with
  | nil =>
      intro right aligned
      rw [List.forall₂_nil_left_iff.mp aligned]
      exact List.Forall₂.nil
  | cons child rest _ih =>
      intro right aligned
      rcases List.forall₂_cons_left_iff.mp aligned with
        ⟨other, rest', headRelated, restAligned, rfl⟩
      rw [localizedRerootRankedChildren_cons, localizedRerootRankedChildren_cons]
      refine List.Forall₂.cons ⟨rfl, headRelated⟩ ?_
      exact input.localizedRerootRankedChildTail_forall₂_of_relation R observable_eq
        rest rest' restAligned child other 0 headRelated

/-! ## Concrete rank transport -/

/-- Pointwise observable-equal sibling tails receive pointwise equal hierarchy ranks from any
aligned pair of previous keys and any equal starting rank. -/
theorem localizedRerootRankedChildTail_map_snd_eq_of_forall₂_observable
    (input : CertifiedLocalizedCIPInput) :
    ∀ (left right : List input.LocalizedRerootCumulativeRule45Key),
      List.Forall₂
        (fun left right =>
          input.localizedRerootCumulativeRule45Observable left =
            input.localizedRerootCumulativeRule45Observable right) left right →
      ∀ (previousLeft previousRight : input.LocalizedRerootCumulativeRule45Key)
        (rank : Nat),
        input.localizedRerootCumulativeRule45Observable previousLeft =
            input.localizedRerootCumulativeRule45Observable previousRight →
        (input.localizedRerootRankedChildTail previousLeft rank left).map Prod.snd =
          (input.localizedRerootRankedChildTail previousRight rank right).map Prod.snd := by
  intro left right aligned previousLeft previousRight rank previousRelated
  exact map_snd_eq_of_forall₂_snd_eq
    (input.localizedRerootRankedChildTail_forall₂_of_relation
      (fun left right =>
        input.localizedRerootCumulativeRule45Observable left =
          input.localizedRerootCumulativeRule45Observable right)
      (fun _ _ related => related)
      left right aligned previousLeft previousRight rank previousRelated)

/-- Pointwise observable-equal sibling lists receive pointwise equal hierarchy ranks. -/
theorem localizedRerootRankedChildren_map_snd_eq_of_forall₂_observable
    (input : CertifiedLocalizedCIPInput) :
    ∀ (left right : List input.LocalizedRerootCumulativeRule45Key),
      List.Forall₂
        (fun left right =>
          input.localizedRerootCumulativeRule45Observable left =
            input.localizedRerootCumulativeRule45Observable right) left right →
      (input.localizedRerootRankedChildren left).map Prod.snd =
        (input.localizedRerootRankedChildren right).map Prod.snd := by
  intro left right aligned
  exact map_snd_eq_of_forall₂_snd_eq
    (input.localizedRerootRankedChildren_forall₂_of_relation
      (fun left right =>
        input.localizedRerootCumulativeRule45Observable left =
          input.localizedRerootCumulativeRule45Observable right)
      (fun _ _ related => related)
      left right aligned)

/-- Map-equality form of ranked-child rank transport. -/
theorem localizedRerootRankedChildren_map_snd_eq_of_map_eq_observable
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootCumulativeRule45Key)
    (observables : left.map input.localizedRerootCumulativeRule45Observable =
      right.map input.localizedRerootCumulativeRule45Observable) :
    (input.localizedRerootRankedChildren left).map Prod.snd =
      (input.localizedRerootRankedChildren right).map Prod.snd :=
  input.localizedRerootRankedChildren_map_snd_eq_of_forall₂_observable left right
    (forall₂_of_map_eq_map input.localizedRerootCumulativeRule45Observable observables)

/-- Pointwise aligned sibling lists receive pointwise ranks and projected label layers that agree
at every depth.  This is the concrete instance of the generic relation transport used by the
projected merge. -/
theorem localizedRerootRankedChildren_forall₂_of_projected_rankedLabels
    (input : CertifiedLocalizedCIPInput) (depth : Nat) :
    ∀ (left right : List input.LocalizedRerootCumulativeRule45Key),
      List.Forall₂
        (fun left right =>
          input.localizedRerootCumulativeRule45Observable left =
              input.localizedRerootCumulativeRule45Observable right ∧
            projectRule4aLabelLayers left.rankedLabels =
              projectRule4aLabelLayers right.rankedLabels) left right →
      List.Forall₂
        (fun (left right : input.LocalizedRerootCumulativeRule45Key × Nat) =>
          left.2 = right.2 ∧
            projectRule4aLayer (left.1.rankedLabels.getD depth []) =
              projectRule4aLayer (right.1.rankedLabels.getD depth []))
        (input.localizedRerootRankedChildren left)
        (input.localizedRerootRankedChildren right) := by
  intro left right aligned
  exact List.Forall₂.imp
    (fun left right data =>
      ⟨data.1,
        projectRule4aLayer_getD_eq left.1.rankedLabels right.1.rankedLabels depth data.2.2⟩)
    (input.localizedRerootRankedChildren_forall₂_of_relation
      (fun left right =>
        input.localizedRerootCumulativeRule45Observable left =
            input.localizedRerootCumulativeRule45Observable right ∧
          projectRule4aLabelLayers left.rankedLabels =
            projectRule4aLabelLayers right.rankedLabels)
      (fun _ _ data => data.1)
      left right aligned)

/-! ## The projection of one merged depth -/

/-- A generic `flatMap` equality for pointwise rank- and projected-layer-aligned ranked children. -/
theorem flatMap_projectedRankedChild_eq_of_forall₂
    (input : CertifiedLocalizedCIPInput) (depth : Nat) :
    ∀ {left right : List (input.LocalizedRerootCumulativeRule45Key × Nat)},
      List.Forall₂
        (fun (left right : input.LocalizedRerootCumulativeRule45Key × Nat) =>
          left.2 = right.2 ∧
            projectRule4aLayer (left.1.rankedLabels.getD depth []) =
              projectRule4aLayer (right.1.rankedLabels.getD depth []))
        left right →
      left.flatMap
          (fun child =>
            OfficialRuleMajorKey.prefixLayer child.2
              (projectRule4aLayer (child.1.rankedLabels.getD depth []))) =
        right.flatMap
          (fun child =>
            OfficialRuleMajorKey.prefixLayer child.2
              (projectRule4aLayer (child.1.rankedLabels.getD depth []))) := by
  intro left right aligned
  induction aligned with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨rankEq, layerEq⟩
      simp only [List.flatMap_cons]
      rw [rankEq, layerEq, ih]

/-- The Rule-4a projection of one merged depth is the `flatMap` of the projected children. -/
private theorem projectRule4aLayer_flatMap_rankedLabels
    (input : CertifiedLocalizedCIPInput)
    (ranked : List (input.LocalizedRerootCumulativeRule45Key × Nat))
    (depth : Nat) :
    projectRule4aLayer
        (ranked.flatMap fun child =>
          OfficialRuleMajorKey.prefixLayer child.2
            (child.1.rankedLabels.getD depth [])) =
      ranked.flatMap fun child =>
        OfficialRuleMajorKey.prefixLayer child.2
          (projectRule4aLayer (child.1.rankedLabels.getD depth [])) := by
  unfold projectRule4aLayer
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro child _
  exact projectRule4aLayer_prefixLayer child.2 (child.1.rankedLabels.getD depth [])

/-! ## Counting merged depths -/

/-- The maximal `rankedLabels` layer count only depends on pointwise layer lengths. -/
theorem localizedRerootRankedLabelChildLayerCount_eq_of_forall₂
    (input : CertifiedLocalizedCIPInput)
    {left right : List input.LocalizedRerootCumulativeRule45Key}
    (aligned : List.Forall₂
      (fun left right => left.rankedLabels.length = right.rankedLabels.length)
      left right) :
    input.localizedRerootRankedLabelChildLayerCount left =
      input.localizedRerootRankedLabelChildLayerCount right :=
  foldl_max_rankedLabels_length_eq_of_forall₂
    (fun key : input.LocalizedRerootCumulativeRule45Key => key.rankedLabels)
    aligned 0

/-- The projected whole-stack merge is the merge of the projected per-child stacks, addressed by
the same hierarchy ranks and collapsed over the same depth range. -/
theorem projectRule4aLabelLayers_mergeLocalizedRerootRankedLabelChildren
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    projectRule4aLabelLayers (input.mergeLocalizedRerootRankedLabelChildren children) =
      (List.range (input.localizedRerootRankedLabelChildLayerCount children)).map
        (fun depth =>
          (input.localizedRerootRankedChildren children).flatMap
            (fun child =>
              OfficialRuleMajorKey.prefixLayer child.2
                (projectRule4aLayer (child.1.rankedLabels.getD depth [])))) := by
  dsimp only [mergeLocalizedRerootRankedLabelChildren, projectRule4aLabelLayers]
  rw [List.map_map]
  apply List.map_congr_left
  intro depth _
  simp only [Function.comp_apply]
  exact projectRule4aLayer_flatMap_rankedLabels input
    (input.localizedRerootRankedChildren children) depth

/-! ## Main transport theorems -/

/-- Pointwise transport of the projected ranked-label merge.  If the sibling lists are aligned on
both comparison-visible observables and projected whole `rankedLabels` stacks, then the Rule-4a
projection of the merged ranked-label layers is the same on both sides. -/
theorem projectRule4aLabelLayers_mergeLocalizedRerootRankedLabelChildren_eq_of_forall₂
    (input : CertifiedLocalizedCIPInput) :
    ∀ (left right : List input.LocalizedRerootCumulativeRule45Key),
      List.Forall₂
        (fun left right =>
          input.localizedRerootCumulativeRule45Observable left =
              input.localizedRerootCumulativeRule45Observable right ∧
            projectRule4aLabelLayers left.rankedLabels =
              projectRule4aLabelLayers right.rankedLabels) left right →
      projectRule4aLabelLayers (input.mergeLocalizedRerootRankedLabelChildren left) =
        projectRule4aLabelLayers (input.mergeLocalizedRerootRankedLabelChildren right) := by
  intro left right aligned
  have lengthsAligned :
      List.Forall₂
        (fun left right : input.LocalizedRerootCumulativeRule45Key =>
          left.rankedLabels.length = right.rankedLabels.length) left right :=
    List.Forall₂.imp
      (fun left right pairAligned => by
        rw [← length_projectRule4aLabelLayers left.rankedLabels,
          ← length_projectRule4aLabelLayers right.rankedLabels, pairAligned.2])
      aligned
  have countEq :=
    input.localizedRerootRankedLabelChildLayerCount_eq_of_forall₂ lengthsAligned
  rw [input.projectRule4aLabelLayers_mergeLocalizedRerootRankedLabelChildren left,
    input.projectRule4aLabelLayers_mergeLocalizedRerootRankedLabelChildren right, countEq]
  apply List.map_congr_left
  intro depth _
  exact input.flatMap_projectedRankedChild_eq_of_forall₂ depth
    (input.localizedRerootRankedChildren_forall₂_of_projected_rankedLabels
      depth left right aligned)

/-- **Main closed public theorem.**  If two sibling lists have the same sequence of
comparison-visible observables and the same sequence of Rule-4a projections of their whole
`rankedLabels` stacks, then the Rule-4a projection of the merged ranked-label layers agrees.  No
sortedness of either input list is assumed. -/
theorem projectRule4aLabelLayers_mergeLocalizedRerootRankedLabelChildren_eq_of_map_eq
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootCumulativeRule45Key)
    (observables : left.map input.localizedRerootCumulativeRule45Observable =
      right.map input.localizedRerootCumulativeRule45Observable)
    (rankedLabels :
      left.map (fun key => projectRule4aLabelLayers key.rankedLabels) =
        right.map (fun key => projectRule4aLabelLayers key.rankedLabels)) :
    projectRule4aLabelLayers (input.mergeLocalizedRerootRankedLabelChildren left) =
      projectRule4aLabelLayers (input.mergeLocalizedRerootRankedLabelChildren right) :=
  input.projectRule4aLabelLayers_mergeLocalizedRerootRankedLabelChildren_eq_of_forall₂
    left right
    (forall₂_and_of_map_eq_map
      input.localizedRerootCumulativeRule45Observable
      (fun key => projectRule4aLabelLayers key.rankedLabels)
      observables rankedLabels)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
