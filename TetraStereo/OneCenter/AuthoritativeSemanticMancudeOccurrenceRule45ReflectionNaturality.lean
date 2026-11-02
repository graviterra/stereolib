import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule45Key

set_option autoImplicit false

/-!
# Natural reflection of cumulative Rules 4b/5 keys

This module contains the source-parametric algebra behind uppercase reflection.  It proves that
stage priorities, cumulative child merges, ranked labels, and constitutional observation layers
commute with the exact cumulative-key reflection relation.  Concrete molecular fixtures only need
to establish that their child keys satisfy that relation.
-/

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open AuthoritativeChemicalInput

/-- Reflect a cumulative Rule-4a--5 stage together with every uppercase reference. -/
def reflectedRule4bcStage : LocalizedCumulativeRule45Stage →
    LocalizedCumulativeRule45Stage
  | .rule4a => .rule4a
  | .rule4b reference => .rule4b (RS.swap reference)
  | .rule4cNoReference => .rule4cNoReference
  | .rule4c reference => .rule4c (RS.swap reference)
  | .rule5NoRule4bReference rule5Reference =>
      .rule5NoRule4bReference (RS.swap rule5Reference)
  | .rule5 rule4bReference rule5Reference =>
      .rule5 (RS.swap rule4bReference) (RS.swap rule5Reference)

theorem localizedRule5Priority_reflectUppercase
    (reference : RS) (label : Option AromaticCanonicalAuxiliaryLabel) :
    localizedRule5Priority (RS.swap reference) (reflectUppercaseOptionalLabel label) =
      localizedRule5Priority reference label := by
  cases reference <;> cases label with
  | none => rfl
  | some label => cases label with
    | pseudoasymmetric descriptor => rfl
    | chiral descriptor => cases descriptor <;> rfl

theorem localizedCumulativeRule45Priority_reflectedRule4bcStage
    (stage : LocalizedCumulativeRule45Stage)
    (label : Option AromaticCanonicalAuxiliaryLabel) :
    localizedCumulativeRule45Priority (reflectedRule4bcStage stage)
        (reflectUppercaseOptionalLabel label) =
      localizedCumulativeRule45Priority stage label := by
  cases stage <;>
    simp [reflectedRule4bcStage, localizedCumulativeRule45Priority,
      localizedRule5Priority_reflectUppercase]

namespace AuthoritativeChemicalInput

private theorem zipIdx_flatMap_eq_of_forall₂
    {α β γ : Type*} {relation : α → β → Prop}
    {left : List α} {right : List β}
    (related : List.Forall₂ relation left right)
    (leftProject : Nat → α → List γ)
    (rightProject : Nat → β → List γ)
    (projectNatural : ∀ index left right,
      relation left right → leftProject index left = rightProject index right) :
    ∀ start,
      (left.zipIdx start).flatMap (fun entry => leftProject entry.2 entry.1) =
        (right.zipIdx start).flatMap (fun entry => rightProject entry.2 entry.1) := by
  intro start
  induction related generalizing start with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.zipIdx, List.flatMap_cons]
      rw [projectNatural start _ _ head]
      exact congrArg₂ (· ++ ·) rfl (induction (start + 1))

private theorem flatMap_eq_of_forall₂
    {α β γ : Type*} {relation : α → β → Prop}
    {left : List α} {right : List β}
    (related : List.Forall₂ relation left right)
    (leftProject : α → List γ) (rightProject : β → List γ)
    (natural : ∀ left right, relation left right →
      leftProject left = rightProject right) :
    left.flatMap leftProject = right.flatMap rightProject := by
  induction related with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.flatMap_cons]
      rw [natural _ _ head, induction]

theorem foldl_max_descriptor_length_eq_of_reflection
    {source : AuthoritativeChemicalInput}
    {left right : List source.AromaticCanonicalCumulativeRule45Key}
    (reflected : List.Forall₂
      source.AromaticCanonicalCumulativeRule45UppercaseReflection left right) :
    ∀ accumulator,
      left.foldl (fun longest child => max longest child.descriptor.length) accumulator =
        right.foldl (fun longest child => max longest child.descriptor.length) accumulator := by
  intro accumulator
  induction reflected generalizing accumulator with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.foldl_cons]
      rw [head.descriptor]
      exact induction _

theorem mergeAromaticCanonicalDescriptorChildren_eq_of_reflection
    {source : AuthoritativeChemicalInput}
    {left right : List source.AromaticCanonicalCumulativeRule45Key}
    (reflected : List.Forall₂
      source.AromaticCanonicalCumulativeRule45UppercaseReflection left right) :
    mergeAromaticCanonicalDescriptorChildren left =
      mergeAromaticCanonicalDescriptorChildren right := by
  unfold mergeAromaticCanonicalDescriptorChildren
    aromaticCanonicalDescriptorChildLayerCount
  rw [foldl_max_descriptor_length_eq_of_reflection reflected 0]
  apply List.map_congr_left
  intro depth _
  exact zipIdx_flatMap_eq_of_forall₂ reflected
    (fun index child => OfficialRuleMajorKey.prefixLayer index
      (child.descriptor.getD depth []))
    (fun index child => OfficialRuleMajorKey.prefixLayer index
      (child.descriptor.getD depth []))
    (by
      intro index left right related
      change OfficialRuleMajorKey.prefixLayer index (left.descriptor.getD depth []) =
        OfficialRuleMajorKey.prefixLayer index (right.descriptor.getD depth [])
      rw [related.descriptor]) 0

theorem foldl_max_label_length_eq_of_reflection
    {source : AuthoritativeChemicalInput}
    {left right : List source.AromaticCanonicalCumulativeRule45Key}
    (reflected : List.Forall₂
      source.AromaticCanonicalCumulativeRule45UppercaseReflection left right) :
    ∀ accumulator,
      left.foldl (fun longest child => max longest child.labels.length) accumulator =
        right.foldl (fun longest child => max longest child.labels.length) accumulator := by
  intro accumulator
  induction reflected generalizing accumulator with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.foldl_cons]
      have lengthEq := congrArg List.length head.labels
      have lengthEq' : _ := lengthEq
      simp [reflectUppercaseRankedLabels] at lengthEq'
      rw [← lengthEq']
      exact induction _

theorem mergeAromaticCanonicalLabelChildren_reflection
    {source : AuthoritativeChemicalInput}
    {left right : List source.AromaticCanonicalCumulativeRule45Key}
    (reflected : List.Forall₂
      source.AromaticCanonicalCumulativeRule45UppercaseReflection left right) :
    mergeAromaticCanonicalLabelChildren right =
      reflectUppercaseRankedLabels (mergeAromaticCanonicalLabelChildren left) := by
  unfold mergeAromaticCanonicalLabelChildren aromaticCanonicalLabelChildLayerCount
  rw [← foldl_max_label_length_eq_of_reflection reflected 0]
  unfold reflectUppercaseRankedLabels
  simp only [List.map_map]
  apply List.map_congr_left
  intro depth _
  change _ = (List.flatMap (fun child => OfficialRuleMajorKey.prefixLayer child.2
    (child.1.labels.getD depth [])) left.zipIdx).map reflectUppercaseRankedEntry
  symm
  rw [List.map_flatMap]
  exact zipIdx_flatMap_eq_of_forall₂ reflected
    (fun index child => (OfficialRuleMajorKey.prefixLayer index
      (child.labels.getD depth [])).map reflectUppercaseRankedEntry)
    (fun index child => OfficialRuleMajorKey.prefixLayer index
      (child.labels.getD depth []))
    (by
      intro index left right related
      change (OfficialRuleMajorKey.prefixLayer index
          (left.labels.getD depth [])).map reflectUppercaseRankedEntry =
        OfficialRuleMajorKey.prefixLayer index (right.labels.getD depth [])
      rw [related.labels]
      simp [reflectUppercaseRankedLabels, OfficialRuleMajorKey.prefixLayer]
      cases left.labels[depth]? <;>
        simp [Function.comp_def, reflectUppercaseRankedEntry]) 0

theorem foldl_max_rankedLabel_length_eq_of_reflection
    {source : AuthoritativeChemicalInput}
    {left right : List source.AromaticCanonicalCumulativeRule45Key}
    (reflected : List.Forall₂
      source.AromaticCanonicalCumulativeRule45UppercaseReflection left right) :
    ∀ accumulator,
      left.foldl (fun longest child => max longest child.rankedLabels.length) accumulator =
        right.foldl (fun longest child => max longest child.rankedLabels.length) accumulator := by
  intro accumulator
  induction reflected generalizing accumulator with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.foldl_cons]
      have lengthEq := congrArg List.length head.rankedLabels
      have lengthEq' : _ := lengthEq
      simp [reflectUppercaseRankedLabels] at lengthEq'
      rw [← lengthEq']
      exact induction _

theorem aromaticCanonicalRankedChildTail_reflection
    {source : AuthoritativeChemicalInput}
    {leftPrevious rightPrevious : source.AromaticCanonicalCumulativeRule45Key}
    (previousReflected : source.AromaticCanonicalCumulativeRule45UppercaseReflection
      leftPrevious rightPrevious) (rank : Nat)
    {left right : List source.AromaticCanonicalCumulativeRule45Key}
    (reflected : List.Forall₂
      source.AromaticCanonicalCumulativeRule45UppercaseReflection left right) :
    List.Forall₂ (fun left right =>
      source.AromaticCanonicalCumulativeRule45UppercaseReflection left.1 right.1 ∧
        left.2 = right.2)
      (aromaticCanonicalRankedChildTail
        source.compareAromaticCanonicalCumulativeRule45Keys leftPrevious rank left)
      (aromaticCanonicalRankedChildTail
        source.compareAromaticCanonicalCumulativeRule45Keys rightPrevious rank right) := by
  induction reflected generalizing leftPrevious rightPrevious rank with
  | nil => exact .nil
  | cons head tail induction =>
      unfold aromaticCanonicalRankedChildTail
      rw [source.compareAromaticCanonicalCumulativeRule45Keys_congr_reflection
        head previousReflected]
      refine .cons ⟨head, rfl⟩ ?_
      exact induction head _

theorem aromaticCanonicalRankedChildren_reflection
    {source : AuthoritativeChemicalInput}
    {left right : List source.AromaticCanonicalCumulativeRule45Key}
    (reflected : List.Forall₂
      source.AromaticCanonicalCumulativeRule45UppercaseReflection left right) :
    List.Forall₂ (fun left right =>
      source.AromaticCanonicalCumulativeRule45UppercaseReflection left.1 right.1 ∧
        left.2 = right.2)
      (aromaticCanonicalRankedChildren
        source.compareAromaticCanonicalCumulativeRule45Keys left)
      (aromaticCanonicalRankedChildren
        source.compareAromaticCanonicalCumulativeRule45Keys right) := by
  cases reflected with
  | nil => exact .nil
  | cons head tail =>
      exact .cons ⟨head, rfl⟩
        (aromaticCanonicalRankedChildTail_reflection head 0 tail)

theorem mergeAromaticCanonicalRankedLabelChildren_reflection
    {source : AuthoritativeChemicalInput}
    {left right : List source.AromaticCanonicalCumulativeRule45Key}
    (reflected : List.Forall₂
      source.AromaticCanonicalCumulativeRule45UppercaseReflection left right) :
    mergeAromaticCanonicalRankedLabelChildren
        source.compareAromaticCanonicalCumulativeRule45Keys right =
      reflectUppercaseRankedLabels
        (mergeAromaticCanonicalRankedLabelChildren
          source.compareAromaticCanonicalCumulativeRule45Keys left) := by
  unfold mergeAromaticCanonicalRankedLabelChildren
    aromaticCanonicalRankedLabelChildLayerCount
  rw [← foldl_max_rankedLabel_length_eq_of_reflection reflected 0]
  unfold reflectUppercaseRankedLabels
  simp only [List.map_map]
  apply List.map_congr_left
  intro depth _
  change _ = (List.flatMap (fun child => OfficialRuleMajorKey.prefixLayer child.2
    (child.1.rankedLabels.getD depth []))
      (aromaticCanonicalRankedChildren
        source.compareAromaticCanonicalCumulativeRule45Keys left)).map
          reflectUppercaseRankedEntry
  symm
  rw [List.map_flatMap]
  have ranked := aromaticCanonicalRankedChildren_reflection reflected
  exact flatMap_eq_of_forall₂ ranked
    (fun child => (OfficialRuleMajorKey.prefixLayer child.2
      (child.1.rankedLabels.getD depth [])).map reflectUppercaseRankedEntry)
    (fun child => OfficialRuleMajorKey.prefixLayer child.2
      (child.1.rankedLabels.getD depth []))
    (by
      intro left right related
      rcases related with ⟨keyRelated, rankEq⟩
      change (OfficialRuleMajorKey.prefixLayer left.2
          (left.1.rankedLabels.getD depth [])).map reflectUppercaseRankedEntry =
        OfficialRuleMajorKey.prefixLayer right.2
          (right.1.rankedLabels.getD depth [])
      rw [rankEq, keyRelated.rankedLabels]
      simp [reflectUppercaseRankedLabels, OfficialRuleMajorKey.prefixLayer]
      cases left.1.rankedLabels[depth]? <;>
        simp [Function.comp_def, reflectUppercaseRankedEntry])

theorem mergeAddressedChildren_mapSourceLayers_eq_of_forall₂
    {α β V γ : Type*} {relation : α → β → Prop}
    {left : List α} {right : List β}
    (related : List.Forall₂ relation left right)
    (leftSources : α → OfficialRuleMajorKey.AddressedSourceLayers V)
    (rightSources : β → OfficialRuleMajorKey.AddressedSourceLayers V)
    (observe : OfficialCIPNode V → γ)
    (layersNatural : ∀ left right, relation left right →
      OfficialRuleMajorKey.mapSourceLayers observe (leftSources left) =
        OfficialRuleMajorKey.mapSourceLayers observe (rightSources right)) :
    OfficialRuleMajorKey.mapSourceLayers observe
        (OfficialRuleMajorKey.mergeAddressedChildren (left.map leftSources)) =
      OfficialRuleMajorKey.mapSourceLayers observe
        (OfficialRuleMajorKey.mergeAddressedChildren (right.map rightSources)) := by
  have countNatural : ∀ accumulator,
      left.foldl (fun longest child => max longest (leftSources child).length) accumulator =
        right.foldl (fun longest child => max longest (rightSources child).length) accumulator := by
    intro accumulator
    induction related generalizing accumulator with
    | nil => rfl
    | cons head tail induction =>
      simp only [List.foldl_cons]
      have lengthNatural := congrArg List.length (layersNatural _ _ head)
      simp [OfficialRuleMajorKey.mapSourceLayers] at lengthNatural
      rw [lengthNatural]
      exact induction _
  unfold OfficialRuleMajorKey.mergeAddressedChildren
    OfficialRuleMajorKey.addressedChildLayerCount
    OfficialRuleMajorKey.mapSourceLayers
  simp only [List.foldl_map]
  rw [countNatural 0]
  simp only [List.map_map]
  apply List.map_congr_left
  intro depth _
  simp only [Function.comp_apply, List.map_flatMap]
  rw [List.zipIdx_map, List.zipIdx_map, List.flatMap_map, List.flatMap_map]
  exact zipIdx_flatMap_eq_of_forall₂ related
    (fun index child =>
      (OfficialRuleMajorKey.prefixLayer index
        ((leftSources child).getD depth [])).map
          (OfficialRuleMajorKey.mapObservation observe))
    (fun index child =>
      (OfficialRuleMajorKey.prefixLayer index
        ((rightSources child).getD depth [])).map
          (OfficialRuleMajorKey.mapObservation observe))
    (by
      intro index left right natural
      dsimp only
      rw [← OfficialRuleMajorKey.prefixLayer_mapObservation,
        ← OfficialRuleMajorKey.prefixLayer_mapObservation,
        ← OfficialRuleMajorKey.mapSourceLayers_getD,
        ← OfficialRuleMajorKey.mapSourceLayers_getD,
        layersNatural _ _ natural]) 0

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
