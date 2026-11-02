import TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule45CompiledReadings
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule45ReflectionNaturality

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule45Comparison

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource

/-!
# Complete Rule-4b/4c prior tie from the actual drawing model

Reflection is reconstructed for the actual emitted daughter keys: their actual six terminal
children have no auxiliary labels, and their actual daughter heads are source-derived.  Under the
corrected geometry calibration the slot-2 daughter head is `S` and the slot-3 daughter head is
`R`; the upstream declarations retain their historical `_R`/`_S` names with corrected statements.
Reflection therefore runs from the slot-2 `S` key to the slot-3 `R` key.  The pointwise singleton
reading lemma is provided twice: the historical, still-true `R`/`S` conditional keeps its
kernel-certificate name and proof unchanged, and the mirrored `S`/`R` sibling
`drawing_singleton_rule4bc_readings_reflection_S_R` is the instance used by the corrected actual
model.

The sorted child merges preserve constitutional observations, descriptor equality and ranked
label reflection.  This supplies the full compound prior comparator, including its exact
reference-count gate.  No Rule-4b/4c tie or old spatial model labels are assumed.  Rule-3 tie and
the final central descriptor remain separate obligations.
-/

private theorem drawing_left_children_explicit :
    source.aromaticCanonicalRerootChildren (centralRootAt centralSlotTwo) =
      [leftContinuingChildAt ⟨0, by decide +kernel⟩,
        leftContinuingChildAt ⟨1, by decide +kernel⟩,
        leftContinuingChildAt ⟨2, by decide +kernel⟩] := rfl

private theorem drawing_right_children_explicit :
    source.aromaticCanonicalRerootChildren (centralRootAt centralSlotThree) =
      [rightContinuingChildAt ⟨0, by decide +kernel⟩,
        rightContinuingChildAt ⟨1, by decide +kernel⟩,
        rightContinuingChildAt ⟨2, by decide +kernel⟩] := rfl

theorem drawing_declarative_children_eq_nil
    (cursor : source.AromaticCanonicalRerootCursor branchCarrierFuel)
    (children : List (source.AromaticCanonicalRerootCursor branchCarrierFuel))
    (canonical : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
    (actual : source.aromaticCanonicalRerootChildren cursor = []) : children = [] := by
  have actualCanonical := (source.aromaticCanonicalRerootChildren_sound cursor).1
  rw [actual] at actualCanonical
  have mapped : children.map (fun child => child.occurrence.1) = [] :=
    canonical.1.trans actualCanonical.symm
  exact List.length_eq_zero_iff.mp (by simpa using congrArg List.length mapped)

theorem drawing_declarative_children_eq_actual
    (cursor : source.AromaticCanonicalRerootCursor branchCarrierFuel)
    (children : List (source.AromaticCanonicalRerootCursor branchCarrierFuel))
    (canonical : source.DeclarativeAromaticCanonicalRerootChildren cursor children) :
    children = source.aromaticCanonicalRerootChildren cursor := by
  have computed := (source.aromaticCanonicalRerootChildren?_eq_some_iff
    cursor children).mpr canonical
  simpa [AuthoritativeChemicalInput.aromaticCanonicalRerootChildren?] using computed.symm

set_option maxRecDepth 10000 in
theorem drawing_leaf_cumulative_reflection
    (position : Fin 3) (stage : LocalizedCumulativeRule45Stage)
    (leftKey rightKey : source.AromaticCanonicalCumulativeRule45Key)
    (leftCanonical : source.CanonicalAromaticCanonicalCumulativeRule45Key
      stage centralTarget centralView 3 (leftContinuingChildAt position) leftKey)
    (rightCanonical : source.CanonicalAromaticCanonicalCumulativeRule45Key
      (reflectedRule4bcStage stage) centralTarget centralView 3
        (rightContinuingChildAt position) rightKey) :
    source.AromaticCanonicalCumulativeRule45UppercaseReflection leftKey rightKey := by
  cases leftCanonical with
  | terminal leftFrame _ leftObserved =>
      cases rightCanonical with
      | terminal rightFrame _ rightObserved =>
          have leftLabel := (source.aromaticCanonicalDependencyLabel_eq_iff
            centralTarget centralView (leftContinuingChildAt position) _).mpr leftObserved
          have rightLabel := (source.aromaticCanonicalDependencyLabel_eq_iff
            centralTarget centralView (rightContinuingChildAt position) _).mpr rightObserved
          rw [leftContinuingChild_central_dependency_none position] at leftLabel
          rw [rightContinuingChild_central_dependency_none position] at rightLabel
          subst_vars
          constructor
          · fin_cases position <;> rfl
          · fin_cases position <;> rfl
          · fin_cases position <;> rfl
          · exact congrArg (fun priority => [[([], priority)]])
              (localizedCumulativeRule45Priority_reflectedRule4bcStage stage none).symm
          · rfl
          · rfl
      | branch rightFrame rightNonempty _ _ _ =>
          exact (rightNonempty (drawing_declarative_children_eq_nil _ _
            rightFrame (rightContinuingChild_children_empty position))).elim
  | branch leftFrame leftNonempty _ _ _ =>
      exact (leftNonempty (drawing_declarative_children_eq_nil _ _
        leftFrame (leftContinuingChild_children_empty position))).elim

theorem drawing_child_key_lists_reflection
    (stage : LocalizedCumulativeRule45Stage)
    {leftKeys rightKeys : List source.AromaticCanonicalCumulativeRule45Key}
    (leftCanonical : source.CanonicalAromaticCanonicalCumulativeRule45KeyList
      stage centralTarget centralView 3
        (source.aromaticCanonicalRerootChildren (centralRootAt centralSlotTwo)) leftKeys)
    (rightCanonical : source.CanonicalAromaticCanonicalCumulativeRule45KeyList
      (reflectedRule4bcStage stage) centralTarget centralView 3
        (source.aromaticCanonicalRerootChildren (centralRootAt centralSlotThree)) rightKeys) :
    List.Forall₂ source.AromaticCanonicalCumulativeRule45UppercaseReflection
      leftKeys rightKeys := by
  rw [drawing_left_children_explicit] at leftCanonical
  rw [drawing_right_children_explicit] at rightCanonical
  cases leftCanonical with
  | cons leftZero leftTail =>
    cases leftTail with
    | cons leftOne leftTail =>
      cases leftTail with
      | cons leftTwo leftTail =>
        cases leftTail
        cases rightCanonical with
        | cons rightZero rightTail =>
          cases rightTail with
          | cons rightOne rightTail =>
            cases rightTail with
            | cons rightTwo rightTail =>
              cases rightTail
              exact .cons
                (drawing_leaf_cumulative_reflection (⟨0, by decide +kernel⟩ : Fin 3) stage _ _
                  leftZero rightZero) <| .cons
                (drawing_leaf_cumulative_reflection (⟨1, by decide +kernel⟩ : Fin 3) stage _ _
                  leftOne rightOne) <| .cons
                (drawing_leaf_cumulative_reflection (⟨2, by decide +kernel⟩ : Fin 3) stage _ _
                  leftTwo rightTwo) .nil


theorem central_actual_cumulative_reflection
    (stage : LocalizedCumulativeRule45Stage)
    (leftKey rightKey : source.AromaticCanonicalCumulativeRule45Key)
    (leftCanonical : source.CanonicalAromaticCanonicalCumulativeRule45Key
      stage centralTarget centralView 4 (centralRootAt centralSlotTwo) leftKey)
    (rightCanonical : source.CanonicalAromaticCanonicalCumulativeRule45Key
      (reflectedRule4bcStage stage) centralTarget centralView 4
        (centralRootAt centralSlotThree) rightKey) :
    source.AromaticCanonicalCumulativeRule45UppercaseReflection leftKey rightKey := by
  cases leftCanonical with
  | terminal frame empty _ =>
      have childrenEq := drawing_declarative_children_eq_actual _ _ frame
      rw [childrenEq, drawing_left_children_explicit] at empty
      simp at empty
  | branch leftFrame _ leftObserved leftChildren leftRanking =>
      cases rightCanonical with
      | terminal frame empty _ =>
          have childrenEq := drawing_declarative_children_eq_actual _ _ frame
          rw [childrenEq, drawing_right_children_explicit] at empty
          simp at empty
      | branch rightFrame _ rightObserved rightChildren rightRanking =>
          have leftChildrenEq := drawing_declarative_children_eq_actual _ _ leftFrame
          have rightChildrenEq := drawing_declarative_children_eq_actual _ _ rightFrame
          subst_vars
          have childrenReflected := drawing_child_key_lists_reflection stage
            leftChildren rightChildren
          have sortedReflected :=
            source.sortAromaticCanonicalCumulativeRule45Keys_reflection childrenReflected
          have leftSorted :=
            (source.sortAromaticCanonicalCumulativeRule45Keys_eq_iff_canonical _ _).mpr
              leftRanking
          have rightSorted :=
            (source.sortAromaticCanonicalCumulativeRule45Keys_eq_iff_canonical _ _).mpr
              rightRanking
          rw [leftSorted, rightSorted] at sortedReflected
          have leftLabel := (source.aromaticCanonicalDependencyLabel_eq_iff
            centralTarget centralView (centralRootAt centralSlotTwo) _).mpr leftObserved
          have rightLabel := (source.aromaticCanonicalDependencyLabel_eq_iff
            centralTarget centralView (centralRootAt centralSlotThree) _).mpr rightObserved
          rw [central_slot_two_label] at leftLabel
          rw [central_slot_three_label] at rightLabel
          subst_vars
          constructor
          · simp only [ExactOfficialRuleMajorKey.assemble,
              ExactOfficialRuleMajorKey.observedRule1aLayers]
            rw [OfficialRuleMajorKey.mapSourceLayers_append,
              OfficialRuleMajorKey.mapSourceLayers_append]
            congr 1
            simpa only [List.map_map, Function.comp_def] using
              mergeAddressedChildren_mapSourceLayers_eq_of_forall₂
                sortedReflected _ _ _ (fun _ _ related => related.rule1a)
          · simp only [ExactOfficialRuleMajorKey.assemble,
              ExactOfficialRuleMajorKey.rule1bLayers]
            rw [OfficialRuleMajorKey.mapSourceLayers_append,
              OfficialRuleMajorKey.mapSourceLayers_append]
            congr 1
            simpa only [List.map_map, Function.comp_def] using
              mergeAddressedChildren_mapSourceLayers_eq_of_forall₂
                sortedReflected _ _ _ (fun _ _ related => related.rule1b)
          · simp only [ExactOfficialRuleMajorKey.assemble,
              ExactOfficialRuleMajorKey.rule2Layers]
            rw [OfficialRuleMajorKey.mapSourceLayers_append,
              OfficialRuleMajorKey.mapSourceLayers_append]
            congr 1
            simpa only [List.map_map, Function.comp_def] using
              mergeAddressedChildren_mapSourceLayers_eq_of_forall₂
                sortedReflected _ _ _ (fun _ _ related => related.rule2)
          · have childrenEq :=
              mergeAromaticCanonicalDescriptorChildren_eq_of_reflection sortedReflected
            have priorityEq :
                localizedCumulativeRule45Priority stage (some (.chiral .S)) =
                  localizedCumulativeRule45Priority (reflectedRule4bcStage stage)
                    (some (.chiral .R)) := by
              simpa [reflectUppercaseOptionalLabel,
                reflectUppercaseAuxiliaryLabel, RS.swap] using
                  (localizedCumulativeRule45Priority_reflectedRule4bcStage
                    stage (some (.chiral .S))).symm
            exact congrArg₂ (· ++ ·)
              (congrArg (fun priority => [[([], priority)]]) priorityEq) childrenEq
          · simp [reflectUppercaseRankedLabels,
              reflectUppercaseRankedEntry, reflectUppercaseOptionalLabel,
              reflectUppercaseAuxiliaryLabel, RS.swap,
              mergeAromaticCanonicalLabelChildren_reflection sortedReflected]
          · simp [reflectUppercaseRankedLabels,
              reflectUppercaseRankedEntry, reflectUppercaseOptionalLabel,
              reflectUppercaseAuxiliaryLabel, RS.swap,
              mergeAromaticCanonicalRankedLabelChildren_reflection sortedReflected]


/-- Pointwise reflection of a singleton Rule-4b/4c reading population at the historical `R`/`S`
reference pair.  This is a pure conditional implication and its proof is unchanged by the
geometry calibration repair; it remains true (the corrected actual instance is the mirrored
sibling `drawing_singleton_rule4bc_readings_reflection_S_R`). -/
theorem drawing_singleton_rule4bc_readings_reflection
    {leftCursor rightCursor : source.AromaticCanonicalRerootCursor branchCarrierFuel}
    {leftReadings rightReadings :
      List source.AromaticCanonicalRerootRule4bcReading}
    (leftCanonical : source.CanonicalAromaticCanonicalRerootRule4bcReadings
      centralTarget centralView 4 leftCursor [some .R] leftReadings)
    (rightCanonical : source.CanonicalAromaticCanonicalRerootRule4bcReadings
      centralTarget centralView 4 rightCursor [some .S] rightReadings)
    (cumulativeReflection :
      ∀ (stage : LocalizedCumulativeRule45Stage)
        (leftKey rightKey : source.AromaticCanonicalCumulativeRule45Key),
        source.CanonicalAromaticCanonicalCumulativeRule45Key
            stage centralTarget centralView 4 leftCursor leftKey →
        source.CanonicalAromaticCanonicalCumulativeRule45Key
            (reflectedRule4bcStage stage) centralTarget centralView 4 rightCursor rightKey →
        source.AromaticCanonicalCumulativeRule45UppercaseReflection leftKey rightKey) :
    List.Forall₂ source.AromaticCanonicalRule4bcReadingUppercaseReflection
      leftReadings rightReadings := by
  cases leftCanonical with
  | cons leftHead leftTail =>
      cases leftTail
      cases rightCanonical with
      | cons rightHead rightTail =>
          cases rightTail
          cases leftHead with
          | reference leftRule4b leftRule4c =>
              cases rightHead with
              | reference rightRule4b rightRule4c =>
                  refine .cons ?_ .nil
                  refine ⟨rfl, ?_, ?_⟩
                  · have reflected := cumulativeReflection (.rule4b .R) _ _
                        leftRule4b (by
                          simpa [reflectedRule4bcStage] using rightRule4b)
                    exact reflected.descriptor.symm
                  · have reflected := cumulativeReflection (.rule4c .R) _ _
                        leftRule4c (by
                          simpa [reflectedRule4bcStage] using rightRule4c)
                    exact reflected.descriptor.symm

/-- Mirrored singleton reflection: left population at `[some .S]`, right population at
`[some .R]`.  This is the instance realised by the corrected actual drawing model, where slot `2`
is `S` and slot `3` is `R`. -/
theorem drawing_singleton_rule4bc_readings_reflection_S_R
    {leftCursor rightCursor : source.AromaticCanonicalRerootCursor branchCarrierFuel}
    {leftReadings rightReadings :
      List source.AromaticCanonicalRerootRule4bcReading}
    (leftCanonical : source.CanonicalAromaticCanonicalRerootRule4bcReadings
      centralTarget centralView 4 leftCursor [some .S] leftReadings)
    (rightCanonical : source.CanonicalAromaticCanonicalRerootRule4bcReadings
      centralTarget centralView 4 rightCursor [some .R] rightReadings)
    (cumulativeReflection :
      ∀ (stage : LocalizedCumulativeRule45Stage)
        (leftKey rightKey : source.AromaticCanonicalCumulativeRule45Key),
        source.CanonicalAromaticCanonicalCumulativeRule45Key
            stage centralTarget centralView 4 leftCursor leftKey →
        source.CanonicalAromaticCanonicalCumulativeRule45Key
            (reflectedRule4bcStage stage) centralTarget centralView 4 rightCursor rightKey →
        source.AromaticCanonicalCumulativeRule45UppercaseReflection leftKey rightKey) :
    List.Forall₂ source.AromaticCanonicalRule4bcReadingUppercaseReflection
      leftReadings rightReadings := by
  cases leftCanonical with
  | cons leftHead leftTail =>
      cases leftTail
      cases rightCanonical with
      | cons rightHead rightTail =>
          cases rightTail
          cases leftHead with
          | reference leftRule4b leftRule4c =>
              cases rightHead with
              | reference rightRule4b rightRule4c =>
                  refine .cons ?_ .nil
                  refine ⟨rfl, ?_, ?_⟩
                  · have reflected := cumulativeReflection (.rule4b .S) _ _
                        leftRule4b (by
                          simpa [reflectedRule4bcStage] using rightRule4b)
                    exact reflected.descriptor.symm
                  · have reflected := cumulativeReflection (.rule4c .S) _ _
                        leftRule4c (by
                          simpa [reflectedRule4bcStage] using rightRule4c)
                    exact reflected.descriptor.symm


theorem central_actual_prior_canonical (slot : Fin 4) :
    source.CanonicalAromaticCanonicalRerootCompoundRule4bcKey
      centralTarget centralView 4 (centralRootAt slot) (centralKeyFrame.keyAt slot).rule45.prior :=
  ((source.buildAromaticCanonicalRerootCompoundRule45Key?_eq_some_iff_canonical
    centralTarget centralView 4 (centralRootAt slot) (centralKeyFrame.keyAt slot).rule45).mp
      (central_rule45_keyAt_computed slot)).1

theorem central_actual_rule4a_reflection :
    source.AromaticCanonicalCumulativeRule45UppercaseReflection
      (centralKeyFrame.keyAt centralSlotTwo).rule45.prior.rule4aKey
      (centralKeyFrame.keyAt centralSlotThree).rule45.prior.rule4aKey :=
  central_actual_cumulative_reflection .rule4a _ _
    (central_actual_prior_canonical centralSlotTwo).1
    (central_actual_prior_canonical centralSlotThree).1

theorem central_actual_prior_readings_reflected :
    List.Forall₂ source.AromaticCanonicalRule4bcReadingUppercaseReflection
      (centralKeyFrame.keyAt centralSlotTwo).rule45.prior.readings
      (centralKeyFrame.keyAt centralSlotThree).rule45.prior.readings := by
  have leftPrior := central_actual_prior_canonical centralSlotTwo
  have rightPrior := central_actual_prior_canonical centralSlotThree
  have leftReadings : source.CanonicalAromaticCanonicalRerootRule4bcReadings
      centralTarget centralView 4 (centralRootAt centralSlotTwo) [some RS.S]
      (centralKeyFrame.keyAt centralSlotTwo).rule45.prior.readings := by
    simpa [central_left_prior_references, aromaticCanonicalRule4bcReferenceAlternatives]
      using leftPrior.2.2.2
  have rightReadings : source.CanonicalAromaticCanonicalRerootRule4bcReadings
      centralTarget centralView 4 (centralRootAt centralSlotThree) [some RS.R]
      (centralKeyFrame.keyAt centralSlotThree).rule45.prior.readings := by
    simpa [central_right_prior_references, aromaticCanonicalRule4bcReferenceAlternatives]
      using rightPrior.2.2.2
  exact drawing_singleton_rule4bc_readings_reflection_S_R leftReadings rightReadings
    central_actual_cumulative_reflection

/-- Both actual count gates obey source reference selection, including its complete ranked input. -/
theorem central_actual_prior_reference_count_exact (slot : Fin 4) :
    (centralKeyFrame.keyAt slot).rule45.prior.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority
        (localizedRule4bReferencesFromRankedLabels
          (centralKeyFrame.keyAt slot).rule45.prior.rule4aKey.rankedLabels) := by
  have canonical := central_actual_prior_canonical slot
  have selected := (localizedRule4bReferencesFromRankedLabels_eq_iff
    (centralKeyFrame.keyAt slot).rule45.prior.rule4aKey.rankedLabels
    (centralKeyFrame.keyAt slot).rule45.prior.references).mpr canonical.2.1
  exact canonical.2.2.1.trans
    (congrArg constitutionalRule4bReferenceCountPriority selected.symm)

theorem central_actual_prior_reference_count_tie :
    compare (centralKeyFrame.keyAt centralSlotTwo).rule45.prior.referenceCountPriority
      (centralKeyFrame.keyAt centralSlotThree).rule45.prior.referenceCountPriority = Ordering.eq :=
  source.compareAromaticCanonicalRule4bReferenceCounts_eq_of_reflectedRankedLabels _ _
    (central_actual_prior_reference_count_exact centralSlotTwo)
    (central_actual_prior_reference_count_exact centralSlotThree)
    central_actual_rule4a_reflection.rankedLabels

theorem central_actual_rule4bc_readings_tie :
    source.compareAromaticCanonicalRerootCompoundRule4bReadings
      (centralKeyFrame.keyAt centralSlotTwo).rule45.prior.readings
      (centralKeyFrame.keyAt centralSlotThree).rule45.prior.readings = Ordering.eq ∧
    source.compareAromaticCanonicalRerootCompoundRule4cReadings
      (centralKeyFrame.keyAt centralSlotTwo).rule45.prior.readings
      (centralKeyFrame.keyAt centralSlotThree).rule45.prior.readings = Ordering.eq :=
  source.compareAromaticCanonicalRerootCompoundRule4bcReadings_eq_of_reflection _ _
    central_actual_prior_readings_reflected

/-- Closed complete prior-key tie.  All count, reference selection, and reading premises are
supplied by the actual compiled keys and actual scheduled drawing-state labels. -/
theorem central_actual_rule4bc_prior_tie :
    source.compareAromaticCanonicalRerootCompoundRule4bcKeys
      (centralKeyFrame.keyAt centralSlotTwo).rule45.prior
      (centralKeyFrame.keyAt centralSlotThree).rule45.prior = Ordering.eq :=
  source.compareAromaticCanonicalRerootCompoundRule4bcKeys_eq_of_reflection _ _
    (central_actual_prior_reference_count_exact centralSlotTwo)
    (central_actual_prior_reference_count_exact centralSlotThree)
    central_actual_rule4a_reflection.rankedLabels central_actual_prior_readings_reflected

/-- The remaining prerequisite is the earlier Rule-3 tie, not any Rule-4/5 drawing premise.
Under the corrected calibration this actual slot-2/slot-3 comparison is `lt` with the
enantiomorphic signal. -/
theorem central_drawing_rule45_forward_of_rule3_tie
    (rule3Tie : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (centralKeyFrame.keyAt centralSlotTwo).rule3
      (centralKeyFrame.keyAt centralSlotThree).rule3 = Ordering.eq) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At
      centralKeyFrame centralSlotTwo centralSlotThree = { ordering := Ordering.lt, pseudo := true } :=
  central_drawing_rule45_forward_of_actual_prior_ties rule3Tie central_actual_rule4bc_prior_tie

end TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule45Comparison
