import TetraStereo.OneCenter.IUPACRule45CanonicalFamilyNonvacuitySeedCore

set_option autoImplicit false

namespace TetraStereo.OneCenter.IUPACNormativeProvision
namespace Rule45CanonicalFamilyNonvacuity

open AuthoritativeChemicalInput
open CertifiedLocalizedCIPInput

set_option maxRecDepth 10000 in
theorem central_cumulative_reflection
    (stage : LocalizedCumulativeRule45Stage)
    (leftKey rightKey : source.AromaticCanonicalCumulativeRule45Key)
    (leftCanonical : source.CanonicalAromaticCanonicalCumulativeRule45Key
      stage target view ruleFuel (rootAt positionTwo) leftKey)
    (rightCanonical : source.CanonicalAromaticCanonicalCumulativeRule45Key
      (reflectedRule4bcStage stage) target view ruleFuel
        (rootAt positionThree) rightKey) :
    source.AromaticCanonicalCumulativeRule45UppercaseReflection leftKey rightKey := by
  cases leftCanonical with
  | terminal frame empty _ =>
      have childrenEq := declarative_rerootChildren_eq_actual _ _ frame
      rw [childrenEq, seedLeftChildren_explicit] at empty
      simp at empty
  | branch leftFrame _ leftObserved leftChildren leftRanking =>
      cases rightCanonical with
      | terminal frame empty _ =>
          have childrenEq := declarative_rerootChildren_eq_actual _ _ frame
          rw [childrenEq, seedRightChildren_explicit] at empty
          simp at empty
      | branch rightFrame _ rightObserved rightChildren rightRanking =>
          have leftChildrenEq := declarative_rerootChildren_eq_actual _ _ leftFrame
          have rightChildrenEq := declarative_rerootChildren_eq_actual _ _ rightFrame
          subst_vars
          have childrenReflected := seedChildKeyLists_reflection stage
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
            target view (rootAt positionTwo) _).mpr leftObserved
          have rightLabel := (source.aromaticCanonicalDependencyLabel_eq_iff
            target view (rootAt positionThree) _).mpr rightObserved
          rw [central_dependency_label_two] at leftLabel
          rw [central_dependency_label_three] at rightLabel
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

theorem canonical_cumulative_rankedLabels_starts_with_dependency
    {stage : LocalizedCumulativeRule45Stage}
    {cursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {key : source.AromaticCanonicalCumulativeRule45Key}
    {label : Option AromaticCanonicalAuxiliaryLabel}
    (canonical : source.CanonicalAromaticCanonicalCumulativeRule45Key
      stage target view ruleFuel cursor key)
    (labelComputed : source.aromaticCanonicalDependencyLabel target view cursor = label) :
    ∃ tail, key.rankedLabels = [[([], label)]] ++ tail := by
  have labelUnique : ∀ observed,
      source.DeclarativeAromaticCanonicalDependencyLabel target view cursor observed →
        observed = label := by
    intro observed observedCanonical
    have observedComputed :=
      (source.aromaticCanonicalDependencyLabel_eq_iff target view cursor observed).mpr
        observedCanonical
    exact observedComputed.symm.trans labelComputed
  cases canonical
  case terminal observed =>
    refine ⟨[], ?_⟩
    simp [labelUnique _ observed]
  case branch observed =>
    simp [labelUnique _ observed]

/-- The left branch contributes one Rule-4b reference, the corrected `S` descriptor. -/
theorem central_references_two :
    (partition.frame.keyAt positionTwo).rule45.prior.references = [.S] := by
  have canonical := (central_key_canonical positionTwo).2.1
  rcases canonical with ⟨rule4a, selected, count, readings⟩
  obtain ⟨tail, ranked⟩ :=
    canonical_cumulative_rankedLabels_starts_with_dependency rule4a
      central_dependency_label_two
  have selectedExact :=
    (localizedRule4bReferencesFromRankedLabels_eq_iff
      (partition.frame.keyAt positionTwo).rule45.prior.rule4aKey.rankedLabels
      (partition.frame.keyAt positionTwo).rule45.prior.references).mpr selected
  rw [ranked] at selectedExact
  simpa [localizedRule4bReferencesFromRankedLabels,
    localizedFirstChiralRankPopulation,
    localizedFirstChiralRankPopulationInLayer,
    localizedChiralDescriptorsAtRank,
    localizedRule4bReferencesFromPopulation] using selectedExact.symm

/-- The mirrored right branch contributes one Rule-4b reference, the corrected `R` descriptor. -/
theorem central_references_three :
    (partition.frame.keyAt positionThree).rule45.prior.references = [.R] := by
  have canonical := (central_key_canonical positionThree).2.1
  rcases canonical with ⟨rule4a, selected, count, readings⟩
  obtain ⟨tail, ranked⟩ :=
    canonical_cumulative_rankedLabels_starts_with_dependency rule4a
      central_dependency_label_three
  have selectedExact :=
    (localizedRule4bReferencesFromRankedLabels_eq_iff
      (partition.frame.keyAt positionThree).rule45.prior.rule4aKey.rankedLabels
      (partition.frame.keyAt positionThree).rule45.prior.references).mpr selected
  rw [ranked] at selectedExact
  simpa [localizedRule4bReferencesFromRankedLabels,
    localizedFirstChiralRankPopulation,
    localizedFirstChiralRankPopulationInLayer,
    localizedChiralDescriptorsAtRank,
    localizedRule4bReferencesFromPopulation] using selectedExact.symm

theorem central_left_references_nonempty :
    (partition.frame.keyAt positionTwo).rule45.prior.references ≠ [] := by
  rw [central_references_two]
  simp

theorem central_right_references_nonempty :
    (partition.frame.keyAt positionThree).rule45.prior.references ≠ [] := by
  rw [central_references_three]
  simp

theorem central_reference_count_tie :
    compare
      (partition.frame.keyAt positionTwo).rule45.prior.referenceCountPriority
      (partition.frame.keyAt positionThree).rule45.prior.referenceCountPriority = .eq := by
  have leftCanonical := (central_key_canonical positionTwo).2.1
  have rightCanonical := (central_key_canonical positionThree).2.1
  rw [leftCanonical.2.2.1, rightCanonical.2.2.1,
    central_references_two, central_references_three]
  rfl

/-- One canonical reading per side suffices for the Rule-4b/4c tie whenever the two selected
references are exchanged by `RS.swap` and cumulative keys reflect.  This is the general form of
the original fixed-`R`/`S` lemma; the concrete instance is recovered below. -/
theorem canonical_singleton_rule4bcReadings_reflection
    {leftCursor rightCursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {leftLabel rightLabel : RS}
    {leftReadings rightReadings :
      List source.AromaticCanonicalRerootRule4bcReading}
    (leftCanonical : source.CanonicalAromaticCanonicalRerootRule4bcReadings
      target view ruleFuel leftCursor [some leftLabel] leftReadings)
    (rightCanonical : source.CanonicalAromaticCanonicalRerootRule4bcReadings
      target view ruleFuel rightCursor [some rightLabel] rightReadings)
    (labelReflection : rightLabel = RS.swap leftLabel)
    (cumulativeReflection :
      ∀ (stage : LocalizedCumulativeRule45Stage)
        (leftKey rightKey : source.AromaticCanonicalCumulativeRule45Key),
        source.CanonicalAromaticCanonicalCumulativeRule45Key
            stage target view ruleFuel leftCursor leftKey →
        source.CanonicalAromaticCanonicalCumulativeRule45Key
            (reflectedRule4bcStage stage) target view ruleFuel rightCursor rightKey →
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
                  refine ⟨?_, ?_, ?_⟩
                  · simp [labelReflection]
                  · have reflected := cumulativeReflection (.rule4b leftLabel) _ _
                        leftRule4b (by
                          simpa [reflectedRule4bcStage, labelReflection] using rightRule4b)
                    exact reflected.descriptor.symm
                  · have reflected := cumulativeReflection (.rule4c leftLabel) _ _
                        leftRule4c (by
                          simpa [reflectedRule4bcStage, labelReflection] using rightRule4c)
                    exact reflected.descriptor.symm

/-- Once recursive cumulative-key transport is supplied, both concrete reading comparators tie
    from the one canonical partition, with no further row-specific semantics. -/
theorem central_rule4bc_ties_of_cumulativeReflection
    (cumulativeReflection :
      ∀ (stage : LocalizedCumulativeRule45Stage)
        (leftKey rightKey : source.AromaticCanonicalCumulativeRule45Key),
        source.CanonicalAromaticCanonicalCumulativeRule45Key
            stage target view ruleFuel (rootAt positionTwo) leftKey →
        source.CanonicalAromaticCanonicalCumulativeRule45Key
            (reflectedRule4bcStage stage) target view ruleFuel
              (rootAt positionThree) rightKey →
        source.AromaticCanonicalCumulativeRule45UppercaseReflection leftKey rightKey) :
    source.compareAromaticCanonicalRerootCompoundRule4bReadings
        (partition.frame.keyAt positionTwo).rule45.prior.readings
        (partition.frame.keyAt positionThree).rule45.prior.readings = .eq ∧
      source.compareAromaticCanonicalRerootCompoundRule4cReadings
        (partition.frame.keyAt positionTwo).rule45.prior.readings
        (partition.frame.keyAt positionThree).rule45.prior.readings = .eq := by
  have leftPrior := (central_key_canonical positionTwo).2.1
  have rightPrior := (central_key_canonical positionThree).2.1
  have leftReadings : source.CanonicalAromaticCanonicalRerootRule4bcReadings
      target view ruleFuel (rootAt positionTwo) [some .S]
        (partition.frame.keyAt positionTwo).rule45.prior.readings := by
    simpa [central_references_two] using leftPrior.2.2.2
  have rightReadings : source.CanonicalAromaticCanonicalRerootRule4bcReadings
      target view ruleFuel (rootAt positionThree) [some .R]
        (partition.frame.keyAt positionThree).rule45.prior.readings := by
    simpa [central_references_three] using rightPrior.2.2.2
  exact source.compareAromaticCanonicalRerootCompoundRule4bcReadings_eq_of_reflection _ _
    (canonical_singleton_rule4bcReadings_reflection
      leftReadings rightReadings rfl cumulativeReflection)

theorem central_rule4bc_ties :
    source.compareAromaticCanonicalRerootCompoundRule4bReadings
        (partition.frame.keyAt positionTwo).rule45.prior.readings
        (partition.frame.keyAt positionThree).rule45.prior.readings = .eq ∧
      source.compareAromaticCanonicalRerootCompoundRule4cReadings
        (partition.frame.keyAt positionTwo).rule45.prior.readings
        (partition.frame.keyAt positionThree).rule45.prior.readings = .eq :=
  central_rule4bc_ties_of_cumulativeReflection central_cumulative_reflection

noncomputable def central_traceSeed_of_rule3
    (rule3Tie :
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        (partition.frame.keyAt positionTwo).rule3
        (partition.frame.keyAt positionThree).rule3 = .eq) :
    Rule45CanonicalTraceNonvacuitySeed := by
  obtain ⟨rule4bTie, rule4cTie⟩ := central_rule4bc_ties
  exact rule45CanonicalTraceNonvacuitySeed_of_activePartitionPair
    source source_structurallyWellFormed carrierFuel ruleFuel center roots partition
      positionTwo positionThree (by decide) roots_computed partition_canonical rule3Tie
      central_left_references_nonempty central_right_references_nonempty
      central_reference_count_tie rule4bTie rule4cTie

/-! ## The remaining Rule-3 automorphism transport -/

theorem aromaticCanonicalRule3SpatialNodeExcept?_eq_some_none_of_noDouble
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    source.aromaticCanonicalRule3SpatialNodeExcept? excluded node = some none := by
  have notEdge : ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge node := by
    rintro ⟨_, current, parent, _, _, ordinary⟩
    exact source_no_ordinary_double_bond parent current ordinary
  have base := source.aromaticCanonicalRule3SpatialNode?_eq_some_none_of_not_edge node notEdge
  simp [AuthoritativeChemicalInput.aromaticCanonicalRule3SpatialNodeExcept?, base]

theorem branchSwap_rule3SpatialNodeExcept_natural
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    source.aromaticCanonicalRule3SpatialNodeExcept? excluded
        (mapAromaticCanonicalOfficialCIPNode branchSwapAtomPermutation node) =
      source.aromaticCanonicalRule3SpatialNodeExcept? excluded node := by
  rw [aromaticCanonicalRule3SpatialNodeExcept?_eq_some_none_of_noDouble,
    aromaticCanonicalRule3SpatialNodeExcept?_eq_some_none_of_noDouble]

theorem seedRightChildren_eq_map :
    source.aromaticCanonicalRerootChildren (rootAt positionThree) =
      (source.aromaticCanonicalRerootChildren (rootAt positionTwo)).map
        branchSwapRerootCursor := by
  rw [seedLeftChildren_explicit, seedRightChildren_explicit]
  simp [branchSwapRerootCursor_maps_seedChildAt]

theorem seedChild_rule3CursorAutomorphismNatural
    (fuel : Nat) (position : Fin 3) :
    AromaticCanonicalRule3CursorAutomorphismNatural source branchSwapAtomPermutation
      branchSwapRerootCursor fuel (seedLeftChildAt position) := by
  induction fuel with
  | zero =>
      exact ⟨branchSwapRerootCursor_node _, by
        rw [branchSwapRerootCursor_maps_seedChildAt,
          seedRightChild_children_empty, seedLeftChild_children_empty]
        rfl⟩
  | succ fuel inductionHypothesis =>
      exact ⟨branchSwapRerootCursor_node _, by
        rw [branchSwapRerootCursor_maps_seedChildAt,
          seedRightChild_children_empty, seedLeftChild_children_empty]
        rfl, by simp [seedLeftChild_children_empty]⟩

theorem central_rule3CursorAutomorphismNatural :
    AromaticCanonicalRule3CursorAutomorphismNatural source branchSwapAtomPermutation
      branchSwapRerootCursor ruleFuel (rootAt positionTwo) := by
  unfold AromaticCanonicalRule3CursorAutomorphismNatural
  refine ⟨branchSwapRerootCursor_node _, ?_, ?_⟩
  · rw [branchSwapRerootCursor_maps_central_two]
    exact seedRightChildren_eq_map
  · intro child present
    rw [seedLeftChildren_explicit] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl
    all_goals exact seedChild_rule3CursorAutomorphismNatural 3 _

theorem central_rule3SpatialKeyExcept_automorphism_natural :
    source.buildAromaticCanonicalRule3SpatialKeyExcept?
        partition.frame.rule3Frame.excluded ruleFuel (rootAt positionThree) =
      (source.buildAromaticCanonicalRule3SpatialKeyExcept?
        partition.frame.rule3Frame.excluded ruleFuel (rootAt positionTwo)).map
          (mapAromaticCanonicalUncancelledRule3SpatialKey branchSwapAtomPermutation) := by
  rw [source.buildAromaticCanonicalRule3SpatialKeyExcept?_eq_with]
  exact buildAromaticCanonicalRule3SpatialKeyWith?_automorphism_natural_of_cursor
    source branchSwapAtomPermutation branchSwapRerootCursor
      (source.aromaticCanonicalRule3SpatialNodeExcept? partition.frame.rule3Frame.excluded)
      (branchSwap_rule3SpatialNodeExcept_natural partition.frame.rule3Frame.excluded)
      (compareAromaticCanonicalUncancelledRule3SpatialKeys_map_natural_of_constitution_of_no_edges
        source branchSwapAtomPermutation branchSwapAtomPermutation_constitution
          source_aromaticMancudeEdgeSetExact source_no_aromatic_edges)
      ruleFuel (rootAt positionTwo) central_rule3CursorAutomorphismNatural

theorem central_rule3_key_computed (position : Fin 4) :
    source.buildAromaticCanonicalRule3SpatialKeyExcept?
        partition.frame.rule3Frame.excluded ruleFuel (rootAt position) =
      some (partition.frame.keyAt position).rule3 := by
  exact (source.buildAromaticCanonicalRule3SpatialKeyExcept?_eq_some_iff_canonical
    partition.frame.rule3Frame.excluded ruleFuel (rootAt position)
      (partition.frame.keyAt position).rule3).mpr (central_key_canonical position).1

theorem central_rule3_right_eq_map_left :
    (partition.frame.keyAt positionThree).rule3 =
      mapAromaticCanonicalUncancelledRule3SpatialKey branchSwapAtomPermutation
        (partition.frame.keyAt positionTwo).rule3 := by
  have transported := central_rule3SpatialKeyExcept_automorphism_natural
  rw [central_rule3_key_computed positionThree,
    central_rule3_key_computed positionTwo] at transported
  exact Option.some.inj transported

theorem central_rule3_tie :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (partition.frame.keyAt positionTwo).rule3
      (partition.frame.keyAt positionThree).rule3 = .eq := by
  rw [central_rule3_right_eq_map_left]
  exact compareAromaticCanonicalUncancelledRule3SpatialKeys_self_map_eq_of_observations
    source branchSwapAtomPermutation
      (exactOfficialRule1aObservation_natural_of_constitution_of_no_edges
        source branchSwapAtomPermutation branchSwapAtomPermutation_constitution
          source_aromaticMancudeEdgeSetExact source_no_aromatic_edges)
      (officialNodeRule2_natural_of_constitution source branchSwapAtomPermutation
        branchSwapAtomPermutation_constitution)
      (partition.frame.keyAt positionTwo).rule3

/-- The unconditional molecular seed: one complete canonical trace activates every typed
    Rules-4b/5 family projection. -/
noncomputable def central_traceSeed : Rule45CanonicalTraceNonvacuitySeed :=
  central_traceSeed_of_rule3 central_rule3_tie

/-- The one seed is compiled into nonvacuity for the whole canonical provision family. -/
noncomputable def familyNonvacuityWitnesses :
    Rule45CanonicalFamilyNonvacuityWitnesses :=
  .of_traceSeed central_traceSeed

end Rule45CanonicalFamilyNonvacuity
end TetraStereo.OneCenter.IUPACNormativeProvision
