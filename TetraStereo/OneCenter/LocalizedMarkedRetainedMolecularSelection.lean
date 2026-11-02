import TetraStereo.OneCenter.LocalizedRetainedContextCompoundComparison
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Retained reference selection and compound prior order for any tetrahedral molecular reader

The retained-context theorems `retainedGeneratedContextTree_references_eq_selection`,
`retainedGeneratedCompound_independentReadback` and `retainedGeneratedCompound_prior_compare` are
stated for the generated reference state of `LocalizedRuleMajorReference.Input`. Their proofs use
that state only through two facts: the generated reader is `molecularReader` of the generated
descriptor map, and that map is tetrahedral. This module restates the chain for an arbitrary
descriptor map with tetrahedral values, read through `molecularReader` at an arbitrary carrier
target of a simple-bonded certified input. Rings are allowed; acyclicity is not used.

The actual Rule-4a key built with that reader selects exactly the independent retained reference
population `retainedReferenceSelection` on the realized arm graph. Successful compound builds at
executable children of the target read back as the retained selection and readings, and their
actual Rule-4a–4c compound order is the comparison of the independent retained prior keys. The
private prior algebra of `LocalizedRetainedContextCompoundComparison` is re-proved here because it
is not exported.

No reference, key, order, comparator law or successful sort is assumed. The descriptor map is a
parameter: this module does not say which map a given evaluator state induces.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularSelection

open CertifiedLocalizedCIPInput DeclarativeCIP LocalizedCumulativeDecoratedTree
open Rule4aTableBridge Rule4cObservationBridge OfficialSparseCanonicalVectorComparison
open RetainedContextStereoReadback RetainedRule4aCanonicalBridge RetainedContextReferenceSelection
open RetainedContextCompoundComparison
noncomputable section
open scoped Classical

/-- The carrier budget at which the retained reference-selection theorem is stated. -/
abbrev retainedCarrierFuel (input : CertifiedLocalizedCIPInput) : Nat :=
  input.certified.input.molecule.atomCount + 1

section Selection

variable {input : CertifiedLocalizedCIPInput}
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
  (singleBonded : input.moleculeGraph.SimpleBonded)
  (target : input.LocalizedRerootCursor (retainedCarrierFuel input))
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)

include tetrahedralMap singleBonded targetUnit

/-- **The actual Rule-4a reference population under any tetrahedral molecular reader is the
independent retained selection.** The reader is `molecularReader descriptorMap` at the target. -/
theorem retainedMolecularContextTree_references_eq_selection
    (tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input))
    {fuel : Nat} {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input .rule4a
      (input.localizedDependencyLabel target.occurrence
        (input.molecularView descriptorMap target.occurrence)) fuel tree key)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target) :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels =
      toReferenceList (retainedReferenceSelection input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph tree)) := by
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
  have hyp := retainedContextTreeRankReadback_of_molecularReader descriptorMap tetrahedralMap
    singleBonded target unit targetUnit tree realizes rootChild
  exact retainedTree_references_eq_retainedReferenceSelection descriptorMap target.occurrence tree
    (retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph tree) unit)
    (fun rule node actual lookup => retainedDecoratedObservation_eq_arm singleBonded target unit
      targetUnit tree realizes rootChild rule node actual lookup)
    trace unit (fun _ _ => rfl) hyp

/-- Adequate-budget existence of the actual Rule-4a key at an executable child, with its
reference list equal to the retained selection. Cursor validity is derived from membership. -/
theorem exists_retainedMolecularContextTree_references_eq_selection
    (cursor : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (rootChild : cursor ∈ input.executableLocalizedRerootChildren target) :
    ∃ (tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input))
      (key : input.LocalizedRerootCumulativeRule45Key),
      tree.source = cursor ∧
      input.buildRuleMajorCumulativeWithReadExec? .rule4a
        (input.localizedDependencyLabel target.occurrence
          (input.molecularView descriptorMap target.occurrence))
        (2 * (retainedCarrierFuel input + 1)) cursor = some key ∧
      localizedRule4bReferencesFromRankedLabels key.rankedLabels =
        toReferenceList (retainedReferenceSelection input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph tree)) := by
  have valid := input.localizedRerootChild_valid target cursor _
    (input.executableLocalizedRerootChildren_declarative target) rootChild
  obtain ⟨tree, key, source, built, trace⟩ := exists_ruleMajorTrace_at_twice input .rule4a
    (input.localizedDependencyLabel target.occurrence
      (input.molecularView descriptorMap target.occurrence)) cursor valid
  refine ⟨tree, key, source, ?_, ?_⟩
  · rw [input.buildRuleMajorCumulativeWithReadExec_eq]
    exact built
  · exact retainedMolecularContextTree_references_eq_selection descriptorMap tetrahedralMap
      singleBonded target unit targetUnit tree trace (by simpa only [source] using rootChild)

/-- Rank bundle and observation law at every stage of one executable child, for the molecular
reader of any tetrahedral map. -/
theorem retainedMolecularStageReadingFacts
    (cursor : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (child : cursor ∈ input.executableLocalizedRerootChildren target)
    (stages : input.RuleMajorContextStages (retainedCarrierFuel input)
      (input.localizedDependencyLabel target.occurrence
        (input.molecularView descriptorMap target.occurrence)) cursor) :
    RetainedStageReadingFacts stages descriptorMap unit := by
  have fill {stage : LocalizedCumulativeRule45Stage} {fuel : Nat}
      {key : input.LocalizedRerootCumulativeRule45Key}
      (tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input))
      (trace : LocalizedRuleMajorSortTrace input stage
        (input.localizedDependencyLabel target.occurrence
          (input.molecularView descriptorMap target.occurrence)) fuel tree key)
      (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target) :
      RetainedContextTreeRankReadback tree descriptorMap unit ∧
        RetainedArmObservation tree unit := by
    have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
    refine ⟨retainedContextTreeRankReadback_of_molecularReader descriptorMap tetrahedralMap
      singleBonded target unit targetUnit tree realizes rootChild, ?_⟩
    intro rule node actual lookup
    exact retainedDecoratedObservation_eq_arm singleBonded target unit targetUnit tree realizes
      rootChild rule node actual lookup
  exact {
    aReadback := (fill stages.a.tree stages.a.trace
      (by simpa only [stages.a.sourceEq] using child)).1
    aObservation := (fill stages.a.tree stages.a.trace
      (by simpa only [stages.a.sourceEq] using child)).2
    bReadback := fun reference => (fill (stages.b reference).tree (stages.b reference).trace
      (by simpa only [(stages.b reference).sourceEq] using child)).1
    bObservation := fun reference => (fill (stages.b reference).tree (stages.b reference).trace
      (by simpa only [(stages.b reference).sourceEq] using child)).2
    cReadback := fun reference => (fill (stages.c reference).tree (stages.c reference).trace
      (by simpa only [(stages.c reference).sourceEq] using child)).1
    cObservation := fun reference => (fill (stages.c reference).tree (stages.c reference).trace
      (by simpa only [(stages.c reference).sourceEq] using child)).2
    noReferenceReadback := (fill stages.noReference.tree stages.noReference.trace
      (by simpa only [stages.noReference.sourceEq] using child)).1
    noReferenceObservation := (fill stages.noReference.tree stages.noReference.trace
      (by simpa only [stages.noReference.sourceEq] using child)).2 }

/-- One successful compound at an executable child agrees with the retained selection and the
retained readings, for the molecular reader of any tetrahedral map. -/
theorem retainedMolecularCompound_independentReadback
    (cursor : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (cursorChild : cursor ∈ input.executableLocalizedRerootChildren target)
    (stages : input.RuleMajorContextStages (retainedCarrierFuel input)
      (input.localizedDependencyLabel target.occurrence
        (input.molecularView descriptorMap target.occurrence)) cursor)
    {compound : input.LocalizedRerootCompoundRule45Key}
    {W D : Nat} (width : stages.widthBound ≤ W) (depth : stages.depthBound ≤ D)
    (built : input.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
      (input.molecularView descriptorMap target.occurrence)
      (2 * (retainedCarrierFuel input + 1)) cursor = some compound) :
    RetainedCompoundReadbackData stages descriptorMap unit compound W D := by
  have uniformBuilt : input.buildRuleMajorCompoundRule45KeyWith?
      (fun stage position => input.buildRuleMajorCumulativeWithRead? stage
        (input.localizedDependencyLabel target.occurrence
          (input.molecularView descriptorMap target.occurrence))
        (2 * (retainedCarrierFuel input + 1)) position) cursor = some compound := by
    rw [← input.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
    rw [← input.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact built
  obtain ⟨_aKey, rankedReferences, _count, _readings⟩ :=
    input.contextStages_compound_readback stages uniformBuilt
  have selectionReferences := retainedMolecularContextTree_references_eq_selection descriptorMap
    tetrahedralMap singleBonded target unit targetUnit stages.a.tree stages.a.trace
    (by simpa only [stages.a.sourceEq] using cursorChild)
  have referencesEq : compound.prior.references = toReferenceList
      (retainedReferenceSelection input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree)) :=
    rankedReferences.trans selectionReferences
  exact retainedStages_compound_independentReadback singleBonded stages descriptorMap unit
    width depth
    (retainedMolecularStageReadingFacts descriptorMap tetrahedralMap singleBonded target unit
      targetUnit cursor cursorChild stages)
    (ruleMajorContextStageGraphIsoBundle_of_stages stages) uniformBuilt referencesEq

end Selection

/-! ## Prior algebra (re-proved from the exported cross-branch comparisons) -/

section PriorAlgebra

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

private def unmaskedRetainedPriorAt
    (molecule : MoleculeGraph input.Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph input.Atom) (W D : Nat) :
    CompletePriorSignature :=
  let selection := retainedReferenceSelection molecule descriptorMap unit graph
  let readings := retainedCompleteReadingsAt molecule descriptorMap unit graph W D
  toLex (selection.countPriority, toLex
    (readings.map (fun key => (ofLex key).1), readings.map (fun key => (ofLex key).2)))

private theorem compare_localUnmaskedRetainedPrior_eq
    (molecule : MoleculeGraph input.Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (left right : RootedDigraph input.Atom) (W D : Nat) :
    compare (unmaskedRetainedPriorAt molecule descriptorMap unit left W D)
        (unmaskedRetainedPriorAt molecule descriptorMap unit right W D) =
      compare (retainedCompletePriorSignatureAt molecule descriptorMap unit left W D)
        (retainedCompletePriorSignatureAt molecule descriptorMap unit right W D) := by
  unfold unmaskedRetainedPriorAt retainedCompletePriorSignatureAt
  cases hL : retainedReferenceSelection molecule descriptorMap unit left <;>
    cases hR : retainedReferenceSelection molecule descriptorMap unit right <;>
    simp only [ReferenceSelection.countPriority, reduceCtorEq, ↓reduceIte]
  all_goals first
    | rfl
    | (simp only [retainedCompleteReadingsAt, hL, hR, retainedCompleteReadingAt,
        List.map_cons, List.map_nil, ofLex_toLex]; rfl)

variable {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
  {cursorL cursorR : input.LocalizedRerootCursor carrierFuel}
  (singleBonded : input.moleculeGraph.SimpleBonded)
  (leftStages : input.RuleMajorContextStages carrierFuel read cursorL)
  (rightStages : input.RuleMajorContextStages carrierFuel read cursorR)
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (unit : DetectedOccurrence input.moleculeGraph)
  (readL : RetainedStageReadingFacts leftStages descriptorMap unit)
  (readR : RetainedStageReadingFacts rightStages descriptorMap unit)
  (isoL : RuleMajorContextStageGraphIsoBundle leftStages)
  (isoR : RuleMajorContextStageGraphIsoBundle rightStages)
  {W D : Nat} (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
  (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)

include singleBonded readL readR isoL isoR leftWidth leftDepth rightWidth rightDepth

private theorem reading_comparisons
    {left right : input.LocalizedRerootCompoundRule45Key}
    (dataL : RetainedCompoundReadbackData leftStages descriptorMap unit left W D)
    (dataR : RetainedCompoundReadbackData rightStages descriptorMap unit right W D)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    (countTie : left.prior.referenceCountPriority = right.prior.referenceCountPriority)
    (l : input.LocalizedRerootRule4bcReading) (hl : l ∈ left.prior.readings)
    (r : input.LocalizedRerootRule4bcReading) (hr : r ∈ right.prior.readings) :
    let observedL := retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph leftStages.a.tree) W D (l.reference?.map senseOf)
    let observedR := retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph rightStages.a.tree) W D (r.reference?.map senseOf)
    input.compareLocalizedRerootRule4bcReadingsByRule4b l r =
        compare (ofLex observedL).1 (ofLex observedR).1 ∧
      (input.compareLocalizedRerootRule4bcReadingsByRule4b l r = .eq →
        OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          l.rule4cKey.descriptor r.rule4cKey.descriptor =
            compare (ofLex observedL).2 (ofLex observedR).2) := by
  dsimp only
  have emptyIff := ReferenceSelection.empty_iff_of_countPriority_eq
    (dataL.count.symm.trans (countTie.trans dataR.count))
  have lp := dataL.readingStages l hl
  have rp := dataR.readingStages r hr
  cases hL : l.reference? with
  | none =>
      have rightNone := (dataR.readingEmpty r hr).mpr
        (emptyIff.mp ((dataL.readingEmpty l hl).mp hL))
      rw [hL] at lp
      rw [rightNone] at rp
      simp only [rightNone, Option.map_none]
      constructor
      · change OfficialRuleMajorKey.compareSparseLayers _ _ _ = compare ([] :
          Certificate.CanonicalSphereKey.Key StereoLabel) []
        dsimp only
        rw [lp.1, rp.1]
        exact (Ordering.then_eq_eq.mp aTie).2
      · intro _
        rw [lp.2, rp.2]
        exact retainedCrossBranch_noReference_compare singleBonded leftStages rightStages
          descriptorMap unit readL readR isoL isoR aTie leftWidth leftDepth rightWidth rightDepth
  | some refL =>
      cases hR : r.reference? with
      | none =>
          have leftNone := (dataL.readingEmpty l hl).mpr
            (emptyIff.mpr ((dataR.readingEmpty r hr).mp hR))
          simp [hL] at leftNone
      | some refR =>
          rw [hL] at lp
          rw [hR] at rp
          simp only [Option.map_some]
          constructor
          · change OfficialRuleMajorKey.compareSparseLayers _ _ _ = _
            dsimp only
            rw [lp.1, rp.1]
            exact retainedCrossBranch_selectedB_compare singleBonded leftStages rightStages
              descriptorMap unit readL readR isoL isoR refL refR aTie leftWidth leftDepth
              rightWidth rightDepth
          · intro bTie
            change OfficialRuleMajorKey.compareSparseLayers _
              l.rule4bKey.descriptor r.rule4bKey.descriptor = .eq at bTie
            rw [lp.1, rp.1] at bTie
            rw [lp.2, rp.2]
            exact retainedCrossBranch_selectedC_compare singleBonded leftStages rightStages
              descriptorMap unit readL readR isoL isoR refL refR aTie bTie leftWidth leftDepth
              rightWidth rightDepth

/-- After a Rule-4a tie, the actual compound Rule-4b/4c order is the comparison of the retained
prior signatures. Exported here because the original is private. -/
theorem compound_after4a_compare
    {left right : input.LocalizedRerootCompoundRule45Key}
    (dataL : RetainedCompoundReadbackData leftStages descriptorMap unit left W D)
    (dataR : RetainedCompoundReadbackData rightStages descriptorMap unit right W D)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq) :
    input.compareLocalizedRerootCompoundRule4bcAfterRule4a left.prior right.prior =
      compare (retainedCompletePriorSignatureAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph leftStages.a.tree) W D)
        (retainedCompletePriorSignatureAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph rightStages.a.tree) W D) := by
  rw [← compare_localUnmaskedRetainedPrior_eq]
  change (compare left.prior.referenceCountPriority right.prior.referenceCountPriority).then _ =
    (compare
      (retainedReferenceSelection input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph leftStages.a.tree)).countPriority
      (retainedReferenceSelection input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph rightStages.a.tree)).countPriority).then _
  rw [← dataL.count, ← dataR.count]
  apply then_congr
  intro countTie
  have countEq := compare_eq_iff_eq.mp countTie
  let observeL := fun reading : input.LocalizedRerootRule4bcReading =>
    retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph leftStages.a.tree) W D (reading.reference?.map senseOf)
  let observeR := fun reading : input.LocalizedRerootRule4bcReading =>
    retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph rightStages.a.tree) W D (reading.reference?.map senseOf)
  have agrees := reading_comparisons singleBonded leftStages rightStages descriptorMap unit
    readL readR isoL isoR leftWidth leftDepth rightWidth rightDepth dataL dataR aTie countEq
  have lists := compareLex_then_map_eq
    input.compareLocalizedRerootRule4bcReadingsByRule4b
    (fun l r => OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      l.rule4cKey.descriptor r.rule4cKey.descriptor)
    compare compare (fun l => (ofLex (observeL l)).1) (fun r => (ofLex (observeR r)).1)
    (fun l => (ofLex (observeL l)).2) (fun r => (ofLex (observeR r)).2)
    left.prior.readings right.prior.readings
    (fun l hl r hr => (agrees l hl r hr).1)
    (fun l hl r hr => (agrees l hl r hr).2)
  have fstL := congrArg (List.map (fun key : CompleteReadingKey => (ofLex key).1)) dataL.observations
  have fstR := congrArg (List.map (fun key : CompleteReadingKey => (ofLex key).1)) dataR.observations
  have sndL := congrArg (List.map (fun key : CompleteReadingKey => (ofLex key).2)) dataL.observations
  have sndR := congrArg (List.map (fun key : CompleteReadingKey => (ofLex key).2)) dataR.observations
  simp only [List.map_map, Function.comp_def] at fstL fstR sndL sndR
  dsimp only [observeL, observeR] at lists
  rw [fstL, fstR, sndL, sndR] at lists
  exact lists

end PriorAlgebra

section Prior

variable {input : CertifiedLocalizedCIPInput}
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
  (singleBonded : input.moleculeGraph.SimpleBonded)
  (target : input.LocalizedRerootCursor (retainedCarrierFuel input))
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)

include tetrahedralMap singleBonded targetUnit

/-- **Actual compound priority through Rule 4c equals the retained ligand prior key order**, for
the molecular reader of any tetrahedral map. Both arms are successful executions at executable
children of one simple-bonded target. Selection, readback, isomorphism and the Rule-4a tie are
derived, not assumed. -/
theorem retainedMolecularCompound_prior_compare
    (cursorL cursorR : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (childL : cursorL ∈ input.executableLocalizedRerootChildren target)
    (childR : cursorR ∈ input.executableLocalizedRerootChildren target)
    (leftStages : input.RuleMajorContextStages (retainedCarrierFuel input)
      (input.localizedDependencyLabel target.occurrence
        (input.molecularView descriptorMap target.occurrence)) cursorL)
    (rightStages : input.RuleMajorContextStages (retainedCarrierFuel input)
      (input.localizedDependencyLabel target.occurrence
        (input.molecularView descriptorMap target.occurrence)) cursorR)
    {W D : Nat} (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)
    {left right : input.LocalizedRerootCompoundRule45Key}
    (builtL : input.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
      (input.molecularView descriptorMap target.occurrence)
      (2 * (retainedCarrierFuel input + 1)) cursorL = some left)
    (builtR : input.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
      (input.molecularView descriptorMap target.occurrence)
      (2 * (retainedCarrierFuel input + 1)) cursorR = some right) :
    input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior =
      compare
        (retainedCompleteLigandPriorKeyAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph leftStages.a.tree) W D)
        (retainedCompleteLigandPriorKeyAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph rightStages.a.tree) W D) := by
  have dataL := retainedMolecularCompound_independentReadback descriptorMap tetrahedralMap
    singleBonded target unit targetUnit cursorL childL leftStages leftWidth leftDepth builtL
  have dataR := retainedMolecularCompound_independentReadback descriptorMap tetrahedralMap
    singleBonded target unit targetUnit cursorR childR rightStages rightWidth rightDepth builtR
  let readL := retainedMolecularStageReadingFacts descriptorMap tetrahedralMap singleBonded target
    unit targetUnit cursorL childL leftStages
  let readR := retainedMolecularStageReadingFacts descriptorMap tetrahedralMap singleBonded target
    unit targetUnit cursorR childR rightStages
  let isoL := ruleMajorContextStageGraphIsoBundle_of_stages leftStages
  let isoR := ruleMajorContextStageGraphIsoBundle_of_stages rightStages
  have initialCompare := retainedMolecularContextTrees_rule4a_compare descriptorMap tetrahedralMap
    singleBonded target unit targetUnit leftStages.a.tree rightStages.a.tree
    leftStages.a.trace rightStages.a.trace
    (by simpa only [leftStages.a.sourceEq] using childL)
    (by simpa only [rightStages.a.sourceEq] using childR)
    (leftStages.a_width_le.trans leftWidth) (rightStages.a_width_le.trans rightWidth)
    (leftStages.a_depth_le.trans leftDepth) (rightStages.a_depth_le.trans rightDepth)
  change (input.compareLocalizedRerootCumulativeRule45Keys left.prior.rule4aKey
    right.prior.rule4aKey).then
      (input.compareLocalizedRerootCompoundRule4bcAfterRule4a left.prior right.prior) =
    (compare
      (retainedMolecularRankPairAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph leftStages.a.tree) W D)
      (retainedMolecularRankPairAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph rightStages.a.tree) W D)).then _
  have rankEq :
      input.compareLocalizedRerootCumulativeRule45Keys left.prior.rule4aKey
        right.prior.rule4aKey =
      compare
        (retainedMolecularRankPairAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph leftStages.a.tree) W D)
        (retainedMolecularRankPairAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph rightStages.a.tree) W D) := by
    rw [dataL.aKey, dataR.aKey]
    simpa [retainedMolecularRankPairAt] using initialCompare
  rw [rankEq]
  exact then_congr fun tied =>
    compound_after4a_compare singleBonded leftStages rightStages descriptorMap unit readL readR
      isoL isoR leftWidth leftDepth rightWidth rightDepth dataL dataR (by
        rw [← dataL.aKey, ← dataR.aKey, rankEq]
        exact tied)

end Prior

end
end TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularSelection

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularSelection.retainedMolecularContextTree_references_eq_selection
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularSelection.exists_retainedMolecularContextTree_references_eq_selection
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularSelection.retainedMolecularStageReadingFacts
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularSelection.retainedMolecularCompound_independentReadback
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularSelection.compound_after4a_compare
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularSelection.retainedMolecularCompound_prior_compare
