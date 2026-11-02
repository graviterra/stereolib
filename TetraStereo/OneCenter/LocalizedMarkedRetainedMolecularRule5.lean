import TetraStereo.OneCenter.LocalizedRetainedContextRule5Comparison
import TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularSelection
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Through-Rule-5 compound order for any tetrahedral molecular reader

`retainedGeneratedCompound_throughRule5` identifies the actual through-Rule-5 callback on two
successful compounds with the comparison of the independent retained complete ligand keys, for
the generated reference state only. This module restates that chain for the molecular reader of
an arbitrary descriptor map with tetrahedral values at an arbitrary carrier target of a
simple-bonded certified input, so that it can be instantiated with a raw auxiliary state.

After the derived prior tie, each common `R`/`S` stream of the actual compound agrees with
`retainedCompleteRule5ReadingsAt`; the callback ordering is `compare` of
`retainedCompleteLigandRule5KeyAt`, and its pseudo flag is the strict reference-sensitive
disagreement of the two streams. Same-cursor stage isomorphisms are the only graph transport.
The private helper lemmas of the generated module are re-proved here. Nothing about which
descriptor map an evaluator state induces, and no four-ligand descriptor, is asserted.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularRule5

open CertifiedLocalizedCIPInput DeclarativeCIP LocalizedCumulativeDecoratedTree
open Rule4aTableBridge Rule5ObservationBridge OfficialSparseCanonicalVectorComparison
open RetainedContextCompoundComparison RetainedContextStereoReadback RetainedRule4aCanonicalBridge
open RetainedContextRule5Comparison LocalizedMarkedRetainedMolecularSelection
noncomputable section

variable {input : CertifiedLocalizedCIPInput}
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
  (singleBonded : input.moleculeGraph.SimpleBonded)
  (target : input.LocalizedRerootCursor (retainedCarrierFuel input))
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)

include tetrahedralMap singleBonded targetUnit

/-- The retained absolute stream on the actual Rule-4b graph represents the appended bits of
the Rule-4c key, for the molecular reader of any tetrahedral map. -/
theorem retainedMolecular_selectedRule5_represents
    (cursor : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (rootChild : cursor ∈ input.executableLocalizedRerootChildren target)
    (stages : input.RuleMajorContextStages (retainedCarrierFuel input)
      (input.localizedDependencyLabel target.occurrence
        (input.molecularView descriptorMap target.occurrence)) cursor)
    (reference common : RS) {W D : Nat}
    (width : (ruleMajorTreeGraph (stages.b reference).tree).width ≤ W)
    (depth : (ruleMajorTreeGraph (stages.b reference).tree).height ≤ D) :
    ∀ path, Certificate.CanonicalSphereKey.pathObservationOf W D
      (retainedCompleteRule5ReadingAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph (stages.b reference).tree) W D
        (some (senseOf reference)) (senseOf common)) path =
      bitObservable (common == reference) (stages.c reference).key path := by
  have trace := (stages.b reference).trace
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
  have child : (stages.b reference).tree.source ∈
      input.executableLocalizedRerootChildren target := by
    simpa only [(stages.b reference).sourceEq] using rootChild
  have hyp := retainedContextTreeRankReadback_of_molecularReader descriptorMap tetrahedralMap
    singleBonded target unit targetUnit (stages.b reference).tree realizes child
  let graph := ruleMajorTreeGraph (stages.b reference).tree
  let observe := retainedContextNodeObservation input.moleculeGraph graph unit
  have observations : RetainedArmObservation (stages.b reference).tree unit := by
    intro rule node actual lookup
    exact retainedDecoratedObservation_eq_arm singleBonded target unit targetUnit
      (stages.b reference).tree realizes child rule node actual lookup
  have mask := retainedRule4b_rule4abOnly_of_simpleBonded singleBonded descriptorMap unit graph
    (senseOf reference)
  have represented := (retainedContextTree_node_bridge4b (stages.b reference).tree observe
    observations
    { label := hyp.label, tetrahedral := hyp.tetrahedral, realAvailableOrRing := hyp.nodeStatus }
    mask width depth graph.root (stages.b reference).tree (stages.b reference).key trace
    (by
      change (stages.b reference).tree.decoratedSubtreeAt? [] = some (stages.b reference).tree
      rw [decoratedSubtreeAt?])).2.2
  intro path
  change Certificate.CanonicalSphereKey.pathObservationOf W D
    (mapObservationKey (absoluteRule5Label (senseOf reference) (senseOf common))
      (observedRule4bComponent graph observe
        (retainedReadingEvidence input.moleculeGraph descriptorMap unit graph (senseOf reference))
        W D graph.root)) path = _
  rw [pathObservationOf_mapObservationKey, represented path,
    stages.b_encoded4b_eq_c reference path]
  exact absolute_encoded4b
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace (stages.c reference).trace).tableMatch
    common path

theorem retainedMolecularCrossBranch_selected_rule5_compare
    (cursorL cursorR : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (childL : cursorL ∈ input.executableLocalizedRerootChildren target)
    (childR : cursorR ∈ input.executableLocalizedRerootChildren target)
    (leftStages : input.RuleMajorContextStages (retainedCarrierFuel input)
      (input.localizedDependencyLabel target.occurrence
        (input.molecularView descriptorMap target.occurrence)) cursorL)
    (rightStages : input.RuleMajorContextStages (retainedCarrierFuel input)
      (input.localizedDependencyLabel target.occurrence
        (input.molecularView descriptorMap target.occurrence)) cursorR)
    (isoL : RuleMajorContextStageGraphIsoBundle leftStages)
    (isoR : RuleMajorContextStageGraphIsoBundle rightStages)
    (leftReference rightReference common : RS) {W D : Nat}
    (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    (cTie : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      (leftStages.c leftReference).key.descriptor
      (rightStages.c rightReference).key.descriptor = .eq) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (input.rule5LiftKey (common == leftReference)
          (leftStages.c leftReference).key).descriptor
        (input.rule5LiftKey (common == rightReference)
          (rightStages.c rightReference).key).descriptor =
      compare
        (retainedCompleteRule5ReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph leftStages.a.tree) W D
          (some (senseOf leftReference)) (senseOf common))
        (retainedCompleteRule5ReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph rightStages.a.tree) W D
          (some (senseOf rightReference)) (senseOf common)) := by
  have cEq := (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mp cTie
  rw [compare_lifts_eq_bits _ _ _ _ cEq]
  have ties := contextCrossBranch_ties leftStages rightStages leftReference rightReference aTie
  have repL := retainedMolecular_selectedRule5_represents descriptorMap tetrahedralMap singleBonded
    target unit targetUnit cursorL childL leftStages leftReference common
    ((leftStages.b_width_le leftReference).trans leftWidth)
    ((leftStages.b_depth_le leftReference).trans leftDepth)
  have repR := retainedMolecular_selectedRule5_represents descriptorMap tetrahedralMap singleBonded
    target unit targetUnit cursorR childR rightStages rightReference common
    ((rightStages.b_width_le rightReference).trans rightWidth)
    ((rightStages.b_depth_le rightReference).trans rightDepth)
  rw [retainedRule5Reading_iso input.moleculeGraph descriptorMap unit (isoL.b leftReference)]
    at repL
  rw [retainedRule5Reading_iso input.moleculeGraph descriptorMap unit (isoR.b rightReference)]
    at repR
  have shapedL := mapObservationKey_wellShaped
    (absoluteRule5Label (senseOf leftReference) (senseOf common))
    (ordinaryKeyWithObservations_stereo_wellShaped (ruleMajorTreeGraph leftStages.a.tree)
      (retainedContextNodeObservation input.moleculeGraph
        (ruleMajorTreeGraph leftStages.a.tree) unit)
      (retainedReadingEvidence input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph leftStages.a.tree) (senseOf leftReference)) W D
      .rule4bLikeUnlikeDescriptorPairs (ruleMajorTreeGraph leftStages.a.tree).root)
  have shapedR := mapObservationKey_wellShaped
    (absoluteRule5Label (senseOf rightReference) (senseOf common))
    (ordinaryKeyWithObservations_stereo_wellShaped (ruleMajorTreeGraph rightStages.a.tree)
      (retainedContextNodeObservation input.moleculeGraph
        (ruleMajorTreeGraph rightStages.a.tree) unit)
      (retainedReadingEvidence input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph rightStages.a.tree) (senseOf rightReference)) W D
      .rule4bLikeUnlikeDescriptorPairs (ruleMajorTreeGraph rightStages.a.tree).root)
  exact compare_of_pathFirstDifference shapedL shapedR repL repR
    (fun outcome => bitTable_pathFirstDifference_iff
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace (leftStages.c leftReference).trace).tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace
        (rightStages.c rightReference).trace).tableMatch
      (LocalizedRuleMajorSortTrace.realizes_of_trace (leftStages.c leftReference).trace)
      (LocalizedRuleMajorSortTrace.realizes_of_trace (rightStages.c rightReference).trace)
      common (contextCompareNatLayers_eq_of_tie ties.cRule1a) outcome)

omit tetrahedralMap singleBonded targetUnit in
private theorem completeListTie_of_rule4b_rule4c_ties
    (left right : List input.LocalizedRerootRule4bcReading)
    (rule4bTie : input.compareLocalizedRerootCompoundRule4bReadings left right = .eq)
    (rule4cTie : input.compareLocalizedRerootCompoundRule4cReadings left right = .eq) :
    List.compareLex input.compareRule4bcReadingsComplete left right = .eq := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons y ys =>
          change List.compareLex input.compareLocalizedRerootRule4bcReadingsByRule4b []
              (y :: ys) = .eq at rule4bTie
          have impossible := List.compareLex_nil_left_eq_eq.mp rule4bTie
          cases impossible
  | cons x xs ih =>
      cases right with
      | nil =>
          change List.compareLex input.compareLocalizedRerootRule4bcReadingsByRule4b
              (x :: xs) [] = .eq at rule4bTie
          have impossible := List.compareLex_nil_right_eq_eq.mp rule4bTie
          cases impossible
      | cons y ys =>
          simp only [compareLocalizedRerootCompoundRule4bReadings,
            compareLocalizedRerootCompoundRule4cReadings,
            List.compareLex_cons_cons, Ordering.then_eq_eq] at rule4bTie rule4cTie
          have cHead : OfficialRuleMajorKey.compareSparseLayers
              compareLocalizedCumulativeRule45Priority
              x.rule4cKey.descriptor y.rule4cKey.descriptor = .eq := by
            simpa [Ordering.byKey] using rule4cTie.1
          have head : input.compareRule4bcReadingsComplete x y = .eq := by
            unfold compareRule4bcReadingsComplete
            rw [localizedCompareLex_eq_right_of_eq rule4bTie.1]
            exact cHead
          rw [List.compareLex_cons_cons, head, Ordering.eq_then]
          exact ih ys rule4bTie.2 rule4cTie.2

omit tetrahedralMap singleBonded targetUnit in
private theorem expectedRule5_descriptor (common : RS)
    (reading : input.LocalizedRerootRule4bcReading) :
    input.localizedRerootRule5Descriptor common
        (input.ruleMajorExpectedRule5Reading reading) =
      (input.rule5LiftKey
        (match reading.reference? with
          | none => false
          | some own => common == own) reading.rule4cKey).descriptor := by
  cases common <;> cases ref : reading.reference? with
  | none => simp [ruleMajorExpectedRule5Reading, localizedRerootRule5Descriptor, ref]
  | some own => cases own <;>
      simp [ruleMajorExpectedRule5Reading, localizedRerootRule5Descriptor, ref]

private theorem retainedMolecularRule5Pair_compare
    (cursorL cursorR : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (childL : cursorL ∈ input.executableLocalizedRerootChildren target)
    (childR : cursorR ∈ input.executableLocalizedRerootChildren target)
    (leftStages : input.RuleMajorContextStages (retainedCarrierFuel input)
      (input.localizedDependencyLabel target.occurrence
        (input.molecularView descriptorMap target.occurrence)) cursorL)
    (rightStages : input.RuleMajorContextStages (retainedCarrierFuel input)
      (input.localizedDependencyLabel target.occurrence
        (input.molecularView descriptorMap target.occurrence)) cursorR)
    (readL : RetainedStageReadingFacts leftStages descriptorMap unit)
    (readR : RetainedStageReadingFacts rightStages descriptorMap unit)
    (isoL : RuleMajorContextStageGraphIsoBundle leftStages)
    (isoR : RuleMajorContextStageGraphIsoBundle rightStages)
    {W D : Nat}
    {left right : input.LocalizedRerootCompoundRule45Key}
    (dataL : RetainedCompoundReadbackData leftStages descriptorMap unit left W D)
    (dataR : RetainedCompoundReadbackData rightStages descriptorMap unit right W D)
    (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    (countEq : left.prior.referenceCountPriority = right.prior.referenceCountPriority)
    (common : RS)
    (x : input.LocalizedRerootRule4bcReading) (hx : x ∈ left.prior.readings)
    (y : input.LocalizedRerootRule4bcReading) (hy : y ∈ right.prior.readings)
    (priorEq : input.compareRule4bcReadingsComplete x y = .eq) :
    Ordering.byKey
        (fun reading => input.localizedRerootRule5Descriptor common
          (input.ruleMajorExpectedRule5Reading reading))
        (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
        x y =
      compare
        (retainedCompleteRule5ReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph leftStages.a.tree) W D
          (x.reference?.map senseOf) (senseOf common))
        (retainedCompleteRule5ReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph rightStages.a.tree) W D
          (y.reference?.map senseOf) (senseOf common)) := by
  have countValues :
      (retainedReferenceSelection input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph leftStages.a.tree)).countPriority =
      (retainedReferenceSelection input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph rightStages.a.tree)).countPriority := by
    rw [← dataL.count, ← dataR.count]
    exact countEq
  have emptyIff := ReferenceSelection.empty_iff_of_countPriority_eq countValues
  have stagesL := dataL.readingStages x hx
  have stagesR := dataR.readingStages y hy
  have priorParts :
      input.compareLocalizedRerootRule4bcReadingsByRule4b x y = .eq ∧
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        x.rule4cKey.descriptor y.rule4cKey.descriptor = .eq := by
    unfold compareRule4bcReadingsComplete at priorEq
    cases hB : input.compareLocalizedRerootRule4bcReadingsByRule4b x y with
    | lt => simp [compareLex, hB] at priorEq
    | gt => simp [compareLex, hB] at priorEq
    | eq =>
        simp [compareLex, hB] at priorEq
        exact ⟨rfl, by simpa [Ordering.byKey, compareLex, hB] using priorEq⟩
  have compareDescriptor :
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (input.localizedRerootRule5Descriptor common
          (input.ruleMajorExpectedRule5Reading x))
        (input.localizedRerootRule5Descriptor common
          (input.ruleMajorExpectedRule5Reading y)) =
      compare
        (retainedCompleteRule5ReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph leftStages.a.tree) W D
          (x.reference?.map senseOf) (senseOf common))
        (retainedCompleteRule5ReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph rightStages.a.tree) W D
          (y.reference?.map senseOf) (senseOf common)) := by
    cases hxRef : x.reference? with
    | none =>
        have leftEmpty := (dataL.readingEmpty x hx).mp hxRef
        have rightEmpty := emptyIff.mp leftEmpty
        have hyRef : y.reference? = none := (dataR.readingEmpty y hy).mpr rightEmpty
        simp [hxRef] at stagesL
        simp [hyRef] at stagesR
        have cTie : OfficialRuleMajorKey.compareSparseLayers
            compareLocalizedCumulativeRule45Priority
            leftStages.noReference.key.descriptor rightStages.noReference.key.descriptor = .eq := by
          simpa [stagesL.2, stagesR.2] using priorParts.2
        have leftNoReference := stagesL.2
        have rightNoReference := stagesR.2
        have descriptorEq : leftStages.noReference.key.descriptor =
            rightStages.noReference.key.descriptor :=
          (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mp cTie
        have actualEq : OfficialRuleMajorKey.compareSparseLayers
            compareLocalizedCumulativeRule45Priority
            (input.rule5LiftKey false leftStages.noReference.key).descriptor
            (input.rule5LiftKey false rightStages.noReference.key).descriptor = .eq := by
          rw [compare_lifts_eq_bits false false leftStages.noReference.key
            rightStages.noReference.key descriptorEq]
          have bitEq : bitTable false leftStages.noReference.key =
              bitTable false rightStages.noReference.key := by
            simp [bitTable, descriptorEq]
          rw [bitEq]
          exact CompilerProjectionFidelity.compareSparseLayers_self
            OfficialRuleMajorKey.compareNat CompilerProjectionFidelity.compareNat_self _
        have independentCompare := retainedCrossBranch_noReference_compare singleBonded
          leftStages rightStages descriptorMap unit
          readL readR isoL isoR aTie leftWidth leftDepth rightWidth rightDepth
        have componentCompare :
            compare
              (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
                (ruleMajorTreeGraph leftStages.a.tree) W D none)).2
              (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
                (ruleMajorTreeGraph rightStages.a.tree) W D none)).2 = .eq :=
          independentCompare.symm.trans cTie
        have componentEq := (key_compare_eq_iff _ _).mp componentCompare
        have readingEq :
            retainedCompleteRule5ReadingAt input.moleculeGraph descriptorMap unit
              (ruleMajorTreeGraph leftStages.a.tree) W D none (senseOf common) =
            retainedCompleteRule5ReadingAt input.moleculeGraph descriptorMap unit
              (ruleMajorTreeGraph rightStages.a.tree) W D none (senseOf common) := by
          unfold retainedCompleteRule5ReadingAt
          rw [componentEq]
        have readingCompare : compare
            (retainedCompleteRule5ReadingAt input.moleculeGraph descriptorMap unit
              (ruleMajorTreeGraph leftStages.a.tree) W D none (senseOf common))
            (retainedCompleteRule5ReadingAt input.moleculeGraph descriptorMap unit
              (ruleMajorTreeGraph rightStages.a.tree) W D none (senseOf common)) = .eq := by
          rw [readingEq]
          exact Std.ReflCmp.compare_self
        rw [expectedRule5_descriptor common x, expectedRule5_descriptor common y,
          leftNoReference, rightNoReference, hxRef, hyRef]
        exact actualEq.trans readingCompare.symm
    | some ownL =>
        have rightNotEmpty :
            retainedReferenceSelection input.moleculeGraph descriptorMap unit
              (ruleMajorTreeGraph rightStages.a.tree) ≠ .empty := by
          intro hEmpty
          have leftEmpty := emptyIff.mpr hEmpty
          have leftReadingEmpty := (dataL.readingEmpty x hx).mpr leftEmpty
          simp [hxRef] at leftReadingEmpty
        cases hyRef : y.reference? with
        | none =>
            have rightEmpty := (dataR.readingEmpty y hy).mp hyRef
            exact (rightNotEmpty rightEmpty).elim
        | some ownR =>
            simp [hxRef] at stagesL
            simp [hyRef] at stagesR
            have cTie : OfficialRuleMajorKey.compareSparseLayers
                compareLocalizedCumulativeRule45Priority
                (leftStages.c ownL).key.descriptor (rightStages.c ownR).key.descriptor = .eq := by
              simpa [stagesL.2, stagesR.2] using priorParts.2
            rw [expectedRule5_descriptor common x, expectedRule5_descriptor common y,
              stagesL.2, stagesR.2, hxRef, hyRef]
            simpa only [Option.map_some] using
              retainedMolecularCrossBranch_selected_rule5_compare descriptorMap tetrahedralMap
                singleBonded target unit targetUnit cursorL cursorR childL childR leftStages
                rightStages isoL isoR ownL ownR common leftWidth leftDepth rightWidth rightDepth
                aTie cTie
  simpa only [Ordering.byKey] using compareDescriptor

/-- At a derived prior tie, the actual Rule-5 stream for either common sense agrees with the
retained stream. Empty, single, and both-reference populations are covered. -/
theorem retainedMolecularCompound_rule5Readings_compare
    (cursorL cursorR : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (childL : cursorL ∈ input.executableLocalizedRerootChildren target)
    (childR : cursorR ∈ input.executableLocalizedRerootChildren target)
    (leftStages : input.RuleMajorContextStages (retainedCarrierFuel input)
      (input.localizedDependencyLabel target.occurrence
        (input.molecularView descriptorMap target.occurrence)) cursorL)
    (rightStages : input.RuleMajorContextStages (retainedCarrierFuel input)
      (input.localizedDependencyLabel target.occurrence
        (input.molecularView descriptorMap target.occurrence)) cursorR)
    {W D : Nat}
    (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)
    {left right : input.LocalizedRerootCompoundRule45Key}
    (builtL : input.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
      (input.molecularView descriptorMap target.occurrence)
      (2 * (retainedCarrierFuel input + 1)) cursorL = some left)
    (builtR : input.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
      (input.molecularView descriptorMap target.occurrence)
      (2 * (retainedCarrierFuel input + 1)) cursorR = some right)
    (priorTie : input.compareLocalizedRerootCompoundRule4bcKeys
      left.prior right.prior = .eq) (common : RS) :
    input.compareLocalizedRerootCompoundRule5Readings common
        left.rule5Readings right.rule5Readings =
      compare
        (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph leftStages.a.tree) W D (senseOf common))
        (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph rightStages.a.tree) W D (senseOf common)) := by
  let view := input.molecularView descriptorMap target.occurrence
  let read := input.localizedDependencyLabel target.occurrence view
  let fuel := 2 * (retainedCarrierFuel input + 1)
  have uniformBuiltL : input.buildRuleMajorCompoundRule45KeyWith?
      (fun stage position => input.buildRuleMajorCumulativeWithRead? stage read fuel
        position) cursorL = some left := by
    rw [← input.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
    rw [← input.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact builtL
  have uniformBuiltR : input.buildRuleMajorCompoundRule45KeyWith?
      (fun stage position => input.buildRuleMajorCumulativeWithRead? stage read fuel
        position) cursorR = some right := by
    rw [← input.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
    rw [← input.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact builtR
  let dataL := retainedMolecularCompound_independentReadback descriptorMap tetrahedralMap
    singleBonded target unit targetUnit cursorL childL leftStages leftWidth leftDepth builtL
  let dataR := retainedMolecularCompound_independentReadback descriptorMap tetrahedralMap
    singleBonded target unit targetUnit cursorR childR rightStages rightWidth rightDepth builtR
  let readL := retainedMolecularStageReadingFacts descriptorMap tetrahedralMap singleBonded target
    unit targetUnit cursorL childL leftStages
  let readR := retainedMolecularStageReadingFacts descriptorMap tetrahedralMap singleBonded target
    unit targetUnit cursorR childR rightStages
  let isoL := ruleMajorContextStageGraphIsoBundle_of_stages leftStages
  let isoR := ruleMajorContextStageGraphIsoBundle_of_stages rightStages
  have tieFacts := (input.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
    left.prior right.prior).mp priorTie
  have aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq := by
    rw [← dataL.aKey, ← dataR.aKey]
    exact tieFacts.1
  have countTie : left.prior.referenceCountPriority = right.prior.referenceCountPriority :=
    compare_eq_iff_eq.mp tieFacts.2.1
  have priorListTie := completeListTie_of_rule4b_rule4c_ties
    left.prior.readings right.prior.readings tieFacts.2.2.1 tieFacts.2.2.2
  have rule5ReadbackL := input.contextStages_compound_rule5Readings_eq_map
    leftStages uniformBuiltL
  have rule5ReadbackR := input.contextStages_compound_rule5Readings_eq_map
    rightStages uniformBuiltR
  have priorTagsL : left.prior.readings.map
      (fun reading => reading.reference?.map senseOf) =
      retainedTaggedAlternativeReferencesAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph leftStages.a.tree) W D := by
    calc
      _ = left.rule5Readings.map
          (fun reading => reading.prior.reference?.map senseOf) := by
            rw [rule5ReadbackL]
            simp [ruleMajorExpectedRule5Reading]
      _ = _ := dataL.tags
  have priorTagsR : right.prior.readings.map
      (fun reading => reading.reference?.map senseOf) =
      retainedTaggedAlternativeReferencesAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph rightStages.a.tree) W D := by
    calc
      _ = right.rule5Readings.map
          (fun reading => reading.prior.reference?.map senseOf) := by
            rw [rule5ReadbackR]
            simp [ruleMajorExpectedRule5Reading]
      _ = _ := dataR.tags
  let expectedCmp := Ordering.byKey (fun reading =>
      input.localizedRerootRule5Descriptor common
        (input.ruleMajorExpectedRule5Reading reading))
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
  let mappedCmp := Ordering.byKey (input.localizedRerootRule5Descriptor common)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
  have mappedExpected : List.compareLex mappedCmp
      (left.prior.readings.map input.ruleMajorExpectedRule5Reading)
      (right.prior.readings.map input.ruleMajorExpectedRule5Reading) =
      List.compareLex expectedCmp left.prior.readings right.prior.readings := by
    exact compareLex_map_rel expectedCmp mappedCmp input.ruleMajorExpectedRule5Reading
      (by intro x y; rfl) _ _
  let observeL := fun reading : input.LocalizedRerootRule4bcReading =>
    retainedCompleteRule5ReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph leftStages.a.tree) W D
      (reading.reference?.map senseOf) (senseOf common)
  let observeR := fun reading : input.LocalizedRerootRule4bcReading =>
    retainedCompleteRule5ReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph rightStages.a.tree) W D
      (reading.reference?.map senseOf) (senseOf common)
  have tiedMap := compareLex_map_eq_of_prior_tie
    input.compareRule4bcReadingsComplete expectedCmp compare observeL observeR
    left.prior.readings right.prior.readings
    (fun x hx y hy priorEq => retainedMolecularRule5Pair_compare descriptorMap tetrahedralMap
      singleBonded target unit targetUnit cursorL cursorR childL childR leftStages rightStages
      readL readR isoL isoR dataL dataR leftWidth leftDepth rightWidth rightDepth aTie countTie
      common x hx y hy priorEq)
    priorListTie
  have mappedL : left.prior.readings.map observeL =
      retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph leftStages.a.tree) W D (senseOf common) := by
    unfold retainedCompleteRule5ReadingsAt
    rw [← priorTagsL]
    simp only [observeL, List.map_map, Function.comp_def]
  have mappedR : right.prior.readings.map observeR =
      retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph rightStages.a.tree) W D (senseOf common) := by
    unfold retainedCompleteRule5ReadingsAt
    rw [← priorTagsR]
    simp only [observeR, List.map_map, Function.comp_def]
  calc
    input.compareLocalizedRerootCompoundRule5Readings common
        left.rule5Readings right.rule5Readings =
      List.compareLex mappedCmp
        (left.prior.readings.map input.ruleMajorExpectedRule5Reading)
        (right.prior.readings.map input.ruleMajorExpectedRule5Reading) := by
          rw [rule5ReadbackL, rule5ReadbackR]
          rfl
    _ = List.compareLex expectedCmp left.prior.readings right.prior.readings := mappedExpected
    _ = List.compareLex compare
        (left.prior.readings.map observeL) (right.prior.readings.map observeR) := tiedMap
    _ = compare
        (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph leftStages.a.tree) W D (senseOf common))
        (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph rightStages.a.tree) W D (senseOf common)) := by
            simp only [List.compare_eq_compareLex]
            rw [mappedL, mappedR]

/-- **Actual through-Rule-5 callback agrees with the retained complete ligand key**, for the
molecular reader of any tetrahedral map at any carrier target of a simple-bonded input. The
ordering uses the senior stream only after the derived prior tie. The pseudo flag is that same
strict decision's disagreement with the junior stream. -/
theorem retainedMolecularCompound_throughRule5
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
    let result := input.compareLocalizedRerootCompoundThroughRule5 left right
    let graphL := ruleMajorTreeGraph leftStages.a.tree
    let graphR := ruleMajorTreeGraph rightStages.a.tree
    result.ordering =
      compare (retainedCompleteLigandRule5KeyAt input.moleculeGraph descriptorMap unit
          graphL W D)
        (retainedCompleteLigandRule5KeyAt input.moleculeGraph descriptorMap unit
          graphR W D) ∧
    (result.pseudo = true ↔
      compare (retainedCompleteLigandPriorKeyAt input.moleculeGraph descriptorMap unit
          graphL W D)
        (retainedCompleteLigandPriorKeyAt input.moleculeGraph descriptorMap unit
          graphR W D) = .eq ∧
      compare (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
          graphL W D .senior)
        (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
          graphR W D .senior) ≠ .eq ∧
      compare (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
          graphL W D .senior)
        (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
          graphR W D .senior) ≠
        compare (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
            graphL W D .junior)
          (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
            graphR W D .junior)) := by
  let graphL := ruleMajorTreeGraph leftStages.a.tree
  let graphR := ruleMajorTreeGraph rightStages.a.tree
  have priorAgreement := retainedMolecularCompound_prior_compare descriptorMap tetrahedralMap
    singleBonded target unit targetUnit cursorL cursorR childL childR leftStages rightStages
    leftWidth leftDepth rightWidth rightDepth builtL builtR
  have ordering :
      (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering =
        compare (retainedCompleteLigandRule5KeyAt input.moleculeGraph descriptorMap unit
            graphL W D)
          (retainedCompleteLigandRule5KeyAt input.moleculeGraph descriptorMap unit
            graphR W D) := by
    have actualThen :
        (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering =
          (input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior).then
            (input.compareLocalizedRerootCompoundRule5Readings .R
              left.rule5Readings right.rule5Readings) := by
      rw [input.compareLocalizedRerootCompoundThroughRule5_ordering]
      rfl
    rw [actualThen, retainedCompleteLigandRule5KeyAt_compare_eq_then, ← priorAgreement]
    apply then_congr
    intro priorTie
    have actualPriorTie :
        input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior = .eq :=
      priorAgreement.symm ▸ priorTie
    simpa [senseOf] using retainedMolecularCompound_rule5Readings_compare descriptorMap
      tetrahedralMap singleBonded target unit targetUnit cursorL cursorR childL childR leftStages
      rightStages leftWidth leftDepth rightWidth rightDepth builtL builtR actualPriorTie .R
  refine ⟨ordering, ?_⟩
  unfold compareLocalizedRerootCompoundThroughRule5
  rw [priorAgreement]
  cases hp : compare
      (retainedCompleteLigandPriorKeyAt input.moleculeGraph descriptorMap unit graphL W D)
      (retainedCompleteLigandPriorKeyAt input.moleculeGraph descriptorMap unit graphR W D) with
  | lt => clear hp; simp
  | gt => clear hp; simp
  | eq =>
      have actualPriorTie :
          input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior = .eq := by
        rw [priorAgreement, hp]
      have senior := retainedMolecularCompound_rule5Readings_compare descriptorMap tetrahedralMap
        singleBonded target unit targetUnit cursorL cursorR childL childR leftStages rightStages
        leftWidth leftDepth rightWidth rightDepth builtL builtR actualPriorTie .R
      have junior := retainedMolecularCompound_rule5Readings_compare descriptorMap tetrahedralMap
        singleBonded target unit targetUnit cursorL cursorR childL childR leftStages rightStages
        leftWidth leftDepth rightWidth rightDepth builtL builtR actualPriorTie .S
      simp only [senseOf] at senior junior
      rw [senior, junior]
      cases hr : compare
          (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit graphL W D
            .senior)
          (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit graphR W D
            .senior) with
      | lt =>
          cases hs : compare
              (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
                graphL W D .junior)
              (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
                graphR W D .junior) <;> (clear hp; clear hr; clear hs; simp)
      | gt =>
          cases hs : compare
              (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
                graphL W D .junior)
              (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
                graphR W D .junior) <;> (clear hp; clear hr; clear hs; simp)
      | eq =>
          cases hs : compare
              (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
                graphL W D .junior)
              (retainedCompleteRule5ReadingsAt input.moleculeGraph descriptorMap unit
                graphR W D .junior) <;> (clear hp; clear hr; clear hs; simp)

end
end TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularRule5

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularRule5.retainedMolecular_selectedRule5_represents
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularRule5.retainedMolecularCrossBranch_selected_rule5_compare
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularRule5.retainedMolecularCompound_rule5Readings_compare
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularRule5.retainedMolecularCompound_throughRule5
