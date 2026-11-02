import TetraStereo.OneCenter.DeclarativeCIPAbsoluteRule5Reading
import TetraStereo.OneCenter.LocalizedActualRule4aTableBridge
import TetraStereo.OneCenter.LocalizedContextAbsoluteRule5Readback
import TetraStereo.OneCenter.LocalizedRetainedContextCompoundComparison
import TetraStereo.OneCenter.LocalizedRuleMajorRule5Observation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! Actual through-Rule-5 comparison for simple-bonded cyclic inputs.

After the retained prior tie, each common R/S stream agrees with
`retainedCompleteRule5ReadingsAt`. The callback ordering is
`compare (retainedCompleteLigandRule5KeyAt …)`. Its pseudo flag is the strict
reference-sensitive disagreement of those two streams. Same-cursor stage
isomorphisms are the only graph transport. This does not assemble a four-ligand
descriptor, and it does not assume a physical cut-arm expansion. -/

namespace TetraStereo.OneCenter.RetainedContextRule5Comparison
universe u
open CertifiedLocalizedCIPInput DeclarativeCIP LocalizedCumulativeDecoratedTree
open Rule4aTableBridge Rule5ObservationBridge OfficialSparseCanonicalVectorComparison
open RetainedContextCompoundComparison RetainedContextStereoReadback RetainedRule4aCanonicalBridge
noncomputable section

theorem retainedRule5Reading_iso {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) {left right : RootedDigraph Atom}
    (iso : RootedDigraph.Iso left right) (W D : Nat)
    (reference : Option DescriptorSense) (common : DescriptorSense) :
    retainedCompleteRule5ReadingAt molecule descriptorMap unit right W D reference common =
      retainedCompleteRule5ReadingAt molecule descriptorMap unit left W D reference common := by
  cases reference with
  | none =>
      simp only [retainedCompleteRule5ReadingAt]
      rw [retainedCompleteReadingAt_iso molecule descriptorMap unit iso W D none]
  | some own =>
      simp only [retainedCompleteRule5ReadingAt]
      rw [retainedCompleteReadingAt_iso molecule descriptorMap unit iso W D (some own)]

/-- The retained absolute stream on the actual Rule-4b graph represents the appended bits of
the Rule-4c key. Ring duplicates stay in the retained rank bundle. -/
theorem retainedGenerated_selectedRule5_represents
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (rootChild : cursor ∈ input.certified.executableLocalizedRerootChildren target)
    (stages : input.certified.RuleMajorContextStages
      (LocalizedRuleMajorReference.carrierFuel input)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursor)
    (reference common : RS) {W D : Nat}
    (width : (ruleMajorTreeGraph (stages.b reference).tree).width ≤ W)
    (depth : (ruleMajorTreeGraph (stages.b reference).tree).height ≤ D) :
    ∀ path, Certificate.CanonicalSphereKey.pathObservationOf W D
      (retainedCompleteRule5ReadingAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph (stages.b reference).tree) W D
        (some (senseOf reference)) (senseOf common)) path =
      bitObservable (common == reference) (stages.c reference).key path := by
  have trace := (stages.b reference).trace
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
  have child : (stages.b reference).tree.source ∈
      input.certified.executableLocalizedRerootChildren target := by
    simpa only [(stages.b reference).sourceEq] using rootChild
  have hyp := retainedGeneratedContextTreeRankReadback input singleBonded target unit targetUnit
    (stages.b reference).tree realizes child
  let graph := ruleMajorTreeGraph (stages.b reference).tree
  let observe := retainedContextNodeObservation input.certified.moleculeGraph graph unit
  have observations : RetainedArmObservation (stages.b reference).tree unit := by
    intro rule node actual lookup
    exact retainedDecoratedObservation_eq_arm singleBonded target unit targetUnit
      (stages.b reference).tree realizes child rule node actual lookup
  have mask := retainedRule4b_rule4abOnly_of_simpleBonded singleBonded
    (LocalizedRuleMajorReference.descriptorMap input) unit graph (senseOf reference)
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
        (retainedReadingEvidence input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit graph (senseOf reference))
        W D graph.root)) path = _
  rw [pathObservationOf_mapObservationKey, represented path,
    stages.b_encoded4b_eq_c reference path]
  exact absolute_encoded4b
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace (stages.c reference).trace).tableMatch
    common path

theorem retainedCrossBranch_selected_rule5_compare
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursorL cursorR : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (childL : cursorL ∈ input.certified.executableLocalizedRerootChildren target)
    (childR : cursorR ∈ input.certified.executableLocalizedRerootChildren target)
    (leftStages : input.certified.RuleMajorContextStages
      (LocalizedRuleMajorReference.carrierFuel input)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursorL)
    (rightStages : input.certified.RuleMajorContextStages
      (LocalizedRuleMajorReference.carrierFuel input)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursorR)
    (isoL : RuleMajorContextStageGraphIsoBundle leftStages)
    (isoR : RuleMajorContextStageGraphIsoBundle rightStages)
    (leftReference rightReference common : RS) {W D : Nat}
    (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)
    (aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    (cTie : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      (leftStages.c leftReference).key.descriptor
      (rightStages.c rightReference).key.descriptor = .eq) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (input.certified.rule5LiftKey (common == leftReference)
          (leftStages.c leftReference).key).descriptor
        (input.certified.rule5LiftKey (common == rightReference)
          (rightStages.c rightReference).key).descriptor =
      compare
        (retainedCompleteRule5ReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph leftStages.a.tree) W D
          (some (senseOf leftReference)) (senseOf common))
        (retainedCompleteRule5ReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph rightStages.a.tree) W D
          (some (senseOf rightReference)) (senseOf common)) := by
  have cEq := (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mp cTie
  rw [compare_lifts_eq_bits _ _ _ _ cEq]
  have ties := contextCrossBranch_ties leftStages rightStages leftReference rightReference aTie
  have repL := retainedGenerated_selectedRule5_represents input singleBonded target unit targetUnit
    cursorL childL leftStages leftReference common
    ((leftStages.b_width_le leftReference).trans leftWidth)
    ((leftStages.b_depth_le leftReference).trans leftDepth)
  have repR := retainedGenerated_selectedRule5_represents input singleBonded target unit targetUnit
    cursorR childR rightStages rightReference common
    ((rightStages.b_width_le rightReference).trans rightWidth)
    ((rightStages.b_depth_le rightReference).trans rightDepth)
  rw [retainedRule5Reading_iso input.certified.moleculeGraph
    (LocalizedRuleMajorReference.descriptorMap input) unit (isoL.b leftReference)] at repL
  rw [retainedRule5Reading_iso input.certified.moleculeGraph
    (LocalizedRuleMajorReference.descriptorMap input) unit (isoR.b rightReference)] at repR
  have shapedL := mapObservationKey_wellShaped
    (absoluteRule5Label (senseOf leftReference) (senseOf common))
    (ordinaryKeyWithObservations_stereo_wellShaped (ruleMajorTreeGraph leftStages.a.tree)
      (retainedContextNodeObservation input.certified.moleculeGraph
        (ruleMajorTreeGraph leftStages.a.tree) unit)
      (retainedReadingEvidence input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph leftStages.a.tree) (senseOf leftReference)) W D
      .rule4bLikeUnlikeDescriptorPairs (ruleMajorTreeGraph leftStages.a.tree).root)
  have shapedR := mapObservationKey_wellShaped
    (absoluteRule5Label (senseOf rightReference) (senseOf common))
    (ordinaryKeyWithObservations_stereo_wellShaped (ruleMajorTreeGraph rightStages.a.tree)
      (retainedContextNodeObservation input.certified.moleculeGraph
        (ruleMajorTreeGraph rightStages.a.tree) unit)
      (retainedReadingEvidence input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
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

private theorem completeListTie_of_rule4b_rule4c_ties
    {input : CertifiedLocalizedCIPInput}
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

private theorem expectedRule5_descriptor
    {input : CertifiedLocalizedCIPInput} (common : RS)
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

private theorem retainedRule5Pair_compare
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursorL cursorR : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (childL : cursorL ∈ input.certified.executableLocalizedRerootChildren target)
    (childR : cursorR ∈ input.certified.executableLocalizedRerootChildren target)
    (leftStages : input.certified.RuleMajorContextStages
      (LocalizedRuleMajorReference.carrierFuel input)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursorL)
    (rightStages : input.certified.RuleMajorContextStages
      (LocalizedRuleMajorReference.carrierFuel input)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursorR)
    (readL : RetainedStageReadingFacts leftStages
      (LocalizedRuleMajorReference.descriptorMap input) unit)
    (readR : RetainedStageReadingFacts rightStages
      (LocalizedRuleMajorReference.descriptorMap input) unit)
    (isoL : RuleMajorContextStageGraphIsoBundle leftStages)
    (isoR : RuleMajorContextStageGraphIsoBundle rightStages)
    {W D : Nat}
    {left right : input.certified.LocalizedRerootCompoundRule45Key}
    (dataL : RetainedCompoundReadbackData leftStages
      (LocalizedRuleMajorReference.descriptorMap input) unit left W D)
    (dataR : RetainedCompoundReadbackData rightStages
      (LocalizedRuleMajorReference.descriptorMap input) unit right W D)
    (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)
    (aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    (countEq : left.prior.referenceCountPriority = right.prior.referenceCountPriority)
    (common : RS)
    (x : input.certified.LocalizedRerootRule4bcReading) (hx : x ∈ left.prior.readings)
    (y : input.certified.LocalizedRerootRule4bcReading) (hy : y ∈ right.prior.readings)
    (priorEq : input.certified.compareRule4bcReadingsComplete x y = .eq) :
    Ordering.byKey
        (fun reading => input.certified.localizedRerootRule5Descriptor common
          (input.certified.ruleMajorExpectedRule5Reading reading))
        (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
        x y =
      compare
        (retainedCompleteRule5ReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph leftStages.a.tree) W D
          (x.reference?.map senseOf) (senseOf common))
        (retainedCompleteRule5ReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph rightStages.a.tree) W D
          (y.reference?.map senseOf) (senseOf common)) := by
  have countValues :
      (retainedReferenceSelection input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph leftStages.a.tree)).countPriority =
      (retainedReferenceSelection input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph rightStages.a.tree)).countPriority := by
    rw [← dataL.count, ← dataR.count]
    exact countEq
  have emptyIff := ReferenceSelection.empty_iff_of_countPriority_eq countValues
  have stagesL := dataL.readingStages x hx
  have stagesR := dataR.readingStages y hy
  have priorParts :
      input.certified.compareLocalizedRerootRule4bcReadingsByRule4b x y = .eq ∧
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        x.rule4cKey.descriptor y.rule4cKey.descriptor = .eq := by
    unfold compareRule4bcReadingsComplete at priorEq
    cases hB : input.certified.compareLocalizedRerootRule4bcReadingsByRule4b x y with
    | lt => simp [compareLex, hB] at priorEq
    | gt => simp [compareLex, hB] at priorEq
    | eq =>
        simp [compareLex, hB] at priorEq
        exact ⟨rfl, by simpa [Ordering.byKey, compareLex, hB] using priorEq⟩
  have compareDescriptor :
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (input.certified.localizedRerootRule5Descriptor common
          (input.certified.ruleMajorExpectedRule5Reading x))
        (input.certified.localizedRerootRule5Descriptor common
          (input.certified.ruleMajorExpectedRule5Reading y)) =
      compare
        (retainedCompleteRule5ReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph leftStages.a.tree) W D
          (x.reference?.map senseOf) (senseOf common))
        (retainedCompleteRule5ReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
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
            (input.certified.rule5LiftKey false leftStages.noReference.key).descriptor
            (input.certified.rule5LiftKey false rightStages.noReference.key).descriptor = .eq := by
          rw [compare_lifts_eq_bits false false leftStages.noReference.key
            rightStages.noReference.key descriptorEq]
          have bitEq : bitTable false leftStages.noReference.key =
              bitTable false rightStages.noReference.key := by
            simp [bitTable, descriptorEq]
          rw [bitEq]
          exact CompilerProjectionFidelity.compareSparseLayers_self
            OfficialRuleMajorKey.compareNat CompilerProjectionFidelity.compareNat_self _
        have independentCompare := retainedCrossBranch_noReference_compare singleBonded
          leftStages rightStages (LocalizedRuleMajorReference.descriptorMap input) unit
          readL readR isoL isoR aTie leftWidth leftDepth rightWidth rightDepth
        have componentCompare :
            compare
              (ofLex (retainedCompleteReadingAt input.certified.moleculeGraph
                (LocalizedRuleMajorReference.descriptorMap input) unit
                (ruleMajorTreeGraph leftStages.a.tree) W D none)).2
              (ofLex (retainedCompleteReadingAt input.certified.moleculeGraph
                (LocalizedRuleMajorReference.descriptorMap input) unit
                (ruleMajorTreeGraph rightStages.a.tree) W D none)).2 = .eq :=
          independentCompare.symm.trans cTie
        have componentEq := (key_compare_eq_iff _ _).mp componentCompare
        have readingEq :
            retainedCompleteRule5ReadingAt input.certified.moleculeGraph
              (LocalizedRuleMajorReference.descriptorMap input) unit
              (ruleMajorTreeGraph leftStages.a.tree) W D none (senseOf common) =
            retainedCompleteRule5ReadingAt input.certified.moleculeGraph
              (LocalizedRuleMajorReference.descriptorMap input) unit
              (ruleMajorTreeGraph rightStages.a.tree) W D none (senseOf common) := by
          unfold retainedCompleteRule5ReadingAt
          rw [componentEq]
        have readingCompare : compare
            (retainedCompleteRule5ReadingAt input.certified.moleculeGraph
              (LocalizedRuleMajorReference.descriptorMap input) unit
              (ruleMajorTreeGraph leftStages.a.tree) W D none (senseOf common))
            (retainedCompleteRule5ReadingAt input.certified.moleculeGraph
              (LocalizedRuleMajorReference.descriptorMap input) unit
              (ruleMajorTreeGraph rightStages.a.tree) W D none (senseOf common)) = .eq := by
          rw [readingEq]
          exact Std.ReflCmp.compare_self
        rw [expectedRule5_descriptor common x, expectedRule5_descriptor common y,
          leftNoReference, rightNoReference, hxRef, hyRef]
        exact actualEq.trans readingCompare.symm
    | some ownL =>
        have rightNotEmpty :
            retainedReferenceSelection input.certified.moleculeGraph
              (LocalizedRuleMajorReference.descriptorMap input) unit
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
              retainedCrossBranch_selected_rule5_compare input singleBonded target unit targetUnit
                cursorL cursorR childL childR leftStages rightStages isoL isoR ownL ownR common
                leftWidth leftDepth rightWidth rightDepth aTie cTie
  simpa only [Ordering.byKey] using compareDescriptor

/-- At a derived prior tie, the actual Rule-5 stream for either common sense agrees with the
retained stream. Empty, single, and both-reference populations are covered. -/
theorem retainedGeneratedCompound_rule5Readings_compare
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursorL cursorR : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (childL : cursorL ∈ input.certified.executableLocalizedRerootChildren target)
    (childR : cursorR ∈ input.certified.executableLocalizedRerootChildren target)
    (leftStages : input.certified.RuleMajorContextStages
      (LocalizedRuleMajorReference.carrierFuel input)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursorL)
    (rightStages : input.certified.RuleMajorContextStages
      (LocalizedRuleMajorReference.carrierFuel input)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursorR)
    {W D : Nat}
    (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)
    {left right : input.certified.LocalizedRerootCompoundRule45Key}
    (builtL : input.certified.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)
      (2 * (LocalizedRuleMajorReference.carrierFuel input + 1)) cursorL = some left)
    (builtR : input.certified.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)
      (2 * (LocalizedRuleMajorReference.carrierFuel input + 1)) cursorR = some right)
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      left.prior right.prior = .eq) (common : RS) :
    input.certified.compareLocalizedRerootCompoundRule5Readings common
        left.rule5Readings right.rule5Readings =
      compare
        (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph leftStages.a.tree) W D (senseOf common))
        (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph rightStages.a.tree) W D (senseOf common)) := by
  let view := input.certified.localizedDependencyView
    (LocalizedRuleMajorReference.referenceState input) target.occurrence
  let read := input.certified.localizedDependencyLabel target.occurrence view
  let fuel := 2 * (LocalizedRuleMajorReference.carrierFuel input + 1)
  have uniformBuiltL : input.certified.buildRuleMajorCompoundRule45KeyWith?
      (fun stage position => input.certified.buildRuleMajorCumulativeWithRead? stage read fuel
        position) cursorL = some left := by
    rw [← input.certified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
    rw [← input.certified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact builtL
  have uniformBuiltR : input.certified.buildRuleMajorCompoundRule45KeyWith?
      (fun stage position => input.certified.buildRuleMajorCumulativeWithRead? stage read fuel
        position) cursorR = some right := by
    rw [← input.certified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
    rw [← input.certified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact builtR
  let dataL := retainedGeneratedCompound_independentReadback input singleBonded target unit
    targetUnit cursorL childL leftStages leftWidth leftDepth builtL
  let dataR := retainedGeneratedCompound_independentReadback input singleBonded target unit
    targetUnit cursorR childR rightStages rightWidth rightDepth builtR
  let readL := retainedGeneratedStageReadingFacts input singleBonded target unit targetUnit
    cursorL childL leftStages
  let readR := retainedGeneratedStageReadingFacts input singleBonded target unit targetUnit
    cursorR childR rightStages
  let isoL := ruleMajorContextStageGraphIsoBundle_of_stages leftStages
  let isoR := ruleMajorContextStageGraphIsoBundle_of_stages rightStages
  have tieFacts := (input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
    left.prior right.prior).mp priorTie
  have aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq := by
    rw [← dataL.aKey, ← dataR.aKey]
    exact tieFacts.1
  have countTie : left.prior.referenceCountPriority = right.prior.referenceCountPriority :=
    compare_eq_iff_eq.mp tieFacts.2.1
  have priorListTie := completeListTie_of_rule4b_rule4c_ties
    left.prior.readings right.prior.readings tieFacts.2.2.1 tieFacts.2.2.2
  have rule5ReadbackL := input.certified.contextStages_compound_rule5Readings_eq_map
    leftStages uniformBuiltL
  have rule5ReadbackR := input.certified.contextStages_compound_rule5Readings_eq_map
    rightStages uniformBuiltR
  have priorTagsL : left.prior.readings.map
      (fun reading => reading.reference?.map senseOf) =
      retainedTaggedAlternativeReferencesAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph leftStages.a.tree) W D := by
    calc
      _ = left.rule5Readings.map
          (fun reading => reading.prior.reference?.map senseOf) := by
            rw [rule5ReadbackL]
            simp [ruleMajorExpectedRule5Reading]
      _ = _ := dataL.tags
  have priorTagsR : right.prior.readings.map
      (fun reading => reading.reference?.map senseOf) =
      retainedTaggedAlternativeReferencesAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph rightStages.a.tree) W D := by
    calc
      _ = right.rule5Readings.map
          (fun reading => reading.prior.reference?.map senseOf) := by
            rw [rule5ReadbackR]
            simp [ruleMajorExpectedRule5Reading]
      _ = _ := dataR.tags
  let expectedCmp := Ordering.byKey (fun reading =>
      input.certified.localizedRerootRule5Descriptor common
        (input.certified.ruleMajorExpectedRule5Reading reading))
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
  let mappedCmp := Ordering.byKey (input.certified.localizedRerootRule5Descriptor common)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
  have mappedExpected : List.compareLex mappedCmp
      (left.prior.readings.map input.certified.ruleMajorExpectedRule5Reading)
      (right.prior.readings.map input.certified.ruleMajorExpectedRule5Reading) =
      List.compareLex expectedCmp left.prior.readings right.prior.readings := by
    exact compareLex_map_rel expectedCmp mappedCmp input.certified.ruleMajorExpectedRule5Reading
      (by intro x y; rfl) _ _
  let observeL := fun reading : input.certified.LocalizedRerootRule4bcReading =>
    retainedCompleteRule5ReadingAt input.certified.moleculeGraph
      (LocalizedRuleMajorReference.descriptorMap input) unit
      (ruleMajorTreeGraph leftStages.a.tree) W D
      (reading.reference?.map senseOf) (senseOf common)
  let observeR := fun reading : input.certified.LocalizedRerootRule4bcReading =>
    retainedCompleteRule5ReadingAt input.certified.moleculeGraph
      (LocalizedRuleMajorReference.descriptorMap input) unit
      (ruleMajorTreeGraph rightStages.a.tree) W D
      (reading.reference?.map senseOf) (senseOf common)
  have tiedMap := compareLex_map_eq_of_prior_tie
    input.certified.compareRule4bcReadingsComplete expectedCmp compare observeL observeR
    left.prior.readings right.prior.readings
    (fun x hx y hy priorEq => retainedRule5Pair_compare input singleBonded target unit targetUnit
      cursorL cursorR childL childR leftStages rightStages readL readR isoL isoR dataL dataR
      leftWidth leftDepth rightWidth rightDepth aTie countTie common x hx y hy priorEq)
    priorListTie
  have mappedL : left.prior.readings.map observeL =
      retainedCompleteRule5ReadingsAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph leftStages.a.tree) W D (senseOf common) := by
    unfold retainedCompleteRule5ReadingsAt
    rw [← priorTagsL]
    simp only [observeL, List.map_map, Function.comp_def]
  have mappedR : right.prior.readings.map observeR =
      retainedCompleteRule5ReadingsAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph rightStages.a.tree) W D (senseOf common) := by
    unfold retainedCompleteRule5ReadingsAt
    rw [← priorTagsR]
    simp only [observeR, List.map_map, Function.comp_def]
  calc
    input.certified.compareLocalizedRerootCompoundRule5Readings common
        left.rule5Readings right.rule5Readings =
      List.compareLex mappedCmp
        (left.prior.readings.map input.certified.ruleMajorExpectedRule5Reading)
        (right.prior.readings.map input.certified.ruleMajorExpectedRule5Reading) := by
          rw [rule5ReadbackL, rule5ReadbackR]
          rfl
    _ = List.compareLex expectedCmp left.prior.readings right.prior.readings := mappedExpected
    _ = List.compareLex compare
        (left.prior.readings.map observeL) (right.prior.readings.map observeR) := tiedMap
    _ = compare
        (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph leftStages.a.tree) W D (senseOf common))
        (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph rightStages.a.tree) W D (senseOf common)) := by
            simp only [List.compare_eq_compareLex]
            rw [mappedL, mappedR]

/-- Actual through-Rule-5 callback agrees with the retained complete ligand key. The ordering
uses the senior stream only after the derived prior tie. The pseudo flag is that same strict
decision's disagreement with the junior stream. -/
theorem retainedGeneratedCompound_throughRule5
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursorL cursorR : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (childL : cursorL ∈ input.certified.executableLocalizedRerootChildren target)
    (childR : cursorR ∈ input.certified.executableLocalizedRerootChildren target)
    (leftStages : input.certified.RuleMajorContextStages
      (LocalizedRuleMajorReference.carrierFuel input)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursorL)
    (rightStages : input.certified.RuleMajorContextStages
      (LocalizedRuleMajorReference.carrierFuel input)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursorR)
    {W D : Nat} (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)
    {left right : input.certified.LocalizedRerootCompoundRule45Key}
    (builtL : input.certified.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)
      (2 * (LocalizedRuleMajorReference.carrierFuel input + 1)) cursorL = some left)
    (builtR : input.certified.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)
      (2 * (LocalizedRuleMajorReference.carrierFuel input + 1)) cursorR = some right) :
    let result := input.certified.compareLocalizedRerootCompoundThroughRule5 left right
    let descriptorMap := LocalizedRuleMajorReference.descriptorMap input
    let graphL := ruleMajorTreeGraph leftStages.a.tree
    let graphR := ruleMajorTreeGraph rightStages.a.tree
    result.ordering =
      compare (retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph descriptorMap unit
          graphL W D)
        (retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph descriptorMap unit
          graphR W D) ∧
    (result.pseudo = true ↔
      compare (retainedCompleteLigandPriorKeyAt input.certified.moleculeGraph descriptorMap unit
          graphL W D)
        (retainedCompleteLigandPriorKeyAt input.certified.moleculeGraph descriptorMap unit
          graphR W D) = .eq ∧
      compare (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph descriptorMap unit
          graphL W D .senior)
        (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph descriptorMap unit
          graphR W D .senior) ≠ .eq ∧
      compare (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph descriptorMap unit
          graphL W D .senior)
        (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph descriptorMap unit
          graphR W D .senior) ≠
        compare (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph descriptorMap unit
            graphL W D .junior)
          (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph descriptorMap unit
            graphR W D .junior)) := by
  let graphL := ruleMajorTreeGraph leftStages.a.tree
  let graphR := ruleMajorTreeGraph rightStages.a.tree
  let descriptorMap := LocalizedRuleMajorReference.descriptorMap input
  have priorAgreement := retainedGeneratedCompound_prior_compare input singleBonded target unit
    targetUnit cursorL cursorR childL childR leftStages rightStages leftWidth leftDepth
    rightWidth rightDepth builtL builtR
  have ordering :
      (input.certified.compareLocalizedRerootCompoundThroughRule5 left right).ordering =
        compare (retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph descriptorMap unit
            graphL W D)
          (retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph descriptorMap unit
            graphR W D) := by
    have actualThen :
        (input.certified.compareLocalizedRerootCompoundThroughRule5 left right).ordering =
          (input.certified.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior).then
            (input.certified.compareLocalizedRerootCompoundRule5Readings .R
              left.rule5Readings right.rule5Readings) := by
      rw [input.certified.compareLocalizedRerootCompoundThroughRule5_ordering]
      rfl
    rw [actualThen, retainedCompleteLigandRule5KeyAt_compare_eq_then, ← priorAgreement]
    apply then_congr
    intro priorTie
    have actualPriorTie :
        input.certified.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior = .eq :=
      priorAgreement.symm ▸ priorTie
    simpa [senseOf] using retainedGeneratedCompound_rule5Readings_compare input singleBonded
      target unit targetUnit cursorL cursorR childL childR leftStages rightStages leftWidth
      leftDepth rightWidth rightDepth builtL builtR actualPriorTie .R
  refine ⟨ordering, ?_⟩
  unfold compareLocalizedRerootCompoundThroughRule5
  rw [priorAgreement]
  cases hp : compare
      (retainedCompleteLigandPriorKeyAt input.certified.moleculeGraph descriptorMap unit graphL W D)
      (retainedCompleteLigandPriorKeyAt input.certified.moleculeGraph descriptorMap unit graphR W D) with
  | lt => clear hp; simp
  | gt => clear hp; simp
  | eq =>
      have actualPriorTie :
          input.certified.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior = .eq := by
        rw [priorAgreement, hp]
      have senior := retainedGeneratedCompound_rule5Readings_compare input singleBonded target unit
        targetUnit cursorL cursorR childL childR leftStages rightStages leftWidth leftDepth
        rightWidth rightDepth builtL builtR actualPriorTie .R
      have junior := retainedGeneratedCompound_rule5Readings_compare input singleBonded target unit
        targetUnit cursorL cursorR childL childR leftStages rightStages leftWidth leftDepth
        rightWidth rightDepth builtL builtR actualPriorTie .S
      simp only [senseOf] at senior junior
      rw [senior, junior]
      cases hr : compare
          (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph descriptorMap unit graphL W D
            .senior)
          (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph descriptorMap unit graphR W D
            .senior) with
      | lt =>
          cases hs : compare
              (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph descriptorMap unit
                graphL W D .junior)
              (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph descriptorMap unit
                graphR W D .junior) <;> (clear hp; clear hr; clear hs; simp)
      | gt =>
          cases hs : compare
              (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph descriptorMap unit
                graphL W D .junior)
              (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph descriptorMap unit
                graphR W D .junior) <;> (clear hp; clear hr; clear hs; simp)
      | eq =>
          cases hs : compare
              (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph descriptorMap unit
                graphL W D .junior)
              (retainedCompleteRule5ReadingsAt input.certified.moleculeGraph descriptorMap unit
                graphR W D .junior) <;> (clear hp; clear hr; clear hs; simp)

end
end TetraStereo.OneCenter.RetainedContextRule5Comparison

assert_kernel_only TetraStereo.OneCenter.RetainedContextRule5Comparison.retainedRule5Reading_iso
assert_kernel_only TetraStereo.OneCenter.RetainedContextRule5Comparison.retainedGenerated_selectedRule5_represents
assert_kernel_only TetraStereo.OneCenter.RetainedContextRule5Comparison.retainedCrossBranch_selected_rule5_compare
assert_kernel_only TetraStereo.OneCenter.RetainedContextRule5Comparison.retainedGeneratedCompound_rule5Readings_compare
assert_kernel_only TetraStereo.OneCenter.RetainedContextRule5Comparison.retainedGeneratedCompound_throughRule5
