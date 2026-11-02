import TetraStereo.OneCenter.DeclarativeCIPCompleteReadingProjection
import TetraStereo.OneCenter.DeclarativeCIPRetainedCompleteSignatures
import TetraStereo.OneCenter.LocalizedContextCompoundReadback
import TetraStereo.OneCenter.LocalizedContextCompoundRule5Readback
import TetraStereo.OneCenter.LocalizedContextCrossBranchReadingComparison
import TetraStereo.OneCenter.LocalizedRetainedContextReferenceSelection
import TetraStereo.OneCenter.LocalizedRetainedContextStageGraphIso
import TetraStereo.OneCenter.LocalizedRetainedNoReferenceRule4cCanonicalBridge
import TetraStereo.OneCenter.LocalizedRetainedRule4aCanonicalBridge
import TetraStereo.OneCenter.LocalizedRetainedRule4bCanonicalBridge
import TetraStereo.OneCenter.LocalizedRetainedRule4cCanonicalBridge
import TetraStereo.OneCenter.LocalizedRuleMajorCompoundComparisonAlgebra
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! Actual compound order through Rule 4c for simple-bonded cyclic inputs.

The reference population is the retained selector on the actual Rule-4a arm graph. Rule-4b,
Rule-4c, and the empty-reference Rule-4c column are the retained readings on that same graph.
Same-cursor stage isomorphisms move later-stage observations back to the Rule-4a graph. No
acyclicity, desired selection, desired key, or physical expansion hypothesis is used. This is
not a four-ligand descriptor theorem. -/

namespace TetraStereo.OneCenter.RetainedContextCompoundComparison
open CertifiedLocalizedCIPInput DeclarativeCIP LocalizedCumulativeDecoratedTree
open Rule4aTableBridge Rule4cObservationBridge OfficialSparseCanonicalVectorComparison
open RetainedContextStereoReadback RetainedRule4aCanonicalBridge RetainedContextReferenceSelection
noncomputable section

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

private theorem rootLookup (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    tree.decoratedSubtreeAt? [] = some tree := by
  rw [decoratedSubtreeAt?]

private def facts4b {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : RetainedContextTreeRankReadback tree descriptorMap unit) :
    RetainedRule4bFieldFacts tree descriptorMap unit where
  label := hyp.label
  tetrahedral := hyp.tetrahedral
  realAvailableOrRing := hyp.nodeStatus

private def facts4c {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : RetainedContextTreeRankReadback tree descriptorMap unit) :
    RetainedRule4cFieldFacts tree descriptorMap unit where
  label := hyp.label
  tetrahedral := hyp.tetrahedral
  realAvailableOrRing := hyp.nodeStatus

private def factsNoReference {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : RetainedContextTreeRankReadback tree descriptorMap unit) :
    RetainedNoReferenceRule4cFieldFacts tree descriptorMap unit where
  label := hyp.label
  tetrahedral := hyp.tetrahedral
  realAvailableOrRing := hyp.nodeStatus

/-- Decorated observation law for one retained arm. The reader is whatever the tree realizes. -/
abbrev RetainedArmObservation (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (unit : DetectedOccurrence input.moleculeGraph) : Prop :=
  ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
    retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph tree) unit rule node =
      priorityValue rule (armObservation rule actual)

theorem retainedContextTrees_scalar4b_compare
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    {leftReference rightReference : RS}
    {fuelLeft fuelRight : Nat}
    {keyLeft keyRight : input.LocalizedRerootCumulativeRule45Key}
    (traceLeft : LocalizedRuleMajorSortTrace input (.rule4b leftReference) read
      fuelLeft left keyLeft)
    (traceRight : LocalizedRuleMajorSortTrace input (.rule4b rightReference) read
      fuelRight right keyRight)
    (readbackLeft : RetainedContextTreeRankReadback left descriptorMap unit)
    (readbackRight : RetainedContextTreeRankReadback right descriptorMap unit)
    (observationsLeft : RetainedArmObservation left unit)
    (observationsRight : RetainedArmObservation right unit)
    {W D : Nat}
    (widthLeft : (ruleMajorTreeGraph left).width ≤ W)
    (depthLeft : (ruleMajorTreeGraph left).height ≤ D)
    (widthRight : (ruleMajorTreeGraph right).width ≤ W)
    (depthRight : (ruleMajorTreeGraph right).height ≤ D)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyLeft.constitutional.rule1a keyRight.constitutional.rule1a = .eq)
    (tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a keyLeft) (scalar4a keyRight) = .eq) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4b keyLeft) (scalar4b keyRight) =
      compare
        (observedRule4bComponent (ruleMajorTreeGraph left)
          (retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph left) unit)
          (retainedReadingEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph left)
            (senseOf leftReference)) W D (ruleMajorTreeGraph left).root)
        (observedRule4bComponent (ruleMajorTreeGraph right)
          (retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph right) unit)
          (retainedReadingEvidence input.moleculeGraph descriptorMap unit
            (ruleMajorTreeGraph right) (senseOf rightReference)) W D
          (ruleMajorTreeGraph right).root) := by
  let graphLeft := ruleMajorTreeGraph left
  let graphRight := ruleMajorTreeGraph right
  let observeLeft := retainedContextNodeObservation input.moleculeGraph graphLeft unit
  let observeRight := retainedContextNodeObservation input.moleculeGraph graphRight unit
  let evidenceLeft := retainedReadingEvidence input.moleculeGraph descriptorMap unit graphLeft
    (senseOf leftReference)
  let evidenceRight := retainedReadingEvidence input.moleculeGraph descriptorMap unit graphRight
    (senseOf rightReference)
  have maskLeft := retainedRule4b_rule4abOnly_of_simpleBonded singleBonded descriptorMap unit
    graphLeft (senseOf leftReference)
  have maskRight := retainedRule4b_rule4abOnly_of_simpleBonded singleBonded descriptorMap unit
    graphRight (senseOf rightReference)
  have fullLeft := LocalizedRuleMajorSortTrace.fullMatch_of_trace traceLeft
  have fullRight := LocalizedRuleMajorSortTrace.fullMatch_of_trace traceRight
  have realizesLeft := LocalizedRuleMajorSortTrace.realizes_of_trace traceLeft
  have realizesRight := LocalizedRuleMajorSortTrace.realizes_of_trace traceRight
  have bridgeLeft := retainedContextTree_node_bridge4b left observeLeft observationsLeft
    (facts4b readbackLeft) maskLeft widthLeft depthLeft graphLeft.root left keyLeft traceLeft
    (rootLookup left)
  have bridgeRight := retainedContextTree_node_bridge4b right observeRight observationsRight
    (facts4b readbackRight) maskRight widthRight depthRight graphRight.root right keyRight
    traceRight (rootLookup right)
  exact compare_of_pathFirstDifference
    (ordinaryKeyWithObservations_stereo_wellShaped graphLeft observeLeft evidenceLeft W D
      .rule4bLikeUnlikeDescriptorPairs graphLeft.root)
    (ordinaryKeyWithObservations_stereo_wellShaped graphRight observeRight evidenceRight W D
      .rule4bLikeUnlikeDescriptorPairs graphRight.root)
    bridgeLeft.2.2 bridgeRight.2.2
    (fun outcome => rule4b_pathFirstDifference_iff fullLeft.tableMatch fullRight.tableMatch
      realizesLeft realizesRight tied tied4a outcome)

theorem retainedContextTrees_scalar4c_compare
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    {leftReference rightReference : RS}
    {fuelLeft fuelRight : Nat}
    {keyLeft keyRight : input.LocalizedRerootCumulativeRule45Key}
    (traceLeft : LocalizedRuleMajorSortTrace input (.rule4c leftReference) read
      fuelLeft left keyLeft)
    (traceRight : LocalizedRuleMajorSortTrace input (.rule4c rightReference) read
      fuelRight right keyRight)
    (readbackLeft : RetainedContextTreeRankReadback left descriptorMap unit)
    (readbackRight : RetainedContextTreeRankReadback right descriptorMap unit)
    (observationsLeft : RetainedArmObservation left unit)
    (observationsRight : RetainedArmObservation right unit)
    {W D : Nat}
    (widthLeft : (ruleMajorTreeGraph left).width ≤ W)
    (depthLeft : (ruleMajorTreeGraph left).height ≤ D)
    (widthRight : (ruleMajorTreeGraph right).width ≤ W)
    (depthRight : (ruleMajorTreeGraph right).height ≤ D)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyLeft.constitutional.rule1a keyRight.constitutional.rule1a = .eq)
    (tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a keyLeft) (scalar4a keyRight) = .eq) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4c keyLeft) (scalar4c keyRight) =
      compare
        (observedRule4cComponent (ruleMajorTreeGraph left)
          (retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph left) unit)
          (retainedReadingEvidence4c input.moleculeGraph descriptorMap unit
            (ruleMajorTreeGraph left) (senseOf leftReference)) W D
          (ruleMajorTreeGraph left).root)
        (observedRule4cComponent (ruleMajorTreeGraph right)
          (retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph right) unit)
          (retainedReadingEvidence4c input.moleculeGraph descriptorMap unit
            (ruleMajorTreeGraph right) (senseOf rightReference)) W D
          (ruleMajorTreeGraph right).root) := by
  let graphLeft := ruleMajorTreeGraph left
  let graphRight := ruleMajorTreeGraph right
  let observeLeft := retainedContextNodeObservation input.moleculeGraph graphLeft unit
  let observeRight := retainedContextNodeObservation input.moleculeGraph graphRight unit
  let evidenceLeft := retainedReadingEvidence4c input.moleculeGraph descriptorMap unit graphLeft
    (senseOf leftReference)
  let evidenceRight := retainedReadingEvidence4c input.moleculeGraph descriptorMap unit graphRight
    (senseOf rightReference)
  have maskLeft := rule4abcOnly_retainedReadingEvidence4c_of_simpleBonded input.moleculeGraph
    descriptorMap unit graphLeft singleBonded (senseOf leftReference)
  have maskRight := rule4abcOnly_retainedReadingEvidence4c_of_simpleBonded input.moleculeGraph
    descriptorMap unit graphRight singleBonded (senseOf rightReference)
  have fullLeft := LocalizedRuleMajorSortTrace.fullMatch_of_trace traceLeft
  have fullRight := LocalizedRuleMajorSortTrace.fullMatch_of_trace traceRight
  have realizesLeft := LocalizedRuleMajorSortTrace.realizes_of_trace traceLeft
  have realizesRight := LocalizedRuleMajorSortTrace.realizes_of_trace traceRight
  have bridgeLeft := retainedContextTree_node_bridge4c left observeLeft observationsLeft
    (facts4c readbackLeft) maskLeft widthLeft depthLeft graphLeft.root left keyLeft traceLeft
    (rootLookup left)
  have bridgeRight := retainedContextTree_node_bridge4c right observeRight observationsRight
    (facts4c readbackRight) maskRight widthRight depthRight graphRight.root right keyRight
    traceRight (rootLookup right)
  exact compare_of_pathFirstDifference
    (ordinaryKeyWithObservations_stereo_wellShaped graphLeft observeLeft evidenceLeft W D
      .rule4cPseudoasymmetricDescriptor graphLeft.root)
    (ordinaryKeyWithObservations_stereo_wellShaped graphRight observeRight evidenceRight W D
      .rule4cPseudoasymmetricDescriptor graphRight.root)
    bridgeLeft.2.2.2 bridgeRight.2.2.2
    (fun outcome => rule4c_pathFirstDifference_iff fullLeft.tableMatch fullRight.tableMatch
      fullLeft.labelMatch fullRight.labelMatch realizesLeft realizesRight tied tied4a outcome)

theorem retainedContextTrees_noReference4c_compare
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    {fuelLeft fuelRight : Nat}
    {keyLeft keyRight : input.LocalizedRerootCumulativeRule45Key}
    (traceLeft : LocalizedRuleMajorSortTrace input .rule4cNoReference read
      fuelLeft left keyLeft)
    (traceRight : LocalizedRuleMajorSortTrace input .rule4cNoReference read
      fuelRight right keyRight)
    (readbackLeft : RetainedContextTreeRankReadback left descriptorMap unit)
    (readbackRight : RetainedContextTreeRankReadback right descriptorMap unit)
    (observationsLeft : RetainedArmObservation left unit)
    (observationsRight : RetainedArmObservation right unit)
    {W D : Nat}
    (widthLeft : (ruleMajorTreeGraph left).width ≤ W)
    (depthLeft : (ruleMajorTreeGraph left).height ≤ D)
    (widthRight : (ruleMajorTreeGraph right).width ≤ W)
    (depthRight : (ruleMajorTreeGraph right).height ≤ D)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyLeft.constitutional.rule1a keyRight.constitutional.rule1a = .eq)
    (tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a keyLeft) (scalar4a keyRight) = .eq) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4b keyLeft) (scalar4b keyRight) =
      compare
        (observedRule4cComponent (ruleMajorTreeGraph left)
          (retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph left) unit)
          (retainedNoReferenceEvidence4c input.moleculeGraph descriptorMap unit
            (ruleMajorTreeGraph left)) W D (ruleMajorTreeGraph left).root)
        (observedRule4cComponent (ruleMajorTreeGraph right)
          (retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph right) unit)
          (retainedNoReferenceEvidence4c input.moleculeGraph descriptorMap unit
            (ruleMajorTreeGraph right)) W D (ruleMajorTreeGraph right).root) := by
  let graphLeft := ruleMajorTreeGraph left
  let graphRight := ruleMajorTreeGraph right
  let observeLeft := retainedContextNodeObservation input.moleculeGraph graphLeft unit
  let observeRight := retainedContextNodeObservation input.moleculeGraph graphRight unit
  let evidenceLeft := retainedNoReferenceEvidence4c input.moleculeGraph descriptorMap unit graphLeft
  let evidenceRight := retainedNoReferenceEvidence4c input.moleculeGraph descriptorMap unit
    graphRight
  have maskLeft := rule4acOnly_retainedNoReferenceEvidence4c_of_simpleBonded input.moleculeGraph
    descriptorMap unit graphLeft singleBonded
  have maskRight := rule4acOnly_retainedNoReferenceEvidence4c_of_simpleBonded input.moleculeGraph
    descriptorMap unit graphRight singleBonded
  have fullLeft := LocalizedRuleMajorSortTrace.fullMatch_of_trace traceLeft
  have fullRight := LocalizedRuleMajorSortTrace.fullMatch_of_trace traceRight
  have realizesLeft := LocalizedRuleMajorSortTrace.realizes_of_trace traceLeft
  have realizesRight := LocalizedRuleMajorSortTrace.realizes_of_trace traceRight
  have bridgeLeft := retainedContextTree_node_bridge_noReference4c left observeLeft
    observationsLeft (factsNoReference readbackLeft) maskLeft widthLeft depthLeft graphLeft.root
    left keyLeft traceLeft (rootLookup left)
  have bridgeRight := retainedContextTree_node_bridge_noReference4c right observeRight
    observationsRight (factsNoReference readbackRight) maskRight widthRight depthRight
    graphRight.root right keyRight traceRight (rootLookup right)
  exact compare_of_pathFirstDifference
    (ordinaryKeyWithObservations_stereo_wellShaped graphLeft observeLeft evidenceLeft W D
      .rule4cPseudoasymmetricDescriptor graphLeft.root)
    (ordinaryKeyWithObservations_stereo_wellShaped graphRight observeRight evidenceRight W D
      .rule4cPseudoasymmetricDescriptor graphRight.root)
    bridgeLeft.2.2 bridgeRight.2.2
    (fun outcome => noReference4c_pathFirstDifference_iff fullLeft.tableMatch fullRight.tableMatch
      fullLeft.labelMatch fullRight.labelMatch realizesLeft realizesRight tied tied4a outcome)

/-- Rank, tetrahedral status, and retained observation at every stage of one cursor. -/
structure RetainedStageReadingFacts
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) : Prop where
  aReadback : RetainedContextTreeRankReadback stages.a.tree descriptorMap unit
  aObservation : RetainedArmObservation stages.a.tree unit
  bReadback : ∀ reference, RetainedContextTreeRankReadback (stages.b reference).tree
    descriptorMap unit
  bObservation : ∀ reference, RetainedArmObservation (stages.b reference).tree unit
  cReadback : ∀ reference, RetainedContextTreeRankReadback (stages.c reference).tree
    descriptorMap unit
  cObservation : ∀ reference, RetainedArmObservation (stages.c reference).tree unit
  noReferenceReadback : RetainedContextTreeRankReadback stages.noReference.tree descriptorMap unit
  noReferenceObservation : RetainedArmObservation stages.noReference.tree unit

def retainedContextBranchReadings
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) :
    List input.LocalizedRerootRule4bcReading :=
  (localizedRule4bcReferenceAlternatives
    (toReferenceList (retainedReferenceSelection input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph stages.a.tree)))).map (contextStageReading stages)

section CrossBranch

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

include singleBonded readL readR isoL isoR

theorem retainedCrossBranch_selectedB_compare (leftReference rightReference : RS)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    {W D : Nat} (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (leftStages.b leftReference).key.descriptor
        (rightStages.b rightReference).key.descriptor =
      compare
        (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph leftStages.a.tree) W D (some (senseOf leftReference)))).1
        (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph rightStages.a.tree) W D (some (senseOf rightReference)))).1 := by
  let ties := contextCrossBranch_ties leftStages rightStages leftReference rightReference aTie
  have scalar := retainedContextTrees_scalar4b_compare singleBonded
    (leftStages.b leftReference).tree (rightStages.b rightReference).tree
    (leftStages.b leftReference).trace (rightStages.b rightReference).trace
    (readL.bReadback leftReference) (readR.bReadback rightReference)
    (readL.bObservation leftReference) (readR.bObservation rightReference)
    ((leftStages.b_width_le leftReference).trans leftWidth)
    ((leftStages.b_depth_le leftReference).trans leftDepth)
    ((rightStages.b_width_le rightReference).trans rightWidth)
    ((rightStages.b_depth_le rightReference).trans rightDepth)
    (contextCompareNatLayers_eq_of_tie ties.bRule1a)
    (contextCompareNatLayers_eq_of_tie ties.bScalar4a)
  change _ = compare
    (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph (leftStages.b leftReference).tree) W D
      (some (senseOf leftReference)))).1
    (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph (rightStages.b rightReference).tree) W D
      (some (senseOf rightReference)))).1 at scalar
  rw [retainedCompleteReadingAt_iso input.moleculeGraph descriptorMap unit
      (isoL.b leftReference), retainedCompleteReadingAt_iso input.moleculeGraph descriptorMap unit
      (isoR.b rightReference)] at scalar
  rw [compare_descriptor_eq_scalar4b_of_scalar4a_eq
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace (leftStages.b leftReference).trace).tableMatch
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace
      (rightStages.b rightReference).trace).tableMatch
    ties.bScalar4a]
  exact scalar

theorem retainedCrossBranch_selectedC_compare (leftReference rightReference : RS)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    (bTie : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      (leftStages.b leftReference).key.descriptor
      (rightStages.b rightReference).key.descriptor = .eq)
    {W D : Nat} (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (leftStages.c leftReference).key.descriptor
        (rightStages.c rightReference).key.descriptor =
      compare
        (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph leftStages.a.tree) W D (some (senseOf leftReference)))).2
        (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph rightStages.a.tree) W D (some (senseOf rightReference)))).2 := by
  let ties := contextCrossBranch_ties leftStages rightStages leftReference rightReference aTie
  have scalarBTie : scalar4b (leftStages.b leftReference).key =
      scalar4b (rightStages.b rightReference).key := by
    have cmpEq := (compare_descriptor_eq_scalar4b_of_scalar4a_eq
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace (leftStages.b leftReference).trace).tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace
        (rightStages.b rightReference).trace).tableMatch
      ties.bScalar4a).symm
    rw [bTie] at cmpEq
    exact (compareSparseLayers_compareNat_eq_iff _ _).mp cmpEq
  have scalarCTie := ties.bToCScalar4bLeft.symm.trans (scalarBTie.trans ties.bToCScalar4bRight)
  have scalar := retainedContextTrees_scalar4c_compare singleBonded
    (leftStages.c leftReference).tree (rightStages.c rightReference).tree
    (leftStages.c leftReference).trace (rightStages.c rightReference).trace
    (readL.cReadback leftReference) (readR.cReadback rightReference)
    (readL.cObservation leftReference) (readR.cObservation rightReference)
    ((leftStages.c_width_le leftReference).trans leftWidth)
    ((leftStages.c_depth_le leftReference).trans leftDepth)
    ((rightStages.c_width_le rightReference).trans rightWidth)
    ((rightStages.c_depth_le rightReference).trans rightDepth)
    (contextCompareNatLayers_eq_of_tie ties.cRule1a)
    (contextCompareNatLayers_eq_of_tie ties.cScalar4a)
  change _ = compare
    (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph (leftStages.c leftReference).tree) W D
      (some (senseOf leftReference)))).2
    (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph (rightStages.c rightReference).tree) W D
      (some (senseOf rightReference)))).2 at scalar
  rw [retainedCompleteReadingAt_iso input.moleculeGraph descriptorMap unit
      (isoL.c leftReference), retainedCompleteReadingAt_iso input.moleculeGraph descriptorMap unit
      (isoR.c rightReference)] at scalar
  rw [compare_descriptor_eq_scalar4c_of_prior_columns_eq
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace (leftStages.c leftReference).trace).tableMatch
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace
      (rightStages.c rightReference).trace).tableMatch
    ties.cScalar4a scalarCTie]
  exact scalar

theorem retainedCrossBranch_noReference_compare
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    {W D : Nat} (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        leftStages.noReference.key.descriptor rightStages.noReference.key.descriptor =
      compare
        (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph leftStages.a.tree) W D none)).2
        (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph rightStages.a.tree) W D none)).2 := by
  let ties := contextCrossBranch_ties leftStages rightStages .R .R aTie
  have scalar := retainedContextTrees_noReference4c_compare singleBonded
    leftStages.noReference.tree rightStages.noReference.tree
    leftStages.noReference.trace rightStages.noReference.trace
    readL.noReferenceReadback readR.noReferenceReadback
    readL.noReferenceObservation readR.noReferenceObservation
    (leftStages.noReference_width_le.trans leftWidth)
    (leftStages.noReference_depth_le.trans leftDepth)
    (rightStages.noReference_width_le.trans rightWidth)
    (rightStages.noReference_depth_le.trans rightDepth)
    (contextCompareNatLayers_eq_of_tie ties.noReferenceRule1a)
    (contextCompareNatLayers_eq_of_tie ties.noReferenceScalar4a)
  change _ = compare
    (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph leftStages.noReference.tree) W D none)).2
    (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph rightStages.noReference.tree) W D none)).2 at scalar
  rw [retainedCompleteReadingAt_iso input.moleculeGraph descriptorMap unit isoL.noReference,
    retainedCompleteReadingAt_iso input.moleculeGraph descriptorMap unit isoR.noReference] at scalar
  rw [compare_descriptor_eq_scalar4b_of_prior_scalar4a_eq
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace leftStages.noReference.trace).tableMatch
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace rightStages.noReference.trace).tableMatch
    ties.noReferenceScalar4a]
  exact scalar

end CrossBranch

theorem retainedStages_RS_completeReading_compare
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    {W D : Nat} (width : stages.widthBound ≤ W) (depth : stages.depthBound ≤ D)
    (readbacks : RetainedStageReadingFacts stages descriptorMap unit)
    (isomorphisms : RuleMajorContextStageGraphIsoBundle stages) :
    input.compareRule4bcReadingsComplete
        { reference? := some .R
          rule4bKey := (stages.b .R).key
          rule4cKey := (stages.c .R).key }
        { reference? := some .S
          rule4bKey := (stages.b .S).key
          rule4cKey := (stages.c .S).key } =
      compare
        (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph stages.a.tree) W D (some .senior))
        (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph stages.a.tree) W D (some .junior)) := by
  let commonGraph := ruleMajorTreeGraph stages.a.tree
  let graphBR := ruleMajorTreeGraph (stages.b .R).tree
  let graphBS := ruleMajorTreeGraph (stages.b .S).tree
  let graphCR := ruleMajorTreeGraph (stages.c .R).tree
  let graphCS := ruleMajorTreeGraph (stages.c .S).tree
  have prefixes := input.ruleMajor_sameBranch_reading_prefixes read
    (2 * (carrierFuel + 1)) cursor .R .S stages.a.key
    (stages.b .R).key (stages.c .R).key (stages.b .S).key (stages.c .S).key
    stages.a.built (stages.b .R).built (stages.c .R).built
    (stages.b .S).built (stages.c .S).built
  have selfCompare : ∀ table : List (List (OfficialSparseEntry Nat)),
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat table table = .eq :=
    CompilerProjectionFidelity.compareSparseLayers_self OfficialRuleMajorKey.compareNat
      CompilerProjectionFidelity.compareNat_self
  have tiedBR : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (stages.b .R).key.constitutional.rule1a (stages.b .S).key.constitutional.rule1a = .eq := by
    rw [prefixes.1]
    exact selfCompare _
  have tiedBR4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a (stages.b .R).key) (scalar4a (stages.b .S).key) = .eq := by
    rw [prefixes.2.1]
    exact selfCompare _
  have tiedCR : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (stages.c .R).key.constitutional.rule1a (stages.c .S).key.constitutional.rule1a = .eq := by
    rw [prefixes.2.2.1]
    exact selfCompare _
  have tiedCR4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a (stages.c .R).key) (scalar4a (stages.c .S).key) = .eq := by
    rw [prefixes.2.2.2.1]
    exact selfCompare _
  have scalarB := retainedContextTrees_scalar4b_compare singleBonded
    (stages.b .R).tree (stages.b .S).tree (stages.b .R).trace (stages.b .S).trace
    (readbacks.bReadback .R) (readbacks.bReadback .S)
    (readbacks.bObservation .R) (readbacks.bObservation .S)
    (W := W) (D := D)
    (Nat.le_trans (stages.b_width_le .R) width)
    (Nat.le_trans (stages.b_depth_le .R) depth)
    (Nat.le_trans (stages.b_width_le .S) width)
    (Nat.le_trans (stages.b_depth_le .S) depth)
    tiedBR tiedBR4a
  have scalarC := retainedContextTrees_scalar4c_compare singleBonded
    (stages.c .R).tree (stages.c .S).tree (stages.c .R).trace (stages.c .S).trace
    (readbacks.cReadback .R) (readbacks.cReadback .S)
    (readbacks.cObservation .R) (readbacks.cObservation .S)
    (W := W) (D := D)
    (Nat.le_trans (stages.c_width_le .R) width)
    (Nat.le_trans (stages.c_depth_le .R) depth)
    (Nat.le_trans (stages.c_width_le .S) width)
    (Nat.le_trans (stages.c_depth_le .S) depth)
    tiedCR tiedCR4a
  have readB : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4b (stages.b .R).key) (scalar4b (stages.b .S).key) =
      compare
        (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit graphBR
          W D (some .senior))).1
        (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit graphBS
          W D (some .junior))).1 := by
    simpa [retainedCompleteReadingAt, senseOf] using scalarB
  have readC : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4c (stages.c .R).key) (scalar4c (stages.c .S).key) =
      compare
        (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit graphCR
          W D (some .senior))).2
        (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit graphCS
          W D (some .junior))).2 := by
    simpa [retainedCompleteReadingAt, senseOf] using scalarC
  have readBCommon : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4b (stages.b .R).key) (scalar4b (stages.b .S).key) =
      compare
        (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit commonGraph
          W D (some .senior))).1
        (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit commonGraph
          W D (some .junior))).1 := by
    calc
      _ = compare
          (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit graphBR
            W D (some .senior))).1
          (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit graphBS
            W D (some .junior))).1 := readB
      _ = _ := by
          rw [retainedCompleteReadingAt_iso input.moleculeGraph descriptorMap unit
                (isomorphisms.b .R) W D (some .senior),
              retainedCompleteReadingAt_iso input.moleculeGraph descriptorMap unit
                (isomorphisms.b .S) W D (some .junior)]
  have readCCommon : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4c (stages.c .R).key) (scalar4c (stages.c .S).key) =
      compare
        (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit commonGraph
          W D (some .senior))).2
        (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit commonGraph
          W D (some .junior))).2 := by
    calc
      _ = compare
          (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit graphCR
            W D (some .senior))).2
          (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit graphCS
            W D (some .junior))).2 := readC
      _ = _ := by
          rw [retainedCompleteReadingAt_iso input.moleculeGraph descriptorMap unit
                (isomorphisms.c .R) W D (some .senior),
              retainedCompleteReadingAt_iso input.moleculeGraph descriptorMap unit
                (isomorphisms.c .S) W D (some .junior)]
  rw [completeReading_compare_eq_then]
  change
    (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      (stages.b .R).key.descriptor (stages.b .S).key.descriptor).then
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (stages.c .R).key.descriptor (stages.c .S).key.descriptor) =
      (compare
        (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit commonGraph
          W D (some .senior))).1
        (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit commonGraph
          W D (some .junior))).1).then
        (compare
          (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit commonGraph
            W D (some .senior))).2
          (ofLex (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit commonGraph
            W D (some .junior))).2)
  rw [compare_descriptor_eq_scalar4b_of_scalar4a_eq
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace (stages.b .R).trace).tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace (stages.b .S).trace).tableMatch
      prefixes.2.1,
    ← readBCommon]
  cases comparison : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4b (stages.b .R).key) (scalar4b (stages.b .S).key) with
  | lt => rfl
  | gt => rfl
  | eq =>
      simp only [Ordering.eq_then]
      have equalB : scalar4b (stages.c .R).key = scalar4b (stages.c .S).key := by
        rw [← prefixes.2.2.2.2.1, ← prefixes.2.2.2.2.2]
        exact (compareSparseLayers_compareNat_eq_iff _ _).mp comparison
      rw [compare_descriptor_eq_scalar4c_of_prior_columns_eq
        (LocalizedRuleMajorSortTrace.fullMatch_of_trace (stages.c .R).trace).tableMatch
        (LocalizedRuleMajorSortTrace.fullMatch_of_trace (stages.c .S).trace).tableMatch
        prefixes.2.2.2.1 equalB]
      exact readCCommon

theorem retainedStages_rankReadings_observations
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) {W D : Nat}
    (width : stages.widthBound ≤ W) (depth : stages.depthBound ≤ D)
    (readbacks : RetainedStageReadingFacts stages descriptorMap unit)
    (isomorphisms : RuleMajorContextStageGraphIsoBundle stages) :
    (input.rankReadings (retainedContextBranchReadings stages descriptorMap unit)).map
      (fun reading => retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) W D (reading.reference?.map senseOf)) =
      retainedCompleteReadingsAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) W D := by
  cases selectionEq : retainedReferenceSelection input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph stages.a.tree) with
  | empty =>
      simp [retainedContextBranchReadings, rankReadings, contextStageReading,
        localizedRule4bcReferenceAlternatives, toReferenceList, retainedCompleteReadingsAt,
        retainedCompleteReadingAt, selectionEq]
  | one sense =>
      cases sense with
      | senior =>
          simp [retainedContextBranchReadings, rankReadings, contextStageReading,
            localizedRule4bcReferenceAlternatives, toReferenceList, retainedCompleteReadingsAt,
            retainedCompleteReadingAt, selectionEq, senseOf]
      | junior =>
          simp [retainedContextBranchReadings, rankReadings, contextStageReading,
            localizedRule4bcReferenceAlternatives, toReferenceList, retainedCompleteReadingsAt,
            retainedCompleteReadingAt, selectionEq, senseOf]
  | both =>
      have comparison := retainedStages_RS_completeReading_compare singleBonded stages
        descriptorMap unit width depth readbacks isomorphisms
      have selectedReadings : retainedContextBranchReadings stages descriptorMap unit =
          [contextStageReading stages (some .R), contextStageReading stages (some .S)] := by
        simp [retainedContextBranchReadings, localizedRule4bcReferenceAlternatives,
          toReferenceList, selectionEq]
      rw [selectedReadings]
      simp only [rankReadings, contextStageReading]
      rw [comparison]
      simp only [retainedCompleteReadingsAt, selectionEq]
      split_ifs with h
      · simpa only [List.map_cons, List.map_nil, Option.map_some, senseOf, if_pos h] using
          (completeReading_descendingPair
            (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
              (ruleMajorTreeGraph stages.a.tree) W D (some .senior))
            (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
              (ruleMajorTreeGraph stages.a.tree) W D (some .junior)))
      · simpa only [List.map_cons, List.map_nil, Option.map_some, senseOf, if_neg h] using
          (completeReading_descendingPair
            (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
              (ruleMajorTreeGraph stages.a.tree) W D (some .senior))
            (retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
              (ruleMajorTreeGraph stages.a.tree) W D (some .junior)))

theorem retainedStages_rankedReferenceTags
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (readbacks : RetainedStageReadingFacts stages descriptorMap unit)
    (isomorphisms : RuleMajorContextStageGraphIsoBundle stages) {W D : Nat}
    (width : stages.widthBound ≤ W) (depth : stages.depthBound ≤ D) :
    (input.rankReadings (retainedContextBranchReadings stages descriptorMap unit)).map
      (fun reading => reading.reference?.map senseOf) =
      retainedTaggedAlternativeReferencesAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) W D := by
  cases selectionEq : retainedReferenceSelection input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph stages.a.tree) with
  | empty =>
      simp [retainedContextBranchReadings, rankReadings, contextStageReading,
        localizedRule4bcReferenceAlternatives, toReferenceList,
        retainedTaggedAlternativeReferencesAt, selectionEq]
  | one sense =>
      cases sense with
      | senior =>
          simp [retainedContextBranchReadings, rankReadings, contextStageReading,
            localizedRule4bcReferenceAlternatives, toReferenceList,
            retainedTaggedAlternativeReferencesAt, selectionEq, senseOf]
      | junior =>
          simp [retainedContextBranchReadings, rankReadings, contextStageReading,
            localizedRule4bcReferenceAlternatives, toReferenceList,
            retainedTaggedAlternativeReferencesAt, selectionEq, senseOf]
  | both =>
      have comparison := retainedStages_RS_completeReading_compare singleBonded stages
        descriptorMap unit width depth readbacks isomorphisms
      have selectedReadings : retainedContextBranchReadings stages descriptorMap unit =
          [contextStageReading stages (some .R), contextStageReading stages (some .S)] := by
        simp [retainedContextBranchReadings, localizedRule4bcReferenceAlternatives,
          toReferenceList, selectionEq]
      rw [selectedReadings]
      simp only [rankReadings, contextStageReading]
      rw [comparison]
      simp only [retainedTaggedAlternativeReferencesAt, selectionEq]
      split_ifs with h
      · simp only [List.map_cons, List.map_nil, Option.map_some, senseOf]
      · simp only [List.map_cons, List.map_nil, Option.map_some, senseOf]

/-- Prior and Rule-5 outputs of one actual compound agree with the retained selection and the
retained readings on its Rule-4a arm graph. -/
structure RetainedCompoundReadbackData
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (compound : input.LocalizedRerootCompoundRule45Key) (W D : Nat) : Prop where
  aKey : compound.prior.rule4aKey = stages.a.key
  references : compound.prior.references = toReferenceList
    (retainedReferenceSelection input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph stages.a.tree))
  count : compound.prior.referenceCountPriority =
    (retainedReferenceSelection input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph stages.a.tree)).countPriority
  readingStages : ∀ reading ∈ compound.prior.readings,
    match reading.reference? with
    | none => reading.rule4bKey = stages.a.key ∧
        reading.rule4cKey = stages.noReference.key
    | some reference => reading.rule4bKey = (stages.b reference).key ∧
        reading.rule4cKey = (stages.c reference).key
  readingEmpty : ∀ reading ∈ compound.prior.readings,
    reading.reference? = none ↔
      retainedReferenceSelection input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) = .empty
  observations : compound.prior.readings.map (fun reading =>
      retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) W D (reading.reference?.map senseOf)) =
    retainedCompleteReadingsAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph stages.a.tree) W D
  tags : compound.rule5Readings.map (fun reading => reading.prior.reference?.map senseOf) =
    retainedTaggedAlternativeReferencesAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph stages.a.tree) W D

theorem retainedStages_compound_independentReadback
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) {W D : Nat}
    (width : stages.widthBound ≤ W) (depth : stages.depthBound ≤ D)
    (readbacks : RetainedStageReadingFacts stages descriptorMap unit)
    (isomorphisms : RuleMajorContextStageGraphIsoBundle stages)
    {compound : input.LocalizedRerootCompoundRule45Key}
    (built : input.buildRuleMajorCompoundRule45KeyWith?
      (fun stage position => input.buildRuleMajorCumulativeWithRead? stage read
        (2 * (carrierFuel + 1)) position) cursor = some compound)
    (referencesEq : compound.prior.references = toReferenceList
      (retainedReferenceSelection input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree))) :
    RetainedCompoundReadbackData stages descriptorMap unit compound W D := by
  obtain ⟨aEq, _builderReferences, countEq, readingsEq⟩ :=
    input.contextStages_compound_readback stages built
  have count : compound.prior.referenceCountPriority =
      (retainedReferenceSelection input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree)).countPriority := by
    rw [countEq, referencesEq]
    cases selection : retainedReferenceSelection input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) with
    | empty => rfl
    | one sense => cases sense <;> rfl
    | both => rfl
  have readingsEqSelection : compound.prior.readings = input.rankReadings
      (retainedContextBranchReadings stages descriptorMap unit) := by
    rw [readingsEq, referencesEq]
    rfl
  have emptyReadingsEq (selection : retainedReferenceSelection input.moleculeGraph
      descriptorMap unit (ruleMajorTreeGraph stages.a.tree) = .empty) :
      compound.prior.readings = [contextStageReading stages none] := by
    rw [readingsEqSelection]
    simp [retainedContextBranchReadings, localizedRule4bcReferenceAlternatives, toReferenceList,
      rankReadings, selection]
  have seniorReadingsEq (selection : retainedReferenceSelection input.moleculeGraph
      descriptorMap unit (ruleMajorTreeGraph stages.a.tree) = .one .senior) :
      compound.prior.readings = [contextStageReading stages (some .R)] := by
    rw [readingsEqSelection]
    simp [retainedContextBranchReadings, localizedRule4bcReferenceAlternatives, toReferenceList,
      rankReadings, selection]
  have juniorReadingsEq (selection : retainedReferenceSelection input.moleculeGraph
      descriptorMap unit (ruleMajorTreeGraph stages.a.tree) = .one .junior) :
      compound.prior.readings = [contextStageReading stages (some .S)] := by
    rw [readingsEqSelection]
    simp [retainedContextBranchReadings, localizedRule4bcReferenceAlternatives, toReferenceList,
      rankReadings, selection]
  have bothReadingsEq (selection : retainedReferenceSelection input.moleculeGraph
      descriptorMap unit (ruleMajorTreeGraph stages.a.tree) = .both) :
      compound.prior.readings = input.rankReadings
        [contextStageReading stages (some .R), contextStageReading stages (some .S)] := by
    rw [readingsEqSelection]
    simp [retainedContextBranchReadings, localizedRule4bcReferenceAlternatives, toReferenceList,
      selection]
  have readingStages : ∀ reading ∈ compound.prior.readings,
      match reading.reference? with
      | none => reading.rule4bKey = stages.a.key ∧
          reading.rule4cKey = stages.noReference.key
      | some reference => reading.rule4bKey = (stages.b reference).key ∧
          reading.rule4cKey = (stages.c reference).key := by
    intro reading present
    cases selection : retainedReferenceSelection input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) with
    | empty =>
        rw [emptyReadingsEq selection] at present
        have equal := List.mem_singleton.mp present
        subst reading
        simp [contextStageReading]
    | one sense =>
        cases sense with
        | senior =>
            rw [seniorReadingsEq selection] at present
            have equal := List.mem_singleton.mp present
            subst reading
            simp [contextStageReading]
        | junior =>
            rw [juniorReadingsEq selection] at present
            have equal := List.mem_singleton.mp present
            subst reading
            simp [contextStageReading]
    | both =>
        rw [bothReadingsEq selection] at present
        simp only [rankReadings] at present
        split at present <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at present
        all_goals
          rcases present with referenceR | referenceS
          · cases referenceR
            simp [contextStageReading]
          · cases referenceS
            simp [contextStageReading]
  have readingEmpty : ∀ reading ∈ compound.prior.readings,
      reading.reference? = none ↔
        retainedReferenceSelection input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph stages.a.tree) = .empty := by
    intro reading present
    constructor
    · intro readingNone
      cases selection : retainedReferenceSelection input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph stages.a.tree) with
      | empty => rfl
      | one sense =>
          cases sense with
          | senior =>
              rw [seniorReadingsEq selection] at present
              have equal := List.mem_singleton.mp present
              subst reading
              simp [contextStageReading] at readingNone
          | junior =>
              rw [juniorReadingsEq selection] at present
              have equal := List.mem_singleton.mp present
              subst reading
              simp [contextStageReading] at readingNone
      | both =>
          rw [bothReadingsEq selection] at present
          simp only [rankReadings] at present
          split at present <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at present
          all_goals
            rcases present with referenceR | referenceS
            · cases referenceR
              simp [contextStageReading] at readingNone
            · cases referenceS
              simp [contextStageReading] at readingNone
    · intro selectionEmpty
      rw [emptyReadingsEq selectionEmpty] at present
      have equal := List.mem_singleton.mp present
      subst reading
      simp [contextStageReading]
  have observations : compound.prior.readings.map (fun reading =>
      retainedCompleteReadingAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) W D (reading.reference?.map senseOf)) =
      retainedCompleteReadingsAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) W D := by
    rw [readingsEqSelection]
    exact retainedStages_rankReadings_observations singleBonded stages descriptorMap unit
      width depth readbacks isomorphisms
  have tags : compound.rule5Readings.map
      (fun reading => reading.prior.reference?.map senseOf) =
      retainedTaggedAlternativeReferencesAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) W D := by
    rw [input.contextStages_compound_rule5Readings_eq_map stages built]
    simp only [List.map_map]
    change (compound.prior.readings.map
        (fun reading => (input.ruleMajorExpectedRule5Reading reading).prior.reference?.map
          senseOf)) = _
    simp only [ruleMajorExpectedRule5Reading]
    rw [readingsEqSelection]
    exact retainedStages_rankedReferenceTags singleBonded stages descriptorMap unit
      readbacks isomorphisms width depth
  exact {
    aKey := aEq
    references := referencesEq
    count := count
    readingStages := readingStages
    readingEmpty := readingEmpty
    observations := observations
    tags := tags }

/-- Generated-reader rank bundle and observation law at every stage of one executable child. -/
theorem retainedGeneratedStageReadingFacts
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (child : cursor ∈ input.certified.executableLocalizedRerootChildren target)
    (stages : input.certified.RuleMajorContextStages
      (LocalizedRuleMajorReference.carrierFuel input)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursor) :
    RetainedStageReadingFacts stages (LocalizedRuleMajorReference.descriptorMap input) unit := by
  let descriptorMap := LocalizedRuleMajorReference.descriptorMap input
  have fill {stage : LocalizedCumulativeRule45Stage} {fuel : Nat}
      {key : input.certified.LocalizedRerootCumulativeRule45Key}
      (tree : LocalizedCumulativeDecoratedTree input.certified
        (LocalizedRuleMajorReference.carrierFuel input))
      (trace : LocalizedRuleMajorSortTrace input.certified stage
        (input.certified.localizedDependencyLabel target.occurrence
          (input.certified.localizedDependencyView
            (LocalizedRuleMajorReference.referenceState input) target.occurrence)) fuel tree key)
      (rootChild : tree.source ∈ input.certified.executableLocalizedRerootChildren target) :
      RetainedContextTreeRankReadback tree descriptorMap unit ∧
        RetainedArmObservation tree unit := by
    have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
    refine ⟨retainedGeneratedContextTreeRankReadback input singleBonded target unit targetUnit
      tree realizes rootChild, ?_⟩
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

/-- One successful generated compound at an executable child agrees with the retained selection
and retained readings. The selector equality is the generated Rule-4a theorem. -/
theorem retainedGeneratedCompound_independentReadback
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (cursorChild : cursor ∈ input.certified.executableLocalizedRerootChildren target)
    (stages : input.certified.RuleMajorContextStages
      (LocalizedRuleMajorReference.carrierFuel input)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursor)
    {compound : input.certified.LocalizedRerootCompoundRule45Key}
    {W D : Nat} (width : stages.widthBound ≤ W) (depth : stages.depthBound ≤ D)
    (built : input.certified.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)
      (2 * (LocalizedRuleMajorReference.carrierFuel input + 1)) cursor = some compound) :
    RetainedCompoundReadbackData stages (LocalizedRuleMajorReference.descriptorMap input)
      unit compound W D := by
  let view := input.certified.localizedDependencyView
    (LocalizedRuleMajorReference.referenceState input) target.occurrence
  let read := input.certified.localizedDependencyLabel target.occurrence view
  let fuel := 2 * (LocalizedRuleMajorReference.carrierFuel input + 1)
  have uniformBuilt : input.certified.buildRuleMajorCompoundRule45KeyWith?
      (fun stage position => input.certified.buildRuleMajorCumulativeWithRead? stage read fuel
        position) cursor = some compound := by
    rw [← input.certified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
    rw [← input.certified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact built
  obtain ⟨_aKey, rankedReferences, _count, _readings⟩ :=
    input.certified.contextStages_compound_readback stages uniformBuilt
  have selectionReferences := retainedGeneratedContextTree_references_eq_selection input
    singleBonded target unit targetUnit stages.a.tree stages.a.trace
    (by simpa only [stages.a.sourceEq] using cursorChild)
  have referencesEq : compound.prior.references = toReferenceList
      (retainedReferenceSelection input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph stages.a.tree)) :=
    rankedReferences.trans selectionReferences
  exact retainedStages_compound_independentReadback singleBonded stages
    (LocalizedRuleMajorReference.descriptorMap input) unit width depth
    (retainedGeneratedStageReadingFacts input singleBonded target unit targetUnit cursor
      cursorChild stages)
    (ruleMajorContextStageGraphIsoBundle_of_stages stages) uniformBuilt referencesEq

private def unmaskedRetainedPriorAt
    (molecule : MoleculeGraph input.Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph input.Atom) (W D : Nat) :
    CompletePriorSignature :=
  let selection := retainedReferenceSelection molecule descriptorMap unit graph
  let readings := retainedCompleteReadingsAt molecule descriptorMap unit graph W D
  toLex (selection.countPriority, toLex
    (readings.map (fun key => (ofLex key).1), readings.map (fun key => (ofLex key).2)))

private theorem compare_localUnmaskedRetainedPrior_eq
    (molecule : MoleculeGraph input.Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
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

section PriorAlgebra

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

private theorem compound_after4a_compare
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

/-- Actual compound priority through Rule 4c agrees with the retained ligand prior key.
Both arms are successful executions at executable children of one simple-bonded target.
Reference selection, stage readback, stage isomorphism, and the Rule-4a tie are derived. -/
theorem retainedGeneratedCompound_prior_compare
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
    input.certified.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior =
      compare
        (retainedCompleteLigandPriorKeyAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph leftStages.a.tree) W D)
        (retainedCompleteLigandPriorKeyAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph rightStages.a.tree) W D) := by
  have dataL := retainedGeneratedCompound_independentReadback input singleBonded target unit
    targetUnit cursorL childL leftStages leftWidth leftDepth builtL
  have dataR := retainedGeneratedCompound_independentReadback input singleBonded target unit
    targetUnit cursorR childR rightStages rightWidth rightDepth builtR
  let readL := retainedGeneratedStageReadingFacts input singleBonded target unit targetUnit
    cursorL childL leftStages
  let readR := retainedGeneratedStageReadingFacts input singleBonded target unit targetUnit
    cursorR childR rightStages
  let isoL := ruleMajorContextStageGraphIsoBundle_of_stages leftStages
  let isoR := ruleMajorContextStageGraphIsoBundle_of_stages rightStages
  have initialCompare := retainedGeneratedContextTrees_rule4a_compare input singleBonded target
    unit targetUnit leftStages.a.tree rightStages.a.tree leftStages.a.trace rightStages.a.trace
    (by simpa only [leftStages.a.sourceEq] using childL)
    (by simpa only [rightStages.a.sourceEq] using childR)
    (leftStages.a_width_le.trans leftWidth) (rightStages.a_width_le.trans rightWidth)
    (leftStages.a_depth_le.trans leftDepth) (rightStages.a_depth_le.trans rightDepth)
  change (input.certified.compareLocalizedRerootCumulativeRule45Keys left.prior.rule4aKey
    right.prior.rule4aKey).then
      (input.certified.compareLocalizedRerootCompoundRule4bcAfterRule4a left.prior right.prior) =
    (compare
      (retainedMolecularRankPairAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph leftStages.a.tree) W D)
      (retainedMolecularRankPairAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph rightStages.a.tree) W D)).then _
  have rankEq :
      input.certified.compareLocalizedRerootCumulativeRule45Keys left.prior.rule4aKey
        right.prior.rule4aKey =
      compare
        (retainedMolecularRankPairAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph leftStages.a.tree) W D)
        (retainedMolecularRankPairAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph rightStages.a.tree) W D) := by
    rw [dataL.aKey, dataR.aKey]
    simpa [retainedMolecularRankPairAt] using initialCompare
  rw [rankEq]
  exact then_congr fun tied =>
    compound_after4a_compare singleBonded leftStages rightStages
      (LocalizedRuleMajorReference.descriptorMap input) unit readL readR isoL isoR
      leftWidth leftDepth rightWidth rightDepth dataL dataR (by
        rw [← dataL.aKey, ← dataR.aKey, rankEq]
        exact tied)

end
end TetraStereo.OneCenter.RetainedContextCompoundComparison

assert_kernel_only TetraStereo.OneCenter.RetainedContextCompoundComparison.retainedContextTrees_scalar4b_compare
assert_kernel_only TetraStereo.OneCenter.RetainedContextCompoundComparison.retainedContextTrees_scalar4c_compare
assert_kernel_only TetraStereo.OneCenter.RetainedContextCompoundComparison.retainedContextTrees_noReference4c_compare
assert_kernel_only TetraStereo.OneCenter.RetainedContextCompoundComparison.retainedCrossBranch_selectedB_compare
assert_kernel_only TetraStereo.OneCenter.RetainedContextCompoundComparison.retainedCrossBranch_selectedC_compare
assert_kernel_only TetraStereo.OneCenter.RetainedContextCompoundComparison.retainedCrossBranch_noReference_compare
assert_kernel_only TetraStereo.OneCenter.RetainedContextCompoundComparison.retainedStages_RS_completeReading_compare
assert_kernel_only TetraStereo.OneCenter.RetainedContextCompoundComparison.retainedStages_rankReadings_observations
assert_kernel_only TetraStereo.OneCenter.RetainedContextCompoundComparison.retainedStages_rankedReferenceTags
assert_kernel_only TetraStereo.OneCenter.RetainedContextCompoundComparison.retainedStages_compound_independentReadback
assert_kernel_only TetraStereo.OneCenter.RetainedContextCompoundComparison.retainedGeneratedStageReadingFacts
assert_kernel_only TetraStereo.OneCenter.RetainedContextCompoundComparison.retainedGeneratedCompound_independentReadback
assert_kernel_only TetraStereo.OneCenter.RetainedContextCompoundComparison.retainedGeneratedCompound_prior_compare
