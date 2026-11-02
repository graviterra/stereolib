import TetraStereo.OneCenter.LocalizedRuleMajorActualAlternativeOrdering
import TetraStereo.OneCenter.LocalizedContextCompleteReadingComparison
import TetraStereo.OneCenter.LocalizedContextBranchStages
import TetraStereo.OneCenter.LocalizedContextCompoundReadback
import TetraStereo.OneCenter.LocalizedContextIncomingEdge
import TetraStereo.OneCenter.LocalizedContextSourceFaithfulness
import TetraStereo.OneCenter.DeclarativeCIPObservedCompleteReadingSignature
import TetraStereo.OneCenter.DeclarativeCIPContextualRule5Order
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Complete reading order for the actual alternative stages at one arbitrary context cursor.
The reference and pseudoasymmetric components are first compared on their executed graphs, then
transported to the `.rule4a` graph by rooted faithful-expansion isomorphisms. -/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree DeclarativeCIP
open Rule4cObservationBridge
noncomputable section
open scoped Classical

local instance contextStageTreeNodeFintype {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    Fintype (ruleMajorTreeGraph tree).Node := (ruleMajorTreeGraph tree).nodeFintype

/-- The actual tree observations agree with the retained-root constitutional observer at every
decorated subtree. -/
def ContextTreeContextualObservationsAt {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (unit : DetectedOccurrence input.moleculeGraph) : Prop :=
  ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
    contextualNodeObservation input.moleculeGraph (ruleMajorTreeGraph tree) unit.1.root rule node =
      priorityValue rule (armObservation rule actual)

/-- Readback facts for all six actual Rule-4a/4b/4c/no-reference graphs in one shared context. -/
structure RuleMajorContextReadingReadbacks {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} {read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel} {cursor : input.LocalizedRerootCursor carrierFuel}
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) : Prop where
  aReadback : ContextTreeRankReadback stages.a.tree descriptorMap unit
  aObservations : ContextTreeContextualObservationsAt stages.a.tree unit
  bReadback : ∀ reference, ContextTreeRankReadback (stages.b reference).tree descriptorMap unit
  bObservations : ∀ reference,
    ContextTreeContextualObservationsAt (stages.b reference).tree unit
  cReadback : ∀ reference, ContextTreeRankReadback (stages.c reference).tree descriptorMap unit
  cObservations : ∀ reference,
    ContextTreeContextualObservationsAt (stages.c reference).tree unit
  noReferenceReadback : ContextTreeRankReadback stages.noReference.tree descriptorMap unit
  noReferenceObservations : ContextTreeContextualObservationsAt stages.noReference.tree unit

/-- Rooted graph isomorphisms from each actual contextual stage graph to the `.rule4a` graph.
The incoming-source bridge constructs this bundle from the same actual cursor. -/
structure RuleMajorContextStageGraphIsoBundle {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} {read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel} {cursor : input.LocalizedRerootCursor carrierFuel}
    (stages : input.RuleMajorContextStages carrierFuel read cursor) where
  b : ∀ reference, RootedDigraph.Iso (ruleMajorTreeGraph stages.a.tree)
    (ruleMajorTreeGraph (stages.b reference).tree)
  c : ∀ reference, RootedDigraph.Iso (ruleMajorTreeGraph stages.a.tree)
    (ruleMajorTreeGraph (stages.c reference).tree)
  noReference : RootedDigraph.Iso (ruleMajorTreeGraph stages.a.tree)
    (ruleMajorTreeGraph stages.noReference.tree)

/-- Actual rule-major R/S alternatives compare exactly as their independent contextual complete
readings on one common graph, the actual `.rule4a` graph. Earlier prefixes are derived from the
five actual stage builds in this same context. -/
theorem ruleMajorContextStages_RS_completeReading_compare
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    {W D : Nat}
    (width : stages.widthBound ≤ W)
    (depth : stages.depthBound ≤ D)
    (readbacks : RuleMajorContextReadingReadbacks stages descriptorMap unit)
    (isomorphisms : RuleMajorContextStageGraphIsoBundle stages) :
    input.compareRule4bcReadingsComplete
        { reference? := some .R
          rule4bKey := (stages.b .R).key
          rule4cKey := (stages.c .R).key }
        { reference? := some .S
          rule4bKey := (stages.b .S).key
          rule4cKey := (stages.c .S).key } =
      compare
        (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph stages.a.tree) W D
          (some .senior))
        (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph stages.a.tree) W D
          (some .junior)) := by
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
  have scalarB := contextTrees_ruleMajor_scalar4b_compare singleBonded
    (stages.b .R).tree (stages.b .S).tree (stages.b .R).trace (stages.b .S).trace
    (readbacks.bReadback .R) (readbacks.bReadback .S)
    (readbacks.bObservations .R) (readbacks.bObservations .S)
    (W := W) (D := D)
    (Nat.le_trans (stages.b_width_le .R) width)
    (Nat.le_trans (stages.b_depth_le .R) depth)
    (Nat.le_trans (stages.b_width_le .S) width)
    (Nat.le_trans (stages.b_depth_le .S) depth)
    tiedBR tiedBR4a
  have scalarC := contextTrees_ruleMajor_scalar4c_compare singleBonded
    (stages.c .R).tree (stages.c .S).tree (stages.c .R).trace (stages.c .S).trace
    (readbacks.cReadback .R) (readbacks.cReadback .S)
    (readbacks.cObservations .R) (readbacks.cObservations .S)
    (W := W) (D := D)
    (Nat.le_trans (stages.c_width_le .R) width)
    (Nat.le_trans (stages.c_depth_le .R) depth)
    (Nat.le_trans (stages.c_width_le .S) width)
    (Nat.le_trans (stages.c_depth_le .S) depth)
    tiedCR tiedCR4a
  have readB : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4b (stages.b .R).key) (scalar4b (stages.b .S).key) =
      compare
        (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit graphBR
          W D (some .senior))).1
        (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit graphBS
          W D (some .junior))).1 := by
    simpa [contextualCompleteReadingAt, senseOf] using scalarB
  have readC : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4c (stages.c .R).key) (scalar4c (stages.c .S).key) =
      compare
        (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit graphCR
          W D (some .senior))).2
        (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit graphCS
          W D (some .junior))).2 := by
    simpa [contextualCompleteReadingAt, senseOf] using scalarC
  have readBCommon : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4b (stages.b .R).key) (scalar4b (stages.b .S).key) =
      compare
        (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit commonGraph
          W D (some .senior))).1
        (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit commonGraph
          W D (some .junior))).1 := by
    calc
      _ = compare
          (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit graphBR
            W D (some .senior))).1
          (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit graphBS
            W D (some .junior))).1 := readB
      _ = _ := by
          rw [contextualCompleteReadingAt_iso input.moleculeGraph descriptorMap unit
                (isomorphisms.b .R) W D (some .senior),
              contextualCompleteReadingAt_iso input.moleculeGraph descriptorMap unit
                (isomorphisms.b .S) W D (some .junior)]
  have readCCommon : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4c (stages.c .R).key) (scalar4c (stages.c .S).key) =
      compare
        (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit commonGraph
          W D (some .senior))).2
        (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit commonGraph
          W D (some .junior))).2 := by
    calc
      _ = compare
          (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit graphCR
            W D (some .senior))).2
          (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit graphCS
            W D (some .junior))).2 := readC
      _ = _ := by
          rw [contextualCompleteReadingAt_iso input.moleculeGraph descriptorMap unit
                (isomorphisms.c .R) W D (some .senior),
              contextualCompleteReadingAt_iso input.moleculeGraph descriptorMap unit
                (isomorphisms.c .S) W D (some .junior)]
  rw [completeReading_compare_eq_then]
  change
    (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      (stages.b .R).key.descriptor (stages.b .S).key.descriptor).then
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (stages.c .R).key.descriptor (stages.c .S).key.descriptor) =
      (compare
        (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit commonGraph
          W D (some .senior))).1
        (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit commonGraph
          W D (some .junior))).1).then
        (compare
          (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit commonGraph
            W D (some .senior))).2
          (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit commonGraph
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

/-- Compile one selected context alternative from its actual stage family. The no-reference case
keeps the genuine `.rule4a` and no-reference Rule-4c keys. -/
abbrev ruleMajorContextBranchReading {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} {read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel} {cursor : input.LocalizedRerootCursor carrierFuel}
    (stages : input.RuleMajorContextStages carrierFuel read cursor) :
    Option RS → input.LocalizedRerootRule4bcReading :=
  CertifiedLocalizedCIPInput.contextStageReading stages

/-- The actual alternatives selected by the independent contextual reference population. -/
def ruleMajorContextBranchReadings {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} {read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel} {cursor : input.LocalizedRerootCursor carrierFuel}
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) :
    List input.LocalizedRerootRule4bcReading :=
  (localizedRule4bcReferenceAlternatives
    (toReferenceList (contextualReferenceSelection input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph stages.a.tree)))).map (ruleMajorContextBranchReading stages)

/-- After actual `rankReadings`, mapping each alternative to its independent contextual complete
reading gives the full contextual list selected on the same physical molecule. This covers empty,
single, and paired reference populations; lowercase pseudo labels remain visible in the none case. -/
theorem ruleMajorContextStages_rankReadings_observations
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    {W D : Nat}
    (width : stages.widthBound ≤ W)
    (depth : stages.depthBound ≤ D)
    (readbacks : RuleMajorContextReadingReadbacks stages descriptorMap unit)
    (isomorphisms : RuleMajorContextStageGraphIsoBundle stages) :
    (input.rankReadings (ruleMajorContextBranchReadings stages descriptorMap unit)).map
      (fun reading => contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) W D
        (reading.reference?.map senseOf)) =
      contextualCompleteReadingsAt input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph stages.a.tree) W D := by
  cases selectionEq : contextualReferenceSelection input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph stages.a.tree) with
  | empty =>
      simp [ruleMajorContextBranchReadings, ruleMajorContextBranchReading, rankReadings,
        contextStageReading, localizedRule4bcReferenceAlternatives, toReferenceList,
        contextualCompleteReadingsAt, contextualCompleteReadingAt, selectionEq]
  | one sense =>
      cases sense with
      | senior =>
          simp [ruleMajorContextBranchReadings, ruleMajorContextBranchReading, rankReadings,
            contextStageReading, localizedRule4bcReferenceAlternatives, toReferenceList,
            contextualCompleteReadingsAt, contextualCompleteReadingAt, selectionEq, senseOf]
      | junior =>
          simp [ruleMajorContextBranchReadings, ruleMajorContextBranchReading, rankReadings,
            contextStageReading, localizedRule4bcReferenceAlternatives, toReferenceList,
            contextualCompleteReadingsAt, contextualCompleteReadingAt, selectionEq, senseOf]
  | both =>
      have comparison := ruleMajorContextStages_RS_completeReading_compare singleBonded stages
        descriptorMap unit width depth readbacks isomorphisms
      have selectedReadings : ruleMajorContextBranchReadings stages descriptorMap unit =
          [contextStageReading stages (some .R), contextStageReading stages (some .S)] := by
        simp [ruleMajorContextBranchReadings, localizedRule4bcReferenceAlternatives,
          toReferenceList, selectionEq]
      rw [selectedReadings]
      simp only [rankReadings, contextStageReading]
      rw [comparison]
      simp only [contextualCompleteReadingsAt, selectionEq]
      split_ifs with h
      · simpa only [List.map_cons, List.map_nil, Option.map_some, senseOf, if_pos h] using
          (completeReading_descendingPair
            (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
              (ruleMajorTreeGraph stages.a.tree) W D (some .senior))
            (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
              (ruleMajorTreeGraph stages.a.tree) W D (some .junior)))
      · simpa only [List.map_cons, List.map_nil, Option.map_some, senseOf, if_neg h] using
          (completeReading_descendingPair
            (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
              (ruleMajorTreeGraph stages.a.tree) W D (some .senior))
            (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
              (ruleMajorTreeGraph stages.a.tree) W D (some .junior)))

/-- Ranked actual alternatives retain exactly the contextual reference tags. This records the
R/S identity order needed by Rule 5; if the complete readings tie, both sides retain R before S. -/
theorem ruleMajorContextStages_rankedReferenceTags
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (readbacks : RuleMajorContextReadingReadbacks stages descriptorMap unit)
    (isomorphisms : RuleMajorContextStageGraphIsoBundle stages) {W D : Nat}
    (width : stages.widthBound ≤ W) (depth : stages.depthBound ≤ D) :
    (input.rankReadings (ruleMajorContextBranchReadings stages descriptorMap unit)).map
      (fun reading => reading.reference?.map senseOf) =
      DeclarativeCIP.contextualTaggedAlternativeReferencesAt input.moleculeGraph
        descriptorMap unit (ruleMajorTreeGraph stages.a.tree) W D := by
  cases selectionEq : contextualReferenceSelection input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph stages.a.tree) with
  | empty =>
      simp [ruleMajorContextBranchReadings, ruleMajorContextBranchReading, rankReadings,
        contextStageReading, localizedRule4bcReferenceAlternatives, toReferenceList,
        DeclarativeCIP.contextualTaggedAlternativeReferencesAt, selectionEq]
  | one sense =>
      cases sense with
      | senior =>
          simp [ruleMajorContextBranchReadings, ruleMajorContextBranchReading, rankReadings,
            contextStageReading, localizedRule4bcReferenceAlternatives, toReferenceList,
            DeclarativeCIP.contextualTaggedAlternativeReferencesAt, selectionEq, senseOf]
      | junior =>
          simp [ruleMajorContextBranchReadings, ruleMajorContextBranchReading, rankReadings,
            contextStageReading, localizedRule4bcReferenceAlternatives, toReferenceList,
            DeclarativeCIP.contextualTaggedAlternativeReferencesAt, selectionEq, senseOf]
  | both =>
      have comparison := ruleMajorContextStages_RS_completeReading_compare singleBonded stages
        descriptorMap unit width depth readbacks isomorphisms
      have selectedReadings : ruleMajorContextBranchReadings stages descriptorMap unit =
          [contextStageReading stages (some .R), contextStageReading stages (some .S)] := by
        simp [ruleMajorContextBranchReadings, localizedRule4bcReferenceAlternatives,
          toReferenceList, selectionEq]
      rw [selectedReadings]
      simp only [rankReadings, contextStageReading]
      rw [comparison]
      simp only [DeclarativeCIP.contextualTaggedAlternativeReferencesAt, selectionEq]
      split_ifs with h
      · simp only [List.map_cons, List.map_nil, Option.map_some, senseOf]
      · simp only [List.map_cons, List.map_nil, Option.map_some, senseOf]

/-- Turn one generated-reader stage trace into the actual executable-child membership needed by
the generated semantic readback lemmas. -/
private theorem contextArm_tree_is_actualChild
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor carrierFuel} {stage : LocalizedCumulativeRule45Stage}
    (target : input.LocalizedRerootCursor carrierFuel)
    (cursorChild : cursor ∈ input.executableLocalizedRerootChildren target)
    (arm : input.RuleMajorContextArm carrierFuel stage read cursor) :
    arm.tree.source ∈ input.executableLocalizedRerootChildren target := by
  rw [arm.sourceEq]
  exact cursorChild

private theorem generatedContextTreeObservations
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input.certified
      (input.certified.certified.input.molecule.atomCount + 1))
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) tree)
    (actualChild : tree.source ∈ input.certified.executableLocalizedRerootChildren target) :
    ContextTreeContextualObservationsAt tree unit := by
  have rootEq := contextTree_outerRoot_eq_unitRoot singleBonded acyclic target unit targetUnit
    tree actualChild
  intro rule node actual lookup
  rw [← rootEq]
  exact contextualTree_nodeObservation singleBonded acyclic tree realizes rule node actual lookup

/-- All actual stage trees at one executable context child inherit the generated-reader
readbacks and the independently proved retained-root observer equations. -/
theorem ruleMajorContextReadingReadbacks_of_generatedActualChild
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursor : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (cursorChild : cursor ∈ input.certified.executableLocalizedRerootChildren target)
    (stages : input.certified.RuleMajorContextStages
      (input.certified.certified.input.molecule.atomCount + 1)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursor) :
    RuleMajorContextReadingReadbacks stages (LocalizedRuleMajorReference.descriptorMap input) unit := by
  have actualA := contextArm_tree_is_actualChild target cursorChild stages.a
  have realizesA := LocalizedRuleMajorSortTrace.realizes_of_trace stages.a.trace
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ruleMajorGeneratedContextTreeRankReadback input singleBonded acyclic target unit
      targetUnit stages.a.tree realizesA actualA
  · exact generatedContextTreeObservations input singleBonded acyclic target unit targetUnit
      stages.a.tree realizesA actualA
  · intro reference
    have actual := contextArm_tree_is_actualChild target cursorChild (stages.b reference)
    exact ruleMajorGeneratedContextTreeRankReadback input singleBonded acyclic target unit
      targetUnit (stages.b reference).tree
      (LocalizedRuleMajorSortTrace.realizes_of_trace (stages.b reference).trace) actual
  · intro reference
    have actual := contextArm_tree_is_actualChild target cursorChild (stages.b reference)
    exact generatedContextTreeObservations input singleBonded acyclic target unit targetUnit
      (stages.b reference).tree
      (LocalizedRuleMajorSortTrace.realizes_of_trace (stages.b reference).trace) actual
  · intro reference
    have actual := contextArm_tree_is_actualChild target cursorChild (stages.c reference)
    exact ruleMajorGeneratedContextTreeRankReadback input singleBonded acyclic target unit
      targetUnit (stages.c reference).tree
      (LocalizedRuleMajorSortTrace.realizes_of_trace (stages.c reference).trace) actual
  · intro reference
    have actual := contextArm_tree_is_actualChild target cursorChild (stages.c reference)
    exact generatedContextTreeObservations input singleBonded acyclic target unit targetUnit
      (stages.c reference).tree
      (LocalizedRuleMajorSortTrace.realizes_of_trace (stages.c reference).trace) actual
  · have actual := contextArm_tree_is_actualChild target cursorChild stages.noReference
    exact ruleMajorGeneratedContextTreeRankReadback input singleBonded acyclic target unit
      targetUnit stages.noReference.tree
      (LocalizedRuleMajorSortTrace.realizes_of_trace stages.noReference.trace) actual
  · have actual := contextArm_tree_is_actualChild target cursorChild stages.noReference
    exact generatedContextTreeObservations input singleBonded acyclic target unit targetUnit
      stages.noReference.tree
      (LocalizedRuleMajorSortTrace.realizes_of_trace stages.noReference.trace) actual

/-- Faithfulness of a generated context arm follows from its actual incoming occurrence and
source equality; no fresh-root or manually supplied graph agreement is used. -/
private theorem generatedContextArm_faithful_of_incoming
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor carrierFuel} {stage : LocalizedCumulativeRule45Stage}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (arm : input.RuleMajorContextArm carrierFuel stage read cursor)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid cursor)
    (sameRoot : cursor.occurrence.1.root = previous.1.root)
    {currentAtom previousAtom : input.Atom}
    (currentObserved : cursor.occurrence.1.node.current? = some currentAtom)
    (previousObserved : previous.1.node.current? = some previousAtom)
    (incomingEdge : input.moleculeGraph.Adj previousAtom currentAtom) :
    RootedDigraph.FaithfulExactExpansion input.moleculeGraph previousAtom currentAtom
      (ruleMajorTreeGraph arm.tree) := by
  apply ruleMajorTreeGraph_faithfulExactExpansion singleBonded acyclic enough
    (LocalizedRuleMajorSortTrace.realizes_of_trace arm.trace) previous ?_ ?_ ?_
    ?_ previousObserved incomingEdge
  · rw [arm.sourceEq]
    exact previousEq
  · rw [arm.sourceEq]
    exact valid
  · rw [arm.sourceEq]
    exact sameRoot
  · rw [arm.sourceEq]
    exact currentObserved

/-- Once actual cursor data supplies a common incoming edge, all actual stage graphs are rooted
isomorphic to the `.rule4a` graph by uniqueness of faithful exact expansions. -/
noncomputable def ruleMajorContextStageGraphIsoBundle_of_incomingData
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (sameRoot : cursor.occurrence.1.root = previous.1.root)
    {currentAtom previousAtom : input.Atom}
    (currentObserved : cursor.occurrence.1.node.current? = some currentAtom)
    (previousObserved : previous.1.node.current? = some previousAtom)
    (incomingEdge : input.moleculeGraph.Adj previousAtom currentAtom) :
    RuleMajorContextStageGraphIsoBundle stages := by
  have faithfulA := generatedContextArm_faithful_of_incoming singleBonded acyclic enough
    stages.a previous previousEq valid sameRoot currentObserved previousObserved incomingEdge
  have isoOfArm : ∀ {stage : LocalizedCumulativeRule45Stage}
      (arm : input.RuleMajorContextArm carrierFuel stage read cursor),
      RootedDigraph.Iso (ruleMajorTreeGraph stages.a.tree) (ruleMajorTreeGraph arm.tree) := by
    intro stage arm
    have faithfulArm := generatedContextArm_faithful_of_incoming singleBonded acyclic enough
      arm previous previousEq valid sameRoot currentObserved previousObserved incomingEdge
    exact Classical.choice (RootedDigraph.faithfulExactExpansion_unique_up_to_iso
      input.moleculeGraph previousAtom currentAtom (ruleMajorTreeGraph stages.a.tree)
      (ruleMajorTreeGraph arm.tree) faithfulA faithfulArm)
  exact ⟨fun reference => isoOfArm (stages.b reference),
    fun reference => isoOfArm (stages.c reference), isoOfArm stages.noReference⟩

/-- Executable child membership is enough to construct the actual stage graph bundle. The result
uses classical choice only to select one isomorphism guaranteed by faithful expansion uniqueness. -/
theorem ruleMajorContextStageGraphIsoBundle_nonempty_of_generatedActualChild
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (cursor : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (cursorChild : cursor ∈ input.certified.executableLocalizedRerootChildren target)
    (stages : input.certified.RuleMajorContextStages
      (input.certified.certified.input.molecule.atomCount + 1)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursor) :
    Nonempty (RuleMajorContextStageGraphIsoBundle stages) := by
  obtain ⟨targetAtom, childAtom, targetObserved, childObserved, previousEq, sameRoot, valid,
    incomingEdge⟩ := input.certified.executableLocalizedRerootChild_incomingData
      singleBonded acyclic target cursor cursorChild
  have enough : input.certified.certified.input.molecule.atomCount ≤
      input.certified.certified.input.molecule.atomCount + 1 := by omega
  exact ⟨ruleMajorContextStageGraphIsoBundle_of_incomingData singleBonded acyclic enough stages
    valid target.occurrence previousEq sameRoot childObserved targetObserved incomingEdge⟩

/-- Chosen actual child graph isomorphisms to the `.rule4a` graph, with all incoming facts
derived from executable cursor membership. -/
noncomputable def ruleMajorContextStageGraphIsoBundle_of_generatedActualChild
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (cursor : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (cursorChild : cursor ∈ input.certified.executableLocalizedRerootChildren target)
    (stages : input.certified.RuleMajorContextStages
      (input.certified.certified.input.molecule.atomCount + 1)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursor) :
    RuleMajorContextStageGraphIsoBundle stages :=
  Classical.choice (ruleMajorContextStageGraphIsoBundle_nonempty_of_generatedActualChild
    input singleBonded acyclic target cursor cursorChild stages)

/-- The generated actual-child wrapper derives path validity, the common incoming edge,
stage-graph isomorphisms, and all molecular readbacks from the executable child itself. -/
theorem generatedRuleMajorContextStages_completeReadingOrder
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursor : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (cursorChild : cursor ∈ input.certified.executableLocalizedRerootChildren target)
    (stages : input.certified.RuleMajorContextStages
      (input.certified.certified.input.molecule.atomCount + 1)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursor)
    {W D : Nat}
    (width : stages.widthBound ≤ W) (depth : stages.depthBound ≤ D) :
    input.certified.compareRule4bcReadingsComplete
        { reference? := some .R
          rule4bKey := (stages.b .R).key
          rule4cKey := (stages.c .R).key }
        { reference? := some .S
          rule4bKey := (stages.b .S).key
          rule4cKey := (stages.c .S).key } =
      compare
        (contextualCompleteReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph stages.a.tree) W D (some .senior))
        (contextualCompleteReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph stages.a.tree) W D (some .junior)) ∧
    (input.certified.rankReadings
      (ruleMajorContextBranchReadings stages (LocalizedRuleMajorReference.descriptorMap input) unit)).map
        (fun reading => contextualCompleteReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph stages.a.tree) W D (reading.reference?.map senseOf)) =
      contextualCompleteReadingsAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph stages.a.tree) W D ∧
    (input.certified.rankReadings
      (ruleMajorContextBranchReadings stages (LocalizedRuleMajorReference.descriptorMap input) unit)).map
        (fun reading => reading.reference?.map senseOf) =
      DeclarativeCIP.contextualTaggedAlternativeReferencesAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph stages.a.tree) W D := by
  let readbacks := ruleMajorContextReadingReadbacks_of_generatedActualChild input singleBonded
    acyclic target unit targetUnit cursor cursorChild stages
  obtain ⟨targetAtom, childAtom, targetObserved, childObserved, previousEq, sameRoot, valid,
    incomingEdge⟩ := input.certified.executableLocalizedRerootChild_incomingData
      singleBonded acyclic target cursor cursorChild
  have enough : input.certified.certified.input.molecule.atomCount ≤
      input.certified.certified.input.molecule.atomCount + 1 := by omega
  let isomorphisms := ruleMajorContextStageGraphIsoBundle_of_incomingData singleBonded acyclic
    enough stages valid target.occurrence previousEq sameRoot childObserved targetObserved incomingEdge
  have compare := ruleMajorContextStages_RS_completeReading_compare singleBonded stages
    (LocalizedRuleMajorReference.descriptorMap input) unit width depth readbacks isomorphisms
  have readings := ruleMajorContextStages_rankReadings_observations singleBonded stages
    (LocalizedRuleMajorReference.descriptorMap input) unit width depth readbacks isomorphisms
  have tags := ruleMajorContextStages_rankedReferenceTags singleBonded stages
    (LocalizedRuleMajorReference.descriptorMap input) unit readbacks isomorphisms width depth
  exact ⟨compare, readings, tags⟩


end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ContextTreeContextualObservationsAt
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.RuleMajorContextReadingReadbacks
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.RuleMajorContextStageGraphIsoBundle
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorContextStages_RS_completeReading_compare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorContextBranchReading
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorContextBranchReadings
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorContextStages_rankReadings_observations
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorContextStages_rankedReferenceTags
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorContextReadingReadbacks_of_generatedActualChild
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorContextStageGraphIsoBundle_of_incomingData
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorContextStageGraphIsoBundle_nonempty_of_generatedActualChild
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorContextStageGraphIsoBundle_of_generatedActualChild
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.generatedRuleMajorContextStages_completeReadingOrder
