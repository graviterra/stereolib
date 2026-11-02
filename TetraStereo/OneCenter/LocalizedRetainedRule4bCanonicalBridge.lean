import TetraStereo.OneCenter.LocalizedContextRule4bCanonicalBridge
import TetraStereo.OneCenter.DeclarativeCIPRetainedStereoEvidence
import TetraStereo.OneCenter.LocalizedRetainedContextObservationReadback
import TetraStereo.OneCenter.LocalizedRetainedContextStereoReadback
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! Retained Rule-4b canonicality for an arbitrary realized contextual tree.

The induction follows the actual rule-major sort trace. Constitutional order is the accepted
observed-tree bridge. At each node the empty-path columns are fieldwise facts:

* a real available reading keeps the ordinary Rule-4a and Rule-4b scalars;
* a ring duplicate is present nonstereogenic at Rule 4a, because its localized label is `none`
  and that priority is `0`, while Rule 4b stays absent;
* a real `.unavailable` reading is not rewritten as nonstereogenic, so the old available-only
  Rule-4a lemma is not applied to a duplicate.

`RetainedRule4bFieldFacts` is this file's interface. Node identity is the shared
`RetainedRankNodeStatus`. `RetainedContextTreeRankReadback` stays the Rule-4a-only bundle:
this module imports `retainedGeneratedContextTreeRankReadback` and does not re-prove it or the
stage-`.rule4a` bridge. Constitutional observations come from the retained observation readback.
The specialization covers every executable child of an arbitrary detected target, with no
acyclicity, all-real, or original-root hypothesis.
-/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree CertifiedLocalizedCIPInput
open OfficialSparseCanonicalVectorComparison DeclarativeCIP RetainedContextStereoReadback
noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}

/-- Label, tetrahedral reading, and the shared real-available/ring status at every node. -/
structure RetainedRule4bFieldFacts
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) : Prop where
  label : ∀ (node : (ruleMajorTreeGraph tree).Node)
      (actual : LocalizedCumulativeDecoratedTree input carrierFuel),
      subtreeAt? tree node.1 = some actual →
        actual.label =
          (occurrenceReading input.moleculeGraph descriptorMap unit
            (ruleMajorTreeGraph tree) node).toLocalizedLabel
  tetrahedral : ∀ node : (ruleMajorTreeGraph tree).Node,
    (occurrenceReading input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph tree) node).IsTetrahedral
  realAvailableOrRing : ∀ node : (ruleMajorTreeGraph tree).Node,
    RetainedRankNodeStatus input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph tree) node

/-- Empty-path Rule 4a. Real available nodes use the ordinary kind code. Ring duplicates use
the present nonstereogenic code, which is the runtime priority of `none`. -/
theorem retainedRule4b_nil4a
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (graph : RootedDigraph input.Atom)
    (observe : ConstitutionalRule → graph.Node → ℤ) (W D : Nat) (node : graph.Node)
    {actual : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key} {ρ : RS}
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) actual key)
    (realizes : LocalizedCumulativeTreeRealizes input read actual)
    (label : actual.label =
      (occurrenceReading input.moleculeGraph descriptorMap unit graph node).toLocalizedLabel)
    (tetra : (occurrenceReading input.moleculeGraph descriptorMap unit graph node).IsTetrahedral)
    (status : RetainedRankNodeStatus input.moleculeGraph descriptorMap unit graph node) :
    observedStereoNodePathObservation graph observe
      (retainedReadingEvidence input.moleculeGraph descriptorMap unit graph (senseOf ρ)) W D
      .rule4aStereogenicUnitKind node [] = encoded4a key [] := by
  cases status with
  | realAvailable real available =>
      have notDuplicate := not_ringDuplicate_of_realAtom graph node real
      have evidenceEq := retainedReadingEvidence_eq_readingEvidence_of_not_ringDuplicate
        input.moleculeGraph descriptorMap unit graph (senseOf ρ) node notDuplicate
      have labelEq : stereoLabel graph
          (retainedReadingEvidence input.moleculeGraph descriptorMap unit graph (senseOf ρ))
          .rule4aStereogenicUnitKind node =
        stereoLabel graph
          (readingEvidence input.moleculeGraph descriptorMap unit graph (senseOf ρ))
          .rule4aStereogenicUnitKind node := by
        unfold stereoLabel
        rw [evidenceEq]
      rw [observedStereoNodePathObservation_nil, labelEq,
        stereoLabel_readingEvidence_rule4a,
        stereoLabel_rankEvidence_rule4a descriptorMap unit graph node available,
        encoded4a_nil_rule4b tableMatch realizes,
        prio4a_eq_kindPriority actual _ label tetra]
  | ringDuplicate distance duplicate _unavailable noneLabel =>
      have same4a : stereoLabel graph
          (retainedReadingEvidence input.moleculeGraph descriptorMap unit graph (senseOf ρ))
          .rule4aStereogenicUnitKind node =
        stereoLabel graph (retainedRankEvidence input.moleculeGraph descriptorMap unit graph)
          .rule4aStereogenicUnitKind node := by
        unfold stereoLabel stereoValue retainedReadingEvidence retainedRankEvidence
        rfl
      rw [observedStereoNodePathObservation_nil, same4a,
        stereoLabel_retainedRankEvidence_rule4a_ringDuplicate_eq_code descriptorMap unit graph
          node distance duplicate,
        encoded4a_nil_rule4b tableMatch realizes]
      have priorityZero : prio4a actual = StereogenicUnitKind.nonstereogenic.priority := by
        unfold prio4a
        rw [label, noneLabel]
        simp [localizedRule4aPriority, StereogenicUnitKind.priority]
      rw [priorityZero]

/-- Empty-path Rule 4b. The retained column is the ordinary eligible-sense column, so a ring
duplicate stays absent. Availability is not required. -/
theorem retainedRule4b_nil4b
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (graph : RootedDigraph input.Atom)
    (observe : ConstitutionalRule → graph.Node → ℤ) (W D : Nat) (node : graph.Node)
    {actual : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key} {ρ : RS}
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) actual key)
    (realizes : LocalizedCumulativeTreeRealizes input read actual)
    (label : actual.label =
      (occurrenceReading input.moleculeGraph descriptorMap unit graph node).toLocalizedLabel)
    (tetra : (occurrenceReading input.moleculeGraph descriptorMap unit graph node).IsTetrahedral) :
    observedStereoNodePathObservation graph observe
      (retainedReadingEvidence input.moleculeGraph descriptorMap unit graph (senseOf ρ)) W D
      .rule4bLikeUnlikeDescriptorPairs node [] = encoded4b key [] := by
  rw [observedStereoNodePathObservation_nil]
  have same4b : stereoLabel graph
      (retainedReadingEvidence input.moleculeGraph descriptorMap unit graph (senseOf ρ))
      .rule4bLikeUnlikeDescriptorPairs node =
    stereoLabel graph
      (readingEvidence input.moleculeGraph descriptorMap unit graph (senseOf ρ))
      .rule4bLikeUnlikeDescriptorPairs node := by
    unfold stereoLabel stereoValue retainedReadingEvidence readingEvidence
    rfl
  rw [same4b]
  have old := stereoNodePathObservation_nil_eq_encoded4b descriptorMap unit graph W D node
    tableMatch realizes label tetra
  rw [stereoNodePathObservation_nil] at old
  exact old

/-- Single-bond retained reading evidence observes only Rules 4a and 4b. -/
theorem retainedRule4b_rule4abOnly_of_simpleBonded
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (graph : RootedDigraph input.Atom)
    (reference : DescriptorSense) :
    Rule4abOnly graph
      (retainedReadingEvidence input.moleculeGraph descriptorMap unit graph reference) := by
  intro rule not4a not4b node
  have single : ∀ atom other, input.moleculeGraph.bond atom other ≤ 1 := by
    intro atom other
    rcases Nat.eq_zero_or_pos (input.moleculeGraph.bond atom other) with zero | positive
    · rw [zero]
      exact Nat.zero_le 1
    · exact le_of_eq (singleBonded atom other positive)
  cases rule with
  | rule4aStereogenicUnitKind => exact (not4a rfl).elim
  | rule4bLikeUnlikeDescriptorPairs => exact (not4b rfl).elim
  | rule3DoubleBondGeometry =>
      have absent := molecularEvidence_rule3_eq_none input.moleculeGraph single descriptorMap
        unit graph node
      change rule3Observation input.moleculeGraph descriptorMap unit graph node = none at absent
      show stereoValue .rule3DoubleBondGeometry
        (some (retainedReadingEvidence input.moleculeGraph descriptorMap unit graph reference
          node)) = ⊥
      simp [stereoValue, retainedReadingEvidence, absent, liftObservation]
  | rule4cPseudoasymmetricDescriptor =>
      show stereoValue .rule4cPseudoasymmetricDescriptor
        (some (retainedReadingEvidence input.moleculeGraph descriptorMap unit graph reference
          node)) = ⊥
      simp [stereoValue, retainedReadingEvidence, liftObservation]
  | rule5EnantiomorphicDescriptor =>
      show stereoValue .rule5EnantiomorphicDescriptor
        (some (retainedReadingEvidence input.moleculeGraph descriptorMap unit graph reference
          node)) = ⊥
      simp [stereoValue, retainedReadingEvidence, liftObservation]

private theorem retainedRule4b_ordinary_le_iff_triple
    (graph : RootedDigraph input.Atom) (observe : ConstitutionalRule → graph.Node → ℤ)
    (evidence : StereochemicalEvidence graph) (mask : Rule4abOnly graph evidence)
    (W D : Nat) (left right : graph.Node) :
    ordinaryKeyWithObservations graph observe evidence W D left ≤
        ordinaryKeyWithObservations graph observe evidence W D right ↔
      observedTripleKey graph observe evidence W D left ≤
        observedTripleKey graph observe evidence W D right := by
  simpa only [not_lt] using
    not_congr (observedOrdinaryKey_lt_iff_tripleKey graph observe evidence mask W D right left)

private theorem retainedRule4b_triple_le_of_compare_ne_lt
    (graph : RootedDigraph input.Atom)
    (observe : ConstitutionalRule → graph.Node → ℤ)
    (evidence : StereochemicalEvidence graph)
    {treeI treeJ : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyI keyJ : input.LocalizedRerootCumulativeRule45Key}
    {readI readJ : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {ρI ρJ : RS}
    (matchI : LocalizedCumulativeTreeTableMatch (.rule4b ρI) treeI keyI)
    (matchJ : LocalizedCumulativeTreeTableMatch (.rule4b ρJ) treeJ keyJ)
    (realizesI : LocalizedCumulativeTreeRealizes input readI treeI)
    (realizesJ : LocalizedCumulativeTreeRealizes input readJ treeJ)
    {W D : Nat} {childI childJ : graph.Node}
    (repI : Represents W D (ruleKeyWithObservations graph W D observe childI) keyI.constitutional)
    (repJ : Represents W D (ruleKeyWithObservations graph W D observe childJ) keyJ.constitutional)
    (rep4aI : Represents4a W D
      (observedRule4aComponent graph observe evidence W D childI) keyI)
    (rep4aJ : Represents4a W D
      (observedRule4aComponent graph observe evidence W D childJ) keyJ)
    (rep4bI : Represents4b W D
      (observedRule4bComponent graph observe evidence W D childI) keyI)
    (rep4bJ : Represents4b W D
      (observedRule4bComponent graph observe evidence W D childJ) keyJ)
    (hne : input.compareRuleMajorCumulativeDescriptor 2 keyI keyJ ≠ Ordering.lt) :
    observedTripleKey graph observe evidence W D childJ ≤
      observedTripleKey graph observe evidence W D childI := by
  have wfI := wellFormedRuleMajorKey_of_tableMatch matchI realizesI
  have wfJ := wellFormedRuleMajorKey_of_tableMatch matchJ realizesJ
  have hconst : OfficialRuleMajorKey.compare keyI.constitutional keyJ.constitutional =
      compare (ruleKeyWithObservations graph W D observe childI)
        (ruleKeyWithObservations graph W D observe childJ) :=
    compare_eq_compare_vector wfI wfJ
      (ruleKeyWithObservations_vectorWellShaped graph observe W D childI)
      (ruleKeyWithObservations_vectorWellShaped graph observe W D childJ) repI repJ
  have order : input.compareRuleMajorCumulativeDescriptor 2 keyI keyJ =
      (compare (ruleKeyWithObservations graph W D observe childI)
        (ruleKeyWithObservations graph W D observe childJ)).then
        ((compare (observedRule4aComponent graph observe evidence W D childI)
            (observedRule4aComponent graph observe evidence W D childJ)).then
          (compare (observedRule4bComponent graph observe evidence W D childI)
            (observedRule4bComponent graph observe evidence W D childJ))) := by
    rw [compareRuleMajor_two, hconst]
    rcases hc : compare (ruleKeyWithObservations graph W D observe childI)
        (ruleKeyWithObservations graph W D observe childJ) with _ | _ | _
    · rfl
    · simp only [Ordering.then]
      have tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          keyI.constitutional.rule1a keyJ.constitutional.rule1a = Ordering.eq := by
        have h : OfficialRuleMajorKey.compare keyI.constitutional keyJ.constitutional =
            Ordering.eq := by rw [hconst, hc]
        unfold OfficialRuleMajorKey.compare at h
        exact (compareLex_eq_eq.1 h).1
      have h4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          (scalar4a keyI) (scalar4a keyJ) =
            compare (observedRule4aComponent graph observe evidence W D childI)
              (observedRule4aComponent graph observe evidence W D childJ) :=
        compare_of_pathFirstDifference
          (ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D
            .rule4aStereogenicUnitKind childI)
          (ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D
            .rule4aStereogenicUnitKind childJ)
          rep4aI rep4aJ
          (fun outcome => rule4a_pathFirstDifference_iff_rule4b matchI matchJ
            realizesI realizesJ tied outcome)
      rw [h4a]
      rcases h4 : compare (observedRule4aComponent graph observe evidence W D childI)
          (observedRule4aComponent graph observe evidence W D childJ) with _ | _ | _
      · rfl
      · exact compare_of_pathFirstDifference
          (ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D
            .rule4bLikeUnlikeDescriptorPairs childI)
          (ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D
            .rule4bLikeUnlikeDescriptorPairs childJ)
          rep4bI rep4bJ
          (fun outcome => rule4b_pathFirstDifference_iff matchI matchJ realizesI realizesJ
            tied (h4a.trans h4) outcome)
      · rfl
    · rfl
  rw [order] at hne
  exact lex_le_of_then_ne_lt _ _ _ vectorCompare_eq_iff vectorCompare_gt_iff
    stereoKeyCompare_eq_iff stereoKeyCompare_gt_iff
    stereoKeyCompare_eq_iff stereoKeyCompare_gt_iff hne

/-- A terminal stage-`.rule4b ρ` tree has the independent pair order and exact Rule-4a/Rule-4b
representations at its sole node. -/
theorem retainedContextTree_terminal_bridge4b
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : RetainedRule4bFieldFacts tree descriptorMap unit)
    {ρ : RS} (cursor : input.LocalizedRerootCursor carrierFuel)
    (fullMatch : LocalizedCumulativeTreeFullMatch (.rule4b ρ)
      (localizedRootTree input cursor (read cursor) [])
      (localizedCumulativeRule45TerminalKey input (.rule4b ρ) cursor (read cursor)))
    (realizes : LocalizedCumulativeTreeRealizes input read
      (localizedRootTree input cursor (read cursor) []))
    {W D : Nat} (node : (ruleMajorTreeGraph tree).Node)
    (lookup : tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (read cursor) [])) :
    (((slotList (toOfficialSourceTree tree).declarativeAddressing node
          (localizedRootTree input cursor (read cursor) []).children.length).map
        (observedTripleKey (ruleMajorTreeGraph tree) observe
          (retainedReadingEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)
            (senseOf ρ)) W D)).Pairwise fun x y => y ≤ x) ∧
      Represents4a W D (observedRule4aComponent (ruleMajorTreeGraph tree) observe
        (retainedReadingEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)
          (senseOf ρ)) W D node)
        (localizedCumulativeRule45TerminalKey input (.rule4b ρ) cursor (read cursor)) ∧
      Represents4b W D (observedRule4bComponent (ruleMajorTreeGraph tree) observe
        (retainedReadingEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)
          (senseOf ρ)) W D node)
        (localizedCumulativeRule45TerminalKey input (.rule4b ρ) cursor (read cursor)) := by
  let evidence := retainedReadingEvidence input.moleculeGraph descriptorMap unit
    (ruleMajorTreeGraph tree) (senseOf ρ)
  have childrenEq : (localizedRootTree input cursor (read cursor) []).children = [] := by
    unfold localizedRootTree
    rfl
  have pairedNil : List.Forall₂ (fun childKey childTree =>
      LocalizedCumulativeTreeTableMatch (.rule4b ρ) childTree childKey ∧
        LocalizedCumulativeTreeRealizes input read childTree)
      ([] : List input.LocalizedRerootCumulativeRule45Key)
      (localizedRootTree input cursor (read cursor) []).children := by
    rw [childrenEq]
    exact List.Forall₂.nil
  refine ⟨by rw [childrenEq]; simp [slotList], ?_, ?_⟩
  · intro path
    cases path with
    | nil =>
        exact retainedRule4b_nil4a descriptorMap unit (ruleMajorTreeGraph tree) observe W D node
          fullMatch.tableMatch realizes
          (hyp.label node _ (by rwa [← decoratedSubtreeAt?_eq_subtreeAt?]))
          (hyp.tetrahedral node) (hyp.realAvailableOrRing node)
    | cons digit path =>
        have encodedBot : encoded4a
            (localizedCumulativeRule45TerminalKey input (.rule4b ρ) cursor (read cursor))
            (digit :: path) = ⊥ := by
          rw [encoded4a_cons_of_key_rule4b fullMatch.tableMatch realizes pairedNil digit path]
          rfl
        have constBot : nodePathObservationWithObservations
            (ruleMajorTreeGraph tree) observe W D 0 node (digit :: path) = ⊥ := by
          have represented := (observedTree_terminal_bridge tree observe observations cursor
            fullMatch realizes (W := W) (D := D) node lookup).2
          have atPath := represented 0 (by omega) (digit :: path)
          unfold nodePathObservationWithObservations
          rw [atPath, encodedObservation_cons_of_key fullMatch.tableMatch realizes pairedNil
            (ruleOfIndex 0) digit path]
          rfl
        rw [encodedBot]
        exact (observedStereoNodePathObservation_eq_bot_iff (ruleMajorTreeGraph tree) observe
          evidence .rule4aStereogenicUnitKind W D (digit :: path) node).2 constBot
  · intro path
    cases path with
    | nil =>
        exact retainedRule4b_nil4b descriptorMap unit (ruleMajorTreeGraph tree) observe W D node
          fullMatch.tableMatch realizes
          (hyp.label node _ (by rwa [← decoratedSubtreeAt?_eq_subtreeAt?]))
          (hyp.tetrahedral node)
    | cons digit path =>
        have encodedBot : encoded4b
            (localizedCumulativeRule45TerminalKey input (.rule4b ρ) cursor (read cursor))
            (digit :: path) = ⊥ := by
          rw [encoded4b_cons_of_key fullMatch.tableMatch realizes pairedNil digit path]
          rfl
        have constBot : nodePathObservationWithObservations
            (ruleMajorTreeGraph tree) observe W D 0 node (digit :: path) = ⊥ := by
          have represented := (observedTree_terminal_bridge tree observe observations cursor
            fullMatch realizes (W := W) (D := D) node lookup).2
          have atPath := represented 0 (by omega) (digit :: path)
          unfold nodePathObservationWithObservations
          rw [atPath, encodedObservation_cons_of_key fullMatch.tableMatch realizes pairedNil
            (ruleOfIndex 0) digit path]
          rfl
        rw [encodedBot]
        exact (observedStereoNodePathObservation_eq_bot_iff (ruleMajorTreeGraph tree) observe
          evidence .rule4bLikeUnlikeDescriptorPairs W D (digit :: path) node).2 constBot

/-- Recursive stage-`.rule4b ρ` bridge for an arbitrary realized contextual tree. The actual
rule-major trace simultaneously determines descending observed triple order and represents both
active stereochemical columns at every resolved subtree. -/
theorem retainedContextTree_node_bridge4b
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : RetainedRule4bFieldFacts tree descriptorMap unit)
    {ρ : RS}
    (mask : Rule4abOnly (ruleMajorTreeGraph tree)
      (retainedReadingEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) (senseOf ρ)))
    {W D : Nat} (hW : (ruleMajorTreeGraph tree).width ≤ W)
    (hD : (ruleMajorTreeGraph tree).height ≤ D)
    {fuel : Nat} (node : (ruleMajorTreeGraph tree).Node)
    (dsub : LocalizedCumulativeDecoratedTree input carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (trace : LocalizedRuleMajorSortTrace input (.rule4b ρ) read fuel dsub key)
    (lookup : tree.decoratedSubtreeAt? node.1 = some dsub) :
    (((slotList (toOfficialSourceTree tree).declarativeAddressing node dsub.children.length).map
        (observedTripleKey (ruleMajorTreeGraph tree) observe
          (retainedReadingEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)
            (senseOf ρ)) W D)).Pairwise fun x y => y ≤ x) ∧
      Represents4a W D (observedRule4aComponent (ruleMajorTreeGraph tree) observe
        (retainedReadingEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)
          (senseOf ρ)) W D node) key ∧
      Represents4b W D (observedRule4bComponent (ruleMajorTreeGraph tree) observe
        (retainedReadingEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)
          (senseOf ρ)) W D node) key := by
  induction fuel generalizing dsub key node lookup with
  | zero =>
      cases trace with
      | terminal _fuel cursor _children _childrenComputed _terminalChildren fullMatch realizes =>
          exact retainedContextTree_terminal_bridge4b tree observe observations hyp cursor fullMatch realizes
            node lookup
  | succ fuel ih =>
      have fullMatch := LocalizedRuleMajorSortTrace.fullMatch_of_trace trace
      have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
      rcases LocalizedRuleMajorSortTrace.structure_of_trace trace with
        ⟨cursor, _children, dsubEq, keyEq, _childrenEq, _childrenComputed, _terminalChildren⟩ |
        ⟨cursor, _children, _childKeys, sortedKeys, sortedTrees, dsubEq, keyEq, childrenEq,
          _childrenComputed, _nonempty, _childKeysComputed, sortedEq, _constitutionalDescending,
          sortedDescending, childrenTraced⟩
      · subst dsub
        subst key
        exact retainedContextTree_terminal_bridge4b tree observe observations hyp cursor fullMatch realizes
          node lookup
      · subst dsub
        subst key
        let evidence := retainedReadingEvidence input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph tree) (senseOf ρ)
        have hdense : DenseAt (toOfficialSourceTree tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length :=
          observedTree_denseAt_of_lookup tree node
            (localizedRootTree input cursor (read cursor) sortedTrees) lookup
        have paired := LocalizedRuleMajorSortTraceList.to_forall₂ childrenTraced
        have lengthEq : sortedKeys.length = sortedTrees.length := List.Forall₂.length_eq paired
        have pairedMatch : List.Forall₂ (fun childKey childTree =>
            LocalizedCumulativeTreeTableMatch (.rule4b ρ) childTree childKey ∧
              LocalizedCumulativeTreeRealizes input read childTree) sortedKeys sortedTrees :=
          List.Forall₂.imp (fun childKey childTree related =>
            ⟨(LocalizedRuleMajorSortTrace.fullMatch_of_trace related).tableMatch,
              LocalizedRuleMajorSortTrace.realizes_of_trace related⟩) paired
        have descending : input.RuleMajorCumulativeKeysDescending
            (CertifiedLocalizedCIPInput.ruleMajorStageWidth (.rule4b ρ)) sortedKeys :=
          sortedDescending
        have countEq : (localizedRootTree input cursor (read cursor) sortedTrees).children.length =
            sortedTrees.length := by rw [childrenEq]
        have slotLength : (slotList (toOfficialSourceTree tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length =
            sortedTrees.length := by simp [slotList, countEq]
        have childAt : ∀ i (hi : i < sortedTrees.length),
            ∃ child : (ruleMajorTreeGraph tree).Node,
              (slotList (toOfficialSourceTree tree).declarativeAddressing node
                (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[i]? =
                  some child ∧
                child.1 = node.1 ++ [i] ∧
                  tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) := by
          intro i hi
          obtain ⟨child, slotSome, addr⟩ := slotList_getD_of_lt
            (addressing := (toOfficialSourceTree tree).declarativeAddressing) (parent := node)
            (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
            hdense (by rw [countEq]; exact hi)
          have addrFlat : child.1 = node.1 ++ [i] := by
            rw [(toOfficialSourceTree tree).declarativeAddressing_address,
              (toOfficialSourceTree tree).declarativeAddressing_address] at addr
            exact addr
          refine ⟨child, slotSome, addrFlat, ?_⟩
          rw [addrFlat, decoratedSubtreeAt?_append tree node.1 [i], lookup]
          simp [childrenEq, decoratedSubtreeAt?, List.getElem?_eq_getElem hi]
        have traceAt : ∀ i (hi : i < sortedTrees.length),
            LocalizedRuleMajorSortTrace input (.rule4b ρ) read fuel (sortedTrees[i]'hi)
              (sortedKeys[i]'(by omega)) :=
          fun i hi => List.Forall₂.get (i := i) paired (by omega) hi
        have ihAt : ∀ i (hi : i < sortedTrees.length)
            (child : (ruleMajorTreeGraph tree).Node),
            tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
              Represents4a W D (observedRule4aComponent (ruleMajorTreeGraph tree) observe
                  evidence W D child) (sortedKeys[i]'(by omega)) ∧
                Represents4b W D (observedRule4bComponent (ruleMajorTreeGraph tree) observe
                  evidence W D child) (sortedKeys[i]'(by omega)) :=
          fun i hi child hl =>
            (ih child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega)) (traceAt i hi) hl).2
        have constAt : ∀ i (hi : i < sortedTrees.length)
            (child : (ruleMajorTreeGraph tree).Node),
            tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
              Represents W D (ruleKeyWithObservations (ruleMajorTreeGraph tree) W D observe child)
                (sortedKeys[i]'(by omega)).constitutional := by
          intro i hi child hl
          exact (observedTree_node_bridge tree observe observations hW hD child
            (sortedTrees[i]'hi) (sortedKeys[i]'(by omega)) (traceAt i hi) hl).2
        have slotSorted : ((slotList (toOfficialSourceTree tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).map
              (observedTripleKey (ruleMajorTreeGraph tree) observe evidence W D)).Pairwise
                fun x y => y ≤ x := by
          rw [List.pairwise_iff_getElem]
          intro i j hi hj hij
          rw [List.length_map, slotLength] at hi hj
          obtain ⟨childI, slotI, _, lookupI⟩ := childAt i hi
          obtain ⟨childJ, slotJ, _, lookupJ⟩ := childAt j hj
          have hneWidth : input.compareRuleMajorCumulativeDescriptor
              (CertifiedLocalizedCIPInput.ruleMajorStageWidth (.rule4b ρ))
              (sortedKeys[i]'(by omega)) (sortedKeys[j]'(by omega)) ≠ Ordering.lt :=
            (List.pairwise_iff_getElem.1 descending) i j (by omega) (by omega) hij
          have widthEq : CertifiedLocalizedCIPInput.ruleMajorStageWidth (.rule4b ρ) = 2 := rfl
          have hne : input.compareRuleMajorCumulativeDescriptor 2
              (sortedKeys[i]'(by omega)) (sortedKeys[j]'(by omega)) ≠ Ordering.lt := by
            rw [← widthEq]
            exact hneWidth
          have hle := retainedRule4b_triple_le_of_compare_ne_lt
            (ruleMajorTreeGraph tree) observe evidence
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt i hi)).tableMatch
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt j hj)).tableMatch
            (LocalizedRuleMajorSortTrace.realizes_of_trace (traceAt i hi))
            (LocalizedRuleMajorSortTrace.realizes_of_trace (traceAt j hj))
            (constAt i hi childI lookupI) (constAt j hj childJ lookupJ)
            (ihAt i hi childI lookupI).1 (ihAt j hj childJ lookupJ).1
            (ihAt i hi childI lookupI).2 (ihAt j hj childJ lookupJ).2 hne
          have getI : (slotList (toOfficialSourceTree tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[i]'(by
                rw [slotLength]
                exact hi) = childI :=
            Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotI)
          have getJ : (slotList (toOfficialSourceTree tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[j]'(by
                rw [slotLength]
                exact hj) = childJ :=
            Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotJ)
          simpa [List.getElem_map, getI, getJ] using hle
        have slotSortedOrd : ((slotList (toOfficialSourceTree tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).map
              (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe evidence W D)).Pairwise
                fun x y => y ≤ x := by
          rw [List.pairwise_map] at slotSorted ⊢
          exact slotSorted.imp fun h =>
            (retainedRule4b_ordinary_le_iff_triple (ruleMajorTreeGraph tree) observe evidence mask W D
              _ _).2 h
        have hperm := slotList_perm
          (addressing := (toOfficialSourceTree tree).declarativeAddressing) (parent := node)
          (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length) hdense
        have consCase : ∀ (rule : StereochemicalRule)
            (enc : input.LocalizedRerootCumulativeRule45Key → List Nat → WithBot StereoLabel)
            (comp : (ruleMajorTreeGraph tree).Node →
              Certificate.CanonicalSphereKey.Key StereoLabel),
            (∀ i (hi : i < sortedTrees.length) (child : (ruleMajorTreeGraph tree).Node),
              tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
                ∀ path, Certificate.CanonicalSphereKey.pathObservationOf W D (comp child) path =
                  enc (sortedKeys[i]'(by omega)) path) →
            (∀ child : (ruleMajorTreeGraph tree).Node, comp child =
              List.getD ((ofLex (ordinaryKeyWithObservations (ruleMajorTreeGraph tree)
                observe evidence W D child)).2) (stereoIndex rule) []) →
            (∀ digit path, enc
              (localizedCumulativeRule45StepKey input (.rule4b ρ) cursor (read cursor) sortedKeys)
              (digit :: path) =
                ((sortedKeys[digit]?).map fun childKey => enc childKey path).getD ⊥) →
            ∀ digit path,
              Certificate.CanonicalSphereKey.pathObservationOf W D (comp node) (digit :: path) =
                enc (localizedCumulativeRule45StepKey input (.rule4b ρ) cursor (read cursor) sortedKeys)
                  (digit :: path) := by
          intro rule enc comp repAt compEq encCons digit path
          rw [compEq node]
          change observedStereoNodePathObservation (ruleMajorTreeGraph tree) observe evidence W D
            rule node (digit :: path) = _
          rw [observedStereoNodePathObservation_cons (ruleMajorTreeGraph tree) observe evidence
            W D rule node hperm slotSortedOrd digit path, encCons digit path]
          by_cases hdigit : digit < sortedTrees.length
          · obtain ⟨child, slotSome, childAddr, childLookup⟩ := childAt digit hdigit
            have digitLtKeys : digit < sortedKeys.length := by omega
            have repChild := repAt digit hdigit child childLookup path
            rw [compEq child] at repChild
            rw [slotSome, List.getElem?_eq_getElem digitLtKeys]
            simp only [Option.map_some, Option.getD_some]
            by_cases hgate : digit < W ∧ path.length < D
            · rw [if_pos hgate]
              exact repChild
            · rw [if_neg hgate, ← repChild]
              symm
              apply (observedStereoNodePathObservation_eq_bot_iff
                (ruleMajorTreeGraph tree) observe evidence rule W D path child).2
              by_contra hne
              have bound := depth_add_length_le_of_nodePathObservationWithObservations
                (ruleMajorTreeGraph tree) observe (W := W) (D := D)
                (by omega : (0 : Nat) < 3) path child hne
              have childDepth : (ruleMajorTreeGraph tree).depth child =
                  (ruleMajorTreeGraph tree).depth node + 1 :=
                (ruleMajorTreeGraph tree).child_depth ⟨digit, childAddr⟩
              have hdigitLtW : digit < W := by
                have countLe : sortedTrees.length ≤ (ruleMajorTreeGraph tree).width := by
                  have countLe := count_le_width
                    (addressing := (toOfficialSourceTree tree).declarativeAddressing)
                    (parent := node)
                    (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
                    hdense
                  rw [countEq] at countLe
                  exact countLe
                omega
              have hpath : ¬ path.length < D := fun h => hgate ⟨hdigitLtW, h⟩
              omega
          · have slotNone : (slotList (toOfficialSourceTree tree).declarativeAddressing node
                (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[digit]? =
                  none := by
              rw [List.getElem?_eq_none_iff, slotLength]
              omega
            have keysNone : sortedKeys[digit]? = none := by
              rw [List.getElem?_eq_none_iff]
              omega
            rw [slotNone, keysNone]
            split <;> rfl
        refine ⟨slotSorted, ?_, ?_⟩
        · intro path
          cases path with
          | nil =>
              exact retainedRule4b_nil4a descriptorMap unit (ruleMajorTreeGraph tree) observe W D node
                fullMatch.tableMatch realizes
                (hyp.label node _ (by rwa [← decoratedSubtreeAt?_eq_subtreeAt?]))
                (hyp.tetrahedral node) (hyp.realAvailableOrRing node)
          | cons digit path =>
              exact consCase .rule4aStereogenicUnitKind encoded4a
                (observedRule4aComponent (ruleMajorTreeGraph tree) observe evidence W D)
                (fun i hi child hl => (ihAt i hi child hl).1) (fun _ => rfl)
                (fun digit path => encoded4a_cons_of_key_rule4b fullMatch.tableMatch realizes
                  pairedMatch digit path) digit path
        · intro path
          cases path with
          | nil =>
              exact retainedRule4b_nil4b descriptorMap unit (ruleMajorTreeGraph tree) observe W D node
                fullMatch.tableMatch realizes
                (hyp.label node _ (by rwa [← decoratedSubtreeAt?_eq_subtreeAt?]))
                (hyp.tetrahedral node)
          | cons digit path =>
              exact consCase .rule4bLikeUnlikeDescriptorPairs encoded4b
                (observedRule4bComponent (ruleMajorTreeGraph tree) observe evidence W D)
                (fun i hi child hl => (ihAt i hi child hl).2) (fun _ => rfl)
                (fun digit path => encoded4b_cons_of_key fullMatch.tableMatch realizes
                  pairedMatch digit path) digit path

/-- The recursive Rule-4b bridge makes the actual decorated-tree addressing canonical for the
full observed ordinary key under the matching Rule-4a/Rule-4b evidence mask. -/
theorem retainedContextTree_keySorted4b
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : RetainedRule4bFieldFacts tree descriptorMap unit)
    {ρ : RS}
    (mask : Rule4abOnly (ruleMajorTreeGraph tree)
      (retainedReadingEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) (senseOf ρ)))
    {fuel : Nat} {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input (.rule4b ρ) read fuel tree key) :
    KeySorted
      (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
        (retainedReadingEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)
          (senseOf ρ))
        (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height)
      (toOfficialSourceTree tree).declarativeAddressing := by
  intro parent first second firstSlot secondSlot addrFirst addrSecond hlt
  obtain ⟨dsub, lookup, _⟩ := observedTree_decoratedSubtree_of_node tree parent
  have hdense : DenseAt (toOfficialSourceTree tree).declarativeAddressing parent
      dsub.children.length := observedTree_denseAt_of_lookup tree parent dsub lookup
  rcases ruleMajorTrace_of_subtree input (.rule4b _) read trace parent.1 dsub lookup with
    ⟨fuel', key', trace'⟩
  have bridge := retainedContextTree_node_bridge4b tree observe observations hyp mask
    (W := (ruleMajorTreeGraph tree).width) (D := (ruleMajorTreeGraph tree).height)
    le_rfl le_rfl parent dsub key' trace' lookup
  have slotSorted := bridge.1
  have firstLt : firstSlot < dsub.children.length := (hdense firstSlot).1 ⟨first, addrFirst⟩
  have secondLt : secondSlot < dsub.children.length := (hdense secondSlot).1 ⟨second, addrSecond⟩
  obtain ⟨childI, slotI, addrI⟩ := slotList_getD_of_lt
    (addressing := (toOfficialSourceTree tree).declarativeAddressing) (parent := parent)
    (count := dsub.children.length) hdense firstLt
  obtain ⟨childJ, slotJ, addrJ⟩ := slotList_getD_of_lt
    (addressing := (toOfficialSourceTree tree).declarativeAddressing) (parent := parent)
    (count := dsub.children.length) hdense secondLt
  have firstEq : first = childI :=
    Subtype.ext (by
      rw [(toOfficialSourceTree tree).declarativeAddressing_address,
        (toOfficialSourceTree tree).declarativeAddressing_address] at addrFirst addrI
      exact addrFirst.trans addrI.symm)
  have secondEq : second = childJ :=
    Subtype.ext (by
      rw [(toOfficialSourceTree tree).declarativeAddressing_address,
        (toOfficialSourceTree tree).declarativeAddressing_address] at addrSecond addrJ
      exact addrSecond.trans addrJ.symm)
  have slotLength : (slotList (toOfficialSourceTree tree).declarativeAddressing parent
      dsub.children.length).length = dsub.children.length := by simp [slotList]
  have getI : (slotList (toOfficialSourceTree tree).declarativeAddressing parent
      dsub.children.length)[firstSlot]'(by rw [slotLength]; exact firstLt) = childI :=
    Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotI)
  have getJ : (slotList (toOfficialSourceTree tree).declarativeAddressing parent
      dsub.children.length)[secondSlot]'(by rw [slotLength]; exact secondLt) = childJ :=
    Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotJ)
  have hpair := (List.pairwise_iff_getElem.1 slotSorted) firstSlot secondSlot
    (by rw [List.length_map, slotLength]; exact firstLt)
    (by rw [List.length_map, slotLength]; exact secondLt) hlt
  simp only [List.getElem_map, getI, getJ] at hpair
  rw [firstEq, secondEq]
  exact (retainedRule4b_ordinary_le_iff_triple (ruleMajorTreeGraph tree) observe _ mask _ _ _ _).2 hpair


/-- The generated dependency reader supplies retained Rule-4b canonicality for every actual
executable child of an arbitrary detected target. Ring duplicates are included. Acyclicity is
not assumed. -/
theorem retainedGeneratedContextTree_rankCanonical4b
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedRuleMajorReference.carrierFuel input))
    {ρ : RS} {fuel : Nat} {key : input.certified.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input.certified (.rule4b ρ)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) fuel tree key)
    (rootChild : tree.source ∈ input.certified.executableLocalizedRerootChildren target) :
    Dense (toOfficialSourceTree tree).declarativeAddressing ∧
      KeySorted
        (ordinaryKeyWithObservations (ruleMajorTreeGraph tree)
          (retainedContextNodeObservation input.certified.moleculeGraph
            (ruleMajorTreeGraph tree) unit)
          (retainedReadingEvidence input.certified.moleculeGraph
            (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph tree)
            (senseOf ρ))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height)
        (toOfficialSourceTree tree).declarativeAddressing ∧
      Represents4a (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
        (observedRule4aComponent (ruleMajorTreeGraph tree)
          (retainedContextNodeObservation input.certified.moleculeGraph
            (ruleMajorTreeGraph tree) unit)
          (retainedReadingEvidence input.certified.moleculeGraph
            (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph tree)
            (senseOf ρ))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
          (ruleMajorTreeGraph tree).root) key ∧
      Represents4b (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
        (observedRule4bComponent (ruleMajorTreeGraph tree)
          (retainedContextNodeObservation input.certified.moleculeGraph
            (ruleMajorTreeGraph tree) unit)
          (retainedReadingEvidence input.certified.moleculeGraph
            (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph tree)
            (senseOf ρ))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
          (ruleMajorTreeGraph tree).root) key := by
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
  have readerEq := LocalizedRuleMajorReference.molecularReader_eq_generatedReader_of_simpleBonded
    input singleBonded target.occurrence
  have realizesMol : LocalizedCumulativeTreeRealizes input.certified
      (input.certified.molecularReader (LocalizedRuleMajorReference.descriptorMap input)
        target.occurrence) tree := by
    rw [readerEq]
    exact realizes
  have observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      retainedContextNodeObservation input.certified.moleculeGraph (ruleMajorTreeGraph tree)
        unit rule node = priorityValue rule (armObservation rule actual) := by
    intro rule node actual lookup
    have lookupSub : subtreeAt? tree node.1 = some actual := by
      rw [← decoratedSubtreeAt?_eq_subtreeAt?]
      exact lookup
    exact input.certified.retainedContextNodeObservation_eq_armObservation singleBonded target
      unit targetUnit tree realizesMol rootChild rule node actual lookupSub
  have rank := retainedGeneratedContextTreeRankReadback input singleBonded target unit targetUnit
    tree realizes rootChild
  have field : RetainedRule4bFieldFacts tree (LocalizedRuleMajorReference.descriptorMap input)
      unit :=
    { label := rank.label
      tetrahedral := rank.tetrahedral
      realAvailableOrRing := rank.nodeStatus }
  have mask := retainedRule4b_rule4abOnly_of_simpleBonded singleBonded
    (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph tree) (senseOf ρ)
  have keySorted := retainedContextTree_keySorted4b tree _ observations field mask trace
  have rootRepresentations := retainedContextTree_node_bridge4b tree _ observations field mask
    (W := (ruleMajorTreeGraph tree).width) (D := (ruleMajorTreeGraph tree).height)
    le_rfl le_rfl (ruleMajorTreeGraph tree).root tree key trace (by
      change tree.decoratedSubtreeAt? [] = some tree
      rw [decoratedSubtreeAt?])
  exact ⟨(toOfficialSourceTree tree).declarativeAddressing_dense, keySorted,
    rootRepresentations.2.1, rootRepresentations.2.2⟩

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.RetainedRule4bFieldFacts
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.retainedRule4b_nil4a
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.retainedRule4b_nil4b
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.retainedRule4b_rule4abOnly_of_simpleBonded
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.retainedContextTree_terminal_bridge4b
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.retainedContextTree_node_bridge4b
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.retainedContextTree_keySorted4b
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.retainedGeneratedContextTree_rankCanonical4b
