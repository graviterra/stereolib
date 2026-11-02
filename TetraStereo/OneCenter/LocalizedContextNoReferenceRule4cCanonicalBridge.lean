import TetraStereo.OneCenter.LocalizedContextRule4aCanonicalBridge
import TetraStereo.OneCenter.LocalizedContextStereoReadback
import TetraStereo.OneCenter.LocalizedRuleMajorCanonicalBridge
import TetraStereo.OneCenter.LocalizedRuleMajorNoReferenceRule4cCanonicalBridge
import TetraStereo.OneCenter.LocalizedRuleMajorNoReferenceRule4cTableBridge
import TetraStereo.OneCenter.DeclarativeCIPObservedReadingKeyProjection
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Contextual no-reference Rule-4c canonicality for the rule-major cumulative builder. The
actual no-reference sort retains the molecular pseudoasymmetric column, including `r` and `s`.
-/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree CertifiedLocalizedCIPInput
open OfficialSparseCanonicalVectorComparison DeclarativeCIP Rule4cObservationBridge
noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}

private theorem context_ordinary_le_iff_rule4ac
    (graph : RootedDigraph input.Atom) (observe : ConstitutionalRule → graph.Node → ℤ)
    (evidence : StereochemicalEvidence graph) (mask : Rule4acOnly graph evidence)
    (W D : Nat) (left right : graph.Node) :
    ordinaryKeyWithObservations graph observe evidence W D left ≤
        ordinaryKeyWithObservations graph observe evidence W D right ↔
      observedRule4acKey graph observe evidence W D left ≤
        observedRule4acKey graph observe evidence W D right := by
  exact observedOrdinaryKey_le_iff_rule4acKey graph observe evidence mask W D left right

private theorem observedRule4acKey_le_of_ruleMajor_compare_ne_lt
    (graph : RootedDigraph input.Atom)
    (observe : ConstitutionalRule → graph.Node → ℤ)
    (evidence : StereochemicalEvidence graph)
    {treeI treeJ : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyI keyJ : input.LocalizedRerootCumulativeRule45Key}
    {readI readJ : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (matchI : LocalizedCumulativeTreeTableMatch .rule4cNoReference treeI keyI)
    (matchJ : LocalizedCumulativeTreeTableMatch .rule4cNoReference treeJ keyJ)
    (labelsI : LocalizedCumulativeTreeLabelMatch treeI keyI)
    (labelsJ : LocalizedCumulativeTreeLabelMatch treeJ keyJ)
    (realizesI : LocalizedCumulativeTreeRealizes input readI treeI)
    (realizesJ : LocalizedCumulativeTreeRealizes input readJ treeJ)
    {W D : Nat} {childI childJ : graph.Node}
    (repI : Represents W D (ruleKeyWithObservations graph W D observe childI) keyI.constitutional)
    (repJ : Represents W D (ruleKeyWithObservations graph W D observe childJ) keyJ.constitutional)
    (rep4aI : Represents4a W D
      (observedRule4aComponent graph observe evidence W D childI) keyI)
    (rep4aJ : Represents4a W D
      (observedRule4aComponent graph observe evidence W D childJ) keyJ)
    (rep4cI : Represents4c W D
      (observedRule4cComponent graph observe evidence W D childI) keyI)
    (rep4cJ : Represents4c W D
      (observedRule4cComponent graph observe evidence W D childJ) keyJ)
    (hne : input.compareRuleMajorCumulativeDescriptor 2 keyI keyJ ≠ Ordering.lt) :
    observedRule4acKey graph observe evidence W D childJ ≤
      observedRule4acKey graph observe evidence W D childI := by
  have wfI := wellFormedRuleMajorKey_of_tableMatch matchI realizesI
  have wfJ := wellFormedRuleMajorKey_of_tableMatch matchJ realizesJ
  have hconst : OfficialRuleMajorKey.compare keyI.constitutional keyJ.constitutional =
      compare (ruleKeyWithObservations graph W D observe childI)
        (ruleKeyWithObservations graph W D observe childJ) :=
    compare_eq_compare_vector wfI wfJ
      (ruleKeyWithObservations_vectorWellShaped graph observe W D childI)
      (ruleKeyWithObservations_vectorWellShaped graph observe W D childJ) repI repJ
  have h4aShapeI := ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D
    .rule4aStereogenicUnitKind childI
  have h4aShapeJ := ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D
    .rule4aStereogenicUnitKind childJ
  have h4cShapeI := ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D
    .rule4cPseudoasymmetricDescriptor childI
  have h4cShapeJ := ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D
    .rule4cPseudoasymmetricDescriptor childJ
  have order : input.compareRuleMajorCumulativeDescriptor 2 keyI keyJ =
      (compare (ruleKeyWithObservations graph W D observe childI)
        (ruleKeyWithObservations graph W D observe childJ)).then
        ((compare (observedRule4aComponent graph observe evidence W D childI)
            (observedRule4aComponent graph observe evidence W D childJ)).then
          (compare (observedRule4cComponent graph observe evidence W D childI)
            (observedRule4cComponent graph observe evidence W D childJ))) := by
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
        compare_of_pathFirstDifference h4aShapeI h4aShapeJ rep4aI rep4aJ
          (fun outcome => rule4a_pathFirstDifference_iff_anyStage matchI matchJ
            realizesI realizesJ tied outcome)
      rw [h4a]
      rcases h4a' : compare (observedRule4aComponent graph observe evidence W D childI)
          (observedRule4aComponent graph observe evidence W D childJ) with _ | _ | _
      · rfl
      · have tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
            (scalar4a keyI) (scalar4a keyJ) = Ordering.eq := by rw [h4a, h4a']
        have h4c : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
            (scalar4b keyI) (scalar4b keyJ) =
              compare (observedRule4cComponent graph observe evidence W D childI)
                (observedRule4cComponent graph observe evidence W D childJ) :=
          compare_of_pathFirstDifference h4cShapeI h4cShapeJ rep4cI rep4cJ
            (fun outcome => noReference4c_pathFirstDifference_iff matchI matchJ labelsI labelsJ
              realizesI realizesJ tied tied4a outcome)
        rw [h4c]
      · rfl
    · rfl
  rw [order] at hne
  exact lex_le_of_then_ne_lt _ _ _ vectorCompare_eq_iff vectorCompare_gt_iff
    stereoKeyCompare_eq_iff stereoKeyCompare_gt_iff
    stereoKeyCompare_eq_iff stereoKeyCompare_gt_iff hne

private theorem context_nil4a_noReference
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (graph : RootedDigraph input.Atom)
    (observe : ConstitutionalRule → graph.Node → ℤ) (W D : Nat) (node : graph.Node)
    {actual : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (tableMatch : LocalizedCumulativeTreeTableMatch .rule4cNoReference actual key)
    (realizes : LocalizedCumulativeTreeRealizes input read actual)
    (label : actual.label =
      (occurrenceReading input.moleculeGraph descriptorMap unit graph node).toLocalizedLabel)
    (tetra : (occurrenceReading input.moleculeGraph descriptorMap unit graph node).IsTetrahedral)
    (available : occurrenceReading input.moleculeGraph descriptorMap unit graph node ≠ .unavailable) :
    observedStereoNodePathObservation graph observe
      (noReferenceEvidence4c input.moleculeGraph descriptorMap unit graph) W D
      .rule4aStereogenicUnitKind node [] = encoded4a key [] := by
  rw [observedStereoNodePathObservation_nil]
  have h := stereoNodePathObservation_nil_eq_encoded4a_noReference descriptorMap unit graph W D
    node tableMatch realizes label tetra available
  rw [stereoNodePathObservation_nil] at h
  exact h

private theorem context_nil4c_noReference
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (graph : RootedDigraph input.Atom)
    (observe : ConstitutionalRule → graph.Node → ℤ) (W D : Nat) (node : graph.Node)
    {actual : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (tableMatch : LocalizedCumulativeTreeTableMatch .rule4cNoReference actual key)
    (labels : LocalizedCumulativeTreeLabelMatch actual key)
    (realizes : LocalizedCumulativeTreeRealizes input read actual)
    (label : actual.label =
      (occurrenceReading input.moleculeGraph descriptorMap unit graph node).toLocalizedLabel)
    (available : occurrenceReading input.moleculeGraph descriptorMap unit graph node ≠ .unavailable) :
    observedStereoNodePathObservation graph observe
      (noReferenceEvidence4c input.moleculeGraph descriptorMap unit graph) W D
      .rule4cPseudoasymmetricDescriptor node [] = encodedPseudo4c key [] := by
  have pseudoEq := stereoNodePathObservation_nil_eq_pseudoValueOfLabel_noReference descriptorMap
      unit graph W D node actual label available
  rw [stereoNodePathObservation_nil] at pseudoEq
  rw [observedStereoNodePathObservation_nil, pseudoEq,
    encodedPseudo4c_nil tableMatch labels realizes]


/-- A terminal no-reference tree has the independent pair order and exact 4a/4c representations
at its sole node. -/
theorem contextTree_terminal_bridge_noReference4c
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : ContextTreeRankReadback tree descriptorMap unit)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (fullMatch : LocalizedCumulativeTreeFullMatch .rule4cNoReference
      (localizedRootTree input cursor (read cursor) [])
      (localizedCumulativeRule45TerminalKey input .rule4cNoReference cursor (read cursor)))
    (realizes : LocalizedCumulativeTreeRealizes input read
      (localizedRootTree input cursor (read cursor) []))
    {W D : Nat} (node : (ruleMajorTreeGraph tree).Node)
    (lookup : tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (read cursor) [])) :
    (((slotList (toOfficialSourceTree tree).declarativeAddressing node
          (localizedRootTree input cursor (read cursor) []).children.length).map
        (observedRule4acKey (ruleMajorTreeGraph tree) observe
          (noReferenceEvidence4c input.moleculeGraph descriptorMap unit
            (ruleMajorTreeGraph tree)) W D)).Pairwise fun x y => y ≤ x) ∧
      Represents4a W D (observedRule4aComponent (ruleMajorTreeGraph tree) observe
        (noReferenceEvidence4c input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph tree)) W D node)
        (localizedCumulativeRule45TerminalKey input .rule4cNoReference cursor (read cursor)) ∧
      Represents4c W D (observedRule4cComponent (ruleMajorTreeGraph tree) observe
        (noReferenceEvidence4c input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph tree)) W D node)
        (localizedCumulativeRule45TerminalKey input .rule4cNoReference cursor (read cursor)) := by
  let evidence := noReferenceEvidence4c input.moleculeGraph descriptorMap unit
    (ruleMajorTreeGraph tree)
  have childrenEq : (localizedRootTree input cursor (read cursor) []).children = [] := by
    unfold localizedRootTree
    rfl
  have pairedNil : List.Forall₂ (fun childKey childTree =>
      LocalizedCumulativeTreeTableMatch .rule4cNoReference childTree childKey ∧
        LocalizedCumulativeTreeRealizes input read childTree ∧
          LocalizedCumulativeTreeLabelMatch childTree childKey)
      ([] : List input.LocalizedRerootCumulativeRule45Key)
      (localizedRootTree input cursor (read cursor) []).children := by
    rw [childrenEq]
    exact List.Forall₂.nil
  have pairedNilBasic : List.Forall₂ (fun childKey childTree =>
      LocalizedCumulativeTreeTableMatch .rule4cNoReference childTree childKey ∧
        LocalizedCumulativeTreeRealizes input read childTree)
      ([] : List input.LocalizedRerootCumulativeRule45Key)
      (localizedRootTree input cursor (read cursor) []).children :=
    List.Forall₂.imp (fun _ _ related => ⟨related.1, related.2.1⟩) pairedNil
  refine ⟨by rw [childrenEq]; simp [slotList], ?_, ?_⟩
  · intro path
    cases path with
    | nil =>
        exact context_nil4a_noReference descriptorMap unit (ruleMajorTreeGraph tree) observe W D node
          fullMatch.tableMatch realizes
          (hyp.label node _ (by rwa [← decoratedSubtreeAt?_eq_subtreeAt?]))
          (hyp.tetrahedral node) (hyp.available node)
    | cons digit path =>
        have encodedBot : encoded4a
            (localizedCumulativeRule45TerminalKey input .rule4cNoReference cursor (read cursor))
            (digit :: path) = ⊥ := by
          rw [encoded4a_cons_of_key_anyStage fullMatch.tableMatch realizes pairedNilBasic digit path]
          rfl
        have constBot : nodePathObservationWithObservations
            (ruleMajorTreeGraph tree) observe W D 0 node (digit :: path) = ⊥ := by
          have represented := (observedTree_terminal_bridge tree observe observations cursor
            fullMatch realizes (W := W) (D := D) node lookup).2
          have atPath := represented 0 (by omega) (digit :: path)
          unfold nodePathObservationWithObservations
          rw [atPath, encodedObservation_cons_of_key fullMatch.tableMatch realizes pairedNilBasic
            (ruleOfIndex 0) digit path]
          rfl
        rw [encodedBot]
        exact (observedStereoNodePathObservation_eq_bot_iff (ruleMajorTreeGraph tree) observe
          evidence .rule4aStereogenicUnitKind W D (digit :: path) node).2 constBot
  · intro path
    cases path with
    | nil =>
        exact context_nil4c_noReference descriptorMap unit (ruleMajorTreeGraph tree) observe W D node
          fullMatch.tableMatch fullMatch.labelMatch realizes
          (hyp.label node _ (by rwa [← decoratedSubtreeAt?_eq_subtreeAt?]))
          (hyp.available node)
    | cons digit path =>
        have encodedBot : encodedPseudo4c
            (localizedCumulativeRule45TerminalKey input .rule4cNoReference cursor (read cursor))
            (digit :: path) = ⊥ := by
          rw [encodedPseudo4c_cons_of_key fullMatch.tableMatch fullMatch.labelMatch realizes
            pairedNil digit path]
          rfl
        have constBot : nodePathObservationWithObservations
            (ruleMajorTreeGraph tree) observe W D 0 node (digit :: path) = ⊥ := by
          have represented := (observedTree_terminal_bridge tree observe observations cursor
            fullMatch realizes (W := W) (D := D) node lookup).2
          have atPath := represented 0 (by omega) (digit :: path)
          unfold nodePathObservationWithObservations
          rw [atPath, encodedObservation_cons_of_key fullMatch.tableMatch realizes pairedNilBasic
            (ruleOfIndex 0) digit path]
          rfl
        rw [encodedBot]
        exact (observedStereoNodePathObservation_eq_bot_iff (ruleMajorTreeGraph tree) observe
          evidence .rule4cPseudoasymmetricDescriptor W D (digit :: path) node).2 constBot
/-- Recursive no-reference bridge for an arbitrary realized contextual tree. The actual rule-major
trace determines descending observed `(constitution, 4a, 4c)` order and both active columns. -/
theorem contextTree_node_bridge_noReference4c
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : ContextTreeRankReadback tree descriptorMap unit)
    (mask : Rule4acOnly (ruleMajorTreeGraph tree)
      (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)))
    {W D : Nat} (hW : (ruleMajorTreeGraph tree).width ≤ W)
    (hD : (ruleMajorTreeGraph tree).height ≤ D)
    {fuel : Nat} (node : (ruleMajorTreeGraph tree).Node)
    (dsub : LocalizedCumulativeDecoratedTree input carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (trace : LocalizedRuleMajorSortTrace input (.rule4cNoReference) read fuel dsub key)
    (lookup : tree.decoratedSubtreeAt? node.1 = some dsub) :
    (((slotList (toOfficialSourceTree tree).declarativeAddressing node dsub.children.length).map
        (observedRule4acKey (ruleMajorTreeGraph tree) observe
          (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D)).Pairwise fun x y => y ≤ x) ∧
      Represents4a W D (observedRule4aComponent (ruleMajorTreeGraph tree) observe
        (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D node) key ∧
      Represents4c W D (observedRule4cComponent (ruleMajorTreeGraph tree) observe
        (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D node) key := by
  induction fuel generalizing dsub key node lookup with
  | zero =>
      cases trace with
      | terminal _fuel cursor _children _childrenComputed _terminalChildren fullMatch realizes =>
          exact contextTree_terminal_bridge_noReference4c tree observe observations hyp cursor fullMatch realizes
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
        exact contextTree_terminal_bridge_noReference4c tree observe observations hyp cursor fullMatch realizes
          node lookup
      · subst dsub
        subst key
        let evidence := noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)
        have hdense : DenseAt (toOfficialSourceTree tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length :=
          observedTree_denseAt_of_lookup tree node
            (localizedRootTree input cursor (read cursor) sortedTrees) lookup
        have paired := LocalizedRuleMajorSortTraceList.to_forall₂ childrenTraced
        have lengthEq : sortedKeys.length = sortedTrees.length := List.Forall₂.length_eq paired
        have pairedMatch : List.Forall₂ (fun childKey childTree =>
            LocalizedCumulativeTreeTableMatch (.rule4cNoReference) childTree childKey ∧
              LocalizedCumulativeTreeRealizes input read childTree ∧
                LocalizedCumulativeTreeLabelMatch childTree childKey) sortedKeys sortedTrees :=
          List.Forall₂.imp (fun childKey childTree related =>
            ⟨(LocalizedRuleMajorSortTrace.fullMatch_of_trace related).tableMatch,
              LocalizedRuleMajorSortTrace.realizes_of_trace related,
              (LocalizedRuleMajorSortTrace.fullMatch_of_trace related).labelMatch⟩) paired
        have pairedBasic : List.Forall₂ (fun childKey childTree =>
            LocalizedCumulativeTreeTableMatch (.rule4cNoReference) childTree childKey ∧
              LocalizedCumulativeTreeRealizes input read childTree) sortedKeys sortedTrees :=
          List.Forall₂.imp (fun _ _ related => ⟨related.1, related.2.1⟩) pairedMatch
        have descending : input.RuleMajorCumulativeKeysDescending
            (CertifiedLocalizedCIPInput.ruleMajorStageWidth .rule4cNoReference) sortedKeys :=
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
            LocalizedRuleMajorSortTrace input (.rule4cNoReference) read fuel (sortedTrees[i]'hi)
              (sortedKeys[i]'(by omega)) :=
          fun i hi => List.Forall₂.get (i := i) paired (by omega) hi
        have ihAt : ∀ i (hi : i < sortedTrees.length)
            (child : (ruleMajorTreeGraph tree).Node),
            tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
              Represents4a W D (observedRule4aComponent (ruleMajorTreeGraph tree) observe
                  evidence W D child) (sortedKeys[i]'(by omega)) ∧
                Represents4c W D (observedRule4cComponent (ruleMajorTreeGraph tree) observe
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
              (observedRule4acKey (ruleMajorTreeGraph tree) observe evidence W D)).Pairwise
                fun x y => y ≤ x := by
          rw [List.pairwise_iff_getElem]
          intro i j hi hj hij
          rw [List.length_map, slotLength] at hi hj
          obtain ⟨childI, slotI, _, lookupI⟩ := childAt i hi
          obtain ⟨childJ, slotJ, _, lookupJ⟩ := childAt j hj
          have hneWidth : input.compareRuleMajorCumulativeDescriptor
              (CertifiedLocalizedCIPInput.ruleMajorStageWidth .rule4cNoReference)
              (sortedKeys[i]'(by omega)) (sortedKeys[j]'(by omega)) ≠ Ordering.lt :=
            (List.pairwise_iff_getElem.1 descending) i j (by omega) (by omega) hij
          have widthEq : CertifiedLocalizedCIPInput.ruleMajorStageWidth .rule4cNoReference = 2 := rfl
          have hne : input.compareRuleMajorCumulativeDescriptor 2
              (sortedKeys[i]'(by omega)) (sortedKeys[j]'(by omega)) ≠ Ordering.lt := by
            rw [← widthEq]
            exact hneWidth
          have hle := observedRule4acKey_le_of_ruleMajor_compare_ne_lt
            (ruleMajorTreeGraph tree) observe evidence
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt i hi)).tableMatch
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt j hj)).tableMatch
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt i hi)).labelMatch
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt j hj)).labelMatch
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
            (context_ordinary_le_iff_rule4ac (ruleMajorTreeGraph tree) observe evidence mask W D
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
              (localizedCumulativeRule45StepKey input (.rule4cNoReference) cursor (read cursor) sortedKeys)
              (digit :: path) =
                ((sortedKeys[digit]?).map fun childKey => enc childKey path).getD ⊥) →
            ∀ digit path,
              Certificate.CanonicalSphereKey.pathObservationOf W D (comp node) (digit :: path) =
                enc (localizedCumulativeRule45StepKey input (.rule4cNoReference) cursor (read cursor) sortedKeys)
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
              exact context_nil4a_noReference descriptorMap unit (ruleMajorTreeGraph tree) observe W D node
                fullMatch.tableMatch realizes
                (hyp.label node _ (by rwa [← decoratedSubtreeAt?_eq_subtreeAt?]))
                (hyp.tetrahedral node) (hyp.available node)
          | cons digit path =>
              exact consCase .rule4aStereogenicUnitKind encoded4a
                (observedRule4aComponent (ruleMajorTreeGraph tree) observe evidence W D)
                (fun i hi child hl => (ihAt i hi child hl).1) (fun _ => rfl)
                (fun digit path => encoded4a_cons_of_key_anyStage fullMatch.tableMatch realizes
                  pairedBasic digit path) digit path
        · intro path
          cases path with
          | nil =>
              exact context_nil4c_noReference descriptorMap unit (ruleMajorTreeGraph tree) observe W D node
                fullMatch.tableMatch fullMatch.labelMatch realizes
                (hyp.label node _ (by rwa [← decoratedSubtreeAt?_eq_subtreeAt?]))
                (hyp.available node)
          | cons digit path =>
              exact consCase .rule4cPseudoasymmetricDescriptor encodedPseudo4c
                (observedRule4cComponent (ruleMajorTreeGraph tree) observe evidence W D)
                (fun i hi child hl => (ihAt i hi child hl).2) (fun _ => rfl)
                (fun digit path => encodedPseudo4c_cons_of_key fullMatch.tableMatch
                  fullMatch.labelMatch realizes pairedMatch digit path) digit path

/-- The no-reference bridge makes the actual contextual addressing canonical for the observed
ordinary key under no-reference Rule-4a/Rule-4c evidence. -/
theorem contextTree_keySorted_noReference4c
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : ContextTreeRankReadback tree descriptorMap unit)
    (mask : Rule4acOnly (ruleMajorTreeGraph tree)
      (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)))
    {fuel : Nat} {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input .rule4cNoReference read fuel tree key) :
    KeySorted
      (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
        (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
        (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height)
      (toOfficialSourceTree tree).declarativeAddressing := by
  intro parent first second firstSlot secondSlot addrFirst addrSecond hlt
  obtain ⟨dsub, lookup, _⟩ := observedTree_decoratedSubtree_of_node tree parent
  have hdense : DenseAt (toOfficialSourceTree tree).declarativeAddressing parent
      dsub.children.length := observedTree_denseAt_of_lookup tree parent dsub lookup
  rcases ruleMajorTrace_of_subtree input .rule4cNoReference read trace parent.1 dsub lookup with
    ⟨fuel', key', trace'⟩
  have bridge := contextTree_node_bridge_noReference4c tree observe observations hyp mask
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
  exact (context_ordinary_le_iff_rule4ac (ruleMajorTreeGraph tree) observe _ mask _ _ _ _).2 hpair

/-- The generated-state reader supplies contextual no-reference Rule-4c canonicality for every actual
executable child tree at an arbitrary detected target. -/
theorem generatedContextTree_rankCanonical_noReference4c
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input.certified
      (input.certified.certified.input.molecule.atomCount + 1))
    {fuel : Nat} {key : input.certified.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input.certified .rule4cNoReference
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) fuel tree key)
    (rootChild : tree.source ∈ input.certified.executableLocalizedRerootChildren target) :
    Dense (toOfficialSourceTree tree).declarativeAddressing ∧
      KeySorted
        (ordinaryKeyWithObservations (ruleMajorTreeGraph tree)
          (contextualNodeObservation input.certified.moleculeGraph (ruleMajorTreeGraph tree) unit.1.root)
          (noReferenceEvidence4c input.certified.moleculeGraph
            (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph tree))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height)
        (toOfficialSourceTree tree).declarativeAddressing ∧
      Represents4a (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
        (observedRule4aComponent (ruleMajorTreeGraph tree)
          (contextualNodeObservation input.certified.moleculeGraph (ruleMajorTreeGraph tree)
            unit.1.root)
          (noReferenceEvidence4c input.certified.moleculeGraph
            (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph tree))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
          (ruleMajorTreeGraph tree).root) key ∧
      Represents4c (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
        (observedRule4cComponent (ruleMajorTreeGraph tree)
          (contextualNodeObservation input.certified.moleculeGraph (ruleMajorTreeGraph tree)
            unit.1.root)
          (noReferenceEvidence4c input.certified.moleculeGraph
            (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph tree))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
          (ruleMajorTreeGraph tree).root) key := by
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
  have hyp := ruleMajorGeneratedContextTreeRankReadback input singleBonded acyclic
    target unit targetUnit tree realizes rootChild
  have rootEq := contextTree_outerRoot_eq_unitRoot singleBonded acyclic
    target unit targetUnit tree rootChild
  have observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      contextualNodeObservation input.certified.moleculeGraph (ruleMajorTreeGraph tree)
        unit.1.root rule node = priorityValue rule (armObservation rule actual) := by
    intro rule node actual lookup
    rw [← rootEq]
    exact contextualTree_nodeObservation singleBonded acyclic tree realizes rule node actual lookup
  have hsingle : ∀ atom other, input.certified.moleculeGraph.bond atom other ≤ 1 := by
    intro atom other
    rcases Nat.eq_zero_or_pos (input.certified.moleculeGraph.bond atom other) with hzero | hpos
    · rw [hzero]
      exact Nat.zero_le 1
    · exact le_of_eq (singleBonded atom other hpos)
  have mask := rule4acOnly_noReferenceEvidence4c_of_single input.certified.moleculeGraph
    (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph tree) hsingle
  have keySorted := contextTree_keySorted_noReference4c tree _ observations hyp mask trace
  have rootRepresentations := contextTree_node_bridge_noReference4c tree _ observations hyp mask
    (W := (ruleMajorTreeGraph tree).width) (D := (ruleMajorTreeGraph tree).height)
    le_rfl le_rfl (ruleMajorTreeGraph tree).root tree key trace (by
      change tree.decoratedSubtreeAt? [] = some tree
      rw [decoratedSubtreeAt?])
  exact ⟨(toOfficialSourceTree tree).declarativeAddressing_dense, keySorted,
    rootRepresentations.2.1, rootRepresentations.2.2⟩


end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextTree_terminal_bridge_noReference4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextTree_node_bridge_noReference4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextTree_keySorted_noReference4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.generatedContextTree_rankCanonical_noReference4c
