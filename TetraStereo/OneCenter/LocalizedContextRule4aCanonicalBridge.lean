import TetraStereo.OneCenter.LocalizedContextRule4aTableBridge
import TetraStereo.OneCenter.LocalizedContextStereoReadback
import TetraStereo.OneCenter.LocalizedRuleMajorObservedCanonicalBridge
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Actual Rule-4a canonicality at arbitrary retained-root contexts. This is the recursive
sorting/representation step; physical observation and generated-reader facts discharge its
node-local premises without requiring an original-root arm or desired comparison outcome. -/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge
open LocalizedCumulativeDecoratedTree CertifiedLocalizedCIPInput
open OfficialSparseCanonicalVectorComparison DeclarativeCIP
noncomputable section
open scoped Classical
variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}

private theorem context_ordinary_le_iff_pair
    (graph : RootedDigraph input.Atom) (observe : ConstitutionalRule → graph.Node → ℤ)
    (evidence : StereochemicalEvidence graph) (hyp : Rule4aOnly graph evidence)
    (W D : Nat) (left right : graph.Node) :
    ordinaryKeyWithObservations graph observe evidence W D left ≤
        ordinaryKeyWithObservations graph observe evidence W D right ↔
      observedPairKey graph observe evidence W D left ≤
        observedPairKey graph observe evidence W D right := by
  simpa only [not_lt] using
    not_congr (observedOrdinaryKey_lt_iff_pairKey graph observe evidence hyp W D right left)

private theorem context_nil4a
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (graph : RootedDigraph input.Atom)
    (observe : ConstitutionalRule → graph.Node → ℤ) (W D : Nat) (node : graph.Node)
    {actual : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (tableMatch : LocalizedCumulativeTreeTableMatch .rule4a actual key)
    (realizes : LocalizedCumulativeTreeRealizes input read actual)
    (label : actual.label = (occurrenceReading input.moleculeGraph descriptorMap unit graph node).toLocalizedLabel)
    (tetra : (occurrenceReading input.moleculeGraph descriptorMap unit graph node).IsTetrahedral)
    (available : occurrenceReading input.moleculeGraph descriptorMap unit graph node ≠ .unavailable) :
    observedStereoNodePathObservation graph observe
      (rankEvidence input.moleculeGraph descriptorMap unit graph) W D
      .rule4aStereogenicUnitKind node [] = encoded4a key [] := by
  rw [observedStereoNodePathObservation_nil,
    stereoLabel_rankEvidence_rule4a descriptorMap unit graph node available,
    encoded4a_nil tableMatch realizes, prio4a_eq_kindPriority actual _ label tetra]

/-- Terminal case: a root-only decorated tree matched by the terminal key. -/
theorem contextTree_terminal_bridge4a (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : ContextTreeRankReadback tree descriptorMap unit)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (fullMatch : LocalizedCumulativeTreeFullMatch .rule4a
      (localizedRootTree input cursor (read cursor) [])
      (localizedCumulativeRule45TerminalKey input .rule4a cursor (read cursor)))
    (realizes : LocalizedCumulativeTreeRealizes input read
      (localizedRootTree input cursor (read cursor) []))
    {W D : ℕ} (node : (ruleMajorTreeGraph tree).Node)
    (lookup : tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (read cursor) [])) :
    (((slotList (toOfficialSourceTree tree).declarativeAddressing node
          (localizedRootTree input cursor (read cursor) []).children.length).map
        (observedPairKey (ruleMajorTreeGraph tree) observe
          (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D)).Pairwise
      fun x y => y ≤ x) ∧
      Represents4a W D (observedRule4aComponent (ruleMajorTreeGraph tree) observe
        (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D node)
        (localizedCumulativeRule45TerminalKey input .rule4a cursor (read cursor)) := by
  have childrenEq : (localizedRootTree input cursor (read cursor) []).children = [] := by
    unfold localizedRootTree; rfl
  have pairedNil : List.Forall₂ (fun childKey childTree =>
      LocalizedCumulativeTreeTableMatch .rule4a childTree childKey ∧
        LocalizedCumulativeTreeRealizes input read childTree)
      ([] : List input.LocalizedRerootCumulativeRule45Key)
      (localizedRootTree input cursor (read cursor) []).children := by
    rw [childrenEq]; exact List.Forall₂.nil
  constructor
  · rw [childrenEq]; simp [slotList]
  · intro path
    cases path with
    | nil =>
        exact context_nil4a descriptorMap unit (ruleMajorTreeGraph tree) observe W D node
          fullMatch.tableMatch realizes (hyp.label node _ (by rwa [← decoratedSubtreeAt?_eq_subtreeAt?])) (hyp.tetrahedral node)
          (hyp.available node)
    | cons digit path =>
        have rhs : encoded4a (localizedCumulativeRule45TerminalKey input .rule4a cursor (read cursor))
            (digit :: path) = ⊥ := by
          rw [encoded4a_cons_of_key fullMatch.tableMatch realizes pairedNil digit path]; rfl
        have constBot : nodePathObservationWithObservations (ruleMajorTreeGraph tree) observe W D 0 node
            (digit :: path) = ⊥ := by
          have h := (observedTree_terminal_bridge tree observe observations cursor fullMatch realizes (W := W) (D := D) node lookup).2
          have h' := h 0 (by omega) (digit :: path)
          unfold nodePathObservationWithObservations
          rw [h', encodedObservation_cons_of_key fullMatch.tableMatch realizes pairedNil
            (ruleOfIndex 0) digit path]
          rfl
        rw [rhs]
        exact (observedStereoNodePathObservation_eq_bot_iff (ruleMajorTreeGraph tree) observe _ _ W D
          (digit :: path) node).2 constBot

/-- **Recursive Rule-4a bridge.** -/
theorem contextTree_node_bridge4a (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : ContextTreeRankReadback tree descriptorMap unit)
    {W D : ℕ} (hW : (ruleMajorTreeGraph tree).width ≤ W) (hD : (ruleMajorTreeGraph tree).height ≤ D)
    {fuel : Nat} (node : (ruleMajorTreeGraph tree).Node)
    (dsub : LocalizedCumulativeDecoratedTree input carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (trace : LocalizedRuleMajorSortTrace input .rule4a read fuel dsub key)
    (lookup : tree.decoratedSubtreeAt? node.1 = some dsub) :
    (((slotList (toOfficialSourceTree tree).declarativeAddressing node dsub.children.length).map
        (observedPairKey (ruleMajorTreeGraph tree) observe
          (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D)).Pairwise
      fun x y => y ≤ x) ∧
      Represents4a W D (observedRule4aComponent (ruleMajorTreeGraph tree) observe
        (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D node) key := by
  induction fuel generalizing dsub key node lookup with
  | zero =>
      cases trace with
      | terminal _fuel cursor _children _childrenComputed _terminalChildren fullMatch realizes =>
          exact contextTree_terminal_bridge4a tree observe observations hyp cursor fullMatch realizes node lookup
  | succ fuel ih =>
      have fullMatch := LocalizedRuleMajorSortTrace.fullMatch_of_trace trace
      have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
      rcases LocalizedRuleMajorSortTrace.structure_of_trace trace with
        ⟨cursor, _children, dsubEq, keyEq, _childrenEq, _childrenComputed, _terminalChildren⟩ |
        ⟨cursor, _children, _childKeys, sortedKeys, sortedTrees, dsubEq, keyEq, childrenEq,
          _childrenComputed, _nonempty, _childKeysComputed, _sortedEq, _constitutionalDescending, sortedDescending,
          childrenTraced⟩
      · subst dsub; subst key
        exact contextTree_terminal_bridge4a tree observe observations hyp cursor fullMatch realizes node lookup
      · subst dsub; subst key
        have hdense : DenseAt (toOfficialSourceTree tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length :=
          observedTree_denseAt_of_lookup tree node (localizedRootTree input cursor (read cursor) sortedTrees) lookup
        have paired := LocalizedRuleMajorSortTraceList.to_forall₂ childrenTraced
        have lengthEq : sortedKeys.length = sortedTrees.length := List.Forall₂.length_eq paired
        have pairedMatch : List.Forall₂ (fun childKey childTree =>
            LocalizedCumulativeTreeTableMatch .rule4a childTree childKey ∧
              LocalizedCumulativeTreeRealizes input read childTree) sortedKeys sortedTrees :=
          List.Forall₂.imp (fun childKey childTree related =>
            ⟨(LocalizedRuleMajorSortTrace.fullMatch_of_trace related).tableMatch,
              LocalizedRuleMajorSortTrace.realizes_of_trace related⟩) paired
        have descending : sortedKeys.Pairwise fun left right =>
            input.compareRuleMajorCumulativeDescriptor 1 left right ≠ Ordering.lt := by
          simpa [CertifiedLocalizedCIPInput.ruleMajorStageWidth] using sortedDescending
        have countEq : (localizedRootTree input cursor (read cursor) sortedTrees).children.length =
            sortedTrees.length := by rw [childrenEq]
        have slotLength : (slotList (toOfficialSourceTree tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length =
            sortedTrees.length := by simp [slotList, countEq]
        -- the child at slot `i`
        have childAt : ∀ i (hi : i < sortedTrees.length), ∃ child : (ruleMajorTreeGraph tree).Node,
            (slotList (toOfficialSourceTree tree).declarativeAddressing node (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[i]? =
                some child ∧
              child.1 = node.1 ++ [i] ∧
                tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) := by
          intro i hi
          obtain ⟨child, slotSome, addr⟩ := slotList_getD_of_lt (addressing := (toOfficialSourceTree tree).declarativeAddressing) (parent := node)
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
            LocalizedRuleMajorSortTrace input .rule4a read fuel (sortedTrees[i]'hi)
              (sortedKeys[i]'(by omega)) :=
          fun i hi => List.Forall₂.get (i := i) paired (by omega) hi
        have ihAt : ∀ i (hi : i < sortedTrees.length) (child : (ruleMajorTreeGraph tree).Node),
            tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
              Represents4a W D (observedRule4aComponent (ruleMajorTreeGraph tree) observe (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D child)
                (sortedKeys[i]'(by omega)) :=
          fun i hi child hl => (ih child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega)) (traceAt i hi) hl).2
        have constAt : ∀ i (hi : i < sortedTrees.length) (child : (ruleMajorTreeGraph tree).Node),
            tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
              Represents W D (ruleKeyWithObservations (ruleMajorTreeGraph tree) W D observe child)
                (sortedKeys[i]'(by omega)).constitutional :=
          fun i hi child hl =>
            (observedTree_node_bridge tree observe observations hW hD child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega))
              (traceAt i hi) hl).2
        have slotSorted : ((slotList (toOfficialSourceTree tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).map
              (observedPairKey (ruleMajorTreeGraph tree) observe (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D)).Pairwise fun x y => y ≤ x := by
          rw [List.pairwise_iff_getElem]
          intro i j hi hj hij
          rw [List.length_map, slotLength] at hi hj
          obtain ⟨childI, slotI, _, lookupI⟩ := childAt i hi
          obtain ⟨childJ, slotJ, _, lookupJ⟩ := childAt j hj
          have hne : input.compareRuleMajorCumulativeDescriptor 1 (sortedKeys[i]'(by omega))
              (sortedKeys[j]'(by omega)) ≠ Ordering.lt :=
            (List.pairwise_iff_getElem.1 descending) i j (by omega) (by omega) hij
          have hle := observedPairKey_le_of_ruleMajor_compare_ne_lt observe (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt i hi)).tableMatch
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt j hj)).tableMatch
            (LocalizedRuleMajorSortTrace.realizes_of_trace (traceAt i hi))
            (LocalizedRuleMajorSortTrace.realizes_of_trace (traceAt j hj))
            (constAt i hi childI lookupI) (constAt j hj childJ lookupJ)
            (ihAt i hi childI lookupI) (ihAt j hj childJ lookupJ) hne
          have getI : (slotList (toOfficialSourceTree tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[i]'(by
                rw [slotLength]; exact hi) = childI :=
            Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotI)
          have getJ : (slotList (toOfficialSourceTree tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[j]'(by
                rw [slotLength]; exact hj) = childJ :=
            Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotJ)
          simpa [List.getElem_map, getI, getJ] using hle
        refine ⟨slotSorted, ?_⟩
        intro path
        cases path with
        | nil =>
            exact context_nil4a descriptorMap unit (ruleMajorTreeGraph tree) observe W D node
              fullMatch.tableMatch realizes (hyp.label node _ (by rwa [← decoratedSubtreeAt?_eq_subtreeAt?])) (hyp.tetrahedral node)
              (hyp.available node)
        | cons digit path =>
            have slotSortedOrd : ((slotList (toOfficialSourceTree tree).declarativeAddressing node
                (localizedRootTree input cursor (read cursor) sortedTrees).children.length).map
                  (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D)).Pairwise fun x y => y ≤ x := by
              rw [List.pairwise_map] at slotSorted ⊢
              exact slotSorted.imp fun h =>
                (context_ordinary_le_iff_pair (ruleMajorTreeGraph tree) observe (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) hyp.rule4aOnly W D _ _).2 h
            change observedStereoNodePathObservation (ruleMajorTreeGraph tree) observe (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D
                .rule4aStereogenicUnitKind node (digit :: path) = encoded4a _ (digit :: path)
            rw [observedStereoNodePathObservation_cons (ruleMajorTreeGraph tree) observe (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D _ node
              (slotList_perm (addressing := (toOfficialSourceTree tree).declarativeAddressing) (parent := node)
                (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
                hdense) slotSortedOrd digit path,
              encoded4a_cons_of_key fullMatch.tableMatch realizes pairedMatch digit path]
            by_cases hdigit : digit < sortedTrees.length
            · obtain ⟨child, slotSome, childAddr, childLookup⟩ := childAt digit hdigit
              have digitLtKeys : digit < sortedKeys.length := by omega
              have rep4child := ihAt digit hdigit child childLookup
              rw [slotSome, List.getElem?_eq_getElem digitLtKeys]
              simp only [Option.map_some, Option.getD_some]
              by_cases hgate : digit < W ∧ path.length < D
              · rw [if_pos hgate]
                exact rep4child path
              · rw [if_neg hgate, ← rep4child path]
                symm
                apply (observedStereoNodePathObservation_eq_bot_iff (ruleMajorTreeGraph tree) observe (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) _ W D
                  path child).2
                by_contra hne
                have bound := depth_add_length_le_of_nodePathObservationWithObservations (ruleMajorTreeGraph tree) observe
                  (W := W) (D := D) (by omega : (0 : ℕ) < 3) path child hne
                have childDepth : (ruleMajorTreeGraph tree).depth child = (ruleMajorTreeGraph tree).depth node + 1 :=
                  (ruleMajorTreeGraph tree).child_depth ⟨digit, childAddr⟩
                have hdigitLtW : digit < W := by
                  have countLe : sortedTrees.length ≤ (ruleMajorTreeGraph tree).width := by
                    have := count_le_width
                      (addressing := (toOfficialSourceTree tree).declarativeAddressing)
                      (parent := node)
                      (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
                      hdense
                    rw [countEq] at this
                    exact this
                  omega
                have hpath : ¬ path.length < D := fun h => hgate ⟨hdigitLtW, h⟩
                omega
            · have slotNone : (slotList (toOfficialSourceTree tree).declarativeAddressing node
                  (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[digit]? =
                    none := by
                rw [List.getElem?_eq_none_iff, slotLength]; omega
              have keysNone : sortedKeys[digit]? = none := by
                rw [List.getElem?_eq_none_iff]; omega
              rw [slotNone, keysNone]
              split <;> rfl

/-! ## The arm's addressing is ordinary-canonical for the rank evidence -/

/-- **Prefix-2 canonical membership of the actual Rule-4a stage addressing.** -/
theorem contextTree_keySorted_rankEvidence (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : ContextTreeRankReadback tree descriptorMap unit)
    {fuel : Nat} {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input .rule4a read fuel tree key) :
    KeySorted (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
        (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
        (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height)
      (toOfficialSourceTree tree).declarativeAddressing := by
  intro parent first second firstSlot secondSlot addrFirst addrSecond hlt
  obtain ⟨dsub, lookup, _⟩ := observedTree_decoratedSubtree_of_node tree parent
  have hdense : DenseAt (toOfficialSourceTree tree).declarativeAddressing parent
      dsub.children.length := observedTree_denseAt_of_lookup tree parent dsub lookup
  rcases ruleMajorTrace_of_subtree input .rule4a read trace parent.1 dsub lookup with ⟨fuel', key', trace'⟩
  have bridge := contextTree_node_bridge4a tree observe observations hyp (W := (ruleMajorTreeGraph tree).width) (D := (ruleMajorTreeGraph tree).height)
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
  exact (context_ordinary_le_iff_pair (ruleMajorTreeGraph tree) observe _ hyp.rule4aOnly _ _ _ _).2 hpair


/-- An actual emitted arm retains the independent target unit's outer root. -/
theorem contextTree_outerRoot_eq_unitRoot
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (target : input.LocalizedRerootCursor carrierFuel)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target) :
    tree.source.occurrence.1.root = unit.1.root := by
  obtain ⟨atom, _path, current, _head, _real, _simple, _support, _parent⟩ :=
    input.carrierOccurrence_realPath singleBonded acyclic tree.source.occurrence
  have step := input.molecularFrameUnit_executableChild_rerootStep
    singleBonded acyclic target tree.source current rootChild
  exact step.1.trans (congrArg OccurrenceUnit.root targetUnit)

/-- All data-level canonicality premises are discharged for the revised evaluator's own
generated reader, at an arbitrary detected target occurrence and any actual child arm. -/
theorem generatedContextTree_rankCanonical
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
    (trace : LocalizedRuleMajorSortTrace input.certified .rule4a
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) fuel tree key)
    (rootChild : tree.source ∈ input.certified.executableLocalizedRerootChildren target) :
    Dense (toOfficialSourceTree tree).declarativeAddressing ∧
      KeySorted
        (contextualOrdinaryKey (ruleMajorTreeGraph tree)
          (rankEvidence input.certified.moleculeGraph (LocalizedRuleMajorReference.descriptorMap input)
            unit (ruleMajorTreeGraph tree)) input.certified.moleculeGraph unit.1.root
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height)
        (toOfficialSourceTree tree).declarativeAddressing ∧
      Represents4a (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
        (observedRule4aComponent (ruleMajorTreeGraph tree)
          (contextualNodeObservation input.certified.moleculeGraph (ruleMajorTreeGraph tree) unit.1.root)
          (rankEvidence input.certified.moleculeGraph (LocalizedRuleMajorReference.descriptorMap input)
            unit (ruleMajorTreeGraph tree))
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
  refine ⟨(toOfficialSourceTree tree).declarativeAddressing_dense,
    contextTree_keySorted_rankEvidence tree _ observations hyp trace, ?_⟩
  exact (contextTree_node_bridge4a tree _ observations hyp le_rfl le_rfl
    (ruleMajorTreeGraph tree).root tree key trace (by
      change tree.decoratedSubtreeAt? [] = some tree
      rw [decoratedSubtreeAt?])).2

/-- Successful executable construction and independent contextual rank canonicality for every
valid actual arm of a generated-state target. No build, readback, reference selection, sorting,
or comparison result is supplied as a premise. -/
theorem exists_generatedContextTree_rankCanonical
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursor : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (rootChild : cursor ∈ input.certified.executableLocalizedRerootChildren target)
    (valid : input.certified.LocalizedRerootCursorValid cursor) :
    ∃ (tree : LocalizedCumulativeDecoratedTree input.certified
        (input.certified.certified.input.molecule.atomCount + 1))
      (key : input.certified.LocalizedRerootCumulativeRule45Key),
      tree.source = cursor ∧
      input.certified.buildRuleMajorCumulativeWithReadExec? .rule4a
        (input.certified.localizedDependencyLabel target.occurrence
          (input.certified.localizedDependencyView
            (LocalizedRuleMajorReference.referenceState input) target.occurrence))
        (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) cursor = some key ∧
      Dense (toOfficialSourceTree tree).declarativeAddressing ∧
      KeySorted
        (contextualOrdinaryKey (ruleMajorTreeGraph tree)
          (rankEvidence input.certified.moleculeGraph (LocalizedRuleMajorReference.descriptorMap input)
            unit (ruleMajorTreeGraph tree)) input.certified.moleculeGraph unit.1.root
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height)
        (toOfficialSourceTree tree).declarativeAddressing ∧
      Represents4a (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
        (observedRule4aComponent (ruleMajorTreeGraph tree)
          (contextualNodeObservation input.certified.moleculeGraph (ruleMajorTreeGraph tree) unit.1.root)
          (rankEvidence input.certified.moleculeGraph (LocalizedRuleMajorReference.descriptorMap input)
            unit (ruleMajorTreeGraph tree))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
          (ruleMajorTreeGraph tree).root) key := by
  obtain ⟨tree, key, source, built, trace⟩ := exists_ruleMajorTrace_at_twice input.certified .rule4a
    (input.certified.localizedDependencyLabel target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursor valid
  refine ⟨tree, key, source, ?_, ?_⟩
  · rw [input.certified.buildRuleMajorCumulativeWithReadExec_eq]
    exact built
  · exact generatedContextTree_rankCanonical input singleBonded acyclic
      target unit targetUnit tree trace (by simpa only [source] using rootChild)

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextTree_terminal_bridge4a
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextTree_node_bridge4a
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextTree_keySorted_rankEvidence
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextTree_outerRoot_eq_unitRoot
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.generatedContextTree_rankCanonical
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.exists_generatedContextTree_rankCanonical
