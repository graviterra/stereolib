import TetraStereo.OneCenter.LocalizedRetainedContextStereoReadback
import TetraStereo.OneCenter.LocalizedContextRule4aTableBridge
import TetraStereo.OneCenter.LocalizedRuleMajorObservedCanonicalBridge
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Retained Rule-4a sort-trace representation

The stage-`.rule4a` sibling order and sphere-key representation for one realized tree.
The constitutional observer is the retained context observer, and the stereochemical column
is `retainedRankEvidence`. Ring duplicates stay in the tree: a real node must be available,
and a ring duplicate is the unavailable reading whose localized label is `none`.

The empty-address equality is false for `rankEvidence` on that duplicate, because that
evidence stores `⊥` while the actual priority of `none` is the present zero. The nil lemma
therefore splits on `RetainedRankNodeStatus`. The fuel induction is the old sort-trace
induction restated at this evidence. It does not assume `Acyclic`, and it does not assume
every node is a real atom.

These theorems are the stage-4a addressing and comparison representation. They do not
prove the retained compound comparison or an end-to-end ring descriptor.
-/

namespace TetraStereo.OneCenter.RetainedRule4aCanonicalBridge

open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open OfficialSparseCanonicalVectorComparison
open DeclarativeCIP
open TetraStereo.OneCenter.Rule4aTableBridge
open TetraStereo.OneCenter.RetainedContextStereoReadback

noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

section WithReader

variable {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}

private theorem retainedContext_ordinary_le_iff_pair
    (graph : RootedDigraph input.Atom) (observe : ConstitutionalRule → graph.Node → ℤ)
    (evidence : StereochemicalEvidence graph) (hyp : Rule4aOnly graph evidence)
    (W D : Nat) (left right : graph.Node) :
    ordinaryKeyWithObservations graph observe evidence W D left ≤
        ordinaryKeyWithObservations graph observe evidence W D right ↔
      observedPairKey graph observe evidence W D left ≤
        observedPairKey graph observe evidence W D right := by
  simpa only [not_lt] using
    not_congr (observedOrdinaryKey_lt_iff_pairKey graph observe evidence hyp W D right left)

/-- Empty-address Rule 4a. A real available node uses its kind priority. A ring duplicate
uses the present nonstereogenic code, which is the priority of localized label `none`. -/
theorem retainedContext_nil4a
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (graph : RootedDigraph input.Atom)
    (observe : ConstitutionalRule → graph.Node → ℤ)
    (W D : Nat) (node : graph.Node)
    (status : RetainedRankNodeStatus input.moleculeGraph descriptorMap unit graph node)
    {actual : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (tableMatch : LocalizedCumulativeTreeTableMatch .rule4a actual key)
    (realizes : LocalizedCumulativeTreeRealizes input read actual)
    (labelEq : actual.label =
      (occurrenceReading input.moleculeGraph descriptorMap unit graph node).toLocalizedLabel)
    (tetra : (occurrenceReading input.moleculeGraph descriptorMap unit graph node).IsTetrahedral) :
    observedStereoNodePathObservation graph observe
        (retainedRankEvidence input.moleculeGraph descriptorMap unit graph) W D
        .rule4aStereogenicUnitKind node [] =
      encoded4a key [] := by
  cases status with
  | realAvailable real available =>
      rw [observedStereoNodePathObservation_nil,
        stereoLabel_retainedRankEvidence_rule4a_real_available descriptorMap unit graph node
          real available,
        encoded4a_nil tableMatch realizes,
        prio4a_eq_kindPriority actual _ labelEq tetra]
  | ringDuplicate distance duplicate unavailable noneLabel =>
      have actualNone : actual.label = none := by
        rw [unavailable] at noneLabel
        rw [labelEq, unavailable]
        exact noneLabel
      rw [observedStereoNodePathObservation_nil,
        stereoLabel_retainedRankEvidence_rule4a_ringDuplicate_eq_code descriptorMap unit graph
          node distance duplicate,
        encoded4a_nil tableMatch realizes]
      have prioZero : prio4a actual = StereogenicUnitKind.nonstereogenic.priority := by
        unfold prio4a
        rw [actualNone]
        rfl
      rw [prioZero]

/-- Terminal case: a root-only decorated tree matched by the terminal key. -/
theorem retainedContextTree_terminal_bridge4a (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : RetainedContextTreeRankReadback tree descriptorMap unit)
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
          (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D)).Pairwise
      fun x y => y ≤ x) ∧
      Represents4a W D (observedRule4aComponent (ruleMajorTreeGraph tree) observe
        (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D node)
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
        exact retainedContext_nil4a descriptorMap unit (ruleMajorTreeGraph tree) observe W D node
          (hyp.nodeStatus node)
          fullMatch.tableMatch realizes (hyp.label node _ (by rwa [← decoratedSubtreeAt?_eq_subtreeAt?])) (hyp.tetrahedral node)
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
theorem retainedContextTree_node_bridge4a (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : RetainedContextTreeRankReadback tree descriptorMap unit)
    {W D : ℕ} (hW : (ruleMajorTreeGraph tree).width ≤ W) (hD : (ruleMajorTreeGraph tree).height ≤ D)
    {fuel : Nat} (node : (ruleMajorTreeGraph tree).Node)
    (dsub : LocalizedCumulativeDecoratedTree input carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (trace : LocalizedRuleMajorSortTrace input .rule4a read fuel dsub key)
    (lookup : tree.decoratedSubtreeAt? node.1 = some dsub) :
    (((slotList (toOfficialSourceTree tree).declarativeAddressing node dsub.children.length).map
        (observedPairKey (ruleMajorTreeGraph tree) observe
          (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D)).Pairwise
      fun x y => y ≤ x) ∧
      Represents4a W D (observedRule4aComponent (ruleMajorTreeGraph tree) observe
        (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D node) key := by
  induction fuel generalizing dsub key node lookup with
  | zero =>
      cases trace with
      | terminal _fuel cursor _children _childrenComputed _terminalChildren fullMatch realizes =>
          exact retainedContextTree_terminal_bridge4a tree observe observations hyp cursor fullMatch realizes node lookup
  | succ fuel ih =>
      have fullMatch := LocalizedRuleMajorSortTrace.fullMatch_of_trace trace
      have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
      rcases LocalizedRuleMajorSortTrace.structure_of_trace trace with
        ⟨cursor, _children, dsubEq, keyEq, _childrenEq, _childrenComputed, _terminalChildren⟩ |
        ⟨cursor, _children, _childKeys, sortedKeys, sortedTrees, dsubEq, keyEq, childrenEq,
          _childrenComputed, _nonempty, _childKeysComputed, _sortedEq, _constitutionalDescending, sortedDescending,
          childrenTraced⟩
      · subst dsub; subst key
        exact retainedContextTree_terminal_bridge4a tree observe observations hyp cursor fullMatch realizes node lookup
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
              Represents4a W D (observedRule4aComponent (ruleMajorTreeGraph tree) observe (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D child)
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
              (observedPairKey (ruleMajorTreeGraph tree) observe (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D)).Pairwise fun x y => y ≤ x := by
          rw [List.pairwise_iff_getElem]
          intro i j hi hj hij
          rw [List.length_map, slotLength] at hi hj
          obtain ⟨childI, slotI, _, lookupI⟩ := childAt i hi
          obtain ⟨childJ, slotJ, _, lookupJ⟩ := childAt j hj
          have hne : input.compareRuleMajorCumulativeDescriptor 1 (sortedKeys[i]'(by omega))
              (sortedKeys[j]'(by omega)) ≠ Ordering.lt :=
            (List.pairwise_iff_getElem.1 descending) i j (by omega) (by omega) hij
          have hle := observedPairKey_le_of_ruleMajor_compare_ne_lt observe (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
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
            exact retainedContext_nil4a descriptorMap unit (ruleMajorTreeGraph tree) observe W D node
              (hyp.nodeStatus node)
              fullMatch.tableMatch realizes (hyp.label node _ (by rwa [← decoratedSubtreeAt?_eq_subtreeAt?])) (hyp.tetrahedral node)
        | cons digit path =>
            have slotSortedOrd : ((slotList (toOfficialSourceTree tree).declarativeAddressing node
                (localizedRootTree input cursor (read cursor) sortedTrees).children.length).map
                  (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D)).Pairwise fun x y => y ≤ x := by
              rw [List.pairwise_map] at slotSorted ⊢
              exact slotSorted.imp fun h =>
                (retainedContext_ordinary_le_iff_pair (ruleMajorTreeGraph tree) observe (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) hyp.rule4aOnly W D _ _).2 h
            change observedStereoNodePathObservation (ruleMajorTreeGraph tree) observe (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D
                .rule4aStereogenicUnitKind node (digit :: path) = encoded4a _ (digit :: path)
            rw [observedStereoNodePathObservation_cons (ruleMajorTreeGraph tree) observe (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D _ node
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
                apply (observedStereoNodePathObservation_eq_bot_iff (ruleMajorTreeGraph tree) observe (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) _ W D
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
theorem retainedContextTree_keySorted_rankEvidence (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : RetainedContextTreeRankReadback tree descriptorMap unit)
    {fuel : Nat} {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input .rule4a read fuel tree key) :
    KeySorted (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
        (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
        (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height)
      (toOfficialSourceTree tree).declarativeAddressing := by
  intro parent first second firstSlot secondSlot addrFirst addrSecond hlt
  obtain ⟨dsub, lookup, _⟩ := observedTree_decoratedSubtree_of_node tree parent
  have hdense : DenseAt (toOfficialSourceTree tree).declarativeAddressing parent
      dsub.children.length := observedTree_denseAt_of_lookup tree parent dsub lookup
  rcases ruleMajorTrace_of_subtree input .rule4a read trace parent.1 dsub lookup with ⟨fuel', key', trace'⟩
  have bridge := retainedContextTree_node_bridge4a tree observe observations hyp (W := (ruleMajorTreeGraph tree).width) (D := (ruleMajorTreeGraph tree).height)
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
  exact (retainedContext_ordinary_le_iff_pair (ruleMajorTreeGraph tree) observe _ hyp.rule4aOnly _ _ _ _).2 hpair


/-- **Stage-4a canonical addressing of one realized tree.** Density, descending sibling keys,
and Rule-4a representation at the root. The observer and the retained bundle are hypotheses:
this statement does not choose a reader. -/
theorem retainedContextTree_rankCanonical
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : RetainedContextTreeRankReadback tree descriptorMap unit)
    {fuel : Nat} {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input .rule4a read fuel tree key) :
    Dense (toOfficialSourceTree tree).declarativeAddressing ∧
      KeySorted
        (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
          (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height)
        (toOfficialSourceTree tree).declarativeAddressing ∧
      Represents4a (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
        (observedRule4aComponent (ruleMajorTreeGraph tree) observe
          (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
          (ruleMajorTreeGraph tree).root) key := by
  refine ⟨(toOfficialSourceTree tree).declarativeAddressing_dense,
    retainedContextTree_keySorted_rankEvidence tree observe observations hyp trace, ?_⟩
  exact (retainedContextTree_node_bridge4a tree observe observations hyp
    (W := (ruleMajorTreeGraph tree).width) (D := (ruleMajorTreeGraph tree).height)
    le_rfl le_rfl (ruleMajorTreeGraph tree).root tree key trace (by
      change tree.decoratedSubtreeAt? [] = some tree
      rw [decoratedSubtreeAt?])).2

/-- **Actual Rule-4a comparison of two realized trees.** The runtime comparator equals the
comparison of the retained pair keys. No agreement of the two arms is assumed. -/
theorem retainedContextTrees_rule4a_compare
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    {fuelLeft fuelRight : Nat}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftTrace : LocalizedRuleMajorSortTrace input .rule4a read fuelLeft left leftKey)
    (rightTrace : LocalizedRuleMajorSortTrace input .rule4a read fuelRight right rightKey)
    (observeLeft : ConstitutionalRule → (ruleMajorTreeGraph left).Node → ℤ)
    (observeRight : ConstitutionalRule → (ruleMajorTreeGraph right).Node → ℤ)
    (leftObservations : ∀ rule node actual, left.decoratedSubtreeAt? node.1 = some actual →
      observeLeft rule node = priorityValue rule (armObservation rule actual))
    (rightObservations : ∀ rule node actual, right.decoratedSubtreeAt? node.1 = some actual →
      observeRight rule node = priorityValue rule (armObservation rule actual))
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {leftUnit rightUnit : DetectedOccurrence input.moleculeGraph}
    (leftReadback : RetainedContextTreeRankReadback left descriptorMap leftUnit)
    (rightReadback : RetainedContextTreeRankReadback right descriptorMap rightUnit)
    {W D : Nat}
    (leftWidth : (ruleMajorTreeGraph left).width ≤ W)
    (rightWidth : (ruleMajorTreeGraph right).width ≤ W)
    (leftHeight : (ruleMajorTreeGraph left).height ≤ D)
    (rightHeight : (ruleMajorTreeGraph right).height ≤ D) :
    input.compareLocalizedRerootCumulativeRule45Keys leftKey rightKey =
      compare
        (observedPairKey (ruleMajorTreeGraph left) observeLeft
          (retainedRankEvidence input.moleculeGraph descriptorMap leftUnit
            (ruleMajorTreeGraph left)) W D (ruleMajorTreeGraph left).root)
        (observedPairKey (ruleMajorTreeGraph right) observeRight
          (retainedRankEvidence input.moleculeGraph descriptorMap rightUnit
            (ruleMajorTreeGraph right)) W D (ruleMajorTreeGraph right).root) := by
  have repL := (retainedContextTree_node_bridge4a left observeLeft leftObservations leftReadback
    leftWidth leftHeight (ruleMajorTreeGraph left).root left leftKey leftTrace (by
      change left.decoratedSubtreeAt? [] = some left
      rw [decoratedSubtreeAt?])).2
  have repR := (retainedContextTree_node_bridge4a right observeRight rightObservations rightReadback
    rightWidth rightHeight (ruleMajorTreeGraph right).root right rightKey rightTrace (by
      change right.decoratedSubtreeAt? [] = some right
      rw [decoratedSubtreeAt?])).2
  have constitution := compare_eq_compare_vector
    (wellFormedRuleMajorKey_of_tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace leftTrace).tableMatch
      (LocalizedRuleMajorSortTrace.realizes_of_trace leftTrace))
    (wellFormedRuleMajorKey_of_tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace rightTrace).tableMatch
      (LocalizedRuleMajorSortTrace.realizes_of_trace rightTrace))
    (ruleKeyWithObservations_vectorWellShaped (ruleMajorTreeGraph left) observeLeft W D
      (ruleMajorTreeGraph left).root)
    (ruleKeyWithObservations_vectorWellShaped (ruleMajorTreeGraph right) observeRight W D
      (ruleMajorTreeGraph right).root)
    (observedTree_node_bridge left observeLeft leftObservations leftWidth leftHeight
      (ruleMajorTreeGraph left).root left leftKey leftTrace (by
        change left.decoratedSubtreeAt? [] = some left
        rw [decoratedSubtreeAt?])).2
    (observedTree_node_bridge right observeRight rightObservations rightWidth rightHeight
      (ruleMajorTreeGraph right).root right rightKey rightTrace (by
        change right.decoratedSubtreeAt? [] = some right
        rw [decoratedSubtreeAt?])).2
  change (OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional).then
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        leftKey.descriptor rightKey.descriptor) =
    (compare
      (ruleKeyWithObservations (ruleMajorTreeGraph left) W D observeLeft
        (ruleMajorTreeGraph left).root)
      (ruleKeyWithObservations (ruleMajorTreeGraph right) W D observeRight
        (ruleMajorTreeGraph right).root)).then _
  rw [constitution]
  cases h : compare
      (ruleKeyWithObservations (ruleMajorTreeGraph left) W D observeLeft
        (ruleMajorTreeGraph left).root)
      (ruleKeyWithObservations (ruleMajorTreeGraph right) W D observeRight
        (ruleMajorTreeGraph right).root) with
  | lt => rfl
  | gt => rfl
  | eq =>
      simp only [Ordering.eq_then]
      have tied := constitution.trans h
      simp only [OfficialRuleMajorKey.compare, compareLex, Ordering.byKey,
        Ordering.then_eq_eq] at tied
      exact compare_descriptor_eq_compare_key
        (LocalizedRuleMajorSortTrace.fullMatch_of_trace leftTrace).tableMatch
        (LocalizedRuleMajorSortTrace.fullMatch_of_trace rightTrace).tableMatch
        (LocalizedRuleMajorSortTrace.realizes_of_trace leftTrace)
        (LocalizedRuleMajorSortTrace.realizes_of_trace rightTrace)
        tied.1
        (ordinaryKeyWithObservations_stereo_wellShaped (ruleMajorTreeGraph left) observeLeft
          (retainedRankEvidence input.moleculeGraph descriptorMap leftUnit
            (ruleMajorTreeGraph left)) W D .rule4aStereogenicUnitKind
          (ruleMajorTreeGraph left).root)
        (ordinaryKeyWithObservations_stereo_wellShaped (ruleMajorTreeGraph right) observeRight
          (retainedRankEvidence input.moleculeGraph descriptorMap rightUnit
            (ruleMajorTreeGraph right)) W D .rule4aStereogenicUnitKind
          (ruleMajorTreeGraph right).root)
        repL repR

end WithReader

/-- Decorated lookup is the subtree lookup used by the retained observer law. -/
theorem retainedDecoratedObservation_eq_arm
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (target : input.LocalizedRerootCursor carrierFuel)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target)
    (rule : ConstitutionalRule)
    (node : (ruleMajorTreeGraph tree).Node)
    (actual : LocalizedCumulativeDecoratedTree input carrierFuel)
    (lookup : tree.decoratedSubtreeAt? node.1 = some actual) :
    retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph tree) unit rule node =
      priorityValue rule (armObservation rule actual) := by
  have subtree : subtreeAt? tree node.1 = some actual := by
    rw [← decoratedSubtreeAt?_eq_subtreeAt?]
    exact lookup
  exact input.retainedContextNodeObservation_eq_armObservation singleBonded target unit targetUnit
    tree realizes rootChild rule node actual subtree

/-- Molecular-reader discharge of stage-4a canonicality for one simple-bonded child tree.
Ring duplicates are allowed. This is not a compound descriptor. -/
theorem retainedMolecularContextTree_rankCanonical
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (target : input.LocalizedRerootCursor carrierFuel)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    {fuel : Nat} {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input .rule4a
      (input.molecularReader descriptorMap target.occurrence) fuel tree key)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target) :
    Dense (toOfficialSourceTree tree).declarativeAddressing ∧
      KeySorted
        (ordinaryKeyWithObservations (ruleMajorTreeGraph tree)
          (retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph tree) unit)
          (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height)
        (toOfficialSourceTree tree).declarativeAddressing ∧
      Represents4a (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
        (observedRule4aComponent (ruleMajorTreeGraph tree)
          (retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph tree) unit)
          (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
          (ruleMajorTreeGraph tree).root) key := by
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
  have hyp := retainedContextTreeRankReadback_of_molecularReader descriptorMap tetrahedralMap
    singleBonded target unit targetUnit tree realizes rootChild
  exact retainedContextTree_rankCanonical tree
    (retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph tree) unit)
    (fun rule node actual lookup => retainedDecoratedObservation_eq_arm singleBonded target unit
      targetUnit tree realizes rootChild rule node actual lookup)
    hyp trace

/-- The generated dependency reader is the molecular reader, so the same canonicality holds. -/
theorem retainedGeneratedContextTree_rankCanonical
    (reference : LocalizedRuleMajorReference.Input)
    (singleBonded : reference.certified.moleculeGraph.SimpleBonded)
    (target : reference.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel reference))
    (unit : DetectedOccurrence reference.certified.moleculeGraph)
    (targetUnit : reference.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree reference.certified
      (LocalizedRuleMajorReference.carrierFuel reference))
    {fuel : Nat} {key : reference.certified.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace reference.certified .rule4a
      (reference.certified.localizedDependencyLabel target.occurrence
        (reference.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState reference) target.occurrence))
      fuel tree key)
    (rootChild : tree.source ∈ reference.certified.executableLocalizedRerootChildren target) :
    Dense (toOfficialSourceTree tree).declarativeAddressing ∧
      KeySorted
        (ordinaryKeyWithObservations (ruleMajorTreeGraph tree)
          (retainedContextNodeObservation reference.certified.moleculeGraph
            (ruleMajorTreeGraph tree) unit)
          (retainedRankEvidence reference.certified.moleculeGraph
            (LocalizedRuleMajorReference.descriptorMap reference) unit (ruleMajorTreeGraph tree))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height)
        (toOfficialSourceTree tree).declarativeAddressing ∧
      Represents4a (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
        (observedRule4aComponent (ruleMajorTreeGraph tree)
          (retainedContextNodeObservation reference.certified.moleculeGraph
            (ruleMajorTreeGraph tree) unit)
          (retainedRankEvidence reference.certified.moleculeGraph
            (LocalizedRuleMajorReference.descriptorMap reference) unit (ruleMajorTreeGraph tree))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
          (ruleMajorTreeGraph tree).root) key := by
  have readerEq := LocalizedRuleMajorReference.molecularReader_eq_generatedReader_of_simpleBonded
    reference singleBonded target.occurrence
  have trace' : LocalizedRuleMajorSortTrace reference.certified .rule4a
      (reference.certified.molecularReader
        (LocalizedRuleMajorReference.descriptorMap reference) target.occurrence) fuel tree key := by
    rw [← readerEq] at trace
    exact trace
  exact retainedMolecularContextTree_rankCanonical
    (LocalizedRuleMajorReference.descriptorMap reference)
    (fun occurrence value observed =>
      LocalizedRuleMajorReference.descriptorMap_tetrahedral reference occurrence value observed)
    singleBonded target unit targetUnit tree trace' rootChild

/-- Molecular-reader discharge of the two-arm Rule-4a comparison. The arms may differ. -/
theorem retainedMolecularContextTrees_rule4a_compare
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (target : input.LocalizedRerootCursor carrierFuel)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    {fuelLeft fuelRight : Nat}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftTrace : LocalizedRuleMajorSortTrace input .rule4a
      (input.molecularReader descriptorMap target.occurrence) fuelLeft left leftKey)
    (rightTrace : LocalizedRuleMajorSortTrace input .rule4a
      (input.molecularReader descriptorMap target.occurrence) fuelRight right rightKey)
    (leftChild : left.source ∈ input.executableLocalizedRerootChildren target)
    (rightChild : right.source ∈ input.executableLocalizedRerootChildren target)
    {W D : Nat}
    (leftWidth : (ruleMajorTreeGraph left).width ≤ W)
    (rightWidth : (ruleMajorTreeGraph right).width ≤ W)
    (leftHeight : (ruleMajorTreeGraph left).height ≤ D)
    (rightHeight : (ruleMajorTreeGraph right).height ≤ D) :
    input.compareLocalizedRerootCumulativeRule45Keys leftKey rightKey =
      compare
        (observedPairKey (ruleMajorTreeGraph left)
          (retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph left) unit)
          (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph left))
          W D (ruleMajorTreeGraph left).root)
        (observedPairKey (ruleMajorTreeGraph right)
          (retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph right) unit)
          (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph right))
          W D (ruleMajorTreeGraph right).root) := by
  have realizesL := LocalizedRuleMajorSortTrace.realizes_of_trace leftTrace
  have realizesR := LocalizedRuleMajorSortTrace.realizes_of_trace rightTrace
  exact retainedContextTrees_rule4a_compare left right leftTrace rightTrace
    (retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph left) unit)
    (retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph right) unit)
    (fun rule node actual lookup => retainedDecoratedObservation_eq_arm singleBonded target unit
      targetUnit left realizesL leftChild rule node actual lookup)
    (fun rule node actual lookup => retainedDecoratedObservation_eq_arm singleBonded target unit
      targetUnit right realizesR rightChild rule node actual lookup)
    (retainedContextTreeRankReadback_of_molecularReader descriptorMap tetrahedralMap singleBonded
      target unit targetUnit left realizesL leftChild)
    (retainedContextTreeRankReadback_of_molecularReader descriptorMap tetrahedralMap singleBonded
      target unit targetUnit right realizesR rightChild)
    leftWidth rightWidth leftHeight rightHeight

/-- Generated-reader discharge of the two-arm Rule-4a comparison. -/
theorem retainedGeneratedContextTrees_rule4a_compare
    (reference : LocalizedRuleMajorReference.Input)
    (singleBonded : reference.certified.moleculeGraph.SimpleBonded)
    (target : reference.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel reference))
    (unit : DetectedOccurrence reference.certified.moleculeGraph)
    (targetUnit : reference.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (left right : LocalizedCumulativeDecoratedTree reference.certified
      (LocalizedRuleMajorReference.carrierFuel reference))
    {fuelLeft fuelRight : Nat}
    {leftKey rightKey : reference.certified.LocalizedRerootCumulativeRule45Key}
    (leftTrace : LocalizedRuleMajorSortTrace reference.certified .rule4a
      (reference.certified.localizedDependencyLabel target.occurrence
        (reference.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState reference) target.occurrence))
      fuelLeft left leftKey)
    (rightTrace : LocalizedRuleMajorSortTrace reference.certified .rule4a
      (reference.certified.localizedDependencyLabel target.occurrence
        (reference.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState reference) target.occurrence))
      fuelRight right rightKey)
    (leftChild : left.source ∈ reference.certified.executableLocalizedRerootChildren target)
    (rightChild : right.source ∈ reference.certified.executableLocalizedRerootChildren target)
    {W D : Nat}
    (leftWidth : (ruleMajorTreeGraph left).width ≤ W)
    (rightWidth : (ruleMajorTreeGraph right).width ≤ W)
    (leftHeight : (ruleMajorTreeGraph left).height ≤ D)
    (rightHeight : (ruleMajorTreeGraph right).height ≤ D) :
    reference.certified.compareLocalizedRerootCumulativeRule45Keys leftKey rightKey =
      compare
        (observedPairKey (ruleMajorTreeGraph left)
          (retainedContextNodeObservation reference.certified.moleculeGraph
            (ruleMajorTreeGraph left) unit)
          (retainedRankEvidence reference.certified.moleculeGraph
            (LocalizedRuleMajorReference.descriptorMap reference) unit (ruleMajorTreeGraph left))
          W D (ruleMajorTreeGraph left).root)
        (observedPairKey (ruleMajorTreeGraph right)
          (retainedContextNodeObservation reference.certified.moleculeGraph
            (ruleMajorTreeGraph right) unit)
          (retainedRankEvidence reference.certified.moleculeGraph
            (LocalizedRuleMajorReference.descriptorMap reference) unit (ruleMajorTreeGraph right))
          W D (ruleMajorTreeGraph right).root) := by
  have readerEq := LocalizedRuleMajorReference.molecularReader_eq_generatedReader_of_simpleBonded
    reference singleBonded target.occurrence
  have leftTrace' : LocalizedRuleMajorSortTrace reference.certified .rule4a
      (reference.certified.molecularReader
        (LocalizedRuleMajorReference.descriptorMap reference) target.occurrence)
      fuelLeft left leftKey := by
    rw [← readerEq] at leftTrace
    exact leftTrace
  have rightTrace' : LocalizedRuleMajorSortTrace reference.certified .rule4a
      (reference.certified.molecularReader
        (LocalizedRuleMajorReference.descriptorMap reference) target.occurrence)
      fuelRight right rightKey := by
    rw [← readerEq] at rightTrace
    exact rightTrace
  exact retainedMolecularContextTrees_rule4a_compare
    (LocalizedRuleMajorReference.descriptorMap reference)
    (fun occurrence value observed =>
      LocalizedRuleMajorReference.descriptorMap_tetrahedral reference occurrence value observed)
    singleBonded target unit targetUnit left right leftTrace' rightTrace'
    leftChild rightChild leftWidth rightWidth leftHeight rightHeight

/-- One valid generated child has a stage-4a key whose addressing and representation are the
retained ones. Existence is the adequate-budget trace, not a molecule-wide descriptor. -/
theorem exists_retainedGeneratedContextTree_rankCanonical
    (reference : LocalizedRuleMajorReference.Input)
    (singleBonded : reference.certified.moleculeGraph.SimpleBonded)
    (target : reference.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel reference))
    (unit : DetectedOccurrence reference.certified.moleculeGraph)
    (targetUnit : reference.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursor : reference.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel reference))
    (rootChild : cursor ∈ reference.certified.executableLocalizedRerootChildren target)
    (valid : reference.certified.LocalizedRerootCursorValid cursor) :
    ∃ (tree : LocalizedCumulativeDecoratedTree reference.certified
        (LocalizedRuleMajorReference.carrierFuel reference))
      (key : reference.certified.LocalizedRerootCumulativeRule45Key),
      tree.source = cursor ∧
        reference.certified.buildRuleMajorCumulativeWithReadExec? .rule4a
          (reference.certified.localizedDependencyLabel target.occurrence
            (reference.certified.localizedDependencyView
              (LocalizedRuleMajorReference.referenceState reference) target.occurrence))
          (2 * (LocalizedRuleMajorReference.carrierFuel reference + 1)) cursor = some key ∧
        Dense (toOfficialSourceTree tree).declarativeAddressing ∧
        KeySorted
          (ordinaryKeyWithObservations (ruleMajorTreeGraph tree)
            (retainedContextNodeObservation reference.certified.moleculeGraph
              (ruleMajorTreeGraph tree) unit)
            (retainedRankEvidence reference.certified.moleculeGraph
              (LocalizedRuleMajorReference.descriptorMap reference) unit
              (ruleMajorTreeGraph tree))
            (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height)
          (toOfficialSourceTree tree).declarativeAddressing ∧
        Represents4a (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
          (observedRule4aComponent (ruleMajorTreeGraph tree)
            (retainedContextNodeObservation reference.certified.moleculeGraph
              (ruleMajorTreeGraph tree) unit)
            (retainedRankEvidence reference.certified.moleculeGraph
              (LocalizedRuleMajorReference.descriptorMap reference) unit
              (ruleMajorTreeGraph tree))
            (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
            (ruleMajorTreeGraph tree).root) key := by
  obtain ⟨tree, key, source, built, trace⟩ := exists_ruleMajorTrace_at_twice reference.certified
    .rule4a
    (reference.certified.localizedDependencyLabel target.occurrence
      (reference.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState reference) target.occurrence))
    cursor valid
  refine ⟨tree, key, source, ?_, ?_⟩
  · rw [reference.certified.buildRuleMajorCumulativeWithReadExec_eq]
    exact built
  · exact retainedGeneratedContextTree_rankCanonical reference singleBonded target unit targetUnit
      tree trace (by simpa only [source] using rootChild)

end

end TetraStereo.OneCenter.RetainedRule4aCanonicalBridge

assert_kernel_only TetraStereo.OneCenter.RetainedRule4aCanonicalBridge.retainedContext_nil4a
assert_kernel_only TetraStereo.OneCenter.RetainedRule4aCanonicalBridge.retainedContextTree_terminal_bridge4a
assert_kernel_only TetraStereo.OneCenter.RetainedRule4aCanonicalBridge.retainedContextTree_node_bridge4a
assert_kernel_only TetraStereo.OneCenter.RetainedRule4aCanonicalBridge.retainedContextTree_keySorted_rankEvidence
assert_kernel_only TetraStereo.OneCenter.RetainedRule4aCanonicalBridge.retainedContextTree_rankCanonical
assert_kernel_only TetraStereo.OneCenter.RetainedRule4aCanonicalBridge.retainedContextTrees_rule4a_compare
assert_kernel_only TetraStereo.OneCenter.RetainedRule4aCanonicalBridge.retainedDecoratedObservation_eq_arm
assert_kernel_only TetraStereo.OneCenter.RetainedRule4aCanonicalBridge.retainedMolecularContextTree_rankCanonical
assert_kernel_only TetraStereo.OneCenter.RetainedRule4aCanonicalBridge.retainedGeneratedContextTree_rankCanonical
assert_kernel_only TetraStereo.OneCenter.RetainedRule4aCanonicalBridge.retainedMolecularContextTrees_rule4a_compare
assert_kernel_only TetraStereo.OneCenter.RetainedRule4aCanonicalBridge.retainedGeneratedContextTrees_rule4a_compare
assert_kernel_only TetraStereo.OneCenter.RetainedRule4aCanonicalBridge.exists_retainedGeneratedContextTree_rankCanonical
