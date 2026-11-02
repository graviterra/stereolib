import TetraStereo.OneCenter.DeclarativeCIPObservedCanonicalOrder
import TetraStereo.OneCenter.LocalizedContextConstitutionalReadback
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Observation-parametric constitutional representation for every actual rule-major trace.
This generalizes the original-root induction without assuming a root center, fresh-root distances,
reference labels, chemical rigidity, or desired comparison results. The contextual physical
observation theorem supplies the observer correspondence in auxiliary contexts. -/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge
open LocalizedCumulativeDecoratedTree CertifiedLocalizedCIPInput
open OfficialSparseCanonicalVectorComparison DeclarativeCIP
noncomputable section
open scoped Classical

theorem observedTree_denseAt_of_lookup
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (node : (ruleMajorTreeGraph tree).Node)
    (dsub : LocalizedCumulativeDecoratedTree input
      carrierFuel)
    (lookup : tree.decoratedSubtreeAt? node.1 = some dsub) :
    DeclarativeCIP.DenseAt (toOfficialSourceTree tree).declarativeAddressing node
      dsub.children.length := by
  have erasedLookup : (toOfficialSourceTree tree).subtreeAt? node.1 =
      some (toOfficialSourceTree dsub) := by
    rw [toOfficialSourceTree_subtreeAt? tree node.1, lookup]
    rfl
  intro slot
  constructor
  · intro present
    obtain ⟨child, addressEq⟩ := present
    have childAddr : child.1 = node.1 ++ [slot] := by
      rw [(toOfficialSourceTree tree).declarativeAddressing_address child,
        (toOfficialSourceTree tree).declarativeAddressing_address node] at addressEq
      exact addressEq
    have childPresent : node.1 ++ [slot] ∈ (toOfficialSourceTree tree).hierarchyAddresses := by
      simpa [childAddr] using child.2
    obtain ⟨childSubtree, childLookup⟩ :=
      (toOfficialSourceTree tree).exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses
        (node.1 ++ [slot]) childPresent
    have childWithin : (toOfficialSourceTree dsub).subtreeAt? [slot] = some childSubtree := by
      rw [(toOfficialSourceTree tree).subtreeAt?_append, erasedLookup] at childLookup
      simpa using childLookup
    have decoratedWithin : (dsub.decoratedSubtreeAt? [slot]).map toOfficialSourceTree =
        some childSubtree := by
      simpa [toOfficialSourceTree_subtreeAt? dsub [slot]] using childWithin
    obtain ⟨dchild, dLookup, _⟩ := Option.map_eq_some_iff.mp decoratedWithin
    rw [decoratedSubtreeAt?] at dLookup
    cases slotLookup : dsub.children[slot]? with
    | none => simp [slotLookup] at dLookup
    | some child =>
        simp [slotLookup, decoratedSubtreeAt?] at dLookup
        exact (List.getElem?_eq_some_iff.1 slotLookup).1
  · intro slotLt
    have childLookup : (toOfficialSourceTree dsub).subtreeAt? [slot] =
        some (toOfficialSourceTree (dsub.children[slot]'slotLt)) := by
      rw [toOfficialSourceTree_subtreeAt? dsub [slot]]
      simp [decoratedSubtreeAt?, List.getElem?_eq_getElem slotLt]
    have fullLookup : (toOfficialSourceTree tree).subtreeAt? (node.1 ++ [slot]) =
        some (toOfficialSourceTree (dsub.children[slot]'slotLt)) := by
      rw [(toOfficialSourceTree tree).subtreeAt?_append, erasedLookup]
      simpa using childLookup
    have occurrence : (node.1 ++ [slot],
        (toOfficialSourceTree (dsub.children[slot]'slotLt)).source) ∈
        (toOfficialSourceTree tree).occurrences :=
      OfficialCIPSourceTree.mem_occurrences_of_subtreeAt?_eq_some (node.1 ++ [slot])
        (toOfficialSourceTree tree) (toOfficialSourceTree (dsub.children[slot]'slotLt))
        fullLookup
    have membership : node.1 ++ [slot] ∈ (toOfficialSourceTree tree).hierarchyAddresses :=
      (toOfficialSourceTree tree).mem_hierarchyAddresses_of_occurrence
        ⟨node.1 ++ [slot], (toOfficialSourceTree (dsub.children[slot]'slotLt)).source⟩ occurrence
    exact ⟨⟨node.1 ++ [slot], membership⟩, by
      simp [(toOfficialSourceTree tree).declarativeAddressing_address
          ⟨node.1 ++ [slot], membership⟩,
        (toOfficialSourceTree tree).declarativeAddressing_address node]⟩

theorem observedTree_nil_observation
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual,
      tree.decoratedSubtreeAt? node.1 = some actual →
        observe rule node = priorityValue rule (armObservation rule actual))
    {W D : Nat} (node : (ruleMajorTreeGraph tree).Node)
    (dsub : LocalizedCumulativeDecoratedTree input
      carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (tableMatch : LocalizedCumulativeTreeTableMatch stage dsub key)
    (realizes : LocalizedCumulativeTreeRealizes input read dsub)
    (lookup : tree.decoratedSubtreeAt? node.1 = some dsub)
    {r : Nat} (hr : r < 3) :
    DeclarativeCIP.nodePathObservationWithObservations (ruleMajorTreeGraph tree) observe W D r node [] =
      OfficialSparseCanonicalVectorComparison.encodedObservation key.constitutional
        (DeclarativeCIP.ruleOfIndex r) [] := by
  rw [DeclarativeCIP.nodePathObservationWithObservations_nil (ruleMajorTreeGraph tree) observe hr]
  unfold OfficialSparseCanonicalVectorComparison.encodedObservation
  have hpresent : SparseSupportAlignment.HasAddress key.constitutional.rule1a [] := by
    have viaTable : SparseSupportAlignment.HasAddress
        (table (fun source => source.atomicNumber) dsub) [] :=
      (hasAddress_atomicNumber_table_iff_subtree realizes []).2 ⟨dsub, rfl⟩
    simpa [← tableMatch.1, tables_rule1a] using viaTable
  rw [if_pos hpresent]
  rw [observations (DeclarativeCIP.ruleOfIndex r) node dsub lookup]
  have colEq : OfficialSparseCanonicalVectorComparison.column key.constitutional
      (DeclarativeCIP.ruleOfIndex r) = table (armObservation (DeclarativeCIP.ruleOfIndex r)) dsub := by
    interval_cases r
    · change key.constitutional.rule1a = table (fun source => source.atomicNumber) dsub
      simpa [tables_rule1a] using tableMatch.1.symm
    · change key.constitutional.rule1b = table (fun source => source.rule1bDistance) dsub
      simpa [tables_rule1b] using tableMatch.2.1.symm
    · change key.constitutional.rule2 = table (fun source => source.isotopeMass) dsub
      simpa [tables_rule2] using tableMatch.2.2.1.symm
  rw [colEq, tableValue_table_eq_observeAt (armObservation (DeclarativeCIP.ruleOfIndex r)) dsub []]
  change ((DeclarativeCIP.priorityValue (DeclarativeCIP.ruleOfIndex r)
      (armObservation (DeclarativeCIP.ruleOfIndex r) dsub) : ℤ) : WithBot ℤ) =
    ((DeclarativeCIP.priorityValue (DeclarativeCIP.ruleOfIndex r)
      (armObservation (DeclarativeCIP.ruleOfIndex r) dsub) : ℤ) : WithBot ℤ)
  rfl

theorem observedTree_terminal_bridge
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual,
      tree.decoratedSubtreeAt? node.1 = some actual →
        observe rule node = priorityValue rule (armObservation rule actual))
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (fullMatch : LocalizedCumulativeTreeFullMatch stage
      (localizedRootTree input cursor (read cursor) [])
      (localizedCumulativeRule45TerminalKey input stage cursor (read cursor)))
    (realizes : LocalizedCumulativeTreeRealizes input read
      (localizedRootTree input cursor (read cursor) []))
    {W D : Nat} (node : (ruleMajorTreeGraph tree).Node)
    (lookup : tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (read cursor) [])) :
    (((DeclarativeCIP.slotList (toOfficialSourceTree tree).declarativeAddressing node
          (localizedRootTree input cursor (read cursor) []).children.length).map
        (DeclarativeCIP.ruleKeyWithObservations (ruleMajorTreeGraph tree) W D observe)).Pairwise
      fun x y => y ≤ x) ∧
      OfficialSparseCanonicalVectorComparison.Represents W D
        (DeclarativeCIP.ruleKeyWithObservations (ruleMajorTreeGraph tree) W D observe node)
        (localizedCumulativeRule45TerminalKey input stage cursor (read cursor)).constitutional := by
  have childrenEq : (localizedRootTree input cursor (read cursor) []).children = [] := by
    unfold localizedRootTree
    rfl
  have slotKeySorted : ((DeclarativeCIP.slotList (toOfficialSourceTree tree).declarativeAddressing
      node (localizedRootTree input cursor (read cursor) []).children.length).map
        (DeclarativeCIP.ruleKeyWithObservations (ruleMajorTreeGraph tree) W D observe)).Pairwise
      fun x y => y ≤ x := by
    simp [DeclarativeCIP.slotList, childrenEq]
  constructor
  · exact slotKeySorted
  · unfold OfficialSparseCanonicalVectorComparison.Represents
    intro r hr path
    cases path with
    | nil =>
        exact observedTree_nil_observation tree observe observations (W := W) (D := D) node
          (localizedRootTree input cursor (read cursor) [])
          (localizedCumulativeRule45TerminalKey input stage cursor (read cursor))
          fullMatch.tableMatch realizes lookup hr
    | cons digit path =>
        change DeclarativeCIP.nodePathObservationWithObservations (ruleMajorTreeGraph tree) observe W D r node
            (digit :: path) =
          OfficialSparseCanonicalVectorComparison.encodedObservation
            (localizedCumulativeRule45TerminalKey input stage cursor (read cursor)).constitutional
            (DeclarativeCIP.ruleOfIndex r) (digit :: path)
        have hdense : DeclarativeCIP.DenseAt (toOfficialSourceTree tree).declarativeAddressing
            node (localizedRootTree input cursor (read cursor) []).children.length :=
          observedTree_denseAt_of_lookup tree node
            (localizedRootTree input cursor (read cursor) []) lookup
        rw [DeclarativeCIP.nodePathObservationWithObservations_cons (ruleMajorTreeGraph tree) observe hr node
          (ranked := DeclarativeCIP.slotList (toOfficialSourceTree tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) []).children.length)
          (DeclarativeCIP.slotList_perm (addressing := (toOfficialSourceTree tree).declarativeAddressing)
            (parent := node)
            (count := (localizedRootTree input cursor (read cursor) []).children.length) hdense)
          slotKeySorted digit path]
        rw [encodedObservation_cons_of_key fullMatch.tableMatch realizes
          (sortedKeys := []) List.Forall₂.nil (DeclarativeCIP.ruleOfIndex r) digit path]
        by_cases hgate : digit < W ∧ path.length < D
        · rw [if_pos hgate]
          simp [childrenEq, DeclarativeCIP.slotList]
        · rw [if_neg hgate]
          simp

/-- Simultaneously recover independent sibling sorting and exact sparse-table representation
at every resolved subtree. The window bounds cover the whole fixed graph; the observer law is
node-local and says nothing about sorting, selected references, or comparison results. -/
theorem observedTree_node_bridge
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual,
      tree.decoratedSubtreeAt? node.1 = some actual →
        observe rule node = priorityValue rule (armObservation rule actual))
    {W D : ℕ} (hW : (ruleMajorTreeGraph tree).width ≤ W) (hD : (ruleMajorTreeGraph tree).height ≤ D)
    {fuel : Nat} (node : (ruleMajorTreeGraph tree).Node)
    (dsub : LocalizedCumulativeDecoratedTree input
      carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (trace : LocalizedRuleMajorSortTrace input stage read fuel dsub key)
    (lookup : tree.decoratedSubtreeAt? node.1 = some dsub) :
    (((DeclarativeCIP.slotList (toOfficialSourceTree tree).declarativeAddressing node dsub.children.length).map
        (DeclarativeCIP.ruleKeyWithObservations (ruleMajorTreeGraph tree) W D observe)).Pairwise
      fun x y => y ≤ x) ∧
      OfficialSparseCanonicalVectorComparison.Represents W D
        (DeclarativeCIP.ruleKeyWithObservations (ruleMajorTreeGraph tree) W D observe node) key.constitutional := by
  induction fuel generalizing dsub key node lookup with
  | zero =>
      cases trace with
      | terminal _fuel cursor _children _childrenComputed _terminalChildren fullMatch realizes =>
          exact observedTree_terminal_bridge tree observe observations cursor fullMatch realizes (W := W) (D := D) node lookup
  | succ fuel ih =>
      have fullMatch := LocalizedRuleMajorSortTrace.fullMatch_of_trace trace
      have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
      rcases LocalizedRuleMajorSortTrace.structure_of_trace trace with
        ⟨cursor, _children, dsubEq, keyEq, _childrenEq, _childrenComputed, _terminalChildren⟩ |
        ⟨cursor, _children, _childKeys, sortedKeys, sortedTrees, dsubEq, keyEq, childrenEq,
          _childrenComputed, _nonempty, _childKeysComputed, _sortedEq, constitutionalDescending, _sortedDescending,
          childrenTraced⟩
      · subst dsub
        subst key
        exact observedTree_terminal_bridge tree observe observations cursor fullMatch realizes (W := W) (D := D) node lookup
      · subst dsub
        subst key
        have hdense : DeclarativeCIP.DenseAt (toOfficialSourceTree tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length :=
          observedTree_denseAt_of_lookup tree node (localizedRootTree input cursor (read cursor) sortedTrees)
            lookup
        have paired := LocalizedRuleMajorSortTraceList.to_forall₂ childrenTraced
        have lengthEq : sortedKeys.length = sortedTrees.length := List.Forall₂.length_eq paired
        have slotKeySorted : ((DeclarativeCIP.slotList (toOfficialSourceTree tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length).map
            (DeclarativeCIP.ruleKeyWithObservations (ruleMajorTreeGraph tree) W D observe)).Pairwise
            fun x y => y ≤ x := by
          rw [List.pairwise_iff_getElem]
          intro i j hi hj hij
          have iLtCount : i < sortedTrees.length := by
            simpa [DeclarativeCIP.slotList] using hi
          have jLtCount : j < sortedTrees.length := by
            simpa [DeclarativeCIP.slotList] using hj
          have iLtSlot : i < (DeclarativeCIP.slotList (toOfficialSourceTree tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length := by
            simpa [DeclarativeCIP.slotList] using iLtCount
          have jLtSlot : j < (DeclarativeCIP.slotList (toOfficialSourceTree tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length := by
            simpa [DeclarativeCIP.slotList] using jLtCount
          obtain ⟨childI, slotI, addrI⟩ := DeclarativeCIP.slotList_getD_of_lt
            (addressing := (toOfficialSourceTree tree).declarativeAddressing) (parent := node)
            (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
            hdense iLtCount
          obtain ⟨childJ, slotJ, addrJ⟩ := DeclarativeCIP.slotList_getD_of_lt
            (addressing := (toOfficialSourceTree tree).declarativeAddressing) (parent := node)
            (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
            hdense jLtCount
          have slotIEq : (DeclarativeCIP.slotList (toOfficialSourceTree tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[i]'iLtSlot =
              childI :=
            Option.some.inj ((List.getElem?_eq_getElem iLtSlot).symm.trans slotI)
          have slotJEq : (DeclarativeCIP.slotList (toOfficialSourceTree tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[j]'jLtSlot =
              childJ :=
            Option.some.inj ((List.getElem?_eq_getElem jLtSlot).symm.trans slotJ)
          have addrIFlat : childI.1 = node.1 ++ [i] := by
            rw [(toOfficialSourceTree tree).declarativeAddressing_address childI,
              (toOfficialSourceTree tree).declarativeAddressing_address node] at addrI
            exact addrI
          have addrJFlat : childJ.1 = node.1 ++ [j] := by
            rw [(toOfficialSourceTree tree).declarativeAddressing_address childJ,
              (toOfficialSourceTree tree).declarativeAddressing_address node] at addrJ
            exact addrJ
          have childLookupAtI : tree.decoratedSubtreeAt? (node.1 ++ [i]) =
              some (sortedTrees[i]'iLtCount) := by
            rw [decoratedSubtreeAt?_append tree node.1 [i], lookup]
            simp [childrenEq, decoratedSubtreeAt?, List.getElem?_eq_getElem iLtCount]
          have childLookupAtJ : tree.decoratedSubtreeAt? (node.1 ++ [j]) =
              some (sortedTrees[j]'jLtCount) := by
            rw [decoratedSubtreeAt?_append tree node.1 [j], lookup]
            simp [childrenEq, decoratedSubtreeAt?, List.getElem?_eq_getElem jLtCount]
          have childLookupAtISorted : tree.decoratedSubtreeAt? childI.1 =
              some (sortedTrees[i]'iLtCount) := by
            rw [addrIFlat]
            exact childLookupAtI
          have childLookupAtJSorted : tree.decoratedSubtreeAt? childJ.1 =
              some (sortedTrees[j]'jLtCount) := by
            rw [addrJFlat]
            exact childLookupAtJ
          have iLtKeys : i < sortedKeys.length := by simpa [lengthEq] using iLtCount
          have jLtKeys : j < sortedKeys.length := by simpa [lengthEq] using jLtCount
          have childTraceI : LocalizedRuleMajorSortTrace input stage read fuel
              (sortedTrees[i]'iLtCount) (sortedKeys[i]'iLtKeys) :=
            List.Forall₂.get (i := i) paired iLtKeys iLtCount
          have childTraceJ : LocalizedRuleMajorSortTrace input stage read fuel
              (sortedTrees[j]'jLtCount) (sortedKeys[j]'jLtKeys) :=
            List.Forall₂.get (i := j) paired jLtKeys jLtCount
          have ihI := ih (dsub := sortedTrees[i]'iLtCount) (key := sortedKeys[i]'iLtKeys)
            (node := childI) (lookup := childLookupAtISorted) childTraceI
          have ihJ := ih (dsub := sortedTrees[j]'jLtCount) (key := sortedKeys[j]'jLtKeys)
            (node := childJ) (lookup := childLookupAtJSorted) childTraceJ
          have ihRepI : OfficialSparseCanonicalVectorComparison.Represents W D
              (DeclarativeCIP.ruleKeyWithObservations (ruleMajorTreeGraph tree) W D observe childI)
              (sortedKeys[i]'iLtKeys).constitutional := ihI.2
          have ihRepJ : OfficialSparseCanonicalVectorComparison.Represents W D
              (DeclarativeCIP.ruleKeyWithObservations (ruleMajorTreeGraph tree) W D observe childJ)
              (sortedKeys[j]'jLtKeys).constitutional := ihJ.2
          have actualNe : OfficialRuleMajorKey.compare (sortedKeys[i]'iLtKeys).constitutional
              (sortedKeys[j]'jLtKeys).constitutional ≠ Ordering.lt := by
            have hne := (List.pairwise_iff_getElem.1 constitutionalDescending) i j
              (by simpa [lengthEq, List.length_map] using iLtCount)
              (by simpa [lengthEq, List.length_map] using jLtCount) hij
            simpa [List.getElem_map] using hne
          have hle : DeclarativeCIP.ruleKeyWithObservations (ruleMajorTreeGraph tree) W D observe childJ ≤
              DeclarativeCIP.ruleKeyWithObservations (ruleMajorTreeGraph tree) W D observe childI :=
            (OfficialSparseCanonicalVectorComparison.compare_ne_lt_iff_rightVector_le
              (leftWellFormed := wellFormedRuleMajorKey_of_tableMatch
                (LocalizedRuleMajorSortTrace.fullMatch_of_trace childTraceI).tableMatch
                (LocalizedRuleMajorSortTrace.realizes_of_trace childTraceI))
              (rightWellFormed := wellFormedRuleMajorKey_of_tableMatch
                (LocalizedRuleMajorSortTrace.fullMatch_of_trace childTraceJ).tableMatch
                (LocalizedRuleMajorSortTrace.realizes_of_trace childTraceJ))
              (leftShaped := DeclarativeCIP.ruleKeyWithObservations_vectorWellShaped (ruleMajorTreeGraph tree) observe W D childI)
              (rightShaped := DeclarativeCIP.ruleKeyWithObservations_vectorWellShaped (ruleMajorTreeGraph tree) observe W D childJ)
              (leftRepresents := ihRepI) (rightRepresents := ihRepJ)).1 actualNe
          simpa [List.getElem_map, slotIEq, slotJEq] using hle
        constructor
        · exact slotKeySorted
        · unfold OfficialSparseCanonicalVectorComparison.Represents
          intro r hr path
          cases path with
          | nil =>
              exact observedTree_nil_observation tree observe observations (W := W) (D := D) node
                (localizedRootTree input cursor (read cursor) sortedTrees)
                (localizedCumulativeRule45StepKey input stage cursor (read cursor) sortedKeys)
                fullMatch.tableMatch realizes lookup hr
          | cons digit path =>
              change DeclarativeCIP.nodePathObservationWithObservations (ruleMajorTreeGraph tree) observe W D r
                  node (digit :: path) =
                OfficialSparseCanonicalVectorComparison.encodedObservation
                  (localizedCumulativeRule45StepKey input stage cursor (read cursor)
                    sortedKeys).constitutional
                  (DeclarativeCIP.ruleOfIndex r) (digit :: path)
              have pairedMatch : List.Forall₂ (fun childKey childTree =>
                  LocalizedCumulativeTreeTableMatch stage childTree childKey ∧
                    LocalizedCumulativeTreeRealizes input read childTree) sortedKeys sortedTrees :=
                List.Forall₂.imp (fun childKey childTree related =>
                  ⟨(LocalizedRuleMajorSortTrace.fullMatch_of_trace related).tableMatch,
                    LocalizedRuleMajorSortTrace.realizes_of_trace related⟩)
                  (LocalizedRuleMajorSortTraceList.to_forall₂ childrenTraced)
              rw [DeclarativeCIP.nodePathObservationWithObservations_cons (ruleMajorTreeGraph tree) observe hr node
                (ranked := DeclarativeCIP.slotList (toOfficialSourceTree tree).declarativeAddressing node
                  (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
                (DeclarativeCIP.slotList_perm (addressing := (toOfficialSourceTree tree).declarativeAddressing)
                  (parent := node)
                  (count := (localizedRootTree input cursor (read cursor)
                    sortedTrees).children.length) hdense) slotKeySorted digit path]
              rw [encodedObservation_cons_of_key fullMatch.tableMatch realizes
                (sortedKeys := sortedKeys) pairedMatch (DeclarativeCIP.ruleOfIndex r) digit path]
              by_cases hdigit : digit < sortedTrees.length
              · have digitLtSlot : digit < (DeclarativeCIP.slotList
                    (toOfficialSourceTree tree).declarativeAddressing node
                    (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length := by
                  simpa [DeclarativeCIP.slotList] using hdigit
                obtain ⟨child, slotSome, childAddr⟩ := DeclarativeCIP.slotList_getD_of_lt
                  (addressing := (toOfficialSourceTree tree).declarativeAddressing) (parent := node)
                  (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
                  hdense hdigit
                have childAddrFlat : child.1 = node.1 ++ [digit] := by
                  rw [(toOfficialSourceTree tree).declarativeAddressing_address child,
                    (toOfficialSourceTree tree).declarativeAddressing_address node] at childAddr
                  exact childAddr
                have childLookupAt : tree.decoratedSubtreeAt? (node.1 ++ [digit]) =
                    some (sortedTrees[digit]'hdigit) := by
                  rw [decoratedSubtreeAt?_append tree node.1 [digit], lookup]
                  simp [childrenEq, decoratedSubtreeAt?, List.getElem?_eq_getElem hdigit]
                have childLookupAtSorted : tree.decoratedSubtreeAt? child.1 =
                    some (sortedTrees[digit]'hdigit) := by
                  rw [childAddrFlat]
                  exact childLookupAt
                have digitLtKeys : digit < sortedKeys.length := by simpa [lengthEq] using hdigit
                have childTrace : LocalizedRuleMajorSortTrace input stage read fuel
                    (sortedTrees[digit]'hdigit) (sortedKeys[digit]'digitLtKeys) :=
                  List.Forall₂.get (i := digit) paired digitLtKeys hdigit
                have ihChild := ih (dsub := sortedTrees[digit]'hdigit)
                  (key := sortedKeys[digit]'digitLtKeys) (node := child)
                  (lookup := childLookupAtSorted) childTrace
                have ihRepChild : OfficialSparseCanonicalVectorComparison.Represents W D
                    (DeclarativeCIP.ruleKeyWithObservations (ruleMajorTreeGraph tree) W D observe child)
                    (sortedKeys[digit]'digitLtKeys).constitutional := ihChild.2
                by_cases hgate : digit < W ∧ path.length < D
                · rw [if_pos hgate]
                  simp [slotSome]
                  rw [List.getElem?_eq_getElem digitLtKeys]
                  simp
                  exact ihRepChild r hr path
                · rw [if_neg hgate]
                  have childObsBot : DeclarativeCIP.nodePathObservationWithObservations (ruleMajorTreeGraph tree) observe W D r child path = ⊥ := by
                    by_contra hne
                    have bound := DeclarativeCIP.depth_add_length_le_of_nodePathObservationWithObservations (ruleMajorTreeGraph tree) observe hr path child hne
                    have childDepth : (ruleMajorTreeGraph tree).depth child =
                        (ruleMajorTreeGraph tree).depth node + 1 :=
                      (ruleMajorTreeGraph tree).child_depth ⟨digit, childAddrFlat⟩
                    have hdigitLtW : digit < W := by
                      have countLeWidth := DeclarativeCIP.count_le_width
                        (addressing := (toOfficialSourceTree tree).declarativeAddressing) (parent := node)
                        (count := (localizedRootTree input cursor (read cursor)
                          sortedTrees).children.length) hdense
                      have countLeWidth' : sortedTrees.length ≤ (ruleMajorTreeGraph tree).width := by
                        simpa using countLeWidth
                      omega
                    have hpathNotLt : ¬ path.length < D := by
                      intro hlt
                      exact hgate ⟨hdigitLtW, hlt⟩
                    have hpathGe : D ≤ path.length := Nat.le_of_not_gt hpathNotLt
                    omega
                  rw [List.getElem?_eq_getElem digitLtKeys]
                  simp
                  rw [(ihRepChild r hr path).symm]
                  exact childObsBot.symm
              · have hdigitGe : sortedTrees.length ≤ digit := Nat.le_of_not_gt hdigit
                have hslotGe : (DeclarativeCIP.slotList
                    (toOfficialSourceTree tree).declarativeAddressing node
                    (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length ≤
                    digit := by
                  simpa [childrenEq, DeclarativeCIP.slotList] using hdigitGe
                have hkeyGe : sortedKeys.length ≤ digit := by
                  omega
                by_cases hgate : digit < W ∧ path.length < D
                · rw [if_pos hgate]
                  rw [List.getElem?_eq_none hslotGe]
                  rw [List.getElem?_eq_none hkeyGe]
                  simp
                · rw [if_neg hgate]
                  rw [List.getElem?_eq_none hkeyGe]
                  simp

theorem observedTree_decoratedSubtree_of_node
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (node : (ruleMajorTreeGraph tree).Node) :
    ∃ dsub : LocalizedCumulativeDecoratedTree input
        carrierFuel,
      tree.decoratedSubtreeAt? node.1 = some dsub ∧
        (toOfficialSourceTree tree).subtreeAt? node.1 = some (toOfficialSourceTree dsub) := by
  obtain ⟨subtree, lookup⟩ :=
    (toOfficialSourceTree tree).exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses
      node.1 node.2
  have erasedLookup : (tree.decoratedSubtreeAt? node.1).map toOfficialSourceTree =
      some subtree :=
    (lookup.symm.trans (toOfficialSourceTree_subtreeAt? tree node.1)).symm
  obtain ⟨dsub, decLookup, dsubEq⟩ := Option.map_eq_some_iff.mp erasedLookup
  exact ⟨dsub, decLookup, by rw [lookup, ← dsubEq]⟩

/-- The independent observer key represents the executed constitutional table at the root of
any actual recursive trace. The premise concerns node observations only. -/
theorem observedTree_root_represents
    {input : CertifiedLocalizedCIPInput} {carrierFuel fuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual,
      tree.decoratedSubtreeAt? node.1 = some actual →
        observe rule node = priorityValue rule (armObservation rule actual))
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input stage read fuel tree key) :
    Represents (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
      (ruleKeyWithObservations (ruleMajorTreeGraph tree) (ruleMajorTreeGraph tree).width
        (ruleMajorTreeGraph tree).height observe (ruleMajorTreeGraph tree).root)
      key.constitutional :=
  (observedTree_node_bridge tree observe observations le_rfl le_rfl
    (ruleMajorTreeGraph tree).root tree key trace (by
      change tree.decoratedSubtreeAt? [] = some tree
      rw [decoratedSubtreeAt?])).2

/-- Actual contextual keys are represented with their observer premise discharged from the
single-bond acyclic molecular graph. No fresh-root condition or rigidity is assumed. -/
theorem contextualTree_root_represents
    {input : CertifiedLocalizedCIPInput} {carrierFuel fuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input stage read fuel tree key) :
    Represents (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
      (contextualRuleKey input.moleculeGraph (ruleMajorTreeGraph tree)
        tree.source.occurrence.1.root (ruleMajorTreeGraph tree).width
        (ruleMajorTreeGraph tree).height (ruleMajorTreeGraph tree).root)
      key.constitutional :=
  observedTree_root_represents tree _
    (contextualTree_nodeObservation singleBonded acyclic tree
      (LocalizedRuleMajorSortTrace.realizes_of_trace trace)) trace


theorem observedTree_canonicalAddressing
    {input : CertifiedLocalizedCIPInput} {carrierFuel fuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual,
      tree.decoratedSubtreeAt? node.1 = some actual →
        observe rule node = priorityValue rule (armObservation rule actual))
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input stage read fuel tree key) :
    DeclarativeCIP.Dense (toOfficialSourceTree tree).declarativeAddressing ∧
      DeclarativeCIP.KeySorted
        (ruleKeyWithObservations (ruleMajorTreeGraph tree) (ruleMajorTreeGraph tree).width
          (ruleMajorTreeGraph tree).height observe)
        (toOfficialSourceTree tree).declarativeAddressing := by
  constructor
  · exact (toOfficialSourceTree tree).declarativeAddressing_dense
  · intro parent first second firstSlot secondSlot addrFirst addrSecond hlt
    obtain ⟨dsub, lookup, _⟩ := observedTree_decoratedSubtree_of_node tree parent
    have hdense : DeclarativeCIP.DenseAt (toOfficialSourceTree tree).declarativeAddressing
        parent dsub.children.length := observedTree_denseAt_of_lookup tree parent dsub lookup
    rcases ruleMajorTrace_of_subtree input stage read trace parent.1 dsub lookup with
      ⟨fuel', key', trace'⟩
    have bridge := observedTree_node_bridge tree observe observations (W := (ruleMajorTreeGraph tree).width) (D := (ruleMajorTreeGraph tree).height)
      (hW := le_rfl) (hD := le_rfl) (node := parent) (dsub := dsub) (key := key')
      trace' lookup
    have slotKeySorted := bridge.1
    have firstLt : firstSlot < dsub.children.length := (hdense firstSlot).1 ⟨first, addrFirst⟩
    have secondLt : secondSlot < dsub.children.length := (hdense secondSlot).1 ⟨second, addrSecond⟩
    have firstSlotLt : firstSlot < (DeclarativeCIP.slotList
        (toOfficialSourceTree tree).declarativeAddressing parent dsub.children.length).length := by
      simpa [DeclarativeCIP.slotList] using firstLt
    have secondSlotLt : secondSlot < (DeclarativeCIP.slotList
        (toOfficialSourceTree tree).declarativeAddressing parent dsub.children.length).length := by
      simpa [DeclarativeCIP.slotList] using secondLt
    obtain ⟨childI, slotI, addrI⟩ := DeclarativeCIP.slotList_getD_of_lt
      (addressing := (toOfficialSourceTree tree).declarativeAddressing) (parent := parent)
      (count := dsub.children.length) hdense firstLt
    obtain ⟨childJ, slotJ, addrJ⟩ := DeclarativeCIP.slotList_getD_of_lt
      (addressing := (toOfficialSourceTree tree).declarativeAddressing) (parent := parent)
      (count := dsub.children.length) hdense secondLt
    have addrIFlat : first.1 = parent.1 ++ [firstSlot] := by
      rw [(toOfficialSourceTree tree).declarativeAddressing_address first,
        (toOfficialSourceTree tree).declarativeAddressing_address parent] at addrFirst
      exact addrFirst
    have addrJFlat : second.1 = parent.1 ++ [secondSlot] := by
      rw [(toOfficialSourceTree tree).declarativeAddressing_address second,
        (toOfficialSourceTree tree).declarativeAddressing_address parent] at addrSecond
      exact addrSecond
    have childIFlat : childI.1 = parent.1 ++ [firstSlot] := by
      rw [(toOfficialSourceTree tree).declarativeAddressing_address childI,
        (toOfficialSourceTree tree).declarativeAddressing_address parent] at addrI
      exact addrI
    have childJFlat : childJ.1 = parent.1 ++ [secondSlot] := by
      rw [(toOfficialSourceTree tree).declarativeAddressing_address childJ,
        (toOfficialSourceTree tree).declarativeAddressing_address parent] at addrJ
      exact addrJ
    have firstEq : first = childI := Subtype.ext (addrIFlat.trans childIFlat.symm)
    have secondEq : second = childJ := Subtype.ext (addrJFlat.trans childJFlat.symm)
    have slotIEq : (DeclarativeCIP.slotList (toOfficialSourceTree tree).declarativeAddressing
        parent dsub.children.length)[firstSlot]'firstSlotLt = childI :=
      Option.some.inj ((List.getElem?_eq_getElem firstSlotLt).symm.trans slotI)
    have slotJEq : (DeclarativeCIP.slotList (toOfficialSourceTree tree).declarativeAddressing
        parent dsub.children.length)[secondSlot]'secondSlotLt = childJ :=
      Option.some.inj ((List.getElem?_eq_getElem secondSlotLt).symm.trans slotJ)
    have firstSlotMapLt : firstSlot < ((DeclarativeCIP.slotList
        (toOfficialSourceTree tree).declarativeAddressing parent dsub.children.length).map
      (DeclarativeCIP.ruleKeyWithObservations (ruleMajorTreeGraph tree) (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height observe)).length := by
      simpa using firstSlotLt
    have secondSlotMapLt : secondSlot < ((DeclarativeCIP.slotList
        (toOfficialSourceTree tree).declarativeAddressing parent dsub.children.length).map
      (DeclarativeCIP.ruleKeyWithObservations (ruleMajorTreeGraph tree) (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height observe)).length := by
      simpa using secondSlotLt
    have hle : DeclarativeCIP.ruleKeyWithObservations (ruleMajorTreeGraph tree) (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height observe childJ ≤
        DeclarativeCIP.ruleKeyWithObservations (ruleMajorTreeGraph tree) (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height observe childI := by
      have hpair := (List.pairwise_iff_getElem.1 slotKeySorted) firstSlot secondSlot
        firstSlotMapLt secondSlotMapLt hlt
      simpa [List.getElem_map, slotIEq, slotJEq] using hpair
    simpa [firstEq, secondEq] using hle
end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.observedTree_denseAt_of_lookup
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.observedTree_nil_observation
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.observedTree_terminal_bridge
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.observedTree_node_bridge
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.observedTree_root_represents
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextualTree_root_represents
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.observedTree_canonicalAddressing
