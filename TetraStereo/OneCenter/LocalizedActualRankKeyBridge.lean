import TetraStereo.OneCenter.LocalizedActualRule4aNodeReadback
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000






















namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.OriginalRootArm
open OfficialSparseCanonicalVectorComparison
open DeclarativeCIP

noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
  {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
    Option LocalizedAuxiliaryLabel}

/-- The readback hypotheses of the bridge, relative to a descriptor map and ranked unit. -/
structure ArmReadback (arm : input.OriginalRootArm center index .rule4a read)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) : Prop where
  label : ∀ (node : (armGraph arm).Node)
    (actual : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1)),
    arm.tree.decoratedSubtreeAt? node.1 = some actual →
      actual.label =
        (occurrenceReading input.moleculeGraph descriptorMap unit (armGraph arm) node).toLocalizedLabel
  tetrahedral : ∀ node : (armGraph arm).Node,
    (occurrenceReading input.moleculeGraph descriptorMap unit (armGraph arm) node).IsTetrahedral
  available : ∀ node : (armGraph arm).Node,
    occurrenceReading input.moleculeGraph descriptorMap unit (armGraph arm) node ≠ .unavailable
  rule4aOnly : Rule4aOnly (armGraph arm)
    (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))

/-- Terminal case: a root-only decorated tree matched by the terminal key. -/
theorem arm_terminal_bridge4a (arm : input.OriginalRootArm center index .rule4a read)
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : ArmReadback arm descriptorMap unit)
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (fullMatch : LocalizedCumulativeTreeFullMatch .rule4a
      (localizedRootTree input cursor (read cursor) [])
      (localizedCumulativeRule45TerminalKey input .rule4a cursor (read cursor)))
    (realizes : LocalizedCumulativeTreeRealizes input read
      (localizedRootTree input cursor (read cursor) []))
    {W D : ℕ} (node : (armGraph arm).Node)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (read cursor) [])) :
    (((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
          (localizedRootTree input cursor (read cursor) []).children.length).map
        (pairKey input.moleculeGraph (armGraph arm)
          (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm)) W D)).Pairwise
      fun x y => y ≤ x) ∧
      Represents4a W D (rule4aComponent input.moleculeGraph (armGraph arm)
        (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm)) W D node)
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
        exact stereoNodePathObservation_nil_eq_encoded4a descriptorMap unit (armGraph arm) W D node
          fullMatch.tableMatch realizes (hyp.label node _ lookup) (hyp.tetrahedral node)
          (hyp.available node)
    | cons digit path =>
        have rhs : encoded4a (localizedCumulativeRule45TerminalKey input .rule4a cursor (read cursor))
            (digit :: path) = ⊥ := by
          rw [encoded4a_cons_of_key fullMatch.tableMatch realizes pairedNil digit path]; rfl
        have constBot : nodePathObservation input.moleculeGraph (armGraph arm) W D 0 node
            (digit :: path) = ⊥ := by
          have h := (arm_terminal_bridge arm cursor fullMatch realizes (W := W) (D := D) node lookup).2
          have h' := h 0 (by omega) (digit :: path)
          unfold nodePathObservation
          rw [h', encodedObservation_cons_of_key fullMatch.tableMatch realizes pairedNil
            (ruleOfIndex 0) digit path]
          rfl
        rw [rhs]
        exact (stereoNodePathObservation_eq_bot_iff input.moleculeGraph (armGraph arm) _ _ W D
          (digit :: path) node).2 constBot

/-- **Recursive Rule-4a bridge.** -/
theorem arm_node_bridge4a (arm : input.OriginalRootArm center index .rule4a read)
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : ArmReadback arm descriptorMap unit)
    {W D : ℕ} (hW : (armGraph arm).width ≤ W) (hD : (armGraph arm).height ≤ D)
    {fuel : Nat} (node : (armGraph arm).Node)
    (dsub : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
    (key : input.LocalizedRerootCumulativeRule45Key)
    (trace : LocalizedActualRecursiveSortTrace input .rule4a read fuel dsub key)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 = some dsub) :
    (((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node dsub.children.length).map
        (pairKey input.moleculeGraph (armGraph arm)
          (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm)) W D)).Pairwise
      fun x y => y ≤ x) ∧
      Represents4a W D (rule4aComponent input.moleculeGraph (armGraph arm)
        (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm)) W D node) key := by
  induction fuel generalizing dsub key node lookup with
  | zero =>
      cases trace with
      | terminal _fuel cursor _children _childrenComputed _terminalChildren fullMatch realizes =>
          exact arm_terminal_bridge4a arm hyp cursor fullMatch realizes node lookup
  | succ fuel ih =>
      have fullMatch := LocalizedActualRecursiveSortTrace.fullMatch_of_trace trace
      have realizes := LocalizedActualRecursiveSortTrace.realizes_of_trace trace
      rcases LocalizedActualRecursiveSortTrace.structure_of_trace trace with
        ⟨cursor, _children, dsubEq, keyEq, _childrenEq, _childrenComputed, _terminalChildren⟩ |
        ⟨cursor, _children, _childKeys, sortedKeys, sortedTrees, dsubEq, keyEq, childrenEq,
          _childrenComputed, _nonempty, _childKeysComputed, sortedEq, _constitutionalDescending,
          childrenTraced⟩
      · subst dsub; subst key
        exact arm_terminal_bridge4a arm hyp cursor fullMatch realizes node lookup
      · subst dsub; subst key
        have hdense : DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length :=
          denseAt_of_lookup arm node (localizedRootTree input cursor (read cursor) sortedTrees) lookup
        have paired := LocalizedActualRecursiveSortTraceList.to_forall₂ childrenTraced
        have lengthEq : sortedKeys.length = sortedTrees.length := List.Forall₂.length_eq paired
        have pairedMatch : List.Forall₂ (fun childKey childTree =>
            LocalizedCumulativeTreeTableMatch .rule4a childTree childKey ∧
              LocalizedCumulativeTreeRealizes input read childTree) sortedKeys sortedTrees :=
          List.Forall₂.imp (fun childKey childTree related =>
            ⟨(LocalizedActualRecursiveSortTrace.fullMatch_of_trace related).tableMatch,
              LocalizedActualRecursiveSortTrace.realizes_of_trace related⟩) paired
        have descending : sortedKeys.Pairwise fun left right =>
            input.compareLocalizedRerootCumulativeRule45Keys left right ≠ Ordering.lt := by
          rw [sortedEq]
          exact input.sortLocalizedRerootCumulativeRule45Keys_descending _
        have countEq : (localizedRootTree input cursor (read cursor) sortedTrees).children.length =
            sortedTrees.length := by rw [childrenEq]
        have slotLength : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length =
            sortedTrees.length := by simp [slotList, countEq]
        -- the child at slot `i`
        have childAt : ∀ i (hi : i < sortedTrees.length), ∃ child : (armGraph arm).Node,
            (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[i]? =
                some child ∧
              child.1 = node.1 ++ [i] ∧
                arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) := by
          intro i hi
          obtain ⟨child, slotSome, addr⟩ := slotList_getD_of_lt (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := node)
            (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
            hdense (by rw [countEq]; exact hi)
          have addrFlat : child.1 = node.1 ++ [i] := by
            rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address,
              (toOfficialSourceTree arm.tree).declarativeAddressing_address] at addr
            exact addr
          refine ⟨child, slotSome, addrFlat, ?_⟩
          rw [addrFlat, decoratedSubtreeAt?_append arm.tree node.1 [i], lookup]
          simp [childrenEq, decoratedSubtreeAt?, List.getElem?_eq_getElem hi]
        have traceAt : ∀ i (hi : i < sortedTrees.length),
            LocalizedActualRecursiveSortTrace input .rule4a read fuel (sortedTrees[i]'hi)
              (sortedKeys[i]'(by omega)) :=
          fun i hi => List.Forall₂.get (i := i) paired (by omega) hi
        have ihAt : ∀ i (hi : i < sortedTrees.length) (child : (armGraph arm).Node),
            arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
              Represents4a W D (rule4aComponent input.moleculeGraph (armGraph arm) (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm)) W D child)
                (sortedKeys[i]'(by omega)) :=
          fun i hi child hl => (ih child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega)) (traceAt i hi) hl).2
        have constAt : ∀ i (hi : i < sortedTrees.length) (child : (armGraph arm).Node),
            arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
              Represents W D (ruleKey input.moleculeGraph (armGraph arm) W D child)
                (sortedKeys[i]'(by omega)).constitutional :=
          fun i hi child hl =>
            (arm_node_bridge arm hW hD child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega))
              (traceAt i hi) hl).2
        have slotSorted : ((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).map
              (pairKey input.moleculeGraph (armGraph arm) (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm)) W D)).Pairwise fun x y => y ≤ x := by
          rw [List.pairwise_iff_getElem]
          intro i j hi hj hij
          rw [List.length_map, slotLength] at hi hj
          obtain ⟨childI, slotI, _, lookupI⟩ := childAt i hi
          obtain ⟨childJ, slotJ, _, lookupJ⟩ := childAt j hj
          have hne : input.compareLocalizedRerootCumulativeRule45Keys (sortedKeys[i]'(by omega))
              (sortedKeys[j]'(by omega)) ≠ Ordering.lt :=
            (List.pairwise_iff_getElem.1 descending) i j (by omega) (by omega) hij
          have hle := pairKey_le_of_compare_ne_lt (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
            (LocalizedActualRecursiveSortTrace.fullMatch_of_trace (traceAt i hi)).tableMatch
            (LocalizedActualRecursiveSortTrace.fullMatch_of_trace (traceAt j hj)).tableMatch
            (LocalizedActualRecursiveSortTrace.realizes_of_trace (traceAt i hi))
            (LocalizedActualRecursiveSortTrace.realizes_of_trace (traceAt j hj))
            (constAt i hi childI lookupI) (constAt j hj childJ lookupJ)
            (ihAt i hi childI lookupI) (ihAt j hj childJ lookupJ) hne
          have getI : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[i]'(by
                rw [slotLength]; exact hi) = childI :=
            Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotI)
          have getJ : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[j]'(by
                rw [slotLength]; exact hj) = childJ :=
            Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotJ)
          simpa [List.getElem_map, getI, getJ] using hle
        refine ⟨slotSorted, ?_⟩
        intro path
        cases path with
        | nil =>
            exact stereoNodePathObservation_nil_eq_encoded4a descriptorMap unit (armGraph arm) W D node
              fullMatch.tableMatch realizes (hyp.label node _ lookup) (hyp.tetrahedral node)
              (hyp.available node)
        | cons digit path =>
            have slotSortedOrd : ((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
                (localizedRootTree input cursor (read cursor) sortedTrees).children.length).map
                  (ordinaryKey input.moleculeGraph (armGraph arm) (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm)) W D)).Pairwise fun x y => y ≤ x := by
              rw [List.pairwise_map] at slotSorted ⊢
              exact slotSorted.imp fun h =>
                (ordinaryKey_le_iff_pairKey input.moleculeGraph (armGraph arm) (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm)) hyp.rule4aOnly W D _ _).2 h
            change stereoNodePathObservation input.moleculeGraph (armGraph arm) (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm)) W D
                .rule4aStereogenicUnitKind node (digit :: path) = encoded4a _ (digit :: path)
            rw [stereoNodePathObservation_cons input.moleculeGraph (armGraph arm) (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm)) W D _ node
              (slotList_perm (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := node)
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
                apply (stereoNodePathObservation_eq_bot_iff input.moleculeGraph (armGraph arm) (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm)) _ W D
                  path child).2
                by_contra hne
                have bound := depth_add_length_le_of_nodePathObservation input.moleculeGraph (armGraph arm)
                  (W := W) (D := D) (by omega : (0 : ℕ) < 3) path child hne
                have childDepth : (armGraph arm).depth child = (armGraph arm).depth node + 1 :=
                  (armGraph arm).child_depth ⟨digit, childAddr⟩
                have hdigitLtW : digit < W := by
                  have countLe : sortedTrees.length ≤ (armGraph arm).width := by
                    have := count_le_width
                      (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing)
                      (parent := node)
                      (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
                      hdense
                    rw [countEq] at this
                    exact this
                  omega
                have hpath : ¬ path.length < D := fun h => hgate ⟨hdigitLtW, h⟩
                omega
            · have slotNone : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
                  (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[digit]? =
                    none := by
                rw [List.getElem?_eq_none_iff, slotLength]; omega
              have keysNone : sortedKeys[digit]? = none := by
                rw [List.getElem?_eq_none_iff]; omega
              rw [slotNone, keysNone]
              split <;> rfl

/-! ## The arm's addressing is ordinary-canonical for the rank evidence -/

/-- **Prefix-2 canonical membership of the actual Rule-4a stage addressing.** -/
theorem arm_keySorted_rankEvidence (arm : input.OriginalRootArm center index .rule4a read)
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : ArmReadback arm descriptorMap unit) :
    KeySorted (ordinaryKey input.moleculeGraph (armGraph arm)
        (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
        (armGraph arm).width (armGraph arm).height)
      (toOfficialSourceTree arm.tree).declarativeAddressing := by
  intro parent first second firstSlot secondSlot addrFirst addrSecond hlt
  obtain ⟨dsub, lookup, _⟩ := decoratedSubtree_of_node arm parent
  have hdense : DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing parent
      dsub.children.length := denseAt_of_lookup arm parent dsub lookup
  rcases trace_of_subtree input .rule4a read arm.trace parent.1 dsub lookup with ⟨fuel', key', trace'⟩
  have bridge := arm_node_bridge4a arm hyp (W := (armGraph arm).width) (D := (armGraph arm).height)
    le_rfl le_rfl parent dsub key' trace' lookup
  have slotSorted := bridge.1
  have firstLt : firstSlot < dsub.children.length := (hdense firstSlot).1 ⟨first, addrFirst⟩
  have secondLt : secondSlot < dsub.children.length := (hdense secondSlot).1 ⟨second, addrSecond⟩
  obtain ⟨childI, slotI, addrI⟩ := slotList_getD_of_lt
    (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := parent)
    (count := dsub.children.length) hdense firstLt
  obtain ⟨childJ, slotJ, addrJ⟩ := slotList_getD_of_lt
    (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := parent)
    (count := dsub.children.length) hdense secondLt
  have firstEq : first = childI :=
    Subtype.ext (by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address] at addrFirst addrI
      exact addrFirst.trans addrI.symm)
  have secondEq : second = childJ :=
    Subtype.ext (by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address] at addrSecond addrJ
      exact addrSecond.trans addrJ.symm)
  have slotLength : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing parent
      dsub.children.length).length = dsub.children.length := by simp [slotList]
  have getI : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing parent
      dsub.children.length)[firstSlot]'(by rw [slotLength]; exact firstLt) = childI :=
    Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotI)
  have getJ : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing parent
      dsub.children.length)[secondSlot]'(by rw [slotLength]; exact secondLt) = childJ :=
    Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotJ)
  have hpair := (List.pairwise_iff_getElem.1 slotSorted) firstSlot secondSlot
    (by rw [List.length_map, slotLength]; exact firstLt)
    (by rw [List.length_map, slotLength]; exact secondLt) hlt
  simp only [List.getElem_map, getI, getJ] at hpair
  rw [firstEq, secondEq]
  exact (ordinaryKey_le_iff_pairKey input.moleculeGraph (armGraph arm) _ hyp.rule4aOnly _ _ _ _).2 hpair

theorem arm_ordinaryCanonicalAddressing_rankEvidence
    (arm : input.OriginalRootArm center index .rule4a read)
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : ArmReadback arm descriptorMap unit) :
    OrdinaryCanonicalAddressing input.moleculeGraph
      (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
      (toOfficialSourceTree arm.tree).declarativeAddressing :=
  ⟨(toOfficialSourceTree arm.tree).declarativeAddressing_dense, arm_keySorted_rankEvidence arm hyp⟩

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.arm_terminal_bridge4a
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.arm_node_bridge4a
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.arm_keySorted_rankEvidence
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.arm_ordinaryCanonicalAddressing_rankEvidence
