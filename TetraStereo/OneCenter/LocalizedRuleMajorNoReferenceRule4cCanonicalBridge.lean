import TetraStereo.OneCenter.LocalizedRuleMajorRule4cCanonicalBridge
import TetraStereo.OneCenter.LocalizedRuleMajorNoReferenceRule4cTableBridge
import TetraStereo.OneCenter.DeclarativeCIPRule4cKeyProjection
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! # Actual no-reference Rule-4c canonical bridge

This is the recursive representation of the builder's genuine empty-uppercase-reference stage.
The second runtime column is still compared with the molecular pseudoasymmetric value, so both
lowercase `r` and `s` labels remain observable. -/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open OfficialSparseCanonicalVectorComparison
open DeclarativeCIP
open Rule4cObservationBridge
open SparsePhysicalFirstDifference SparseSupportAlignment

noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-- Node-local readback required for the no-reference actual 4c induction. -/
structure RuleMajorTreeReadbackNoReference4c
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) : Prop where
  label : ∀ (node : (ruleMajorTreeGraph tree).Node)
    (actual : LocalizedCumulativeDecoratedTree input carrierFuel),
    tree.decoratedSubtreeAt? node.1 = some actual →
      actual.label = (occurrenceReading input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph tree) node).toLocalizedLabel
  tetrahedral : ∀ node : (ruleMajorTreeGraph tree).Node,
    (occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node).IsTetrahedral
  available : ∀ node : (ruleMajorTreeGraph tree).Node,
    occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node ≠ .unavailable
  rule4acOnly : Rule4acOnly (ruleMajorTreeGraph tree)
    (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))

private theorem noReference4c_cons_support
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key} {stage : LocalizedCumulativeRule45Stage}
    (tableMatch : LocalizedCumulativeTreeTableMatch stage tree key)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {sortedKeys : List input.LocalizedRerootCumulativeRule45Key}
    (paired : List.Forall₂ (fun childKey childTree =>
        LocalizedCumulativeTreeTableMatch stage childTree childKey ∧
          LocalizedCumulativeTreeRealizes input read childTree) sortedKeys tree.children)
    (digit : Nat) (path : List Nat) :
    (HasAddress key.constitutional.rule1a (digit :: path) →
      ∃ (hd : digit < tree.children.length) (hk : digit < sortedKeys.length),
        HasAddress (sortedKeys[digit]'hk).constitutional.rule1a path ∧
        LocalizedCumulativeTreeTableMatch stage (tree.children[digit]'hd) (sortedKeys[digit]'hk) ∧
        LocalizedCumulativeTreeRealizes input read (tree.children[digit]'hd) ∧
        tree.decoratedSubtreeAt? (digit :: path) =
          (tree.children[digit]'hd).decoratedSubtreeAt? path) ∧
    (¬ HasAddress key.constitutional.rule1a (digit :: path) →
      ∀ (hk : digit < sortedKeys.length),
        ¬ HasAddress (sortedKeys[digit]'hk).constitutional.rule1a path) := by
  have keysLength : sortedKeys.length = tree.children.length := List.Forall₂.length_eq paired
  constructor
  · intro hpresent
    have guardTable : HasAddress (table (fun node => node.atomicNumber) tree) (digit :: path) := by
      simpa [← tableMatch.1, tables_rule1a] using hpresent
    obtain ⟨subtree, subtreeLookup⟩ :=
      (hasAddress_atomicNumber_table_iff_subtree realizes (digit :: path)).1 guardTable
    obtain ⟨child, subtree', childGet, childPath⟩ :=
      (decoratedSubtreeAt?_cons_some tree digit path).1 ⟨subtree, subtreeLookup⟩
    have hd : digit < tree.children.length := (List.getElem?_eq_some_iff.1 childGet).1
    have hk : digit < sortedKeys.length := by omega
    have childIs : child = tree.children[digit]'hd :=
      (Option.some.inj ((List.getElem?_eq_getElem hd).symm.trans childGet)).symm
    have slotPaired := List.Forall₂.get (i := digit) paired hk hd
    simp only [List.get_eq_getElem] at slotPaired
    have childSubtree : (tree.children[digit]'hd).decoratedSubtreeAt? path = some subtree' := by
      simpa [childIs] using childPath
    refine ⟨hd, hk, ?_, slotPaired.1, slotPaired.2, ?_⟩
    · have viaChildTable : HasAddress
          (table (fun node => node.atomicNumber) (tree.children[digit]'hd)) path :=
        (hasAddress_atomicNumber_table_iff_subtree slotPaired.2 path).2 ⟨subtree', childSubtree⟩
      have h1 := slotPaired.1.1
      rw [tables_rule1a] at h1
      rw [← h1]
      exact viaChildTable
    · rw [decoratedSubtreeAt?, childGet, childIs]
  · intro hpresent hk childGuard
    apply hpresent
    have hd : digit < tree.children.length := by omega
    have slotPaired := List.Forall₂.get (i := digit) paired hk hd
    simp only [List.get_eq_getElem] at slotPaired
    have viaChildTable : HasAddress
        (table (fun node => node.atomicNumber) (tree.children[digit]'hd)) path := by
      have h1 := slotPaired.1.1
      rw [tables_rule1a] at h1
      rw [h1]
      exact childGuard
    obtain ⟨subtree', childPath⟩ :=
      (hasAddress_atomicNumber_table_iff_subtree slotPaired.2 path).1 viaChildTable
    have lookup : ∃ subtree, tree.decoratedSubtreeAt? (digit :: path) = some subtree :=
      (decoratedSubtreeAt?_cons_some tree digit path).2
        ⟨_, subtree', List.getElem?_eq_getElem hd, childPath⟩
    have viaTable := (hasAddress_atomicNumber_table_iff_subtree realizes (digit :: path)).2 lookup
    simpa [← tableMatch.1, tables_rule1a] using viaTable

theorem encoded4a_cons_of_key_anyStage
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key} {stage : LocalizedCumulativeRule45Stage}
    (tableMatch : LocalizedCumulativeTreeTableMatch stage tree key)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {sortedKeys : List input.LocalizedRerootCumulativeRule45Key}
    (paired : List.Forall₂ (fun childKey childTree =>
        LocalizedCumulativeTreeTableMatch stage childTree childKey ∧
          LocalizedCumulativeTreeRealizes input read childTree) sortedKeys tree.children)
    (digit : Nat) (path : List Nat) :
    encoded4a key (digit :: path) =
      ((sortedKeys[digit]?).map fun childKey => encoded4a childKey path).getD ⊥ := by
  obtain ⟨present, absent⟩ := noReference4c_cons_support tableMatch realizes paired digit path
  unfold encoded4a
  by_cases hpresent : HasAddress key.constitutional.rule1a (digit :: path)
  · obtain ⟨_hd, hk, childGuard, childMatch, _childRealizes, lookupEq⟩ := present hpresent
    rw [if_pos hpresent, List.getElem?_eq_getElem hk]
    simp only [Option.map_some, Option.getD_some]
    rw [if_pos childGuard]
    have valueEq : tableValue (scalar4a key) (digit :: path) =
        tableValue (scalar4a (sortedKeys[digit]'hk)) path := by
      rw [scalar4a_eq_table_anyStage tableMatch, scalar4a_eq_table_anyStage childMatch,
        tableValue_table_eq_observeAt, tableValue_table_eq_observeAt]
      unfold observeAt
      rw [lookupEq]
    rw [valueEq]
  · rw [if_neg hpresent]
    cases keysGet : sortedKeys[digit]? with
    | none => rfl
    | some childKey =>
        simp only [Option.map_some, Option.getD_some]
        have hk : digit < sortedKeys.length := (List.getElem?_eq_some_iff.1 keysGet).1
        have childKeyIs : childKey = sortedKeys[digit]'hk :=
          Option.some.inj (keysGet.symm.trans (List.getElem?_eq_getElem hk))
        rw [childKeyIs, if_neg (absent hpresent hk)]

theorem stereoNodePathObservation_nil_eq_encoded4a_noReference
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (graph : RootedDigraph input.Atom)
    (W D : Nat) (node : graph.Node)
    (tableMatch : LocalizedCumulativeTreeTableMatch .rule4cNoReference tree key)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (hlabel : tree.label =
      (occurrenceReading input.moleculeGraph descriptorMap unit graph node).toLocalizedLabel)
    (htetra : (occurrenceReading input.moleculeGraph descriptorMap unit graph node).IsTetrahedral)
    (havail : occurrenceReading input.moleculeGraph descriptorMap unit graph node ≠ .unavailable) :
    stereoNodePathObservation input.moleculeGraph graph
        (noReferenceEvidence4c input.moleculeGraph descriptorMap unit graph) W D
        .rule4aStereogenicUnitKind node [] = encoded4a key [] := by
  rw [stereoNodePathObservation_nil]
  rw [← encoded4a_rule4bTableView_anyStage .R tableMatch []]
  change stereoLabel graph (readingEvidence input.moleculeGraph descriptorMap unit graph .senior)
      .rule4aStereogenicUnitKind node =
    encoded4a (rule4bTableView .R tree key) []
  have old := @stereoNodePathObservation_nil_eq_encoded4a_rule4b input carrierFuel read tree
    (rule4bTableView .R tree key) .R descriptorMap unit graph W D node
    (rule4bTableView_matches_anyStage .R tableMatch) realizes hlabel htetra havail .senior
  rw [stereoNodePathObservation_nil] at old
  exact old

section NoReferenceRuleMajorRootArm

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
  {index : Fin 4}
  {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
    Option LocalizedAuxiliaryLabel}
variable (arm : input.RuleMajorRootArm center index .rule4cNoReference read)
  {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
  {unit : DetectedOccurrence input.moleculeGraph}

/-- Terminal no-reference keys read the actual Rule-4a and molecular Rule-4c columns. -/
theorem ruleMajorRootArm_terminal_bridge_noReference4c
    (hyp : RuleMajorTreeReadbackNoReference4c arm.tree descriptorMap unit)
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (fullMatch : LocalizedCumulativeTreeFullMatch .rule4cNoReference
      (localizedRootTree input cursor (read cursor) [])
      (localizedCumulativeRule45TerminalKey input .rule4cNoReference cursor (read cursor)))
    (realizes : LocalizedCumulativeTreeRealizes input read
      (localizedRootTree input cursor (read cursor) []))
    {W D : Nat} (node : (ruleMajorArmGraph arm).Node)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (read cursor) [])) :
    (((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
          (localizedRootTree input cursor (read cursor) []).children.length).map
        (rule4acKey input.moleculeGraph (ruleMajorArmGraph arm)
          (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm)) W D)).Pairwise
      fun x y => y ≤ x) ∧
      Represents4a W D (rule4aComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm)) W D node)
        (localizedCumulativeRule45TerminalKey input .rule4cNoReference cursor (read cursor)) ∧
      Represents4c W D (rule4cComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm)) W D node)
        (localizedCumulativeRule45TerminalKey input .rule4cNoReference cursor (read cursor)) := by
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
  have constBot : ∀ digit path,
      nodePathObservation input.moleculeGraph (ruleMajorArmGraph arm) W D 0 node
        (digit :: path) = ⊥ := by
    intro digit path
    have hconst := (ruleMajorRootArm_terminal_bridge arm cursor fullMatch realizes
      (W := W) (D := D) node lookup).2
    have hroot := hconst 0 (by omega) (digit :: path)
    unfold nodePathObservation
    rw [hroot, encodedObservation_cons_of_key fullMatch.tableMatch realizes pairedNilBasic
      (ruleOfIndex 0) digit path]
    rfl
  refine ⟨by rw [childrenEq]; simp [slotList], ?_, ?_⟩
  · intro path
    cases path with
    | nil =>
        exact stereoNodePathObservation_nil_eq_encoded4a_noReference descriptorMap unit
          (ruleMajorArmGraph arm) W D node fullMatch.tableMatch realizes
          (hyp.label node _ lookup) (hyp.tetrahedral node) (hyp.available node)
    | cons digit path =>
        have rhs : encoded4a
            (localizedCumulativeRule45TerminalKey input .rule4cNoReference cursor (read cursor))
            (digit :: path) = ⊥ := by
          rw [encoded4a_cons_of_key_anyStage fullMatch.tableMatch realizes pairedNilBasic digit path]
          rfl
        rw [rhs]
        exact (stereoNodePathObservation_eq_bot_iff input.moleculeGraph (ruleMajorArmGraph arm)
          (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm))
          .rule4aStereogenicUnitKind W D (digit :: path) node).2 (constBot digit path)
  · intro path
    cases path with
    | nil =>
        rw [encodedPseudo4c_nil fullMatch.tableMatch fullMatch.labelMatch realizes]
        exact stereoNodePathObservation_nil_eq_pseudoValueOfLabel_noReference descriptorMap unit
          (ruleMajorArmGraph arm) W D node (localizedRootTree input cursor (read cursor) [])
          (hyp.label node _ lookup) (hyp.available node)
    | cons digit path =>
        have rhs : encodedPseudo4c
            (localizedCumulativeRule45TerminalKey input .rule4cNoReference cursor (read cursor))
            (digit :: path) = ⊥ := by
          rw [encodedPseudo4c_cons_of_key fullMatch.tableMatch fullMatch.labelMatch realizes
            pairedNil digit path]
          rfl
        rw [rhs]
        exact (stereoNodePathObservation_eq_bot_iff input.moleculeGraph (ruleMajorArmGraph arm)
          (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm))
          .rule4cPseudoasymmetricDescriptor W D (digit :: path) node).2 (constBot digit path)

/-- Recursive representation of the genuine empty-reference stage.  Its two actual comparison
columns establish descending `(constitution, Rule 4a, Rule 4c)` keys at every node. -/
theorem ruleMajorRootArm_node_bridge_noReference4c
    (hyp : RuleMajorTreeReadbackNoReference4c arm.tree descriptorMap unit)
    {W D : Nat} (hW : (ruleMajorArmGraph arm).width ≤ W)
    (hD : (ruleMajorArmGraph arm).height ≤ D)
    {fuel : Nat} (node : (ruleMajorArmGraph arm).Node)
    (dsub : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
    (key : input.LocalizedRerootCumulativeRule45Key)
    (trace : LocalizedRuleMajorSortTrace input .rule4cNoReference read fuel dsub key)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 = some dsub) :
    (((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node dsub.children.length).map
        (rule4acKey input.moleculeGraph (ruleMajorArmGraph arm)
          (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm)) W D)).Pairwise
      fun x y => y ≤ x) ∧
      Represents4a W D (rule4aComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm)) W D node) key ∧
      Represents4c W D (rule4cComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm)) W D node) key := by
  induction fuel generalizing dsub key node lookup with
  | zero =>
      cases trace with
      | terminal _fuel cursor _children _childrenComputed _terminalChildren fullMatch realizes =>
          exact ruleMajorRootArm_terminal_bridge_noReference4c arm hyp cursor fullMatch realizes node lookup
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
        exact ruleMajorRootArm_terminal_bridge_noReference4c arm hyp cursor fullMatch realizes node lookup
      · subst dsub
        subst key
        set E := noReferenceEvidence4c input.moleculeGraph descriptorMap unit
          (ruleMajorArmGraph arm) with hE
        have hdense : DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length :=
          ruleMajorRootArm_denseAt_of_lookup arm node
            (localizedRootTree input cursor (read cursor) sortedTrees) lookup
        have paired := LocalizedRuleMajorSortTraceList.to_forall₂ childrenTraced
        have lengthEq : sortedKeys.length = sortedTrees.length := List.Forall₂.length_eq paired
        have pairedMatch : List.Forall₂ (fun childKey childTree =>
            LocalizedCumulativeTreeTableMatch .rule4cNoReference childTree childKey ∧
              LocalizedCumulativeTreeRealizes input read childTree ∧
                LocalizedCumulativeTreeLabelMatch childTree childKey) sortedKeys sortedTrees :=
          List.Forall₂.imp (fun childKey childTree related =>
            ⟨(LocalizedRuleMajorSortTrace.fullMatch_of_trace related).tableMatch,
              LocalizedRuleMajorSortTrace.realizes_of_trace related,
              (LocalizedRuleMajorSortTrace.fullMatch_of_trace related).labelMatch⟩) paired
        have pairedMatchBasic : List.Forall₂ (fun childKey childTree =>
            LocalizedCumulativeTreeTableMatch .rule4cNoReference childTree childKey ∧
              LocalizedCumulativeTreeRealizes input read childTree) sortedKeys sortedTrees :=
          List.Forall₂.imp (fun _ _ related => ⟨related.1, related.2.1⟩) pairedMatch
        have descending : input.RuleMajorCumulativeKeysDescending 2 sortedKeys := by
          have widthEq : CertifiedLocalizedCIPInput.ruleMajorStageWidth .rule4cNoReference = 2 := rfl
          rw [← widthEq]
          exact sortedDescending
        have countEq : (localizedRootTree input cursor (read cursor) sortedTrees).children.length =
            sortedTrees.length := by rw [childrenEq]
        have slotLength : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length =
            sortedTrees.length := by simp [slotList, countEq]
        have childAt : ∀ i (hi : i < sortedTrees.length), ∃ child : (ruleMajorArmGraph arm).Node,
            (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[i]? =
                some child ∧ child.1 = node.1 ++ [i] ∧
                arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) := by
          intro i hi
          obtain ⟨child, slotSome, addr⟩ := slotList_getD_of_lt
            (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := node)
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
            LocalizedRuleMajorSortTrace input .rule4cNoReference read fuel (sortedTrees[i]'hi)
              (sortedKeys[i]'(by omega)) :=
          fun i hi => List.Forall₂.get (i := i) paired (by omega) hi
        have ihAt : ∀ i (hi : i < sortedTrees.length) (child : (ruleMajorArmGraph arm).Node),
            arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
              Represents4a W D (rule4aComponent input.moleculeGraph (ruleMajorArmGraph arm)
                  E W D child) (sortedKeys[i]'(by omega)) ∧
              Represents4c W D (rule4cComponent input.moleculeGraph (ruleMajorArmGraph arm)
                  E W D child) (sortedKeys[i]'(by omega)) := by
          intro i hi child hl
          exact (ih child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega)) (traceAt i hi) hl).2
        have constAt : ∀ i (hi : i < sortedTrees.length) (child : (ruleMajorArmGraph arm).Node),
            arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
              Represents W D (ruleKey input.moleculeGraph (ruleMajorArmGraph arm) W D child)
                (sortedKeys[i]'(by omega)).constitutional := by
          intro i hi child hl
          exact (ruleMajorRootArm_node_bridge arm hW hD child (sortedTrees[i]'hi)
            (sortedKeys[i]'(by omega)) (traceAt i hi) hl).2
        have slotSorted : ((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).map
              (rule4acKey input.moleculeGraph (ruleMajorArmGraph arm) E W D)).Pairwise
              (fun x y => y ≤ x) := by
          rw [List.pairwise_iff_getElem]
          intro i j hi hj hij
          rw [List.length_map, slotLength] at hi hj
          obtain ⟨childI, slotI, _, lookupI⟩ := childAt i hi
          obtain ⟨childJ, slotJ, _, lookupJ⟩ := childAt j hj
          have hneWidth : input.compareRuleMajorCumulativeDescriptor 2
              (sortedKeys[i]'(by omega)) (sortedKeys[j]'(by omega)) ≠ Ordering.lt :=
            (List.pairwise_iff_getElem.1 descending) i j (by omega) (by omega) hij
          have hle := Rule4cObservationBridge.rule4acKey_le_of_compare_ne_lt E
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt i hi)).tableMatch
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt j hj)).tableMatch
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt i hi)).labelMatch
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt j hj)).labelMatch
            (LocalizedRuleMajorSortTrace.realizes_of_trace (traceAt i hi))
            (LocalizedRuleMajorSortTrace.realizes_of_trace (traceAt j hj))
            (constAt i hi childI lookupI) (constAt j hj childJ lookupJ)
            (ihAt i hi childI lookupI).1 (ihAt j hj childJ lookupJ).1
            (ihAt i hi childI lookupI).2 (ihAt j hj childJ lookupJ).2 hneWidth
          have getI : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[i]'(by
                rw [slotLength]; exact hi) = childI :=
            Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotI)
          have getJ : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[j]'(by
                rw [slotLength]; exact hj) = childJ :=
            Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotJ)
          simpa [List.getElem_map, getI, getJ] using hle
        have slotSortedOrd : ((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).map
              (ordinaryKey input.moleculeGraph (ruleMajorArmGraph arm) E W D)).Pairwise
              (fun x y => y ≤ x) := by
          rw [List.pairwise_map] at slotSorted ⊢
          exact slotSorted.imp fun h =>
            (ordinaryKey_le_iff_rule4acKey input.moleculeGraph (ruleMajorArmGraph arm) E
              hyp.rule4acOnly W D _ _).2 h
        have hperm := slotList_perm
          (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing)
          (parent := node)
          (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length) hdense
        have consCase : ∀ (rule : StereochemicalRule)
            (enc : input.LocalizedRerootCumulativeRule45Key → List Nat → WithBot StereoLabel)
            (comp : (ruleMajorArmGraph arm).Node → Certificate.CanonicalSphereKey.Key StereoLabel),
            (∀ i (hi : i < sortedTrees.length) (child : (ruleMajorArmGraph arm).Node),
              arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
                ∀ path, Certificate.CanonicalSphereKey.pathObservationOf W D (comp child) path =
                  enc (sortedKeys[i]'(by omega)) path) →
            (∀ child : (ruleMajorArmGraph arm).Node, comp child =
              (ofLex (ordinaryKey input.moleculeGraph (ruleMajorArmGraph arm) E W D child)).2.getD
                (stereoIndex rule) []) →
            (∀ digit path, enc (localizedCumulativeRule45StepKey input .rule4cNoReference cursor
                (read cursor) sortedKeys) (digit :: path) =
              ((sortedKeys[digit]?).map fun childKey => enc childKey path).getD ⊥) →
            ∀ digit path,
              Certificate.CanonicalSphereKey.pathObservationOf W D (comp node) (digit :: path) =
                enc (localizedCumulativeRule45StepKey input .rule4cNoReference cursor
                  (read cursor) sortedKeys) (digit :: path) := by
          intro rule enc comp repAt compEq encCons digit path
          rw [compEq node]
          change stereoNodePathObservation input.moleculeGraph (ruleMajorArmGraph arm) E W D rule node
            (digit :: path) = _
          rw [stereoNodePathObservation_cons input.moleculeGraph (ruleMajorArmGraph arm) E W D rule node
            hperm slotSortedOrd digit path, encCons digit path]
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
              apply (stereoNodePathObservation_eq_bot_iff input.moleculeGraph (ruleMajorArmGraph arm)
                E rule W D path child).2
              by_contra hne
              have bound := depth_add_length_le_of_nodePathObservation input.moleculeGraph
                (ruleMajorArmGraph arm) (W := W) (D := D) (by omega : (0 : Nat) < 3) path child hne
              have childDepth : (ruleMajorArmGraph arm).depth child =
                  (ruleMajorArmGraph arm).depth node + 1 :=
                (ruleMajorArmGraph arm).child_depth ⟨digit, childAddr⟩
              have countLe : sortedTrees.length ≤ (ruleMajorArmGraph arm).width := by
                have := count_le_width
                  (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing)
                  (parent := node)
                  (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
                  hdense
                rw [countEq] at this
                exact this
              have hdigitLtW : digit < W := by omega
              have hpath : ¬ path.length < D := fun h => hgate ⟨hdigitLtW, h⟩
              omega
          · have slotNone : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
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
              exact stereoNodePathObservation_nil_eq_encoded4a_noReference descriptorMap unit
                (ruleMajorArmGraph arm) W D node fullMatch.tableMatch realizes
                (hyp.label node _ lookup) (hyp.tetrahedral node) (hyp.available node)
          | cons digit path =>
              exact consCase .rule4aStereogenicUnitKind encoded4a
                (rule4aComponent input.moleculeGraph (ruleMajorArmGraph arm) E W D)
                (fun i hi child hl => (ihAt i hi child hl).1) (fun _ => rfl)
                (fun digit path => encoded4a_cons_of_key_anyStage fullMatch.tableMatch realizes
                  pairedMatchBasic digit path) digit path
        · intro path
          cases path with
          | nil =>
              rw [encodedPseudo4c_nil fullMatch.tableMatch fullMatch.labelMatch realizes]
              exact stereoNodePathObservation_nil_eq_pseudoValueOfLabel_noReference descriptorMap unit
                (ruleMajorArmGraph arm) W D node
                (localizedRootTree input cursor (read cursor) sortedTrees)
                (hyp.label node _ lookup) (hyp.available node)
          | cons digit path =>
              exact consCase .rule4cPseudoasymmetricDescriptor encodedPseudo4c
                (rule4cComponent input.moleculeGraph (ruleMajorArmGraph arm) E W D)
                (fun i hi child hl => (ihAt i hi child hl).2) (fun _ => rfl)
                (fun digit path => encodedPseudo4c_cons_of_key fullMatch.tableMatch fullMatch.labelMatch
                  realizes pairedMatch digit path) digit path

/-- The actual no-reference addressing is sorted by the independent complete `(4a,4c)` key. -/
theorem ruleMajorRootArm_keySorted_noReference4c
    (hyp : RuleMajorTreeReadbackNoReference4c arm.tree descriptorMap unit) :
    KeySorted (ordinaryKey input.moleculeGraph (ruleMajorArmGraph arm)
        (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm))
        (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height)
      (toOfficialSourceTree arm.tree).declarativeAddressing := by
  intro parent first second firstSlot secondSlot addrFirst addrSecond hlt
  obtain ⟨dsub, lookup, _⟩ := ruleMajorRootArm_decoratedSubtree_of_node arm parent
  have hdense : DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing parent
      dsub.children.length := ruleMajorRootArm_denseAt_of_lookup arm parent dsub lookup
  rcases ruleMajorTrace_of_subtree input .rule4cNoReference read arm.trace parent.1 dsub lookup with
    ⟨fuel', key', trace'⟩
  have bridge := ruleMajorRootArm_node_bridge_noReference4c arm hyp
    (W := (ruleMajorArmGraph arm).width) (D := (ruleMajorArmGraph arm).height)
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
  exact (ordinaryKey_le_iff_rule4acKey input.moleculeGraph (ruleMajorArmGraph arm)
    (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm))
    hyp.rule4acOnly (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height _ _).2 hpair

/-- Ordinary-canonical addressing for the actual empty-reference stage-4c arm. -/
theorem ruleMajorRootArm_ordinaryCanonicalAddressing_noReference4c
    (hyp : RuleMajorTreeReadbackNoReference4c arm.tree descriptorMap unit) :
    OrdinaryCanonicalAddressing input.moleculeGraph
      (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm))
      (toOfficialSourceTree arm.tree).declarativeAddressing :=
  ⟨(toOfficialSourceTree arm.tree).declarativeAddressing_dense,
    ruleMajorRootArm_keySorted_noReference4c arm hyp⟩

/-- Root Rule-4a representation for the no-reference actual stage-4c arm. -/
theorem ruleMajorRootArm_root_represents4a_noReference4c
    (hyp : RuleMajorTreeReadbackNoReference4c arm.tree descriptorMap unit) :
    Represents4a (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
      (rule4aComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm))
        (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height (ruleMajorArmGraph arm).root)
      arm.key :=
  (ruleMajorRootArm_node_bridge_noReference4c arm hyp le_rfl le_rfl
    (ruleMajorArmGraph arm).root arm.tree arm.key arm.trace rfl).2.1

/-- Root Rule-4c representation keeps the independently read pseudoasymmetric label at every
address, including lowercase `r` and `s`. -/
theorem ruleMajorRootArm_root_represents4c_noReference
    (hyp : RuleMajorTreeReadbackNoReference4c arm.tree descriptorMap unit) :
    Represents4c (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
      (rule4cComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (noReferenceEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm))
        (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height (ruleMajorArmGraph arm).root)
      arm.key :=
  (ruleMajorRootArm_node_bridge_noReference4c arm hyp le_rfl le_rfl
    (ruleMajorArmGraph arm).root arm.tree arm.key arm.trace rfl).2.2

end NoReferenceRuleMajorRootArm

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.RuleMajorTreeReadbackNoReference4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.encoded4a_cons_of_key_anyStage
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.stereoNodePathObservation_nil_eq_encoded4a_noReference
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_terminal_bridge_noReference4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_node_bridge_noReference4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_keySorted_noReference4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_ordinaryCanonicalAddressing_noReference4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_root_represents4a_noReference4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_root_represents4c_noReference
