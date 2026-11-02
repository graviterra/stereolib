import TetraStereo.OneCenter.LocalizedActualCanonicalConstitutionalRefinement
import TetraStereo.OneCenter.LocalizedTerminalTwinAuxiliaryRefusal
import TetraStereo.OneCenter.DeclarativeCIPMultiReferenceProblem
import TetraStereo.OneCenter.DeclarativeCIPFinalTetrahedralOutcome
import TetraStereo.OneCenter.LocalizedPhysicalCalibratedRootReader
import TetraStereo.OneCenter.LocalizedRigidFinalDeclarativeDescriptor
import TetraStereo.OneCenter.DeclarativeCIPSingletonOutcome
import TetraStereo.OneCenter.DeclarativeCIPTerminalReading
import TetraStereo.OneCenter.LocalizedTerminalEndpointObservationAbsorption
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-!
# Declarative refusal at a physical terminal-twin center

This module derives the absence of a complete declarative ranking directly from terminal physical
branches.  It does not read a runtime descriptor value and it does not assume a desired tie.
-/

namespace TetraStereo.OneCenter

open DeclarativeCIP
open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.TerminalTwinAuxiliaryRefusal
open LocalizedUniversalReference

noncomputable section
open scoped Classical

/-- A realized decorated tree whose source has no executable children is its one-node tree. -/
theorem localizedCumulativeTree_eq_root_of_executableChildren_empty
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (read : input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel)
    (tree : LocalizedCumulativeDecoratedTree input fuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (terminal : input.executableLocalizedRerootChildren? tree.source = some []) :
    tree = localizedRootTree input tree.source (read tree.source) [] := by
  cases realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealizes =>
      have hchildren : input.localizedRerootChildren? cursor = some [] := by
        rw [input.localizedRerootChildren?_eq_some_executable]
        simpa [executableLocalizedRerootChildren?_eq_some] using terminal
      have hchildrenEq : children = [] := by
        rw [hchildren] at childrenComputed
        exact Option.some.inj childrenComputed.symm
      have hsorted : sortedChildren = [] := by
        have hp : sortedChildren.map (fun child => child.source) = [] := by
          rw [hchildrenEq] at sourcePerm
          exact List.Perm.eq_nil sourcePerm
        cases sortedChildren with
        | nil => rfl
        | cons head tail => simp at hp
      subst hchildrenEq
      subst hsorted
      rfl

/-- If the actual source cursor has no executable children, the faithful original-root arm is
literally its one-node decorated tree. -/
theorem OriginalRootArm.tree_eq_root_of_executableChildren_empty
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter) (index : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
    (arm : input.OriginalRootArm center index stage read)
    (terminal : input.executableLocalizedRerootChildren?
      (input.localizedLigandRootCursor center index) = some []) :
    arm.tree = localizedRootTree input (input.localizedLigandRootCursor center index)
      (read (input.localizedLigandRootCursor center index)) [] := by
  have h := localizedCumulativeTree_eq_root_of_executableChildren_empty input read
    arm.tree arm.realizes (by simpa [arm.source] using terminal)
  simpa [arm.source] using h

/-- A terminal physical ligand has no actual children in its original-root cursor. -/
theorem localizedLigandRootCursor_children_empty_of_terminal
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter)
    (index : Fin 4) (leaf : input.Atom)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (neighbors : input.moleculeGraph.neighborFinset leaf = {center.1})
    (ligandEq : input.canonicalLigandAtom center index = leaf) :
    input.executableLocalizedRerootChildren?
      (input.localizedLigandRootCursor center index) = some [] := by
  let child := input.localizedLigandRootCursor center index
  let parent : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) :=
    { occurrence := input.localizedAtomRootOccurrence
        (input.certified.input.molecule.atomCount + 1) center.1
      previous? := none }
  have nodeEq : child.occurrence.1.node = OfficialCIPNode.rootFromEdge center.1 leaf := by
    rw [show child = input.localizedLigandRootCursor center index from rfl,
      localizedLigandRootCursor_node, ← ligandEq,
      input.localizedLigandRootNode_eq_rootFromEdge]
  have incoming : child.previous? = some parent.occurrence := by
    simp [child, parent, localizedLigandRootCursor_previous]
  have addr : child.occurrence.1.address = parent.occurrence.1.address ++
      [input.localizedLigandRootSlot center index] := by
    simp [child, parent, localizedLigandRootCursor_address]
  have actual : input.ActualPhysicalAtomAtNode child.occurrence.1.node leaf := by
    simp only [ActualPhysicalAtomAtNode, nodeEq, OfficialCIPNode.rootFromEdge]
    simp
  have parentObserved : child.occurrence.1.node.parent? = some center.1 := by
    rw [nodeEq]
    rfl
  have nonduplicate : child.occurrence.1.node.isDuplicateLeaf = false := by
    rw [nodeEq]
    rfl
  have adjLeaf : input.moleculeGraph.Adj leaf center.1 := by
    apply (MoleculeGraph.mem_neighborFinset input.moleculeGraph leaf center.1).mp
    rw [neighbors]
    simp
  have adj : input.moleculeGraph.Adj center.1 leaf :=
    (input.moleculeGraph.adj_symm).2 adjLeaf
  have bond : input.moleculeGraph.bond leaf center.1 = 1 := by
    rw [input.moleculeGraph.bond_symm]
    exact singleBonded center.1 leaf adj
  exact physicalLeaf_terminal input parent child leaf center.1 incoming
    (input.localizedLigandRootSlot center index) addr actual parentObserved neighbors bond
    nonduplicate

/-- Any faithful original-root arm over a terminal ligand therefore has no child tree. -/
theorem OriginalRootArm.tree_eq_root_of_terminal
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter)
    (index : Fin 4) (leaf : input.Atom) (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
    (arm : input.OriginalRootArm center index stage read)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (neighbors : input.moleculeGraph.neighborFinset leaf = {center.1})
    (ligandEq : input.canonicalLigandAtom center index = leaf) :
    arm.tree = localizedRootTree input (input.localizedLigandRootCursor center index)
      (read (input.localizedLigandRootCursor center index)) [] := by
  exact OriginalRootArm.tree_eq_root_of_executableChildren_empty input center index stage read arm
    (localizedLigandRootCursor_children_empty_of_terminal input center index leaf singleBonded
      neighbors ligandEq)

/-- Every node of a terminal original-root arm graph has the empty source address. -/
theorem OriginalRootArm.armGraph_node_address_eq_nil
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter)
    (index : Fin 4) (leaf : input.Atom) (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
    (arm : input.OriginalRootArm center index stage read)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (neighbors : input.moleculeGraph.neighborFinset leaf = {center.1})
    (ligandEq : input.canonicalLigandAtom center index = leaf)
    (node : (OriginalRootArm.armGraph arm).Node) :
    node.1 = [] := by
  have treeEq := OriginalRootArm.tree_eq_root_of_terminal input center index leaf stage read arm
    singleBonded neighbors ligandEq
  rcases node with ⟨address, addressMem⟩
  change address ∈ (LocalizedCumulativeDecoratedTree.toOfficialSourceTree arm.tree).hierarchyAddresses at addressMem
  obtain ⟨sourceTree, sourceLookup⟩ :=
    (LocalizedCumulativeDecoratedTree.toOfficialSourceTree arm.tree).exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses
      address addressMem
  have erasedEq : LocalizedCumulativeDecoratedTree.toOfficialSourceTree arm.tree =
      LocalizedCumulativeDecoratedTree.toOfficialSourceTree
        (localizedRootTree input (input.localizedLigandRootCursor center index)
          (read (input.localizedLigandRootCursor center index)) []) :=
    congrArg LocalizedCumulativeDecoratedTree.toOfficialSourceTree treeEq
  have sourceLookup' :
      (LocalizedCumulativeDecoratedTree.toOfficialSourceTree
        (localizedRootTree input (input.localizedLigandRootCursor center index)
          (read (input.localizedLigandRootCursor center index)) [])).subtreeAt? address =
        some sourceTree := by
    rw [← erasedEq]
    exact sourceLookup
  cases address with
  | nil => rfl
  | cons slot rest =>
      simp [localizedRootTree, LocalizedCumulativeDecoratedTree.toOfficialSourceTree, LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList, OfficialCIPSourceTree.subtreeAt?] at sourceLookup'

/-- The two physical twin leaves occupy distinct positions in the certified canonical frame. -/
theorem terminalTwin_canonicalSlots
    (input : LocalizedUniversalReference.Input)
    (center : input.certified.TetrahedralCenter)
    (twin : ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule ⟨center.1, center.2⟩) :
    ∃ a b : input.certified.Atom,
      TerminalTwinConfigurationGauge.TerminalTwinPair
        input.certified.detectedMultiCenterMolecule ⟨center.1, center.2⟩ a b ∧
      ∃ left right : Fin 4, left ≠ right ∧
        input.certified.canonicalLigandAtom center left = a ∧
        input.certified.canonicalLigandAtom center right = b := by
  obtain ⟨a, b, pair⟩ := twin
  have hna : input.certified.moleculeGraph.neighborFinset a = {center.1} := by
    simpa [CertifiedLocalizedCIPInput.detectedMultiCenter_mol] using pair.neighbor_a
  have hnb : input.certified.moleculeGraph.neighborFinset b = {center.1} := by
    simpa [CertifiedLocalizedCIPInput.detectedMultiCenter_mol] using pair.neighbor_b
  have adjA : input.certified.moleculeGraph.Adj center.1 a := by
    apply (input.certified.moleculeGraph.adj_symm).2
    apply (MoleculeGraph.mem_neighborFinset _ _ _).mp
    rw [hna]
    simp
  have adjB : input.certified.moleculeGraph.Adj center.1 b := by
    apply (input.certified.moleculeGraph.adj_symm).2
    apply (MoleculeGraph.mem_neighborFinset _ _ _).mp
    rw [hnb]
    simp
  let na : input.certified.moleculeGraph.Neighbor center.1 := ⟨a, adjA⟩
  let nb : input.certified.moleculeGraph.Neighbor center.1 := ⟨b, adjB⟩
  obtain ⟨left, hleft⟩ := (input.certified.canonicalLigandNeighbor_bijective center).2 na
  obtain ⟨right, hright⟩ := (input.certified.canonicalLigandNeighbor_bijective center).2 nb
  have leftAtom : input.certified.canonicalLigandAtom center left = a := congrArg Subtype.val hleft
  have rightAtom : input.certified.canonicalLigandAtom center right = b := congrArg Subtype.val hright
  have different : left ≠ right := by
    intro eq
    apply pair.ne
    rw [← leftAtom, ← rightAtom, eq]
  exact ⟨a, b, pair, left, right, different, leftAtom, rightAtom⟩

/-- Choose the actual faithful original-root arms at the two canonical twin positions. -/
theorem terminalTwin_originalRootArms
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (center : input.certified.TetrahedralCenter)
    (twin : ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule ⟨center.1, center.2⟩) :
    ∃ a b : input.certified.Atom,
      TerminalTwinConfigurationGauge.TerminalTwinPair
        input.certified.detectedMultiCenterMolecule ⟨center.1, center.2⟩ a b ∧
      ∃ left right : Fin 4, left ≠ right ∧
        input.certified.canonicalLigandAtom center left = a ∧
        input.certified.canonicalLigandAtom center right = b ∧
        ∃ (armL : input.certified.OriginalRootArm center left .rule4a
          (fun _ => none))
          (armR : input.certified.OriginalRootArm center right .rule4a
            (fun _ => none)),
        (∀ node : OriginalRootArm.armGraph armL |>.Node, node = (OriginalRootArm.armGraph armL).root) ∧
        (∀ node : OriginalRootArm.armGraph armR |>.Node, node = (OriginalRootArm.armGraph armR).root) := by
  obtain ⟨a, b, pair, left, right, different, eqL, eqR⟩ :=
    terminalTwin_canonicalSlots input center twin
  have hna : input.certified.moleculeGraph.neighborFinset a = {center.1} := by
    simpa [CertifiedLocalizedCIPInput.detectedMultiCenter_mol] using pair.neighbor_a
  have hnb : input.certified.moleculeGraph.neighborFinset b = {center.1} := by
    simpa [CertifiedLocalizedCIPInput.detectedMultiCenter_mol] using pair.neighbor_b
  have adjA : input.certified.moleculeGraph.Adj center.1 a := by
    apply (input.certified.moleculeGraph.adj_symm).2
    apply (MoleculeGraph.mem_neighborFinset _ _ _).mp
    rw [hna]
    simp
  have adjB : input.certified.moleculeGraph.Adj center.1 b := by
    apply (input.certified.moleculeGraph.adj_symm).2
    apply (MoleculeGraph.mem_neighborFinset _ _ _).mp
    rw [hnb]
    simp
  let read : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel :=
    fun _ => none
  let armL := Classical.choice (input.certified.exists_originalRootArm center left .rule4a read)
  let armR := Classical.choice (input.certified.exists_originalRootArm center right .rule4a read)
  have treeL := OriginalRootArm.tree_eq_root_of_terminal input.certified center left a .rule4a
    read armL singleBonded hna eqL
  have treeR := OriginalRootArm.tree_eq_root_of_terminal input.certified center right b .rule4a
    read armR singleBonded hnb eqR
  refine ⟨a, b, pair, left, right, different, eqL, eqR, armL, armR, ?_, ?_⟩
  · intro node
    apply Subtype.ext
    exact OriginalRootArm.armGraph_node_address_eq_nil input.certified center left a .rule4a
      read armL singleBonded hna eqL node
  · intro node
    apply Subtype.ext
    exact OriginalRootArm.armGraph_node_address_eq_nil input.certified center right b .rule4a
      read armR singleBonded hnb eqR node

private theorem terminalRootTreeTableMatch (input : CertifiedLocalizedCIPInput)
    {fuel : Nat} (stage : LocalizedCumulativeRule45Stage)
    (cursor : input.LocalizedRerootCursor fuel) (label : Option LocalizedAuxiliaryLabel) :
    LocalizedCumulativeTreeTableMatch stage (localizedRootTree input cursor label [])
      { constitutional := input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true
        descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
        labels := [[([], label)]], rankedLabels := [[([], label)]] } := by
  unfold LocalizedCumulativeTreeTableMatch
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [LocalizedCumulativeDecoratedTree.tables_rule1a,
      LocalizedCumulativeDecoratedTree.table_eq_root_merge]
    simp [localizedRootTree, LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables,
      LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount, SparseAddress.mergePairTable,
      SparseAddress.mergePairs, MoleculeGraph.officialRuleMajorRootKey]
  · rw [LocalizedCumulativeDecoratedTree.tables_rule1b,
      LocalizedCumulativeDecoratedTree.table_eq_root_merge]
    simp [localizedRootTree, LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables,
      LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount, SparseAddress.mergePairTable,
      SparseAddress.mergePairs, MoleculeGraph.officialRuleMajorRootKey]
  · rw [LocalizedCumulativeDecoratedTree.tables_rule2,
      LocalizedCumulativeDecoratedTree.table_eq_root_merge]
    simp [localizedRootTree, LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables,
      LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount, SparseAddress.mergePairTable,
      SparseAddress.mergePairs, MoleculeGraph.officialRuleMajorRootKey]
  · rw [LocalizedCumulativeDecoratedTree.tables_descriptor,
      LocalizedCumulativeDecoratedTree.table_eq_root_merge]
    simp [localizedRootTree, LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables,
      LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount, SparseAddress.mergePairTable,
      SparseAddress.mergePairs]

/-- The first three production columns of a terminal arm are precisely the production root key. -/
private theorem terminalArm_rootColumns
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter)
    (index : Fin 4) (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
    (arm : input.OriginalRootArm center index stage read)
    (treeEq : arm.tree = localizedRootTree input (input.localizedLigandRootCursor center index)
      (read (input.localizedLigandRootCursor center index)) []) :
    arm.key.constitutional.rule1a =
        (input.moleculeGraph.officialRuleMajorRootKey
          (input.localizedLigandRootCursor center index).occurrence.1.node true).rule1a ∧
      arm.key.constitutional.rule1b =
        (input.moleculeGraph.officialRuleMajorRootKey
          (input.localizedLigandRootCursor center index).occurrence.1.node true).rule1b ∧
      arm.key.constitutional.rule2 =
        (input.moleculeGraph.officialRuleMajorRootKey
          (input.localizedLigandRootCursor center index).occurrence.1.node true).rule2 := by
  let cursor := input.localizedLigandRootCursor center index
  let expected : input.LocalizedRerootCumulativeRule45Key :=
    { constitutional := input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true
      descriptor := [[([], localizedCumulativeRule45Priority stage (read cursor))]]
      labels := [[([], read cursor)]], rankedLabels := [[([], read cursor)]] }
  let expectedTree := localizedRootTree input cursor (read cursor) []
  have hmatch := terminalRootTreeTableMatch input stage cursor (read cursor)
  have table1 : (arm.tree.tables stage).rule1a = arm.key.constitutional.rule1a := arm.tableMatch.1
  have table1b : (arm.tree.tables stage).rule1b = arm.key.constitutional.rule1b := arm.tableMatch.2.1
  have table2 : (arm.tree.tables stage).rule2 = arm.key.constitutional.rule2 := arm.tableMatch.2.2.1
  have expected1 : (expectedTree.tables stage).rule1a = expected.constitutional.rule1a := by
    simpa [expectedTree, expected, cursor] using hmatch.1
  have expected1b : (expectedTree.tables stage).rule1b = expected.constitutional.rule1b := by
    simpa [expectedTree, expected, cursor] using hmatch.2.1
  have expected2 : (expectedTree.tables stage).rule2 = expected.constitutional.rule2 := by
    simpa [expectedTree, expected, cursor] using hmatch.2.2.1
  have tree1 : (arm.tree.tables stage).rule1a = (expectedTree.tables stage).rule1a := by rw [treeEq]
  have tree1b : (arm.tree.tables stage).rule1b = (expectedTree.tables stage).rule1b := by rw [treeEq]
  have tree2 : (arm.tree.tables stage).rule2 = (expectedTree.tables stage).rule2 := by rw [treeEq]
  simpa [expected, cursor] using ⟨table1.symm.trans (tree1.trans expected1),
    table1b.symm.trans (tree1b.trans expected1b),
    table2.symm.trans (tree2.trans expected2)⟩

private theorem terminalArms_notHigher
    (input : LocalizedUniversalReference.Input)
    (descriptorMap : DeclarativeCIP.DescriptorMap
      (DeclarativeCIP.DetectedOccurrence input.certified.moleculeGraph))
    (center : input.certified.TetrahedralCenter) (left right : Fin 4)
    (armL : input.certified.OriginalRootArm center left .rule4a (fun _ => none))
    (armR : input.certified.OriginalRootArm center right .rule4a (fun _ => none))
    (compareEq : OfficialRuleMajorKey.compare armL.key.constitutional
      armR.key.constitutional = Ordering.eq)
    (singletonL : ∀ node : OriginalRootArm.armGraph armL |>.Node,
      node = (OriginalRootArm.armGraph armL).root)
    (singletonR : ∀ node : OriginalRootArm.armGraph armR |>.Node,
      node = (OriginalRootArm.armGraph armR).root)
    (outsideL : DeclarativeCIP.occurrenceReading input.certified.moleculeGraph descriptorMap
      (input.certified.topUnit center) (OriginalRootArm.armGraph armL)
      (OriginalRootArm.armGraph armL).root = .outsideInventory)
    (outsideR : DeclarativeCIP.occurrenceReading input.certified.moleculeGraph descriptorMap
      (input.certified.topUnit center) (OriginalRootArm.armGraph armR)
      (OriginalRootArm.armGraph armR).root = .outsideInventory)
    (noMultipleL : ¬ DeclarativeCIP.HasMultipleBond input.certified.moleculeGraph
      ((OriginalRootArm.armGraph armL).label (OriginalRootArm.armGraph armL).root))
    (noMultipleR : ¬ DeclarativeCIP.HasMultipleBond input.certified.moleculeGraph
      ((OriginalRootArm.armGraph armR).label (OriginalRootArm.armGraph armR).root)) :
    ¬ (multiReferenceProblem input.certified.moleculeGraph input.certified.localizedDetectedFrame
      input.certified.geometricOrientation).Higher descriptorMap
        (input.certified.topUnit center) left right := by
  let problem := multiReferenceProblem input.certified.moleculeGraph
    input.certified.localizedDetectedFrame input.certified.geometricOrientation
  let localProblem := input.certified.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem
  let localMap := finalRootDescriptorMap input.certified descriptorMap
  have noConstitutionalHigher :
      ¬ localProblem.ConstitutionalHigher localMap center left right := by
    intro h
    have h' : DeclarativeCIP.Problem.ConstitutionalHigher
        input.certified.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem
        localMap center left right := h
    have cmp := (OriginalRootArm.compare_eq_gt_iff_constitutionalHigher armL armR localMap).mpr h'
    rw [compareEq] at cmp
    cases cmp
  intro higher
  rcases higher with ⟨rule, earlierTie, decisive⟩
  cases rule with
  | rule1aAtomicNumber =>
      apply noConstitutionalHigher
      refine ⟨.rule1aAtomicNumber, ?_, ?_⟩
      · intro previous before
        cases previous <;> simp only [ruleIndex] at before <;> omega
      · exact (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome
          input.certified descriptorMap center .rule1aAtomicNumber left right .gt).mpr decisive
  | rule1bDuplicateNodeProximity =>
      apply noConstitutionalHigher
      refine ⟨.rule1bDuplicateNodeProximity, ?_, ?_⟩
      · intro previous before
        cases previous with
        | rule1aAtomicNumber =>
            exact (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome
              input.certified descriptorMap center .rule1aAtomicNumber left right .eq).mpr
              (earlierTie .rule1aAtomicNumber (by change 0 < 1; omega))
        | rule1bDuplicateNodeProximity => simp [ruleIndex] at before
        | rule2AtomicMass => simp [ruleIndex] at before
      · exact (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome
          input.certified descriptorMap center .rule1bDuplicateNodeProximity left right .gt).mpr
          decisive
  | rule2AtomicMass =>
      apply noConstitutionalHigher
      refine ⟨.rule2AtomicMass, ?_, ?_⟩
      · intro previous before
        cases previous with
        | rule1aAtomicNumber =>
            exact (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome
              input.certified descriptorMap center .rule1aAtomicNumber left right .eq).mpr
              (earlierTie .rule1aAtomicNumber (by change 0 < 2; omega))
        | rule1bDuplicateNodeProximity =>
            exact (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome
              input.certified descriptorMap center .rule1bDuplicateNodeProximity left right .eq).mpr
              (earlierTie .rule1bDuplicateNodeProximity (by change 1 < 2; omega))
        | rule2AtomicMass => simp [ruleIndex] at before
      · exact (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome
          input.certified descriptorMap center .rule2AtomicMass left right .gt).mpr decisive
  | rule3DoubleBondGeometry =>
      have leftAdmissible : problem.admissibleExpansion (input.certified.topUnit center) left
          (OriginalRootArm.armGraph armL) := by
        simpa [problem, input.certified.localizedDetectedFrame_ligand_topUnit] using armL.faithful
      have rightAdmissible : problem.admissibleExpansion (input.certified.topUnit center) right
          (OriginalRootArm.armGraph armR) := by
        simpa [problem, input.certified.localizedDetectedFrame_ligand_topUnit] using armR.faithful
      have judgment := (DeclarativeCIP.ruleOutcome_iff_judgment
        input.certified.moleculeGraph input.certified.localizedDetectedFrame
        input.certified.geometricOrientation descriptorMap .rule3DoubleBondGeometry (by decide) (by decide)
        (input.certified.topUnit center) leftAdmissible rightAdmissible Ordering.gt).mp decisive
      exact (DeclarativeCIP.singleton_later_judgment_not_gt
        input.certified.moleculeGraph descriptorMap (input.certified.topUnit center)
        (OriginalRootArm.armGraph armL) (OriginalRootArm.armGraph armR)
        singletonL singletonR outsideL outsideR noMultipleL noMultipleR
        .rule3DoubleBondGeometry (by decide)) judgment
  | rule4aStereogenicUnitKind =>
      have leftAdmissible : problem.admissibleExpansion (input.certified.topUnit center) left
          (OriginalRootArm.armGraph armL) := by
        simpa [problem, input.certified.localizedDetectedFrame_ligand_topUnit] using armL.faithful
      have rightAdmissible : problem.admissibleExpansion (input.certified.topUnit center) right
          (OriginalRootArm.armGraph armR) := by
        simpa [problem, input.certified.localizedDetectedFrame_ligand_topUnit] using armR.faithful
      have judgment := (DeclarativeCIP.ruleOutcome_iff_judgment input.certified.moleculeGraph
        input.certified.localizedDetectedFrame input.certified.geometricOrientation descriptorMap
        .rule4aStereogenicUnitKind (by decide) (by decide) (input.certified.topUnit center)
        leftAdmissible rightAdmissible Ordering.gt).mp decisive
      exact (DeclarativeCIP.singleton_later_judgment_not_gt input.certified.moleculeGraph
        descriptorMap (input.certified.topUnit center) (OriginalRootArm.armGraph armL)
        (OriginalRootArm.armGraph armR) singletonL singletonR outsideL outsideR
        noMultipleL noMultipleR .rule4aStereogenicUnitKind (by decide)) judgment
  | rule4bLikeUnlikeDescriptorPairs =>
      have leftAdmissible : problem.admissibleExpansion (input.certified.topUnit center) left
          (OriginalRootArm.armGraph armL) := by
        simpa [problem, input.certified.localizedDetectedFrame_ligand_topUnit] using armL.faithful
      have rightAdmissible : problem.admissibleExpansion (input.certified.topUnit center) right
          (OriginalRootArm.armGraph armR) := by
        simpa [problem, input.certified.localizedDetectedFrame_ligand_topUnit] using armR.faithful
      have judgment := (DeclarativeCIP.ruleOutcome_iff_judgment input.certified.moleculeGraph
        input.certified.localizedDetectedFrame input.certified.geometricOrientation descriptorMap
        .rule4bLikeUnlikeDescriptorPairs (by decide) (by decide) (input.certified.topUnit center)
        leftAdmissible rightAdmissible Ordering.gt).mp decisive
      exact (DeclarativeCIP.singleton_later_judgment_not_gt input.certified.moleculeGraph
        descriptorMap (input.certified.topUnit center) (OriginalRootArm.armGraph armL)
        (OriginalRootArm.armGraph armR) singletonL singletonR outsideL outsideR
        noMultipleL noMultipleR .rule4bLikeUnlikeDescriptorPairs (by decide)) judgment
  | rule4cPseudoasymmetricDescriptor =>
      have leftAdmissible : problem.admissibleExpansion (input.certified.topUnit center) left
          (OriginalRootArm.armGraph armL) := by
        simpa [problem, input.certified.localizedDetectedFrame_ligand_topUnit] using armL.faithful
      have rightAdmissible : problem.admissibleExpansion (input.certified.topUnit center) right
          (OriginalRootArm.armGraph armR) := by
        simpa [problem, input.certified.localizedDetectedFrame_ligand_topUnit] using armR.faithful
      have judgment := (DeclarativeCIP.ruleOutcome_iff_judgment input.certified.moleculeGraph
        input.certified.localizedDetectedFrame input.certified.geometricOrientation descriptorMap
        .rule4cPseudoasymmetricDescriptor (by decide) (by decide) (input.certified.topUnit center)
        leftAdmissible rightAdmissible Ordering.gt).mp decisive
      exact (DeclarativeCIP.singleton_later_judgment_not_gt input.certified.moleculeGraph
        descriptorMap (input.certified.topUnit center) (OriginalRootArm.armGraph armL)
        (OriginalRootArm.armGraph armR) singletonL singletonR outsideL outsideR
        noMultipleL noMultipleR .rule4cPseudoasymmetricDescriptor (by decide)) judgment
  | rule5EnantiomorphicDescriptor =>
      have leftAdmissible : problem.admissibleExpansion (input.certified.topUnit center) left
          (OriginalRootArm.armGraph armL) := by
        simpa [problem, input.certified.localizedDetectedFrame_ligand_topUnit] using armL.faithful
      have rightAdmissible : problem.admissibleExpansion (input.certified.topUnit center) right
          (OriginalRootArm.armGraph armR) := by
        simpa [problem, input.certified.localizedDetectedFrame_ligand_topUnit] using armR.faithful
      have judgment := (DeclarativeCIP.ruleOutcome_iff_judgment input.certified.moleculeGraph
        input.certified.localizedDetectedFrame input.certified.geometricOrientation descriptorMap
        .rule5EnantiomorphicDescriptor (by decide) (by decide) (input.certified.topUnit center)
        leftAdmissible rightAdmissible Ordering.gt).mp decisive
      exact (DeclarativeCIP.singleton_later_judgment_not_gt input.certified.moleculeGraph
        descriptorMap (input.certified.topUnit center) (OriginalRootArm.armGraph armL)
        (OriginalRootArm.armGraph armR) singletonL singletonR outsideL outsideR
        noMultipleL noMultipleR .rule5EnantiomorphicDescriptor (by decide)) judgment
  | rule6ReferencePromotion =>
      have leftAdmissible : problem.admissibleExpansion (input.certified.topUnit center) left
          (OriginalRootArm.armGraph armL) := by
        simpa [problem, input.certified.localizedDetectedFrame_ligand_topUnit] using armL.faithful
      have rightAdmissible : problem.admissibleExpansion (input.certified.topUnit center) right
          (OriginalRootArm.armGraph armR) := by
        simpa [problem, input.certified.localizedDetectedFrame_ligand_topUnit] using armR.faithful
      have judgment := decisive (OriginalRootArm.armGraph armL) (OriginalRootArm.armGraph armR)
        leftAdmissible rightAdmissible
      simp [multiReferenceProblem, Problem.OutcomeOnGraphs] at judgment

/-- A physical terminal-twin pair at a final detected center prevents any complete declarative
descriptor judgment, regardless of the auxiliary descriptor map. -/
theorem terminalTwin_top_no_descriptorJudgment
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (_acyclic : input.certified.moleculeGraph.Acyclic)
    (center : input.certified.TetrahedralCenter)
    (twin : ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule ⟨center.1, center.2⟩)
    (descriptorMap : DeclarativeCIP.DescriptorMap
      (DeclarativeCIP.DetectedOccurrence input.certified.moleculeGraph)) :
    ¬ ∃ descriptor, DeclarativeCIP.Problem.DescriptorJudgment
      (multiReferenceProblem input.certified.moleculeGraph input.certified.localizedDetectedFrame
        input.certified.geometricOrientation)
      descriptorMap (input.certified.topUnit center) descriptor := by
  obtain ⟨a, b, pair, left, right, different, eqL, eqR, armL, armR, singletonL, singletonR⟩ :=
    terminalTwin_originalRootArms input singleBonded center twin
  have hna : input.certified.moleculeGraph.neighborFinset a = {center.1} := by
    simpa [CertifiedLocalizedCIPInput.detectedMultiCenter_mol] using pair.neighbor_a
  have hnb : input.certified.moleculeGraph.neighborFinset b = {center.1} := by
    simpa [CertifiedLocalizedCIPInput.detectedMultiCenter_mol] using pair.neighbor_b
  let cursorL := input.certified.localizedLigandRootCursor center left
  let cursorR := input.certified.localizedLigandRootCursor center right
  have cursorL_atom : cursorL.occurrence.1.node = OfficialCIPNode.rootFromEdge center.1 a := by
    change (input.certified.localizedLigandRootCursor center left).occurrence.1.node = _
    rw [input.certified.localizedLigandRootCursor_node,
      input.certified.localizedLigandRootNode_eq_rootFromEdge, eqL]
  have cursorR_atom : cursorR.occurrence.1.node = OfficialCIPNode.rootFromEdge center.1 b := by
    change (input.certified.localizedLigandRootCursor center right).occurrence.1.node = _
    rw [input.certified.localizedLigandRootCursor_node,
      input.certified.localizedLigandRootNode_eq_rootFromEdge, eqR]
  have actualL : input.certified.ActualPhysicalAtomAtNode cursorL.occurrence.1.node a := by
    simp [CertifiedLocalizedCIPInput.ActualPhysicalAtomAtNode, cursorL_atom,
      OfficialCIPNode.rootFromEdge]
  have actualR : input.certified.ActualPhysicalAtomAtNode cursorR.occurrence.1.node b := by
    simp [CertifiedLocalizedCIPInput.ActualPhysicalAtomAtNode, cursorR_atom,
      OfficialCIPNode.rootFromEdge]
  have zEq : input.certified.moleculeGraph.atomZ a = input.certified.moleculeGraph.atomZ b := by
    simpa [CertifiedLocalizedCIPInput.detectedMultiCenter_mol] using pair.z_eq
  have massEq : input.certified.moleculeGraph.atomMass a = input.certified.moleculeGraph.atomMass b := by
    simpa [CertifiedLocalizedCIPInput.detectedMultiCenter_mol] using pair.mass_eq
  have labelEq := TerminalTwinAuxiliaryRefusal.officialNodeAtomLabel_eq_of_actualPhysical_z_mass
    input.certified cursorL.occurrence.1.node cursorR.occurrence.1.node a b actualL actualR zEq massEq
  have distanceEq : cursorL.occurrence.1.node.rule1bRootDistance =
      cursorR.occurrence.1.node.rule1bRootDistance := by
    rw [cursorL_atom, cursorR_atom]
    rfl
  have rootCompare := TerminalEndpointObservation.officialRuleMajorRootKey_compare_eq_of_label_distance
    input.certified cursorL cursorR labelEq distanceEq
  have rootCompareReverse := TerminalEndpointObservation.officialRuleMajorRootKey_compare_eq_of_label_distance
    input.certified cursorR cursorL labelEq.symm distanceEq.symm
  have treeL := OriginalRootArm.tree_eq_root_of_terminal input.certified center left a .rule4a
    (fun _ => none) armL singleBonded hna eqL
  have treeR := OriginalRootArm.tree_eq_root_of_terminal input.certified center right b .rule4a
    (fun _ => none) armR singleBonded hnb eqR
  have columnsL := terminalArm_rootColumns input.certified center left .rule4a
    (fun _ => none) armL treeL
  have columnsR := terminalArm_rootColumns input.certified center right .rule4a
    (fun _ => none) armR treeR
  have compareEq : OfficialRuleMajorKey.compare armL.key.constitutional
      armR.key.constitutional = Ordering.eq := by
    simpa only [OfficialRuleMajorKey.compare, compareLex, Ordering.byKey,
      columnsL.1, columnsR.1, columnsL.2.1, columnsR.2.1, columnsL.2.2, columnsR.2.2]
      using rootCompare
  have compareEqReverse : OfficialRuleMajorKey.compare armR.key.constitutional
      armL.key.constitutional = Ordering.eq := by
    simpa only [OfficialRuleMajorKey.compare, compareLex, Ordering.byKey,
      columnsR.1, columnsL.1, columnsR.2.1, columnsL.2.1, columnsR.2.2, columnsL.2.2]
      using rootCompareReverse
  let graphL := OriginalRootArm.armGraph armL
  let graphR := OriginalRootArm.armGraph armR
  have rootLabelL : graphL.label graphL.root = ⟨some a, .realAtom⟩ := by
    let tree := LocalizedCumulativeDecoratedTree.toOfficialSourceTree armL.tree
    have h := OfficialCIPSourceTree.declarativeLabel_eq_of_subtreeAt?
      tree tree tree.toDeclarativeDigraph.root (by rfl)
    change tree.declarativeLabel tree.toDeclarativeDigraph.root = _
    rw [h, armL.root]
    simp [OfficialCIPNode.toDeclarativeLabel, OfficialCIPNode.rootFromEdge,
      OfficialCIPNodeProvenance.toDeclarative, eqL]
  have rootLabelR : graphR.label graphR.root = ⟨some b, .realAtom⟩ := by
    let tree := LocalizedCumulativeDecoratedTree.toOfficialSourceTree armR.tree
    have h := OfficialCIPSourceTree.declarativeLabel_eq_of_subtreeAt?
      tree tree tree.toDeclarativeDigraph.root (by rfl)
    change tree.declarativeLabel tree.toDeclarativeDigraph.root = _
    rw [h, armR.root]
    simp [OfficialCIPNode.toDeclarativeLabel, OfficialCIPNode.rootFromEdge,
      OfficialCIPNodeProvenance.toDeclarative, eqR]
  have degreeL : (input.certified.moleculeGraph.neighborFinset a).card ≤ 1 := by
    rw [hna]
    simp
  have degreeR : (input.certified.moleculeGraph.neighborFinset b).card ≤ 1 := by
    rw [hnb]
    simp
  have outsideL := DeclarativeCIP.occurrenceReading_root_outsideInventory_of_leaf
    input.certified.moleculeGraph descriptorMap (input.certified.topUnit center) graphL a rootLabelL degreeL
  have outsideR := DeclarativeCIP.occurrenceReading_root_outsideInventory_of_leaf
    input.certified.moleculeGraph descriptorMap (input.certified.topUnit center) graphR b rootLabelR degreeR
  have noMultipleL := DeclarativeCIP.noMultipleBond_of_simpleBonded input.certified.moleculeGraph
    singleBonded (graphL.label graphL.root)
  have noMultipleR := DeclarativeCIP.noMultipleBond_of_simpleBonded input.certified.moleculeGraph
    singleBonded (graphR.label graphR.root)
  have notLeft := terminalArms_notHigher input descriptorMap center left right armL armR compareEq
    singletonL singletonR outsideL outsideR noMultipleL noMultipleR
  have notRight := terminalArms_notHigher input descriptorMap center right left armR armL
    compareEqReverse singletonR singletonL outsideR outsideL noMultipleR noMultipleL
  exact DeclarativeCIP.no_descriptorJudgment_of_unordered_pair
    (multiReferenceProblem input.certified.moleculeGraph input.certified.localizedDetectedFrame
      input.certified.geometricOrientation) descriptorMap (input.certified.topUnit center)
    left right different notLeft notRight

end
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.localizedLigandRootCursor_children_empty_of_terminal
assert_kernel_only TetraStereo.OneCenter.OriginalRootArm.armGraph_node_address_eq_nil
assert_kernel_only TetraStereo.OneCenter.OriginalRootArm.tree_eq_root_of_terminal
assert_kernel_only TetraStereo.OneCenter.localizedCumulativeTree_eq_root_of_executableChildren_empty
assert_kernel_only TetraStereo.OneCenter.OriginalRootArm.tree_eq_root_of_executableChildren_empty
assert_kernel_only TetraStereo.OneCenter.terminalTwin_top_no_descriptorJudgment
