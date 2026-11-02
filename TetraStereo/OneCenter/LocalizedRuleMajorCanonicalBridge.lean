import TetraStereo.OneCenter.LocalizedActualRule4bKeyBridge
import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeTrace
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Canonical addressing for rule-major cumulative keys

The rule-major builder sorts each sibling family by the whole Rule-4a column followed by the
whole Rule-4b column.  This module proves the constitutional and Rule-4b representation bridges
for that builder's own recursive trace.  Unlike the production stage-major bridge, these order
proofs need no side condition saying that constitutionally tied siblings have equal Rule-4a tables:
the comparator already compares the complete Rule-4a column before it reads Rule 4b.
-/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.OriginalRootArm
open OfficialSparseCanonicalVectorComparison
open DeclarativeCIP

noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-- The rooted digraph underlying one decorated rule-major tree. -/
abbrev ruleMajorTreeGraph (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :=
  (toOfficialSourceTree tree).toDeclarativeDigraph

/-- Readback needed for the Rule-4b canonicality induction when sibling sorting is rule-major.
The conditions are node-local; no hypothesis about tied sibling tables or physical descriptors is
required. -/
structure RuleMajorTreeReadback4b
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (ρ : RS) : Prop where
  label : ∀ (node : (ruleMajorTreeGraph tree).Node)
    (actual : LocalizedCumulativeDecoratedTree input carrierFuel),
    tree.decoratedSubtreeAt? node.1 = some actual →
      actual.label =
        (occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node).toLocalizedLabel
  tetrahedral : ∀ node : (ruleMajorTreeGraph tree).Node,
    (occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node).IsTetrahedral
  available : ∀ node : (ruleMajorTreeGraph tree).Node,
    occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node ≠ .unavailable
  rule4abOnly : Rule4abOnly (ruleMajorTreeGraph tree)
    (readingEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) (senseOf ρ))

/-- A non-increasing rule-major comparison of stage-`.rule4b` keys yields the same order on the
independent triple `(constitutional vector, Rule-4a key, Rule-4b key)`.  Unlike the production
stage-major comparator bridge, this requires no separate Rule-4a-table agreement premise. -/
theorem tripleKey_le_of_ruleMajor_compare_ne_lt {graph : RootedDigraph input.Atom}
    (evidence : StereochemicalEvidence graph)
    {carrierFuel : Nat} {treeI treeJ : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyI keyJ : input.LocalizedRerootCumulativeRule45Key}
    {readI readJ : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {ρI ρJ : RS}
    (matchI : LocalizedCumulativeTreeTableMatch (.rule4b ρI) treeI keyI)
    (matchJ : LocalizedCumulativeTreeTableMatch (.rule4b ρJ) treeJ keyJ)
    (realizesI : LocalizedCumulativeTreeRealizes input readI treeI)
    (realizesJ : LocalizedCumulativeTreeRealizes input readJ treeJ)
    {W D : Nat} {childI childJ : graph.Node}
    (repI : Represents W D (ruleKey input.moleculeGraph graph W D childI) keyI.constitutional)
    (repJ : Represents W D (ruleKey input.moleculeGraph graph W D childJ) keyJ.constitutional)
    (rep4aI : Represents4a W D
      (rule4aComponent input.moleculeGraph graph evidence W D childI) keyI)
    (rep4aJ : Represents4a W D
      (rule4aComponent input.moleculeGraph graph evidence W D childJ) keyJ)
    (rep4bI : Represents4b W D
      (rule4bComponent input.moleculeGraph graph evidence W D childI) keyI)
    (rep4bJ : Represents4b W D
      (rule4bComponent input.moleculeGraph graph evidence W D childJ) keyJ)
    (hne : input.compareRuleMajorCumulativeDescriptor 2 keyI keyJ ≠ Ordering.lt) :
    tripleKey input.moleculeGraph graph evidence W D childJ ≤
      tripleKey input.moleculeGraph graph evidence W D childI := by
  have order := compareRuleMajor_eq_then matchI matchJ realizesI realizesJ repI repJ
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ childI)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ childJ)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ childI)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ childJ)
    rep4aI rep4aJ rep4bI rep4bJ
  rw [order] at hne
  exact lex_le_of_then_ne_lt _ _ _ vectorCompare_eq_iff vectorCompare_gt_iff
    stereoKeyCompare_eq_iff stereoKeyCompare_gt_iff
    stereoKeyCompare_eq_iff stereoKeyCompare_gt_iff hne

/-! ## The node observation used by the recursive bridge -/

/-! ## The one declarative graph fixed by the actual rule-major arm -/

/-- The one declarative graph erased from a rule-major root arm's actual decorated tree. -/
abbrev ruleMajorArmGraph {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
    {index : Fin 4} {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.RuleMajorRootArm center index stage read) : DeclarativeCIP.RootedDigraph input.Atom :=
  (toOfficialSourceTree arm.tree).toDeclarativeDigraph

/-- The three constitutional rules on an official node agree with the observations stored at the
decorated subtree resolved by that same ranked address.  This isolates the source-tree fact needed
by the recursive representation proof from the particular sorting trace. -/
def RuleMajorTreeNodeObservation {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.RuleMajorRootArm center index stage read) : Prop :=
  ∀ (rule : DeclarativeCIP.ConstitutionalRule) (node : (ruleMajorArmGraph arm).Node)
    (dsub : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)),
    arm.tree.decoratedSubtreeAt? node.1 = some dsub →
      DeclarativeCIP.nodeObservation input.moleculeGraph (ruleMajorArmGraph arm) rule node =
        DeclarativeCIP.priorityValue rule (armObservation rule dsub)

/-- The rule-major root arm's generated source tree supplies the node observation relation for
every resolved decorated subtree.  The proof uses the generated path's history length only for
Rule 1b, where it identifies stored root distance with hierarchy depth. -/
theorem ruleMajorRootArm_nodeObservation
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.RuleMajorRootArm center index stage read) : RuleMajorTreeNodeObservation arm := by
  intro rule node dsub lookup
  obtain ⟨subtree, subtreeLookup⟩ :=
    (toOfficialSourceTree arm.tree).exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses
      node.1 node.2
  unfold DeclarativeCIP.nodeObservation
  have depthEq : (ruleMajorArmGraph arm).depth node = node.1.length := rfl
  rw [depthEq]
  have labelEq : (ruleMajorArmGraph arm).label node = subtree.source.toDeclarativeLabel :=
    (toOfficialSourceTree arm.tree).declarativeLabel_eq_of_subtreeAt? subtree node subtreeLookup
  rw [labelEq]
  congr 1
  have erasedLookup : (arm.tree.decoratedSubtreeAt? node.1).map toOfficialSourceTree =
      some subtree :=
    (subtreeLookup.symm.trans (toOfficialSourceTree_subtreeAt? arm.tree node.1)).symm
  obtain ⟨actual, decLookup, actualEq⟩ := Option.map_eq_some_iff.mp erasedLookup
  have actualIsDsub : actual = dsub := Option.some.inj (decLookup.symm.trans lookup)
  subst dsub
  have shape : actual = localizedRootTree input actual.source (read actual.source) actual.children :=
    realizes_of_decoratedSubtreeAt? arm.tree arm.realizes node.1 actual decLookup
  have sourceEq : actual.source.occurrence.1.node = subtree.source := by
    simpa [actualEq] using (toOfficialSourceTree_source actual).symm
  have shapeObs : armObservation rule actual = armSourceObservation input rule actual.source := by
    rw [shape]
    cases rule <;> rfl
  rw [shapeObs]
  cases rule with
  | rule1aAtomicNumber =>
      simpa [DeclarativeCIP.ruleValue, armSourceObservation, sourceEq] using
        (MoleculeGraph.officialNodeAtomLabel_first_eq_nodeAtomicNumber
          input.moleculeGraph subtree.source).symm
  | rule1bDuplicateNodeProximity =>
      have historyLength : subtree.source.history.length = node.1.length + 2 :=
        generatedSourceTree_history_length input (toOfficialSourceTree arm.tree) center.1
          (input.canonicalLigandAtom center index) arm.generated arm.root node subtree subtreeLookup
      have graphGenerated : subtree.source.GraphGenerated :=
        generatedSourceTree_source_graphGenerated input (toOfficialSourceTree arm.tree) center.1
          (input.canonicalLigandAtom center index) arm.generated arm.root node subtree subtreeLookup
      have historyLength' : subtree.source.history.length =
          (List.replicate node.1.length 0).length + 2 := by simpa using historyLength
      simpa [DeclarativeCIP.ruleValue, armSourceObservation, sourceEq] using
        (OfficialCIPNode.rule1bRootDistance_eq_independent subtree.source
          (List.replicate node.1.length 0) historyLength' graphGenerated).symm
  | rule2AtomicMass =>
      simpa [DeclarativeCIP.ruleValue, armSourceObservation, sourceEq] using
        (MoleculeGraph.officialNodeAtomLabel_second_eq_nodeAtomicMass
          input.moleculeGraph subtree.source).symm

/-- Density below a node resolved to a decorated subtree. -/
theorem ruleMajorRootArm_denseAt_of_lookup
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.RuleMajorRootArm center index stage read) (node : (ruleMajorArmGraph arm).Node)
    (dsub : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1))
    (lookup : arm.tree.decoratedSubtreeAt? node.1 = some dsub) :
    DeclarativeCIP.DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing node
      dsub.children.length := by
  have erasedLookup : (toOfficialSourceTree arm.tree).subtreeAt? node.1 =
      some (toOfficialSourceTree dsub) := by
    rw [toOfficialSourceTree_subtreeAt? arm.tree node.1, lookup]
    rfl
  intro slot
  constructor
  · intro present
    obtain ⟨child, addressEq⟩ := present
    have childAddr : child.1 = node.1 ++ [slot] := by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address child,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address node] at addressEq
      exact addressEq
    have childPresent : node.1 ++ [slot] ∈ (toOfficialSourceTree arm.tree).hierarchyAddresses := by
      simpa [childAddr] using child.2
    obtain ⟨childSubtree, childLookup⟩ :=
      (toOfficialSourceTree arm.tree).exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses
        (node.1 ++ [slot]) childPresent
    have childWithin : (toOfficialSourceTree dsub).subtreeAt? [slot] = some childSubtree := by
      rw [(toOfficialSourceTree arm.tree).subtreeAt?_append, erasedLookup] at childLookup
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
    have fullLookup : (toOfficialSourceTree arm.tree).subtreeAt? (node.1 ++ [slot]) =
        some (toOfficialSourceTree (dsub.children[slot]'slotLt)) := by
      rw [(toOfficialSourceTree arm.tree).subtreeAt?_append, erasedLookup]
      simpa using childLookup
    have occurrence : (node.1 ++ [slot],
        (toOfficialSourceTree (dsub.children[slot]'slotLt)).source) ∈
        (toOfficialSourceTree arm.tree).occurrences :=
      OfficialCIPSourceTree.mem_occurrences_of_subtreeAt?_eq_some (node.1 ++ [slot])
        (toOfficialSourceTree arm.tree) (toOfficialSourceTree (dsub.children[slot]'slotLt))
        fullLookup
    have membership : node.1 ++ [slot] ∈ (toOfficialSourceTree arm.tree).hierarchyAddresses :=
      (toOfficialSourceTree arm.tree).mem_hierarchyAddresses_of_occurrence
        ⟨node.1 ++ [slot], (toOfficialSourceTree (dsub.children[slot]'slotLt)).source⟩ occurrence
    exact ⟨⟨node.1 ++ [slot], membership⟩, by
      simp [(toOfficialSourceTree arm.tree).declarativeAddressing_address
          ⟨node.1 ++ [slot], membership⟩,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address node]⟩

/-- Empty-path observation for a local key at the graph node resolved to its decorated subtree. -/
theorem ruleMajorRootArm_nil_observation
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.RuleMajorRootArm center index stage read)
    {W D : Nat} (node : (ruleMajorArmGraph arm).Node)
    (dsub : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1))
    (key : input.LocalizedRerootCumulativeRule45Key)
    (tableMatch : LocalizedCumulativeTreeTableMatch stage dsub key)
    (realizes : LocalizedCumulativeTreeRealizes input read dsub)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 = some dsub)
    {r : Nat} (hr : r < 3) :
    DeclarativeCIP.nodePathObservation input.moleculeGraph (ruleMajorArmGraph arm) W D r node [] =
      OfficialSparseCanonicalVectorComparison.encodedObservation key.constitutional
        (DeclarativeCIP.ruleOfIndex r) [] := by
  rw [DeclarativeCIP.nodePathObservation_nil input.moleculeGraph (ruleMajorArmGraph arm) hr]
  unfold OfficialSparseCanonicalVectorComparison.encodedObservation
  have hpresent : SparseSupportAlignment.HasAddress key.constitutional.rule1a [] := by
    have viaTable : SparseSupportAlignment.HasAddress
        (table (fun source => source.atomicNumber) dsub) [] :=
      (hasAddress_atomicNumber_table_iff_subtree realizes []).2 ⟨dsub, rfl⟩
    simpa [← tableMatch.1, tables_rule1a] using viaTable
  rw [if_pos hpresent]
  rw [ruleMajorRootArm_nodeObservation arm (DeclarativeCIP.ruleOfIndex r) node dsub lookup]
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

/-- The terminal case for constitutional representation in the rule-major root arm. -/
theorem ruleMajorRootArm_terminal_bridge
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.RuleMajorRootArm center index stage read)
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (fullMatch : LocalizedCumulativeTreeFullMatch stage
      (localizedRootTree input cursor (read cursor) [])
      (localizedCumulativeRule45TerminalKey input stage cursor (read cursor)))
    (realizes : LocalizedCumulativeTreeRealizes input read
      (localizedRootTree input cursor (read cursor) []))
    {W D : Nat} (node : (ruleMajorArmGraph arm).Node)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (read cursor) [])) :
    (((DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
          (localizedRootTree input cursor (read cursor) []).children.length).map
        (DeclarativeCIP.ruleKey input.moleculeGraph (ruleMajorArmGraph arm) W D)).Pairwise
      fun x y => y ≤ x) ∧
      OfficialSparseCanonicalVectorComparison.Represents W D
        (DeclarativeCIP.ruleKey input.moleculeGraph (ruleMajorArmGraph arm) W D node)
        (localizedCumulativeRule45TerminalKey input stage cursor (read cursor)).constitutional := by
  have childrenEq : (localizedRootTree input cursor (read cursor) []).children = [] := by
    unfold localizedRootTree
    rfl
  have slotKeySorted : ((DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing
      node (localizedRootTree input cursor (read cursor) []).children.length).map
        (DeclarativeCIP.ruleKey input.moleculeGraph (ruleMajorArmGraph arm) W D)).Pairwise
      fun x y => y ≤ x := by
    simp [DeclarativeCIP.slotList, childrenEq]
  constructor
  · exact slotKeySorted
  · unfold OfficialSparseCanonicalVectorComparison.Represents
    intro r hr path
    cases path with
    | nil =>
        exact ruleMajorRootArm_nil_observation arm (W := W) (D := D) node
          (localizedRootTree input cursor (read cursor) [])
          (localizedCumulativeRule45TerminalKey input stage cursor (read cursor))
          fullMatch.tableMatch realizes lookup hr
    | cons digit path =>
        change DeclarativeCIP.nodePathObservation input.moleculeGraph (ruleMajorArmGraph arm) W D r node
            (digit :: path) =
          OfficialSparseCanonicalVectorComparison.encodedObservation
            (localizedCumulativeRule45TerminalKey input stage cursor (read cursor)).constitutional
            (DeclarativeCIP.ruleOfIndex r) (digit :: path)
        have hdense : DeclarativeCIP.DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing
            node (localizedRootTree input cursor (read cursor) []).children.length :=
          ruleMajorRootArm_denseAt_of_lookup arm node
            (localizedRootTree input cursor (read cursor) []) lookup
        rw [DeclarativeCIP.nodePathObservation_cons input.moleculeGraph (ruleMajorArmGraph arm) hr node
          (ranked := DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) []).children.length)
          (DeclarativeCIP.slotList_perm (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing)
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

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorTreeGraph
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.RuleMajorTreeReadback4b
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.tripleKey_le_of_ruleMajor_compare_ne_lt

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open OfficialSparseCanonicalVectorComparison
open DeclarativeCIP


theorem ruleMajorRootArm_node_bridge
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.RuleMajorRootArm center index stage read)
    {W D : ℕ} (hW : (ruleMajorArmGraph arm).width ≤ W) (hD : (ruleMajorArmGraph arm).height ≤ D)
    {fuel : Nat} (node : (ruleMajorArmGraph arm).Node)
    (dsub : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1))
    (key : input.LocalizedRerootCumulativeRule45Key)
    (trace : LocalizedRuleMajorSortTrace input stage read fuel dsub key)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 = some dsub) :
    (((DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node dsub.children.length).map
        (DeclarativeCIP.ruleKey input.moleculeGraph (ruleMajorArmGraph arm) W D)).Pairwise
      fun x y => y ≤ x) ∧
      OfficialSparseCanonicalVectorComparison.Represents W D
        (DeclarativeCIP.ruleKey input.moleculeGraph (ruleMajorArmGraph arm) W D node) key.constitutional := by
  induction fuel generalizing dsub key node lookup with
  | zero =>
      cases trace with
      | terminal _fuel cursor _children _childrenComputed _terminalChildren fullMatch realizes =>
          exact ruleMajorRootArm_terminal_bridge arm cursor fullMatch realizes (W := W) (D := D) node lookup
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
        exact ruleMajorRootArm_terminal_bridge arm cursor fullMatch realizes (W := W) (D := D) node lookup
      · subst dsub
        subst key
        have hdense : DeclarativeCIP.DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length :=
          ruleMajorRootArm_denseAt_of_lookup arm node (localizedRootTree input cursor (read cursor) sortedTrees)
            lookup
        have paired := LocalizedRuleMajorSortTraceList.to_forall₂ childrenTraced
        have lengthEq : sortedKeys.length = sortedTrees.length := List.Forall₂.length_eq paired
        have slotKeySorted : ((DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length).map
            (DeclarativeCIP.ruleKey input.moleculeGraph (ruleMajorArmGraph arm) W D)).Pairwise
            fun x y => y ≤ x := by
          rw [List.pairwise_iff_getElem]
          intro i j hi hj hij
          have iLtCount : i < sortedTrees.length := by
            simpa [DeclarativeCIP.slotList] using hi
          have jLtCount : j < sortedTrees.length := by
            simpa [DeclarativeCIP.slotList] using hj
          have iLtSlot : i < (DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length := by
            simpa [DeclarativeCIP.slotList] using iLtCount
          have jLtSlot : j < (DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length := by
            simpa [DeclarativeCIP.slotList] using jLtCount
          obtain ⟨childI, slotI, addrI⟩ := DeclarativeCIP.slotList_getD_of_lt
            (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := node)
            (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
            hdense iLtCount
          obtain ⟨childJ, slotJ, addrJ⟩ := DeclarativeCIP.slotList_getD_of_lt
            (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := node)
            (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
            hdense jLtCount
          have slotIEq : (DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[i]'iLtSlot =
              childI :=
            Option.some.inj ((List.getElem?_eq_getElem iLtSlot).symm.trans slotI)
          have slotJEq : (DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[j]'jLtSlot =
              childJ :=
            Option.some.inj ((List.getElem?_eq_getElem jLtSlot).symm.trans slotJ)
          have addrIFlat : childI.1 = node.1 ++ [i] := by
            rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address childI,
              (toOfficialSourceTree arm.tree).declarativeAddressing_address node] at addrI
            exact addrI
          have addrJFlat : childJ.1 = node.1 ++ [j] := by
            rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address childJ,
              (toOfficialSourceTree arm.tree).declarativeAddressing_address node] at addrJ
            exact addrJ
          have childLookupAtI : arm.tree.decoratedSubtreeAt? (node.1 ++ [i]) =
              some (sortedTrees[i]'iLtCount) := by
            rw [decoratedSubtreeAt?_append arm.tree node.1 [i], lookup]
            simp [childrenEq, decoratedSubtreeAt?, List.getElem?_eq_getElem iLtCount]
          have childLookupAtJ : arm.tree.decoratedSubtreeAt? (node.1 ++ [j]) =
              some (sortedTrees[j]'jLtCount) := by
            rw [decoratedSubtreeAt?_append arm.tree node.1 [j], lookup]
            simp [childrenEq, decoratedSubtreeAt?, List.getElem?_eq_getElem jLtCount]
          have childLookupAtISorted : arm.tree.decoratedSubtreeAt? childI.1 =
              some (sortedTrees[i]'iLtCount) := by
            rw [addrIFlat]
            exact childLookupAtI
          have childLookupAtJSorted : arm.tree.decoratedSubtreeAt? childJ.1 =
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
              (DeclarativeCIP.ruleKey input.moleculeGraph (ruleMajorArmGraph arm) W D childI)
              (sortedKeys[i]'iLtKeys).constitutional := ihI.2
          have ihRepJ : OfficialSparseCanonicalVectorComparison.Represents W D
              (DeclarativeCIP.ruleKey input.moleculeGraph (ruleMajorArmGraph arm) W D childJ)
              (sortedKeys[j]'jLtKeys).constitutional := ihJ.2
          have actualNe : OfficialRuleMajorKey.compare (sortedKeys[i]'iLtKeys).constitutional
              (sortedKeys[j]'jLtKeys).constitutional ≠ Ordering.lt := by
            have hne := (List.pairwise_iff_getElem.1 constitutionalDescending) i j
              (by simpa [lengthEq, List.length_map] using iLtCount)
              (by simpa [lengthEq, List.length_map] using jLtCount) hij
            simpa [List.getElem_map] using hne
          have hle : DeclarativeCIP.ruleKey input.moleculeGraph (ruleMajorArmGraph arm) W D childJ ≤
              DeclarativeCIP.ruleKey input.moleculeGraph (ruleMajorArmGraph arm) W D childI :=
            (OfficialSparseCanonicalVectorComparison.compare_ne_lt_iff_rightVector_le
              (leftWellFormed := wellFormedRuleMajorKey_of_tableMatch
                (LocalizedRuleMajorSortTrace.fullMatch_of_trace childTraceI).tableMatch
                (LocalizedRuleMajorSortTrace.realizes_of_trace childTraceI))
              (rightWellFormed := wellFormedRuleMajorKey_of_tableMatch
                (LocalizedRuleMajorSortTrace.fullMatch_of_trace childTraceJ).tableMatch
                (LocalizedRuleMajorSortTrace.realizes_of_trace childTraceJ))
              (leftShaped := DeclarativeCIP.ruleKey_vectorWellShaped input.moleculeGraph
                (ruleMajorArmGraph arm) W D childI)
              (rightShaped := DeclarativeCIP.ruleKey_vectorWellShaped input.moleculeGraph
                (ruleMajorArmGraph arm) W D childJ)
              (leftRepresents := ihRepI) (rightRepresents := ihRepJ)).1 actualNe
          simpa [List.getElem_map, slotIEq, slotJEq] using hle
        constructor
        · exact slotKeySorted
        · unfold OfficialSparseCanonicalVectorComparison.Represents
          intro r hr path
          cases path with
          | nil =>
              exact ruleMajorRootArm_nil_observation arm (W := W) (D := D) node
                (localizedRootTree input cursor (read cursor) sortedTrees)
                (localizedCumulativeRule45StepKey input stage cursor (read cursor) sortedKeys)
                fullMatch.tableMatch realizes lookup hr
          | cons digit path =>
              change DeclarativeCIP.nodePathObservation input.moleculeGraph (ruleMajorArmGraph arm) W D r
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
              rw [DeclarativeCIP.nodePathObservation_cons input.moleculeGraph (ruleMajorArmGraph arm) hr node
                (ranked := DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
                  (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
                (DeclarativeCIP.slotList_perm (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing)
                  (parent := node)
                  (count := (localizedRootTree input cursor (read cursor)
                    sortedTrees).children.length) hdense) slotKeySorted digit path]
              rw [encodedObservation_cons_of_key fullMatch.tableMatch realizes
                (sortedKeys := sortedKeys) pairedMatch (DeclarativeCIP.ruleOfIndex r) digit path]
              by_cases hdigit : digit < sortedTrees.length
              · have digitLtSlot : digit < (DeclarativeCIP.slotList
                    (toOfficialSourceTree arm.tree).declarativeAddressing node
                    (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length := by
                  simpa [DeclarativeCIP.slotList] using hdigit
                obtain ⟨child, slotSome, childAddr⟩ := DeclarativeCIP.slotList_getD_of_lt
                  (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := node)
                  (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
                  hdense hdigit
                have childAddrFlat : child.1 = node.1 ++ [digit] := by
                  rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address child,
                    (toOfficialSourceTree arm.tree).declarativeAddressing_address node] at childAddr
                  exact childAddr
                have childLookupAt : arm.tree.decoratedSubtreeAt? (node.1 ++ [digit]) =
                    some (sortedTrees[digit]'hdigit) := by
                  rw [decoratedSubtreeAt?_append arm.tree node.1 [digit], lookup]
                  simp [childrenEq, decoratedSubtreeAt?, List.getElem?_eq_getElem hdigit]
                have childLookupAtSorted : arm.tree.decoratedSubtreeAt? child.1 =
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
                    (DeclarativeCIP.ruleKey input.moleculeGraph (ruleMajorArmGraph arm) W D child)
                    (sortedKeys[digit]'digitLtKeys).constitutional := ihChild.2
                by_cases hgate : digit < W ∧ path.length < D
                · rw [if_pos hgate]
                  simp [slotSome]
                  rw [List.getElem?_eq_getElem digitLtKeys]
                  simp
                  exact ihRepChild r hr path
                · rw [if_neg hgate]
                  have childObsBot : DeclarativeCIP.nodePathObservation input.moleculeGraph
                      (ruleMajorArmGraph arm) W D r child path = ⊥ := by
                    by_contra hne
                    have bound := DeclarativeCIP.depth_add_length_le_of_nodePathObservation
                      input.moleculeGraph (ruleMajorArmGraph arm) hr path child hne
                    have childDepth : (ruleMajorArmGraph arm).depth child =
                        (ruleMajorArmGraph arm).depth node + 1 :=
                      (ruleMajorArmGraph arm).child_depth ⟨digit, childAddrFlat⟩
                    have hdigitLtW : digit < W := by
                      have countLeWidth := DeclarativeCIP.count_le_width
                        (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := node)
                        (count := (localizedRootTree input cursor (read cursor)
                          sortedTrees).children.length) hdense
                      have countLeWidth' : sortedTrees.length ≤ (ruleMajorArmGraph arm).width := by
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
                    (toOfficialSourceTree arm.tree).declarativeAddressing node
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



theorem ruleMajorTrace_of_subtree (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input stage read fuel tree key) :
    ∀ (path : List ℕ) (subtree : LocalizedCumulativeDecoratedTree input carrierFuel),
      tree.decoratedSubtreeAt? path = some subtree →
        ∃ (fuel' : Nat) (key' : input.LocalizedRerootCumulativeRule45Key),
          LocalizedRuleMajorSortTrace input stage read fuel' subtree key' := by
  induction fuel generalizing tree key with
  | zero =>
      intro path subtree lookup
      cases path with
      | nil =>
          rw [decoratedSubtreeAt?] at lookup
          have same : tree = subtree := Option.some.inj lookup
          subst subtree
          exact ⟨0, key, trace⟩
      | cons _slot _path =>
          cases trace with
          | terminal _fuel cursor _children _childrenComputed _terminalChildren _fullMatch
              _realizes =>
              have childrenEq : (localizedRootTree input cursor (read cursor) []).children = [] :=
                by unfold localizedRootTree; rfl
              rw [decoratedSubtreeAt?] at lookup
              simp [childrenEq] at lookup
  | succ fuel ih =>
      intro path subtree lookup
      cases path with
      | nil =>
          rw [decoratedSubtreeAt?] at lookup
          have same : tree = subtree := Option.some.inj lookup
          subst subtree
          exact ⟨fuel + 1, key, trace⟩
      | cons slot path' =>
          cases trace with
          | terminal _fuel cursor _children _childrenComputed _terminalChildren _fullMatch
              _realizes =>
              have childrenEq : (localizedRootTree input cursor (read cursor) []).children = [] :=
                by unfold localizedRootTree; rfl
              rw [decoratedSubtreeAt?] at lookup
              simp [childrenEq] at lookup
          | node _fuel cursor children childKeys sortedKeys sortedTrees childrenComputed nonempty
              childKeysComputed sortedEq constitutionalDescending _sortedDescending fullMatch realizes childrenTraced =>
              have childrenEq : (localizedRootTree input cursor (read cursor) sortedTrees).children =
                  sortedTrees := by
                unfold localizedRootTree; rfl
              rw [decoratedSubtreeAt?] at lookup
              cases slotLookup : sortedTrees[slot]? with
              | none => simp [childrenEq, slotLookup] at lookup
              | some child =>
                  simp [childrenEq, slotLookup] at lookup
                  have paired := LocalizedRuleMajorSortTraceList.to_forall₂ childrenTraced
                  have slotLtTrees : slot < sortedTrees.length :=
                    (List.getElem?_eq_some_iff.1 slotLookup).1
                  have lengthEq : sortedKeys.length = sortedTrees.length :=
                    List.Forall₂.length_eq paired
                  have slotLtKeys : slot < sortedKeys.length := by
                    simpa [lengthEq] using slotLtTrees
                  have childTrace : LocalizedRuleMajorSortTrace input stage read fuel
                      (sortedTrees[slot]'slotLtTrees) (sortedKeys[slot]'slotLtKeys) :=
                    List.Forall₂.get (i := slot) paired slotLtKeys slotLtTrees
                  have childEq : sortedTrees[slot]'slotLtTrees = child :=
                    Option.some.inj ((List.getElem?_eq_getElem slotLtTrees).symm.trans slotLookup)
                  have childLookup : (sortedTrees[slot]'slotLtTrees).decoratedSubtreeAt? path' =
                      some subtree := by
                    simpa [childEq] using lookup
                  exact ih (tree := sortedTrees[slot]'slotLtTrees)
                    (key := sortedKeys[slot]'slotLtKeys) childTrace path' subtree childLookup

/-- Every official node of a rule-major arm resolves to one decorated subtree of that same tree. -/
theorem ruleMajorRootArm_decoratedSubtree_of_node
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.RuleMajorRootArm center index stage read) (node : (ruleMajorArmGraph arm).Node) :
    ∃ dsub : LocalizedCumulativeDecoratedTree input
        (input.certified.input.molecule.atomCount + 1),
      arm.tree.decoratedSubtreeAt? node.1 = some dsub ∧
        (toOfficialSourceTree arm.tree).subtreeAt? node.1 = some (toOfficialSourceTree dsub) := by
  obtain ⟨subtree, lookup⟩ :=
    (toOfficialSourceTree arm.tree).exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses
      node.1 node.2
  have erasedLookup : (arm.tree.decoratedSubtreeAt? node.1).map toOfficialSourceTree =
      some subtree :=
    (lookup.symm.trans (toOfficialSourceTree_subtreeAt? arm.tree node.1)).symm
  obtain ⟨dsub, decLookup, dsubEq⟩ := Option.map_eq_some_iff.mp erasedLookup
  exact ⟨dsub, decLookup, by rw [lookup, ← dsubEq]⟩



theorem ruleMajorRootArm_root_represents
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.RuleMajorRootArm center index stage read) :
    OfficialSparseCanonicalVectorComparison.Represents (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
      (DeclarativeCIP.ruleKey input.moleculeGraph (ruleMajorArmGraph arm) (ruleMajorArmGraph arm).width
        (ruleMajorArmGraph arm).height (ruleMajorArmGraph arm).root)
      arm.key.constitutional :=
  (ruleMajorRootArm_node_bridge arm (W := (ruleMajorArmGraph arm).width) (D := (ruleMajorArmGraph arm).height)
    (hW := le_rfl) (hD := le_rfl) (node := (ruleMajorArmGraph arm).root) (dsub := arm.tree)
    (key := arm.key) arm.trace (by
      change arm.tree.decoratedSubtreeAt? [] = some arm.tree
      rw [decoratedSubtreeAt?])).2

/-- **Canonicality of the actual addressing.**  The ranked-sibling addressing of the arm's erased
source tree — the one fixed original-arm digraph — is a `CanonicalAddressing` for the independent
constitutional keys: it is dense structurally, and at every node the sibling order is key-sorted.
For the sorting clause, the node resolves to a decorated subtree whose rule-major sort trace transfers the
actual constitutional descending order of the sorted child keys through the comparator bridge
to the pairwise vector-key order of the slot list, and address injectivity (both are plain
hierarchy-address subtypes) identifies the arbitrary sibling pair with the corresponding slot-list
entries. -/
theorem ruleMajorRootArm_canonicalAddressing
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.RuleMajorRootArm center index stage read) :
    DeclarativeCIP.CanonicalAddressing input.moleculeGraph
      (toOfficialSourceTree arm.tree).declarativeAddressing := by
  constructor
  · exact (toOfficialSourceTree arm.tree).declarativeAddressing_dense
  · intro parent first second firstSlot secondSlot addrFirst addrSecond hlt
    obtain ⟨dsub, lookup, _⟩ := ruleMajorRootArm_decoratedSubtree_of_node arm parent
    have hdense : DeclarativeCIP.DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing
        parent dsub.children.length := ruleMajorRootArm_denseAt_of_lookup arm parent dsub lookup
    rcases ruleMajorTrace_of_subtree input stage read arm.trace parent.1 dsub lookup with
      ⟨fuel', key', trace'⟩
    have bridge := ruleMajorRootArm_node_bridge arm (W := (ruleMajorArmGraph arm).width) (D := (ruleMajorArmGraph arm).height)
      (hW := le_rfl) (hD := le_rfl) (node := parent) (dsub := dsub) (key := key')
      trace' lookup
    have slotKeySorted := bridge.1
    have firstLt : firstSlot < dsub.children.length := (hdense firstSlot).1 ⟨first, addrFirst⟩
    have secondLt : secondSlot < dsub.children.length := (hdense secondSlot).1 ⟨second, addrSecond⟩
    have firstSlotLt : firstSlot < (DeclarativeCIP.slotList
        (toOfficialSourceTree arm.tree).declarativeAddressing parent dsub.children.length).length := by
      simpa [DeclarativeCIP.slotList] using firstLt
    have secondSlotLt : secondSlot < (DeclarativeCIP.slotList
        (toOfficialSourceTree arm.tree).declarativeAddressing parent dsub.children.length).length := by
      simpa [DeclarativeCIP.slotList] using secondLt
    obtain ⟨childI, slotI, addrI⟩ := DeclarativeCIP.slotList_getD_of_lt
      (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := parent)
      (count := dsub.children.length) hdense firstLt
    obtain ⟨childJ, slotJ, addrJ⟩ := DeclarativeCIP.slotList_getD_of_lt
      (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := parent)
      (count := dsub.children.length) hdense secondLt
    have addrIFlat : first.1 = parent.1 ++ [firstSlot] := by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address first,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address parent] at addrFirst
      exact addrFirst
    have addrJFlat : second.1 = parent.1 ++ [secondSlot] := by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address second,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address parent] at addrSecond
      exact addrSecond
    have childIFlat : childI.1 = parent.1 ++ [firstSlot] := by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address childI,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address parent] at addrI
      exact addrI
    have childJFlat : childJ.1 = parent.1 ++ [secondSlot] := by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address childJ,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address parent] at addrJ
      exact addrJ
    have firstEq : first = childI := Subtype.ext (addrIFlat.trans childIFlat.symm)
    have secondEq : second = childJ := Subtype.ext (addrJFlat.trans childJFlat.symm)
    have slotIEq : (DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing
        parent dsub.children.length)[firstSlot]'firstSlotLt = childI :=
      Option.some.inj ((List.getElem?_eq_getElem firstSlotLt).symm.trans slotI)
    have slotJEq : (DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing
        parent dsub.children.length)[secondSlot]'secondSlotLt = childJ :=
      Option.some.inj ((List.getElem?_eq_getElem secondSlotLt).symm.trans slotJ)
    have firstSlotMapLt : firstSlot < ((DeclarativeCIP.slotList
        (toOfficialSourceTree arm.tree).declarativeAddressing parent dsub.children.length).map
      (DeclarativeCIP.ruleKey input.moleculeGraph (ruleMajorArmGraph arm) (ruleMajorArmGraph arm).width
        (ruleMajorArmGraph arm).height)).length := by
      simpa using firstSlotLt
    have secondSlotMapLt : secondSlot < ((DeclarativeCIP.slotList
        (toOfficialSourceTree arm.tree).declarativeAddressing parent dsub.children.length).map
      (DeclarativeCIP.ruleKey input.moleculeGraph (ruleMajorArmGraph arm) (ruleMajorArmGraph arm).width
        (ruleMajorArmGraph arm).height)).length := by
      simpa using secondSlotLt
    have hle : DeclarativeCIP.ruleKey input.moleculeGraph (ruleMajorArmGraph arm) (ruleMajorArmGraph arm).width
        (ruleMajorArmGraph arm).height childJ ≤
        DeclarativeCIP.ruleKey input.moleculeGraph (ruleMajorArmGraph arm) (ruleMajorArmGraph arm).width
          (ruleMajorArmGraph arm).height childI := by
      have hpair := (List.pairwise_iff_getElem.1 slotKeySorted) firstSlot secondSlot
        firstSlotMapLt secondSlotMapLt hlt
      simpa [List.getElem_map, slotIEq, slotJEq] using hpair
    simpa [firstEq, secondEq] using hle

end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorTreeGraph
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.RuleMajorTreeReadback4b
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.tripleKey_le_of_ruleMajor_compare_ne_lt
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.RuleMajorTreeNodeObservation
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_nodeObservation
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_denseAt_of_lookup
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_nil_observation
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_terminal_bridge
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_node_bridge
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorTrace_of_subtree
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_decoratedSubtree_of_node
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_root_represents
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_canonicalAddressing




namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open OfficialSparseCanonicalVectorComparison
open DeclarativeCIP

noncomputable section
open scoped Classical

section RuleMajorRootArmRule4b

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
  {index : Fin 4}
  {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
    Option LocalizedAuxiliaryLabel}
  {ρ : RS}
variable (arm : input.RuleMajorRootArm center index (.rule4b ρ) read)
  {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
  {unit : DetectedOccurrence input.moleculeGraph}

theorem ruleMajorRootArm_terminal_bridge4b (hyp : RuleMajorTreeReadback4b arm.tree descriptorMap unit ρ)
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (fullMatch : LocalizedCumulativeTreeFullMatch (.rule4b ρ)
      (localizedRootTree input cursor (read cursor) [])
      (localizedCumulativeRule45TerminalKey input (.rule4b ρ) cursor (read cursor)))
    (realizes : LocalizedCumulativeTreeRealizes input read
      (localizedRootTree input cursor (read cursor) []))
    {W D : ℕ} (node : (ruleMajorArmGraph arm).Node)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (read cursor) [])) :
    (((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
          (localizedRootTree input cursor (read cursor) []).children.length).map
        (tripleKey input.moleculeGraph (ruleMajorArmGraph arm)
          (readingEvidence input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ)) W D)).Pairwise
      fun x y => y ≤ x) ∧
      Represents4a W D (rule4aComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (readingEvidence input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ)) W D node)
        (localizedCumulativeRule45TerminalKey input (.rule4b ρ) cursor (read cursor)) ∧
      Represents4b W D (rule4bComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (readingEvidence input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ)) W D node)
        (localizedCumulativeRule45TerminalKey input (.rule4b ρ) cursor (read cursor)) := by
  have childrenEq : (localizedRootTree input cursor (read cursor) []).children = [] := by
    unfold localizedRootTree; rfl
  have pairedNil : List.Forall₂ (fun childKey childTree =>
      LocalizedCumulativeTreeTableMatch (.rule4b ρ) childTree childKey ∧
        LocalizedCumulativeTreeRealizes input read childTree)
      ([] : List input.LocalizedRerootCumulativeRule45Key)
      (localizedRootTree input cursor (read cursor) []).children := by
    rw [childrenEq]; exact List.Forall₂.nil
  have constBot : ∀ digit path, nodePathObservation input.moleculeGraph (ruleMajorArmGraph arm) W D 0 node
      (digit :: path) = ⊥ := by
    intro digit path
    have h := (ruleMajorRootArm_terminal_bridge arm cursor fullMatch realizes (W := W) (D := D) node lookup).2
    have h' := h 0 (by omega) (digit :: path)
    unfold nodePathObservation
    rw [h', encodedObservation_cons_of_key fullMatch.tableMatch realizes pairedNil
      (ruleOfIndex 0) digit path]
    rfl
  refine ⟨by rw [childrenEq]; simp [slotList], ?_, ?_⟩
  · intro path
    cases path with
    | nil =>
        exact stereoNodePathObservation_nil_eq_encoded4a_rule4b descriptorMap unit (ruleMajorArmGraph arm) W D
          node fullMatch.tableMatch realizes (hyp.label node _ lookup) (hyp.tetrahedral node)
          (hyp.available node) _
    | cons digit path =>
        have rhs : encoded4a (localizedCumulativeRule45TerminalKey input (.rule4b ρ) cursor (read cursor))
            (digit :: path) = ⊥ := by
          rw [encoded4a_cons_of_key_rule4b fullMatch.tableMatch realizes pairedNil digit path]; rfl
        rw [rhs]
        exact (stereoNodePathObservation_eq_bot_iff input.moleculeGraph (ruleMajorArmGraph arm) _ _ W D
          (digit :: path) node).2 (constBot digit path)
  · intro path
    cases path with
    | nil =>
        exact stereoNodePathObservation_nil_eq_encoded4b descriptorMap unit (ruleMajorArmGraph arm) W D node
          fullMatch.tableMatch realizes (hyp.label node _ lookup) (hyp.tetrahedral node)
    | cons digit path =>
        have rhs : encoded4b (localizedCumulativeRule45TerminalKey input (.rule4b ρ) cursor (read cursor))
            (digit :: path) = ⊥ := by
          rw [encoded4b_cons_of_key fullMatch.tableMatch realizes pairedNil digit path]; rfl
        rw [rhs]
        exact (stereoNodePathObservation_eq_bot_iff input.moleculeGraph (ruleMajorArmGraph arm) _ _ W D
          (digit :: path) node).2 (constBot digit path)

/-- **Recursive Rule-4b bridge.** -/
theorem ruleMajorRootArm_node_bridge4b (hyp : RuleMajorTreeReadback4b arm.tree descriptorMap unit ρ)
    {W D : ℕ} (hW : (ruleMajorArmGraph arm).width ≤ W) (hD : (ruleMajorArmGraph arm).height ≤ D)
    {fuel : Nat} (node : (ruleMajorArmGraph arm).Node)
    (dsub : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
    (key : input.LocalizedRerootCumulativeRule45Key)
    (trace : LocalizedRuleMajorSortTrace input (.rule4b ρ) read fuel dsub key)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 = some dsub) :
    (((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node dsub.children.length).map
        (tripleKey input.moleculeGraph (ruleMajorArmGraph arm)
          (readingEvidence input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ)) W D)).Pairwise
      fun x y => y ≤ x) ∧
      Represents4a W D (rule4aComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (readingEvidence input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ)) W D node) key ∧
      Represents4b W D (rule4bComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (readingEvidence input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ)) W D node) key := by
  induction fuel generalizing dsub key node lookup with
  | zero =>
      cases trace with
      | terminal _fuel cursor _children _childrenComputed _terminalChildren fullMatch realizes =>
          exact ruleMajorRootArm_terminal_bridge4b arm hyp cursor fullMatch realizes node lookup
  | succ fuel ih =>
      have fullMatch := LocalizedRuleMajorSortTrace.fullMatch_of_trace trace
      have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
      rcases LocalizedRuleMajorSortTrace.structure_of_trace trace with
        ⟨cursor, _children, dsubEq, keyEq, _childrenEq, _childrenComputed, _terminalChildren⟩ |
        ⟨cursor, _children, _childKeys, sortedKeys, sortedTrees, dsubEq, keyEq, childrenEq,
          _childrenComputed, _nonempty, _childKeysComputed, sortedEq, _constitutionalDescending,
          sortedDescending, childrenTraced⟩
      · subst dsub; subst key
        exact ruleMajorRootArm_terminal_bridge4b arm hyp cursor fullMatch realizes node lookup
      · subst dsub; subst key
        set E := readingEvidence input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ)
          with hE
        have hdense : DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length :=
          ruleMajorRootArm_denseAt_of_lookup arm node (localizedRootTree input cursor (read cursor) sortedTrees) lookup
        have paired := LocalizedRuleMajorSortTraceList.to_forall₂ childrenTraced
        have lengthEq : sortedKeys.length = sortedTrees.length := List.Forall₂.length_eq paired
        have pairedMatch : List.Forall₂ (fun childKey childTree =>
            LocalizedCumulativeTreeTableMatch (.rule4b ρ) childTree childKey ∧
              LocalizedCumulativeTreeRealizes input read childTree) sortedKeys sortedTrees :=
          List.Forall₂.imp (fun childKey childTree related =>
            ⟨(LocalizedRuleMajorSortTrace.fullMatch_of_trace related).tableMatch,
              LocalizedRuleMajorSortTrace.realizes_of_trace related⟩) paired
        have descending : input.RuleMajorCumulativeKeysDescending
            (CertifiedLocalizedCIPInput.ruleMajorStageWidth (.rule4b ρ)) sortedKeys := sortedDescending
        have countEq : (localizedRootTree input cursor (read cursor) sortedTrees).children.length =
            sortedTrees.length := by rw [childrenEq]
        have slotLength : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length =
            sortedTrees.length := by simp [slotList, countEq]
        have childAt : ∀ i (hi : i < sortedTrees.length), ∃ child : (ruleMajorArmGraph arm).Node,
            (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[i]? =
                some child ∧
              child.1 = node.1 ++ [i] ∧
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
            LocalizedRuleMajorSortTrace input (.rule4b ρ) read fuel (sortedTrees[i]'hi)
              (sortedKeys[i]'(by omega)) :=
          fun i hi => List.Forall₂.get (i := i) paired (by omega) hi
        have ihAt : ∀ i (hi : i < sortedTrees.length) (child : (ruleMajorArmGraph arm).Node),
            arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
              Represents4a W D (rule4aComponent input.moleculeGraph (ruleMajorArmGraph arm) E W D child)
                  (sortedKeys[i]'(by omega)) ∧
                Represents4b W D (rule4bComponent input.moleculeGraph (ruleMajorArmGraph arm) E W D child)
                  (sortedKeys[i]'(by omega)) :=
          fun i hi child hl => (ih child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega)) (traceAt i hi) hl).2
        have constAt : ∀ i (hi : i < sortedTrees.length) (child : (ruleMajorArmGraph arm).Node),
            arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
              Represents W D (ruleKey input.moleculeGraph (ruleMajorArmGraph arm) W D child)
                (sortedKeys[i]'(by omega)).constitutional :=
          fun i hi child hl =>
            (ruleMajorRootArm_node_bridge arm hW hD child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega))
              (traceAt i hi) hl).2
        have slotSorted : ((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).map
              (tripleKey input.moleculeGraph (ruleMajorArmGraph arm) E W D)).Pairwise fun x y => y ≤ x := by
          rw [List.pairwise_iff_getElem]
          intro i j hi hj hij
          rw [List.length_map, slotLength] at hi hj
          obtain ⟨childI, slotI, _, lookupI⟩ := childAt i hi
          obtain ⟨childJ, slotJ, _, lookupJ⟩ := childAt j hj
          have hneWidth : input.compareRuleMajorCumulativeDescriptor
              (CertifiedLocalizedCIPInput.ruleMajorStageWidth (.rule4b ρ))
              (sortedKeys[i]'(by omega))
              (sortedKeys[j]'(by omega)) ≠ Ordering.lt :=
            (List.pairwise_iff_getElem.1 descending) i j (by omega) (by omega) hij
          have widthEq : CertifiedLocalizedCIPInput.ruleMajorStageWidth (.rule4b ρ) = 2 := by
            rfl
          have hne : input.compareRuleMajorCumulativeDescriptor 2 (sortedKeys[i]'(by omega))
              (sortedKeys[j]'(by omega)) ≠ Ordering.lt := by
            rw [← widthEq]
            exact hneWidth
          have hle := tripleKey_le_of_ruleMajor_compare_ne_lt E
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt i hi)).tableMatch
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt j hj)).tableMatch
            (LocalizedRuleMajorSortTrace.realizes_of_trace (traceAt i hi))
            (LocalizedRuleMajorSortTrace.realizes_of_trace (traceAt j hj))
            (constAt i hi childI lookupI) (constAt j hj childJ lookupJ)
            (ihAt i hi childI lookupI).1 (ihAt j hj childJ lookupJ).1
            (ihAt i hi childI lookupI).2 (ihAt j hj childJ lookupJ).2
            hne
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
              (ordinaryKey input.moleculeGraph (ruleMajorArmGraph arm) E W D)).Pairwise fun x y => y ≤ x := by
          rw [List.pairwise_map] at slotSorted ⊢
          exact slotSorted.imp fun h =>
            (ordinaryKey_le_iff_tripleKey input.moleculeGraph (ruleMajorArmGraph arm) E hyp.rule4abOnly W D
              _ _).2 h
        have hperm := slotList_perm (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing)
          (parent := node)
          (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length) hdense
        -- the common `cons` argument for both columns
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
            (∀ digit path, enc (localizedCumulativeRule45StepKey input (.rule4b ρ) cursor (read cursor)
                sortedKeys) (digit :: path) =
              ((sortedKeys[digit]?).map fun childKey => enc childKey path).getD ⊥) →
            ∀ digit path,
              Certificate.CanonicalSphereKey.pathObservationOf W D (comp node) (digit :: path) =
                enc (localizedCumulativeRule45StepKey input (.rule4b ρ) cursor (read cursor) sortedKeys)
                  (digit :: path) := by
          intro rule enc comp repAt compEq encCons digit path
          rw [compEq node]
          change stereoNodePathObservation input.moleculeGraph (ruleMajorArmGraph arm) E W D rule node
            (digit :: path) = _
          rw [stereoNodePathObservation_cons input.moleculeGraph (ruleMajorArmGraph arm) E W D rule node hperm
            slotSortedOrd digit path, encCons digit path]
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
              apply (stereoNodePathObservation_eq_bot_iff input.moleculeGraph (ruleMajorArmGraph arm) E rule W D
                path child).2
              by_contra hne
              have bound := depth_add_length_le_of_nodePathObservation input.moleculeGraph (ruleMajorArmGraph arm)
                (W := W) (D := D) (by omega : (0 : ℕ) < 3) path child hne
              have childDepth : (ruleMajorArmGraph arm).depth child = (ruleMajorArmGraph arm).depth node + 1 :=
                (ruleMajorArmGraph arm).child_depth ⟨digit, childAddr⟩
              have hdigitLtW : digit < W := by
                have countLe : sortedTrees.length ≤ (ruleMajorArmGraph arm).width := by
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
        refine ⟨slotSorted, ?_, ?_⟩
        · intro path
          cases path with
          | nil =>
              exact stereoNodePathObservation_nil_eq_encoded4a_rule4b descriptorMap unit (ruleMajorArmGraph arm)
                W D node fullMatch.tableMatch realizes (hyp.label node _ lookup) (hyp.tetrahedral node)
                (hyp.available node) _
          | cons digit path =>
              exact consCase .rule4aStereogenicUnitKind encoded4a
                (rule4aComponent input.moleculeGraph (ruleMajorArmGraph arm) E W D)
                (fun i hi child hl => (ihAt i hi child hl).1) (fun _ => rfl)
                (fun digit path => encoded4a_cons_of_key_rule4b fullMatch.tableMatch realizes
                  pairedMatch digit path) digit path
        · intro path
          cases path with
          | nil =>
              exact stereoNodePathObservation_nil_eq_encoded4b descriptorMap unit (ruleMajorArmGraph arm) W D
                node fullMatch.tableMatch realizes (hyp.label node _ lookup) (hyp.tetrahedral node)
          | cons digit path =>
              exact consCase .rule4bLikeUnlikeDescriptorPairs encoded4b
                (rule4bComponent input.moleculeGraph (ruleMajorArmGraph arm) E W D)
                (fun i hi child hl => (ihAt i hi child hl).2) (fun _ => rfl)
                (fun digit path => encoded4b_cons_of_key fullMatch.tableMatch realizes
                  pairedMatch digit path) digit path



theorem ruleMajorRootArm_keySorted_readingEvidence (hyp : RuleMajorTreeReadback4b arm.tree descriptorMap unit ρ) :
    KeySorted (ordinaryKey input.moleculeGraph (ruleMajorArmGraph arm)
        (readingEvidence input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ))
        (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height)
      (toOfficialSourceTree arm.tree).declarativeAddressing := by
  intro parent first second firstSlot secondSlot addrFirst addrSecond hlt
  obtain ⟨dsub, lookup, _⟩ := ruleMajorRootArm_decoratedSubtree_of_node arm parent
  have hdense : DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing parent
      dsub.children.length := ruleMajorRootArm_denseAt_of_lookup arm parent dsub lookup
  rcases ruleMajorTrace_of_subtree input (.rule4b ρ) read arm.trace parent.1 dsub lookup with
    ⟨fuel', key', trace'⟩
  have bridge := ruleMajorRootArm_node_bridge4b arm hyp (W := (ruleMajorArmGraph arm).width) (D := (ruleMajorArmGraph arm).height)
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
  exact (ordinaryKey_le_iff_tripleKey input.moleculeGraph (ruleMajorArmGraph arm) _ hyp.rule4abOnly _ _ _ _).2
    hpair

/-- **C2.**  The actual stage-`.rule4b ρ` addressing is ordinary-canonical for the reading
evidence under `senseOf ρ`. -/
theorem ruleMajorRootArm_ordinaryCanonicalAddressing_readingEvidence (hyp : RuleMajorTreeReadback4b arm.tree descriptorMap unit ρ) :
    OrdinaryCanonicalAddressing input.moleculeGraph
      (readingEvidence input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ))
      (toOfficialSourceTree arm.tree).declarativeAddressing :=
  ⟨(toOfficialSourceTree arm.tree).declarativeAddressing_dense,
    ruleMajorRootArm_keySorted_readingEvidence arm hyp⟩

/-! ## C1: the root key's Rule-4b column is the independent reading -/

/-- **C1.**  The actual Rule-4b column of the arm's root key is represented by the independent
complete reading under `senseOf ρ`. -/
theorem ruleMajorRootArm_root_represents4b (hyp : RuleMajorTreeReadback4b arm.tree descriptorMap unit ρ) :
    Represents4b (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
      (reading input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ)) arm.key :=
  (ruleMajorRootArm_node_bridge4b arm hyp le_rfl le_rfl (ruleMajorArmGraph arm).root arm.tree arm.key arm.trace rfl).2.2

theorem ruleMajorRootArm_root_represents4a (hyp : RuleMajorTreeReadback4b arm.tree descriptorMap unit ρ) :
    Represents4a (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
      (rule4aComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (readingEvidence input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ))
        (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height (ruleMajorArmGraph arm).root) arm.key :=
  (ruleMajorRootArm_node_bridge4b arm hyp le_rfl le_rfl (ruleMajorArmGraph arm).root arm.tree arm.key arm.trace rfl).2.1

end RuleMajorRootArmRule4b

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorArmGraph
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorTreeGraph
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.RuleMajorTreeReadback4b
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.tripleKey_le_of_ruleMajor_compare_ne_lt
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.RuleMajorTreeNodeObservation
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_nodeObservation
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_denseAt_of_lookup
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_nil_observation
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_terminal_bridge
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_node_bridge
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorTrace_of_subtree
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_decoratedSubtree_of_node
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_root_represents
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_canonicalAddressing
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_terminal_bridge4b
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_node_bridge4b
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_keySorted_readingEvidence
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_ordinaryCanonicalAddressing_readingEvidence
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_root_represents4a
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_root_represents4b
