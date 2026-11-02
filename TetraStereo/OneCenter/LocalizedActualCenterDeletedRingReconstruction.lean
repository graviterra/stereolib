import TetraStereo.OneCenter.LocalizedActualKeyTieBondReconstruction
import TetraStereo.OneCenter.LocalizedCenterDeletedTreeRingReconstruction
import TetraStereo.OneCenter.LocalizedOutwardDecoratedSourceFaithfulness
import TetraStereo.OneCenter.LocalizedMultipleBondRealSpine
import TetraStereo.OneCenter.LocalizedMultipleBondRealCutEquivalence
import TetraStereo.OneCenter.LocalizedRealizedTreeCutIsomorphism
import TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage
import TetraStereo.KernelOnly

set_option autoImplicit false



































































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput








/-- **Distance reading from a provenance equation.**  `rule1bRootDistance` matches on the stored
provenance, so a provenance equation for the whole node rewrites the distance match. -/
theorem rule1bRootDistance_eq_of_provenance_real {V : Type*} (node : OfficialCIPNode V)
    (hprov : node.provenance = OfficialCIPNodeProvenance.realAtom) :
    node.rule1bRootDistance = node.depth := by
  simp [OfficialCIPNode.rule1bRootDistance, hprov]

/-- **Distance reading from a ring-duplicate provenance equation.** -/
theorem rule1bRootDistance_eq_of_provenance_ringDuplicate {V : Type*}
    (node : OfficialCIPNode V) {d : Nat}
    (hprov : node.provenance = OfficialCIPNodeProvenance.ringDuplicate d) :
    node.rule1bRootDistance = d := by
  simp [OfficialCIPNode.rule1bRootDistance, hprov]

/-- **The stored distance of a root edge is one.**  The root history has length two and real
provenance. -/
theorem rule1bRootDistance_rootFromEdge {V : Type*} (parent current : V) :
    (OfficialCIPNode.rootFromEdge parent current).rule1bRootDistance = 1 := by
  simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.rootFromEdge, OfficialCIPNode.depth]

/-- **The canonical ligand root edge is a real path node.**  The one-edge walk from the centre to
the canonical ligand is simple: the centre has no self-bond, so the edge never closes on itself.
This is the base case of the whole arm provenance induction. -/
theorem realPathNode_rootFromEdge
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    input.RealPathNode center.1
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index)) := by
  let ligand := input.canonicalLigandAtom center index
  have centerNeLigand : center.1 ≠ ligand := by
    intro h
    exact moleculeGraph_not_adj_self input.moleculeGraph center.1
      (h.symm ▸ input.canonicalLigandAtom_adj center index)
  refine ⟨ligand,
    SimpleGraph.Walk.cons (input.canonicalLigandAtom_adj center index)
      SimpleGraph.Walk.nil, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · exact (SimpleGraph.Walk.cons_isPath_iff
      (input.canonicalLigandAtom_adj center index) SimpleGraph.Walk.nil).2
      ⟨by simp, by simpa [ligand] using centerNeLigand⟩
  · rfl
  · intro parent parentObserved
    have parentEq : center.1 = parent :=
      Option.some.inj (by simpa [OfficialCIPNode.parent?, OfficialCIPNode.rootFromEdge] using
        parentObserved)
    rw [← parentEq]
    exact SimpleGraph.Walk.penultimate_cons_nil
      (input.canonicalLigandAtom_adj center index)

/-- **A real executable child of a real arm node has positive Rule-1b distance.**  Its depth is
the parent history length, which is at least two: the parent branch ends in `[ligand, center]`. -/
theorem centerArmRealNode_realChild_rule1bDistance_pos
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (_tree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    (_singleBonded : input.moleculeGraph.SimpleBonded)
    {node child : OfficialCIPNode input.Atom} {next : input.Atom}
    (real : input.RealPathNode center.1 node)
    (suffixHist : [input.canonicalLigandAtom center index, center.1] <:+ node.history)
    (_childObserved : child.current? = some next)
    (childMem : child ∈ input.executableOfficialCIPChildren node)
    (childReal : child.provenance = OfficialCIPNodeProvenance.realAtom) :
    0 < child.rule1bRootDistance := by
  have lenEq : child.history.length = node.history.length + 1 :=
    input.history_length_of_mem_executableOfficialCIPChildren
      (input.realPathNode_provenance real) childMem
  have depthEq : child.depth = node.history.length := by
    unfold OfficialCIPNode.depth
    rw [lenEq]
    simp
  have hlen : 2 ≤ node.history.length := by
    have := suffixHist.length_le
    simpa using this
  have hdist : child.rule1bRootDistance = child.depth :=
    rule1bRootDistance_eq_of_provenance_real child childReal
  rw [hdist, depthEq]
  omega

/-- **The visible Rule-1b distance classifies the executable child role.**  A real child is
exactly a child of positive distance; the zero-distance centre closure is exactly a child of
distance zero.  This is the visible-role reconstruction: provenance is recovered from the
observable shape. -/
theorem centerArmRealNode_child_visibleRole_classification
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (tree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {node child : OfficialCIPNode input.Atom} {current next : input.Atom}
    (real : input.RealPathNode center.1 node)
    (suffixHist : [input.canonicalLigandAtom center index, center.1] <:+ node.history)
    (currentObserved : node.current? = some current)
    (childObserved : child.current? = some next)
    (childMem : child ∈ input.executableOfficialCIPChildren node) :
    (0 < child.rule1bRootDistance ↔
        child.provenance = OfficialCIPNodeProvenance.realAtom) ∧
      (child.rule1bRootDistance = 0 ↔
        child.provenance = OfficialCIPNodeProvenance.ringDuplicate 0) := by
  have classified := input.centerArmRealNode_child_classification center index tree singleBonded
    real suffixHist currentObserved childObserved childMem
  constructor
  · constructor
    · intro hpos
      rcases classified with ⟨realProv, _fresh⟩ | ⟨_nextCenter, dupProv⟩
      · exact realProv
      · exfalso
        have hzero : child.rule1bRootDistance = 0 :=
          rule1bRootDistance_eq_of_provenance_ringDuplicate child dupProv
        omega
    · intro childReal
      exact input.centerArmRealNode_realChild_rule1bDistance_pos center index tree singleBonded
        real suffixHist childObserved childMem childReal
  · constructor
    · intro hzero
      rcases classified with ⟨realProv, _fresh⟩ | ⟨_nextCenter, dupProv⟩
      · exfalso
        have hpos : 0 < child.rule1bRootDistance :=
          input.centerArmRealNode_realChild_rule1bDistance_pos center index tree singleBonded
            real suffixHist childObserved childMem realProv
        omega
      · exact dupProv
    · intro dupProv
      exact rule1bRootDistance_eq_of_provenance_ringDuplicate child dupProv

/-! ## 2. The arm-visible invariant

The invariant below holds at every actual decorated subtree of an arm expansion rooted at
`rootFromEdge center ligand`.  It collects exactly the facts the comparison transport needs at a
position: same original root, the stored `[ligand, center]` suffix, real-path realisation, the
two-role provenance classification and the two visible distance laws. -/

/-- **The visible role invariant of one actual decorated arm subtree.** -/
structure ArmTreeVisible (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)) : Prop where
  /-- The stored original root is the centre. -/
  root_eq_center : tree.source.occurrence.1.root = center.1
  /-- The branch history ends in the canonical ligand and the centre. -/
  suffix : [input.canonicalLigandAtom center index, center.1] <:+
    tree.source.occurrence.1.node.history
  /-- Real provenance carries a simple physical walk from the centre. -/
  real_path : tree.source.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
    input.RealPathNode center.1 tree.source.occurrence.1.node
  /-- The provenance is real, or the zero-distance centre closure. -/
  role : tree.source.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∨
    (tree.source.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.ringDuplicate 0 ∧
      tree.source.occurrence.1.node.current? = some center.1)
  /-- Distance zero is exactly the centre closure role. -/
  visible_zero : tree.source.occurrence.1.node.rule1bRootDistance = 0 ↔
    tree.source.occurrence.1.node.provenance = OfficialCIPNodeProvenance.ringDuplicate 0
  /-- Positive distance is exactly the real role. -/
  visible_pos : 0 < tree.source.occurrence.1.node.rule1bRootDistance ↔
    tree.source.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom

/-- **The canonical ligand root source satisfies the arm-visible invariant.** -/
theorem armTreeVisible_of_ligandRootSource
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (rootSource : tree.source = input.localizedLigandRootCursor center index) :
    ArmTreeVisible input center index tree := by
  have nodeEq : tree.source.occurrence.1.node =
      OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index) := by
    rw [rootSource]
    exact input.localizedLigandRootNode_eq_rootFromEdge center index
  have hdist : (OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index)).rule1bRootDistance = 1 :=
    rule1bRootDistance_rootFromEdge center.1 (input.canonicalLigandAtom center index)
  have hprov : (OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index)).provenance =
        OfficialCIPNodeProvenance.realAtom := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rootSource]
    rfl
  · rw [nodeEq]
    exact ⟨[], by simp [OfficialCIPNode.rootFromEdge]⟩
  · intro _realProv
    rw [nodeEq]
    exact input.realPathNode_rootFromEdge center index
  · rw [nodeEq]
    exact Or.inl rfl
  · constructor
    · intro hring
      rw [nodeEq, hdist] at hring
      omega
    · intro hzero
      have hzero' : (OfficialCIPNode.rootFromEdge center.1
          (input.canonicalLigandAtom center index)).provenance =
            OfficialCIPNodeProvenance.ringDuplicate 0 := by
        rw [← nodeEq]
        exact hzero
      rw [hprov] at hzero'
      cases hzero'
  · constructor
    · intro _hpos
      rw [nodeEq]
      exact hprov
    · intro _realProv
      rw [nodeEq, hdist]
      omega

/-- **A visible arm tree with an executable child is real.**  Duplicate leaves have no executable
children, so a nonempty child list forces the real role. -/
theorem armTreeVisible_provenance_real_of_childMem
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (visible : ArmTreeVisible input center index tree)
    (childMem : ∃ child : OfficialCIPNode input.Atom,
      child ∈ input.executableOfficialCIPChildren tree.source.occurrence.1.node) :
    tree.source.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  cases visible.role with
  | inl realProv => exact realProv
  | inr h =>
      obtain ⟨child, childPresent⟩ := childMem
      have dup : tree.source.occurrence.1.node.isDuplicateLeaf = true := by
        simp [OfficialCIPNode.isDuplicateLeaf, h.1]
      unfold executableOfficialCIPChildren at childPresent
      rw [if_pos dup] at childPresent
      exact False.elim (List.not_mem_nil childPresent)




theorem generatedBy_perm_of_generated
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren) :
    ((LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList tree.children).map
        OfficialCIPSourceTree.source).Perm
      (input.executableOfficialCIPChildren tree.source.occurrence.1.node) := by
  obtain ⟨source, _atomicNumber, _rule1bDistance, _isotopeMass, _label, children⟩ := tree
  rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTree_mk] at generated
  unfold OfficialCIPSourceTree.GeneratedBy at generated
  exact generated.1

/-- **Forest extraction from actual generatedness.** -/
theorem generatedBy_forest_of_generated
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren) :
    OfficialCIPSourceTree.ForestGeneratedBy input.executableOfficialCIPChildren
      (LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList tree.children) := by
  obtain ⟨source, _atomicNumber, _rule1bDistance, _isotopeMass, _label, children⟩ := tree
  rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTree_mk] at generated
  unfold OfficialCIPSourceTree.GeneratedBy at generated
  exact generated.2

/-- **Generatedness descends to actual decorated subtrees.**  The root permutation supplies the
first step and `ForestGeneratedBy` supplies every deeper step along the sibling-slot path. -/
theorem generatedOf_subtree
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ {tree : LocalizedCumulativeDecoratedTree input carrierFuel},
      (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
        input.executableOfficialCIPChildren →
        ∀ {path : List Nat} {node : LocalizedCumulativeDecoratedTree input carrierFuel},
          subtreeAt? tree path = some node →
            (LocalizedCumulativeDecoratedTree.toOfficialSourceTree node).GeneratedBy
              input.executableOfficialCIPChildren := by
  intro tree generated path
  induction path generalizing tree with
  | nil =>
      intro node lookup
      have nodeEq : node = tree := by
        rw [subtreeAt?_nil] at lookup
        exact (Option.some.inj lookup).symm
      rw [nodeEq]
      exact generated
  | cons slot rest ih =>
      intro node lookup
      rw [subtreeAt?_cons_eq_some_iff] at lookup
      obtain ⟨child, childLookup, restLookup⟩ := lookup
      have childGenerated :
          (LocalizedCumulativeDecoratedTree.toOfficialSourceTree child).GeneratedBy
            input.executableOfficialCIPChildren := by
        have forest := generatedBy_forest_of_generated input generated
        have childTreeMem : LocalizedCumulativeDecoratedTree.toOfficialSourceTree child ∈
            LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList tree.children := by
          rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_eq_map]
          exact List.mem_map.mpr ⟨child, List.mem_of_getElem? childLookup, rfl⟩
        exact (OfficialCIPSourceTree.forestGeneratedBy_iff_forall
          input.executableOfficialCIPChildren
          (LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList tree.children)).mp forest
          (LocalizedCumulativeDecoratedTree.toOfficialSourceTree child) childTreeMem
      exact ih childGenerated restLookup





theorem armTreeVisible_of_child
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (armTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {read : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    {tree child : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (visible : ArmTreeVisible input center index tree)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren)
    {slot : Nat} (lookup : tree.children[slot]? = some child) :
    ArmTreeVisible input center index child := by
  have childMem : child.source.occurrence.1.node ∈
      input.executableOfficialCIPChildren tree.source.occurrence.1.node := by
    have genPerm := generatedBy_perm_of_generated input generated
    have inMap : child.source.occurrence.1.node ∈
        (LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList tree.children).map
          OfficialCIPSourceTree.source := by
      rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_eq_map]
      exact List.mem_map.mpr ⟨LocalizedCumulativeDecoratedTree.toOfficialSourceTree child,
        List.mem_map.mpr ⟨child, List.mem_of_getElem? lookup, rfl⟩,
        LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source child⟩
    exact genPerm.mem_iff.mp inMap
  have parentReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom :=
    armTreeVisible_provenance_real_of_childMem input center index visible
      ⟨child.source.occurrence.1.node, childMem⟩
  obtain ⟨next, copyIndex, childExtend⟩ :=
    input.mem_executableOfficialCIPChildren_extend tree.source.occurrence.1.node
      child.source.occurrence.1.node childMem
  have childObserved : child.source.occurrence.1.node.current? = some next := by
    simp [childExtend]
  have currentObserved : tree.source.occurrence.1.node.current? = some (nodeCurrent tree) :=
    nodeCurrent_spec tree
  have rawClassified := input.centerArmRealNode_child_classification center index armTree
    singleBonded (visible.real_path parentReal) visible.suffix currentObserved childObserved
    childMem
  have classified := input.centerArmRealNode_child_visibleRole_classification center index armTree
    singleBonded (visible.real_path parentReal) visible.suffix currentObserved childObserved
    childMem
  have childRole : child.source.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom ∨
      (child.source.occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.ringDuplicate 0 ∧
        child.source.occurrence.1.node.current? = some center.1) := by
    rcases rawClassified with ⟨realProv, _fresh⟩ | ⟨nextCenter, dupProv⟩
    · exact Or.inl realProv
    · exact Or.inr ⟨dupProv, by simp [childExtend, nextCenter]⟩
  have suffixChild : [input.canonicalLigandAtom center index, center.1] <:+
      child.source.occurrence.1.node.history := by
    obtain ⟨pre, hpre⟩ := visible.suffix
    refine ⟨next :: pre, ?_⟩
    simpa [childExtend, OfficialCIPNode.extend_history] using congrArg (List.cons next) hpre
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have childRootEq := child_root_of_child realizes lookup
    rw [childRootEq, visible.root_eq_center]
  · exact suffixChild
  · intro childRealProv
    exact input.realPathNode_child_of_mem_executableOfficialCIPChildren
      (visible.real_path parentReal) childMem childRealProv
  · exact childRole
  · exact ⟨classified.2.1, classified.2.2⟩
  · exact ⟨classified.1.1, classified.1.2⟩

/-- **The arm-visible invariant holds at every actual position.**  Induction on the position
length: the root case is the ligand root source; the step descends along the actual child lookup
at the parent position. -/
theorem armTreeVisible_of_position
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (armTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {read : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren)
    (rootSource : tree.source = input.localizedLigandRootCursor center index)
    (p : Position tree) :
    ArmTreeVisible input center index (positionNode p) := by
  induction hlen : p.val.length using Nat.strong_induction_on generalizing p with
  | h n ih =>
      cases hp : p.val with
      | nil =>
          have pEq : p = rootPosition tree := Subtype.ext hp
          rw [pEq, positionNode_rootPosition]
          exact armTreeVisible_of_ligandRootSource input center index rootSource
      | cons slot rest =>
          have ne : p.val ≠ [] := by
            rw [hp]
            simp
          let parent := positionParent p ne
          have parentLen : parent.val.length = rest.length := by
            rw [positionParent_val, hp]
            simp
          have parentLt : rest.length < n := by
            rw [← hlen, hp]
            simp
          have visibleParent : ArmTreeVisible input center index (positionNode parent) :=
            ih rest.length parentLt parent parentLen
          obtain ⟨slot', lookup'⟩ := positionParent_node_child p ne
          exact armTreeVisible_of_child input center index singleBonded armTree visibleParent
            (realizes_of_subtree realizes (positionNode_spec parent))
            (generatedOf_subtree input generated (positionNode_spec parent)) lookup'

/-! ## 3. The centre-attachment marker

The attachment of a real position to the original centre is visible: at the root it is the
implicit stored parent edge; at every other real position it is exactly a zero-distance ring
child in the decorated tree.  Both readings are equivalent to the physical bond, so ring
closures through the centre are preserved by the comparison transport. -/

/-- **The centre-attachment marker of a real position.**  The root is attached through its stored
parent; any other real position is attached exactly when one of its actual children has Rule-1b
distance zero. -/
def ArmPositionCenterAttachment (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : RealPosition tree) : Prop :=
  p.1 = rootPosition tree ∨
    ∃ q : Position tree,
      (∃ slot : Nat, q.val = p.1.val ++ [slot]) ∧
        (positionNode q).rule1bDistance = 0

/-- **The stored parent of a non-root real arm position is not the centre.**  The parent is the
previous atom on the position's branch; if it were the centre, the branch history would contain
the centre twice, contradicting the simplicity of the real path. -/
theorem armRealPosition_parent_ne_center
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (armTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {read : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren)
    (rootSource : tree.source = input.localizedLigandRootCursor center index)
    {p : RealPosition tree} (ne : p.1.val ≠ []) :
    (positionNode p.1).source.occurrence.1.node.parent? ≠ some center.1 := by
  let parentPos := positionParent p.1 ne
  obtain ⟨slot, lookup⟩ := positionParent_node_child p.1 ne
  have parentGenerated := generatedOf_subtree input generated (positionNode_spec parentPos)
  have childMem : (positionNode p.1).source.occurrence.1.node ∈
      input.executableOfficialCIPChildren
        (positionNode parentPos).source.occurrence.1.node := by
    have genPerm := generatedBy_perm_of_generated input parentGenerated
    have inMap : (positionNode p.1).source.occurrence.1.node ∈
        (LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList
          (positionNode parentPos).children).map
          OfficialCIPSourceTree.source := by
      rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_eq_map]
      exact List.mem_map.mpr ⟨LocalizedCumulativeDecoratedTree.toOfficialSourceTree
        (positionNode p.1),
        List.mem_map.mpr ⟨positionNode p.1, List.mem_of_getElem? lookup, rfl⟩,
        LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source (positionNode p.1)⟩
    exact genPerm.mem_iff.mp inMap
  have visibleParent := armTreeVisible_of_position input center index singleBonded armTree
    realizes generated rootSource parentPos
  have parentReal : (positionNode parentPos).source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom :=
    armTreeVisible_provenance_real_of_childMem input center index visibleParent
      ⟨(positionNode p.1).source.occurrence.1.node, childMem⟩
  have parentRealPath := visibleParent.real_path parentReal
  obtain ⟨next, copyIndex, childExtend⟩ :=
    input.mem_executableOfficialCIPChildren_extend
      (positionNode parentPos).source.occurrence.1.node
      (positionNode p.1).source.occurrence.1.node childMem
  have parentHeadObserved : (positionNode parentPos).source.occurrence.1.node.history.head? =
      some (nodeCurrent (positionNode parentPos)) := by
    obtain ⟨current, _path, currentObserved, headObserved, _prov, _isPath, _supp, _pen⟩ :=
      parentRealPath
    have currentEq : current = nodeCurrent (positionNode parentPos) :=
      Option.some.inj (currentObserved.symm.trans (nodeCurrent_spec (positionNode parentPos)))
    rw [← currentEq]
    exact headObserved
  have parentObserved : (positionNode p.1).source.occurrence.1.node.parent? =
      some (nodeCurrent (positionNode parentPos)) := by
    rw [childExtend]
    cases hhist : (positionNode parentPos).source.occurrence.1.node.history with
    | nil =>
        obtain ⟨t, ht⟩ := visibleParent.suffix
        rw [hhist] at ht
        have hlen : (t ++ [input.canonicalLigandAtom center index, center.1]).length = 0 := by
          simpa using congrArg List.length ht
        simp at hlen
    | cons first rest =>
        have firstEq : first = nodeCurrent (positionNode parentPos) := by
          have := parentHeadObserved
          rw [hhist] at this
          simpa using this
        cases hrest : rest with
        | nil =>
            obtain ⟨t, ht⟩ := visibleParent.suffix
            rw [hhist, hrest] at ht
            have hlen :
                (t ++ [input.canonicalLigandAtom center index, center.1]).length =
                  (first :: []).length := by
              exact congrArg List.length ht
            simp at hlen
        | cons second tail =>
            simp [OfficialCIPNode.parent?, OfficialCIPNode.extend_history, hhist, hrest,
              firstEq]
  have nodeCurrentNeCenter : nodeCurrent (positionNode parentPos) ≠ center.1 := by
    intro hcurrent
    have nodup := input.realPathNode_history_nodup parentRealPath
    have hlast : (positionNode parentPos).source.occurrence.1.node.history.getLast? =
        some center.1 := by
      obtain ⟨t, ht⟩ := visibleParent.suffix
      rw [← ht, List.getLast?_append_cons]
      simp
    have centerInTail : center.1 ∈
        (positionNode parentPos).source.occurrence.1.node.history.tail := by
      cases hhist : (positionNode parentPos).source.occurrence.1.node.history with
      | nil =>
          obtain ⟨t, ht⟩ := visibleParent.suffix
          rw [hhist] at ht
          have hlen :
              (t ++ [input.canonicalLigandAtom center index, center.1]).length = 0 := by
            simpa using congrArg List.length ht
          simp at hlen
      | cons first rest =>
          cases hrest : rest with
          | nil =>
              obtain ⟨t, ht⟩ := visibleParent.suffix
              rw [hhist, hrest] at ht
              have hlen :
                  (t ++ [input.canonicalLigandAtom center index, center.1]).length =
                    (first :: []).length := by
                exact congrArg List.length ht
              simp at hlen
          | cons second tail =>
              have restLast : rest.getLast? = some center.1 := by
                rw [hhist, hrest] at hlast
                rw [List.getLast?_cons_cons] at hlast
                simpa [hrest] using hlast
              simpa [hhist, hrest] using (List.mem_of_mem_getLast? restLast)
    have notNodup : ¬ (positionNode parentPos).source.occurrence.1.node.history.Nodup := by
      intro nodup'
      cases hhist : (positionNode parentPos).source.occurrence.1.node.history with
      | nil =>
          have := parentHeadObserved
          rw [hhist] at this
          simp at this
      | cons first rest =>
          have firstNodeCurrent : first = nodeCurrent (positionNode parentPos) := by
            have := parentHeadObserved
            rw [hhist] at this
            simpa using this
          rw [hhist, List.nodup_cons] at nodup'
          have firstCenter : first = center.1 := firstNodeCurrent.trans hcurrent
          have notMem : center.1 ∉ rest := by
            rw [← firstCenter]
            exact nodup'.1
          exact notMem (by simpa [hhist] using centerInTail)
    exact notNodup nodup
  intro hparent
  have hcurrent : nodeCurrent (positionNode parentPos) = center.1 :=
    Option.some.inj (parentObserved.symm.trans hparent)
  exact nodeCurrentNeCenter hcurrent

/-- **The stored parent of a non-root real position is the parent position's current atom.**  The
child node is an actual executable `extend` of the parent source node (generatedness), and
`extend` stores the parent history head as the immediate stored parent. -/
theorem armRealPosition_parent_current
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (armTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {read : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren)
    (rootSource : tree.source = input.localizedLigandRootCursor center index)
    {p : RealPosition tree} (ne : p.1.val ≠ []) :
    (positionNode p.1).source.occurrence.1.node.parent? =
      some (nodeCurrent (positionNode (positionParent p.1 ne))) := by
  let parentPos := positionParent p.1 ne
  obtain ⟨slot, lookup⟩ := positionParent_node_child p.1 ne
  have parentGenerated := generatedOf_subtree input generated (positionNode_spec parentPos)
  have childMem : (positionNode p.1).source.occurrence.1.node ∈
      input.executableOfficialCIPChildren
        (positionNode parentPos).source.occurrence.1.node := by
    have genPerm := generatedBy_perm_of_generated input parentGenerated
    have inMap : (positionNode p.1).source.occurrence.1.node ∈
        (LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList
          (positionNode parentPos).children).map
          OfficialCIPSourceTree.source := by
      rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_eq_map]
      exact List.mem_map.mpr ⟨LocalizedCumulativeDecoratedTree.toOfficialSourceTree
        (positionNode p.1),
        List.mem_map.mpr ⟨positionNode p.1, List.mem_of_getElem? lookup, rfl⟩,
        LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source (positionNode p.1)⟩
    exact genPerm.mem_iff.mp inMap
  have visibleParent := armTreeVisible_of_position input center index singleBonded armTree
    realizes generated rootSource parentPos
  have parentReal : (positionNode parentPos).source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom :=
    armTreeVisible_provenance_real_of_childMem input center index visibleParent
      ⟨(positionNode p.1).source.occurrence.1.node, childMem⟩
  have parentRealPath := visibleParent.real_path parentReal
  obtain ⟨next, copyIndex, childExtend⟩ :=
    input.mem_executableOfficialCIPChildren_extend
      (positionNode parentPos).source.occurrence.1.node
      (positionNode p.1).source.occurrence.1.node childMem
  have parentHeadObserved : (positionNode parentPos).source.occurrence.1.node.history.head? =
      some (nodeCurrent (positionNode parentPos)) := by
    obtain ⟨current, _path, currentObserved, headObserved, _prov, _isPath, _supp, _pen⟩ :=
      parentRealPath
    have currentEq : current = nodeCurrent (positionNode parentPos) :=
      Option.some.inj (currentObserved.symm.trans (nodeCurrent_spec (positionNode parentPos)))
    rw [← currentEq]
    exact headObserved
  have parentObserved : (positionNode p.1).source.occurrence.1.node.parent? =
      some (nodeCurrent (positionNode parentPos)) := by
    rw [childExtend]
    cases hhist : (positionNode parentPos).source.occurrence.1.node.history with
    | nil =>
        obtain ⟨t, ht⟩ := visibleParent.suffix
        rw [hhist] at ht
        have hlen : (t ++ [input.canonicalLigandAtom center index, center.1]).length = 0 := by
          simpa using congrArg List.length ht
        simp at hlen
    | cons first rest =>
        have firstEq : first = nodeCurrent (positionNode parentPos) := by
          have := parentHeadObserved
          rw [hhist] at this
          simpa using this
        cases hrest : rest with
        | nil =>
            obtain ⟨t, ht⟩ := visibleParent.suffix
            rw [hhist, hrest] at ht
            have hlen :
                (t ++ [input.canonicalLigandAtom center index, center.1]).length =
                  (first :: []).length := by
              exact congrArg List.length ht
            simp at hlen
        | cons second tail =>
            simp [OfficialCIPNode.parent?, OfficialCIPNode.extend_history, hhist, hrest,
              firstEq]
  exact parentObserved

/-- **The centre-attachment marker is the physical centre bond.**  At every real position of an
actual arm expansion, being bonded to the original centre is equivalent to the visible marker:
root position (stored parent edge) or a zero-distance ring child. -/
theorem armRealPosition_centerAttachment_iff
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (armTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {read : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren)
    (rootSource : tree.source = input.localizedLigandRootCursor center index)
    (p : RealPosition tree) :
    input.moleculeGraph.Adj (realPositionAtom p) center.1 ↔
      ArmPositionCenterAttachment input p := by
  constructor
  · intro adjacent
    by_cases pRoot : p.1 = rootPosition tree
    · left
      exact pRoot
    · right
      have ne : p.1.val ≠ [] := by
        intro hval
        exact pRoot (Subtype.ext hval)
      have visible := armTreeVisible_of_position input center index singleBonded armTree
        realizes generated rootSource p.1
      have parentNeCenter :
          (positionNode p.1).source.occurrence.1.node.parent? ≠ some center.1 :=
        armRealPosition_parent_ne_center input center index singleBonded armTree
          realizes generated rootSource ne
      have attached := input.centerArmRealNode_centerAttachment_iff center index armTree
        singleBonded (visible.real_path p.2) visible.suffix (realPositionAtom_spec p)
        parentNeCenter
      obtain ⟨child, childMem, childDistZero⟩ := attached.mpr adjacent
      have childInMap : child ∈
          (LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList
            (positionNode p.1).children).map
            OfficialCIPSourceTree.source :=
        (generatedBy_perm_of_generated input
          (generatedOf_subtree input generated (positionNode_spec p.1))).mem_iff.mpr childMem
      obtain ⟨cTree, cTreeMem, cTreeSrc⟩ := List.mem_map.mp childInMap
      have cTreeMemDecorated : cTree ∈
          (positionNode p.1).children.map
            LocalizedCumulativeDecoratedTree.toOfficialSourceTree := by
        rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_eq_map] at cTreeMem
        exact cTreeMem
      obtain ⟨dTree, dTreeMem, dTreeEq⟩ := List.mem_map.mp cTreeMemDecorated
      obtain ⟨slot', bound', dTreeEq'⟩ := List.mem_iff_getElem.mp dTreeMem
      refine ⟨positionChild p.1 slot' bound', ⟨slot', rfl⟩, ?_⟩
      · have nodeEq : positionNode (positionChild p.1 slot' bound') = dTree := by
          rw [positionNode_positionChild, dTreeEq']
        have columnsEq := (positionNode_columns_eq_officialLabel input realizes
          (positionChild p.1 slot' bound')).2.1
        have srcEq : dTree.source.occurrence.1.node = child := by
          have : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree dTree).source = child := by
            rw [dTreeEq, cTreeSrc]
          exact (LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source dTree).symm.trans
            this
        rw [columnsEq, nodeEq, srcEq]
        exact childDistZero
  · intro marker
    rcases marker with pRoot | ⟨q, ⟨slot, qVal⟩, qDistZero⟩
    · have observed : tree.source.occurrence.1.node.current? =
          some (input.canonicalLigandAtom center index) := by
        rw [rootSource, input.localizedLigandRootCursor_node center index]
        rw [input.localizedLigandRootNode_eq_rootFromEdge center index]
        rfl
      have currentEq : nodeCurrent tree = input.canonicalLigandAtom center index :=
        Option.some.inj ((nodeCurrent_spec tree).symm.trans observed)
      have adj : input.moleculeGraph.Adj (nodeCurrent tree) center.1 := by
        rw [currentEq]
        exact (input.moleculeGraph.adj_symm).mp (input.canonicalLigandAtom_adj center index)
      have pAtomEq : realPositionAtom p = nodeCurrent tree := by
        rw [realPositionAtom, positionCurrent, pRoot, positionNode_rootPosition]
      rw [pAtomEq]
      exact adj
    · have childLookup : (positionNode p.1).children[slot]? = some (positionNode q) := by
        have spec := positionNode_spec q
        rw [qVal, subtreeAt?_append_singleton, positionNode_spec p.1, Option.bind_some] at spec
        exact spec
      have visible := armTreeVisible_of_position input center index singleBonded armTree
        realizes generated rootSource p.1
      have childMem : (positionNode q).source.occurrence.1.node ∈
          input.executableOfficialCIPChildren
            (positionNode p.1).source.occurrence.1.node := by
        have genPerm := generatedBy_perm_of_generated input
          (generatedOf_subtree input generated (positionNode_spec p.1))
        have inMap : (positionNode q).source.occurrence.1.node ∈
            (LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList
              (positionNode p.1).children).map
              OfficialCIPSourceTree.source := by
          rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_eq_map]
          exact List.mem_map.mpr ⟨LocalizedCumulativeDecoratedTree.toOfficialSourceTree
            (positionNode q),
            List.mem_map.mpr ⟨positionNode q, List.mem_of_getElem? childLookup, rfl⟩,
            LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source (positionNode q)⟩
        exact genPerm.mem_iff.mp inMap
      have childObserved : (positionNode q).source.occurrence.1.node.current? =
          some (nodeCurrent (positionNode q)) := nodeCurrent_spec (positionNode q)
      have qNodeDistZero :
          (positionNode q).source.occurrence.1.node.rule1bRootDistance = 0 := by
        have columnsEq := (positionNode_columns_eq_officialLabel input realizes q).2.1
        rw [← columnsEq]
        exact qDistZero
      have classified := input.centerArmRealNode_child_classification center index armTree
        singleBonded (visible.real_path p.2) visible.suffix (realPositionAtom_spec p)
        childObserved childMem
      rcases classified with ⟨_realProv, _fresh⟩ | ⟨nextCenter, _dupProv⟩
      · exfalso
        have hpos : 0 < (positionNode q).source.occurrence.1.node.rule1bRootDistance :=
          input.centerArmRealNode_realChild_rule1bDistance_pos center index armTree
            singleBonded (visible.real_path p.2) visible.suffix childObserved childMem _realProv
        omega
      · have adj := input.adj_of_mem_executableOfficialCIPChildren
          (positionNode p.1).source.occurrence.1.node
          (positionNode q).source.occurrence.1.node
          (realPositionAtom p) (nodeCurrent (positionNode q)) (realPositionAtom_spec p)
          childObserved childMem
        rw [nextCenter] at adj
        exact adj

/-- **Real tree-child edges are physical bonds.**  The child source node is an actual executable
child of the parent source node (generatedness), and executable children are adjacent. -/
theorem armRealPosition_child_adjacent
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {read : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (_realizes : LocalizedCumulativeTreeRealizes input read tree)
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren)
    (_rootSource : tree.source = input.localizedLigandRootCursor center index)
    (p c : RealPosition tree) (child : RealPositionChild p c) :
    input.moleculeGraph.Adj (realPositionAtom p) (realPositionAtom c) := by
  obtain ⟨slot, childVal⟩ := child
  have childLookup : (positionNode p.1).children[slot]? = some (positionNode c.1) := by
    have spec := positionNode_spec c.1
    rw [childVal, subtreeAt?_append_singleton, positionNode_spec p.1, Option.bind_some] at spec
    exact spec
  have childMem : (positionNode c.1).source.occurrence.1.node ∈
      input.executableOfficialCIPChildren (positionNode p.1).source.occurrence.1.node := by
    have genPerm := generatedBy_perm_of_generated input
      (generatedOf_subtree input generated (positionNode_spec p.1))
    have inMap : (positionNode c.1).source.occurrence.1.node ∈
        (LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList
          (positionNode p.1).children).map
          OfficialCIPSourceTree.source := by
      rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_eq_map]
      exact List.mem_map.mpr ⟨LocalizedCumulativeDecoratedTree.toOfficialSourceTree
        (positionNode c.1),
        List.mem_map.mpr ⟨positionNode c.1, List.mem_of_getElem? childLookup, rfl⟩,
        LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source (positionNode c.1)⟩
    exact genPerm.mem_iff.mp inMap
  exact input.adj_of_mem_executableOfficialCIPChildren
    (positionNode p.1).source.occurrence.1.node
    (positionNode c.1).source.occurrence.1.node
    (realPositionAtom p) (realPositionAtom c) (realPositionAtom_spec p)
    (realPositionAtom_spec c) childMem

















def centerDeletedComparisonStage : LocalizedCumulativeRule45Stage :=
  LocalizedCumulativeRule45Stage.rule4a



def centerDeletedNoneReader (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel :=
  fun _ => none






structure CenterDeletedRingComparison (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (i j : Fin 4) : Type where
  singleBonded : input.moleculeGraph.SimpleBonded
  armTreeI : input.CenterDeletedComponentTreeAt center.1
    (input.canonicalLigandAtom center i)
  armTreeJ : input.CenterDeletedComponentTreeAt center.1
    (input.canonicalLigandAtom center j)
  compared : input.compareLocalizedConstitutionalCursors?
    (input.localizedLigandRootCursor center i)
    (input.localizedLigandRootCursor center j) = some Ordering.eq
  keyI : input.LocalizedRerootCumulativeRule45Key
  keyJ : input.LocalizedRerootCumulativeRule45Key
  builtI : input.buildLocalizedRerootCumulativeRule45KeyWithRead? centerDeletedComparisonStage
    (centerDeletedNoneReader input) (2 * (input.certified.input.molecule.atomCount + 1 + 1))
    (input.localizedLigandRootCursor center i) = some keyI
  builtJ : input.buildLocalizedRerootCumulativeRule45KeyWithRead? centerDeletedComparisonStage
    (centerDeletedNoneReader input) (2 * (input.certified.input.molecule.atomCount + 1 + 1))
    (input.localizedLigandRootCursor center j) = some keyJ
  decoratedI : LocalizedCumulativeDecoratedTree input
    (input.certified.input.molecule.atomCount + 1)
  decoratedJ : LocalizedCumulativeDecoratedTree input
    (input.certified.input.molecule.atomCount + 1)
  sourceI : decoratedI.source = input.localizedLigandRootCursor center i
  sourceJ : decoratedJ.source = input.localizedLigandRootCursor center j
  tableMatchI : LocalizedCumulativeTreeTableMatch centerDeletedComparisonStage decoratedI keyI
  tableMatchJ : LocalizedCumulativeTreeTableMatch centerDeletedComparisonStage decoratedJ keyJ
  realizesI : LocalizedCumulativeTreeRealizes input (centerDeletedNoneReader input) decoratedI
  realizesJ : LocalizedCumulativeTreeRealizes input (centerDeletedNoneReader input) decoratedJ
  generatedI : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree decoratedI).GeneratedBy
    input.executableOfficialCIPChildren
  generatedJ : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree decoratedJ).GeneratedBy
    input.executableOfficialCIPChildren
  faithfulI : DeclarativeCIP.RootedDigraph.FaithfulExactExpansion input.moleculeGraph center.1
    (input.canonicalLigandAtom center i)
    (LocalizedCumulativeDecoratedTree.toOfficialSourceTree decoratedI).toDeclarativeDigraph
  faithfulJ : DeclarativeCIP.RootedDigraph.FaithfulExactExpansion input.moleculeGraph center.1
    (input.canonicalLigandAtom center j)
    (LocalizedCumulativeDecoratedTree.toOfficialSourceTree decoratedJ).toDeclarativeDigraph
  shapeEq : LocalizedCumulativeDecoratedTree.shape decoratedI =
    LocalizedCumulativeDecoratedTree.shape decoratedJ
  visibleI : ArmTreeVisible input center i decoratedI
  visibleJ : ArmTreeVisible input center j decoratedJ





theorem exists_centerDeletedRingComparison
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (i j : Fin 4)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (armTreeI : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center i))
    (armTreeJ : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center j))
    (compared : input.compareLocalizedConstitutionalCursors?
      (input.localizedLigandRootCursor center i)
      (input.localizedLigandRootCursor center j) = some Ordering.eq) :
    Nonempty (CenterDeletedRingComparison input center i j) := by
  obtain ⟨keyI, builtI, treeI, sourceI, tableMatchI, realizesI, generatedI, _sourceRootI,
      faithfulI⟩ :=
    input.localizedLigandRoot_sourceTree_faithfulExactExpansion center i
      centerDeletedComparisonStage (centerDeletedNoneReader input)
  obtain ⟨keyJ, builtJ, treeJ, sourceJ, tableMatchJ, realizesJ, generatedJ, _sourceRootJ,
      faithfulJ⟩ :=
    input.localizedLigandRoot_sourceTree_faithfulExactExpansion center j
      centerDeletedComparisonStage (centerDeletedNoneReader input)
  have observableEq :=
    constitutionalObservable_eq_of_compareCursors_eq input centerDeletedComparisonStage
      centerDeletedComparisonStage (centerDeletedNoneReader input)
      (centerDeletedNoneReader input) (2 * (input.certified.input.molecule.atomCount + 1 + 1))
      (2 * (input.certified.input.molecule.atomCount + 1 + 1))
      (input.localizedLigandRootCursor center i) (input.localizedLigandRootCursor center j)
      keyI keyJ builtI builtJ compared
  have shapeEq : LocalizedCumulativeDecoratedTree.shape treeI =
      LocalizedCumulativeDecoratedTree.shape treeJ :=
    shape_eq_of_actualComparison input centerDeletedComparisonStage
      centerDeletedComparisonStage treeI treeJ keyI keyJ tableMatchI tableMatchJ observableEq
  refine ⟨?_⟩
  exact
    { singleBonded := singleBonded
      armTreeI := armTreeI
      armTreeJ := armTreeJ
      compared := compared
      keyI := keyI
      keyJ := keyJ
      builtI := builtI
      builtJ := builtJ
      decoratedI := treeI
      decoratedJ := treeJ
      sourceI := sourceI
      sourceJ := sourceJ
      tableMatchI := tableMatchI
      tableMatchJ := tableMatchJ
      realizesI := realizesI
      realizesJ := realizesJ
      generatedI := generatedI
      generatedJ := generatedJ
      faithfulI := faithfulI
      faithfulJ := faithfulJ
      shapeEq := shapeEq
      visibleI := armTreeVisible_of_ligandRootSource input center i sourceI
      visibleJ := armTreeVisible_of_ligandRootSource input center j sourceJ }

/-! ## The actual real-position equivalence -/





theorem centerDeletedRealPosition_real_of_mapped {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j) (p : RealPosition C.decoratedI) :
    PositionReal (shapePositionEquiv C.shapeEq p.1) := by
  have pVisibleI := armTreeVisible_of_position input center i C.singleBonded C.armTreeI
    C.realizesI C.generatedI C.sourceI p.1
  have pVisibleJ := armTreeVisible_of_position input center j C.singleBonded C.armTreeJ
    C.realizesJ C.generatedJ C.sourceJ (shapePositionEquiv C.shapeEq p.1)
  have distPos : 0 < (positionNode p.1).source.occurrence.1.node.rule1bRootDistance :=
    pVisibleI.visible_pos.mpr p.2
  have distEq := shapePositionEquiv_positionNode_rule1bDistance_eq C.shapeEq p.1
  have columnsI := (positionNode_columns_eq_officialLabel input C.realizesI p.1).2.1
  have columnsJ := (positionNode_columns_eq_officialLabel input C.realizesJ
    (shapePositionEquiv C.shapeEq p.1)).2.1
  have distPos' : 0 <
      (positionNode (shapePositionEquiv C.shapeEq p.1)).source.occurrence.1.node.rule1bRootDistance := by
    rw [← columnsJ, distEq, columnsI]
    exact distPos
  exact pVisibleJ.visible_pos.mp distPos'

/-- **Realness is transported back by the visible distance.**  The inverse image of a real
position of the right arm is real on the left arm, by the same argument at `shapeEq.symm`. -/
theorem centerDeletedRealPosition_real_of_mapped_inv {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j) (q : RealPosition C.decoratedJ) :
    PositionReal (shapePositionEquiv C.shapeEq.symm q.1) := by
  have qVisibleJ := armTreeVisible_of_position input center j C.singleBonded C.armTreeJ
    C.realizesJ C.generatedJ C.sourceJ q.1
  have qVisibleI := armTreeVisible_of_position input center i C.singleBonded C.armTreeI
    C.realizesI C.generatedI C.sourceI (shapePositionEquiv C.shapeEq.symm q.1)
  have distPos : 0 < (positionNode q.1).source.occurrence.1.node.rule1bRootDistance :=
    qVisibleJ.visible_pos.mpr q.2
  have distEq := shapePositionEquiv_positionNode_rule1bDistance_eq C.shapeEq.symm q.1
  have columnsJ := (positionNode_columns_eq_officialLabel input C.realizesJ q.1).2.1
  have columnsI := (positionNode_columns_eq_officialLabel input C.realizesI
    (shapePositionEquiv C.shapeEq.symm q.1)).2.1
  have distPos' : 0 <
      (positionNode (shapePositionEquiv C.shapeEq.symm q.1)).source.occurrence.1.node.rule1bRootDistance := by
    rw [← columnsI, distEq, columnsJ]
    exact distPos
  exact qVisibleI.visible_pos.mp distPos'





def centerDeletedRealPositionEquiv {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j) :
    RealPosition C.decoratedI ≃ RealPosition C.decoratedJ where
  toFun p := ⟨shapePositionEquiv C.shapeEq p.1,
    centerDeletedRealPosition_real_of_mapped C p⟩
  invFun q := ⟨shapePositionEquiv C.shapeEq.symm q.1,
    centerDeletedRealPosition_real_of_mapped_inv C q⟩
  left_inv _p := Subtype.ext rfl
  right_inv _q := Subtype.ext rfl

/-- **The root position is exactly transported.**  The image position is the root of the right
tree exactly when the source position is the root of the left tree. -/
theorem centerDeletedRealPosition_root_iff {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j) (p : RealPosition C.decoratedI) :
    (centerDeletedRealPositionEquiv C p).1 = rootPosition C.decoratedJ ↔
      p.1 = rootPosition C.decoratedI := by
  have hmap : (centerDeletedRealPositionEquiv C p).1 = shapePositionEquiv C.shapeEq p.1 := rfl
  rw [hmap]
  constructor
  · intro h
    apply Subtype.ext
    have hval := congrArg (fun q : Position C.decoratedJ => q.val) h
    simpa [shapePositionEquiv_val] using hval
  · intro h
    rw [h]
    exact shapePositionEquiv_rootPosition C.shapeEq

/-! ## Preservation along the real-position equivalence -/




theorem centerDeletedRealPosition_node_columns {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j) (p : RealPosition C.decoratedI) :
    (positionNode ((centerDeletedRealPositionEquiv C p).1)).atomicNumber =
        (positionNode p.1).atomicNumber ∧
      (positionNode ((centerDeletedRealPositionEquiv C p).1)).rule1bDistance =
          (positionNode p.1).rule1bDistance ∧
        (positionNode ((centerDeletedRealPositionEquiv C p).1)).isotopeMass =
            (positionNode p.1).isotopeMass := by
  have hmap : (centerDeletedRealPositionEquiv C p).1 = shapePositionEquiv C.shapeEq p.1 := rfl
  rw [hmap]
  exact ⟨shapePositionEquiv_positionNode_atomicNumber_eq C.shapeEq p.1,
    shapePositionEquiv_positionNode_rule1bDistance_eq C.shapeEq p.1,
    shapePositionEquiv_positionNode_isotopeMass_eq C.shapeEq p.1⟩





theorem centerDeletedRealPosition_officialLabel_columns {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j) (p : RealPosition C.decoratedI) :
    (ofLex (input.moleculeGraph.officialNodeAtomLabel
        (positionNode ((centerDeletedRealPositionEquiv C p).1)).source.occurrence.1.node)).1 =
      (ofLex (input.moleculeGraph.officialNodeAtomLabel
        (positionNode p.1).source.occurrence.1.node)).1 ∧
      (ofLex (input.moleculeGraph.officialNodeAtomLabel
        (positionNode ((centerDeletedRealPositionEquiv C p).1)).source.occurrence.1.node)).2 =
      (ofLex (input.moleculeGraph.officialNodeAtomLabel
        (positionNode p.1).source.occurrence.1.node)).2 := by
  have hmap : (centerDeletedRealPositionEquiv C p).1 = shapePositionEquiv C.shapeEq p.1 := rfl
  rw [hmap]
  have atomicEq := shapePositionEquiv_positionNode_atomicNumber_eq C.shapeEq p.1
  have massEq := shapePositionEquiv_positionNode_isotopeMass_eq C.shapeEq p.1
  have columnsI := positionNode_columns_eq_officialLabel input C.realizesI p.1
  have columnsJ := positionNode_columns_eq_officialLabel input C.realizesJ
    (shapePositionEquiv C.shapeEq p.1)
  exact ⟨columnsJ.1.symm.trans (atomicEq.trans columnsI.1),
    columnsJ.2.2.symm.trans (massEq.trans columnsI.2.2)⟩

/-- **The source-node Rule-1b distance is preserved at every mapped real position.**  The visible
distance of the actual source record — the quantity the Section 1 role laws read — agrees between
a real position and its image. -/
theorem centerDeletedRealPosition_sourceDistance_eq {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j) (p : RealPosition C.decoratedI) :
    (positionNode ((centerDeletedRealPositionEquiv C p).1)).source.occurrence.1.node.rule1bRootDistance =
      (positionNode p.1).source.occurrence.1.node.rule1bRootDistance := by
  have hmap : (centerDeletedRealPositionEquiv C p).1 = shapePositionEquiv C.shapeEq p.1 := rfl
  rw [hmap]
  have distEq := shapePositionEquiv_positionNode_rule1bDistance_eq C.shapeEq p.1
  have columnsI := (positionNode_columns_eq_officialLabel input C.realizesI p.1).2.1
  have columnsJ := (positionNode_columns_eq_officialLabel input C.realizesJ
    (shapePositionEquiv C.shapeEq p.1)).2.1
  exact columnsJ.symm.trans (distEq.trans columnsI)

/-- **Tree child edges are preserved and reflected.**  A real position is an actual sorted child
of another exactly when its image is an actual sorted child of the image, because the raw address
`p.val ++ [slot]` is preserved by both directions. -/
theorem centerDeletedRealPosition_child_iff {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j) (p c : RealPosition C.decoratedI) :
    RealPositionChild (centerDeletedRealPositionEquiv C p)
        (centerDeletedRealPositionEquiv C c) ↔ RealPositionChild p c := by
  constructor
  · intro h
    obtain ⟨slot, hslot⟩ := h
    refine ⟨slot, ?_⟩
    simpa [centerDeletedRealPositionEquiv] using hslot
  · intro h
    obtain ⟨slot, hslot⟩ := h
    refine ⟨slot, ?_⟩
    simpa [centerDeletedRealPositionEquiv] using hslot

/-- **A left tree child edge is a physical bond on the right.**  The child relation transports,
and the Section 3 child-edge lemma gives the physical bond between the image atoms. -/
theorem centerDeletedRealPosition_child_adjacent {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j) (p c : RealPosition C.decoratedI)
    (child : RealPositionChild p c) :
    input.moleculeGraph.Adj
        (realPositionAtom (centerDeletedRealPositionEquiv C p))
        (realPositionAtom (centerDeletedRealPositionEquiv C c)) :=
  armRealPosition_child_adjacent input center j C.realizesJ C.generatedJ C.sourceJ
    (centerDeletedRealPositionEquiv C p) (centerDeletedRealPositionEquiv C c)
    ((centerDeletedRealPosition_child_iff C p c).mp child)

/-- **A right tree child edge is a physical bond on the left.**  The reverse direction of the
child transport, giving the reverse adjacency of the comparison. -/
theorem centerDeletedRealPosition_child_adjacent_inv {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j) (p c : RealPosition C.decoratedI)
    (child : RealPositionChild (centerDeletedRealPositionEquiv C p)
      (centerDeletedRealPositionEquiv C c)) :
    input.moleculeGraph.Adj (realPositionAtom p) (realPositionAtom c) :=
  armRealPosition_child_adjacent input center i C.realizesI C.generatedI C.sourceI p c
    ((centerDeletedRealPosition_child_iff C p c).mpr child)

/-! ## Centre-attachment preservation -/




theorem centerDeletedRealPosition_attachmentMarker_iff {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j) (p : RealPosition C.decoratedI) :
    ArmPositionCenterAttachment input (centerDeletedRealPositionEquiv C p) ↔
      ArmPositionCenterAttachment input p := by
  constructor
  · intro marker
    rcases marker with rootMarker | ⟨q, ⟨slot, qVal⟩, qDistZero⟩
    · left
      exact (centerDeletedRealPosition_root_iff C p).mp rootMarker
    · right
      refine ⟨shapePositionEquiv C.shapeEq.symm q, ⟨slot, ?_⟩, ?_⟩
      · have hmap : (centerDeletedRealPositionEquiv C p).1 =
            shapePositionEquiv C.shapeEq p.1 := rfl
        rw [shapePositionEquiv_val, qVal, hmap, shapePositionEquiv_val]
      · have hdist := shapePositionEquiv_positionNode_rule1bDistance_eq C.shapeEq.symm q
        rw [hdist, qDistZero]
  · intro marker
    rcases marker with rootMarker | ⟨q, ⟨slot, qVal⟩, qDistZero⟩
    · left
      exact (centerDeletedRealPosition_root_iff C p).mpr rootMarker
    · right
      refine ⟨shapePositionEquiv C.shapeEq q, ⟨slot, ?_⟩, ?_⟩
      · have hmap : (centerDeletedRealPositionEquiv C p).1 =
            shapePositionEquiv C.shapeEq p.1 := rfl
        rw [hmap, shapePositionEquiv_val]
        exact qVal
      · have hdist := shapePositionEquiv_positionNode_rule1bDistance_eq C.shapeEq q
        rw [hdist, qDistZero]

/-- **The physical centre bond is preserved and reflected at every real position.**  The physical
bond between a position's atom and the original centre holds exactly when it holds at the image
position: both sides are equivalent to their visible marker (Section 3), and the marker is
transported by the equal-shape address map.  Ring closures through the centre are therefore
*preserved* by the comparison, not discarded. -/
theorem centerDeletedRealPosition_centerAttachment_iff {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j) (p : RealPosition C.decoratedI) :
    input.moleculeGraph.Adj (realPositionAtom (centerDeletedRealPositionEquiv C p)) center.1 ↔
      input.moleculeGraph.Adj (realPositionAtom p) center.1 := by
  have attI := armRealPosition_centerAttachment_iff input center i C.singleBonded C.armTreeI
    C.realizesI C.generatedI C.sourceI p
  have attJ := armRealPosition_centerAttachment_iff input center j C.singleBonded C.armTreeJ
    C.realizesJ C.generatedJ C.sourceJ (centerDeletedRealPositionEquiv C p)
  exact attJ.trans ((centerDeletedRealPosition_attachmentMarker_iff C p).trans attI.symm)















/-! ### Duplicate-free executable children under single bonds -/

open TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage

/-- A sibling slot is determined by its value in a duplicate-free list of children.  Both
memberships give `getElem?` successes at their slots, and the duplicate-free list is injective on
indices. -/
theorem zipIdx_slot_eq_of_nodup {α : Type*} {l : List α} {x y : α} {i j : Nat}
    (nodup : l.Nodup) (memI : (x, i) ∈ l.zipIdx) (memJ : (y, j) ∈ l.zipIdx)
    (eq : x = y) : i = j := by
  have lookupI : l[i]? = some x := List.mk_mem_zipIdx_iff_getElem?.mp memI
  have lookupJ : l[j]? = some y := List.mk_mem_zipIdx_iff_getElem?.mp memJ
  obtain ⟨boundI, getI⟩ := List.getElem?_eq_some_iff.mp lookupI
  obtain ⟨boundJ, getJ⟩ := List.getElem?_eq_some_iff.mp lookupJ
  have inj := List.nodup_iff_injective_getElem.mp nodup
  have finEq : (⟨i, boundI⟩ : Fin l.length) = ⟨j, boundJ⟩ :=
    inj (by simpa [getI, getJ] using eq)
  exact congrArg (fun f : Fin l.length => (f : Nat)) finEq

/-- Two extends of one node are equal only at the same neighbour atom. -/
theorem OfficialCIPNode_extend_neighbor_eq_of_eq {input : CertifiedLocalizedCIPInput}
    {node : OfficialCIPNode input.Atom} {next₁ next₂ : input.Atom} {c₁ c₂ : Nat}
    (eq : node.extend next₁ c₁ = node.extend next₂ c₂) : next₁ = next₂ := by
  have currentEq : (node.extend next₁ c₁).current? = (node.extend next₂ c₂).current? :=
    congrArg (fun n : OfficialCIPNode input.Atom => n.current?) eq
  simpa [OfficialCIPNode.extend] using currentEq

/-- Under `SimpleBonded` every neighbour has bond multiplicity one, so the executable neighbour
copy list carries each adjacent atom exactly once at copy index zero. -/
theorem executableOfficialNeighborCopies_eq_map_of_singleBonded
    (input : CertifiedLocalizedCIPInput) (singleBonded : input.moleculeGraph.SimpleBonded)
    (atom : input.Atom) :
    input.executableOfficialNeighborCopies atom =
      ((input.moleculeGraph.neighborFinset atom).sort (· ≤ ·)).map fun neighbor => (neighbor, 0) := by
  unfold executableOfficialNeighborCopies
  have bondsOne : ∀ neighbor, neighbor ∈ ((input.moleculeGraph.neighborFinset atom).sort (· ≤ ·)) →
      input.moleculeGraph.bond atom neighbor = 1 := by
    intro neighbor mem
    apply singleBonded
    exact (input.moleculeGraph.mem_neighborFinset atom neighbor).mp
      ((Finset.mem_sort (r := (· ≤ ·))).mp mem)
  have hinduct : ∀ l : List input.Atom,
      l ⊆ ((input.moleculeGraph.neighborFinset atom).sort (· ≤ ·)) →
      List.flatMap (fun neighbor => List.map (fun copyIndex => (neighbor, copyIndex))
        (List.range (input.moleculeGraph.bond atom neighbor))) l =
        List.map (fun neighbor => (neighbor, 0)) l := by
    intro l
    induction l with
    | nil =>
        intro _hsub
        rfl
    | cons neighbor rest ih =>
        intro hsub
        rw [List.flatMap_cons, ih (fun n mem => hsub (List.mem_cons_of_mem neighbor mem))]
        simp [bondsOne neighbor (hsub (List.mem_cons_self (a := neighbor) (l := rest)))]
  exact hinduct ((input.moleculeGraph.neighborFinset atom).sort (· ≤ ·)) (fun _n mem => mem)

/-- The executable neighbour copy list is duplicate-free under `SimpleBonded`. -/
theorem executableOfficialNeighborCopies_nodup_of_singleBonded
    (input : CertifiedLocalizedCIPInput) (singleBonded : input.moleculeGraph.SimpleBonded)
    (atom : input.Atom) :
    (input.executableOfficialNeighborCopies atom).Nodup := by
  rw [executableOfficialNeighborCopies_eq_map_of_singleBonded input singleBonded atom]
  apply List.Nodup.map_on
  · intro neighbor₁ _mem₁ neighbor₂ _mem₂ eq
    exact (Prod.ext_iff.mp eq).1
  exact Finset.sort_nodup (input.moleculeGraph.neighborFinset atom) (· ≤ ·)

/-- Every executable neighbour copy carries copy index zero under `SimpleBonded`. -/
theorem snd_eq_zero_of_mem_executableOfficialNeighborCopies_of_singleBonded
    (input : CertifiedLocalizedCIPInput) (singleBonded : input.moleculeGraph.SimpleBonded)
    {atom : input.Atom} {neighbor : input.Atom} {copyIndex : Nat}
    (present : (neighbor, copyIndex) ∈ input.executableOfficialNeighborCopies atom) :
    copyIndex = 0 := by
  rw [executableOfficialNeighborCopies_eq_map_of_singleBonded input singleBonded atom] at present
  obtain ⟨neighbor', _present', pairEq⟩ := List.mem_map.mp present
  exact (congrArg Prod.snd pairEq).symm

/-- Every executable child copy of a node carries copy index zero under `SimpleBonded`. -/
theorem snd_eq_zero_of_mem_executableOfficialChildCopies_of_singleBonded
    (input : CertifiedLocalizedCIPInput) (singleBonded : input.moleculeGraph.SimpleBonded)
    {node : OfficialCIPNode input.Atom} {neighbor : input.Atom} {copyIndex : Nat}
    (present : (neighbor, copyIndex) ∈ input.executableOfficialChildCopies node) :
    copyIndex = 0 := by
  unfold executableOfficialChildCopies at present
  cases hcurrent : node.current? with
  | none => simp [hcurrent] at present
  | some current =>
      cases hparent : node.parent? with
      | none =>
          simp [hcurrent, hparent] at present
          exact snd_eq_zero_of_mem_executableOfficialNeighborCopies_of_singleBonded
            input singleBonded present
      | some parent =>
          simp [hcurrent, hparent] at present
          exact snd_eq_zero_of_mem_executableOfficialNeighborCopies_of_singleBonded
            input singleBonded present.1

/-- The executable child copies of one node are duplicate-free under `SimpleBonded`. -/
theorem executableOfficialChildCopies_nodup_of_singleBonded
    (input : CertifiedLocalizedCIPInput) (singleBonded : input.moleculeGraph.SimpleBonded)
    (node : OfficialCIPNode input.Atom) :
    (input.executableOfficialChildCopies node).Nodup := by
  unfold executableOfficialChildCopies
  cases hcurrent : node.current? with
  | none => simp
  | some current =>
      cases hparent : node.parent? with
      | none => exact executableOfficialNeighborCopies_nodup_of_singleBonded input singleBonded current
      | some parent =>
          exact (executableOfficialNeighborCopies_nodup_of_singleBonded input singleBonded
            current).filter _

/-- **The actual executable children of one node are duplicate-free under `SimpleBonded`.**  Each
neighbour contributes exactly the zero copy, and distinct neighbours extend to distinct child
nodes, so the official child list has no repeats.  This replaces the acyclic child uniqueness of
the earlier cut machinery in the whole position-injectivity argument below. -/
theorem executableOfficialCIPChildren_nodup_of_singleBonded
    (input : CertifiedLocalizedCIPInput) (singleBonded : input.moleculeGraph.SimpleBonded)
    (node : OfficialCIPNode input.Atom) :
    (input.executableOfficialCIPChildren node).Nodup := by
  cases duplicate : node.isDuplicateLeaf with
  | true => simp [executableOfficialCIPChildren, duplicate]
  | false =>
      rw [executableOfficialCIPChildren]
      rw [if_neg]
      · apply List.Nodup.map_on
        · intro copy₁ mem₁ copy₂ mem₂ eq
          rcases copy₁ with ⟨neighbor₁, c₁⟩
          rcases copy₂ with ⟨neighbor₂, c₂⟩
          have neighborEq : neighbor₁ = neighbor₂ :=
            OfficialCIPNode_extend_neighbor_eq_of_eq eq
          have c₁zero : c₁ = 0 := snd_eq_zero_of_mem_executableOfficialChildCopies_of_singleBonded
            input singleBonded mem₁
          have c₂zero : c₂ = 0 := snd_eq_zero_of_mem_executableOfficialChildCopies_of_singleBonded
            input singleBonded mem₂
          simp [neighborEq, c₁zero, c₂zero]
        · exact executableOfficialChildCopies_nodup_of_singleBonded input singleBonded node
      · intro htrue
        rw [duplicate] at htrue
        cases htrue

/-! ### Reverse source membership: the erased source-tree structure -/

/-- A node occurring in one subtree of a forest occurs in the whole forest, with the witness
subtree exposed. -/
theorem exists_of_mem_sourceNodesList {V : Type*} {node : OfficialCIPNode V}
    {trees : List (OfficialCIPSourceTree V)} (present : node ∈ sourceNodesList trees) :
    ∃ subtree : OfficialCIPSourceTree V, subtree ∈ trees ∧ node ∈ sourceNodes subtree := by
  induction trees with
  | nil =>
      change node ∈ [] at present
      cases present
  | cons tree trees ih =>
      change node ∈ sourceNodes tree ++ sourceNodesList trees at present
      rcases List.mem_append.mp present with here | later
      · exact ⟨tree, List.mem_cons_self, here⟩
      · obtain ⟨subtree, subtreeMem, presentIn⟩ := ih later
        exact ⟨subtree, List.mem_cons_of_mem tree subtreeMem, presentIn⟩

/-- The source-node count of a subtree is bounded by the containing forest's total count. -/
theorem sourceNodes_length_le_of_mem {V : Type*} {sub : OfficialCIPSourceTree V}
    {children : List (OfficialCIPSourceTree V)} (mem : sub ∈ children) :
    (sourceNodes sub).length ≤ (sourceNodesList children).length := by
  induction children with
  | nil => simp at mem
  | cons c cs ih =>
      cases List.mem_cons.mp mem with
      | inl same =>
          rw [same]
          change (sourceNodes c).length ≤
            (sourceNodes c ++ sourceNodesList cs).length
          rw [List.length_append]
          omega
      | inr later =>
          have := ih later
          change (sourceNodes sub).length ≤
            (sourceNodes c ++ sourceNodesList cs).length
          rw [List.length_append]
          omega

/-- **Every source node of a generated official source tree continues the stored branch.**  The
subtree root's history is a suffix of every member node's history, because every generated edge
is an `extend` step. -/
theorem history_suffix_of_mem_sourceNodes_of_generated
    (input : CertifiedLocalizedCIPInput) :
    ∀ (tree : OfficialCIPSourceTree input.Atom),
      tree.GeneratedBy input.executableOfficialCIPChildren →
        ∀ n : OfficialCIPNode input.Atom, n ∈ sourceNodes tree →
          tree.source.history <:+ n.history
  | .node source children, generated, n, present => by
      change n ∈ source :: sourceNodesList children at present
      rcases List.mem_cons.mp present with same | below
      · subst same
        rfl
      · obtain ⟨sub, subMem, presentIn⟩ := exists_of_mem_sourceNodesList below
        unfold OfficialCIPSourceTree.GeneratedBy at generated
        have subGenerated := (OfficialCIPSourceTree.forestGeneratedBy_iff_forall
          input.executableOfficialCIPChildren children).mp generated.2 sub subMem
        have subSourceChild : sub.source ∈ input.executableOfficialCIPChildren source :=
          generated.1.mem_iff.mp (List.mem_map.mpr ⟨sub, subMem, rfl⟩)
        obtain ⟨next, copyIndex, subExtend⟩ :=
          input.mem_executableOfficialCIPChildren_extend source sub.source subSourceChild
        have ih' := history_suffix_of_mem_sourceNodes_of_generated input sub subGenerated n presentIn
        rw [subExtend, OfficialCIPNode.extend_history] at ih'
        exact List.IsSuffix.trans
          (⟨[next], rfl⟩ : source.history <:+ next :: source.history) ih'
termination_by tree => (sourceNodes tree).length
decreasing_by
  have h := sourceNodes_length_le_of_mem (V := input.Atom) subMem
  change (sourceNodes sub).length < (source :: sourceNodesList children).length
  rw [List.length_cons]
  omega

/-! ### Direction A: real positions are actual source records -/

/-- **Membership direction of the address bridge.**  The source node stored at any actual
subtree address is a source node of the erased tree: the lookup descends through the decorated
children, and `sourceNodes` collects exactly the erasures of those children in order. -/
theorem centerDeleted_mem_sourceNodes_of_subtreeAt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
      (path : List Nat) {node : LocalizedCumulativeDecoratedTree input carrierFuel},
      subtreeAt? tree path = some node →
        node.source.occurrence.1.node ∈
          sourceNodes (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree) := by
  intro tree path
  induction path generalizing tree with
  | nil =>
      intro node lookup
      have nodeEq : node = tree := (Option.some.inj (by simpa using lookup)).symm
      rw [nodeEq, ← LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source]
      cases LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree with
      | node source children =>
          change source ∈ source :: sourceNodesList children
          exact List.mem_cons_self
  | cons slot rest ih =>
      intro node lookup
      rw [subtreeAt?_cons_eq_some_iff] at lookup
      obtain ⟨child, childLookup, restLookup⟩ := lookup
      have presentIn := ih restLookup
      have childTreeMem : LocalizedCumulativeDecoratedTree.toOfficialSourceTree child ∈
          LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList tree.children := by
        rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_eq_map]
        exact List.mem_map.mpr ⟨child, List.mem_of_getElem? childLookup, rfl⟩
      have presentInList := mem_sourceNodesList_of_mem childTreeMem presentIn
      obtain ⟨source, _atomicNumber, _rule1bDistance, _isotopeMass, _label, children⟩ := tree
      rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTree_mk]
      change node.source.occurrence.1.node ∈ source.occurrence.1.node :: sourceNodesList
        (LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList children)
      exact List.mem_cons_of_mem source.occurrence.1.node presentInList

/-- **A real position is a real arm node record.**  The arm-visible invariant at the position
supplies the real path witness, and the position's own realness supplies the provenance premise. -/
theorem centerDeletedRealArmNode_of_realPosition
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (armTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {read : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren)
    (rootSource : tree.source = input.localizedLigandRootCursor center index)
    (p : RealPosition tree) :
    RealArmNode input center index (positionNode p.1).source.occurrence.1.node := by
  have visible := armTreeVisible_of_position input center index singleBonded armTree
    realizes generated rootSource p.1
  exact ⟨visible.real_path p.2, visible.suffix⟩



noncomputable def centerDeletedRealArmPosition_of_realPosition
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (armTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {read : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren)
    (rootSource : tree.source = input.localizedLigandRootCursor center index)
    (p : RealPosition tree) :
    RealArmPosition input center index
      (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree) :=
  ⟨⟨(positionNode p.1).source.occurrence.1.node,
    realPositionAtom p,
    realPositionAtom_spec p,
    centerDeletedRealArmNode_of_realPosition input center index singleBonded armTree
      realizes generated rootSource p⟩,
  centerDeleted_mem_sourceNodes_of_subtreeAt input p.1.val (positionNode_spec p.1)⟩

/-! ### Direction B: source records are unique actual addresses -/

set_option linter.unusedVariables false in
/-- **Existence direction of the address bridge.**  Every source node of the erased generated
tree is stored at some actual tree address.  The descent follows the source-tree membership into
the child whose erasure contains the node; the measure is the branch history length above the
subtree source, which every `extend` step grows by exactly one. -/
theorem exists_centerDeletedPosition_of_sourceNode
    (input : CertifiedLocalizedCIPInput)
    (fuel : Nat) :
    ∀ (tree : LocalizedCumulativeDecoratedTree input fuel)
      (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
        input.executableOfficialCIPChildren)
      (n : OfficialCIPNode input.Atom),
      n ∈ sourceNodes (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree) →
        ∃ p : Position tree,
          (positionNode p).source.occurrence.1.node = n := by
  have main : ∀ m (tree : LocalizedCumulativeDecoratedTree input fuel)
      (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
        input.executableOfficialCIPChildren)
      (n : OfficialCIPNode input.Atom),
      n.history.length - tree.source.occurrence.1.node.history.length = m →
        n ∈ sourceNodes (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree) →
          ∃ p : Position tree,
            (positionNode p).source.occurrence.1.node = n := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro tree generated n hmeasure present
        by_cases hroot : n = tree.source.occurrence.1.node
        · refine ⟨rootPosition tree, ?_⟩
          simpa [positionNode_rootPosition] using hroot.symm
        · obtain ⟨source, _atomicNumber, _rule1bDistance, _isotopeMass, _label, children⟩ := tree
          let tree : LocalizedCumulativeDecoratedTree input fuel :=
            ⟨source, _atomicNumber, _rule1bDistance, _isotopeMass, _label, children⟩
          rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTree_mk] at present
          change n ∈ source.occurrence.1.node :: sourceNodesList
            (LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList children) at present
          rcases List.mem_cons.mp present with same | below
          · exact False.elim (hroot same)
          · obtain ⟨subtree, subtreeMem, presentIn⟩ := exists_of_mem_sourceNodesList below
            rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_eq_map] at subtreeMem
            obtain ⟨child, childMem, childErased⟩ := List.mem_map.mp subtreeMem
            have childLookup : ∃ slot, children[slot]? = some child :=
              List.mem_iff_getElem?.mp childMem
            obtain ⟨slot, slotLookup⟩ := childLookup
            have childGenerated :
                (LocalizedCumulativeDecoratedTree.toOfficialSourceTree child).GeneratedBy
                  input.executableOfficialCIPChildren :=
              generatedOf_subtree input generated (show subtreeAt? ⟨source, _atomicNumber,
                _rule1bDistance, _isotopeMass, _label, children⟩ [slot] = some child from
                (subtreeAt?_cons_eq_some_iff).mpr ⟨child, slotLookup, subtreeAt?_nil child⟩)
            have childSourceMem : child.source.occurrence.1.node ∈
                input.executableOfficialCIPChildren tree.source.occurrence.1.node := by
              have genPerm := generatedBy_perm_of_generated input generated
              have inMap : child.source.occurrence.1.node ∈
                  (LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList
                    tree.children).map OfficialCIPSourceTree.source := by
                rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_eq_map]
                exact List.mem_map.mpr ⟨LocalizedCumulativeDecoratedTree.toOfficialSourceTree child,
                  List.mem_map.mpr ⟨child, childMem, rfl⟩,
                  LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source child⟩
              exact genPerm.mem_iff.mp inMap
            have childLen : child.source.occurrence.1.node.history.length =
                source.occurrence.1.node.history.length + 1 := by
              obtain ⟨next, copyIndex, childExtend⟩ :=
                input.mem_executableOfficialCIPChildren_extend
                  tree.source.occurrence.1.node child.source.occurrence.1.node childSourceMem
              have hsrc : tree.source.occurrence.1.node = source.occurrence.1.node := rfl
              rw [childExtend, OfficialCIPNode.extend_history_length, hsrc]
            have nLen : child.source.occurrence.1.node.history.length ≤ n.history.length := by
              have suffix := history_suffix_of_mem_sourceNodes_of_generated input
                (LocalizedCumulativeDecoratedTree.toOfficialSourceTree child) childGenerated n
                (by simpa [childErased] using presentIn)
              simpa [LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source child] using
                suffix.length_le
            have hsmall : n.history.length -
                child.source.occurrence.1.node.history.length < m := by
              have hmeasure' : n.history.length -
                  source.occurrence.1.node.history.length = m := by
                simpa using hmeasure
              have hbound : source.occurrence.1.node.history.length + 1 ≤ n.history.length := by
                rw [← childLen]
                exact nLen
              rw [← hmeasure', childLen]
              omega
            obtain ⟨pChild, pNode⟩ :=
              ih (n.history.length - child.source.occurrence.1.node.history.length) hsmall
                child childGenerated n rfl (by simpa [childErased] using presentIn)
            let p : Position tree := ⟨slot :: pChild.val, by
              rw [subtreeAt?_isSome_iff]
              refine ⟨positionNode pChild, ?_⟩
              rw [subtreeAt?_cons_eq_some_iff]
              exact ⟨child, slotLookup, positionNode_spec pChild⟩⟩
            refine ⟨p, ?_⟩
            have pNodeSpec : subtreeAt? tree p.val = some (positionNode p) := positionNode_spec p
            have nodeEq : positionNode p = positionNode pChild := by
              have spec := positionNode_spec pChild
              have full : subtreeAt? tree (slot :: pChild.val) = some (positionNode pChild) := by
                rw [subtreeAt?_cons_eq_some_iff]
                exact ⟨child, slotLookup, spec⟩
              exact Option.some.inj (pNodeSpec.symm.trans full)
            simpa [nodeEq] using pNode
  intro tree generated n present
  exact main (n.history.length - tree.source.occurrence.1.node.history.length)
    tree generated n rfl present

/-- **Direction B of the source-record bridge.**  The actual tree address at which a source node
of the erased generated tree is stored. -/
noncomputable def centerDeletedPosition_of_sourceNode
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input fuel}
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren)
    (n : OfficialCIPNode input.Atom)
    (present : n ∈ sourceNodes (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree)) :
    Position tree :=
  Classical.choose (exists_centerDeletedPosition_of_sourceNode input fuel tree generated n present)

/-- The defining equation of the address bridge: the constructed position stores the node. -/
theorem centerDeletedPosition_of_sourceNode_node
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input fuel}
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren)
    (n : OfficialCIPNode input.Atom)
    (present : n ∈ sourceNodes (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree)) :
    (positionNode (centerDeletedPosition_of_sourceNode input generated n present)).source.occurrence.1.node = n :=
  Classical.choose_spec (exists_centerDeletedPosition_of_sourceNode input fuel tree generated n present)

/-! ### Position injectivity: real node records determine their address -/

set_option linter.unusedVariables false in
/-- **The arm-visible invariant descends along any actual address.**  The visible invariant at
the subtree found at the address follows by descending through the actual children; unlike
`armTreeVisible_of_position` it consumes the invariant of the current tree directly rather than
the ligand-root source equation.  (`realizes`/`generated`/`visible` occur only in the recursive
branch of the induction, so the branch-local unused-variable linter is disabled here.) -/
theorem armTreeVisible_descend
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (armTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {read : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel} :
    ∀ {tree : LocalizedCumulativeDecoratedTree input
        (input.certified.input.molecule.atomCount + 1)}
      (realizes : LocalizedCumulativeTreeRealizes input read tree)
      (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
        input.executableOfficialCIPChildren)
      (visible : ArmTreeVisible input center index tree)
      {path : List Nat} {node : LocalizedCumulativeDecoratedTree input
        (input.certified.input.molecule.atomCount + 1)},
      subtreeAt? tree path = some node →
        ArmTreeVisible input center index node := by
  intro tree realizes generated visible path
  induction path generalizing tree with
  | nil =>
      intro node lookup
      have nodeEq : node = tree := (Option.some.inj (by simpa using lookup)).symm
      rw [nodeEq]
      exact visible
  | cons slot rest ih =>
      intro node lookup
      rw [subtreeAt?_cons_eq_some_iff] at lookup
      obtain ⟨child, childLookup, restLookup⟩ := lookup
      exact ih (realizes_of_child realizes childLookup)
        (generatedOf_subtree input generated (show subtreeAt? tree [slot] = some child from
          (subtreeAt?_cons_eq_some_iff).mpr ⟨child, childLookup, subtreeAt?_nil child⟩))
        (armTreeVisible_of_child input center index singleBonded armTree visible
          realizes generated childLookup) restLookup

/-- **The source-node list of an erased tree with an empty erased forest is its root alone.**  The
erasure of the decorated tree is stuck on the opaque tree argument, so this is stated through the
erased forest equation rather than by unfolding. -/
theorem sourceNodes_of_erased_children_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (childrenNil : LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList tree.children = []) :
    sourceNodes (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree) =
      [tree.source.occurrence.1.node] := by
  cases h : tree with
  | mk source _atomicNumber _rule1bDistance _isotopeMass _label children =>
      rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTree_mk]
      rw [h] at childrenNil
      rw [childrenNil]
      rfl

set_option linter.unusedVariables false in
/-- **A real descendant rules out the centre-closure child role.**  If a source node has a real
arm descendant it cannot be a duplicate leaf, so by the visible role classification it is real. -/
theorem armTreeVisible_provenance_real_of_realDescendant
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (armTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {read : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren)
    (visible : ArmTreeVisible input center index tree)
    {descendant : OfficialCIPNode input.Atom}
    (descendantPresent : descendant ∈ sourceNodes
      (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree))
    (descendantReal : descendant.provenance = OfficialCIPNodeProvenance.realAtom) :
    tree.source.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  cases visible.role with
  | inl realProv => exact realProv
  | inr h =>
      have duplicate : tree.source.occurrence.1.node.isDuplicateLeaf = true := by
        simp [OfficialCIPNode.isDuplicateLeaf, h.1]
      have emptyChildren : input.executableOfficialCIPChildren
          tree.source.occurrence.1.node = [] := by
        simp [executableOfficialCIPChildren, duplicate]
      have perm := generatedBy_perm_of_generated input generated
      have nilPerm : (LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList
          tree.children).map OfficialCIPSourceTree.source = [] := by
        have perm' : List.Perm ((LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList
            tree.children).map OfficialCIPSourceTree.source) [] :=
          perm.trans (by simp [emptyChildren])
        have hlen : ((LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList
            tree.children).map OfficialCIPSourceTree.source).length = 0 :=
          List.Perm.length_eq perm'
        cases h : LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList tree.children with
        | nil => rfl
        | cons a rest =>
            simp [h] at hlen
      have childrenNil : LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList
          tree.children = [] := by
        have hlen : (LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList
            tree.children).length = 0 := by
          rw [← List.length_map]
          exact congrArg List.length nilPerm
        cases h : LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList tree.children with
        | nil => rfl
        | cons a rest =>
            simp [h] at hlen
      have presentForm : descendant ∈ [tree.source.occurrence.1.node] := by
        simpa [sourceNodes_of_erased_children_nil input childrenNil] using descendantPresent
      have descendantEq : descendant = tree.source.occurrence.1.node := by
        simpa using presentForm
      have provEq : descendant.provenance = OfficialCIPNodeProvenance.ringDuplicate 0 := by
        rw [descendantEq]
        exact h.1
      rw [descendantReal] at provEq
      cases provEq

/-- **A non-root position cannot store the root node.**  A position below the root stores a
generated child whose history extends the root history, while the root history is a suffix of
every generated source record; the two facts force equal branch lengths against the `extend`
growth step. -/
theorem centerDeletedRealPosition_root_ne_cons_node
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren)
    {q : Position tree} (qCons : q.val ≠ []) :
    tree.source.occurrence.1.node ≠ (positionNode q).source.occurrence.1.node := by
  intro nodeEq
  cases hq : q.val with
  | nil => exact False.elim (qCons hq)
  | cons slot rest =>
      obtain ⟨child, childLookup, q', _q'val, posEqQ⟩ := exists_child_of_position_cons hq
      have childNodeMem : child.source.occurrence.1.node ∈
          input.executableOfficialCIPChildren tree.source.occurrence.1.node := by
        have genPerm := generatedBy_perm_of_generated input generated
        have inMap : child.source.occurrence.1.node ∈
            (LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList tree.children).map
              OfficialCIPSourceTree.source := by
          rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_eq_map]
          exact List.mem_map.mpr ⟨LocalizedCumulativeDecoratedTree.toOfficialSourceTree child,
            List.mem_map.mpr ⟨child, List.mem_of_getElem? childLookup, rfl⟩,
            LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source child⟩
        exact genPerm.mem_iff.mp inMap
      obtain ⟨next, _copyIndex, childExtend⟩ :=
        input.mem_executableOfficialCIPChildren_extend tree.source.occurrence.1.node
          child.source.occurrence.1.node childNodeMem
      have childLen : child.source.occurrence.1.node.history.length =
          tree.source.occurrence.1.node.history.length + 1 := by
        rw [childExtend, OfficialCIPNode.extend_history_length]
      have qNodeEq : (positionNode q).source.occurrence.1.node =
          (positionNode q').source.occurrence.1.node := by
        rw [posEqQ]
      have childGenerated :
          (LocalizedCumulativeDecoratedTree.toOfficialSourceTree child).GeneratedBy
            input.executableOfficialCIPChildren :=
        generatedOf_subtree input generated (show subtreeAt? tree [slot] = some child from
          (subtreeAt?_cons_eq_some_iff).mpr ⟨child, childLookup, subtreeAt?_nil child⟩)
      have memQ : (positionNode q').source.occurrence.1.node ∈ sourceNodes
          (LocalizedCumulativeDecoratedTree.toOfficialSourceTree child) :=
        centerDeleted_mem_sourceNodes_of_subtreeAt input q'.val (positionNode_spec q')
      have suffixQ := history_suffix_of_mem_sourceNodes_of_generated input
        (LocalizedCumulativeDecoratedTree.toOfficialSourceTree child)
        childGenerated (positionNode q').source.occurrence.1.node memQ
      have nodeQLen : child.source.occurrence.1.node.history.length ≤
          (positionNode q').source.occurrence.1.node.history.length := by
        obtain ⟨pre, hpre⟩ := suffixQ
        rw [← hpre, List.length_append]
        simp [LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source child]
      have lenEq : tree.source.occurrence.1.node.history.length =
          (positionNode q').source.occurrence.1.node.history.length := by
        exact congrArg (fun n : OfficialCIPNode input.Atom => n.history.length)
          (nodeEq.trans qNodeEq)
      omega

set_option linter.unusedVariables false in
/-- **Real position injectivity by stored node.**  Distinct real positions of one actual realized
arm tree store distinct source nodes: the node record determines the address.  The proof recurses
on the total sibling-slot length; the equal-slot step descends, and the distinct-slot step forces
the two child nodes to extend the parent at the same fresh path successor, so the duplicate-free
executable child enumeration (`SimpleBonded`) identifies the slots.  No whole-molecule acyclicity
and no address fibre is assumed. -/
theorem centerDeletedRealPosition_eq_of_node_eq
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (armTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {read : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    (bound : Nat) :
    ∀ (tree : LocalizedCumulativeDecoratedTree input
        (input.certified.input.molecule.atomCount + 1))
      (realizes : LocalizedCumulativeTreeRealizes input read tree)
      (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
        input.executableOfficialCIPChildren)
      (visible : ArmTreeVisible input center index tree)
      (p q : RealPosition tree),
      p.1.val.length + q.1.val.length ≤ bound →
        (positionNode p.1).source.occurrence.1.node =
            (positionNode q.1).source.occurrence.1.node → p = q := by
  induction bound using Nat.strong_induction_on with
  | h bound ih =>
      intro tree realizes generated visible p q hle nodeEq
      cases hp : p.1.val with
      | nil =>
          cases hq : q.1.val with
          | nil => exact Subtype.ext (Subtype.ext (hp.trans hq.symm))
          | cons qSlot qRest =>
              have nodeEq' : tree.source.occurrence.1.node =
                  (positionNode q.1).source.occurrence.1.node := by
                simpa [positionNode_eq_tree_of_val_eq_nil hp] using nodeEq
              have qCons : q.1.val ≠ [] := by rw [hq]; simp
              exact False.elim (centerDeletedRealPosition_root_ne_cons_node input
                generated qCons nodeEq')
      | cons pSlot pRest =>
          cases hq : q.1.val with
          | nil =>
              have nodeEq' : tree.source.occurrence.1.node =
                  (positionNode p.1).source.occurrence.1.node := by
                simpa [positionNode_eq_tree_of_val_eq_nil hq] using nodeEq.symm
              have pCons : p.1.val ≠ [] := by rw [hp]; simp
              exact False.elim (centerDeletedRealPosition_root_ne_cons_node input
                generated pCons nodeEq')
          | cons qSlot qRest =>
              obtain ⟨childP, lookupP, p', p'val, posEqP⟩ :=
                exists_child_of_position_cons hp
              obtain ⟨childQ, lookupQ, q', q'val, posEqQ⟩ :=
                exists_child_of_position_cons hq
              have nodeEq' : (positionNode p').source.occurrence.1.node =
                  (positionNode q').source.occurrence.1.node := by
                simpa [posEqP, posEqQ] using nodeEq
              by_cases hslot : pSlot = qSlot
              · have hslot' : qSlot = pSlot := hslot.symm
                subst hslot'
                have childEq : childQ = childP :=
                  (Option.some.inj (lookupP.symm.trans lookupQ)).symm
                subst childEq
                have realizesChild : LocalizedCumulativeTreeRealizes input read childQ :=
                  realizes_of_child realizes lookupP
                have generatedChild :
                    (LocalizedCumulativeDecoratedTree.toOfficialSourceTree childQ).GeneratedBy
                      input.executableOfficialCIPChildren :=
                  generatedOf_subtree input generated (show subtreeAt? tree [qSlot] =
                      some childQ from
                    (subtreeAt?_cons_eq_some_iff).mpr ⟨childQ, lookupP, subtreeAt?_nil childQ⟩)
                have visibleChild : ArmTreeVisible input center index childQ :=
                  armTreeVisible_of_child input center index singleBonded armTree visible
                    realizes generated lookupP
                let p'Real : RealPosition childQ :=
                  ⟨p', by
                    have hProv : (positionNode p.1).source.occurrence.1.node.provenance =
                        OfficialCIPNodeProvenance.realAtom := p.2
                    unfold PositionReal
                    rw [← posEqP]
                    exact hProv⟩
                let q'Real : RealPosition childQ :=
                  ⟨q', by
                    have hProv : (positionNode q.1).source.occurrence.1.node.provenance =
                        OfficialCIPNodeProvenance.realAtom := q.2
                    unfold PositionReal
                    rw [← posEqQ]
                    exact hProv⟩
                have hsmall : p'.val.length + q'.val.length < bound := by
                  rw [p'val, q'val]
                  have hle' : Nat.succ pRest.length + Nat.succ qRest.length ≤ bound := by
                    simpa [hp, hq] using hle
                  omega
                have p'eq := ih (p'.val.length + q'.val.length) hsmall childQ realizesChild
                  generatedChild visibleChild p'Real q'Real le_rfl nodeEq'
                have restEq : pRest = qRest := by
                  have h := congrArg (fun r : RealPosition childQ => r.1.val) p'eq
                  change p'.val = q'.val at h
                  rw [p'val, q'val] at h
                  exact h
                exact Subtype.ext (Subtype.ext (by rw [hp, hq, restEq]))
              · have memP : (positionNode p').source.occurrence.1.node ∈ sourceNodes
                    (LocalizedCumulativeDecoratedTree.toOfficialSourceTree childP) :=
                  centerDeleted_mem_sourceNodes_of_subtreeAt input p'.val (positionNode_spec p')
                have memQ : (positionNode q').source.occurrence.1.node ∈ sourceNodes
                    (LocalizedCumulativeDecoratedTree.toOfficialSourceTree childQ) :=
                  centerDeleted_mem_sourceNodes_of_subtreeAt input q'.val (positionNode_spec q')
                have realizesP := realizes_of_child realizes lookupP
                have realizesQ := realizes_of_child realizes lookupQ
                have generatedP := generatedOf_subtree input generated
                  (show subtreeAt? tree [pSlot] = some childP from
                    (subtreeAt?_cons_eq_some_iff).mpr ⟨childP, lookupP, subtreeAt?_nil childP⟩)
                have generatedQ := generatedOf_subtree input generated
                  (show subtreeAt? tree [qSlot] = some childQ from
                    (subtreeAt?_cons_eq_some_iff).mpr ⟨childQ, lookupQ, subtreeAt?_nil childQ⟩)
                have visibleP := armTreeVisible_of_child input center index singleBonded
                  armTree visible realizes generated lookupP
                have visibleQ := armTreeVisible_of_child input center index singleBonded
                  armTree visible realizes generated lookupQ
                have childNodeMemP : childP.source.occurrence.1.node ∈
                    input.executableOfficialCIPChildren tree.source.occurrence.1.node := by
                  have genPerm := generatedBy_perm_of_generated input generated
                  have inMap : childP.source.occurrence.1.node ∈
                      (LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList
                        tree.children).map OfficialCIPSourceTree.source := by
                    rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_eq_map]
                    exact List.mem_map.mpr ⟨LocalizedCumulativeDecoratedTree.toOfficialSourceTree
                      childP,
                      List.mem_map.mpr ⟨childP, List.mem_of_getElem? lookupP, rfl⟩,
                      LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source childP⟩
                  exact genPerm.mem_iff.mp inMap
                have childNodeMemQ : childQ.source.occurrence.1.node ∈
                    input.executableOfficialCIPChildren tree.source.occurrence.1.node := by
                  have genPerm := generatedBy_perm_of_generated input generated
                  have inMap : childQ.source.occurrence.1.node ∈
                      (LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList
                        tree.children).map OfficialCIPSourceTree.source := by
                    rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_eq_map]
                    exact List.mem_map.mpr ⟨LocalizedCumulativeDecoratedTree.toOfficialSourceTree
                      childQ,
                      List.mem_map.mpr ⟨childQ, List.mem_of_getElem? lookupQ, rfl⟩,
                      LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source childQ⟩
                  exact genPerm.mem_iff.mp inMap
                obtain ⟨nextP, _copyP, childPExtend⟩ :=
                  input.mem_executableOfficialCIPChildren_extend tree.source.occurrence.1.node
                    childP.source.occurrence.1.node childNodeMemP
                obtain ⟨nextQ, _copyQ, childQExtend⟩ :=
                  input.mem_executableOfficialCIPChildren_extend tree.source.occurrence.1.node
                    childQ.source.occurrence.1.node childNodeMemQ
                have suffixP := history_suffix_of_mem_sourceNodes_of_generated input
                  (LocalizedCumulativeDecoratedTree.toOfficialSourceTree childP)
                  generatedP (positionNode p').source.occurrence.1.node memP
                have suffixQ := history_suffix_of_mem_sourceNodes_of_generated input
                  (LocalizedCumulativeDecoratedTree.toOfficialSourceTree childQ)
                  generatedQ (positionNode q').source.occurrence.1.node memQ
                obtain ⟨preP, prePEq⟩ := suffixP
                obtain ⟨preQ, preQEq⟩ := suffixQ
                have histP : (positionNode p').source.occurrence.1.node.history =
                    preP ++ nextP :: tree.source.occurrence.1.node.history := by
                  rw [← prePEq, LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source childP,
                    childPExtend, OfficialCIPNode.extend_history]
                have histQ : (positionNode q').source.occurrence.1.node.history =
                    preQ ++ nextQ :: tree.source.occurrence.1.node.history := by
                  rw [← preQEq, LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source childQ,
                    childQExtend, OfficialCIPNode.extend_history]
                have histEq : preP ++ nextP :: tree.source.occurrence.1.node.history =
                    preQ ++ nextQ :: tree.source.occurrence.1.node.history := by
                  have h := congrArg (fun n : OfficialCIPNode input.Atom => n.history) nodeEq'
                  change (positionNode p').source.occurrence.1.node.history =
                    (positionNode q').source.occurrence.1.node.history at h
                  rw [histP, histQ] at h
                  exact h
                have nextEq : nextP = nextQ := by
                  have hlen := congrArg List.length histEq
                  have hlen' : preP.length + Nat.succ
                      tree.source.occurrence.1.node.history.length =
                      preQ.length + Nat.succ
                        tree.source.occurrence.1.node.history.length := by
                    simpa [List.length_append] using hlen
                  have lenEq : preP.length = preQ.length := by omega
                  have hdrop := congrArg (fun l : List input.Atom => l.drop preP.length) histEq
                  have dropP : (preP ++ nextP :: tree.source.occurrence.1.node.history).drop
                      preP.length = nextP :: tree.source.occurrence.1.node.history := by
                    rw [List.drop_append_of_le_length (by simp)]
                    simp
                  have dropQ : (preQ ++ nextQ :: tree.source.occurrence.1.node.history).drop
                      preP.length = nextQ :: tree.source.occurrence.1.node.history := by
                    rw [List.drop_append_of_le_length (by omega)]
                    simp [lenEq]
                  have hdrop' : nextP :: tree.source.occurrence.1.node.history =
                      nextQ :: tree.source.occurrence.1.node.history := by
                    change List.drop preP.length
                        (preP ++ nextP :: tree.source.occurrence.1.node.history) =
                      List.drop preP.length
                        (preQ ++ nextQ :: tree.source.occurrence.1.node.history) at hdrop
                    rw [dropP, dropQ] at hdrop
                    exact hdrop
                  have hheads := congrArg (fun l : List input.Atom => l.head?) hdrop'
                  exact Option.some.inj (by simpa using hheads)
                have provP : childP.source.occurrence.1.node.provenance =
                    OfficialCIPNodeProvenance.realAtom := by
                  have realN : (positionNode p').source.occurrence.1.node.provenance =
                      OfficialCIPNodeProvenance.realAtom := by
                    have hProv : (positionNode p.1).source.occurrence.1.node.provenance =
                        OfficialCIPNodeProvenance.realAtom := p.2
                    rw [← posEqP]
                    exact hProv
                  exact armTreeVisible_provenance_real_of_realDescendant input center index
                    singleBonded armTree realizesP generatedP visibleP memP realN
                have provQ : childQ.source.occurrence.1.node.provenance =
                    OfficialCIPNodeProvenance.realAtom := by
                  have realN : (positionNode q').source.occurrence.1.node.provenance =
                      OfficialCIPNodeProvenance.realAtom := by
                    have hProv : (positionNode q.1).source.occurrence.1.node.provenance =
                        OfficialCIPNodeProvenance.realAtom := q.2
                    rw [← posEqQ]
                    exact hProv
                  exact armTreeVisible_provenance_real_of_realDescendant input center index
                    singleBonded armTree realizesQ generatedQ visibleQ memQ realN
                have nodeEqChilds : childP.source.occurrence.1.node =
                    childQ.source.occurrence.1.node := by
                  have histEq' : childP.source.occurrence.1.node.history =
                      childQ.source.occurrence.1.node.history := by
                    rw [childPExtend, childQExtend, OfficialCIPNode.extend_history,
                      OfficialCIPNode.extend_history]
                    exact congrArg (fun n => n :: tree.source.occurrence.1.node.history) nextEq
                  have hCur : childP.source.occurrence.1.node.current? =
                      childQ.source.occurrence.1.node.current? := by
                    rw [childPExtend, childQExtend]
                    simp [OfficialCIPNode.extend, nextEq]
                  have hProv : childP.source.occurrence.1.node.provenance =
                      childQ.source.occurrence.1.node.provenance := by
                    rw [provP, provQ]
                  cases hPNode : childP.source.occurrence.1.node with
                  | mk cP hP pP =>
                      cases hQNode : childQ.source.occurrence.1.node with
                      | mk cQ hQ pQ =>
                          rw [hPNode] at hCur
                          rw [hQNode] at hCur
                          change cP = cQ at hCur
                          rw [hPNode] at histEq'
                          rw [hQNode] at histEq'
                          change hP = hQ at histEq'
                          rw [hPNode] at hProv
                          rw [hQNode] at hProv
                          change pP = pQ at hProv
                          rw [hCur, histEq', hProv]
                have mappedNodeListPerm :
                    (tree.children.map fun t => t.source.occurrence.1.node).Perm
                      (input.executableOfficialCIPChildren
                        tree.source.occurrence.1.node) := by
                  rw [← LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_map_source]
                  exact generatedBy_perm_of_generated input generated
                have mappedNodeListNodup :
                    (tree.children.map fun t => t.source.occurrence.1.node).Nodup :=
                  mappedNodeListPerm.nodup_iff.mpr
                    (executableOfficialCIPChildren_nodup_of_singleBonded input singleBonded
                      tree.source.occurrence.1.node)
                have zipP : (childP.source.occurrence.1.node, pSlot) ∈
                    (tree.children.map fun t => t.source.occurrence.1.node).zipIdx :=
                  (List.mk_mem_zipIdx_iff_getElem?).mpr (by
                    rw [List.getElem?_map]
                    simp [lookupP])
                have zipQ : (childQ.source.occurrence.1.node, qSlot) ∈
                    (tree.children.map fun t => t.source.occurrence.1.node).zipIdx :=
                  (List.mk_mem_zipIdx_iff_getElem?).mpr (by
                    rw [List.getElem?_map]
                    simp [lookupQ])
                have slotEq : pSlot = qSlot :=
                  zipIdx_slot_eq_of_nodup mappedNodeListNodup zipP zipQ nodeEqChilds
                exact False.elim (hslot slotEq)

/-! ### The real-position / source-record equivalence -/


noncomputable def centerDeletedRealPositionEquivRealArmPosition
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (armTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {read : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren)
    (rootSource : tree.source = input.localizedLigandRootCursor center index) :
    RealPosition tree ≃ RealArmPosition input center index
      (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree) where
  toFun := centerDeletedRealArmPosition_of_realPosition input center index singleBonded armTree
    realizes generated rootSource
  invFun := fun r =>
    ⟨centerDeletedPosition_of_sourceNode input generated r.1.node r.2, by
      obtain ⟨_current, _path, _observed, _head, prov, _simple, _supportReverse, _penultimate⟩ :=
        r.1.real.1
      have nodeEq := centerDeletedPosition_of_sourceNode_node input generated r.1.node r.2
      unfold PositionReal
      rw [nodeEq]
      exact prov⟩
  left_inv := by
    intro p
    apply Subtype.ext
    let toP := centerDeletedRealArmPosition_of_realPosition input center index singleBonded
      armTree realizes generated rootSource p
    let pos := centerDeletedPosition_of_sourceNode input generated toP.1.node toP.2
    have nodeEq' : (positionNode pos).source.occurrence.1.node =
        (positionNode p.1).source.occurrence.1.node := by
      rw [centerDeletedPosition_of_sourceNode_node input generated toP.1.node toP.2]
      rfl
    have provPos : PositionReal pos := by
      obtain ⟨_current, _path, _observed, _head, prov, _simple, _supportReverse,
        _penultimate⟩ := toP.1.real.1
      have nodeEq := centerDeletedPosition_of_sourceNode_node input generated toP.1.node toP.2
      unfold PositionReal
      rw [nodeEq]
      exact prov
    have posEq : (⟨pos, provPos⟩ : RealPosition tree) = p :=
      centerDeletedRealPosition_eq_of_node_eq input center index singleBonded armTree
        (pos.val.length + p.1.val.length) tree realizes generated
        (armTreeVisible_of_ligandRootSource input center index rootSource)
        ⟨pos, provPos⟩ p le_rfl nodeEq'
    exact congrArg (fun r : RealPosition tree => r.1) posEq
  right_inv := by
    intro r
    apply Subtype.ext
    have provPos : PositionReal (centerDeletedPosition_of_sourceNode input generated
        r.1.node r.2) := by
      obtain ⟨_current, _path, _observed, _head, prov, _simple, _supportReverse,
        _penultimate⟩ := r.1.real.1
      have nodeEq := centerDeletedPosition_of_sourceNode_node input generated r.1.node r.2
      unfold PositionReal
      rw [nodeEq]
      exact prov
    have hcur : realPositionAtom (⟨centerDeletedPosition_of_sourceNode input generated
        r.1.node r.2, provPos⟩ : RealPosition tree) = r.1.current := by
      have spec := realPositionAtom_spec (⟨centerDeletedPosition_of_sourceNode input generated
        r.1.node r.2, provPos⟩ : RealPosition tree)
      have nodeEq := centerDeletedPosition_of_sourceNode_node input generated r.1.node r.2
      rw [positionSource] at spec
      rw [nodeEq] at spec
      exact Option.some.inj (spec.symm.trans r.1.currentObserved)
    exact realArmOccurrence_eq_of_current_eq input center index armTree hcur
















theorem centerDeletedRootEq
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (source : tree.source = input.localizedLigandRootCursor center index) :
    (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).source =
      OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center index) := by
  rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source, source]
  change input.localizedLigandRootNode center index =
    OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center index)
  exact input.localizedLigandRootNode_eq_rootFromEdge center index

/-- **The root real position of an actual arm tree.**  The root source has real provenance by the
canonical ligand edge, so the root address is real. -/
noncomputable def centerDeletedRootRealPosition
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (rootSource : tree.source = input.localizedLigandRootCursor center index) :
    RealPosition tree :=
  ⟨rootPosition tree, by
    unfold PositionReal
    rw [positionNode_rootPosition, rootSource,
      input.localizedLigandRootCursor_node center index]
    rw [input.localizedLigandRootNode_eq_rootFromEdge center index]
    rfl⟩

/-- **The root real position observes the canonical ligand atom.** -/
theorem centerDeletedRootRealPosition_atom
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (rootSource : tree.source = input.localizedLigandRootCursor center index) :
    realPositionAtom (centerDeletedRootRealPosition input center index rootSource) =
      input.canonicalLigandAtom center index := by
  have observed : tree.source.occurrence.1.node.current? =
      some (input.canonicalLigandAtom center index) := by
    rw [rootSource, input.localizedLigandRootCursor_node center index]
    rw [input.localizedLigandRootNode_eq_rootFromEdge center index]
    rfl
  have currentEq : nodeCurrent tree = input.canonicalLigandAtom center index :=
    Option.some.inj ((nodeCurrent_spec tree).symm.trans observed)
  rw [realPositionAtom, positionCurrent]
  change nodeCurrent (positionNode (rootPosition tree)) =
    input.canonicalLigandAtom center index
  rw [positionNode_rootPosition]
  exact currentEq




theorem centerDeletedRealArmPosition_of_rootRealPosition
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (armTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {read : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren)
    (rootSource : tree.source = input.localizedLigandRootCursor center index) :
    centerDeletedRealArmPosition_of_realPosition input center index singleBonded armTree
      realizes generated rootSource
      (centerDeletedRootRealPosition input center index rootSource) =
      realArmRootPosition input center index
        (centerDeletedRootEq input center index rootSource) := by
  apply Subtype.ext
  have sameLigand : realPositionAtom
      (centerDeletedRootRealPosition input center index rootSource) =
      input.canonicalLigandAtom center index :=
    centerDeletedRootRealPosition_atom input center index rootSource
  exact realArmOccurrence_eq_root_of_current_eq_ligand input center index armTree sameLigand

/-- **The atom of a bridge-inverse position is the occurrence current.**  The defining equation of
the address bridge and the observation equation of the occurrence identify the atom. -/
theorem centerDeletedRealPosition_atom_of_symm
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (armTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {read : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren)
    (rootSource : tree.source = input.localizedLigandRootCursor center index)
    (r : RealArmPosition input center index
      (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree)) :
    realPositionAtom ((centerDeletedRealPositionEquivRealArmPosition input center index
      singleBonded armTree realizes generated rootSource).symm r) = r.1.current := by
  have provPos : PositionReal (centerDeletedPosition_of_sourceNode input generated
      r.1.node r.2) := by
    obtain ⟨_current, _path, _observed, _head, prov, _simple, _supportReverse,
      _penultimate⟩ := r.1.real.1
    have nodeEq := centerDeletedPosition_of_sourceNode_node input generated r.1.node r.2
    unfold PositionReal
    rw [nodeEq]
    exact prov
  have hcur : realPositionAtom (⟨centerDeletedPosition_of_sourceNode input generated
      r.1.node r.2, provPos⟩ : RealPosition tree) = r.1.current := by
    have spec := realPositionAtom_spec (⟨centerDeletedPosition_of_sourceNode input generated
      r.1.node r.2, provPos⟩ : RealPosition tree)
    have nodeEq := centerDeletedPosition_of_sourceNode_node input generated r.1.node r.2
    rw [positionSource] at spec
    rw [nodeEq] at spec
    exact Option.some.inj (spec.symm.trans r.1.currentObserved)
  change realPositionAtom (⟨centerDeletedPosition_of_sourceNode input generated r.1.node r.2,
    provPos⟩ : RealPosition tree) = r.1.current
  exact hcur

/-- **The carrier inverse observes the carrier atom.**  The chosen covering occurrence of the
carrier atom observes it by the defining specification. -/
theorem realArmPositionOfCarrier_current
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {tree : OfficialCIPSourceTree input.Atom}
    (rootEq : tree.source = OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index))
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren)
    (w : ↥(centerDeletedArmCarrier input center index)) :
    (realArmPositionOfCarrier input center index rootEq generated w).1.current = w.1.1 := by
  unfold realArmPositionOfCarrier
  have hspec := Classical.choose_spec
    (exists_realArmOccurrence_of_mem_carrier input center index rootEq generated w.1 w.2)
  exact hspec.2

/-- **The carrier image observes the occurrence current.** -/
theorem realArmPositionToCarrier_current
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {tree : OfficialCIPSourceTree input.Atom}
    (position : RealArmPosition input center index tree) :
    (realArmPositionToCarrier input center index position).1.1 = position.1.current := rfl




theorem realArmPositionOfCarrier_ligand_eq_root
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (domainTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {tree : OfficialCIPSourceTree input.Atom}
    (rootEq : tree.source = OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index))
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren) :
    realArmPositionOfCarrier input center index rootEq generated
      (⟨⟨input.canonicalLigandAtom center index,
        input.canonicalLigandAtom_ne_center center index⟩,
      ligand_mem_centerDeletedArmCarrier input center index⟩ :
        ↥(centerDeletedArmCarrier input center index)) =
      realArmRootPosition input center index rootEq := by
  unfold realArmPositionOfCarrier realArmRootPosition
  apply Subtype.ext
  let chosen := Classical.choose
    (exists_realArmOccurrence_of_mem_carrier input center index rootEq generated
      (⟨input.canonicalLigandAtom center index,
        input.canonicalLigandAtom_ne_center center index⟩ : {v : input.Atom // v ≠ center.1})
      (ligand_mem_centerDeletedArmCarrier input center index))
  have hspec := Classical.choose_spec
    (exists_realArmOccurrence_of_mem_carrier input center index rootEq generated
      (⟨input.canonicalLigandAtom center index,
        input.canonicalLigandAtom_ne_center center index⟩ : {v : input.Atom // v ≠ center.1})
      (ligand_mem_centerDeletedArmCarrier input center index))
  have sameLigand : chosen.current = input.canonicalLigandAtom center index := hspec.2
  exact realArmOccurrence_eq_root_of_current_eq_ligand input center index domainTree sameLigand

/-- **The official label of a real position is its physical atom record.**  Real provenance makes
the official label the raw Rule-1a/2 pair of the observed atom. -/
theorem centerDeletedRealPosition_atomColumns
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : RealPosition tree) :
    (ofLex (input.moleculeGraph.officialNodeAtomLabel
      (positionNode p.1).source.occurrence.1.node)).1 =
        input.moleculeGraph.atomZ (realPositionAtom p) ∧
      (ofLex (input.moleculeGraph.officialNodeAtomLabel
        (positionNode p.1).source.occurrence.1.node)).2 =
        input.moleculeGraph.atomMass (realPositionAtom p) := by
  have obs := realPositionAtom_spec p
  rw [positionSource] at obs
  have prov : (positionNode p.1).source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom := p.2
  have hlabel : input.moleculeGraph.officialNodeAtomLabel
      (positionNode p.1).source.occurrence.1.node =
      input.moleculeGraph.rawCIPAtomLabel (realPositionAtom p) := by
    unfold MoleculeGraph.officialNodeAtomLabel
    rw [obs, prov]
  constructor
  · rw [hlabel]
    unfold MoleculeGraph.rawCIPAtomLabel
    rfl
  · rw [hlabel]
    unfold MoleculeGraph.rawCIPAtomLabel
    rfl







theorem centerDeletedRealPosition_adjacent_child
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (armTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {read : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (generated : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren)
    (rootSource : tree.source = input.localizedLigandRootCursor center index)
    (p q : RealPosition tree)
    (adjacent : input.moleculeGraph.Adj (realPositionAtom p) (realPositionAtom q)) :
    RealPositionChild p q ∨ RealPositionChild q p := by
  let bridge := centerDeletedRealPositionEquivRealArmPosition input center index singleBonded
    armTree realizes generated rootSource
  let occP : RealArmOccurrence input center index :=
    ⟨(positionNode p.1).source.occurrence.1.node, realPositionAtom p, realPositionAtom_spec p,
      centerDeletedRealArmNode_of_realPosition input center index singleBonded armTree realizes
        generated rootSource p⟩
  let occQ : RealArmOccurrence input center index :=
    ⟨(positionNode q.1).source.occurrence.1.node, realPositionAtom q, realPositionAtom_spec q,
      centerDeletedRealArmNode_of_realPosition input center index singleBonded armTree realizes
        generated rootSource q⟩
  have occPAtom : occP.current = realPositionAtom p := rfl
  have occQAtom : occQ.current = realPositionAtom q := rfl
  have qNeCenter : occQ.current ≠ center.1 :=
    realArmOccurrence_current_ne_center input center index occQ.real.1 occQ.real.2
      occQ.currentObserved
  by_cases hparent : occP.node.parent? = some occQ.current
  · right
    have pNonRoot : p.1.val ≠ [] := by
      intro hval
      have pRootNode : (positionNode p.1).source.occurrence.1.node =
          tree.source.occurrence.1.node := by
        rw [positionNode_eq_tree_of_val_eq_nil hval]
      have rootParent : tree.source.occurrence.1.node.parent? = some center.1 := by
        rw [rootSource, input.localizedLigandRootCursor_node center index]
        rw [input.localizedLigandRootNode_eq_rootFromEdge center index]
        simp [OfficialCIPNode.parent?, OfficialCIPNode.rootFromEdge]
      have currentEqCenter : occQ.current = center.1 :=
        Option.some.inj (hparent.symm.trans (by
          change (positionNode p.1).source.occurrence.1.node.parent? = some center.1
          rw [pRootNode]
          exact rootParent))
      exact qNeCenter currentEqCenter
    let parentPos : Position tree := positionParent p.1 pNonRoot
    have parentObserved : (positionNode p.1).source.occurrence.1.node.parent? =
        some (nodeCurrent (positionNode parentPos)) :=
      armRealPosition_parent_current input center index singleBonded armTree realizes generated
        rootSource pNonRoot
    have parentCurrentEq : nodeCurrent (positionNode parentPos) = realPositionAtom q :=
      Option.some.inj (parentObserved.symm.trans hparent)
    let parentRealPos : RealPosition tree := realPositionParent realizes p pNonRoot
    have parentOccEq : (bridge parentRealPos).1 = (bridge q).1 := by
      apply realArmOccurrence_eq_of_current_eq input center index armTree
      change realPositionAtom parentRealPos = realPositionAtom q
      simpa [realPositionAtom, positionCurrent] using parentCurrentEq
    have bridgeEq : bridge parentRealPos = bridge q := Subtype.ext parentOccEq
    have parentEqPos : parentPos = q.1 := congrArg Subtype.val (bridge.injective bridgeEq)
    have hpval := position_eq_parent_append_last p.1 pNonRoot
    refine ⟨p.1.val.getLast pNonRoot, ?_⟩
    rw [← parentEqPos]
    exact hpval
  · left
    have notVisited : occQ.current ∉ occP.node.history := by
      intro visited
      have qEqCenter : occQ.current = center.1 :=
        input.centerArm_visited_eq_center center index armTree occP.real.1 occP.real.2
          occP.currentObserved visited (by simpa [occPAtom, occQAtom] using adjacent) hparent
      exact qNeCenter qEqCenter
    have childIff := input.centerArmRealNode_realChild_iff center singleBonded
      occP.real.1 occP.currentObserved (occP.node.extend occQ.current 0) occQ.current
    obtain ⟨childMem, childReal, _childObs⟩ :=
      childIff.mpr ⟨notVisited, by simpa [occPAtom, occQAtom] using adjacent, rfl⟩
    have genPerm := generatedBy_perm_of_generated input
      (generatedOf_subtree input generated (positionNode_spec p.1))
    have inMap : occP.node.extend occQ.current 0 ∈
        (LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList
          (positionNode p.1).children).map
          OfficialCIPSourceTree.source :=
      genPerm.mem_iff.mpr childMem
    obtain ⟨cSrc, cSrcMem, cSrcEq⟩ := List.mem_map.mp inMap
    have cSrcMemDecorated : cSrc ∈
        (positionNode p.1).children.map
          LocalizedCumulativeDecoratedTree.toOfficialSourceTree := by
      rw [LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_eq_map] at cSrcMem
      exact cSrcMem
    obtain ⟨dTree, dTreeMem, dTreeEq⟩ := List.mem_map.mp cSrcMemDecorated
    obtain ⟨slot', bound', dTreeEq'⟩ := List.mem_iff_getElem.mp dTreeMem
    let qPos : Position tree := positionChild p.1 slot' bound'
    have dTreeSource : dTree.source.occurrence.1.node = occP.node.extend occQ.current 0 := by
      have hsrc : (LocalizedCumulativeDecoratedTree.toOfficialSourceTree dTree).source =
          occP.node.extend occQ.current 0 := by
        rw [dTreeEq, cSrcEq]
      exact (LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source dTree).symm.trans hsrc
    have qPosNode : (positionNode qPos).source.occurrence.1.node =
        occP.node.extend occQ.current 0 := by
      rw [positionNode_positionChild, dTreeEq']
      exact dTreeSource
    have qPosRealProof : PositionReal qPos := by
      unfold PositionReal
      rw [qPosNode]
      exact childReal
    let qPosReal : RealPosition tree := ⟨qPos, qPosRealProof⟩
    have qPosOccEq : (bridge qPosReal).1 = (bridge q).1 := by
      apply realArmOccurrence_eq_of_current_eq input center index armTree
      change realPositionAtom qPosReal = realPositionAtom q
      have qPosCurrent : (positionNode qPos).source.occurrence.1.node.current? =
          some occQ.current := by
        rw [qPosNode]
        rfl
      have hcurrent : nodeCurrent (positionNode qPos) = occQ.current :=
        Option.some.inj ((nodeCurrent_spec (positionNode qPos)).symm.trans qPosCurrent)
      simpa [realPositionAtom, positionCurrent, occQAtom] using hcurrent
    have bridgeEq : bridge qPosReal = bridge q := Subtype.ext qPosOccEq
    have qEqPos : qPos = q.1 := congrArg Subtype.val (bridge.injective bridgeEq)
    refine ⟨slot', ?_⟩
    rw [← qEqPos]
    rfl



noncomputable def centerDeletedPositionOfCarrier {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j)
    (w : ↥(centerDeletedArmCarrier input center i)) : RealPosition C.decoratedI :=
  (centerDeletedRealPositionEquivRealArmPosition input center i C.singleBonded C.armTreeI
    C.realizesI C.generatedI C.sourceI).symm
    (realArmPositionOfCarrier input center i (centerDeletedRootEq input center i C.sourceI)
      C.generatedI w)




noncomputable def centerDeletedPhysicalComponentEquiv {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j) :
    ↥(centerDeletedArmCarrier input center i) ≃ ↥(centerDeletedArmCarrier input center j) :=
  (realArmPositionEquiv input center i C.armTreeI
    (LocalizedCumulativeDecoratedTree.toOfficialSourceTree C.decoratedI)
    (centerDeletedRootEq input center i C.sourceI) C.generatedI).symm.trans
    ((centerDeletedRealPositionEquivRealArmPosition input center i C.singleBonded C.armTreeI
      C.realizesI C.generatedI C.sourceI).symm.trans
      ((centerDeletedRealPositionEquiv C).trans
        ((centerDeletedRealPositionEquivRealArmPosition input center j C.singleBonded C.armTreeJ
          C.realizesJ C.generatedJ C.sourceJ).trans
          (realArmPositionEquiv input center j C.armTreeJ
            (LocalizedCumulativeDecoratedTree.toOfficialSourceTree C.decoratedJ)
            (centerDeletedRootEq input center j C.sourceJ) C.generatedJ))))




theorem centerDeletedPhysicalComponentEquiv_root {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j) :
    centerDeletedPhysicalComponentEquiv C
      (⟨⟨input.canonicalLigandAtom center i,
        input.canonicalLigandAtom_ne_center center i⟩,
      ligand_mem_centerDeletedArmCarrier input center i⟩ :
        ↥(centerDeletedArmCarrier input center i)) =
      (⟨⟨input.canonicalLigandAtom center j,
        input.canonicalLigandAtom_ne_center center j⟩,
      ligand_mem_centerDeletedArmCarrier input center j⟩ :
        ↥(centerDeletedArmCarrier input center j)) := by
  let wI : ↥(centerDeletedArmCarrier input center i) :=
    ⟨⟨input.canonicalLigandAtom center i, input.canonicalLigandAtom_ne_center center i⟩,
      ligand_mem_centerDeletedArmCarrier input center i⟩
  let wJ : ↥(centerDeletedArmCarrier input center j) :=
    ⟨⟨input.canonicalLigandAtom center j, input.canonicalLigandAtom_ne_center center j⟩,
      ligand_mem_centerDeletedArmCarrier input center j⟩
  have h1 : realArmPositionOfCarrier input center i
      (centerDeletedRootEq input center i C.sourceI) C.generatedI wI =
      realArmRootPosition input center i (centerDeletedRootEq input center i C.sourceI) :=
    realArmPositionOfCarrier_ligand_eq_root input center i C.armTreeI
      (centerDeletedRootEq input center i C.sourceI) C.generatedI
  have h2 : (centerDeletedRealPositionEquivRealArmPosition input center i C.singleBonded
      C.armTreeI C.realizesI C.generatedI C.sourceI).symm
      (realArmRootPosition input center i (centerDeletedRootEq input center i C.sourceI)) =
      centerDeletedRootRealPosition input center i C.sourceI := by
    have hroot := centerDeletedRealArmPosition_of_rootRealPosition input center i C.singleBonded
      C.armTreeI C.realizesI C.generatedI C.sourceI
    rw [← hroot]
    exact (centerDeletedRealPositionEquivRealArmPosition input center i C.singleBonded
      C.armTreeI C.realizesI C.generatedI C.sourceI).left_inv
      (centerDeletedRootRealPosition input center i C.sourceI)
  have h3 : centerDeletedRealPositionEquiv C
      (centerDeletedRootRealPosition input center i C.sourceI) =
      centerDeletedRootRealPosition input center j C.sourceJ := by
    apply Subtype.ext
    exact (centerDeletedRealPosition_root_iff C
      (centerDeletedRootRealPosition input center i C.sourceI)).mpr rfl
  have h4 : centerDeletedRealArmPosition_of_realPosition input center j C.singleBonded C.armTreeJ
      C.realizesJ C.generatedJ C.sourceJ
      (centerDeletedRootRealPosition input center j C.sourceJ) =
      realArmRootPosition input center j (centerDeletedRootEq input center j C.sourceJ) :=
    centerDeletedRealArmPosition_of_rootRealPosition input center j C.singleBonded C.armTreeJ
      C.realizesJ C.generatedJ C.sourceJ
  have h5 : realArmPositionToCarrier input center j
      (realArmRootPosition input center j (centerDeletedRootEq input center j C.sourceJ)) = wJ := by
    apply Subtype.ext
    apply Subtype.ext
    exact realArmPositionToCarrier_rootPosition input center j
      (centerDeletedRootEq input center j C.sourceJ)
  change realArmPositionToCarrier input center j
      (centerDeletedRealArmPosition_of_realPosition input center j C.singleBonded C.armTreeJ
        C.realizesJ C.generatedJ C.sourceJ
        (centerDeletedRealPositionEquiv C
          ((centerDeletedRealPositionEquivRealArmPosition input center i C.singleBonded
            C.armTreeI C.realizesI C.generatedI C.sourceI).symm
            (realArmPositionOfCarrier input center i
              (centerDeletedRootEq input center i C.sourceI) C.generatedI wI)))) = wJ
  rw [h1, h2, h3, h4, h5]




theorem centerDeletedPhysicalComponentEquiv_centerAttachment_iff
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j)
    (w : ↥(centerDeletedArmCarrier input center i)) :
    input.moleculeGraph.Adj (centerDeletedPhysicalComponentEquiv C w).1.1 center.1 ↔
      input.moleculeGraph.Adj w.1.1 center.1 := by
  let pos : RealPosition C.decoratedI := centerDeletedPositionOfCarrier C w
  have hmain := centerDeletedRealPosition_centerAttachment_iff C pos
  have hleft : (centerDeletedPhysicalComponentEquiv C w).1.1 =
      realPositionAtom (centerDeletedRealPositionEquiv C pos) := rfl
  have hright : w.1.1 = realPositionAtom pos := by
    have hcur := centerDeletedRealPosition_atom_of_symm input center i C.singleBonded C.armTreeI
      C.realizesI C.generatedI C.sourceI
      (realArmPositionOfCarrier input center i (centerDeletedRootEq input center i C.sourceI)
        C.generatedI w)
    have hcar := realArmPositionOfCarrier_current input center i
      (centerDeletedRootEq input center i C.sourceI) C.generatedI w
    exact (hcur.trans hcar).symm
  rw [← hleft, ← hright] at hmain
  exact hmain

/-- **The physical carrier equivalence preserves the Rule-1a atomic number.**  The Section 4
official-label transport is pinned to the physical atoms by the real-provenance label reading. -/
theorem centerDeletedPhysicalComponentEquiv_atomZ {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j)
    (w : ↥(centerDeletedArmCarrier input center i)) :
    input.moleculeGraph.atomZ (centerDeletedPhysicalComponentEquiv C w).1.1 =
      input.moleculeGraph.atomZ w.1.1 := by
  let pos : RealPosition C.decoratedI := centerDeletedPositionOfCarrier C w
  have hcols := centerDeletedRealPosition_officialLabel_columns C pos
  have hleft : (ofLex (input.moleculeGraph.officialNodeAtomLabel
      (positionNode ((centerDeletedRealPositionEquiv C pos).1)).source.occurrence.1.node)).1 =
      input.moleculeGraph.atomZ (centerDeletedPhysicalComponentEquiv C w).1.1 := by
    have hb := centerDeletedRealPosition_atomColumns input (centerDeletedRealPositionEquiv C pos)
    have hmapped : realPositionAtom (centerDeletedRealPositionEquiv C pos) =
        (centerDeletedPhysicalComponentEquiv C w).1.1 := rfl
    rw [hmapped] at hb
    exact hb.1
  have hright : (ofLex (input.moleculeGraph.officialNodeAtomLabel
      (positionNode pos.1).source.occurrence.1.node)).1 = input.moleculeGraph.atomZ w.1.1 := by
    have hb := centerDeletedRealPosition_atomColumns input pos
    have hatom : realPositionAtom pos = w.1.1 := by
      have hcur := centerDeletedRealPosition_atom_of_symm input center i C.singleBonded C.armTreeI
        C.realizesI C.generatedI C.sourceI
        (realArmPositionOfCarrier input center i (centerDeletedRootEq input center i C.sourceI)
          C.generatedI w)
      have hcar := realArmPositionOfCarrier_current input center i
        (centerDeletedRootEq input center i C.sourceI) C.generatedI w
      change realPositionAtom (centerDeletedPositionOfCarrier C w) = w.1.1
      exact hcur.trans hcar
    rw [hatom] at hb
    exact hb.1
  exact hleft.symm.trans (hcols.1.trans hright)

/-- **The physical carrier equivalence preserves the Rule-2 isotope mass.** -/
theorem centerDeletedPhysicalComponentEquiv_atomMass {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j)
    (w : ↥(centerDeletedArmCarrier input center i)) :
    input.moleculeGraph.atomMass (centerDeletedPhysicalComponentEquiv C w).1.1 =
      input.moleculeGraph.atomMass w.1.1 := by
  let pos : RealPosition C.decoratedI := centerDeletedPositionOfCarrier C w
  have hcols := centerDeletedRealPosition_officialLabel_columns C pos
  have hleft : (ofLex (input.moleculeGraph.officialNodeAtomLabel
      (positionNode ((centerDeletedRealPositionEquiv C pos).1)).source.occurrence.1.node)).2 =
      input.moleculeGraph.atomMass (centerDeletedPhysicalComponentEquiv C w).1.1 := by
    have hb := centerDeletedRealPosition_atomColumns input (centerDeletedRealPositionEquiv C pos)
    have hmapped : realPositionAtom (centerDeletedRealPositionEquiv C pos) =
        (centerDeletedPhysicalComponentEquiv C w).1.1 := rfl
    rw [hmapped] at hb
    exact hb.2
  have hright : (ofLex (input.moleculeGraph.officialNodeAtomLabel
      (positionNode pos.1).source.occurrence.1.node)).2 = input.moleculeGraph.atomMass w.1.1 := by
    have hb := centerDeletedRealPosition_atomColumns input pos
    have hatom : realPositionAtom pos = w.1.1 := by
      have hcur := centerDeletedRealPosition_atom_of_symm input center i C.singleBonded C.armTreeI
        C.realizesI C.generatedI C.sourceI
        (realArmPositionOfCarrier input center i (centerDeletedRootEq input center i C.sourceI)
          C.generatedI w)
      have hcar := realArmPositionOfCarrier_current input center i
        (centerDeletedRootEq input center i C.sourceI) C.generatedI w
      change realPositionAtom (centerDeletedPositionOfCarrier C w) = w.1.1
      exact hcur.trans hcar
    rw [hatom] at hb
    exact hb.2
  exact hleft.symm.trans (hcols.2.trans hright)

/-- **Internal physical edges of the right carrier are tree child edges of the left arm.**  The
right-atom bond is a tree child edge between the mapped positions (Section 6 reverse adjacency),
which transports back through the Section 4 child equivalence to the left addresses. -/
theorem centerDeletedPhysicalComponentEquiv_adjacent_child
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j)
    (w x : ↥(centerDeletedArmCarrier input center i))
    (adjacent : input.moleculeGraph.Adj (centerDeletedPhysicalComponentEquiv C w).1.1
      (centerDeletedPhysicalComponentEquiv C x).1.1) :
    RealPositionChild (centerDeletedPositionOfCarrier C w) (centerDeletedPositionOfCarrier C x) ∨
      RealPositionChild (centerDeletedPositionOfCarrier C x) (centerDeletedPositionOfCarrier C w) := by
  let posW : RealPosition C.decoratedI := centerDeletedPositionOfCarrier C w
  let posX : RealPosition C.decoratedI := centerDeletedPositionOfCarrier C x
  have hatomW : (centerDeletedPhysicalComponentEquiv C w).1.1 =
      realPositionAtom (centerDeletedRealPositionEquiv C posW) := rfl
  have hatomX : (centerDeletedPhysicalComponentEquiv C x).1.1 =
      realPositionAtom (centerDeletedRealPositionEquiv C posX) := rfl
  have hadj : input.moleculeGraph.Adj
      (realPositionAtom (centerDeletedRealPositionEquiv C posW))
      (realPositionAtom (centerDeletedRealPositionEquiv C posX)) := by
    rw [← hatomW, ← hatomX]
    exact adjacent
  have h := centerDeletedRealPosition_adjacent_child input center j C.singleBonded C.armTreeJ
    C.realizesJ C.generatedJ C.sourceJ (centerDeletedRealPositionEquiv C posW)
    (centerDeletedRealPositionEquiv C posX) hadj
  rcases h with hc | hc
  · left
    exact (centerDeletedRealPosition_child_iff C posW posX).mpr hc
  · right
    exact (centerDeletedRealPosition_child_iff C posX posW).mpr hc

/-- **The actual address of a carrier atom observes that atom.**  The bridge inverse sends the
chosen covering record to the source-record address, and both the inverse-address and the
carrier-observation readings agree with the carrier atom itself. -/
theorem centerDeletedPositionOfCarrier_atom {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j)
    (w : ↥(centerDeletedArmCarrier input center i)) :
    realPositionAtom (centerDeletedPositionOfCarrier C w) = w.1.1 := by
  have hcur := centerDeletedRealPosition_atom_of_symm input center i C.singleBonded C.armTreeI
    C.realizesI C.generatedI C.sourceI
    (realArmPositionOfCarrier input center i (centerDeletedRootEq input center i C.sourceI)
      C.generatedI w)
  have hcar := realArmPositionOfCarrier_current input center i
    (centerDeletedRootEq input center i C.sourceI) C.generatedI w
  change realPositionAtom (centerDeletedPositionOfCarrier C w) = w.1.1
  exact hcur.trans hcar

/-- **The physical component equivalence pulls physical adjacency back.**  Physical adjacency on
the transported arm pulls back through the reverse-adjacency derivation of Section 6 to a tree
child relation on the original arm, and the forward child-adjacency law of Section 3 turns that
stored edge back into the physical bond on the original arm. -/
theorem centerDeletedPhysicalComponentEquiv_adjacent {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j)
    (w x : ↥(centerDeletedArmCarrier input center i))
    (adjacent : input.moleculeGraph.Adj (centerDeletedPhysicalComponentEquiv C w).1.1
      (centerDeletedPhysicalComponentEquiv C x).1.1) :
    input.moleculeGraph.Adj w.1.1 x.1.1 := by
  have hchild := centerDeletedPhysicalComponentEquiv_adjacent_child C w x adjacent
  have hatomW := centerDeletedPositionOfCarrier_atom C w
  have hatomX := centerDeletedPositionOfCarrier_atom C x
  rcases hchild with hc | hc
  · have hadj := centerDeletedRealPosition_child_adjacent_inv C
      (centerDeletedPositionOfCarrier C w) (centerDeletedPositionOfCarrier C x) hc
    rw [hatomW, hatomX] at hadj
    exact hadj
  · have hadj := centerDeletedRealPosition_child_adjacent_inv C
      (centerDeletedPositionOfCarrier C x) (centerDeletedPositionOfCarrier C w) hc
    rw [hatomX, hatomW] at hadj
    exact (input.moleculeGraph.adj_symm).1 hadj

/-- **The physical component equivalence preserves physical adjacency exactly.**  The pull-back
direction is `centerDeletedPhysicalComponentEquiv_adjacent`; the push-forward direction runs the
reverse-adjacency derivation on the original arm (physical bond to tree child), transports the
tree edge through the comparator-tie equivalence, and reads it back as a physical bond with the
forward child-adjacency law on the transported arm.  This is the final adjacency-preservation
assembly of the physical coloured rooted component equivalence, still without any whole-molecule
acyclicity hypothesis. -/
theorem centerDeletedPhysicalComponentEquiv_adjacent_iff {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j)
    (w x : ↥(centerDeletedArmCarrier input center i)) :
    input.moleculeGraph.Adj (centerDeletedPhysicalComponentEquiv C w).1.1
        (centerDeletedPhysicalComponentEquiv C x).1.1 ↔
      input.moleculeGraph.Adj w.1.1 x.1.1 := by
  constructor
  · exact centerDeletedPhysicalComponentEquiv_adjacent C w x
  · intro hadj
    let posW : RealPosition C.decoratedI := centerDeletedPositionOfCarrier C w
    let posX : RealPosition C.decoratedI := centerDeletedPositionOfCarrier C x
    have hatomW : realPositionAtom posW = w.1.1 := centerDeletedPositionOfCarrier_atom C w
    have hatomX : realPositionAtom posX = x.1.1 := centerDeletedPositionOfCarrier_atom C x
    have hchild := centerDeletedRealPosition_adjacent_child input center i C.singleBonded
      C.armTreeI C.realizesI C.generatedI C.sourceI posW posX
      (by rw [← hatomW, ← hatomX] at hadj; exact hadj)
    rcases hchild with hc | hc
    · have hadjR := centerDeletedRealPosition_child_adjacent C posW posX hc
      have hcarW : (centerDeletedPhysicalComponentEquiv C w).1.1 =
          realPositionAtom (centerDeletedRealPositionEquiv C posW) := rfl
      have hcarX : (centerDeletedPhysicalComponentEquiv C x).1.1 =
          realPositionAtom (centerDeletedRealPositionEquiv C posX) := rfl
      rw [← hcarW, ← hcarX] at hadjR
      exact hadjR
    · have hadjR := centerDeletedRealPosition_child_adjacent C posX posW hc
      have hcarW : (centerDeletedPhysicalComponentEquiv C w).1.1 =
          realPositionAtom (centerDeletedRealPositionEquiv C posW) := rfl
      have hcarX : (centerDeletedPhysicalComponentEquiv C x).1.1 =
          realPositionAtom (centerDeletedRealPositionEquiv C posX) := rfl
      rw [← hcarX, ← hcarW] at hadjR
      exact (input.moleculeGraph.adj_symm).1 hadjR







structure CenterDeletedPhysicalComponentIsomorphism
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter) (i j : Fin 4) where
  toEquiv : ↥(centerDeletedArmCarrier input center i) ≃
    ↥(centerDeletedArmCarrier input center j)
  root : toEquiv (⟨⟨input.canonicalLigandAtom center i,
      input.canonicalLigandAtom_ne_center center i⟩,
    ligand_mem_centerDeletedArmCarrier input center i⟩ : ↥(centerDeletedArmCarrier input center i)) =
    (⟨⟨input.canonicalLigandAtom center j,
      input.canonicalLigandAtom_ne_center center j⟩,
    ligand_mem_centerDeletedArmCarrier input center j⟩ : ↥(centerDeletedArmCarrier input center j))
  atomZ : ∀ w : ↥(centerDeletedArmCarrier input center i),
    input.moleculeGraph.atomZ (toEquiv w).1.1 = input.moleculeGraph.atomZ w.1.1
  atomMass : ∀ w : ↥(centerDeletedArmCarrier input center i),
    input.moleculeGraph.atomMass (toEquiv w).1.1 = input.moleculeGraph.atomMass w.1.1
  centerAttachment_iff : ∀ w : ↥(centerDeletedArmCarrier input center i),
    input.moleculeGraph.Adj (toEquiv w).1.1 center.1 ↔ input.moleculeGraph.Adj w.1.1 center.1
  adjacent_iff : ∀ w x : ↥(centerDeletedArmCarrier input center i),
    input.moleculeGraph.Adj (toEquiv w).1.1 (toEquiv x).1.1 ↔
      input.moleculeGraph.Adj w.1.1 x.1.1

/-- **A comparator-tie comparison realizes the full physical isomorphism package.**  All six
fields are the Section 6 preservation laws of `centerDeletedPhysicalComponentEquiv`. -/
noncomputable def centerDeletedPhysicalComponentIsomorphismOfComparison
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {i j : Fin 4}
    (C : CenterDeletedRingComparison input center i j) :
    CenterDeletedPhysicalComponentIsomorphism input center i j where
  toEquiv := centerDeletedPhysicalComponentEquiv C
  root := centerDeletedPhysicalComponentEquiv_root C
  atomZ := centerDeletedPhysicalComponentEquiv_atomZ C
  atomMass := centerDeletedPhysicalComponentEquiv_atomMass C
  centerAttachment_iff := centerDeletedPhysicalComponentEquiv_centerAttachment_iff C
  adjacent_iff := centerDeletedPhysicalComponentEquiv_adjacent_iff C





theorem exists_centerDeletedPhysicalComponentIsomorphism
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {i j : Fin 4}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (armTreeI : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center i))
    (armTreeJ : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center j))
    (compared : input.compareLocalizedConstitutionalCursors?
      (input.localizedLigandRootCursor center i)
      (input.localizedLigandRootCursor center j) = some Ordering.eq) :
    Nonempty (CenterDeletedPhysicalComponentIsomorphism input center i j) := by
  obtain ⟨C⟩ := exists_centerDeletedRingComparison input center i j singleBonded armTreeI
    armTreeJ compared
  exact ⟨centerDeletedPhysicalComponentIsomorphismOfComparison C⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Direct kernel-authority guards

Every public export of this module is checked here against
`TetraStereo.KernelOnly.assert_kernel_only`: only `propext`, `Classical.choice` and `Quot.sound`
may appear in the closure. -/

assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule1bRootDistance_eq_of_provenance_real
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule1bRootDistance_eq_of_provenance_ringDuplicate
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule1bRootDistance_rootFromEdge
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realPathNode_rootFromEdge
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerArmRealNode_realChild_rule1bDistance_pos
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerArmRealNode_child_visibleRole_classification
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ArmTreeVisible
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.armTreeVisible_of_ligandRootSource
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.armTreeVisible_provenance_real_of_childMem
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.armTreeVisible_of_child
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.generatedBy_perm_of_generated
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.generatedBy_forest_of_generated
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.generatedOf_subtree
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.armTreeVisible_of_position
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ArmPositionCenterAttachment
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.armRealPosition_parent_ne_center
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.armRealPosition_centerAttachment_iff
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.armRealPosition_child_adjacent
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedComparisonStage
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedNoneReader
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.CenterDeletedRingComparison
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_centerDeletedRingComparison
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPosition_real_of_mapped
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPosition_real_of_mapped_inv
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPositionEquiv
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPosition_root_iff
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPosition_node_columns
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPosition_officialLabel_columns
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPosition_sourceDistance_eq
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPosition_child_iff
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPosition_child_adjacent
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPosition_child_adjacent_inv
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPosition_attachmentMarker_iff
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPosition_centerAttachment_iff
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.armRealPosition_parent_current
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.zipIdx_slot_eq_of_nodup
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OfficialCIPNode_extend_neighbor_eq_of_eq
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableOfficialNeighborCopies_eq_map_of_singleBonded
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableOfficialNeighborCopies_nodup_of_singleBonded
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.snd_eq_zero_of_mem_executableOfficialNeighborCopies_of_singleBonded
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.snd_eq_zero_of_mem_executableOfficialChildCopies_of_singleBonded
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableOfficialChildCopies_nodup_of_singleBonded
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableOfficialCIPChildren_nodup_of_singleBonded
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_of_mem_sourceNodesList
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sourceNodes_length_le_of_mem
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.history_suffix_of_mem_sourceNodes_of_generated
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeleted_mem_sourceNodes_of_subtreeAt
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealArmNode_of_realPosition
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealArmPosition_of_realPosition
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_centerDeletedPosition_of_sourceNode
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedPosition_of_sourceNode
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedPosition_of_sourceNode_node
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.armTreeVisible_descend
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sourceNodes_of_erased_children_nil
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.armTreeVisible_provenance_real_of_realDescendant
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPosition_root_ne_cons_node
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPosition_eq_of_node_eq
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPositionEquivRealArmPosition
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRootEq
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRootRealPosition
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRootRealPosition_atom
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealArmPosition_of_rootRealPosition
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPosition_atom_of_symm
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realArmPositionOfCarrier_current
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realArmPositionToCarrier_current
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realArmPositionOfCarrier_ligand_eq_root
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPosition_atomColumns
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedRealPosition_adjacent_child
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedPositionOfCarrier
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedPhysicalComponentEquiv
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedPhysicalComponentEquiv_root
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedPhysicalComponentEquiv_centerAttachment_iff
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedPhysicalComponentEquiv_atomZ
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedPhysicalComponentEquiv_atomMass
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedPhysicalComponentEquiv_adjacent_child
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedPositionOfCarrier_atom
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedPhysicalComponentEquiv_adjacent
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedPhysicalComponentEquiv_adjacent_iff
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.CenterDeletedPhysicalComponentIsomorphism
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.centerDeletedPhysicalComponentIsomorphismOfComparison
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_centerDeletedPhysicalComponentIsomorphism
