import TetraStereo.OneCenter.LocalizedMultipleBondRealCutEquivalence
import TetraStereo.KernelOnly

set_option autoImplicit false








































namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
variable {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
variable {tree : LocalizedCumulativeDecoratedTree input carrierFuel}

/-! ## Actual child positions of the real slice -/

/-- **Real child position.**  `q` is the position of an actual sorted child of the decorated node
at `p`, and both positions are real.  This is the tree-side neighbour relation whose physical
counterpart is proved below. -/
def RealPositionChild (p q : RealPosition tree) : Prop :=
  ∃ slot, q.1.val = p.1.val ++ [slot]

/-! ## The root position -/

/-- **The root real position carries the attachment atom.** -/
theorem realPositionAtom_rootPosition
    (startReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    {oAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom) :
    realPositionAtom (⟨rootPosition tree, startReal⟩ : RealPosition tree) = oAtom := by
  have spec := realPositionAtom_spec (⟨rootPosition tree, startReal⟩ : RealPosition tree)
  have spec' : tree.source.occurrence.1.node.current? =
      some (realPositionAtom (⟨rootPosition tree, startReal⟩ : RealPosition tree)) := by
    simpa using spec
  exact Option.some.inj (spec'.symm.trans oObserved)

/-! ## The actual parent real position -/




def realPositionParent
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (p : RealPosition tree) (ne : p.1.val ≠ []) : RealPosition tree :=
  ⟨positionParent p.1 ne, by
    obtain ⟨slot, lookup⟩ := positionParent_node_child p.1 ne
    exact provenance_real_of_executableChild
      (positionNode (positionParent p.1 ne)).source (positionNode p.1).source
      (mem_executable_of_child
        (realizes_of_subtree realizes (positionNode_spec (positionParent p.1 ne))) lookup)⟩

/-- **The recorded incoming occurrence of a nonroot real position is its actual parent
position.**  The occurrence is the parent position's source occurrence, its provenance is real,
and its current atom is exactly the parent position's atom. -/
theorem realPosition_parent_incoming
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (p : RealPosition tree) (ne : p.1.val ≠ []) :
    ∃ previous : input.LocalizedCIPOccurrence carrierFuel,
      (positionNode p.1).source.previous? = some previous ∧
        previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
          previous.1.node.current? =
            some (realPositionAtom (realPositionParent realizes p ne)) := by
  obtain ⟨slot, lookup⟩ := positionParent_node_child p.1 ne
  have realizedParent : LocalizedCumulativeTreeRealizes input read
      (positionNode (positionParent p.1 ne)) :=
    realizes_of_subtree realizes (positionNode_spec (positionParent p.1 ne))
  have previousEq : (positionNode p.1).source.previous? =
      some (positionNode (positionParent p.1 ne)).source.occurrence :=
    child_previous_of_child realizedParent lookup
  refine ⟨(positionNode (positionParent p.1 ne)).source.occurrence, previousEq, ?_, ?_⟩
  · exact (realPositionParent realizes p ne).2
  · exact realPositionAtom_spec (realPositionParent realizes p ne)

/-! ## The reverse adjacency direction -/










theorem exists_realPositionChild_of_adjacent_of_ne
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (p : RealPosition tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : (positionNode p.1).source.previous? = some previous)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {previousAtom : input.Atom}
    (previousObserved : previous.1.node.current? = some previousAtom)
    (incomingRoot : previous.1.root = (positionNode p.1).source.occurrence.1.root)
    {w : input.Atom}
    (adjacent : input.moleculeGraph.Adj (realPositionAtom p) w)
    (wNe : w ≠ previousAtom) :
    ∃ q : RealPosition tree, RealPositionChild p q ∧ realPositionAtom q = w := by
  have realizedNode : LocalizedCumulativeTreeRealizes input read (positionNode p.1) :=
    realizes_of_subtree realizes (positionNode_spec p.1)
  have sourceReal : input.RealPathNode (positionNode p.1).source.occurrence.1.root
      (positionNode p.1).source.occurrence.1.node :=
    input.carrierOccurrence_realPath_of_provenance_real (positionNode p.1).source.occurrence p.2
  have previousRealPath : input.RealPathNode previous.1.root previous.1.node :=
    input.carrierOccurrence_realPath_of_provenance_real previous previousReal
  have localIff :=
    input.localizedRerootChildren?_realChild_exists_iff_adjacent
      (acyclic := acyclic) (enough := enough) (cursor := (positionNode p.1).source)
      (previous := previous) previousEq incomingRoot sourceReal previousRealPath
      (nodeCurrent_spec (positionNode p.1)) previousObserved
      (input.executableLocalizedRerootChildren (positionNode p.1).source)
      (input.localizedRerootChildren?_eq_some_executable (positionNode p.1).source)
  obtain ⟨cursorChild, cursorMem, cursorChildReal, cursorChildCurrent⟩ :=
    (localIff w).mpr ⟨show input.moleculeGraph.Adj (nodeCurrent (positionNode p.1)) w from
      adjacent, wNe⟩
  obtain ⟨perm, _executable⟩ := exists_sourcePerm_executable realizedNode
  have cursorMapMem : cursorChild ∈
      (positionNode p.1).children.map (fun child => child.source) :=
    perm.mem_iff.mpr cursorMem
  obtain ⟨child, childMem, childSource⟩ := List.mem_map.mp cursorMapMem
  obtain ⟨slot, slotBound, slotEq⟩ := List.mem_iff_getElem.mp childMem
  have nodeChild : positionNode (positionChild p.1 slot slotBound) = child := by
    rw [positionNode_positionChild p.1 slot slotBound, slotEq]
  have childReal : PositionReal (positionChild p.1 slot slotBound) := by
    change (positionNode (positionChild p.1 slot slotBound)).source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom
    rw [nodeChild, childSource]
    exact cursorChildReal
  refine ⟨⟨positionChild p.1 slot slotBound, childReal⟩, ⟨slot, rfl⟩, ?_⟩
  change nodeCurrent (positionNode (positionChild p.1 slot slotBound)) = w
  rw [nodeChild]
  show occurrenceCurrent child.source.occurrence = w
  rw [childSource]
  exact occurrenceCurrent_eq_of_observed cursorChildCurrent

/-! ## Disjointness and uniqueness of the two neighbour cases -/




theorem realPositionChild_atom_ne_incoming
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (p q : RealPosition tree) (hchild : RealPositionChild p q)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : (positionNode p.1).source.previous? = some previous)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {previousAtom : input.Atom}
    (previousObserved : previous.1.node.current? = some previousAtom)
    (incomingRoot : previous.1.root = (positionNode p.1).source.occurrence.1.root) :
    realPositionAtom q ≠ previousAtom := by
  obtain ⟨slot, hval⟩ := hchild
  have realizedNode : LocalizedCumulativeTreeRealizes input read (positionNode p.1) :=
    realizes_of_subtree realizes (positionNode_spec p.1)
  have qSpec : subtreeAt? tree (p.1.val ++ [slot]) = some (positionNode q.1) := by
    rw [← hval]
    exact positionNode_spec q.1
  have lookup : (positionNode p.1).children[slot]? = some (positionNode q.1) := by
    have h := subtreeAt?_append_singleton p.1.val tree slot
    rw [positionNode_spec p.1, qSpec] at h
    simpa using h.symm
  have cursorMem : (positionNode q.1).source ∈
      input.executableLocalizedRerootChildren (positionNode p.1).source :=
    mem_executable_of_child realizedNode lookup
  have sourceReal : input.RealPathNode (positionNode p.1).source.occurrence.1.root
      (positionNode p.1).source.occurrence.1.node :=
    input.carrierOccurrence_realPath_of_provenance_real (positionNode p.1).source.occurrence p.2
  have previousRealPath : input.RealPathNode previous.1.root previous.1.node :=
    input.carrierOccurrence_realPath_of_provenance_real previous previousReal
  have localIff :=
    input.localizedRerootChildren?_realChild_exists_iff_adjacent
      (acyclic := acyclic) (enough := enough) (cursor := (positionNode p.1).source)
      (previous := previous) previousEq incomingRoot sourceReal previousRealPath
      (nodeCurrent_spec (positionNode p.1)) previousObserved
      (input.executableLocalizedRerootChildren (positionNode p.1).source)
      (input.localizedRerootChildren?_eq_some_executable (positionNode p.1).source)
  exact ((localIff (realPositionAtom q)).mp
    ⟨(positionNode q.1).source, cursorMem, q.2, nodeCurrent_spec (positionNode q.1)⟩).2



theorem realPositionChild_atom_unique
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (p q₁ q₂ : RealPosition tree)
    (_h₁ : RealPositionChild p q₁) (_h₂ : RealPositionChild p q₂)
    (atomEq : realPositionAtom q₁ = realPositionAtom q₂) :
    q₁ = q₂ :=
  realPosition_injective acyclic enough realizes q₁ q₂ atomEq

/-! ## The neighbor partition -/










theorem realPosition_adjacent_iff_incoming_or_child
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (p : RealPosition tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : (positionNode p.1).source.previous? = some previous)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {previousAtom : input.Atom}
    (previousObserved : previous.1.node.current? = some previousAtom)
    (incomingRoot : previous.1.root = (positionNode p.1).source.occurrence.1.root)
    (incomingAdjacent : input.moleculeGraph.Adj (realPositionAtom p) previousAtom)
    (w : input.Atom) :
    input.moleculeGraph.Adj (realPositionAtom p) w ↔
      w = previousAtom ∨
        ∃ q : RealPosition tree, RealPositionChild p q ∧ realPositionAtom q = w := by
  constructor
  · intro adjacent
    by_cases h : w = previousAtom
    · exact Or.inl h
    · exact Or.inr (exists_realPositionChild_of_adjacent_of_ne acyclic enough realizes p
        previous previousEq previousReal previousObserved incomingRoot adjacent h)
  · rintro (rfl | ⟨q, hchild, rfl⟩)
    · exact incomingAdjacent
    · obtain ⟨slot, hval⟩ := hchild
      exact realPositionAtom_adjacent_of_positionChild realizes p q hval




theorem realPositionAtom_ne_attachment
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (startReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (q : RealPosition tree) :
    realPositionAtom q ≠ pAtom := by
  have mem := realPositionAtom_mem_cutBranch (acyclic := acyclic) (enough := enough) realizes
    previous previousEq valid startReal previousReal oObserved pObserved incomingEdge q
  exact AcyclicCutBranchAutomorphism.cutBranch_ne_center input.moleculeGraph mem

/-- **Neighbor partition at the tree root.**  The root's recorded incoming occurrence is the
external incoming occurrence of the tree source, whose atom is the deleted physical atom `pAtom`.
The neighbors of the root's atom are exactly that external boundary atom and the atoms of actual
real child positions; the boundary atom itself is not the atom of any real position
(`realPositionAtom_ne_attachment`). -/
theorem realPosition_root_neighbor_partition
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    (startReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (w : input.Atom) :
    input.moleculeGraph.Adj
        (realPositionAtom (⟨rootPosition tree, startReal⟩ : RealPosition tree)) w ↔
      w = pAtom ∨
        ∃ q : RealPosition tree,
          RealPositionChild (⟨rootPosition tree, startReal⟩ : RealPosition tree) q ∧
            realPositionAtom q = w := by
  have previousEq' : (positionNode (rootPosition tree) : LocalizedCumulativeDecoratedTree
      input carrierFuel).source.previous? = some previous := by
    simpa using previousEq
  have incomingRoot : previous.1.root =
      (positionNode (rootPosition tree) : LocalizedCumulativeDecoratedTree
        input carrierFuel).source.occurrence.1.root := by
    rw [positionNode_rootPosition]
    exact sameRoot.symm
  have incomingAdjacent : input.moleculeGraph.Adj
      (realPositionAtom (⟨rootPosition tree, startReal⟩ : RealPosition tree)) pAtom := by
    rw [realPositionAtom_rootPosition startReal oObserved]
    exact (input.moleculeGraph.adj_symm).mp incomingEdge
  exact realPosition_adjacent_iff_incoming_or_child acyclic enough realizes
    (⟨rootPosition tree, startReal⟩ : RealPosition tree) previous previousEq' previousReal
    pObserved incomingRoot incomingAdjacent w

/-- **Neighbor partition at a nonroot real position.**  The recorded incoming occurrence is the
actual parent position (`realPosition_parent_incoming`), so the neighbors of the position's atom
are exactly the parent position's atom and the atoms of actual real child positions. -/
theorem realPosition_nonroot_neighbor_partition
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (p : RealPosition tree) (ne : p.1.val ≠ []) (w : input.Atom) :
    input.moleculeGraph.Adj (realPositionAtom p) w ↔
      w = realPositionAtom (realPositionParent realizes p ne) ∨
        ∃ q : RealPosition tree, RealPositionChild p q ∧ realPositionAtom q = w := by
  obtain ⟨slot, lookup⟩ := positionParent_node_child p.1 ne
  have realizedParent : LocalizedCumulativeTreeRealizes input read
      (positionNode (positionParent p.1 ne)) :=
    realizes_of_subtree realizes (positionNode_spec (positionParent p.1 ne))
  have previousEq : (positionNode p.1).source.previous? =
      some (positionNode (positionParent p.1 ne)).source.occurrence :=
    child_previous_of_child realizedParent lookup
  have rootEq : (positionNode p.1).source.occurrence.1.root =
      (positionNode (positionParent p.1 ne)).source.occurrence.1.root :=
    child_root_of_child realizedParent lookup
  have previousReal :
      (positionNode (positionParent p.1 ne)).source.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom :=
    (realPositionParent realizes p ne).2
  have previousObserved :
      (positionNode (positionParent p.1 ne)).source.occurrence.1.node.current? =
        some (realPositionAtom (realPositionParent realizes p ne)) :=
    realPositionAtom_spec (realPositionParent realizes p ne)
  have incomingAdjacent : input.moleculeGraph.Adj (realPositionAtom p)
      (realPositionAtom (realPositionParent realizes p ne)) :=
    (input.moleculeGraph.adj_symm).mp (nodeCurrent_adjacent_of_child realizedParent lookup)
  exact realPosition_adjacent_iff_incoming_or_child acyclic enough realizes p
    (positionNode (positionParent p.1 ne)).source.occurrence previousEq previousReal
    previousObserved rootEq.symm incomingAdjacent w

/-! ## Full adjacency between actual real positions -/








theorem realPosition_adjacent_iff_realPositionChild
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (startReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (p q : RealPosition tree) :
    input.moleculeGraph.Adj (realPositionAtom p) (realPositionAtom q) ↔
      RealPositionChild p q ∨ RealPositionChild q p := by
  constructor
  · intro adjacent
    by_cases hpNil : p.1.val = []
    · have pValEq : p.1 = rootPosition tree := position_ext (by rw [hpNil]; rfl)
      have pEq : p = (⟨rootPosition tree, startReal⟩ : RealPosition tree) :=
        Subtype.ext pValEq
      have partition := realPosition_root_neighbor_partition (acyclic := acyclic)
        (enough := enough) realizes previous previousEq sameRoot startReal previousReal
        oObserved pObserved incomingEdge (realPositionAtom q)
      rcases partition.mp (pEq ▸ adjacent) with hAtom | hChild
      · exact absurd hAtom
          (realPositionAtom_ne_attachment (acyclic := acyclic) (enough := enough) realizes
            previous previousEq valid startReal previousReal oObserved pObserved incomingEdge q)
      · obtain ⟨q', hchild, hAtomEq⟩ := hChild
        have qEq : q' = q := realPosition_injective acyclic enough realizes q' q hAtomEq
        exact Or.inl (pEq.symm ▸ qEq ▸ hchild)
    · let parent : RealPosition tree := realPositionParent realizes p hpNil
      have partition := realPosition_nonroot_neighbor_partition (acyclic := acyclic)
        (enough := enough) realizes p hpNil (realPositionAtom q)
      by_cases hqParent : realPositionAtom q = realPositionAtom parent
      · have qEq : q = parent :=
          realPosition_injective acyclic enough realizes q parent hqParent
        refine Or.inr ⟨p.1.val.getLast hpNil, ?_⟩
        rw [qEq]
        show p.1.val = (positionParent p.1 hpNil).val ++ [p.1.val.getLast hpNil]
        exact position_eq_parent_append_last p.1 hpNil
      · rcases partition.mp adjacent with hIncoming | hChild
        · exact absurd hIncoming hqParent
        · obtain ⟨q', hchild, hAtomEq⟩ := hChild
          have qEq : q' = q := realPosition_injective acyclic enough realizes q' q hAtomEq
          exact Or.inl (qEq ▸ hchild)
  · rintro (hChild | hChild)
    · obtain ⟨slot, hval⟩ := hChild
      exact realPositionAtom_adjacent_of_positionChild realizes p q hval
    · obtain ⟨slot, hval⟩ := hChild
      exact (input.moleculeGraph.adj_symm).mp
        (realPositionAtom_adjacent_of_positionChild realizes q p hval)

/-! ## Transport through the actual cut equivalence -/






theorem realPositionCutEquiv_adj_iff
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (startReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (p q : RealPosition tree) :
    input.moleculeGraph.Adj
        ((realPositionCutEquiv acyclic enough realizes previous previousEq sameRoot valid
          startReal previousReal oObserved pObserved incomingEdge p :
            AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom) :
          input.Atom)
        ((realPositionCutEquiv acyclic enough realizes previous previousEq sameRoot valid
          startReal previousReal oObserved pObserved incomingEdge q :
            AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom) :
          input.Atom) ↔
      RealPositionChild p q ∨ RealPositionChild q p := by
  rw [realPositionCutEquiv_apply_coe, realPositionCutEquiv_apply_coe]
  exact realPosition_adjacent_iff_realPositionChild acyclic enough realizes previous
    previousEq sameRoot valid startReal previousReal oObserved pObserved incomingEdge p q

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.RealPositionChild
assert_kernel_only TetraStereo.OneCenter.realPositionAtom_rootPosition
assert_kernel_only TetraStereo.OneCenter.realPositionParent
assert_kernel_only TetraStereo.OneCenter.realPosition_parent_incoming
assert_kernel_only TetraStereo.OneCenter.exists_realPositionChild_of_adjacent_of_ne
assert_kernel_only TetraStereo.OneCenter.realPositionChild_atom_ne_incoming
assert_kernel_only TetraStereo.OneCenter.realPositionChild_atom_unique
assert_kernel_only TetraStereo.OneCenter.realPosition_adjacent_iff_incoming_or_child
assert_kernel_only TetraStereo.OneCenter.realPositionAtom_ne_attachment
assert_kernel_only TetraStereo.OneCenter.realPosition_root_neighbor_partition
assert_kernel_only TetraStereo.OneCenter.realPosition_nonroot_neighbor_partition
assert_kernel_only TetraStereo.OneCenter.realPosition_adjacent_iff_realPositionChild
assert_kernel_only TetraStereo.OneCenter.realPositionCutEquiv_adj_iff
