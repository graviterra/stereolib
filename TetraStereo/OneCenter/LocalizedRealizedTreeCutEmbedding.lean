import TetraStereo.OneCenter.LocalizedCumulativeTreeObservableFaithfulness
import TetraStereo.OneCenter.LocalizedAcyclicGeneralCutCorrespondence
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput




















variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-! ## Root-first subtree lookup -/

/-- Root-first lookup of the decorated subtree at a sibling-slot path.

`[]` returns the tree itself; `slot :: rest` descends into the actual sorted child at `slot` and
continues in that child.  The lookup is the shared coordinate system of the actual tree. -/
def subtreeAt? (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    List Nat → Option (LocalizedCumulativeDecoratedTree input carrierFuel)
  | [] => some tree
  | slot :: rest => (tree.children[slot]?).bind fun child => subtreeAt? child rest

@[simp] theorem subtreeAt?_nil (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    subtreeAt? tree [] = some tree := rfl

@[simp] theorem subtreeAt?_cons (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (slot : Nat) (rest : List Nat) :
    subtreeAt? tree (slot :: rest) =
      (tree.children[slot]?).bind (fun child => subtreeAt? child rest) := rfl

/-- Lookup along a concatenated path is lookup of the prefix followed by lookup of the suffix. -/
theorem subtreeAt?_append (path₁ path₂ : List Nat)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    subtreeAt? tree (path₁ ++ path₂) =
      (subtreeAt? tree path₁).bind (fun node => subtreeAt? node path₂) := by
  induction path₁ generalizing tree with
  | nil => rfl
  | cons slot rest ih =>
      simp only [List.cons_append, subtreeAt?]
      cases tree.children[slot]? with
      | none => simp
      | some child => simpa using ih child

/-- Appending one slot is lookup of the path, then the child at that slot. -/
theorem subtreeAt?_append_singleton (path : List Nat)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (slot : Nat) :
    subtreeAt? tree (path ++ [slot]) =
      (subtreeAt? tree path).bind (fun node => node.children[slot]?) := by
  rw [subtreeAt?_append]
  simp [subtreeAt?]

/-- Unfold one successful step of the lookup. -/
theorem subtreeAt?_cons_eq_some_iff {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {slot : Nat} {rest : List Nat}
    {node : LocalizedCumulativeDecoratedTree input carrierFuel} :
    subtreeAt? tree (slot :: rest) = some node ↔
      ∃ child, tree.children[slot]? = some child ∧ subtreeAt? child rest = some node := by
  rw [subtreeAt?_cons, Option.bind_eq_some_iff]

/-- A lookup succeeds exactly when it is some subtree. -/
theorem subtreeAt?_isSome_iff {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (path : List Nat) :
    (subtreeAt? tree path).isSome = true ↔
      ∃ node, subtreeAt? tree path = some node := by
  rw [Option.isSome_iff_exists]

/-! ## Positions -/

/-- A position in an actual decorated tree: a root-first sibling-slot path at which the actual
subtree lookup succeeds. -/
abbrev Position (tree : LocalizedCumulativeDecoratedTree input carrierFuel) : Type :=
  {path : List Nat // (subtreeAt? tree path).isSome = true}

/-- The decorated subtree actually found at a position. -/
def positionNode {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) : LocalizedCumulativeDecoratedTree input carrierFuel :=
  (subtreeAt? tree p.val).get p.property

/-- The actual cursor source of the decorated subtree at a position. -/
def positionSource {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) : input.LocalizedRerootCursor carrierFuel :=
  (positionNode p).source

/-- The position of the tree root. -/
def rootPosition (tree : LocalizedCumulativeDecoratedTree input carrierFuel) : Position tree :=
  ⟨[], by simp [subtreeAt?]⟩

theorem positionNode_spec {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) : subtreeAt? tree p.val = some (positionNode p) :=
  Option.eq_some_of_isSome p.property

@[simp] theorem positionNode_rootPosition (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    positionNode (rootPosition tree) = tree := by
  have h := positionNode_spec (rootPosition tree)
  rw [show (rootPosition tree).val = [] from rfl, subtreeAt?_nil] at h
  exact (Option.some.inj h).symm

@[simp] theorem positionSource_rootPosition (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    positionSource (rootPosition tree) = tree.source := by
  simp [positionSource]

/-- Two positions are adjacent when one slot path is the other followed by one sibling slot. -/
def PositionAdjacent {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p q : Position tree) : Prop :=
  (∃ slot, q.val = p.val ++ [slot]) ∨ (∃ slot, p.val = q.val ++ [slot])

theorem positionAdjacent_comm {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {p q : Position tree} (adjacent : PositionAdjacent p q) : PositionAdjacent q p := by
  rcases adjacent with ⟨slot, hs⟩ | ⟨slot, hs⟩
  · exact Or.inr ⟨slot, hs⟩
  · exact Or.inl ⟨slot, hs⟩

theorem position_ext {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {p q : Position tree} (h : p.val = q.val) : p = q :=
  Subtype.ext h

/-! ## Actual child structure of a realized tree

The next lemmas extract the actual child frame of a realized node without assuming any
tree/atom identification. -/

variable {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}

/-- A realized tree exposes the actual reroot child frame and the permutation from its sorted
child sources onto that frame. -/
theorem exists_sourcePerm {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    ∃ children : List (input.LocalizedRerootCursor carrierFuel),
      input.localizedRerootChildren? tree.source = some children ∧
        (tree.children.map (fun child => child.source)).Perm children := by
  cases realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize =>
      exact ⟨children, childrenComputed, sourcePerm⟩

/-- The frame exposed by a realized tree is exactly the executable child list. -/
theorem exists_sourcePerm_executable {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    (tree.children.map (fun child => child.source)).Perm
        (input.executableLocalizedRerootChildren tree.source) ∧
      input.localizedRerootChildren? tree.source =
        some (input.executableLocalizedRerootChildren tree.source) := by
  obtain ⟨children, computed, perm⟩ := exists_sourcePerm realizes
  have executable := input.localizedRerootChildren?_eq_some_executable tree.source
  have childrenEq : children = input.executableLocalizedRerootChildren tree.source :=
    Option.some.inj (computed.symm.trans executable)
  exact ⟨childrenEq ▸ perm, executable⟩

/-- Every child of a realized tree is itself realized. -/
theorem realizes_of_child {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {slot : Nat} {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : tree.children[slot]? = some child) :
    LocalizedCumulativeTreeRealizes input read child := by
  cases realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize =>
      exact childrenRealize child (List.mem_of_getElem? lookup)

/-- Every lookup succeeds at a realized subtree. -/
theorem realizes_of_subtree {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {path : List Nat} {node : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : subtreeAt? tree path = some node) :
    LocalizedCumulativeTreeRealizes input read node := by
  induction path generalizing tree with
  | nil =>
      rw [subtreeAt?_nil] at lookup
      rw [← Option.some.inj lookup]
      exact realizes
  | cons slot rest ih =>
      rw [subtreeAt?_cons_eq_some_iff] at lookup
      obtain ⟨child, childLookup, restLookup⟩ := lookup
      exact ih (realizes_of_child realizes childLookup) restLookup

/-- The source of a child of a realized tree is an actual executable child of its source. -/
theorem mem_executable_of_child {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {slot : Nat} {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : tree.children[slot]? = some child) :
    E input tree.source child.source := by
  obtain ⟨perm, _executable⟩ := exists_sourcePerm_executable realizes
  have childSourceMem : child.source ∈ tree.children.map (fun child => child.source) :=
    List.mem_map.mpr ⟨child, List.mem_of_getElem? lookup, rfl⟩
  exact perm.mem_iff.mp childSourceMem

/-- Every position source is actually child-reachable from the tree root. -/
theorem actualChildReachable_of_subtree {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {path : List Nat} {node : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : subtreeAt? tree path = some node) :
    input.ActualChildReachable tree.source node.source := by
  induction path generalizing tree with
  | nil =>
      rw [subtreeAt?_nil] at lookup
      rw [← Option.some.inj lookup]
      exact Relation.ReflTransGen.refl
  | cons slot rest ih =>
      rw [subtreeAt?_cons_eq_some_iff] at lookup
      obtain ⟨child, childLookup, restLookup⟩ := lookup
      exact Relation.ReflTransGen.head (mem_executable_of_child realizes childLookup)
        (ih (realizes_of_child realizes childLookup) restLookup)

theorem actualChildReachable_positionSource {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    input.ActualChildReachable tree.source (positionSource p) :=
  actualChildReachable_of_subtree realizes (positionNode_spec p)

/-! ## Child and parent positions -/

/-- The position of one actual sorted child of the node at `p`. -/
def positionChild {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) (slot : Nat) (bound : slot < (positionNode p).children.length) :
    Position tree :=
  ⟨p.val ++ [slot], by
    simp [subtreeAt?_append_singleton, positionNode_spec, List.getElem?_eq_getElem bound]⟩

theorem positionNode_positionChild {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) (slot : Nat) (bound : slot < (positionNode p).children.length) :
    positionNode (positionChild p slot bound) = (positionNode p).children[slot] := by
  have h₁ := positionNode_spec (positionChild p slot bound)
  have h₂ : subtreeAt? tree (p.val ++ [slot]) = some ((positionNode p).children[slot]) := by
    rw [subtreeAt?_append_singleton, positionNode_spec]
    simp [List.getElem?_eq_getElem bound]
  exact Option.some.inj (h₁.symm.trans h₂)

theorem positionChild_val {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) (slot : Nat) (bound : slot < (positionNode p).children.length) :
    (positionChild p slot bound).val = p.val ++ [slot] := rfl

/-- Split a nonempty path at its last slot: the parent lookup and the final child lookup. -/
theorem subtreeAt?_dropLast {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {path : List Nat} {node : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : subtreeAt? tree path = some node) (ne : path ≠ []) :
    ∃ (parent : LocalizedCumulativeDecoratedTree input carrierFuel) (slot : Nat),
      subtreeAt? tree path.dropLast = some parent ∧
        parent.children[slot]? = some node := by
  induction path generalizing tree with
  | nil => exact absurd rfl ne
  | cons slot rest ih =>
      rw [subtreeAt?_cons_eq_some_iff] at lookup
      obtain ⟨child, childLookup, restLookup⟩ := lookup
      cases rest with
      | nil =>
          have nodeEq : node = child := (Option.some.inj restLookup).symm
          exact ⟨tree, slot, by simp, by rw [nodeEq]; exact childLookup⟩
      | cons slot' rest' =>
          obtain ⟨parent, last, parentLookup, childLookupLast⟩ :=
            ih restLookup (by simp)
          refine ⟨parent, last, ?_, childLookupLast⟩
          rw [List.dropLast_cons_of_ne_nil (by simp), subtreeAt?_cons]
          exact Option.bind_eq_some_iff.mpr ⟨child, childLookup, parentLookup⟩

/-- The parent position of a nonempty position. -/
def positionParent {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) (ne : p.val ≠ []) : Position tree :=
  ⟨p.val.dropLast, by
    obtain ⟨parent, _slot, parentLookup, _childLookup⟩ :=
      subtreeAt?_dropLast (positionNode_spec p) ne
    rw [parentLookup]
    simp⟩

theorem positionParent_val {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) (ne : p.val ≠ []) :
    (positionParent p ne).val = p.val.dropLast := rfl

theorem positionParent_node_child {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) (ne : p.val ≠ []) :
    ∃ slot : Nat, (positionNode (positionParent p ne)).children[slot]? = some (positionNode p) := by
  obtain ⟨parent, slot, parentLookup, childLookup⟩ :=
    subtreeAt?_dropLast (positionNode_spec p) ne
  have parentEq : parent = positionNode (positionParent p ne) := by
    have spec := positionNode_spec (positionParent p ne)
    rw [positionParent_val, parentLookup] at spec
    exact Option.some.inj spec
  exact ⟨slot, parentEq ▸ childLookup⟩

theorem position_eq_parent_append_last {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) (ne : p.val ≠ []) :
    p.val = (positionParent p ne).val ++ [p.val.getLast ne] := by
  rw [positionParent_val]
  exact (List.dropLast_concat_getLast ne).symm

/-! ## Physical atoms of realized nodes

The remaining results interpret the intrinsic positions of a realized tree as physical atoms of
the incoming-edge cut branch.  Everything is derived from `LocalizedCumulativeTreeRealizes`, the
physical incoming edge, the preserved original root, path validity and acyclicity; no tree/atom
bijection or coverage is assumed. -/

section PhysicalEmbedding

variable (singleBonded : input.moleculeGraph.SimpleBonded)
variable (acyclic : input.moleculeGraph.Acyclic)



def nodeAtom (node : LocalizedCumulativeDecoratedTree input carrierFuel) : input.Atom :=
  (node.source.occurrence.1.node.current?).get (by
    obtain ⟨current, _path, observed, _head, _provenance, _simple, _support, _penultimate⟩ :=
      input.carrierOccurrence_realPath singleBonded acyclic node.source.occurrence
    exact Option.isSome_iff_exists.mpr ⟨current, observed⟩)

/-- The defining equation of `nodeAtom`. -/
theorem nodeAtom_spec (node : LocalizedCumulativeDecoratedTree input carrierFuel) :
    node.source.occurrence.1.node.current? = some (nodeAtom singleBonded acyclic node) :=
  Option.eq_some_of_isSome _

/-- A node observing a given atom carries that atom. -/
theorem nodeAtom_eq_of_observed {node : LocalizedCumulativeDecoratedTree input carrierFuel}
    {atom : input.Atom}
    (observed : node.source.occurrence.1.node.current? = some atom) :
    nodeAtom singleBonded acyclic node = atom :=
  Option.some.inj ((nodeAtom_spec singleBonded acyclic node).symm.trans observed)

/-- Nodes with the same actual source cursor carry the same physical atom. -/
theorem nodeAtom_eq_of_source_eq
    {left right : LocalizedCumulativeDecoratedTree input carrierFuel}
    (sourceEq : left.source = right.source) :
    nodeAtom singleBonded acyclic left = nodeAtom singleBonded acyclic right := by
  have leftSpec := nodeAtom_spec singleBonded acyclic left
  have rightSpec := nodeAtom_spec singleBonded acyclic right
  rw [sourceEq] at leftSpec
  exact Option.some.inj (leftSpec.symm.trans rightSpec)

/-- The physical atom observed at a position. -/
def positionAtom {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) : input.Atom :=
  nodeAtom singleBonded acyclic (positionNode p)

/-- The current atom of the position's actual source cursor is the position atom. -/
theorem positionAtom_spec {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) :
    (positionSource p).occurrence.1.node.current? =
      some (positionAtom singleBonded acyclic p) :=
  nodeAtom_spec singleBonded acyclic (positionNode p)

/-- The root position carries the incoming attachment atom. -/
theorem positionAtom_rootPosition
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) {oAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom) :
    positionAtom singleBonded acyclic (rootPosition tree) = oAtom := by
  rw [positionAtom, positionNode_rootPosition]
  exact nodeAtom_eq_of_observed singleBonded acyclic oObserved

/-- A real node's official atom label is the raw CIP label of its current atom. -/
theorem officialNodeAtomLabel_eq_of_observed
    {node : OfficialCIPNode input.Atom} {atom : input.Atom}
    (observed : node.current? = some atom)
    (real : node.provenance = OfficialCIPNodeProvenance.realAtom) :
    input.moleculeGraph.officialNodeAtomLabel node =
      toLex (input.moleculeGraph.atomZ atom, input.moleculeGraph.atomMass atom) := by
  simp [MoleculeGraph.officialNodeAtomLabel, observed, real, MoleculeGraph.rawCIPAtomLabel]

/-- The Rule-1a atomic number stored at a realized node is the physical atom's atomic number. -/
theorem atomicNumber_eq_atomZ
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    tree.atomicNumber = input.moleculeGraph.atomZ (nodeAtom singleBonded acyclic tree) := by
  cases realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize =>
      have observed : cursor.occurrence.1.node.current? =
          some (nodeAtom singleBonded acyclic
            (localizedRootTree input cursor (read cursor) sortedChildren)) :=
        nodeAtom_spec singleBonded acyclic
          (localizedRootTree input cursor (read cursor) sortedChildren)
      have real :=
        input.carrierOccurrence_provenance_real singleBonded acyclic cursor.occurrence
      have labelEq := officialNodeAtomLabel_eq_of_observed observed real
      show (ofLex (input.moleculeGraph.officialNodeAtomLabel cursor.occurrence.1.node)).1 =
        input.moleculeGraph.atomZ (nodeAtom singleBonded acyclic
          (localizedRootTree input cursor (read cursor) sortedChildren))
      rw [labelEq]
      simp

/-- The Rule-2 isotope mass stored at a realized node is the physical atom's mass. -/
theorem isotopeMass_eq_atomMass
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    tree.isotopeMass = input.moleculeGraph.atomMass (nodeAtom singleBonded acyclic tree) := by
  cases realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize =>
      have observed : cursor.occurrence.1.node.current? =
          some (nodeAtom singleBonded acyclic
            (localizedRootTree input cursor (read cursor) sortedChildren)) :=
        nodeAtom_spec singleBonded acyclic
          (localizedRootTree input cursor (read cursor) sortedChildren)
      have real :=
        input.carrierOccurrence_provenance_real singleBonded acyclic cursor.occurrence
      have labelEq := officialNodeAtomLabel_eq_of_observed observed real
      show (ofLex (input.moleculeGraph.officialNodeAtomLabel cursor.occurrence.1.node)).2 =
        input.moleculeGraph.atomMass (nodeAtom singleBonded acyclic
          (localizedRootTree input cursor (read cursor) sortedChildren))
      rw [labelEq]
      simp

/-- The atomic number at any position is the physical position atom's atomic number. -/
theorem positionAtomicNumber_eq_atomZ
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    (positionNode p).atomicNumber = input.moleculeGraph.atomZ (positionAtom singleBonded acyclic p) :=
  atomicNumber_eq_atomZ singleBonded acyclic (realizes_of_subtree realizes (positionNode_spec p))

/-- The isotope mass at any position is the physical position atom's mass. -/
theorem positionIsotopeMass_eq_atomMass
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    (positionNode p).isotopeMass =
      input.moleculeGraph.atomMass (positionAtom singleBonded acyclic p) :=
  isotopeMass_eq_atomMass singleBonded acyclic (realizes_of_subtree realizes (positionNode_spec p))

/-! ## Actual child data of a realized node -/

/-- The recorded previous occurrence of an actual child is the parent's occurrence. -/
theorem child_previous_of_child
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {slot : Nat} {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : tree.children[slot]? = some child) :
    child.source.previous? = some tree.source.occurrence := by
  obtain ⟨children, computed, perm⟩ := exists_sourcePerm realizes
  have present : child.source ∈ children :=
    perm.mem_iff.mp (List.mem_map.mpr ⟨child, List.mem_of_getElem? lookup, rfl⟩)
  exact input.localizedRerootChildren?_previous_eq tree.source children computed
    child.source present

/-- An actual child keeps the parent's original occurrence root. -/
theorem child_root_of_child
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {slot : Nat} {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : tree.children[slot]? = some child) :
    child.source.occurrence.1.root = tree.source.occurrence.1.root := by
  obtain ⟨children, computed, perm⟩ := exists_sourcePerm realizes
  have present : child.source ∈ children :=
    perm.mem_iff.mp (List.mem_map.mpr ⟨child, List.mem_of_getElem? lookup, rfl⟩)
  exact input.localizedRerootChildren?_root_eq tree.source children computed
    child.source present

/-- An actual child is a valid reroot cursor. -/
theorem child_valid_of_child
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {slot : Nat} {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : tree.children[slot]? = some child) :
    input.LocalizedRerootCursorValid child.source :=
  input.localizedRerootChild_valid tree.source child.source
    (input.executableLocalizedRerootChildren tree.source)
    (input.executableLocalizedRerootChildren_declarative tree.source)
    (mem_executable_of_child realizes lookup)

/-- The parent and child atoms of an actual child are physically adjacent. -/
theorem child_atom_adjacent
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    {slot : Nat} {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : tree.children[slot]? = some child) :
    input.moleculeGraph.Adj (nodeAtom singleBonded acyclic tree)
      (nodeAtom singleBonded acyclic child) := by
  have localIff := input.localizedRerootChildren?_current_iff_adjacent_of_previous
    singleBonded acyclic enough tree.source previous previousEq sameRoot
    oObserved pObserved
    (input.executableLocalizedRerootChildren tree.source)
    (input.localizedRerootChildren?_eq_some_executable tree.source)
  have adjacent := ((localIff (nodeAtom singleBonded acyclic child)).mp
    ⟨child.source, mem_executable_of_child realizes lookup,
      nodeAtom_spec singleBonded acyclic child⟩).1
  rwa [← nodeAtom_eq_of_observed singleBonded acyclic oObserved] at adjacent

/-- A position whose slot path is empty is the root position. -/
theorem positionNode_eq_tree_of_val_eq_nil
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel} {p : Position tree}
    (pathEq : p.val = []) : positionNode p = tree := by
  have spec := positionNode_spec p
  rw [pathEq, subtreeAt?_nil] at spec
  exact (Option.some.inj spec).symm

/-- **Cut membership at a position.**  The atom at any position of a realized subtree lies in the
physical branch of the node's current atom after deleting the incoming attachment atom. -/
theorem positionAtom_mem_cutBranch
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (p : Position tree) :
    positionAtom singleBonded acyclic p ∈
      AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom :=
  input.actualReachable_current_mem_cutBranch_general singleBonded acyclic enough
    tree.source previous previousEq valid oObserved pObserved incomingEdge
    (positionSource p) (actualChildReachable_positionSource realizes p)
    (nodeAtom_spec singleBonded acyclic (positionNode p))

/-- **Cut membership inside a child branch.**  The atom at any position of an actual child lies in
the physical branch of the child atom after deleting the parent atom.  The child's root data is
derived from realizization; only the parent's recorded incoming occurrence is needed. -/
theorem positionAtom_mem_child_cutBranch
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    {slot : Nat} {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : tree.children[slot]? = some child) (q : Position child) :
    positionAtom singleBonded acyclic q ∈
      AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph
        (nodeAtom singleBonded acyclic tree) (nodeAtom singleBonded acyclic child) :=
  positionAtom_mem_cutBranch singleBonded acyclic enough
    (realizes_of_child realizes lookup) (tree.source.occurrence)
    (child_previous_of_child realizes lookup)
    (child_valid_of_child realizes lookup)
    (nodeAtom_spec singleBonded acyclic child) (nodeAtom_spec singleBonded acyclic tree)
    (child_atom_adjacent singleBonded acyclic enough realizes previous previousEq sameRoot
      oObserved pObserved lookup) q

/-- Distinct sorted children of a realized node carry distinct physical atoms. -/
theorem child_atom_injective
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {i j : Nat} (hi : i < tree.children.length) (hj : j < tree.children.length)
    (same : nodeAtom singleBonded acyclic tree.children[i] =
      nodeAtom singleBonded acyclic tree.children[j]) :
    i = j := by
  obtain ⟨children, computed, perm⟩ := exists_sourcePerm realizes
  have hci : tree.children[i]? = some tree.children[i] := List.getElem?_eq_getElem hi
  have hcj : tree.children[j]? = some tree.children[j] := List.getElem?_eq_getElem hj
  have memI : tree.children[i].source ∈ children :=
    perm.mem_iff.mp (List.mem_map.mpr ⟨tree.children[i], List.mem_of_getElem? hci, rfl⟩)
  have memJ : tree.children[j].source ∈ children :=
    perm.mem_iff.mp (List.mem_map.mpr ⟨tree.children[j], List.mem_of_getElem? hcj, rfl⟩)
  have sameCurrent : tree.children[i].source.occurrence.1.node.current? =
      tree.children[j].source.occurrence.1.node.current? := by
    rw [nodeAtom_spec singleBonded acyclic tree.children[i],
      nodeAtom_spec singleBonded acyclic tree.children[j], same]
  have sourcesEq : tree.children[i].source = tree.children[j].source :=
    input.localizedRerootChildren?_current_injective singleBonded acyclic tree.source
      children computed _ memI _ memJ sameCurrent
  have childrenNodup : children.Nodup := by
    have executable := input.localizedRerootChildren?_eq_some_executable tree.source
    have childrenEq : children = input.executableLocalizedRerootChildren tree.source :=
      Option.some.inj (computed.symm.trans executable)
    rw [childrenEq]
    exact input.executableLocalizedRerootChildren_nodup tree.source
  have mappedNodup : (tree.children.map (fun t => t.source)).Nodup :=
    perm.nodup_iff.mpr childrenNodup
  have mappedInjective := List.nodup_iff_injective_getElem.mp mappedNodup
  have hi' : i < (tree.children.map (fun t => t.source)).length := by simpa using hi
  have hj' : j < (tree.children.map (fun t => t.source)).length := by simpa using hj
  have finEq : (⟨i, hi'⟩ : Fin (tree.children.map (fun t => t.source)).length) =
      ⟨j, hj'⟩ := by
    apply mappedInjective
    simpa using sourcesEq
  exact congrArg Fin.val finEq

/-- A nonempty position exposes its first actual child slot and the residual child position. -/
theorem exists_child_of_position_cons
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel} {p : Position tree}
    {slot : Nat} {rest : List Nat} (pathEq : p.val = slot :: rest) :
    ∃ (child : LocalizedCumulativeDecoratedTree input carrierFuel),
      tree.children[slot]? = some child ∧
        ∃ q : Position child, q.val = rest ∧ positionNode p = positionNode q := by
  have lookup := positionNode_spec p
  rw [pathEq, subtreeAt?_cons_eq_some_iff] at lookup
  obtain ⟨child, childLookup, restLookup⟩ := lookup
  let q : Position child :=
    ⟨rest, by rw [subtreeAt?_isSome_iff]; exact ⟨positionNode p, restLookup⟩⟩
  refine ⟨child, childLookup, q, rfl, ?_⟩
  exact Option.some.inj (restLookup.symm.trans (positionNode_spec q))

/-- **Position injectivity.**  Distinct positions of a realized tree carry distinct physical atoms.
The proof recurses on the total slot-path length and uses the disjointness of the physical cut
branches of distinct children. -/
theorem positionAtom_injective_aux
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel) (bound : Nat) :
    ∀ (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
      (_realizes : LocalizedCumulativeTreeRealizes input read tree)
      (previous : input.LocalizedCIPOccurrence carrierFuel)
      (_previousEq : tree.source.previous? = some previous)
      (_sameRoot : tree.source.occurrence.1.root = previous.1.root)
      (oAtom pAtom : input.Atom)
      (_oObserved : tree.source.occurrence.1.node.current? = some oAtom)
      (_pObserved : previous.1.node.current? = some pAtom)
      (p q : Position tree),
      p.val.length + q.val.length ≤ bound →
        positionAtom singleBonded acyclic p = positionAtom singleBonded acyclic q → p = q := by
  induction bound using Nat.strong_induction_on with
  | _ bound ih =>
    intro tree realizes previous previousEq sameRoot oAtom pAtom oObserved pObserved p q
      hbound hatom
    obtain ⟨pPath, pProp⟩ := p
    obtain ⟨qPath, qProp⟩ := q
    cases pPath with
    | nil =>
        cases qPath with
        | nil => rfl
        | cons qSlot qRest =>
            exfalso
            have pAtomEq : positionAtom singleBonded acyclic (⟨[], pProp⟩ : Position tree) =
                nodeAtom singleBonded acyclic tree := by
              change nodeAtom singleBonded acyclic
                (positionNode (⟨[], pProp⟩ : Position tree)) = nodeAtom singleBonded acyclic tree
              rw [positionNode_eq_tree_of_val_eq_nil rfl]
            have qAtomEqTree :
                positionAtom singleBonded acyclic (⟨qSlot :: qRest, qProp⟩ : Position tree) =
                  nodeAtom singleBonded acyclic tree := by
              rw [← pAtomEq]
              exact hatom.symm
            obtain ⟨childQ, lookupQ, q', _qVal, nodeEqQ⟩ :=
              exists_child_of_position_cons
                (p := (⟨qSlot :: qRest, qProp⟩ : Position tree)) rfl
            have qEq :
                positionAtom singleBonded acyclic (⟨qSlot :: qRest, qProp⟩ : Position tree) =
                  positionAtom singleBonded acyclic q' := by
              change nodeAtom singleBonded acyclic
                (positionNode (⟨qSlot :: qRest, qProp⟩ : Position tree)) =
                  nodeAtom singleBonded acyclic (positionNode q')
              rw [nodeEqQ]
            have q'AtomTree : positionAtom singleBonded acyclic q' =
                nodeAtom singleBonded acyclic tree := qEq.symm.trans qAtomEqTree
            have mem := positionAtom_mem_child_cutBranch singleBonded acyclic enough realizes
              previous previousEq sameRoot oObserved pObserved lookupQ q'
            rw [q'AtomTree] at mem
            exact AcyclicCutBranchAutomorphism.center_not_mem_cutBranch input.moleculeGraph
              (nodeAtom singleBonded acyclic tree) (nodeAtom singleBonded acyclic childQ) mem
    | cons pSlot pRest =>
        cases qPath with
        | nil =>
            exfalso
            have qAtomEq : positionAtom singleBonded acyclic (⟨[], qProp⟩ : Position tree) =
                nodeAtom singleBonded acyclic tree := by
              change nodeAtom singleBonded acyclic
                (positionNode (⟨[], qProp⟩ : Position tree)) = nodeAtom singleBonded acyclic tree
              rw [positionNode_eq_tree_of_val_eq_nil rfl]
            have pAtomEqTree :
                positionAtom singleBonded acyclic (⟨pSlot :: pRest, pProp⟩ : Position tree) =
                  nodeAtom singleBonded acyclic tree := by
              rw [← qAtomEq]
              exact hatom
            obtain ⟨childP, lookupP, p', _pVal, nodeEqP⟩ :=
              exists_child_of_position_cons
                (p := (⟨pSlot :: pRest, pProp⟩ : Position tree)) rfl
            have pEq :
                positionAtom singleBonded acyclic (⟨pSlot :: pRest, pProp⟩ : Position tree) =
                  positionAtom singleBonded acyclic p' := by
              change nodeAtom singleBonded acyclic
                (positionNode (⟨pSlot :: pRest, pProp⟩ : Position tree)) =
                  nodeAtom singleBonded acyclic (positionNode p')
              rw [nodeEqP]
            have p'AtomTree : positionAtom singleBonded acyclic p' =
                nodeAtom singleBonded acyclic tree := pEq.symm.trans pAtomEqTree
            have mem := positionAtom_mem_child_cutBranch singleBonded acyclic enough realizes
              previous previousEq sameRoot oObserved pObserved lookupP p'
            rw [p'AtomTree] at mem
            exact AcyclicCutBranchAutomorphism.center_not_mem_cutBranch input.moleculeGraph
              (nodeAtom singleBonded acyclic tree) (nodeAtom singleBonded acyclic childP) mem
        | cons qSlot qRest =>
            by_cases hslot : pSlot = qSlot
            · subst hslot
              obtain ⟨childP, lookupP, p', pVal, nodeEqP⟩ :=
                exists_child_of_position_cons
                  (p := (⟨pSlot :: pRest, pProp⟩ : Position tree)) rfl
              obtain ⟨childQ, lookupQ, q', qVal, nodeEqQ⟩ :=
                exists_child_of_position_cons
                  (p := (⟨pSlot :: qRest, qProp⟩ : Position tree)) rfl
              have childEq : childP = childQ := Option.some.inj (lookupP.symm.trans lookupQ)
              subst childEq
              have pEq :
                  positionAtom singleBonded acyclic (⟨pSlot :: pRest, pProp⟩ : Position tree) =
                    positionAtom singleBonded acyclic p' := by
                change nodeAtom singleBonded acyclic
                  (positionNode (⟨pSlot :: pRest, pProp⟩ : Position tree)) =
                    nodeAtom singleBonded acyclic (positionNode p')
                rw [nodeEqP]
              have qEq :
                  positionAtom singleBonded acyclic (⟨pSlot :: qRest, qProp⟩ : Position tree) =
                    positionAtom singleBonded acyclic q' := by
                change nodeAtom singleBonded acyclic
                  (positionNode (⟨pSlot :: qRest, qProp⟩ : Position tree)) =
                    nodeAtom singleBonded acyclic (positionNode q')
                rw [nodeEqQ]
              have hatom' : positionAtom singleBonded acyclic p' =
                  positionAtom singleBonded acyclic q' :=
                pEq.symm.trans (hatom.trans qEq)
              have hb : (pRest.length + 1) + (qRest.length + 1) ≤ bound := by simpa using hbound
              have hsmall : pRest.length + qRest.length < bound := by omega
              have hle : p'.val.length + q'.val.length ≤ pRest.length + qRest.length := by
                rw [pVal, qVal]
              have hpq : p' = q' :=
                ih (pRest.length + qRest.length) hsmall childP
                  (realizes_of_child realizes lookupP)
                  (tree.source.occurrence) (child_previous_of_child realizes lookupP)
                  (child_root_of_child realizes lookupP)
                  (nodeAtom singleBonded acyclic childP) (nodeAtom singleBonded acyclic tree)
                  (nodeAtom_spec singleBonded acyclic childP)
                  (nodeAtom_spec singleBonded acyclic tree) p' q' hle hatom'
              have restEq : pRest = qRest :=
                pVal.symm.trans ((congrArg Subtype.val hpq).trans qVal)
              apply position_ext
              change pSlot :: pRest = pSlot :: qRest
              rw [restEq]
            · exfalso
              obtain ⟨childP, lookupP, p', _pVal, nodeEqP⟩ :=
                exists_child_of_position_cons
                  (p := (⟨pSlot :: pRest, pProp⟩ : Position tree)) rfl
              obtain ⟨childQ, lookupQ, q', _qVal, nodeEqQ⟩ :=
                exists_child_of_position_cons
                  (p := (⟨qSlot :: qRest, qProp⟩ : Position tree)) rfl
              have pEq :
                  positionAtom singleBonded acyclic (⟨pSlot :: pRest, pProp⟩ : Position tree) =
                    positionAtom singleBonded acyclic p' := by
                change nodeAtom singleBonded acyclic
                  (positionNode (⟨pSlot :: pRest, pProp⟩ : Position tree)) =
                    nodeAtom singleBonded acyclic (positionNode p')
                rw [nodeEqP]
              have qEq :
                  positionAtom singleBonded acyclic (⟨qSlot :: qRest, qProp⟩ : Position tree) =
                    positionAtom singleBonded acyclic q' := by
                change nodeAtom singleBonded acyclic
                  (positionNode (⟨qSlot :: qRest, qProp⟩ : Position tree)) =
                    nodeAtom singleBonded acyclic (positionNode q')
                rw [nodeEqQ]
              have hatom' : positionAtom singleBonded acyclic p' =
                  positionAtom singleBonded acyclic q' :=
                pEq.symm.trans (hatom.trans qEq)
              obtain ⟨hiP, hvalP⟩ := List.getElem_of_getElem? lookupP
              obtain ⟨hiQ, hvalQ⟩ := List.getElem_of_getElem? lookupQ
              have distinct : nodeAtom singleBonded acyclic childP ≠
                  nodeAtom singleBonded acyclic childQ := by
                intro same
                apply hslot
                apply child_atom_injective singleBonded acyclic realizes hiP hiQ
                calc nodeAtom singleBonded acyclic tree.children[pSlot]
                    = nodeAtom singleBonded acyclic childP := by rw [hvalP]
                  _ = nodeAtom singleBonded acyclic childQ := same
                  _ = nodeAtom singleBonded acyclic tree.children[qSlot] := by rw [hvalQ]
              have memP := positionAtom_mem_child_cutBranch singleBonded acyclic enough realizes
                previous previousEq sameRoot oObserved pObserved lookupP p'
              have memQ := positionAtom_mem_child_cutBranch singleBonded acyclic enough realizes
                previous previousEq sameRoot oObserved pObserved lookupQ q'
              rw [hatom'] at memP
              have adjP := child_atom_adjacent singleBonded acyclic enough realizes previous
                previousEq sameRoot oObserved pObserved lookupP
              have adjQ := child_atom_adjacent singleBonded acyclic enough realizes previous
                previousEq sameRoot oObserved pObserved lookupQ
              exact distinct (AcyclicCutBranchAutomorphism.cutBranch_disjoint_of_acyclic
                input.moleculeGraph acyclic adjP adjQ memP memQ)

/-- **Position injectivity.** -/
theorem positionAtom_injective
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (p q : Position tree)
    (atomEq : positionAtom singleBonded acyclic p = positionAtom singleBonded acyclic q) :
    p = q :=
  positionAtom_injective_aux singleBonded acyclic enough (p.val.length + q.val.length)
    tree realizes previous previousEq sameRoot oAtom pAtom oObserved pObserved p q le_rfl atomEq

/-! ## Physical adjacency -/

/-- A one-slot extension of a position is a physical neighbor of the parent-position atom. -/
theorem positionAtom_adjacent_of_positionChild
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {p : Position tree}
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (prevEq : (positionNode p).source.previous? = some previous)
    (same : (positionNode p).source.occurrence.1.root = previous.1.root)
    {parentAtom : input.Atom}
    (prevObs : previous.1.node.current? = some parentAtom)
    {q : Position tree} {slot : Nat} (pathEq : q.val = p.val ++ [slot]) :
    input.moleculeGraph.Adj (positionAtom singleBonded acyclic p)
      (positionAtom singleBonded acyclic q) := by
  have realizedP : LocalizedCumulativeTreeRealizes input read (positionNode p) :=
    realizes_of_subtree realizes (positionNode_spec p)
  have childLookup : (positionNode p).children[slot]? = some (positionNode q) := by
    have spec := positionNode_spec q
    rw [pathEq, subtreeAt?_append_singleton, positionNode_spec, Option.bind_some] at spec
    exact spec
  have adjacent := child_atom_adjacent singleBonded acyclic enough realizedP previous prevEq
    same (positionAtom_spec singleBonded acyclic p) prevObs childLookup
  simpa [positionAtom] using adjacent

/-- If a position atom is adjacent to `q` and `q`'s atom is not the incoming atom of that
position, then `q` lies one actual child step below the position. -/
theorem exists_positionChild_of_adjacent_of_ne
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previousRoot : input.LocalizedCIPOccurrence carrierFuel)
    (previousEqRoot : tree.source.previous? = some previousRoot)
    (sameRootRoot : tree.source.occurrence.1.root = previousRoot.1.root)
    {oAtomRoot pAtomRoot : input.Atom}
    (oObservedRoot : tree.source.occurrence.1.node.current? = some oAtomRoot)
    (pObservedRoot : previousRoot.1.node.current? = some pAtomRoot)
    {p : Position tree}
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (prevEq : (positionNode p).source.previous? = some previous)
    (same : (positionNode p).source.occurrence.1.root = previous.1.root)
    {parentAtom : input.Atom}
    (prevObs : previous.1.node.current? = some parentAtom)
    {q : Position tree}
    (adjacent : input.moleculeGraph.Adj (positionAtom singleBonded acyclic p)
      (positionAtom singleBonded acyclic q))
    (hne : positionAtom singleBonded acyclic q ≠ parentAtom) :
    ∃ slot : Nat, q.val = p.val ++ [slot] := by
  have realizedP : LocalizedCumulativeTreeRealizes input read (positionNode p) :=
    realizes_of_subtree realizes (positionNode_spec p)
  have localIff := input.localizedRerootChildren?_current_iff_adjacent_of_previous
    singleBonded acyclic enough (positionNode p).source previous prevEq same
    (positionAtom_spec singleBonded acyclic p) prevObs
    (input.executableLocalizedRerootChildren (positionNode p).source)
    (input.localizedRerootChildren?_eq_some_executable (positionNode p).source)
  obtain ⟨cursorChild, cursorMem, cursorCurrent⟩ :=
    (localIff (positionAtom singleBonded acyclic q)).mpr ⟨adjacent, hne⟩
  obtain ⟨perm, _computed⟩ := exists_sourcePerm_executable realizedP
  have mappedMem := perm.mem_iff.mpr cursorMem
  obtain ⟨sub, subMem, subSource⟩ := List.mem_map.mp mappedMem
  obtain ⟨slot, lookup⟩ := List.mem_iff_getElem?.mp subMem
  obtain ⟨bound, _⟩ := List.getElem_of_getElem? lookup
  have subAtom : nodeAtom singleBonded acyclic sub = positionAtom singleBonded acyclic q := by
    have spec := nodeAtom_spec singleBonded acyclic sub
    rw [subSource] at spec
    exact Option.some.inj (spec.symm.trans cursorCurrent)
  have childEq : (positionNode p).children[slot] = sub :=
    Option.some.inj ((List.getElem?_eq_getElem bound).symm.trans lookup)
  let lifted : Position tree := positionChild p slot bound
  have liftedAtom : positionAtom singleBonded acyclic lifted =
      positionAtom singleBonded acyclic q := by
    show positionAtom singleBonded acyclic (positionChild p slot bound) =
      positionAtom singleBonded acyclic q
    simp only [positionAtom]
    rw [positionNode_positionChild, childEq]
    exact subAtom
  have qEq : q = lifted :=
    positionAtom_injective singleBonded acyclic enough realizes previousRoot previousEqRoot
      sameRootRoot oObservedRoot pObservedRoot q lifted liftedAtom.symm
  refine ⟨slot, ?_⟩
  rw [qEq]
  show (positionChild p slot bound).val = p.val ++ [slot]
  rfl

/-- **Adjacency faithfulness.**  Two positions are physically adjacent exactly when they are
adjacent in the intrinsic tree. -/
theorem positionAtom_adjacent_iff_positionAdjacent
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    (valid : input.LocalizedRerootCursorValid tree.source)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (p q : Position tree) :
    input.moleculeGraph.Adj (positionAtom singleBonded acyclic p)
        (positionAtom singleBonded acyclic q) ↔
      PositionAdjacent p q := by
  constructor
  · intro adjacent
    by_cases hpNil : p.val = []
    · by_cases hqAtom : positionAtom singleBonded acyclic q = pAtom
      · exfalso
        have memQ := positionAtom_mem_cutBranch singleBonded acyclic enough realizes previous
          previousEq valid oObserved pObserved incomingEdge q
        rw [hqAtom] at memQ
        exact AcyclicCutBranchAutomorphism.center_not_mem_cutBranch input.moleculeGraph pAtom
          oAtom memQ
      · have pRoot : p = rootPosition tree := position_ext (by rw [hpNil]; rfl)
        subst p
        obtain ⟨slot, hs⟩ := exists_positionChild_of_adjacent_of_ne singleBonded acyclic enough
          realizes previous previousEq sameRoot oObserved pObserved
          (p := rootPosition tree)
          previous (by simpa using previousEq) (by simpa using sameRoot)
          (parentAtom := pAtom) pObserved adjacent hqAtom
        exact Or.inl ⟨slot, hs⟩
    · obtain ⟨parentSlot, parentLookup⟩ := positionParent_node_child p hpNil
      have realizedParent : LocalizedCumulativeTreeRealizes input read
          (positionNode (positionParent p hpNil)) :=
        realizes_of_subtree realizes (positionNode_spec (positionParent p hpNil))
      have prevEqP : (positionNode p).source.previous? =
          some (positionNode (positionParent p hpNil)).source.occurrence :=
        child_previous_of_child realizedParent parentLookup
      have sameP : (positionNode p).source.occurrence.1.root =
          (positionNode (positionParent p hpNil)).source.occurrence.1.root :=
        child_root_of_child realizedParent parentLookup
      by_cases hqParent : positionAtom singleBonded acyclic q =
          positionAtom singleBonded acyclic (positionParent p hpNil)
      · have qEq : q = positionParent p hpNil :=
          positionAtom_injective singleBonded acyclic enough realizes previous previousEq
            sameRoot oObserved pObserved q (positionParent p hpNil) hqParent
        rw [qEq]
        exact Or.inr ⟨p.val.getLast hpNil, position_eq_parent_append_last p hpNil⟩
      · obtain ⟨slot, hs⟩ :=
          exists_positionChild_of_adjacent_of_ne singleBonded acyclic enough realizes previous
            previousEq sameRoot oObserved pObserved
            (positionNode (positionParent p hpNil)).source.occurrence prevEqP sameP
            (parentAtom := positionAtom singleBonded acyclic (positionParent p hpNil))
            (positionAtom_spec singleBonded acyclic (positionParent p hpNil)) adjacent hqParent
        exact Or.inl ⟨slot, hs⟩
  · intro intrinsic
    rcases intrinsic with ⟨slot, hs⟩ | ⟨slot, hs⟩
    · by_cases hpNil : p.val = []
      · have pRoot : p = rootPosition tree := position_ext (by rw [hpNil]; rfl)
        subst p
        have prevEqR : (positionNode (rootPosition tree)).source.previous? = some previous := by
          simpa using previousEq
        have sameR : (positionNode (rootPosition tree)).source.occurrence.1.root =
            previous.1.root := by
          simpa using sameRoot
        exact positionAtom_adjacent_of_positionChild singleBonded acyclic enough realizes
          previous prevEqR sameR pObserved hs
      · obtain ⟨parentSlot, parentLookup⟩ := positionParent_node_child p hpNil
        have realizedParent : LocalizedCumulativeTreeRealizes input read
            (positionNode (positionParent p hpNil)) :=
          realizes_of_subtree realizes (positionNode_spec (positionParent p hpNil))
        have prevEqP : (positionNode p).source.previous? =
            some (positionNode (positionParent p hpNil)).source.occurrence :=
          child_previous_of_child realizedParent parentLookup
        have sameP : (positionNode p).source.occurrence.1.root =
            (positionNode (positionParent p hpNil)).source.occurrence.1.root :=
          child_root_of_child realizedParent parentLookup
        exact positionAtom_adjacent_of_positionChild singleBonded acyclic enough realizes
          (positionNode (positionParent p hpNil)).source.occurrence prevEqP sameP
          (positionAtom_spec singleBonded acyclic (positionParent p hpNil)) hs
    · by_cases hqNil : q.val = []
      · have qRoot : q = rootPosition tree := position_ext (by rw [hqNil]; rfl)
        subst q
        have prevEqR : (positionNode (rootPosition tree)).source.previous? = some previous := by
          simpa using previousEq
        have sameR : (positionNode (rootPosition tree)).source.occurrence.1.root =
            previous.1.root := by
          simpa using sameRoot
        exact (input.moleculeGraph.adj_symm).mp
          (positionAtom_adjacent_of_positionChild (p := rootPosition tree) (q := p)
            singleBonded acyclic enough realizes previous prevEqR sameR pObserved hs)
      · obtain ⟨parentSlot, parentLookup⟩ := positionParent_node_child q hqNil
        have realizedParent : LocalizedCumulativeTreeRealizes input read
            (positionNode (positionParent q hqNil)) :=
          realizes_of_subtree realizes (positionNode_spec (positionParent q hqNil))
        have prevEqQ : (positionNode q).source.previous? =
            some (positionNode (positionParent q hqNil)).source.occurrence :=
          child_previous_of_child realizedParent parentLookup
        have sameQ : (positionNode q).source.occurrence.1.root =
            (positionNode (positionParent q hqNil)).source.occurrence.1.root :=
          child_root_of_child realizedParent parentLookup
        exact (input.moleculeGraph.adj_symm).mp
          (positionAtom_adjacent_of_positionChild (p := q) (q := p)
            singleBonded acyclic enough realizes
            (positionNode (positionParent q hqNil)).source.occurrence prevEqQ sameQ
            (positionAtom_spec singleBonded acyclic (positionParent q hqNil)) hs)

end PhysicalEmbedding

/-! ## Kernel-authority guards for the shared position API -/

assert_kernel_only subtreeAt?
assert_kernel_only subtreeAt?_nil
assert_kernel_only subtreeAt?_cons
assert_kernel_only subtreeAt?_append
assert_kernel_only subtreeAt?_append_singleton
assert_kernel_only subtreeAt?_cons_eq_some_iff
assert_kernel_only subtreeAt?_isSome_iff
assert_kernel_only Position
assert_kernel_only positionNode
assert_kernel_only positionSource
assert_kernel_only rootPosition
assert_kernel_only positionNode_spec
assert_kernel_only positionNode_rootPosition
assert_kernel_only positionSource_rootPosition
assert_kernel_only PositionAdjacent
assert_kernel_only positionAdjacent_comm
assert_kernel_only position_ext

/-! ## Kernel-authority guards for the actual child structure -/

assert_kernel_only exists_sourcePerm
assert_kernel_only exists_sourcePerm_executable
assert_kernel_only realizes_of_child
assert_kernel_only realizes_of_subtree
assert_kernel_only mem_executable_of_child
assert_kernel_only actualChildReachable_of_subtree
assert_kernel_only actualChildReachable_positionSource
assert_kernel_only positionChild
assert_kernel_only positionNode_positionChild
assert_kernel_only positionChild_val
assert_kernel_only subtreeAt?_dropLast
assert_kernel_only positionParent
assert_kernel_only positionParent_val
assert_kernel_only positionParent_node_child
assert_kernel_only position_eq_parent_append_last

/-! ## Kernel-authority guards for the physical embedding -/

assert_kernel_only nodeAtom
assert_kernel_only nodeAtom_spec
assert_kernel_only nodeAtom_eq_of_observed
assert_kernel_only nodeAtom_eq_of_source_eq
assert_kernel_only positionAtom
assert_kernel_only positionAtom_spec
assert_kernel_only positionAtom_rootPosition
assert_kernel_only officialNodeAtomLabel_eq_of_observed
assert_kernel_only atomicNumber_eq_atomZ
assert_kernel_only isotopeMass_eq_atomMass
assert_kernel_only positionAtomicNumber_eq_atomZ
assert_kernel_only positionIsotopeMass_eq_atomMass
assert_kernel_only child_previous_of_child
assert_kernel_only child_root_of_child
assert_kernel_only child_valid_of_child
assert_kernel_only child_atom_adjacent
assert_kernel_only positionNode_eq_tree_of_val_eq_nil
assert_kernel_only positionAtom_mem_cutBranch
assert_kernel_only positionAtom_mem_child_cutBranch
assert_kernel_only child_atom_injective
assert_kernel_only exists_child_of_position_cons
assert_kernel_only positionAtom_injective_aux
assert_kernel_only positionAtom_injective
assert_kernel_only positionAtom_adjacent_of_positionChild
assert_kernel_only exists_positionChild_of_adjacent_of_ne
assert_kernel_only positionAtom_adjacent_iff_positionAdjacent

end TetraStereo.OneCenter
