import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalChildMultiplicity
import TetraStereo.OneCenter.ProductionCIPRule1aGraphRealization

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeGeneratedCursorPhysicalCut
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeChronologicalChildMultiplicity
open TetraStereo.UniversalProof.NativeGeneratedRealPaths
open TetraStereo.UniversalProof.NativeGeneratedRealNodeInventory

/-- Independent incident endpoints read directly from actual raw bond records, without copy order. -/
def incidentFromBond (atom : Nat) (bond : RawBond) : List Nat :=
  if bond.source == atom then [bond.target]
  else if bond.target == atom then [bond.source] else []

def rawIncident (mol : RawMolecule) (atom : Nat) : List Nat :=
  mol.bonds.flatMap (incidentFromBond atom)

/-- Incidence exposes the actual endpoint records, not a supplied child inventory. -/
theorem mem_rawIncident {mol : RawMolecule} {atom neighbor : Nat} :
    neighbor ∈ rawIncident mol atom ↔ ∃ bond ∈ mol.bonds,
      (bond.source = atom ∧ bond.target = neighbor) ∨
        (bond.target = atom ∧ bond.source = neighbor) := by
  simp only [rawIncident, List.mem_flatMap]
  constructor
  · rintro ⟨bond, member, endpoint⟩
    refine ⟨bond, member, ?_⟩
    by_cases source : bond.source = atom
    · simp [incidentFromBond, source] at endpoint
      exact Or.inl ⟨source, endpoint.symm⟩
    · by_cases target : bond.target = atom
      · simp [incidentFromBond, source, target] at endpoint
        exact Or.inr ⟨target, endpoint.symm⟩
      · simp [incidentFromBond, source, target] at endpoint
  · rintro ⟨bond, member, endpoints⟩
    refine ⟨bond, member, ?_⟩
    rcases endpoints with ⟨source, target⟩ | ⟨target, source⟩
    · simp [incidentFromBond, source, target]
    · by_cases first : bond.source = atom
      · have same : neighbor = atom := source.symm.trans first
        simp [incidentFromBond, first, target, same]
      · have neighborDifferent : neighbor ≠ atom := by
          intro same
          exact first (source.trans same)
        simp [incidentFromBond, target, source, neighborDifferent]

/-- No self endpoint occurs in the chronological raw incidence inventory. -/
theorem rawIncident_not_self {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree) (atom : Nat) :
    atom ∉ rawIncident mol atom := by
  intro member
  obtain ⟨bond, bondMember, endpoints⟩ := mem_rawIncident.mp member
  have order := (tree.2.1 bond bondMember).2.1
  rcases endpoints with ⟨source, target⟩ | ⟨target, source⟩ <;> omega

/-- Every actual raw incident edge has positive physical order. -/
theorem incident_positive {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {atom neighbor : Nat} (member : neighbor ∈ rawIncident mol atom) :
    0 < mol.bondOrder atom neighbor := by
  have different : atom ≠ neighbor := by
    intro same
    subst neighbor
    exact rawIncident_not_self tree atom member
  apply (mol.bondOrder_pos_iff_exists_bond different).mpr
  obtain ⟨bond, bondMember, endpoints⟩ := mem_rawIncident.mp member
  refine ⟨bond, bondMember, ?_⟩
  rcases endpoints with ⟨source, target⟩ | ⟨target, source⟩ <;>
    simp [RawBond.connects, source, target]

/-- Physical positivity and the derived single-copy upper bound force canonical order one. -/
theorem incident_canonical_order_one {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    (node : CanonicalBranchNode) {neighbor : Nat} (member : neighbor ∈ rawIncident mol node.atom) :
    mol.canonicalBondOrder node neighbor = 1 := by
  have physical := incident_positive tree member
  have positive : 0 < mol.canonicalBondOrder node neighbor := by
    unfold RawMolecule.canonicalBondOrder
    split <;> (try split_ifs) <;> first | exact Nat.zero_lt_succ 0 | exact physical
  have upper := chronological_canonicalBondOrder_le_one tree node neighbor
  omega

/-- Actual bond-copy generation equals one unit copy for each independently incident endpoint. -/
theorem copiesFromBond_unit {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    (node : CanonicalBranchNode) {bond : RawBond} (bondMember : bond ∈ mol.bonds) :
    copiesFromBond mol node bond = (incidentFromBond node.atom bond).map (fun atom => (atom, 0)) := by
  by_cases source : bond.source = node.atom
  · have member : bond.target ∈ rawIncident mol node.atom :=
      mem_rawIncident.mpr ⟨bond, bondMember, Or.inl ⟨source, rfl⟩⟩
    have order := incident_canonical_order_one tree node member
    simp [copiesFromBond, incidentFromBond, source, order]
  · by_cases target : bond.target = node.atom
    · have member : bond.source ∈ rawIncident mol node.atom :=
        mem_rawIncident.mpr ⟨bond, bondMember, Or.inr ⟨target, rfl⟩⟩
      have order := incident_canonical_order_one tree node member
      simp [copiesFromBond, incidentFromBond, source, target, order]
    · simp [copiesFromBond, incidentFromBond, source, target]

/-- Complete production seeds are the exact raw incident list tagged with unit copy-index. -/
theorem childCopySeeds_eq_rawIncident {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) (node : CanonicalBranchNode) :
    childCopySeeds mol node = (rawIncident mol node.atom).map (fun atom => (atom, 0)) := by
  unfold childCopySeeds rawIncident
  rw [List.map_flatMap]
  exact List.flatMap_congr (fun bond member => copiesFromBond_unit tree node member)

/-- The independent raw incidence list is distinct, as a consequence of raw edge uniqueness. -/
theorem rawIncident_nodup {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree) (atom : Nat) :
    (rawIncident mol atom).Nodup := by
  let node : CanonicalBranchNode := { atom := atom, parent := atom, history := [atom], provenance := .realAtom }
  have distinct := chronological_childCopySeeds_nodup tree node
  rw [childCopySeeds_eq_rawIncident tree node] at distinct
  exact List.Nodup.of_map (fun atom => (atom, 0)) distinct

/-- The actual one-parent-copy erasure commutes with unit-copy tagging. -/
theorem erase_unit_copies (atoms : List Nat) (parent : Nat) :
    eraseCanonicalParentCopy parent (atoms.map (fun atom => (atom, 0))) =
      (atoms.erase parent).map (fun atom => (atom, 0)) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms ih =>
      by_cases same : atom = parent
      · simp [eraseCanonicalParentCopy, same]
      · simp [eraseCanonicalParentCopy, same, ih]

/-- Child-copy atoms are exactly physical incidence with the stored parent removed once. -/
theorem canonicalChildCopies_atoms {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    (node : CanonicalBranchNode) :
    (mol.canonicalChildCopies node).map Prod.fst = (rawIncident mol node.atom).erase node.parent := by
  rw [canonicalChildCopies_eq_erasedSeeds, childCopySeeds_eq_rawIncident tree node, erase_unit_copies]
  simp only [List.map_map, Function.comp_def]
  exact List.map_id _

/-- Actual generated real children retain precisely that independent cut incidence list. -/
theorem generated_children_atoms {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {node : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root node) :
    (mol.canonicalChildren node).map CanonicalBranchNode.atom =
      (rawIncident mol node.atom).erase node.parent := by
  have real := chronological_generated_all_real tree rootBound generated
  have leaf : node.forcedLeaf = false := by simp [CanonicalBranchNode.forcedLeaf, real]
  simp only [RawMolecule.canonicalChildren, leaf, Bool.false_eq_true, ↓reduceIte,
    List.map_map, Function.comp_def]
  exact canonicalChildCopies_atoms tree node

/-- Both original-tree directions have the same physical neighbor inventory; histories are retained. -/
theorem generated_neighbors_atoms_perm {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {node : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root node) :
    ((({ node := node } : CanonicalRerootCursor).neighbors mol).map CanonicalBranchNode.atom).Perm
      (rawIncident mol node.atom) := by
  cases generated with
  | root =>
      have children := generated_children_atoms tree rootBound (CanonicalCenterTreeNode.root (mol := mol) (center := root))
      simpa [CanonicalRerootCursor.neighbors, canonicalOriginalParent?, canonicalCenterRoot,
        List.erase_of_not_mem (rawIncident_not_self tree root)] using List.Perm.of_eq children
  | @child parent node parentGenerated member =>
      have nodeGenerated := CanonicalCenterTreeNode.child parentGenerated member
      have children := generated_children_atoms tree rootBound nodeGenerated
      have recovered := canonicalOriginalParent?_eq_some_of_child parentGenerated member
      have parentEq := canonical_children_parent member
      have adjacent := generated_child_bond_positive parentGenerated.history_head member
      have parentMember : parent.atom ∈ rawIncident mol node.atom := by
        have ne : node.atom ≠ parent.atom := by
          intro same
          rw [same, mol.bondOrder_self] at adjacent
          exact (Nat.lt_irrefl 0) adjacent
        obtain ⟨bond, bondMember, connects⟩ := (mol.bondOrder_pos_iff_exists_bond ne).mp adjacent
        simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connects
        apply mem_rawIncident.mpr
        refine ⟨bond, bondMember, ?_⟩
        rcases connects with first | second
        · exact Or.inl first
        · exact Or.inr ⟨second.2, second.1⟩
      have permutation := (List.perm_cons_erase parentMember).symm
      simpa only [CanonicalRerootCursor.neighbors, recovered, Option.toList_some,
        List.map_append, List.map_cons, List.map_nil, List.singleton_append, children, parentEq] using permutation

/-- Mapping the actual remembered-edge filter removes precisely the remembered physical atom. -/
theorem cut_filter_atoms (nodes : List CanonicalBranchNode) (current previous : CanonicalBranchNode)
    (identity : ∀ node ∈ nodes, node.atom = previous.atom → node = previous) :
    ((nodes.filterMap fun node => if node == previous then none
      else some ({ node := node, previous? := some current } : CanonicalRerootCursor)).map
        (fun cursor => cursor.node.atom)) = (nodes.map CanonicalBranchNode.atom).filter (· != previous.atom) := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih =>
      have tail := ih (fun other member same => identity other (List.mem_cons_of_mem node member) same)
      have normalizedTail :
          ((nodes.filterMap fun other => if other = previous then none
            else some ({ node := other, previous? := some current } : CanonicalRerootCursor)).map
              (fun cursor => cursor.node.atom)) =
            (nodes.map CanonicalBranchNode.atom).filter (· != previous.atom) := by
        simpa only [beq_iff_eq] using tail
      by_cases same : node = previous
      · simpa [same] using normalizedTail
      · have atomDifferent : node.atom ≠ previous.atom := by
          intro atoms
          exact same (identity node List.mem_cons_self atoms)
        simpa [same, atomDifferent] using congrArg (List.cons node.atom) normalizedTail

/-- Actual forward cursors equal the independently incident list with exactly the incoming atom cut.
Node generation, not a supplied child equality, derives the atom/full-node identity used by the cut. -/
theorem generated_cut_atoms_perm {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {node previous : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root node)
    (previousGenerated : CanonicalCenterTreeNode mol root previous) :
    ((({ node := node, previous? := some previous } : CanonicalRerootCursor).children mol).map
      (fun cursor => cursor.node.atom)).Perm ((rawIncident mol node.atom).erase previous.atom) := by
  have real := chronological_generated_all_real tree rootBound generated
  have leaf : node.forcedLeaf = false := by simp [CanonicalBranchNode.forcedLeaf, real]
  have neighbors := generated_neighbors_atoms_perm tree rootBound generated
  have distinct : ((({ node := node } : CanonicalRerootCursor).neighbors mol).map
      CanonicalBranchNode.atom).Nodup := neighbors.nodup_iff.mpr (rawIncident_nodup tree node.atom)
  have identity : ∀ neighbor ∈ ({ node := node } : CanonicalRerootCursor).neighbors mol,
      neighbor.atom = previous.atom → neighbor = previous := by
    intro neighbor member same
    have neighborGenerated : CanonicalCenterTreeNode mol root neighbor := by
      rcases generated.neighbor_cases member with parentCase | childCase
      · exact parentCase.1
      · exact CanonicalCenterTreeNode.child generated childCase
    exact generated_real_node_unique tree rootBound neighborGenerated previousGenerated
      (chronological_generated_all_real tree rootBound neighborGenerated)
      (chronological_generated_all_real tree rootBound previousGenerated) same
  change ((({ node := node, previous? := some previous } : CanonicalRerootCursor).children mol).map
    (fun cursor => cursor.node.atom)).Perm _
  unfold CanonicalRerootCursor.children
  simp only [leaf, Bool.false_eq_true, ↓reduceIte]
  change ((List.filterMap (fun neighbor => if neighbor == previous then none
    else some ({ node := neighbor, previous? := some node } : CanonicalRerootCursor))
      (({ node := node } : CanonicalRerootCursor).neighbors mol)).map
        (fun cursor => cursor.node.atom)).Perm _
  rw [cut_filter_atoms _ node previous identity, ← distinct.erase_eq_filter previous.atom]
  exact neighbors.erase previous.atom

/-- The lower cursor domain covers ascending and descending edges with no rediscovery. -/
theorem genuine_cursor_cut_atoms_perm {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {cursor : CanonicalRerootCursor}
    (eligible : CanonicalCenterRerootCursor mol root cursor) :
    ((cursor.children mol).map (fun child => child.node.atom)).Perm
      ((rawIncident mol cursor.node.atom).erase ((cursor.previous?.map CanonicalBranchNode.atom).getD root)) := by
  cases eligible with
  | @descending parent node parentGenerated member =>
      exact generated_cut_atoms_perm tree rootBound (CanonicalCenterTreeNode.child parentGenerated member) parentGenerated
  | @ascending node previous nodeGenerated member =>
      exact generated_cut_atoms_perm tree rootBound nodeGenerated (CanonicalCenterTreeNode.child nodeGenerated member)

/-- No-previous mapping retains every physical neighbor once. -/
theorem no_previous_map_atoms (nodes : List CanonicalBranchNode) (current : CanonicalBranchNode) :
    ((nodes.filterMap fun node => some ({ node := node, previous? := some current } : CanonicalRerootCursor)).map
      (fun cursor => cursor.node.atom)) = nodes.map CanonicalBranchNode.atom := by
  induction nodes with
  | nil => rfl
  | cons node nodes _ih => simp

/-- A genuine node with no incoming cut enumerates the whole actual physical incident inventory. -/
theorem generated_no_previous_atoms_perm {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) {node : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root node) :
    ((({ node := node } : CanonicalRerootCursor).children mol).map
      (fun child => child.node.atom)).Perm (rawIncident mol node.atom) := by
  have real := chronological_generated_all_real tree rootBound generated
  have leaf : node.forcedLeaf = false := by simp [CanonicalBranchNode.forcedLeaf, real]
  unfold CanonicalRerootCursor.children
  simp only [leaf, Bool.false_eq_true, ↓reduceIte]
  rw [no_previous_map_atoms]
  exact generated_neighbors_atoms_perm tree rootBound generated

end TetraStereo.UniversalProof.NativeGeneratedCursorPhysicalCut
