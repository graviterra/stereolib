import TetraStereo.OneCenter.ChronologicalPhysicalTree
import TetraStereo.OneCenter.ProductionCIPExactExpansion
import TetraStereo.UniversalProof.NextFrontier.NativeGeneratedRealNodeInventory
import Mathlib.Data.List.Nodup

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeChronologicalChildMultiplicity
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking

/-- Independent raw target uniqueness also entails oriented-independent raw edge uniqueness. -/
theorem chronological_bondRecordsUnique {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) : mol.BondRecordsUnique := by
  have records : mol.bonds.Nodup := List.Nodup.of_map RawBond.target tree.2.2.1
  apply records.map_on
  intro a ha b hb sameKey
  have aOrder := (tree.2.1 a ha).2.1
  have bOrder := (tree.2.1 b hb).2.1
  have targets := congrArg Prod.snd sameKey
  simp only [RawBond.edgeKey, Nat.max_eq_right (Nat.le_of_lt aOrder),
    Nat.max_eq_right (Nat.le_of_lt bOrder)] at targets
  exact List.inj_on_of_nodup_map tree.2.2.1 ha hb targets

/-- Folding actual single raw bond records never creates multiplicity above one. -/
theorem single_raw_fold_le_one (bonds : List RawBond)
    (single : ∀ bond ∈ bonds, bond.kind = .single) (u v accumulator : Nat)
    (initial : accumulator ≤ 1) :
    bonds.foldl (fun order bond =>
      if bond.directedConnects u v then max order bond.kind.order else order) accumulator ≤ 1 := by
  induction bonds generalizing accumulator with
  | nil => exact initial
  | cons bond bonds ih =>
      simp only [List.foldl_cons]
      apply ih (fun b hb => single b (List.mem_cons_of_mem bond hb))
      by_cases connects : bond.directedConnects u v = true
      · simp only [connects, ↓reduceIte]
        rw [single bond List.mem_cons_self]
        change max accumulator 1 ≤ 1
        exact max_le initial (Nat.le_refl 1)
      · simp only [connects]
        exact initial

/-- Actual physical bond order is zero or one throughout the chronological raw domain. -/
theorem chronological_bondOrder_le_one {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) (u v : Nat) : mol.bondOrder u v ≤ 1 := by
  have directed : ∀ a b, mol.directedBondOrder a b ≤ 1 := by
    intro a b
    exact single_raw_fold_le_one mol.bonds (fun bond member => (tree.2.1 bond member).1)
      a b 0 (by decide)
  unfold RawMolecule.bondOrder
  split_ifs
  · exact Nat.zero_le 1
  · exact max_le (directed u v) (directed v u)

/-- Root-edge coordination conventions can lower order to one, never increase single raw order. -/
theorem chronological_canonicalBondOrder_le_one {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) (node : CanonicalBranchNode) (next : Nat) :
    mol.canonicalBondOrder node next ≤ 1 := by
  unfold RawMolecule.canonicalBondOrder
  split <;> (try split_ifs) <;>
    first | exact Nat.le_refl 1 | exact chronological_bondOrder_le_one tree node.atom next

/-- Every actually emitted child copy has zero copy-index; the order bound is derived. -/
theorem chronological_child_copy_index_zero {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) (node : CanonicalBranchNode) (copy : Nat × Nat)
    (member : copy ∈ mol.canonicalChildCopies node) : copy.2 = 0 := by
  obtain ⟨bond, bondMember, endpoints, index⟩ := mol.canonicalChildCopies_source node copy member
  have upper := chronological_canonicalBondOrder_le_one tree node copy.1
  omega

/-- Actual copies with the same physical atom are identical pairs, not different multiplicities. -/
theorem chronological_same_atom_copies_equal {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) (node : CanonicalBranchNode) (a b : Nat × Nat)
    (aMember : a ∈ mol.canonicalChildCopies node) (bMember : b ∈ mol.canonicalChildCopies node)
    (sameAtom : a.1 = b.1) : a = b := by
  apply Prod.ext sameAtom
  exact (chronological_child_copy_index_zero tree node a aMember).trans
    (chronological_child_copy_index_zero tree node b bMember).symm

/-- Mancude labels do not alter child multiplicity: emitted children can only be real or rings.
    Ring exclusion for genuine generated paths remains the next separate proof cut. -/
theorem chronological_children_real_or_ring {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {parent child : CanonicalBranchNode}
    (member : child ∈ mol.canonicalChildren parent) :
    child.provenance = .realAtom ∨ ∃ distance, child.provenance = .ringDuplicate distance := by
  unfold RawMolecule.canonicalChildren at member
  by_cases leaf : parent.forcedLeaf
  · simp [leaf] at member
  · simp only [leaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at member
    obtain ⟨copy, copyMember, rfl⟩ := member
    have zero := chronological_child_copy_index_zero tree parent copy copyMember
    by_cases seen : copy.1 ∈ parent.history
    · right
      exact ⟨canonicalHistoryDistance parent copy.1, by simp [zero, seen]⟩
    · left
      simp [zero, seen]


/-- Public local expansion of the production bond-to-copy generator. -/
def copiesFromBond (mol : RawMolecule) (node : CanonicalBranchNode)
    (bond : RawBond) : List (Nat × Nat) :=
  let next? := if bond.source == node.atom then some bond.target
    else if bond.target == node.atom then some bond.source else none
  match next? with
  | none => []
  | some next => (List.range (mol.canonicalBondOrder node next)).map fun index => (next, index)

def childCopySeeds (mol : RawMolecule) (node : CanonicalBranchNode) : List (Nat × Nat) :=
  mol.bonds.flatMap (copiesFromBond mol node)

theorem canonicalChildCopies_eq_erasedSeeds (mol : RawMolecule) (node : CanonicalBranchNode) :
    mol.canonicalChildCopies node = eraseCanonicalParentCopy node.parent (childCopySeeds mol node) := rfl

/-- One raw record never emits a repeated pair, independently of its order. -/
theorem copiesFromBond_nodup (mol : RawMolecule) (node : CanonicalBranchNode) (bond : RawBond) :
    (copiesFromBond mol node bond).Nodup := by
  unfold copiesFromBond
  split_ifs <;> simp only
  · exact List.nodup_range.map (fun a b same => congrArg Prod.snd same)
  · exact List.nodup_range.map (fun a b same => congrArg Prod.snd same)
  · exact List.nodup_nil

/-- Each seed's atom is an actual endpoint opposite the current atom. -/
theorem copiesFromBond_endpoints {mol : RawMolecule} {node : CanonicalBranchNode}
    {bond : RawBond} {copy : Nat × Nat} (member : copy ∈ copiesFromBond mol node bond) :
    (bond.source = node.atom ∧ bond.target = copy.1) ∨
      (bond.target = node.atom ∧ bond.source = copy.1) := by
  by_cases source : bond.source = node.atom
  · simp [copiesFromBond, source] at member
    obtain ⟨index, _range, rfl⟩ := member
    exact Or.inl ⟨source, rfl⟩
  · by_cases target : bond.target = node.atom
    · simp [copiesFromBond, source, target] at member
      obtain ⟨index, _range, rfl⟩ := member
      exact Or.inr ⟨target, rfl⟩
    · simp [copiesFromBond, source, target] at member

/-- Two records sharing an emitted pair represent the same unordered physical edge. -/
theorem copiesFromBond_shared_edge {mol : RawMolecule} {node : CanonicalBranchNode}
    {a b : RawBond} {copy : Nat × Nat}
    (left : copy ∈ copiesFromBond mol node a) (right : copy ∈ copiesFromBond mol node b) :
    a.edgeKey = b.edgeKey := by
  rcases copiesFromBond_endpoints left with left | left <;>
    rcases copiesFromBond_endpoints right with right | right <;>
    simp only [RawBond.edgeKey, left.1, left.2, right.1, right.2, Nat.min_comm, Nat.max_comm]

/-- Raw target uniqueness derives distinct complete copy seeds, without an inventory premise. -/
theorem chronological_childCopySeeds_nodup {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) (node : CanonicalBranchNode) :
    (childCopySeeds mol node).Nodup := by
  unfold childCopySeeds
  apply List.nodup_flatMap.mpr
  refine ⟨fun bond _member => copiesFromBond_nodup mol node bond, ?_⟩
  have rawNodup : mol.bonds.Nodup := List.Nodup.of_map RawBond.target tree.2.2.1
  apply rawNodup.imp_of_mem
  intro a b aMember bMember different copy left right
  apply different
  exact List.inj_on_of_nodup_map (chronological_bondRecordsUnique tree) aMember bMember
    (copiesFromBond_shared_edge left right)

/-- Erasing the actual parent preserves the derived pair inventory. -/
theorem chronological_canonicalChildCopies_nodup {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) (node : CanonicalBranchNode) :
    (mol.canonicalChildCopies node).Nodup := by
  rw [canonicalChildCopies_eq_erasedSeeds, eraseCanonicalParentCopy_eq_erase]
  exact (chronological_childCopySeeds_nodup tree node).erase (node.parent, 0)

/-- The parent is absent after one erasure because the unerased inventory was already distinct. -/
theorem chronological_parent_copy_absent {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) (node : CanonicalBranchNode) :
    (node.parent, 0) ∉ mol.canonicalChildCopies node := by
  rw [canonicalChildCopies_eq_erasedSeeds, eraseCanonicalParentCopy_eq_erase]
  exact (chronological_childCopySeeds_nodup tree node).not_mem_erase

/-- Zero copy-index makes the complete copy inventory also a distinct physical-atom inventory. -/
theorem chronological_copy_atoms_nodup {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) (node : CanonicalBranchNode) :
    ((mol.canonicalChildCopies node).map Prod.fst).Nodup := by
  apply (chronological_canonicalChildCopies_nodup tree node).map_on
  intro a aMember b bMember same
  exact chronological_same_atom_copies_equal tree node a b aMember bMember same

/-- Actual emitted child nodes are distinct, by injectivity of their physical-atom field. -/
theorem chronological_canonicalChildren_nodup {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) (node : CanonicalBranchNode) :
    (mol.canonicalChildren node).Nodup := by
  unfold RawMolecule.canonicalChildren
  split_ifs
  · exact List.nodup_nil
  · apply (chronological_canonicalChildCopies_nodup tree node).map_on
    intro a aMember b bMember same
    exact chronological_same_atom_copies_equal tree node a b aMember bMember
      (congrArg CanonicalBranchNode.atom same)

open TetraStereo.UniversalProof.NativeGeneratedRealPaths
open TetraStereo.UniversalProof.NativeChronologicalTreeSimplePathUniqueness
open TetraStereo.UniversalProof.NativeChronologicalTreeAcyclic
open TetraStereo.UniversalProof.NativeGeneratedRealNodeInventory

/-- In the actual acyclic physical graph, a visited adjacent atom is the stored parent.
The root-path is derived from genuine real generation; no ancestor exclusion is assumed. -/
theorem generated_visited_neighbor_is_parent {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root node)
    (real : node.provenance = .realAtom) {neighbor : Nat}
    (visited : neighbor ∈ node.history) (positive : 0 < mol.bondOrder neighbor node.atom) :
    neighbor = node.parent := by
  have supported := generated_real_root_path rootBound tree.wellFormed generated real
  obtain ⟨path, support⟩ := raw_supported_realizes_path supported
  have member : neighbor ∈ path.val.support := by
    rw [support]
    exact List.mem_reverse.mpr visited
  let before := path.val.takeUntil neighbor member
  have beforeSimple : before.IsPath := path.property.takeUntil member
  have neighborBound : neighbor < mol.atomCount :=
    supported.2.2.2.2 neighbor (List.mem_reverse.mpr visited)
  have currentBound : node.atom < mol.atomCount :=
    supported.2.2.2.2 node.atom (List.mem_of_getLast? supported.2.2.2.1)
  have adjacent : (physicalGraph mol).Adj neighbor node.atom :=
    ⟨neighborBound, currentBound, positive⟩
  have extension := (chronological_physicalGraph_acyclic tree).path_concat
    beforeSimple path.property adjacent member
  have history : node.history = node.atom :: before.support.reverse := by
    have sameSupport := congrArg SimpleGraph.Walk.support extension
    rw [support, SimpleGraph.Walk.support_concat] at sameSupport
    have reversed := congrArg List.reverse sameSupport
    simpa only [List.reverse_reverse, List.concat_eq_append, List.reverse_append,
      List.reverse_singleton, List.singleton_append] using reversed
  have last : before.support.getLast? = some neighbor := by
    rw [List.getLast?_eq_some_getLast before.support_ne_nil]
    simp only [SimpleGraph.Walk.getLast_support]
  rw [generated_parent_from_history generated, history]
  simp only [List.tail_cons, List.head?_reverse, last, Option.getD_some]

/-- Actual child generation from a real generated node cannot revisit an ancestor.
The sole adjacent ancestor is the stored parent, whose unit copy was actually erased. -/
theorem chronological_child_not_visited {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    {parent : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root parent)
    (real : parent.provenance = .realAtom) {copy : Nat × Nat}
    (member : copy ∈ mol.canonicalChildCopies parent) : copy.1 ∉ parent.history := by
  intro visited
  obtain ⟨bond, bondMember, endpoints, copyBound⟩ :=
    mol.canonicalChildCopies_source parent copy member
  have positive : 0 < mol.canonicalBondOrder parent copy.1 := by omega
  have physical := mol.canonicalBondOrder_pos_imp_bondOrder_pos parent copy.1
    generated.history_head positive
  have same := generated_visited_neighbor_is_parent tree rootBound generated real visited
    (by rwa [mol.bondOrder_symm parent.atom copy.1] at physical)
  have zero := chronological_child_copy_index_zero tree parent copy member
  have copyEq : copy = (parent.parent, 0) := Prod.ext same zero
  exact chronological_parent_copy_absent tree parent (copyEq ▸ member)

/-- Every actual child of a genuine real generated node is real; no desired provenance premise. -/
theorem chronological_children_real {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    {parent child : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root parent)
    (real : parent.provenance = .realAtom) (member : child ∈ mol.canonicalChildren parent) :
    child.provenance = .realAtom := by
  unfold RawMolecule.canonicalChildren at member
  by_cases leaf : parent.forcedLeaf
  · simp [leaf] at member
  · simp only [leaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at member
    obtain ⟨copy, copyMember, rfl⟩ := member
    have zero := chronological_child_copy_index_zero tree parent copy copyMember
    have fresh := chronological_child_not_visited tree rootBound generated real copyMember
    simp [zero, fresh]

/-- The entire genuine generated tree contains real nodes only, derived by generation induction. -/
theorem chronological_generated_all_real {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root node) :
    node.provenance = .realAtom := by
  induction generated with
  | root => rfl
  | @child parent child parentGenerated member ih =>
      exact chronological_children_real tree rootBound parentGenerated ih member

end TetraStereo.UniversalProof.NativeChronologicalChildMultiplicity
