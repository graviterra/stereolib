import TetraStereo.OneCenter.CanonicalTreeProfile
import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalChildMultiplicity
import TetraStereo.UniversalProof.NextFrontier.NativeGlobalProfileInventory

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeChronologicalProfileSuccess
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeChronologicalChildMultiplicity
open TetraStereo.UniversalProof.NativeGlobalProfileInventory
open TetraStereo.UniversalProof.NativeGeneratedRealPaths

/-- The shared executable collector agrees with the structural inventory replica for all inputs. -/
theorem collect_eq_collectReplica (fuel cap : Nat) (mol : RawMolecule)
    (nodes : List CanonicalBranchNode) :
    CanonicalTreeProfile.collect fuel cap mol nodes = collectReplica fuel cap mol nodes := by
  induction fuel generalizing cap nodes with
  | zero => cases nodes <;> rfl
  | succ fuel ih =>
      cases nodes with
      | nil => rfl
      | cons first rest =>
          simp only [CanonicalTreeProfile.collect, collectReplica,
            ih (cap - (first :: rest).length) ((first :: rest).flatMap mol.canonicalChildren)]

/-- Every returned finite-inventory member is actual generation, regardless of fuel. -/
theorem inventory_generated {mol : RawMolecule} {root fuel : Nat} {node : CanonicalBranchNode}
    (member : node ∈ inventory mol root fuel) : CanonicalCenterTreeNode mol root node := by
  obtain ⟨level, _inRange, inFrontier⟩ := List.mem_flatMap.mp member
  exact frontier_generated inFrontier

/-- Root collection succeeds from independently checked raw chronological facts alone. -/
theorem chronological_collect_success {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount) :
    CanonicalTreeProfile.collect (mol.atomCount + 1) mol.atomCount mol [canonicalCenterRoot root] =
      some (inventory mol root (mol.atomCount + 1)) := by
  rw [collect_eq_collectReplica]
  exact collectReplica_root_success tree rootBound
    (fun parent _generated => chronological_canonicalChildren_nodup tree parent)
    (fun _parent generated _child member => chronological_generated_all_real tree rootBound
      (CanonicalCenterTreeNode.child generated member))

/-- Every genuine occurrence is included in the exact fuel used by the executable profile. -/
theorem chronological_center_mem_inventory {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    {center : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root center) :
    center ∈ inventory mol root (mol.atomCount + 1) := by
  have member := generated_mem_inventory tree rootBound
    (fun _parent parentGenerated _child childMember => chronological_generated_all_real tree rootBound
      (CanonicalCenterTreeNode.child parentGenerated childMember)) generated
  obtain ⟨level, inRange, inFrontier⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr ⟨level, List.mem_range.mpr
    (Nat.lt_trans (List.mem_range.mp inRange) (Nat.lt_succ_self _)), inFrontier⟩

/-- All executable node guards are derived from genuine generation, never supplied as booleans. -/
theorem chronological_inventory_checks {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    (fuel : Nat) :
    (inventory mol root fuel).all (fun node =>
      node.provenance == .realAtom && node.history.head? == some node.atom &&
      node.history.getLast? == some root && !node.history.isEmpty &&
      decide node.history.Nodup && node.history.all (fun atom => decide (atom < mol.atomCount))) = true := by
  rw [List.all_eq_true]
  intro node member
  have generated := inventory_generated member
  have real := chronological_generated_all_real tree rootBound generated
  obtain ⟨nodup, bounds⟩ := generated.real_history rootBound tree.wellFormed real
  have head := generated.history_head
  have last := generated_history_root_tail generated
  have nonempty : node.history.isEmpty = false := by
    cases stored : node.history with
    | nil => simp [stored] at head
    | cons first rest => rfl
  have bounded : node.history.all (fun atom => decide (atom < mol.atomCount)) = true := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using bounds
  simp [real, head, last, nonempty, nodup, bounded]

/-- Actual executable profile success for every genuinely generated center in the raw tree domain.
The returned original center, immutable center history, and inventory are exact computed values. -/
theorem chronological_profile_success {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    {center : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root center) :
    CanonicalTreeProfile.profile? mol center =
      some ⟨center, ⟨center.history⟩, inventory mol root (mol.atomCount + 1)⟩ := by
  have rootTail := generated_history_root_tail generated
  have endpoints := (mol.wellFormed_iff_all_bondEndpointsOK).mp tree.wellFormed
  have admission : (!(decide (root < mol.atomCount)) ||
      !(mol.bonds.all mol.bondEndpointsOK?)) = false := by
    simp [rootBound, endpoints]
  have collected : CanonicalTreeProfile.collect (mol.atomCount + 1) mol.atomCount mol
      [{ atom := root, parent := root, history := [root], provenance := .realAtom }] =
      some (inventory mol root (mol.atomCount + 1)) :=
    chronological_collect_success tree rootBound
  have member := chronological_center_mem_inventory tree rootBound generated
  have contains : (inventory mol root (mol.atomCount + 1)).contains center = true := by
    simpa using member
  have checked := chronological_inventory_checks tree rootBound (mol.atomCount + 1)
  simp only [CanonicalTreeProfile.profile?, rootTail, Bind.bind, Option.bind,
    admission, collected, contains, checked, Bool.not_true, Bool.false_eq_true, ite_false]

end TetraStereo.UniversalProof.NativeChronologicalProfileSuccess
