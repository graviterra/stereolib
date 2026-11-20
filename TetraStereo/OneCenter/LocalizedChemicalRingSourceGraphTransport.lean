import TetraStereo.OneCenter.LocalizedRetainedContextStageGraphIso
import TetraStereo.OneCenter.DeclarativeCIPRetainedRelabelTransport
import TetraStereo.OneCenter.LocalizedRetainedOccurrenceTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Structural relabelling of source-tree graphs. Atom names move; hierarchy addresses and
duplicate provenance remain intact. Sibling permutations are assembled through the existing
source-tree isomorphism construction. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingSourceGraphTransport

open DeclarativeCIP CertifiedLocalizedCIPInput
open Rule4aTableBridge

variable {Atom : Type} [DecidableEq Atom]

mutual
  def mapTree (e : Equiv.Perm Atom) : OfficialCIPSourceTree Atom → OfficialCIPSourceTree Atom
    | .node source children => .node (mapOfficialNode e source) (mapForest e children)
    termination_by tree => sizeOf tree
    decreasing_by simp_wf

  def mapForest (e : Equiv.Perm Atom) : List (OfficialCIPSourceTree Atom) →
      List (OfficialCIPSourceTree Atom)
    | [] => []
    | tree :: trees => mapTree e tree :: mapForest e trees
    termination_by trees => sizeOf trees
    decreasing_by all_goals (simp_wf <;> omega)
end

theorem mapForest_eq (e : Equiv.Perm Atom) (trees : List (OfficialCIPSourceTree Atom)) :
    mapForest e trees = trees.map (mapTree e) := by
  induction trees with
  | nil => simp [mapForest]
  | cons t ts ih => simp [mapForest, ih]

theorem mapTree_node (e : Equiv.Perm Atom) (source : OfficialCIPNode Atom)
    (children : List (OfficialCIPSourceTree Atom)) :
    mapTree e (.node source children) = .node (mapOfficialNode e source) (children.map (mapTree e)) := by
  rw [mapTree, mapForest_eq]

mutual
  theorem occurrences_mapTree (e : Equiv.Perm Atom) (tree : OfficialCIPSourceTree Atom) :
      (mapTree e tree).occurrences = tree.occurrences.map
        (fun entry => (entry.1, mapOfficialNode e entry.2)) := by
    cases tree with
    | node source children =>
        rw [mapTree, OfficialCIPSourceTree.occurrences, OfficialCIPSourceTree.occurrences,
          forestOccurrences_mapForest]
        rfl
    termination_by sizeOf tree
    decreasing_by simp_wf

  theorem forestOccurrences_mapForest (e : Equiv.Perm Atom)
      (trees : List (OfficialCIPSourceTree Atom)) (start : Nat) :
      OfficialCIPSourceTree.forestOccurrences (mapForest e trees) start =
        (OfficialCIPSourceTree.forestOccurrences trees start).map
          (fun entry => (entry.1, mapOfficialNode e entry.2)) := by
    cases trees with
    | nil => simp [mapForest, OfficialCIPSourceTree.forestOccurrences]
    | cons tree trees =>
        rw [mapForest, OfficialCIPSourceTree.forestOccurrences,
          OfficialCIPSourceTree.forestOccurrences, occurrences_mapTree,
          forestOccurrences_mapForest]
        simp only [List.map_append, List.map_map, Function.comp_def]
    termination_by sizeOf trees
    decreasing_by all_goals (simp_wf <;> omega)
end

theorem hierarchyAddresses_mapTree (e : Equiv.Perm Atom) (tree : OfficialCIPSourceTree Atom) :
    (mapTree e tree).hierarchyAddresses = tree.hierarchyAddresses := by
  simp [OfficialCIPSourceTree.hierarchyAddresses, occurrences_mapTree, List.flatMap_map]

theorem source_mapTree (e : Equiv.Perm Atom) (tree : OfficialCIPSourceTree Atom) :
    (mapTree e tree).source = mapOfficialNode e tree.source := by
  cases tree
  simp [mapTree, OfficialCIPSourceTree.source]

theorem subtreeAt_mapTree (e : Equiv.Perm Atom) (address : List Nat)
    (tree : OfficialCIPSourceTree Atom) :
    (mapTree e tree).subtreeAt? address = (tree.subtreeAt? address).map (mapTree e) := by
  induction address generalizing tree with
  | nil => rfl
  | cons i rest ih =>
      cases tree with
      | node source children =>
          rw [mapTree_node]
          simp only [OfficialCIPSourceTree.subtreeAt?, List.getElem?_map]
          cases children[i]? <;> simp [ih]

theorem sourceAt_mapTree (e : Equiv.Perm Atom) (tree : OfficialCIPSourceTree Atom)
    (address : List Nat) :
    (mapTree e tree).sourceAtAddress? address =
      (tree.sourceAtAddress? address).map (mapOfficialNode e) := by
  simp only [OfficialCIPSourceTree.sourceAtAddress?, subtreeAt_mapTree, Option.map_map]
  congr 1
  funext t
  exact source_mapTree e t

theorem toDeclarativeLabel_map (e : Equiv.Perm Atom) (node : OfficialCIPNode Atom) :
    (mapOfficialNode e node).toDeclarativeLabel = mapNodeLabel e node.toDeclarativeLabel := by
  cases node
  simp [mapOfficialNode, OfficialCIPNode.toDeclarativeLabel, mapNodeLabel]

noncomputable def treeRelabel (e : Equiv.Perm Atom) (tree : OfficialCIPSourceTree Atom) :
    RootedDigraph.Relabel e tree.toDeclarativeDigraph (mapTree e tree).toDeclarativeDigraph where
  toEquiv :=
    { toFun := fun node => ⟨node.1, by rw [hierarchyAddresses_mapTree]; exact node.2⟩
      invFun := fun node => ⟨node.1, by rw [← hierarchyAddresses_mapTree e tree]; exact node.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_root := rfl
  map_child := fun _ _ => Iff.rfl
  map_depth := fun _ => rfl
  map_label := by
    intro node
    change mapNodeLabel e (tree.declarativeLabel node) =
      (mapTree e tree).declarativeLabel ⟨node.1, _⟩
    unfold OfficialCIPSourceTree.declarativeLabel
    rw [sourceAt_mapTree]
    cases h : tree.sourceAtAddress? node.1
    · rfl
    · simp only [Option.map_some, toDeclarativeLabel_map]

/-- Two images under the same atom relabelling are atom-preservingly isomorphic. -/
def commonImageIso {e : Equiv.Perm Atom} {left first second : RootedDigraph Atom}
    (a : RootedDigraph.Relabel e left first) (b : RootedDigraph.Relabel e left second) :
    RootedDigraph.Iso first second where
  toEquiv := a.toEquiv.symm.trans b.toEquiv
  map_root := by simp [Equiv.trans_apply, ← a.map_root, b.map_root]
  map_child := by
    intro x y
    have ha := (a.map_child (a.toEquiv.symm x) (a.toEquiv.symm y)).symm
    simp only [Equiv.apply_symm_apply] at ha
    exact ha.trans (b.map_child _ _)
  map_label := by
    intro x
    have ha := (a.map_label (a.toEquiv.symm x)).symm
    simp only [Equiv.apply_symm_apply] at ha
    exact ha.trans (b.map_label _)
  map_depth := by
    intro x
    have ha := (a.map_depth (a.toEquiv.symm x)).symm
    simp only [Equiv.apply_symm_apply] at ha
    exact ha.trans (b.map_depth _)

def relabelThenIso {e : Equiv.Perm Atom} {left middle right : RootedDigraph Atom}
    (a : RootedDigraph.Relabel e left middle) (b : RootedDigraph.Iso middle right) :
    RootedDigraph.Relabel e left right where
  toEquiv := a.toEquiv.trans b.toEquiv
  map_root := by simp [Equiv.trans_apply, a.map_root, b.map_root]
  map_child := fun x y => (a.map_child x y).trans (b.map_child _ _)
  map_label := fun x => (a.map_label x).trans (b.map_label _)
  map_depth := fun x => (a.map_depth x).trans (b.map_depth _)

/-- Relabelled child graphs assemble into a relabelled parent, regardless of sibling order. -/
noncomputable def nodeRelabel (e : Equiv.Perm Atom) (source : OfficialCIPNode Atom)
    (left right : List (OfficialCIPSourceTree Atom))
    (slots : Fin left.length ≃ Fin right.length)
    (children : ∀ i, RootedDigraph.Relabel e (left.get i).toDeclarativeDigraph
      (right.get (slots i)).toDeclarativeDigraph) :
    RootedDigraph.Relabel e (OfficialCIPSourceTree.node source left).toDeclarativeDigraph
      (OfficialCIPSourceTree.node (mapOfficialNode e source) right).toDeclarativeDigraph := by
  let mapped := left.map (mapTree e)
  let castSlots : Fin mapped.length ≃ Fin left.length := finCongr (List.length_map _)
  let mappedSlots := castSlots.trans slots
  have childIso : ∀ i : Fin mapped.length,
      RootedDigraph.Iso (mapped.get i).toDeclarativeDigraph
        (right.get (mappedSlots i)).toDeclarativeDigraph := by
    intro i
    have h := commonImageIso (treeRelabel e (left.get (castSlots i))) (children (castSlots i))
    simpa [mapped, castSlots, mappedSlots, List.get_eq_getElem] using h
  have iso := sourceTreeSiblingGraphIso (mapOfficialNode e source) mapped right mappedSlots childIso
  have rel := treeRelabel e (.node source left)
  rw [mapTree_node] at rel
  exact relabelThenIso rel iso

end TetraStereo.OneCenter.LocalizedChemicalRingSourceGraphTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourceGraphTransport.treeRelabel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourceGraphTransport.nodeRelabel
