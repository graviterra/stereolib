import TetraStereo.OneCenter.LocalizedChemicalRingReaddressedTree
import TetraStereo.OneCenter.LocalizedActualCanonicalConstitutionalRefinement
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Readdressing an actual source tree preserves generation

The generic dense-address materialization is instantiated with the complete source nodes of an
existing official tree. Its enumerator premise is derived from that tree's generatedness.
Thus promoted addressings can be supplied to the existing residual-path reconstruction without
pretending that the original sibling order was already promoted-canonical.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReaddressedSource

open DeclarativeCIP LocalizedChemicalRingReaddressedTree OfficialCIPSourceTree
open scoped Classical
noncomputable section

variable {V : Type} [DecidableEq V] (tree : OfficialCIPSourceTree V)

def payload (node : tree.toDeclarativeDigraph.Node) : OfficialCIPNode V :=
  (tree.sourceAtAddress? node.1).getD tree.source

theorem payload_lookup (node : tree.toDeclarativeDigraph.Node) :
    tree.sourceAtAddress? node.1 = some (payload tree node) := by
  obtain ⟨sub, _, lookup⟩ := tree.exists_source_lookup node
  simp only [payload, lookup, Option.getD_some]

theorem payload_of_lookup (node : tree.toDeclarativeDigraph.Node)
    (sub : OfficialCIPSourceTree V) (lookup : tree.subtreeAt? node.1 = some sub) :
    payload tree node = sub.source := by
  simp only [payload, sourceAtAddress?, lookup, Option.map_some, Option.getD_some]

omit [DecidableEq V] in
theorem source_child_lookup (position : List Nat) (sub : OfficialCIPSourceTree V)
    (lookup : tree.subtreeAt? position = some sub) (slot : Nat) :
    tree.sourceAtAddress? (position ++ [slot]) = (sub.children[slot]?).map source := by
  unfold sourceAtAddress?
  rw [tree.subtreeAt?_append, lookup, Option.bind_some]
  cases sub with
  | node src children =>
      simp only [OfficialCIPSourceTree.subtreeAt?, OfficialCIPSourceTree.children]
      cases children[slot]? <;> rfl

theorem original_children_sources (node : tree.toDeclarativeDigraph.Node)
    (sub : OfficialCIPSourceTree V) (lookup : tree.subtreeAt? node.1 = some sub) :
    (orderedChildren tree.toDeclarativeDigraph tree.declarativeAddressing
      tree.declarativeAddressing_dense node).map (payload tree) = sub.children.map source := by
  apply List.ext_getElem?
  intro slot
  simp only [List.getElem?_map]
  cases found : (orderedChildren tree.toDeclarativeDigraph tree.declarativeAddressing
      tree.declarativeAddressing_dense node)[slot]? with
  | some child =>
      have address := (orderedChildren_get_iff tree.toDeclarativeDigraph tree.declarativeAddressing
        tree.declarativeAddressing_dense node child slot).mp found
      change child.1 = node.1 ++ [slot] at address
      have read := payload_lookup tree child
      rw [address, source_child_lookup tree node.1 sub lookup slot] at read
      exact read.symm
  | none =>
      cases childLookup : sub.children[slot]? with
      | none => rfl
      | some childSub =>
          have actualLookup : tree.subtreeAt? (node.1 ++ [slot]) = some childSub := by
            rw [tree.subtreeAt?_append, lookup, Option.bind_some]
            cases sub with
            | node src children =>
                change children[slot]? = some childSub at childLookup
                simp only [OfficialCIPSourceTree.subtreeAt?, childLookup]
          have present := mem_hierarchyAddresses_of_occurrence tree
            (node.1 ++ [slot], childSub.source)
            (mem_occurrences_of_subtreeAt?_eq_some _ tree childSub actualLookup)
          let child : tree.toDeclarativeDigraph.Node := ⟨node.1 ++ [slot], present⟩
          have orderedLookup := (orderedChildren_get_iff tree.toDeclarativeDigraph
            tree.declarativeAddressing tree.declarativeAddressing_dense node child slot).mpr rfl
          rw [found] at orderedLookup
          cases orderedLookup

theorem local_enumerator_law (enumerate : OfficialCIPNode V → List (OfficialCIPNode V))
    (generated : tree.GeneratedBy enumerate) (node : tree.toDeclarativeDigraph.Node) :
    ((tree.toDeclarativeDigraph.childList node).map (payload tree)).Perm
      (enumerate (payload tree node)) := by
  obtain ⟨sub, lookup⟩ := tree.exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses node.1 node.2
  have subGenerated := GeneratedBy.of_subtreeAt? enumerate node.1 tree sub generated lookup
  have ordered := ((orderedChildren_perm tree.toDeclarativeDigraph tree.declarativeAddressing
    tree.declarativeAddressing_dense node).symm.map (payload tree))
  rw [original_children_sources tree node sub lookup] at ordered
  rw [payload_of_lookup tree node sub lookup]
  cases sub with
  | node src children => exact ordered.trans subGenerated.1

variable (addressing : tree.toDeclarativeDigraph.Addressing) (dense : Dense addressing)

def readdressed : OfficialCIPSourceTree V :=
  atNode tree.toDeclarativeDigraph addressing dense (payload tree) tree.toDeclarativeDigraph.root

theorem readdressed_source : (readdressed tree addressing dense).source = tree.source := by
  rw [readdressed, source_atNode]
  rfl

/-- No child-order premise is needed: generatedness survives every dense readdressing. -/
theorem readdressed_generated (enumerate : OfficialCIPNode V → List (OfficialCIPNode V))
    (generated : tree.GeneratedBy enumerate) :
    (readdressed tree addressing dense).GeneratedBy enumerate :=
  LocalizedChemicalRingReaddressedTree.generated tree.toDeclarativeDigraph addressing dense
    (payload tree) enumerate (local_enumerator_law tree enumerate generated) _

/-- Complete source-node readback in the new addressing; absent addresses are not invented. -/
theorem readdressed_lookup_iff (position : List Nat) (source : OfficialCIPNode V) :
    (readdressed tree addressing dense).sourceAtAddress? position = some source ↔
      ∃ node, addressing.address node = position ∧ payload tree node = source := by
  rw [readdressed, sourceAt_eq_some_iff, addressing.root_address, List.nil_append]

end
end TetraStereo.OneCenter.LocalizedChemicalRingReaddressedSource

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReaddressedSource.local_enumerator_law
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReaddressedSource.readdressed_source
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReaddressedSource.readdressed_generated
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReaddressedSource.readdressed_lookup_iff
