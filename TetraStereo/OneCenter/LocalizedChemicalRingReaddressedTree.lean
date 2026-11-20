import TetraStereo.OneCenter.DeclarativeCIPCanonicalAddressing
import TetraStereo.OneCenter.AuthoritativeLocalizedRule1bConformance
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Materializing a dense addressing without changing source occurrences

An arbitrary dense addressing of a finite rooted hierarchy determines an official source tree.
The construction retains each node's complete source payload, including its molecular history.
Source lookup realizes the chosen addressing exactly. A local enumerator law suffices to prove
generatedness; no ordering compatibility with the old source tree is assumed.

This is a structural adapter for the promoted-address residual-path bridge. It does not supply
constitutional observation agreement or a chemical meaning for auxiliary descriptors.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReaddressedTree

open DeclarativeCIP
open scoped Classical
noncomputable section

variable {V : Type} (graph : RootedDigraph V) (addressing : graph.Addressing)
  (dense : Dense addressing)

def count (node : graph.Node) : Nat := Classical.choose (dense node)

theorem count_dense (node : graph.Node) : DenseAt addressing node (count graph addressing dense node) :=
  Classical.choose_spec (dense node)

def orderedChildren (node : graph.Node) : List graph.Node :=
  slotList addressing node (count graph addressing dense node)

theorem orderedChildren_perm (node : graph.Node) :
    (orderedChildren graph addressing dense node).Perm (graph.childList node) :=
  slotList_perm (count_dense graph addressing dense node)

theorem orderedChildren_mem (node child : graph.Node) :
    child ∈ orderedChildren graph addressing dense node ↔ graph.child node child := by
  rw [(orderedChildren_perm graph addressing dense node).mem_iff, graph.mem_childList]

theorem orderedChildren_length (node : graph.Node) :
    (orderedChildren graph addressing dense node).length = count graph addressing dense node := by
  simp [orderedChildren, slotList]

theorem orderedChildren_get_iff (node child : graph.Node) (slot : Nat) :
    (orderedChildren graph addressing dense node)[slot]? = some child ↔
      addressing.address child = addressing.address node ++ [slot] := by
  constructor
  · intro lookup
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    rw [orderedChildren_length] at bound
    obtain ⟨found, foundLookup, address⟩ :=
      slotList_getD_of_lt (count_dense graph addressing dense node) bound
    have same : found = child := Option.some.inj (foundLookup.symm.trans lookup)
    simpa only [same] using address
  · intro address
    have bound := (count_dense graph addressing dense node slot).mp ⟨child, address⟩
    obtain ⟨found, lookup, foundAddress⟩ :=
      slotList_getD_of_lt (count_dense graph addressing dense node) bound
    have same : found = child := addressing.address_injective (foundAddress.trans address.symm)
    simpa only [same] using lookup

variable (payload : graph.Node → OfficialCIPNode V)

def atNode (node : graph.Node) : OfficialCIPSourceTree V :=
  .node (payload node) ((orderedChildren graph addressing dense node).attach.map
    fun child => atNode child.1)
termination_by graph.height + 1 - graph.depth node
decreasing_by
  have edge := (orderedChildren_mem graph addressing dense node child.1).mp child.2
  have depth := graph.child_depth edge
  have bound := graph.depth_le_height child.1
  omega

theorem atNode_eq (node : graph.Node) :
    atNode graph addressing dense payload node =
      .node (payload node) ((orderedChildren graph addressing dense node).map
        (atNode graph addressing dense payload)) := by
  rw [atNode, List.attach_map_val]

theorem source_atNode (node : graph.Node) :
    (atNode graph addressing dense payload node).source = payload node := by
  rw [atNode_eq]
  rfl

theorem sourceAt_cons (node : graph.Node) (slot : Nat) (path : List Nat) :
    (atNode graph addressing dense payload node).sourceAtAddress? (slot :: path) =
      ((orderedChildren graph addressing dense node)[slot]?).bind
        (fun child => (atNode graph addressing dense payload child).sourceAtAddress? path) := by
  rw [atNode_eq]
  simp only [OfficialCIPSourceTree.sourceAtAddress?, OfficialCIPSourceTree.subtreeAt?,
    List.getElem?_map]
  cases (orderedChildren graph addressing dense node)[slot]? <;> rfl

/-- Lookup at a relative address returns exactly the source payload of its represented node. -/
theorem sourceAt_eq_some_iff (path : List Nat) (node : graph.Node) (source : OfficialCIPNode V) :
    (atNode graph addressing dense payload node).sourceAtAddress? path = some source ↔
      ∃ target, addressing.address target = addressing.address node ++ path ∧
        payload target = source := by
  induction path generalizing node with
  | nil =>
      change some (atNode graph addressing dense payload node).source = some source ↔ _
      rw [source_atNode, Option.some.injEq]
      constructor
      · intro same
        exact ⟨node, by simp, same⟩
      · rintro ⟨target, address, same⟩
        have eq : target = node := addressing.address_injective (by simpa using address)
        simpa only [eq] using same
  | cons slot path ih =>
      rw [sourceAt_cons, Option.bind_eq_some_iff]
      constructor
      · rintro ⟨child, lookup, found⟩
        obtain ⟨target, address, same⟩ := (ih child).mp found
        have childAddress := (orderedChildren_get_iff graph addressing dense node child slot).mp lookup
        exact ⟨target, by simpa [childAddress, List.append_assoc] using address, same⟩
      · rintro ⟨target, address, same⟩
        have occupiedPrefix := addressing.prefix_occupied target
          (addressing.address node ++ [slot]) path
          (by simpa [List.append_assoc] using address)
        obtain ⟨child, childAddress⟩ := occupiedPrefix
        refine ⟨child, (orderedChildren_get_iff graph addressing dense node child slot).mpr childAddress,
          (ih child).mpr ⟨target, ?_, same⟩⟩
        simpa [childAddress, List.append_assoc] using address

/-- Readdressing preserves the exact generated child multiset. -/
theorem generated (enumerate : OfficialCIPNode V → List (OfficialCIPNode V))
    (localLaw : ∀ node, ((graph.childList node).map payload).Perm (enumerate (payload node))) :
    ∀ node, (atNode graph addressing dense payload node).GeneratedBy enumerate := by
  intro root
  apply node_induction graph (motive := fun node =>
    (atNode graph addressing dense payload node).GeneratedBy enumerate) ?_ root
  intro node ih
  rw [atNode_eq, OfficialCIPSourceTree.GeneratedBy]
  constructor
  · simpa only [List.map_map, Function.comp_def, source_atNode] using
      ((orderedChildren_perm graph addressing dense node).map payload).trans (localLaw node)
  · rw [OfficialCIPSourceTree.forestGeneratedBy_iff_forall]
    intro tree member
    obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
    exact ih child ((orderedChildren_mem graph addressing dense node child).mp childMember)

end
end TetraStereo.OneCenter.LocalizedChemicalRingReaddressedTree

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReaddressedTree.orderedChildren_get_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReaddressedTree.sourceAt_eq_some_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReaddressedTree.generated
