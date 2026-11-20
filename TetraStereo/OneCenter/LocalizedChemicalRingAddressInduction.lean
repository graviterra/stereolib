import TetraStereo.OneCenter.LocalizedChemicalRingReaddressedTree
import Mathlib.Data.List.Forall2
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! A root relation that is preserved at every pair of corresponding child slots is preserved
at every shared address of two dense addressings. The node relation is arbitrary; no molecular
atom identification, key equality, or label agreement is built into this structural lemma. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingAddressInduction

open DeclarativeCIP LocalizedChemicalRingReaddressedTree

private theorem forall₂_lookup_right {α β : Type*} {R : α → β → Prop}
    {left : List α} {right : List β} (related : List.Forall₂ R left right)
    {slot : Nat} {x : α} (lookup : left[slot]? = some x) :
    ∃ y, right[slot]? = some y ∧ R x y := by
  obtain ⟨leftBound, value⟩ := List.getElem?_eq_some_iff.mp lookup
  have rightBound : slot < right.length := by
    rw [← related.length_eq]
    exact leftBound
  refine ⟨right[slot], List.getElem?_eq_getElem rightBound, ?_⟩
  have pair : R left[slot] right[slot] := related.get leftBound rightBound
  rw [value] at pair
  exact pair

section Propagation

variable {AtomL AtomR : Type}
    (left : RootedDigraph AtomL) (right : RootedDigraph AtomR)
    (addressL : left.Addressing) (addressR : right.Addressing)
    (denseL : Dense addressL) (denseR : Dense addressR)
    (R : left.Node → right.Node → Prop)
    (roots : R left.root right.root)
    (children : ∀ x y, R x y →
      List.Forall₂ R (orderedChildren left addressL denseL x)
        (orderedChildren right addressR denseR y))

include roots children in
/-- Every left node has a related right node at exactly the same address. -/
theorem exists_related_at_address (x : left.Node) :
    ∃ y, addressR.address y = addressL.address x ∧ R x y := by
  induction left.reachable x with
  | refl =>
      exact ⟨right.root, addressR.root_address.trans addressL.root_address.symm, roots⟩
  | @tail parent node _ edge ih =>
      obtain ⟨otherParent, parentAddress, parents⟩ := ih
      obtain ⟨slot, nodeAddress⟩ := (addressL.child_iff parent node).mp edge
      have lookup := (orderedChildren_get_iff left addressL denseL parent node slot).mpr nodeAddress
      obtain ⟨otherNode, otherLookup, nodes⟩ :=
        forall₂_lookup_right (children parent otherParent parents) lookup
      have otherAddress :=
        (orderedChildren_get_iff right addressR denseR otherParent otherNode slot).mp otherLookup
      refine ⟨otherNode, ?_, nodes⟩
      exact otherAddress.trans ((congrArg (fun position => position ++ [slot]) parentAddress).trans
        nodeAddress.symm)

include roots children in
/-- Slot preservation propagates to the existing addressings, without choosing new orders. -/
theorem related_of_address_eq (x : left.Node) (y : right.Node)
    (same : addressL.address x = addressR.address y) : R x y := by
  obtain ⟨other, address, related⟩ :=
    exists_related_at_address left right addressL addressR denseL denseR R roots children x
  have equal : other = y := addressR.address_injective (address.trans same)
  exact equal ▸ related

end Propagation

section SortedChildren

variable {Atom : Type} (graph : RootedDigraph Atom)
    (addressing : graph.Addressing) (dense : Dense addressing)

/-- Any relation ordered by sibling slot numbers is pairwise on the actual dense slot list. -/
theorem orderedChildren_pairwise (R : graph.Node → graph.Node → Prop)
    (ordered : ∀ parent first second firstSlot secondSlot,
      addressing.address first = addressing.address parent ++ [firstSlot] →
      addressing.address second = addressing.address parent ++ [secondSlot] →
      firstSlot < secondSlot → R first second)
    (parent : graph.Node) :
    (orderedChildren graph addressing dense parent).Pairwise R := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  exact ordered parent _ _ i j
    ((orderedChildren_get_iff graph addressing dense parent _ i).mp (List.getElem?_eq_getElem hi))
    ((orderedChildren_get_iff graph addressing dense parent _ j).mp (List.getElem?_eq_getElem hj)) hij

/-- A key-sorted addressing lists each parent's child keys in descending order. -/
theorem orderedChildren_keySorted {K : Type*} [LinearOrder K]
    (key : graph.Node → K) (sorted : KeySorted key addressing) (parent : graph.Node) :
    (orderedChildren graph addressing dense parent).Pairwise (fun a b => key b ≤ key a) :=
  orderedChildren_pairwise graph addressing dense _ sorted parent

end SortedChildren
end TetraStereo.OneCenter.LocalizedChemicalRingAddressInduction

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAddressInduction.exists_related_at_address
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAddressInduction.related_of_address_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAddressInduction.orderedChildren_pairwise
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingAddressInduction.orderedChildren_keySorted
