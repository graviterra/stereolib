import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey
import TetraStereo.OneCenter.DeclarativeCIPRetainedWindowIndependence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! Joint markers depend on the order of sibling priors, not their encoding.

This removes the literal-prior-equality requirement when replacing compiled deep priors
by mathematically equivalent cut priors or changing their sufficient observation windows.
The marker window itself stays fixed. No runtime correspondence or chemical policy is
assumed or established here: the consumer must derive sibling order agreement.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerPriorOrderCongruence

open DeclarativeCIP
open LocalizedChemicalRingJointMarkerKey
open Certificate.CanonicalSphereKey (sortDesc Desc)

noncomputable section
open scoped Classical

/-- Sorting complete keys with different prior encodings gives the same marker sequence
when their comparisons and marker projections agree on the input list. -/
theorem sorted_marker_projection_eq
    {α P Q : Type*} [LinearOrder P] [LinearOrder Q]
    (entries : List α) (left : α → Lex (P × JointMarker))
    (right : α → Lex (Q × JointMarker))
    (markers : ∀ x ∈ entries, (ofLex (left x)).2 = (ofLex (right x)).2)
    (orders : ∀ x ∈ entries, ∀ y ∈ entries, left y ≤ left x ↔ right y ≤ right x) :
    (sortDesc (entries.map left)).map (fun key => (ofLex key).2) =
      (sortDesc (entries.map right)).map (fun key => (ofLex key).2) := by
  let relation : α → α → Prop := fun x y => left y ≤ left x
  have first := List.map_insertionSort relation Desc left entries
    (fun _ _ _ _ => Iff.rfl)
  have second := List.map_insertionSort relation Desc right entries orders
  change ((entries.map left).insertionSort Desc).map _ =
    ((entries.map right).insertionSort Desc).map _
  rw [← first, ← second, List.map_map, List.map_map]
  apply List.map_congr_left
  intro x member
  exact markers x ((List.mem_insertionSort relation).mp member)

/-- Only comparisons of siblings matter to the recursively sorted marker. Priors may
have different types and different values; strict order and ties must agree locally. -/
theorem jointMarkerKey_eq_of_sibling_order
    {Atom P Q : Type*} [LinearOrder P] [LinearOrder Q]
    (graph : RootedDigraph Atom) (leftPrior : graph.Node → P)
    (rightPrior : graph.Node → Q) (marks : graph.Node → List Nat)
    (W D n : Nat)
    (orders : ∀ parent left right, graph.child parent left → graph.child parent right →
      OrderAgrees (leftPrior left) (leftPrior right) (rightPrior left) (rightPrior right)) :
    ∀ node, jointMarkerKey graph leftPrior marks W D n node =
      jointMarkerKey graph rightPrior marks W D n node := by
  refine node_induction graph ?_
  intro node ih
  rw [jointMarkerKey_eq, jointMarkerKey_eq]
  apply assembleJointMarker_congr (fun _ _ => rfl)
  unfold rankedJointKeys
  apply sorted_marker_projection_eq
  · intro child member
    exact ih child (graph.mem_childList.mp member)
  · intro left leftMem right rightMem
    have leftEdge := graph.mem_childList.mp leftMem
    have rightEdge := graph.mem_childList.mp rightMem
    have markerLeft := ih left leftEdge
    have markerRight := ih right rightEdge
    rw [jointKey_eq_marker, jointKey_eq_marker, jointKey_eq_marker, jointKey_eq_marker]
    simp only [Prod.Lex.toLex_le_toLex]
    rw [(orders node right left rightEdge leftEdge).1,
      (orders node right left rightEdge leftEdge).2, markerLeft, markerRight]

/-- A change of graph representation and prior encoding preserves the marker when one
isomorphism preserves all marks and sibling priority comparisons. Literal prior-key
equality, including equality of their observation-window encodings, is unnecessary. -/
theorem jointMarkerKey_iso_of_sibling_order
    {Atom P Q : Type*} [LinearOrder P] [LinearOrder Q]
    {left right : RootedDigraph Atom} (iso : RootedDigraph.Iso left right)
    (leftPrior : left.Node → P) (rightPrior : right.Node → Q)
    (leftMarks : left.Node → List Nat) (rightMarks : right.Node → List Nat)
    (W D n : Nat)
    (orders : ∀ parent a b, left.child parent a → left.child parent b →
      OrderAgrees (leftPrior a) (leftPrior b)
        (rightPrior (iso.toEquiv a)) (rightPrior (iso.toEquiv b)))
    (marks : ∀ node index, index < n →
      (rightMarks (iso.toEquiv node)).getD index 0 = (leftMarks node).getD index 0)
    (node : left.Node) :
    jointMarkerKey left leftPrior leftMarks W D n node =
      jointMarkerKey right rightPrior rightMarks W D n (iso.toEquiv node) := by
  calc
    _ = jointMarkerKey left (fun x => rightPrior (iso.toEquiv x)) leftMarks W D n node :=
      jointMarkerKey_eq_of_sibling_order left leftPrior _ leftMarks W D n orders node
    _ = _ := (jointMarkerKey_iso iso (fun x => rightPrior (iso.toEquiv x)) rightPrior
      leftMarks rightMarks W D n (fun _ => rfl) marks node).symm

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerPriorOrderCongruence

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerPriorOrderCongruence.sorted_marker_projection_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerPriorOrderCongruence.jointMarkerKey_eq_of_sibling_order
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerPriorOrderCongruence.jointMarkerKey_iso_of_sibling_order
