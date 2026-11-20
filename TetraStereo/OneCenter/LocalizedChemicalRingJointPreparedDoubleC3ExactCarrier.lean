import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyOrdinary
import TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input
import TetraStereo.OneCenter.LocalizedMarkedCarrierLookup
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

/-! An explicit actual carrier occurrence for the left DoubleC3 auxiliary. The finite checks
inspect only local carrier edges and the first five entries of the rooted lookup. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingDoubleC3Input
open LocalizedMarkedCarrierLookup (lookup?)

abbrev input := certified true


/-- Ordered finite enumeration, avoiding quotient-based Finset.sort reduction. -/
def neighbors (a : Fin 25) : List (Fin 25) :=
  (List.finRange 25).filter fun b => decide (input.moleculeGraph.Adj a b)

theorem neighbors_eq_sorted (a : Fin 25) :
    neighbors a = (input.moleculeGraph.neighborFinset a).sort (· ≤ ·) := by
  have setEq : input.moleculeGraph.neighborFinset a = (neighbors a).toFinset := by
    ext b
    simp [neighbors, MoleculeGraph.mem_neighborFinset]
  rw [setEq]
  apply Eq.symm
  apply (List.toFinset_sort (· ≤ ·) ((List.nodup_finRange 25).filter _)).mpr
  exact ((List.sortedLT_finRange 25).pairwise.imp (fun h => le_of_lt h)).filter _

def children (node : OfficialCIPNode input.Atom) : List (OfficialCIPNode input.Atom) :=
  if node.isDuplicateLeaf then []
  else
    let copies := match node.current? with
      | none => []
      | some current =>
          let all := (neighbors current).flatMap fun neighbor =>
            (List.range (input.moleculeGraph.bond current neighbor)).map fun index => (neighbor, index)
          match node.parent? with
          | none => all
          | some parent => all.filter fun copy => !(copy.1 == parent && copy.2 == 0)
    copies.map fun copy => node.extend copy.1 copy.2

theorem children_eq (node : OfficialCIPNode input.Atom) :
    children node = input.executableOfficialCIPChildren node := by
  cases leaf : node.isDuplicateLeaf <;>
    cases current : node.current? <;> cases parent : node.parent? <;>
    simp only [children, executableOfficialCIPChildren, executableOfficialChildCopies,
      executableOfficialNeighborCopies, leaf, current, parent, Bool.false_eq_true,
      if_false, if_true, ← neighbors_eq_sorted]

def subtree (root : Fin 25) : Nat → List Nat → OfficialCIPNode input.Atom →
    List input.LocalizedCIPOccurrenceFrame
  | 0, path, node => [{ root := root, address := path, node := node, remaining := 0 }]
  | fuel + 1, path, node =>
      { root := root, address := path, node := node, remaining := fuel + 1 } ::
        (children node).zipIdx.flatMap fun child => subtree root fuel (path ++ [child.2]) child.1

theorem subtree_eq (root : Fin 25) (fuel : Nat) :
    ∀ path node, subtree root fuel path node = input.localizedOccurrenceSubtree root fuel path node := by
  induction fuel with
  | zero => intro path node; rfl
  | succ fuel ih =>
      intro path node
      simp only [subtree, localizedOccurrenceSubtree, children_eq, ih]


private theorem map_attach_congr {α β : Type} (xs ys : List α) (same : xs = ys)
    (f : {x // x ∈ xs} → β) (g : {x // x ∈ ys} → β)
    (pointwise : ∀ x hx hy, f ⟨x, hx⟩ = g ⟨x, hy⟩) : xs.attach.map f = ys.attach.map g := by
  subst ys
  apply List.map_congr_left
  intro entry _
  exact pointwise entry.1 entry.2 entry.2

def computableRooted (root : Fin 25) : List (input.LocalizedCIPOccurrence 26) :=
  (subtree root 27 [] (OfficialCIPNode.root root)).attach.map fun entry =>
    ⟨entry.1, by
      unfold localizedOccurrences
      rw [List.mem_dedup, List.mem_flatMap]
      refine ⟨root, by simp, ?_⟩
      change entry.1 ∈ input.localizedOccurrenceSubtree root 27 [] (OfficialCIPNode.root root)
      rw [← subtree_eq]
      exact entry.2⟩

theorem computableRooted_eq (root : Fin 25) :
    computableRooted root = LocalizedMarkedCarrierLookup.rootedCarrier input
      (input.certified.input.molecule.atomCount + 1) root := by
  change computableRooted root = LocalizedMarkedCarrierLookup.rootedCarrier input 26 root
  unfold computableRooted LocalizedMarkedCarrierLookup.rootedCarrier localizedOccurrencesAtAtom
  apply map_attach_congr _ _ (subtree_eq root 27 [] (OfficialCIPNode.root root))
  intros
  rfl

def armNode : OfficialCIPNode input.Atom := OfficialCIPNode.rootFromEdge (0 : Fin 25) (4 : Fin 25)
def centerNode : OfficialCIPNode input.Atom :=
  { current? := some (3 : Fin 25), history := [(3 : Fin 25), (4 : Fin 25), (0 : Fin 25)], provenance := .realAtom }

def centerFrame : input.LocalizedCIPOccurrenceFrame :=
  { root := (0 : Fin 25), address := [2, 0], node := centerNode, remaining := 25 }

private theorem root_arm_edge :
    (armNode, 2) ∈ (input.executableOfficialCIPChildren (OfficialCIPNode.root (0 : Fin 25))).zipIdx := by
  rw [← children_eq]
  decide +kernel

private theorem arm_center_edge :
    (centerNode, 0) ∈ (input.executableOfficialCIPChildren armNode).zipIdx := by
  rw [← children_eq]
  decide +kernel

theorem centerFrame_mem : centerFrame ∈ input.localizedOccurrences 26 := by
  apply (input.mem_localizedOccurrences_iff 26 centerFrame).mpr
  change input.DeclarativeLocalizedOccurrenceSubtree (0 : Fin 25) [] 27
    (OfficialCIPNode.root (0 : Fin 25)) centerFrame
  exact .subtreeDescendant root_arm_edge
    (.subtreeDescendant arm_center_edge (.subtreeRoot [2, 0] 25 centerNode))

def target : input.LocalizedCIPOccurrence 26 := ⟨centerFrame, centerFrame_mem⟩

/-- The actual callback lookup returns this explicit carrier occurrence. -/
theorem actual_lookup : lookup? input leftCenter = some target := by
  change LocalizedMarkedCarrierLookup.lookupAtRoot? input (0 : Fin 25) leftCenter = some target
  unfold LocalizedMarkedCarrierLookup.lookupAtRoot?
  rw [← computableRooted_eq]
  decide +kernel

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier.centerFrame_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier.target
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier.actual_lookup

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier.neighbors_eq_sorted
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier.children_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier.subtree_eq

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier.computableRooted_eq
