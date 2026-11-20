import TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleInput
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-! Kernel-computable occurrence expansion for the cyclic example. The only replacement is
the exact sorted neighbor table; equality with the actual official expansion is proved first.
No descriptor state or comparison result is part of this construction. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleCarrier

open LocalizedChemicalRingCyclicExampleInput
open CertifiedLocalizedCIPInput

abbrev Atom := Fin 9
abbrev Frame := certified.LocalizedCIPOccurrenceFrame

def neighbors (a : Atom) : List Atom :=
  match a.val with
  | 0 => [1, 2, 4, 5]
  | 1 => [0]
  | 2 => [0, 3, 4, 6]
  | 3 => [2]
  | 4 => [0, 2, 7, 8]
  | 5 => [0]
  | 6 => [2]
  | _ => [4]

theorem neighbors_eq (a : Atom) :
    (certified.moleculeGraph.neighborFinset a).sort (· ≤ ·) = neighbors a := by
  have same : (neighbors a).toFinset = certified.moleculeGraph.neighborFinset a := by
    ext b
    fin_cases a <;> fin_cases b <;> decide +kernel
  rw [← same]
  apply (List.toFinset_sort (r := (· ≤ ·)) (l := neighbors a) ?_).mpr
  · fin_cases a <;> decide +kernel
  · fin_cases a <;> decide +kernel

def neighborCopies (atom : Atom) : List (Atom × Nat) :=
  (neighbors atom).flatMap fun neighbor =>
    (List.range (certified.moleculeGraph.bond atom neighbor)).map fun index => (neighbor, index)

theorem neighborCopies_eq (atom : Atom) :
    certified.executableOfficialNeighborCopies atom = neighborCopies atom := by
  unfold executableOfficialNeighborCopies neighborCopies
  rw [neighbors_eq]

def childCopies (node : OfficialCIPNode Atom) : List (Atom × Nat) :=
  match node.current? with
  | none => []
  | some current =>
      match node.parent? with
      | none => neighborCopies current
      | some parent => (neighborCopies current).filter fun copy =>
          !(copy.1 == parent && copy.2 == 0)

theorem childCopies_eq (node : OfficialCIPNode Atom) :
    certified.executableOfficialChildCopies node = childCopies node := by
  unfold executableOfficialChildCopies childCopies
  cases node.current? with
  | none => rfl
  | some current =>
      cases node.parent? with
      | none => exact neighborCopies_eq current
      | some parent =>
          simp only [neighborCopies_eq]
          rfl

def children (node : OfficialCIPNode Atom) : List (OfficialCIPNode Atom) :=
  if node.isDuplicateLeaf then [] else (childCopies node).map fun copy => node.extend copy.1 copy.2

theorem children_eq (node : OfficialCIPNode Atom) :
    certified.executableOfficialCIPChildren node = children node := by
  unfold executableOfficialCIPChildren children
  rw [childCopies_eq]
  rfl

def subtree (rootAtom : Atom) : Nat → List Nat → OfficialCIPNode Atom → List Frame
  | 0, path, node => [{ root := rootAtom, address := path, node := node, remaining := 0 }]
  | fuel + 1, path, node =>
      { root := rootAtom, address := path, node := node, remaining := fuel + 1 } ::
        (children node).zipIdx.flatMap fun child =>
          subtree rootAtom fuel (path ++ [child.2]) child.1

theorem subtree_eq (rootAtom : Atom) : ∀ fuel path node,
    certified.localizedOccurrenceSubtree rootAtom fuel path node = subtree rootAtom fuel path node
  | 0, _, _ => rfl
  | fuel + 1, path, node => by
      rw [localizedOccurrenceSubtree, subtree, children_eq]
      congr 1
      congr 1
      funext child
      exact subtree_eq rootAtom fuel _ _

def occurrencesAt (fuel : Nat) (atom : Atom) : List Frame :=
  subtree atom (fuel + 1) [] (OfficialCIPNode.root atom)

theorem occurrencesAt_eq (fuel : Nat) (atom : Atom) :
    certified.localizedOccurrencesAtAtom fuel atom = occurrencesAt fuel atom := by
  exact subtree_eq atom (fuel + 1) [] (OfficialCIPNode.root atom)

def carrier (fuel : Nat) : List Frame :=
  ((List.finRange 9).flatMap (occurrencesAt fuel)).dedup

theorem carrier_eq (fuel : Nat) : certified.localizedOccurrences fuel = carrier fuel := by
  unfold localizedOccurrences carrier localizedOccurrencesAtAtom occurrencesAt
  simp only [subtree_eq]
  rfl

end TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleCarrier

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleCarrier.neighbors_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleCarrier.children_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleCarrier.subtree_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleCarrier.carrier_eq
