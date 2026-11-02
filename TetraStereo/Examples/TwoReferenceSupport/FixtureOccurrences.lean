import TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture
import TetraStereo.Examples.TwoReferenceSupport.FixtureInventory
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

namespace FixtureOccurrences

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput

abbrev Input := input.certified
abbrev Atom := input.certified.Atom
abbrev Fuel := LocalizedUniversalReference.carrierFuel input
abbrev Occurrence := LocalizedUniversalReference.Occurrence input

/-- The atom witnesses use the already checked finite source indexing. -/
def atom (index : Fin 33) : Atom := FixtureInventory.fixtureAtom index

def atom0 : Atom := atom 0
def atom1 : Atom := atom 1
def atom2 : Atom := atom 2
def atom3 : Atom := atom 3
def atom4 : Atom := atom 4
def atom5 : Atom := atom 5
def atom6 : Atom := atom 6
def atom7 : Atom := atom 7
def atom8 : Atom := atom 8
def atom9 : Atom := atom 9
def atom10 : Atom := atom 10
def atom11 : Atom := atom 11
def atom12 : Atom := atom 12
def atom13 : Atom := atom 13
def atom14 : Atom := atom 14
def atom15 : Atom := atom 15
def atom16 : Atom := atom 16
def atom17 : Atom := atom 17
def atom18 : Atom := atom 18
def atom19 : Atom := atom 19
def atom20 : Atom := atom 20
def atom21 : Atom := atom 21
def atom22 : Atom := atom 22
def atom23 : Atom := atom 23
def atom24 : Atom := atom 24
def atom25 : Atom := atom 25
def atom26 : Atom := atom 26
def atom27 : Atom := atom 27
def atom28 : Atom := atom 28
def atom29 : Atom := atom 29
def atom30 : Atom := atom 30
def atom31 : Atom := atom 31
def atom32 : Atom := atom 32

/-- Root-relative official nodes along the actual source bonds. -/
def rootNode : OfficialCIPNode Atom := .root atom0
def n3Node : OfficialCIPNode Atom := rootNode.extend atom3 0
def n18Node : OfficialCIPNode Atom := rootNode.extend atom18 0
def a4Node : OfficialCIPNode Atom := n3Node.extend atom4 0
def a11Node : OfficialCIPNode Atom := n3Node.extend atom11 0
def a19Node : OfficialCIPNode Atom := n18Node.extend atom19 0
def a26Node : OfficialCIPNode Atom := n18Node.extend atom26 0
def b7Node : OfficialCIPNode Atom := a4Node.extend atom7 0
def b14Node : OfficialCIPNode Atom := a11Node.extend atom14 0
def b22Node : OfficialCIPNode Atom := a19Node.extend atom22 0
def b29Node : OfficialCIPNode Atom := a26Node.extend atom29 0

/-- Sorting can be rewritten using the sort-free list characterization, since `Finset.sort`
uses quotient lifting that the kernel does not directly unfold. -/
theorem sort_of_toFinset_eq (a : Atom) (l : List Atom)
    (hset : l.toFinset = input.certified.moleculeGraph.neighborFinset a)
    (hnd : l.Nodup) (hpw : l.Pairwise (· ≤ ·)) :
    (input.certified.moleculeGraph.neighborFinset a).sort (· ≤ ·) = l := by
  rw [← hset]
  exact (List.toFinset_sort (r := (· ≤ ·)) (l := l) hnd).mpr hpw

/-- Exact canonical index-sorted neighbors at every atom of the actual source. This establishes
that occurrence sibling numbers come from executable child ordering. -/
theorem neighborSort_eq (a : Atom) :
    (input.certified.moleculeGraph.neighborFinset a).sort (· ≤ ·) =
      match a.val with
      | 0 => [atom1, atom2, atom3, atom18]
      | 1 => [atom0]
      | 2 => [atom0]
      | 3 => [atom0, atom4, atom11]
      | 4 => [atom3, atom5, atom6, atom7]
      | 5 => [atom4]
      | 6 => [atom4]
      | 7 => [atom4, atom8, atom9, atom10]
      | 8 => [atom7]
      | 9 => [atom7]
      | 10 => [atom7]
      | 11 => [atom3, atom12, atom13, atom14]
      | 12 => [atom11]
      | 13 => [atom11]
      | 14 => [atom11, atom15, atom16, atom17]
      | 15 => [atom14]
      | 16 => [atom14]
      | 17 => [atom14]
      | 18 => [atom0, atom19, atom26]
      | 19 => [atom18, atom20, atom21, atom22]
      | 20 => [atom19]
      | 21 => [atom19]
      | 22 => [atom19, atom23, atom24, atom25]
      | 23 => [atom22]
      | 24 => [atom22]
      | 25 => [atom22]
      | 26 => [atom18, atom27, atom28, atom29]
      | 27 => [atom26]
      | 28 => [atom26]
      | 29 => [atom26, atom30, atom31, atom32]
      | 30 => [atom29]
      | 31 => [atom29]
      | _ => [atom29] := by
  fin_cases a
  · exact sort_of_toFinset_eq atom0 [atom1, atom2, atom3, atom18]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom1 [atom0]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom2 [atom0]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom3 [atom0, atom4, atom11]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom4 [atom3, atom5, atom6, atom7]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom5 [atom4]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom6 [atom4]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom7 [atom4, atom8, atom9, atom10]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom8 [atom7]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom9 [atom7]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom10 [atom7]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom11 [atom3, atom12, atom13, atom14]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom12 [atom11]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom13 [atom11]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom14 [atom11, atom15, atom16, atom17]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom15 [atom14]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom16 [atom14]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom17 [atom14]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom18 [atom0, atom19, atom26]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom19 [atom18, atom20, atom21, atom22]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom20 [atom19]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom21 [atom19]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom22 [atom19, atom23, atom24, atom25]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom23 [atom22]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom24 [atom22]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom25 [atom22]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom26 [atom18, atom27, atom28, atom29]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom27 [atom26]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom28 [atom26]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom29 [atom26, atom30, atom31, atom32]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom30 [atom29]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom31 [atom29]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact sort_of_toFinset_eq atom32 [atom29]
      (by ext y; fin_cases y <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- These lists expose the sibling indices assigned by the actual executable child enumeration:
source atoms are traversed in canonical ascending atom-index order, with the incoming parent
removed. -/
theorem rootChildren :
    input.certified.executableOfficialCIPChildren rootNode =
      [rootNode.extend atom1 0, rootNode.extend atom2 0,
       n3Node, n18Node] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    rootNode, n3Node, n18Node, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem n3Children : input.certified.executableOfficialCIPChildren n3Node =
    [a4Node, a11Node] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    n3Node, a4Node, a11Node, rootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem n18Children : input.certified.executableOfficialCIPChildren n18Node =
    [a19Node, a26Node] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    n18Node, a19Node, a26Node, rootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem a4Children : input.certified.executableOfficialCIPChildren a4Node =
    [a4Node.extend atom5 0, a4Node.extend atom6 0, b7Node] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    a4Node, b7Node, n3Node, rootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem a11Children : input.certified.executableOfficialCIPChildren a11Node =
    [a11Node.extend atom12 0, a11Node.extend atom13 0, b14Node] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    a11Node, b14Node, n3Node, rootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem a19Children : input.certified.executableOfficialCIPChildren a19Node =
    [a19Node.extend atom20 0, a19Node.extend atom21 0, b22Node] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    a19Node, b22Node, n18Node, rootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

theorem a26Children : input.certified.executableOfficialCIPChildren a26Node =
    [a26Node.extend atom27 0, a26Node.extend atom28 0, b29Node] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    a26Node, b29Node, n18Node, rootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq]
  decide +kernel

/-- Exact actual occurrence frames under the root-zero official expansion. Their addresses are
computed from the executable child lists above; in particular a `B` center is the third child of
its actual `A` node after excluding that node's incoming nitrogen. -/
def frame4 : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [2, 0], node := a4Node, remaining := Fuel - 1 }
def frame11 : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [2, 1], node := a11Node, remaining := Fuel - 1 }
def frame19 : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [3, 0], node := a19Node, remaining := Fuel - 1 }
def frame26 : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [3, 1], node := a26Node, remaining := Fuel - 1 }
def frame7 : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [2, 0, 2], node := b7Node, remaining := Fuel - 2 }
def frame14 : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [2, 1, 2], node := b14Node, remaining := Fuel - 2 }
def frame22 : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [3, 0, 2], node := b22Node, remaining := Fuel - 2 }
def frame29 : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [3, 1, 2], node := b29Node, remaining := Fuel - 2 }

theorem frame4_mem : frame4 ∈ input.certified.localizedOccurrences Fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom0 [] (Fuel + 1) rootNode frame4
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := Fuel) (node := rootNode) (child := n3Node) (slot := 2)
    (occurrence := frame4) ?_ ?_
  · rw [rootChildren]; simp [n3Node]
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [2]) (fuel := Fuel - 1) (node := n3Node) (child := a4Node) (slot := 0)
      (occurrence := frame4) ?_ ?_
    · rw [n3Children]; simp [a4Node]
    · simpa [frame4] using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (input := input.certified) (root := atom0) (path := [2, 0]) (fuel := Fuel - 1)
          (node := a4Node))

theorem frame11_mem : frame11 ∈ input.certified.localizedOccurrences Fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom0 [] (Fuel + 1) rootNode frame11
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := Fuel) (node := rootNode) (child := n3Node) (slot := 2)
    (occurrence := frame11) ?_ ?_
  · rw [rootChildren]; simp [n3Node]
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [2]) (fuel := Fuel - 1) (node := n3Node) (child := a11Node) (slot := 1)
      (occurrence := frame11) ?_ ?_
    · rw [n3Children]; simp [a11Node]
    · simpa [frame11] using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (input := input.certified) (root := atom0) (path := [2, 1]) (fuel := Fuel - 1)
          (node := a11Node))

theorem frame19_mem : frame19 ∈ input.certified.localizedOccurrences Fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom0 [] (Fuel + 1) rootNode frame19
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := Fuel) (node := rootNode) (child := n18Node) (slot := 3)
    (occurrence := frame19) ?_ ?_
  · rw [rootChildren]; simp [n18Node]
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [3]) (fuel := Fuel - 1) (node := n18Node) (child := a19Node) (slot := 0)
      (occurrence := frame19) ?_ ?_
    · rw [n18Children]; simp [a19Node]
    · simpa [frame19] using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (input := input.certified) (root := atom0) (path := [3, 0]) (fuel := Fuel - 1)
          (node := a19Node))

theorem frame26_mem : frame26 ∈ input.certified.localizedOccurrences Fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom0 [] (Fuel + 1) rootNode frame26
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := Fuel) (node := rootNode) (child := n18Node) (slot := 3)
    (occurrence := frame26) ?_ ?_
  · rw [rootChildren]; simp [n18Node]
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [3]) (fuel := Fuel - 1) (node := n18Node) (child := a26Node) (slot := 1)
      (occurrence := frame26) ?_ ?_
    · rw [n18Children]; simp [a26Node]
    · simpa [frame26] using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (input := input.certified) (root := atom0) (path := [3, 1]) (fuel := Fuel - 1)
          (node := a26Node))

theorem frame7_mem : frame7 ∈ input.certified.localizedOccurrences Fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom0 [] (Fuel + 1) rootNode frame7
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := Fuel) (node := rootNode) (child := n3Node) (slot := 2)
    (occurrence := frame7) ?_ ?_
  · rw [rootChildren]; simp [n3Node]
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [2]) (fuel := Fuel - 1) (node := n3Node) (child := a4Node) (slot := 0)
      (occurrence := frame7) ?_ ?_
    · rw [n3Children]; simp [a4Node]
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (path := [2, 0]) (fuel := Fuel - 2) (node := a4Node) (child := b7Node) (slot := 2)
        (occurrence := frame7) ?_ ?_
      · rw [a4Children]; simp [b7Node]
      · simpa [frame7] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (input := input.certified) (root := atom0) (path := [2, 0, 2]) (fuel := Fuel - 2)
            (node := b7Node))

theorem frame14_mem : frame14 ∈ input.certified.localizedOccurrences Fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom0 [] (Fuel + 1) rootNode frame14
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := Fuel) (node := rootNode) (child := n3Node) (slot := 2)
    (occurrence := frame14) ?_ ?_
  · rw [rootChildren]; simp [n3Node]
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [2]) (fuel := Fuel - 1) (node := n3Node) (child := a11Node) (slot := 1)
      (occurrence := frame14) ?_ ?_
    · rw [n3Children]; simp [a11Node]
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (path := [2, 1]) (fuel := Fuel - 2) (node := a11Node) (child := b14Node) (slot := 2)
        (occurrence := frame14) ?_ ?_
      · rw [a11Children]; simp [b14Node]
      · simpa [frame14] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (input := input.certified) (root := atom0) (path := [2, 1, 2]) (fuel := Fuel - 2)
            (node := b14Node))

theorem frame22_mem : frame22 ∈ input.certified.localizedOccurrences Fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom0 [] (Fuel + 1) rootNode frame22
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := Fuel) (node := rootNode) (child := n18Node) (slot := 3)
    (occurrence := frame22) ?_ ?_
  · rw [rootChildren]; simp [n18Node]
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [3]) (fuel := Fuel - 1) (node := n18Node) (child := a19Node) (slot := 0)
      (occurrence := frame22) ?_ ?_
    · rw [n18Children]; simp [a19Node]
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (path := [3, 0]) (fuel := Fuel - 2) (node := a19Node) (child := b22Node) (slot := 2)
        (occurrence := frame22) ?_ ?_
      · rw [a19Children]; simp [b22Node]
      · simpa [frame22] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (input := input.certified) (root := atom0) (path := [3, 0, 2]) (fuel := Fuel - 2)
            (node := b22Node))

theorem frame29_mem : frame29 ∈ input.certified.localizedOccurrences Fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom0 [] (Fuel + 1) rootNode frame29
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := Fuel) (node := rootNode) (child := n18Node) (slot := 3)
    (occurrence := frame29) ?_ ?_
  · rw [rootChildren]; simp [n18Node]
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [3]) (fuel := Fuel - 1) (node := n18Node) (child := a26Node) (slot := 1)
      (occurrence := frame29) ?_ ?_
    · rw [n18Children]; simp [a26Node]
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (path := [3, 1]) (fuel := Fuel - 2) (node := a26Node) (child := b29Node) (slot := 2)
        (occurrence := frame29) ?_ ?_
      · rw [a26Children]; simp [b29Node]
      · simpa [frame29] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (input := input.certified) (root := atom0) (path := [3, 1, 2]) (fuel := Fuel - 2)
            (node := b29Node))

/-- The carrier elements consumed as actual-reader targets. -/
def occurrence4 : Occurrence := ⟨frame4, frame4_mem⟩
def occurrence11 : Occurrence := ⟨frame11, frame11_mem⟩
def occurrence19 : Occurrence := ⟨frame19, frame19_mem⟩
def occurrence26 : Occurrence := ⟨frame26, frame26_mem⟩
def occurrence7 : Occurrence := ⟨frame7, frame7_mem⟩
def occurrence14 : Occurrence := ⟨frame14, frame14_mem⟩
def occurrence22 : Occurrence := ⟨frame22, frame22_mem⟩
def occurrence29 : Occurrence := ⟨frame29, frame29_mem⟩

theorem occurrence4_current : occurrence4.1.node.current? = some atom4 := rfl
theorem occurrence11_current : occurrence11.1.node.current? = some atom11 := rfl
theorem occurrence19_current : occurrence19.1.node.current? = some atom19 := rfl
theorem occurrence26_current : occurrence26.1.node.current? = some atom26 := rfl
theorem occurrence7_current : occurrence7.1.node.current? = some atom7 := rfl
theorem occurrence14_current : occurrence14.1.node.current? = some atom14 := rfl
theorem occurrence22_current : occurrence22.1.node.current? = some atom22 := rfl
theorem occurrence29_current : occurrence29.1.node.current? = some atom29 := rfl

theorem occurrence4_root : occurrence4.1.root = atom0 := rfl
theorem occurrence11_root : occurrence11.1.root = atom0 := rfl
theorem occurrence19_root : occurrence19.1.root = atom0 := rfl
theorem occurrence26_root : occurrence26.1.root = atom0 := rfl
theorem occurrence7_root : occurrence7.1.root = atom0 := rfl
theorem occurrence14_root : occurrence14.1.root = atom0 := rfl
theorem occurrence22_root : occurrence22.1.root = atom0 := rfl
theorem occurrence29_root : occurrence29.1.root = atom0 := rfl

/-- The detected center wrappers used by the physical-domain consumer. -/
abbrev Center := input.certified.detectedMultiCenterMolecule.Center

def rootCenter : Center := ⟨atom0, by
  change atom0 ∈ FixtureInventory.Input.tetrahedralCenterSet
  rw [FixtureInventory.detectedCenterSet]
  simp [atom0, atom, FixtureInventory.fixtureAtom]
⟩

def center4 : Center := FixtureInventory.center4
def center7 : Center := FixtureInventory.center7
def center11 : Center := FixtureInventory.center11
def center14 : Center := FixtureInventory.center14
def center19 : Center := FixtureInventory.center19
def center22 : Center := FixtureInventory.center22
def center26 : Center := FixtureInventory.center26
def center29 : Center := FixtureInventory.center29

theorem occurrence4_current_center : occurrence4.1.node.current? = some center4.1 := rfl
theorem occurrence11_current_center : occurrence11.1.node.current? = some center11.1 := rfl
theorem occurrence19_current_center : occurrence19.1.node.current? = some center19.1 := rfl
theorem occurrence26_current_center : occurrence26.1.node.current? = some center26.1 := rfl
theorem occurrence7_current_center : occurrence7.1.node.current? = some center7.1 := rfl
theorem occurrence14_current_center : occurrence14.1.node.current? = some center14.1 := rfl
theorem occurrence22_current_center : occurrence22.1.node.current? = some center22.1 := rfl
theorem occurrence29_current_center : occurrence29.1.node.current? = some center29.1 := rfl

theorem occurrence4_root_eq : rootCenter.1 = occurrence4.1.root := rfl
theorem occurrence11_root_eq : rootCenter.1 = occurrence11.1.root := rfl
theorem occurrence19_root_eq : rootCenter.1 = occurrence19.1.root := rfl
theorem occurrence26_root_eq : rootCenter.1 = occurrence26.1.root := rfl
theorem occurrence7_root_eq : rootCenter.1 = occurrence7.1.root := rfl
theorem occurrence14_root_eq : rootCenter.1 = occurrence14.1.root := rfl
theorem occurrence22_root_eq : rootCenter.1 = occurrence22.1.root := rfl
theorem occurrence29_root_eq : rootCenter.1 = occurrence29.1.root := rfl

end FixtureOccurrences

assert_kernel_only FixtureOccurrences.sort_of_toFinset_eq
assert_kernel_only FixtureOccurrences.neighborSort_eq
assert_kernel_only FixtureOccurrences.rootChildren
assert_kernel_only FixtureOccurrences.n3Children
assert_kernel_only FixtureOccurrences.n18Children
assert_kernel_only FixtureOccurrences.a4Children
assert_kernel_only FixtureOccurrences.a11Children
assert_kernel_only FixtureOccurrences.a19Children
assert_kernel_only FixtureOccurrences.a26Children
assert_kernel_only FixtureOccurrences.frame4_mem
assert_kernel_only FixtureOccurrences.frame11_mem
assert_kernel_only FixtureOccurrences.frame19_mem
assert_kernel_only FixtureOccurrences.frame26_mem
assert_kernel_only FixtureOccurrences.frame7_mem
assert_kernel_only FixtureOccurrences.frame14_mem
assert_kernel_only FixtureOccurrences.frame22_mem
assert_kernel_only FixtureOccurrences.frame29_mem
assert_kernel_only FixtureOccurrences.occurrence4_current
assert_kernel_only FixtureOccurrences.occurrence11_current
assert_kernel_only FixtureOccurrences.occurrence19_current
assert_kernel_only FixtureOccurrences.occurrence26_current
assert_kernel_only FixtureOccurrences.occurrence7_current
assert_kernel_only FixtureOccurrences.occurrence14_current
assert_kernel_only FixtureOccurrences.occurrence22_current
assert_kernel_only FixtureOccurrences.occurrence29_current
assert_kernel_only FixtureOccurrences.occurrence4_root
assert_kernel_only FixtureOccurrences.occurrence11_root
assert_kernel_only FixtureOccurrences.occurrence19_root
assert_kernel_only FixtureOccurrences.occurrence26_root
assert_kernel_only FixtureOccurrences.occurrence7_root
assert_kernel_only FixtureOccurrences.occurrence14_root
assert_kernel_only FixtureOccurrences.occurrence22_root
assert_kernel_only FixtureOccurrences.occurrence29_root
assert_kernel_only FixtureOccurrences.rootCenter
assert_kernel_only FixtureOccurrences.center4
assert_kernel_only FixtureOccurrences.center7
assert_kernel_only FixtureOccurrences.center11
assert_kernel_only FixtureOccurrences.center14
assert_kernel_only FixtureOccurrences.center19
assert_kernel_only FixtureOccurrences.center22
assert_kernel_only FixtureOccurrences.center26
assert_kernel_only FixtureOccurrences.center29
assert_kernel_only FixtureOccurrences.occurrence4_current_center
assert_kernel_only FixtureOccurrences.occurrence11_current_center
assert_kernel_only FixtureOccurrences.occurrence19_current_center
assert_kernel_only FixtureOccurrences.occurrence26_current_center
assert_kernel_only FixtureOccurrences.occurrence7_current_center
assert_kernel_only FixtureOccurrences.occurrence14_current_center
assert_kernel_only FixtureOccurrences.occurrence22_current_center
assert_kernel_only FixtureOccurrences.occurrence29_current_center
assert_kernel_only FixtureOccurrences.occurrence4_root_eq
assert_kernel_only FixtureOccurrences.occurrence11_root_eq
assert_kernel_only FixtureOccurrences.occurrence19_root_eq
assert_kernel_only FixtureOccurrences.occurrence26_root_eq
assert_kernel_only FixtureOccurrences.occurrence7_root_eq
assert_kernel_only FixtureOccurrences.occurrence14_root_eq
assert_kernel_only FixtureOccurrences.occurrence22_root_eq
assert_kernel_only FixtureOccurrences.occurrence29_root_eq
