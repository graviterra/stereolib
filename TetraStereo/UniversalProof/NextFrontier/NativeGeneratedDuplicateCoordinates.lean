import TetraStereo.UniversalProof.NextFrontier.NativeOriginFrame
import TetraStereo.OneCenter.ProductionCIPFaithfulDistance

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeGeneratedDuplicateCoordinates

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeOriginFrame

theorem generated_history_nonempty {mol : RawMolecule} {root : Nat}
    {parent : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root parent) :
    0 < parent.history.length := by
  have head := generated.history_head
  cases historyEq : parent.history with
  | nil => simp [historyEq] at head
  | cons x xs => simp

theorem multiple_distance_parent (mol : RawMolecule) (parent child : CanonicalBranchNode)
    (member : child ∈ mol.canonicalChildren parent) (distance : Nat)
    (provenance : child.provenance = .multipleBondDuplicate distance) :
    distance = parent.depth := by
  unfold canonicalChildren at member
  by_cases leaf : parent.forcedLeaf
  · simp [leaf] at member
  · simp only [leaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at member
    obtain ⟨copy, _copyMember, rfl⟩ := member
    by_cases multiple : copy.2 != 0
    · simp [multiple] at provenance
      exact provenance.symm
    · by_cases ring : copy.1 ∈ parent.history
      · simp [multiple, ring] at provenance
      · simp [multiple, ring] at provenance

theorem multiple_coordinate_bound {mol : RawMolecule} {root : Nat}
    {parent child : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root parent)
    (member : child ∈ mol.canonicalChildren parent) (distance : Nat)
    (provenance : child.provenance = .multipleBondDuplicate distance) :
    distance + 1 = parent.history.length := by
  have depthEq := multiple_distance_parent mol parent child member distance provenance
  have positive := generated_history_nonempty generated
  simp only [CanonicalBranchNode.depth] at depthEq
  omega

theorem ring_coordinate_index {mol : RawMolecule} {root : Nat}
    {parent child : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root parent)
    (member : child ∈ mol.canonicalChildren parent) (distance : Nat)
    (provenance : child.provenance = .ringDuplicate distance) :
    firstNatIndex? child.atom parent.history.reverse = some distance ∧
      distance < parent.history.length ∧
      parent.history.reverse[distance]? = some child.atom := by
  obtain ⟨inHistory, distanceEq, _notParent⟩ :=
    mol.canonicalChildren_ringDuplicate_data parent child generated.history_head member
      distance provenance
  obtain ⟨index, indexEq, canonicalEq⟩ :=
    canonicalHistoryDistance_eq_index_of_mem parent child.atom inHistory
  have same : distance = index := distanceEq.trans canonicalEq
  have actualIndex : firstNatIndex? child.atom parent.history.reverse = some distance := by
    rw [same]
    exact indexEq
  have bound := firstNatIndex?_eq_some_imp_lt_length child.atom parent.history.reverse
    distance actualIndex
  have selected := firstNatIndex?_eq_some_imp_getElem? child.atom parent.history.reverse
    distance actualIndex
  exact ⟨actualIndex, by simpa using bound, selected⟩

def multipleCoordinate {mol : RawMolecule} {root : Nat}
    {parent child : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root parent)
    (member : child ∈ mol.canonicalChildren parent) (distance : Nat)
    (provenance : child.provenance = .multipleBondDuplicate distance) :
    GeneratedDuplicateCoordinate mol root :=
  { parent := parent, child := child, parentGenerated := generated, childGenerated := member,
    storedDistance := distance, duplicateKind := Or.inl provenance,
    coordinateBound := Nat.le_of_eq (multiple_coordinate_bound generated member distance provenance) }

def ringCoordinate {mol : RawMolecule} {root : Nat}
    {parent child : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root parent)
    (member : child ∈ mol.canonicalChildren parent) (distance : Nat)
    (provenance : child.provenance = .ringDuplicate distance) :
    GeneratedDuplicateCoordinate mol root :=
  { parent := parent, child := child, parentGenerated := generated, childGenerated := member,
    storedDistance := distance, duplicateKind := Or.inr provenance,
    coordinateBound := by
      have bound := (ring_coordinate_index generated member distance provenance).2.1
      omega }

theorem multiple_rootward_parent {mol : RawMolecule} {root : Nat}
    {parent child : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root parent)
    (member : child ∈ mol.canonicalChildren parent) (distance : Nat)
    (provenance : child.provenance = .multipleBondDuplicate distance) :
    (multipleCoordinate generated member distance provenance).rootwardCoordinate =
      parent.history.reverse := by
  change parent.history.reverse.take (distance + 1) = parent.history.reverse
  rw [multiple_coordinate_bound generated member distance provenance]
  simp

theorem ring_rootward_ends_at_duplicate {mol : RawMolecule} {root : Nat}
    {parent child : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root parent)
    (member : child ∈ mol.canonicalChildren parent) (distance : Nat)
    (provenance : child.provenance = .ringDuplicate distance) :
    (ringCoordinate generated member distance provenance).rootwardCoordinate.getLast? =
      some child.atom := by
  have selected := (ring_coordinate_index generated member distance provenance).2.2
  change (parent.history.reverse.take (distance + 1)).getLast? = some child.atom
  rw [List.getLast?_take]
  simp [selected]

theorem multiple_fixed_frame_distance {mol : RawMolecule} {root : Nat}
    (frame : OriginalTreeFrame mol root) {parent child : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root parent)
    (member : child ∈ mol.canonicalChildren parent) (distance : Nat)
    (provenance : child.provenance = .multipleBondDuplicate distance) :
    duplicateReferenceDistance frame (multipleCoordinate generated member distance provenance) =
      frame.distance parent := by
  unfold duplicateReferenceDistance
  rw [multiple_rootward_parent generated member distance provenance]
  rfl

theorem ring_fixed_frame_distance {mol : RawMolecule} {root : Nat}
    (frame : OriginalTreeFrame mol root) {parent child : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root parent)
    (member : child ∈ mol.canonicalChildren parent) (distance : Nat)
    (provenance : child.provenance = .ringDuplicate distance) :
    duplicateReferenceDistance frame (ringCoordinate generated member distance provenance) =
      pathDistance frame.center.history.reverse
        (parent.history.reverse.take (distance + 1)) := rfl

/-- Minimal generation fixture, not a saturated-chemistry admission claim. -/
def multipleFixture : RawMolecule :=
  { atoms := [AtomSpec.aliphatic .C, AtomSpec.aliphatic .C]
    bonds := [⟨0, 1, .double⟩] }

def multipleFixtureChild : CanonicalBranchNode :=
  { atom := 1, parent := 0, history := [1, 0], provenance := .multipleBondDuplicate 0 }

theorem multiple_fixture_generated :
    multipleFixtureChild ∈ multipleFixture.canonicalChildren (canonicalCenterRoot 0) := by
  decide +kernel

def multipleFixtureCoordinate : GeneratedDuplicateCoordinate multipleFixture 0 :=
  multipleCoordinate (.root : CanonicalCenterTreeNode multipleFixture 0 (canonicalCenterRoot 0))
    multiple_fixture_generated 0 rfl

theorem generated_duplicate_inhabited :
    Nonempty (GeneratedDuplicateCoordinate multipleFixture 0) :=
  ⟨multipleFixtureCoordinate⟩

end TetraStereo.UniversalProof.NativeGeneratedDuplicateCoordinates
