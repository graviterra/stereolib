import TetraStereo.OneCenter.CanonicalComparisonFrame
import TetraStereo.UniversalProof.NextFrontier.NativeOriginFrame
import TetraStereo.UniversalProof.NextFrontier.NativeGeneratedDuplicateCoordinates

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRuntimeFrameCoreRefinement

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeOriginFrame

/-- Only the accepted frame's original center history enters the computational layer. -/
def coreFrame {mol : RawMolecule} {root : Nat} (frame : OriginalTreeFrame mol root) :
    CanonicalComparisonFrame.Frame := ⟨frame.center.history⟩

theorem commonPrefix_agrees (xs ys : List Nat) :
    CanonicalComparisonFrame.commonPrefixLength xs ys =
      NativeOriginFrame.commonPrefixLength xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [CanonicalComparisonFrame.commonPrefixLength,
        NativeOriginFrame.commonPrefixLength, ih]

theorem pathDistance_agrees (origin target : List Nat) :
    CanonicalComparisonFrame.pathDistance origin target =
      NativeOriginFrame.pathDistance origin target := by
  simp only [CanonicalComparisonFrame.pathDistance, NativeOriginFrame.pathDistance,
    commonPrefix_agrees]

theorem frameDistance_agrees (origin target : List Nat) :
    CanonicalComparisonFrame.frameDistance origin target =
      NativeOriginFrame.frameDistance origin target :=
  pathDistance_agrees origin.reverse target.reverse

theorem realDistance_agrees {mol : RawMolecule} {root : Nat}
    (frame : OriginalTreeFrame mol root) (node : CanonicalBranchNode) :
    (coreFrame frame).realDistance node = frame.distance node :=
  frameDistance_agrees frame.center.history node.history

/-- Generation and the reference observation are both retained in the conclusion. -/
theorem generated_real_reference {mol : RawMolecule} {root : Nat}
    (frame : OriginalTreeFrame mol root) (node : CanonicalBranchNode)
    (generated : CanonicalCenterTreeNode mol root node) (real : node.provenance = .realAtom) :
    CanonicalCenterTreeNode mol root node ∧
      CanonicalComparisonFrame.observeNode (coreFrame frame) node = some (frame.distance node) := by
  refine ⟨generated, ?_⟩
  rw [CanonicalComparisonFrame.real_observation (coreFrame frame) node real,
    realDistance_agrees frame node]

/-- Every actual canonical child retains its original parent history in the tail. -/
theorem generated_child_tail {mol : RawMolecule} (parent child : CanonicalBranchNode)
    (member : child ∈ mol.canonicalChildren parent) : child.history.tail = parent.history := by
  rw [mol.canonicalChildren_history parent child member]
  rfl

theorem generated_duplicate_bound {mol : RawMolecule} {root : Nat}
    (duplicate : GeneratedDuplicateCoordinate mol root) :
    duplicate.storedDistance + 1 ≤ duplicate.child.history.tail.length := by
  rw [generated_child_tail duplicate.parent duplicate.child duplicate.childGenerated]
  exact duplicate.coordinateBound

theorem generated_duplicate_coordinate {mol : RawMolecule} {root : Nat}
    (duplicate : GeneratedDuplicateCoordinate mol root) :
    CanonicalComparisonFrame.duplicateRootwardCoordinate duplicate.child duplicate.storedDistance =
      duplicate.rootwardCoordinate := by
  unfold CanonicalComparisonFrame.duplicateRootwardCoordinate
  rw [generated_child_tail duplicate.parent duplicate.child duplicate.childGenerated]
  rfl

theorem generated_duplicate_distance {mol : RawMolecule} {root : Nat}
    (frame : OriginalTreeFrame mol root) (duplicate : GeneratedDuplicateCoordinate mol root) :
    (coreFrame frame).duplicateDistance duplicate.child duplicate.storedDistance =
      duplicateReferenceDistance frame duplicate := by
  unfold CanonicalComparisonFrame.Frame.duplicateDistance
  rw [generated_duplicate_coordinate duplicate]
  exact pathDistance_agrees frame.center.history.reverse duplicate.rootwardCoordinate

theorem generated_duplicate_reference {mol : RawMolecule} {root : Nat}
    (frame : OriginalTreeFrame mol root) (duplicate : GeneratedDuplicateCoordinate mol root) :
    CanonicalComparisonFrame.observeNode (coreFrame frame) duplicate.child =
      some (duplicateReferenceDistance frame duplicate) := by
  have bound := generated_duplicate_bound duplicate
  rcases duplicate.duplicateKind with multiple | ring
  · rw [CanonicalComparisonFrame.multiple_observation (coreFrame frame) duplicate.child
      duplicate.storedDistance multiple bound, generated_duplicate_distance frame duplicate]
  · rw [CanonicalComparisonFrame.ring_observation (coreFrame frame) duplicate.child
      duplicate.storedDistance ring bound, generated_duplicate_distance frame duplicate]

/-- Multiple-coordinate bounds and parent identification come from actual generation,
not a supplied successful observation or desired comparison result. -/
theorem actual_multiple_reference {mol : RawMolecule} {root : Nat}
    (frame : OriginalTreeFrame mol root) {parent child : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root parent)
    (member : child ∈ mol.canonicalChildren parent) (stored : Nat)
    (kind : child.provenance = .multipleBondDuplicate stored) :
    CanonicalComparisonFrame.observeNode (coreFrame frame) child = some (frame.distance parent) := by
  have observed := generated_duplicate_reference frame
    (NativeGeneratedDuplicateCoordinates.multipleCoordinate generated member stored kind)
  rw [NativeGeneratedDuplicateCoordinates.multiple_fixed_frame_distance
    frame generated member stored kind] at observed
  exact observed

/-- Ring-coordinate bounds and the ancestor prefix come from actual generation. -/
theorem actual_ring_reference {mol : RawMolecule} {root : Nat}
    (frame : OriginalTreeFrame mol root) {parent child : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol root parent)
    (member : child ∈ mol.canonicalChildren parent) (stored : Nat)
    (kind : child.provenance = .ringDuplicate stored) :
    CanonicalComparisonFrame.observeNode (coreFrame frame) child =
      some (NativeOriginFrame.pathDistance frame.center.history.reverse
        (parent.history.reverse.take (stored + 1))) := by
  have observed := generated_duplicate_reference frame
    (NativeGeneratedDuplicateCoordinates.ringCoordinate generated member stored kind)
  rw [NativeGeneratedDuplicateCoordinates.ring_fixed_frame_distance
    frame generated member stored kind] at observed
  exact observed

/-- The production scalar is retained, while the sidecar computes the frame reference. -/
theorem generated_real_padding_reference {mol : RawMolecule} {root : Nat}
    (frame : OriginalTreeFrame mol root) (parent : CanonicalBranchNode)
    (generated : CanonicalCenterTreeNode mol root parent) (real : parent.provenance = .realAtom) :
    CanonicalCenterTreeNode mol root parent ∧
      (CanonicalComparisonFrame.paddingSidecar (coreFrame frame) parent
        (parent.rule1bRootDistance + 1)).original mol =
          mol.canonicalPhantom parent.atom (parent.rule1bRootDistance + 1) ∧
      (CanonicalComparisonFrame.paddingSidecar (coreFrame frame) parent
        (parent.rule1bRootDistance + 1)).distance? =
          some (paddingReferenceDistance frame parent) := by
  refine ⟨generated, rfl, ?_⟩
  rw [CanonicalComparisonFrame.padding_real_distance (coreFrame frame) parent
    (parent.rule1bRootDistance + 1) real, realDistance_agrees frame parent]
  rfl

theorem multiple_fixture_observed :
    CanonicalComparisonFrame.observeNode
      (coreFrame (⟨canonicalCenterRoot 0, .root⟩ :
        OriginalTreeFrame NativeGeneratedDuplicateCoordinates.multipleFixture 0))
      NativeGeneratedDuplicateCoordinates.multipleFixtureChild = some 0 := by
  exact actual_multiple_reference
    (⟨canonicalCenterRoot 0, .root⟩ :
      OriginalTreeFrame NativeGeneratedDuplicateCoordinates.multipleFixture 0)
    (.root : CanonicalCenterTreeNode NativeGeneratedDuplicateCoordinates.multipleFixture 0
      (canonicalCenterRoot 0))
    NativeGeneratedDuplicateCoordinates.multiple_fixture_generated 0 rfl

/-- Actual methyl cursors retain their original identity and have equal reference distances.
No production comparator equality or full physical transport claim is made. -/
theorem actual_methyl_reference_tie :
    CanonicalCenterRerootCursor InteriorMethylDepthCounterexample.molecule 1
      InteriorMethylDepthCounterexample.incoming ∧
    CanonicalCenterRerootCursor InteriorMethylDepthCounterexample.molecule 1
      InteriorMethylDepthCounterexample.outgoing ∧
    CanonicalComparisonFrame.observeNode (coreFrame fixtureFrame)
      InteriorMethylDepthCounterexample.incoming.node = some 1 ∧
    CanonicalComparisonFrame.observeNode (coreFrame fixtureFrame)
      InteriorMethylDepthCounterexample.outgoing.node = some 1 := by
  exact ⟨real_fixture_generated.1, real_fixture_generated.2, rfl, rfl⟩

theorem actual_methyl_hydrogen_reference_tie :
    CanonicalCenterTreeNode InteriorMethylDepthCounterexample.molecule 1 incomingHydrogen ∧
    CanonicalCenterTreeNode InteriorMethylDepthCounterexample.molecule 1 outgoingHydrogen ∧
    CanonicalComparisonFrame.observeNode (coreFrame fixtureFrame) incomingHydrogen = some 2 ∧
    CanonicalComparisonFrame.observeNode (coreFrame fixtureFrame) outgoingHydrogen = some 2 := by
  exact ⟨fixture_hydrogens_generated.1, fixture_hydrogens_generated.2, rfl, rfl⟩

theorem actual_methyl_nodes_preserved :
    (CanonicalComparisonFrame.frameNode (coreFrame fixtureFrame)
      InteriorMethylDepthCounterexample.incoming.node).original =
        InteriorMethylDepthCounterexample.incoming.node ∧
    (CanonicalComparisonFrame.frameNode (coreFrame fixtureFrame)
      InteriorMethylDepthCounterexample.outgoing.node).original =
        InteriorMethylDepthCounterexample.outgoing.node := ⟨rfl, rfl⟩

/-- Equal effective padding references coexist with deliberately unequal original scalars. -/
theorem actual_methyl_padding_reference_tie :
    (CanonicalComparisonFrame.paddingSidecar (coreFrame fixtureFrame)
      InteriorMethylDepthCounterexample.incoming.node
      (InteriorMethylDepthCounterexample.incoming.node.rule1bRootDistance + 1)).distance? = some 2 ∧
    (CanonicalComparisonFrame.paddingSidecar (coreFrame fixtureFrame)
      InteriorMethylDepthCounterexample.outgoing.node
      (InteriorMethylDepthCounterexample.outgoing.node.rule1bRootDistance + 1)).distance? = some 2 ∧
    ((CanonicalComparisonFrame.paddingSidecar (coreFrame fixtureFrame)
      InteriorMethylDepthCounterexample.incoming.node
      (InteriorMethylDepthCounterexample.incoming.node.rule1bRootDistance + 1)).original
        InteriorMethylDepthCounterexample.molecule).provenance = .phantom 1 ∧
    ((CanonicalComparisonFrame.paddingSidecar (coreFrame fixtureFrame)
      InteriorMethylDepthCounterexample.outgoing.node
      (InteriorMethylDepthCounterexample.outgoing.node.rule1bRootDistance + 1)).original
        InteriorMethylDepthCounterexample.molecule).provenance = .phantom 3 := ⟨rfl, rfl, rfl, rfl⟩

end TetraStereo.UniversalProof.NativeRuntimeFrameCoreRefinement
