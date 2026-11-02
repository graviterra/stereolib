import TetraStereo.UniversalProof.NextFrontier.InteriorMethylPhysicalFixture

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeOriginFrame

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking

def commonPrefixLength : List Nat → List Nat → Nat
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => if x = y then 1 + commonPrefixLength xs ys else 0

theorem commonPrefix_self (xs : List Nat) : commonPrefixLength xs xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [commonPrefixLength, ih, Nat.add_comm]

theorem commonPrefix_symm (xs ys : List Nat) :
    commonPrefixLength xs ys = commonPrefixLength ys xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys => simp [commonPrefixLength, eq_comm, ih]

theorem commonPrefix_extension (xs tail : List Nat) :
    commonPrefixLength xs (xs ++ tail) = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [commonPrefixLength, ih, Nat.add_comm]

/-- Tree metric on rootward paths; no graph-shortest-distance claim. -/
def pathDistance (origin target : List Nat) : Nat :=
  origin.length + target.length - 2 * commonPrefixLength origin target

theorem pathDistance_self (xs : List Nat) : pathDistance xs xs = 0 := by
  simp [pathDistance, commonPrefix_self]; omega

theorem pathDistance_symm (xs ys : List Nat) :
    pathDistance xs ys = pathDistance ys xs := by
  simp only [pathDistance, commonPrefix_symm xs ys]
  omega

theorem descending_edge_one (parent : List Nat) (child : Nat) :
    pathDistance parent (parent ++ [child]) = 1 := by
  simp [pathDistance, commonPrefix_extension]; omega

theorem ascending_edge_one (parent : List Nat) (child : Nat) :
    pathDistance (parent ++ [child]) parent = 1 := by
  rw [pathDistance_symm]
  exact descending_edge_one parent child

def frameDistance (originHistory targetHistory : List Nat) : Nat :=
  pathDistance originHistory.reverse targetHistory.reverse

theorem frameDistance_self (history : List Nat) : frameDistance history history = 0 :=
  pathDistance_self history.reverse

theorem frameDistance_symm (origin target : List Nat) :
    frameDistance origin target = frameDistance target origin :=
  pathDistance_symm origin.reverse target.reverse

theorem generated_history_child_edge (history : List Nat) (atom : Nat) :
    frameDistance history (atom :: history) = 1 := by
  simp only [frameDistance, List.reverse_cons]
  exact descending_edge_one history.reverse atom

theorem generated_history_parent_edge (history : List Nat) (atom : Nat) :
    frameDistance (atom :: history) history = 1 := by
  rw [frameDistance_symm]
  exact generated_history_child_edge history atom

/-- Immutable original generated center, separate from the unchanged discovery cursor. -/
structure OriginalTreeFrame (mol : RawMolecule) (discoveryRoot : Nat) where
  center : CanonicalBranchNode
  generated : CanonicalCenterTreeNode mol discoveryRoot center

def OriginalTreeFrame.distance {mol : RawMolecule} {root : Nat}
    (frame : OriginalTreeFrame mol root) (target : CanonicalBranchNode) : Nat :=
  frameDistance frame.center.history target.history

def preserveDiscovery (cursor : CanonicalRerootCursor) : CanonicalRerootCursor := cursor

theorem original_cursor_preserved (cursor : CanonicalRerootCursor) :
    preserveDiscovery cursor = cursor := rfl

theorem original_history_preserved (cursor : CanonicalRerootCursor) :
    (preserveDiscovery cursor).node.history = cursor.node.history := rfl

theorem original_provenance_preserved (cursor : CanonicalRerootCursor) :
    (preserveDiscovery cursor).node.provenance = cursor.node.provenance := rfl

def fixtureFrame : OriginalTreeFrame InteriorMethylDepthCounterexample.molecule 1 :=
  ⟨InteriorMethylDepthCounterexample.tagOccurrence,
    InteriorMethylDepthCounterexample.actual_tag_generated⟩

theorem real_fixture_generated :
    CanonicalCenterRerootCursor InteriorMethylDepthCounterexample.molecule 1
      InteriorMethylDepthCounterexample.incoming ∧
    CanonicalCenterRerootCursor InteriorMethylDepthCounterexample.molecule 1
      InteriorMethylDepthCounterexample.outgoing :=
  ⟨InteriorMethylDepthCounterexample.actual_incoming_generated,
    InteriorMethylDepthCounterexample.actual_outgoing_generated⟩

theorem fixture_incoming_distance :
    fixtureFrame.distance InteriorMethylDepthCounterexample.incoming.node = 1 := rfl

theorem fixture_outgoing_distance :
    fixtureFrame.distance InteriorMethylDepthCounterexample.outgoing.node = 1 := rfl

theorem fixture_hydrogen_distances :
    frameDistance [0, 1] [3, 1] = 2 ∧
    frameDistance [0, 1] [6, 2, 0, 1] = 2 := ⟨rfl, rfl⟩

def incomingHydrogen : CanonicalBranchNode := canonicalRoot 1 3

def outgoingHydrogen : CanonicalBranchNode :=
  { atom := 6, parent := 2, history := [6, 2, 0, 1], provenance := .realAtom }

theorem fixture_hydrogens_generated :
    CanonicalCenterTreeNode InteriorMethylDepthCounterexample.molecule 1 incomingHydrogen ∧
    CanonicalCenterTreeNode InteriorMethylDepthCounterexample.molecule 1 outgoingHydrogen := by
  constructor
  · exact .child .root (by decide +kernel)
  · have parentGenerated :
        CanonicalCenterTreeNode InteriorMethylDepthCounterexample.molecule 1
          InteriorMethylDepthCounterexample.outgoing.node :=
        .child InteriorMethylDepthCounterexample.actual_tag_generated (by decide +kernel)
    exact .child parentGenerated (by decide +kernel)

/-- Coordinate interpretation is available only with an actual generated parent/child
and provenance, not for an arbitrary stored scalar or a fabricated real cursor. -/
structure GeneratedDuplicateCoordinate (mol : RawMolecule) (root : Nat) where
  parent : CanonicalBranchNode
  child : CanonicalBranchNode
  parentGenerated : CanonicalCenterTreeNode mol root parent
  childGenerated : child ∈ mol.canonicalChildren parent
  storedDistance : Nat
  duplicateKind : child.provenance = .multipleBondDuplicate storedDistance ∨
    child.provenance = .ringDuplicate storedDistance
  coordinateBound : storedDistance + 1 ≤ parent.history.length

def GeneratedDuplicateCoordinate.rootwardCoordinate {mol : RawMolecule} {root : Nat}
    (duplicate : GeneratedDuplicateCoordinate mol root) : List Nat :=
  duplicate.parent.history.reverse.take (duplicate.storedDistance + 1)

def duplicateReferenceDistance {mol : RawMolecule} {root : Nat}
    (frame : OriginalTreeFrame mol root) (duplicate : GeneratedDuplicateCoordinate mol root) : Nat :=
  pathDistance frame.center.history.reverse duplicate.rootwardCoordinate

/-- Padding inherits its parent coordinate in the fixed frame, then takes one tree edge. -/
def paddingReferenceDistance {mol : RawMolecule} {root : Nat}
    (frame : OriginalTreeFrame mol root) (parent : CanonicalBranchNode) : Nat :=
  frame.distance parent + 1

theorem padding_frame_bound {mol : RawMolecule} {root : Nat}
    (frame : OriginalTreeFrame mol root) (parent : CanonicalBranchNode) :
    paddingReferenceDistance frame parent = frame.distance parent + 1 := rfl

theorem frame_inhabited :
    Nonempty (OriginalTreeFrame InteriorMethylDepthCounterexample.molecule 1) :=
  ⟨fixtureFrame⟩

end TetraStereo.UniversalProof.NativeOriginFrame
