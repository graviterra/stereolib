import TetraStereo.OneCenter.BranchSphereKey

set_option autoImplicit false

namespace TetraStereo.OneCenter.CanonicalComparisonFrame

open TetraStereo.OneCenter.RawMolecule

/-! Proposed import-safe observation layer. The frame is chosen once by the caller,
not from a pair being compared. This module neither changes discovery identity nor
claims that a rootward-history metric equals physical graph distance. -/

def commonPrefixLength : List Nat → List Nat → Nat
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => if x = y then 1 + commonPrefixLength xs ys else 0

def pathDistance (origin target : List Nat) : Nat :=
  origin.length + target.length - 2 * commonPrefixLength origin target

def frameDistance (originHistory targetHistory : List Nat) : Nat :=
  pathDistance originHistory.reverse targetHistory.reverse

/-- Immutable comparison-origin history, separate from each original node history. -/
structure Frame where
  originHistory : List Nat
  deriving DecidableEq, Repr

def Frame.realDistance (frame : Frame) (node : CanonicalBranchNode) : Nat :=
  frameDistance frame.originHistory node.history

/-- A candidate duplicate coordinate. Bounds and actual generation are established
separately; the guarded public observation below refuses an out-of-bounds scalar. -/
def duplicateRootwardCoordinate (node : CanonicalBranchNode) (storedDistance : Nat) : List Nat :=
  node.history.tail.reverse.take (storedDistance + 1)

def Frame.duplicateDistance (frame : Frame) (node : CanonicalBranchNode)
    (storedDistance : Nat) : Nat :=
  pathDistance frame.originHistory.reverse (duplicateRootwardCoordinate node storedDistance)

def Frame.duplicateDistance? (frame : Frame) (node : CanonicalBranchNode)
    (storedDistance : Nat) : Option Nat :=
  if storedDistance + 1 ≤ node.history.tail.length then
    some (frame.duplicateDistance node storedDistance)
  else none

/-- Raw phantom nodes have no history-based observation. Padding is observed only
through its explicit parent/frame sidecar, without rewriting the production node. -/
def observeNode (frame : Frame) (node : CanonicalBranchNode) : Option Nat :=
  match node.provenance with
  | .realAtom => some (frame.realDistance node)
  | .multipleBondDuplicate stored => frame.duplicateDistance? node stored
  | .ringDuplicate stored => frame.duplicateDistance? node stored
  | .phantom _ => none

/-- Original node retained alongside its fixed frame; no distance supplied by the caller. -/
structure FramedNode where
  frame : Frame
  original : CanonicalBranchNode
  deriving DecidableEq, Repr

def frameNode (frame : Frame) (node : CanonicalBranchNode) : FramedNode := ⟨frame, node⟩
def FramedNode.distance? (node : FramedNode) : Option Nat := observeNode node.frame node.original

def frameNodes (frame : Frame) (nodes : List CanonicalBranchNode) : List FramedNode :=
  nodes.map (frameNode frame)

/-- The original padding scalar remains discovery metadata. The effective distance
is computed from the framed parent; an unsupported parent remains unsupported. -/
structure PaddingSidecar where
  parent : FramedNode
  storedDistance : Nat
  deriving DecidableEq, Repr

def paddingSidecar (frame : Frame) (parent : CanonicalBranchNode)
    (storedDistance : Nat) : PaddingSidecar :=
  ⟨frameNode frame parent, storedDistance⟩

def PaddingSidecar.original (padding : PaddingSidecar) (mol : RawMolecule) : CanonicalBranchNode :=
  mol.canonicalPhantom padding.parent.original.atom padding.storedDistance

def PaddingSidecar.distance? (padding : PaddingSidecar) : Option Nat :=
  padding.parent.distance?.map (fun distance => distance + 1)

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

theorem pathDistance_self (xs : List Nat) : pathDistance xs xs = 0 := by
  simp [pathDistance, commonPrefix_self]
  omega

theorem pathDistance_symm (xs ys : List Nat) : pathDistance xs ys = pathDistance ys xs := by
  simp only [pathDistance, commonPrefix_symm xs ys]
  omega

theorem frameDistance_self (history : List Nat) : frameDistance history history = 0 :=
  pathDistance_self history.reverse

theorem frameDistance_symm (origin target : List Nat) :
    frameDistance origin target = frameDistance target origin :=
  pathDistance_symm origin.reverse target.reverse

theorem real_observation (frame : Frame) (node : CanonicalBranchNode)
    (real : node.provenance = .realAtom) :
    observeNode frame node = some (frame.realDistance node) := by
  simp only [observeNode, real]

theorem multiple_observation (frame : Frame) (node : CanonicalBranchNode) (stored : Nat)
    (kind : node.provenance = .multipleBondDuplicate stored)
    (bound : stored + 1 ≤ node.history.tail.length) :
    observeNode frame node = some (frame.duplicateDistance node stored) := by
  simp only [observeNode, kind, Frame.duplicateDistance?, if_pos bound]

theorem ring_observation (frame : Frame) (node : CanonicalBranchNode) (stored : Nat)
    (kind : node.provenance = .ringDuplicate stored)
    (bound : stored + 1 ≤ node.history.tail.length) :
    observeNode frame node = some (frame.duplicateDistance node stored) := by
  simp only [observeNode, kind, Frame.duplicateDistance?, if_pos bound]

theorem invalid_duplicate_coordinate (frame : Frame) (node : CanonicalBranchNode) (stored : Nat)
    (invalid : ¬ stored + 1 ≤ node.history.tail.length) :
    frame.duplicateDistance? node stored = none := by
  simp only [Frame.duplicateDistance?, if_neg invalid]

theorem raw_phantom_unobserved (frame : Frame) (node : CanonicalBranchNode) (stored : Nat)
    (kind : node.provenance = .phantom stored) : observeNode frame node = none := by
  simp only [observeNode, kind]

theorem frameNode_preserves_original (frame : Frame) (node : CanonicalBranchNode) :
    (frameNode frame node).original = node := rfl

theorem frameNode_preserves_history (frame : Frame) (node : CanonicalBranchNode) :
    (frameNode frame node).original.history = node.history := rfl

theorem frameNode_preserves_provenance (frame : Frame) (node : CanonicalBranchNode) :
    (frameNode frame node).original.provenance = node.provenance := rfl

theorem frameNodes_preserves_originals (frame : Frame) (nodes : List CanonicalBranchNode) :
    (frameNodes frame nodes).map FramedNode.original = nodes := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih =>
    simpa only [frameNodes, List.map_cons, frameNode] using congrArg (List.cons node) ih

theorem frameNodes_preserves_frame (frame : Frame) (nodes : List CanonicalBranchNode)
    (node : FramedNode) (member : node ∈ frameNodes frame nodes) : node.frame = frame := by
  obtain ⟨original, _originalMember, rfl⟩ := List.mem_map.mp member
  rfl

theorem padding_preserves_production_node (frame : Frame) (mol : RawMolecule)
    (parent : CanonicalBranchNode) (stored : Nat) :
    (paddingSidecar frame parent stored).original mol = mol.canonicalPhantom parent.atom stored := rfl

theorem padding_preserves_provenance (frame : Frame) (mol : RawMolecule)
    (parent : CanonicalBranchNode) (stored : Nat) :
    ((paddingSidecar frame parent stored).original mol).provenance = .phantom stored := rfl

theorem padding_preserves_empty_history (frame : Frame) (mol : RawMolecule)
    (parent : CanonicalBranchNode) (stored : Nat) :
    ((paddingSidecar frame parent stored).original mol).history = [] := rfl

theorem padding_raw_observation_none (frame : Frame) (mol : RawMolecule)
    (parent : CanonicalBranchNode) (stored : Nat) :
    observeNode frame ((paddingSidecar frame parent stored).original mol) = none := rfl

theorem padding_from_parent (frame : Frame) (parent : CanonicalBranchNode) (stored : Nat) :
    (paddingSidecar frame parent stored).distance? =
      (observeNode frame parent).map (fun distance => distance + 1) := rfl

theorem padding_real_distance (frame : Frame) (parent : CanonicalBranchNode) (stored : Nat)
    (real : parent.provenance = .realAtom) :
    (paddingSidecar frame parent stored).distance? = some (frame.realDistance parent + 1) := by
  change (observeNode frame parent).map (fun distance => distance + 1) = _
  rw [real_observation frame parent real]
  rfl

theorem padding_unsupported_parent (frame : Frame) (parent : CanonicalBranchNode)
    (stored parentStored : Nat) (phantom : parent.provenance = .phantom parentStored) :
    (paddingSidecar frame parent stored).distance? = none := by
  change (observeNode frame parent).map (fun distance => distance + 1) = none
  rw [raw_phantom_unobserved frame parent parentStored phantom]
  rfl

end TetraStereo.OneCenter.CanonicalComparisonFrame
