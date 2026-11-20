import TetraStereo.OneCenter.DeclarativeCIPRetainedCutArm
import TetraStereo.OneCenter.DeclarativeCIPRetainedCompleteSignatures
import TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames
import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerPriorOrderCongruence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-!
# Source joint-key core of a real predecessor-cut arm

This is the small standalone core requested for actual/source cursor transport.  It exports:

* `rerootParentCarrier`: the rerooted-arm predecessor `rawNewParent focus node`;
* `sourceSubtreeGraph` / `sourceSubtreeKey`: the existing source-only cut `sourceCutArm` and its
  independent retained complete key, read at the reroot parent's molecular occurrence context;
* `carrierReferenceMark` / `carrierReferenceMarks`: ordered atom-identity marks on the carrier;
* `RealCutArm`: a genuine `realCutRetainedArm` plus the concrete prior and all marks;
* `RealCutArm.jointMarker`: the mathematical `jointMarkerKey` recursion;
* `RealCutArm.CarrierFaithful`: the layout hypothesis a cursor-transport isomorphism must satisfy;
* `RealCutArm.prior_eq_actualCarrier` / `marks_eq_actualCarrier`: transport of the source key and
  marks across that layout.

No compiled stage graph, runtime comparator, `preparedFacts`, `generated`, or `preparedDescriptor?`
occurs below.  The root fallback prior is the uncut outer-root arm; it is harmless to a joint marker
because a root's own prior is never a sibling prior.  This file does not prove the runtime bridge,
faithful-cut isomorphism from `realCutRetainedArm` to a production arm, native-window selection,
Rule-6 family semantics, IUPAC fidelity or physical correctness.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey

open CertifiedLocalizedCIPInput DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier
open DeclarativeCIP.RetainedCutArm
open LocalizedRetainedSourceCutFrames
open LocalizedChemicalRingJointMarkerKey
open LocalizedChemicalRingJointMarkerPriorOrderCongruence

noncomputable section
open scoped Classical

universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
variable {molecule : MoleculeGraph Atom} {root : Atom}

/-- The predecessor of a carrier node in the arm rerooted at `focus`: exactly the carrier-level
reroot parent `rawNewParent focus node`, not the outer-root prefix parent. -/
def rerootParentCarrier (focus : List Atom) (node : CarrierNode Atom) : Option (CarrierNode Atom) :=
  rawNewParent focus node

theorem rerootParentCarrier_focus (focus : List Atom) :
    rerootParentCarrier focus (CarrierNode.real focus) = none :=
  rawNewParent_focus focus

omit [Fintype Atom] in
theorem rerootParentCarrier_ring (focus path : List Atom) (atom : Atom) :
    rerootParentCarrier focus (CarrierNode.ring path atom) = some (CarrierNode.real path) := by
  simp [rerootParentCarrier, rawNewParent]

/-- The inherited molecular occurrence context of a reroot parent. -/
def rerootParentOccurrence (root : Atom) (parent : CarrierNode Atom) : OccurrenceUnit Atom :=
  occurrenceReadback root parent

/-- The source cut whose focus is `node`, entered from its reroot parent in the arm at `focus`.
At the arm root there is no parent and the fallback is the uncut outer-root arm. -/
def sourceSubtreeGraph (molecule : MoleculeGraph Atom) (root : Atom)
    (focus : List Atom) (node : CarrierNode Atom) : RootedDigraph Atom :=
  match rerootParentCarrier focus node with
  | some parent => sourceCutArm molecule root node parent
  | none =>
      cutRetainedArm molecule root ⟨CarrierNode.real [root], carrier_root_valid molecule root⟩
        none CutAnchor.noCut

/-- The retained complete key of the node's source predecessor-cut subtree, read in the molecular
occurrence context of its reroot parent. -/
def sourceSubtreeKey (molecule : MoleculeGraph Atom) (root : Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (focus : List Atom) (node : CarrierNode Atom) (W D : Nat) : CompleteLigandRule5Key :=
  match rerootParentCarrier focus node with
  | some parent =>
      retainedCompleteLigandRule5KeyAt molecule descriptorMap
        (rerootParentOccurrence root parent) (sourceCutArm molecule root node parent) W D
  | none =>
      retainedCompleteLigandRule5KeyAt molecule descriptorMap
        (occurrenceReadback root node)
        (cutRetainedArm molecule root ⟨CarrierNode.real [root], carrier_root_valid molecule root⟩
          none CutAnchor.noCut) W D

theorem sourceSubtreeKey_eq_some (molecule : MoleculeGraph Atom) (root : Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    {focus : List Atom} {node parent : CarrierNode Atom}
    (hparent : rerootParentCarrier focus node = some parent) (W D : Nat) :
    sourceSubtreeKey molecule root descriptorMap focus node W D =
      retainedCompleteLigandRule5KeyAt molecule descriptorMap
        (rerootParentOccurrence root parent) (sourceCutArm molecule root node parent) W D := by
  simp only [sourceSubtreeKey, hparent]

theorem sourceSubtreeKey_eq_none (molecule : MoleculeGraph Atom) (root : Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    {focus : List Atom} {node : CarrierNode Atom}
    (hparent : rerootParentCarrier focus node = none) (W D : Nat) :
    sourceSubtreeKey molecule root descriptorMap focus node W D =
      retainedCompleteLigandRule5KeyAt molecule descriptorMap
        (occurrenceReadback root node)
        (cutRetainedArm molecule root ⟨CarrierNode.real [root], carrier_root_valid molecule root⟩
          none CutAnchor.noCut) W D := by
  simp only [sourceSubtreeKey, hparent]

/-- The absolute atom-identity mark of one inherited reference at a carrier node. -/
def carrierReferenceMark (molecule : MoleculeGraph Atom) (root : Atom)
    (reference : Atom) (node : Nodes molecule root) : Nat :=
  if CarrierNode.atomOf node.1 = some reference then 1 else 0

theorem carrierReferenceMark_eq_one (molecule : MoleculeGraph Atom) (root : Atom)
    {reference : Atom} {node : Nodes molecule root}
    (h : CarrierNode.atomOf node.1 = some reference) :
    carrierReferenceMark molecule root reference node = 1 := by
  simp [carrierReferenceMark, h]

theorem carrierReferenceMark_eq_zero (molecule : MoleculeGraph Atom) (root : Atom)
    {reference : Atom} {node : Nodes molecule root}
    (h : CarrierNode.atomOf node.1 ≠ some reference) :
    carrierReferenceMark molecule root reference node = 0 := by
  simp [carrierReferenceMark, h]

/-- Ordered atom-identity marks in the caller's reference order. -/
def carrierReferenceMarks (molecule : MoleculeGraph Atom) (root : Atom)
    (references : List Atom) (node : Nodes molecule root) : List Nat :=
  references.map fun reference => carrierReferenceMark molecule root reference node

theorem carrierReferenceMarks_length (molecule : MoleculeGraph Atom) (root : Atom)
    (references : List Atom) (node : Nodes molecule root) :
    (carrierReferenceMarks molecule root references node).length = references.length := by
  simp [carrierReferenceMarks]

/-- A real predecessor-cut arm with the concrete source priors and ordered marks. -/
structure RealCutArm (molecule : MoleculeGraph Atom) (root : Atom) where
  descriptorMap : DescriptorMap (DetectedOccurrence molecule)
  focus : List Atom
  hfocus : SimpleFrom molecule root focus
  incoming : Option (Nodes molecule root)
  anchor : RealCutAnchor focus hfocus incoming
  W : Nat
  D : Nat
  references : List Atom

namespace RealCutArm

variable (arm : RealCutArm molecule root)

/-- The genuine real predecessor-cut graph. -/
def graph : RootedDigraph Atom :=
  realCutRetainedArm molecule root arm.hfocus arm.incoming arm.anchor

/-- The molecular carrier node underlying an arm node. -/
def carrier (node : arm.graph.Node) : Nodes molecule root := node.1

/-- The reroot parent carrier of an arm node, selected by `rawNewParent` at the arm's own focus. -/
def parentCarrier (node : arm.graph.Node) : Option (CarrierNode Atom) :=
  rerootParentCarrier arm.focus (arm.carrier node).1

/-- The concrete source-cut prior of an arm node. -/
def prior (node : arm.graph.Node) : CompleteLigandRule5Key :=
  sourceSubtreeKey molecule root arm.descriptorMap arm.focus (arm.carrier node).1 arm.W arm.D

/-- Ordered atom-identity marks of an arm node. -/
def marks (node : arm.graph.Node) : List Nat :=
  carrierReferenceMarks molecule root arm.references (arm.carrier node)

/-- The joint marker at any arm node, with the concrete prior and all ordered marks. -/
def markerAt (W D n : Nat) (node : arm.graph.Node) : JointMarker :=
  jointMarkerKey arm.graph arm.prior arm.marks W D n node

/-- The root joint marker of the arm. -/
def jointMarker : JointMarker :=
  arm.markerAt arm.W arm.D arm.references.length arm.graph.root

/-- The arm root has no reroot parent; its prior is the documented fallback. -/
theorem parentCarrier_root : arm.parentCarrier arm.graph.root = none :=
  rerootParentCarrier_focus arm.focus

/-- At an internal node the prior is exactly the retained complete key of its source cut. -/
theorem prior_eq_sourceCutArm {node : arm.graph.Node} {parent : CarrierNode Atom}
    (hparent : arm.parentCarrier node = some parent) :
    arm.prior node =
      retainedCompleteLigandRule5KeyAt molecule arm.descriptorMap
        (rerootParentOccurrence root parent)
        (sourceCutArm molecule root (arm.carrier node).1 parent) arm.W arm.D := by
  exact sourceSubtreeKey_eq_some molecule root arm.descriptorMap hparent arm.W arm.D

theorem marks_length (node : arm.graph.Node) :
    (arm.marks node).length = arm.references.length :=
  carrierReferenceMarks_length molecule root arm.references (arm.carrier node)

/-- The layout hypothesis supplied by a cursor-transport isomorphism: every actual-arm node has the
same source carrier as the corresponding molecular cut node. -/
def CarrierFaithful {actual : RootedDigraph Atom} (iso : RootedDigraph.Iso actual arm.graph)
    (actualCarrier : actual.Node → CarrierNode Atom) : Prop :=
  ∀ node, actualCarrier node = (arm.carrier (iso.toEquiv node)).1

/-- Under a carrier-faithful layout, the source prior at the corresponding actual node is the
computed `sourceSubtreeKey` at its actual source carrier. -/
theorem prior_eq_actualCarrier {actual : RootedDigraph Atom}
    (iso : RootedDigraph.Iso actual arm.graph)
    (actualCarrier : actual.Node → CarrierNode Atom)
    (faithful : arm.CarrierFaithful iso actualCarrier) (node : actual.Node) :
    arm.prior (iso.toEquiv node) =
      sourceSubtreeKey molecule root arm.descriptorMap arm.focus (actualCarrier node)
        arm.W arm.D := by
  unfold prior
  rw [faithful node]

/-- Under a carrier-faithful layout, the marks at the corresponding actual node are the marks of
its actual source carrier. -/
theorem marks_eq_actualCarrier {actual : RootedDigraph Atom}
    (iso : RootedDigraph.Iso actual arm.graph)
    (actualCarrier : actual.Node → CarrierNode Atom)
    (faithful : arm.CarrierFaithful iso actualCarrier) (node : actual.Node) :
    arm.marks (iso.toEquiv node) =
      carrierReferenceMarks molecule root arm.references
        ⟨actualCarrier node, by
          rw [faithful node]
          exact (arm.carrier (iso.toEquiv node)).2⟩ := by
  exact congrArg (carrierReferenceMarks molecule root arm.references)
    (Subtype.ext (faithful node).symm)

/-- The joint marker depends only on sibling source-prior order and marks, not on the literal prior
encoding.  Root's accepted sibling-order congruence is reused. -/
theorem markerAt_iso_of_sibling_order {other : RealCutArm molecule root}
    (iso : RootedDigraph.Iso arm.graph other.graph) (W D n : Nat)
    (orders : ∀ parent left right, arm.graph.child parent left → arm.graph.child parent right →
      OrderAgrees (arm.prior left) (arm.prior right)
        (other.prior (iso.toEquiv left)) (other.prior (iso.toEquiv right)))
    (marks : ∀ node index, index < n →
      (other.marks (iso.toEquiv node)).getD index 0 = (arm.marks node).getD index 0)
    (node : arm.graph.Node) :
    arm.markerAt W D n node = other.markerAt W D n (iso.toEquiv node) :=
  jointMarkerKey_iso_of_sibling_order iso arm.prior other.prior arm.marks other.marks
    W D n orders marks node

end RealCutArm

end

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.rerootParentCarrier
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.rerootParentCarrier_focus
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.rerootParentCarrier_ring
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.rerootParentOccurrence
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.sourceSubtreeGraph
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.sourceSubtreeKey
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.sourceSubtreeKey_eq_some
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.sourceSubtreeKey_eq_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.carrierReferenceMark
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.carrierReferenceMark_eq_one
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.carrierReferenceMark_eq_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.carrierReferenceMarks
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.carrierReferenceMarks_length
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.RealCutArm
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.RealCutArm.graph
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.RealCutArm.carrier
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.RealCutArm.parentCarrier
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.RealCutArm.prior
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.RealCutArm.marks
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.RealCutArm.markerAt
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.RealCutArm.jointMarker
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.RealCutArm.parentCarrier_root
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.RealCutArm.prior_eq_sourceCutArm
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.RealCutArm.marks_length
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.RealCutArm.CarrierFaithful
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.RealCutArm.prior_eq_actualCarrier
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.RealCutArm.marks_eq_actualCarrier
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.RealCutArm.markerAt_iso_of_sibling_order

assert_closure_excludes
  TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey.RealCutArm.jointMarker
  [TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm,
   TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?]
