import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey
import TetraStereo.OneCenter.DeclarativeCIPCanonicalAddressing
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Source joint marker of a terminal ring cut

The real-arm source core `...SourceJointKey` covers a real focus.  A full source auxiliary frame can
also have a ring-terminal child slot: the child is the one-node `ringTerminalArm` entered from its
unique carrier parent.  This module supplies only that missing source case.

It exports:

* `childList_eq_nil_of_no_child` and `jointMarkerKey_eq_of_childList_eq_nil`: the general leaf
  equation for the mathematical joint marker;
* `sourceCutArm_ring_terminal`: the source cut of a ring focus is exactly `ringTerminalArm`;
* `sourceSubtreeGraph_ringTerminal` / `sourceSubtreeKey_ringTerminal`: the source joint-key core's
  general subtree graph and prior at a ring terminal node are the terminal graph and its retained
  complete key in the carrier parent's occurrence context;
* `carrierReferenceMark_ring` / `carrierReferenceMarks_ring`: ordered reference marks at the ring
  atom;
* `TerminalRingCut`: the source data of a terminal ring cut and its genuine source graphs;
* `TerminalRingCut.jointMarkerAt_eq_assemble_map`: the exact singleton-tree equation for the source
  terminal marker, with the reference vector written at the ring atom.

The terminal node's own prior is deliberately an arbitrary parameter.  A one-node graph has no
children, so its root marker is `assembleJointMarker W D n marks []` and no prior can enter that
equation.  This is why no source prior is selected here.

No compiled stage graph, runtime comparator, `preparedFacts`, `generated`, or `preparedDescriptor?`
occurs below.  This file does not itself prove the runtime bridge from an actual terminal frame to
this source graph, native-window selection, Rule-6 semantics, IUPAC fidelity or physical
correctness.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal

open CertifiedLocalizedCIPInput DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier
open DeclarativeCIP.RetainedCutArm
open LocalizedRetainedSourceCutFrames
open LocalizedChemicalRingJointMarkerKey
open LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey

noncomputable section
open scoped Classical

universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
variable {molecule : MoleculeGraph Atom} {root : Atom}

/-! ## General leaf equation -/

omit [Fintype Atom] [DecidableEq Atom] in
/-- A node with no child has empty `childList`. -/
theorem childList_eq_nil_of_no_child {graph : RootedDigraph Atom} {node : graph.Node}
    (h : ∀ child, ¬ graph.child node child) :
    graph.childList node = [] := by
  cases hlist : graph.childList node with
  | nil => rfl
  | cons child rest =>
      have hmem : child ∈ graph.childList node := by
        rw [hlist]
        simp
      exfalso
      exact (h child) ((RootedDigraph.mem_childList graph).1 hmem)

omit [Fintype Atom] [DecidableEq Atom] in
/-- At a childless node the joint marker is exactly the assembled vector of the node's own marks,
with the empty child-key list. -/
theorem jointMarkerKey_eq_of_childList_eq_nil
    {graph : RootedDigraph Atom} {P : Type*} [LinearOrder P]
    (prior : graph.Node → P) (marks : graph.Node → List Nat)
    (W D n : Nat) {node : graph.Node} (hchildren : graph.childList node = []) :
    jointMarkerKey graph prior marks W D n node =
      assembleJointMarker W D n (marks node) [] := by
  rw [jointMarkerKey_eq]
  have hranked : rankedJointKeys graph prior marks W D n node = [] := by
    unfold rankedJointKeys
    rw [hchildren]
    rfl
  rw [hranked]
  simp

/-! ## The source terminal graph -/

/-- The source predecessor cut of a ring focus is its genuine one-node terminal arm. -/
theorem sourceCutArm_ring_terminal (molecule : MoleculeGraph Atom) (root : Atom)
    {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom)) :
    sourceCutArm molecule root (.ring path atom) (.real path) =
      ringTerminalArm molecule root h := by
  let anchor : CutAnchor ⟨CarrierNode.ring path atom, h⟩
      (some ⟨CarrierNode.real path, h.1⟩) := CutAnchor.ringParent
  have hsource := sourceCutArm_eq (molecule := molecule) (root := root)
    (focus := ⟨CarrierNode.ring path atom, h⟩)
    (incoming := ⟨CarrierNode.real path, h.1⟩) anchor
  exact hsource.trans (cutRetainedArm_ringParent h)

/-- The general source-subtree graph of the real-arm source core, evaluated at a ring terminal
node, is exactly `ringTerminalArm`.  Any reroot focus gives the same ring carrier parent. -/
theorem sourceSubtreeGraph_ringTerminal (molecule : MoleculeGraph Atom) (root : Atom)
    (focus : List Atom) {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom)) :
    sourceSubtreeGraph molecule root focus (.ring path atom) =
      ringTerminalArm molecule root h := by
  simp only [sourceSubtreeGraph, rerootParentCarrier_ring focus path atom]
  exact sourceCutArm_ring_terminal molecule root h

/-- The source joint-key prior at a ring terminal node is the retained complete key of the
one-node terminal graph, read in the carrier parent's occurrence context. -/
theorem sourceSubtreeKey_ringTerminal (molecule : MoleculeGraph Atom) (root : Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (focus : List Atom) {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom)) (W D : Nat) :
    sourceSubtreeKey molecule root descriptorMap focus (.ring path atom) W D =
      retainedCompleteLigandRule5KeyAt molecule descriptorMap
        (occurrenceReadback root (.real path)) (ringTerminalArm molecule root h) W D := by
  have hparent : rerootParentCarrier focus (.ring path atom) = some (.real path) :=
    rerootParentCarrier_ring focus path atom
  rw [sourceSubtreeKey_eq_some molecule root descriptorMap hparent W D,
    sourceCutArm_ring_terminal molecule root h]
  rfl

/-- The terminal arm's root has no children. -/
theorem ringTerminalArm_childList_root (molecule : MoleculeGraph Atom) (root : Atom)
    {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom)) :
    (ringTerminalArm molecule root h).childList (ringTerminalArm molecule root h).root = [] := by
  apply childList_eq_nil_of_no_child
  intro child hchild
  change False at hchild
  exact hchild

/-- Exact singleton-tree equation for an arbitrary prior and arbitrary node marks on
`ringTerminalArm`.  The prior is present only because `jointMarkerKey` is total; no child exists,
so it cannot affect the root marker. -/
theorem jointMarkerKey_ringTerminalArm_eq
    (molecule : MoleculeGraph Atom) (root : Atom)
    {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom))
    {P : Type*} [LinearOrder P]
    (prior : (ringTerminalArm molecule root h).Node → P)
    (marks : (ringTerminalArm molecule root h).Node → List Nat)
    (W D n : Nat) :
    jointMarkerKey (ringTerminalArm molecule root h) prior marks W D n
        (ringTerminalArm molecule root h).root =
      assembleJointMarker W D n
        (marks (ringTerminalArm molecule root h).root) [] :=
  jointMarkerKey_eq_of_childList_eq_nil (graph := ringTerminalArm molecule root h)
    prior marks W D n (ringTerminalArm_childList_root molecule root h)

/-! ## Ordered reference marks at the ring atom -/

/-- A ring carrier node marks exactly its terminal atom, independently of the ring prefix. -/
theorem carrierReferenceMark_ring (molecule : MoleculeGraph Atom) (root : Atom)
    {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom))
    (reference : Atom) :
    carrierReferenceMark molecule root reference ⟨CarrierNode.ring path atom, h⟩ =
      if atom = reference then 1 else 0 := by
  simp [carrierReferenceMark, CarrierNode.atomOf]

/-- In the caller's reference order, the marks of the ring carrier node are exactly the terminal
atom's indicator vector. -/
theorem carrierReferenceMarks_ring (molecule : MoleculeGraph Atom) (root : Atom)
    {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom))
    (references : List Atom) :
    carrierReferenceMarks molecule root references ⟨CarrierNode.ring path atom, h⟩ =
      references.map fun reference => if atom = reference then 1 else 0 := by
  unfold carrierReferenceMarks
  apply List.map_congr_left
  intro reference _
  exact carrierReferenceMark_ring molecule root h reference

/-! ## A terminal ring cut as source data -/

/-- The source data of a terminal ring cut: a valid ring carrier node, cut from its unique carrier
parent, together with the inherited ordered reference list. -/
structure TerminalRingCut (molecule : MoleculeGraph Atom) (root : Atom) where
  path : List Atom
  atom : Atom
  valid : CarrierNode.Valid molecule root (.ring path atom)
  references : List Atom

namespace TerminalRingCut

variable (cut : TerminalRingCut molecule root)

/-- The carrier parent from which the terminal ring node is cut. -/
def parent : CarrierNode Atom :=
  CarrierNode.real cut.path

/-- The ring focus as a valid molecular occurrence node. -/
def focus : Nodes molecule root :=
  ⟨CarrierNode.ring cut.path cut.atom, cut.valid⟩

/-- The incoming carrier parent as a valid molecular occurrence node. -/
def incoming : Nodes molecule root :=
  ⟨CarrierNode.real cut.path, cut.valid.1⟩

/-- The genuine one-node source terminal graph. -/
def graph : RootedDigraph Atom :=
  ringTerminalArm molecule root cut.valid

/-- The valid molecular carrier node represented by the terminal graph root. -/
def carrier : Nodes molecule root :=
  cut.focus

/-- The terminal graph is the source predecessor cut from the carrier parent. -/
theorem graph_eq_sourceCutArm :
    cut.graph =
      sourceCutArm molecule root (.ring cut.path cut.atom) (.real cut.path) := by
  unfold graph
  exact (sourceCutArm_ring_terminal molecule root cut.valid).symm

/-- The terminal graph is the existing `cutRetainedArm` at the ring-parent anchor. -/
theorem graph_eq_cutRetainedArm :
    cut.graph =
      cutRetainedArm molecule root cut.focus (some cut.incoming)
        (CutAnchor.ringParent (path := cut.path) (atom := cut.atom) (h := cut.valid)) := by
  unfold graph focus incoming
  exact (cutRetainedArm_ringParent cut.valid).symm

/-- The general source joint-key prior at the terminal ring node is the retained complete key of
`cut.graph`, read in the carrier parent's occurrence context. -/
theorem sourceSubtreeKey_eq (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (focus : List Atom) (W D : Nat) :
    sourceSubtreeKey molecule root descriptorMap focus
        (.ring cut.path cut.atom) W D =
      retainedCompleteLigandRule5KeyAt molecule descriptorMap
        (occurrenceReadback root (.real cut.path)) cut.graph W D := by
  simpa [graph] using
    sourceSubtreeKey_ringTerminal molecule root descriptorMap focus cut.valid W D

/-- Ordered atom-identity marks carried by every node of the terminal graph.  There is only one
node, so this function is constant. -/
def marks (_node : cut.graph.Node) : List Nat :=
  carrierReferenceMarks molecule root cut.references cut.carrier

/-- The marks at the terminal graph root are the ring atom's indicator vector. -/
theorem marks_root_eq_map :
    cut.marks cut.graph.root =
      cut.references.map fun reference => if cut.atom = reference then 1 else 0 := by
  simpa [marks, carrier, focus] using
    carrierReferenceMarks_ring molecule root cut.valid cut.references

/-- The number of marker columns is the inherited reference-list length. -/
theorem marks_root_length :
    (cut.marks cut.graph.root).length = cut.references.length := by
  simpa [marks] using
    carrierReferenceMarks_length molecule root cut.references cut.carrier

/-- The source joint marker at any terminal node.  The prior is explicit and arbitrary: on a
childless graph it is not read by the root marker.  The marker layout `(W,D)` is separate from any
prior-observation window because no prior is selected here. -/
def markerAt (prior : cut.graph.Node → CompleteLigandRule5Key)
    (W D n : Nat) (node : cut.graph.Node) : JointMarker :=
  jointMarkerKey cut.graph prior cut.marks W D n node

/-- The source terminal marker at the root, with `references.length` mark columns. -/
def jointMarkerAt (prior : cut.graph.Node → CompleteLigandRule5Key)
    (markerW markerD : Nat) : JointMarker :=
  cut.markerAt prior markerW markerD cut.references.length cut.graph.root

/-- Exact singleton-tree equation: the terminal marker is the assembled vector of the root's
marks and an empty child-key list. -/
theorem markerAt_root_eq_assemble
    (prior : cut.graph.Node → CompleteLigandRule5Key) (W D n : Nat) :
    cut.markerAt prior W D n cut.graph.root =
      assembleJointMarker W D n (cut.marks cut.graph.root) [] := by
  have hchildren : cut.graph.childList cut.graph.root = [] := by
    simpa [graph] using ringTerminalArm_childList_root molecule root cut.valid
  unfold markerAt
  exact jointMarkerKey_eq_of_childList_eq_nil (graph := cut.graph)
    (node := cut.graph.root) prior cut.marks W D n hchildren

/-- Exact source terminal marker equation, before expanding the ring-atom marks. -/
theorem jointMarkerAt_eq_assemble
    (prior : cut.graph.Node → CompleteLigandRule5Key) (markerW markerD : Nat) :
    cut.jointMarkerAt prior markerW markerD =
      assembleJointMarker markerW markerD cut.references.length
        (cut.marks cut.graph.root) [] := by
  unfold jointMarkerAt
  exact cut.markerAt_root_eq_assemble prior markerW markerD cut.references.length

/-- Exact source terminal marker equation with the ordered marks written at the ring atom.  This is
the terminal-ring case the root/cursor integration consumes. -/
theorem jointMarkerAt_eq_assemble_map
    (prior : cut.graph.Node → CompleteLigandRule5Key) (markerW markerD : Nat) :
    cut.jointMarkerAt prior markerW markerD =
      assembleJointMarker markerW markerD cut.references.length
        (cut.references.map fun reference => if cut.atom = reference then 1 else 0) [] := by
  rw [cut.jointMarkerAt_eq_assemble prior, cut.marks_root_eq_map]

end TerminalRingCut

end

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.childList_eq_nil_of_no_child
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.jointMarkerKey_eq_of_childList_eq_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.sourceCutArm_ring_terminal
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.sourceSubtreeGraph_ringTerminal
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.sourceSubtreeKey_ringTerminal
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.ringTerminalArm_childList_root
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.jointMarkerKey_ringTerminalArm_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.carrierReferenceMark_ring
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.carrierReferenceMarks_ring
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.TerminalRingCut
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.TerminalRingCut.parent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.TerminalRingCut.focus
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.TerminalRingCut.incoming
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.TerminalRingCut.graph
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.TerminalRingCut.carrier
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.TerminalRingCut.graph_eq_sourceCutArm
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.TerminalRingCut.graph_eq_cutRetainedArm
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.TerminalRingCut.sourceSubtreeKey_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.TerminalRingCut.marks
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.TerminalRingCut.marks_root_eq_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.TerminalRingCut.marks_root_length
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.TerminalRingCut.markerAt
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.TerminalRingCut.jointMarkerAt
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.TerminalRingCut.markerAt_root_eq_assemble
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.TerminalRingCut.jointMarkerAt_eq_assemble
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal.TerminalRingCut.jointMarkerAt_eq_assemble_map
