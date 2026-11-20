import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedUniformCutPrior
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! Transport of the actual joint marker to a molecular predecessor cut.
Only the structural carrier-faithful isomorphism is supplied here. Parent contexts,
reference marks and ordinary-prior comparisons are derived. The source cut's prior map
is the candidate cut map, and its prior window is the source-only molecular window.
The separate cursor-cover theorem is responsible for constructing the isomorphism.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceMarkerTransport

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedCanonicalMarker LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedVirtualTarget LocalizedMarkedRetainedPromotedKey
open LocalizedChemicalRingJointMarkerKey LocalizedCumulativeDecoratedTree
open LocalizedChemicalRingJointPreparedDeepCutPrior
open LocalizedChemicalRingJointPreparedUniformCutPrior LocalizedChemicalRingSourceCutWindows
open LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey

noncomputable section

variable (input : CertifiedLocalizedCIPInput)

/-- A valid molecular carrier fixes its original root, including at a ring terminal. -/
theorem carrier_root_unique {first second : input.Atom} (node : CarrierNode input.Atom)
    (validFirst : CarrierNode.Valid input.moleculeGraph first node)
    (validSecond : CarrierNode.Valid input.moleculeGraph second node) : first = second := by
  cases node with
  | real path =>
      exact Option.some.inj ((SimpleFrom.head?_eq validFirst).symm.trans
        (SimpleFrom.head?_eq validSecond))
  | ring path atom =>
      exact Option.some.inj ((SimpleFrom.head?_eq validFirst.1).symm.trans
        (SimpleFrom.head?_eq validSecond.1))

variable (single : input.moleculeGraph.SimpleBonded)
  {root : input.Atom} (arm : RealCutArm input.moleculeGraph root)
  (tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input))
  (iso : RootedDigraph.Iso (ruleMajorTreeGraph tree) arm.graph)
  (faithful : ∀ node, input.occurrenceCarrierNode single (nodeSource input tree node).occurrence =
    (arm.carrier (iso.toEquiv node)).1)

include faithful in
/-- The structural carrier identity also identifies the occurrence's outer molecular root. -/
theorem node_root_eq (node : (ruleMajorTreeGraph tree).Node) :
    (nodeSource input tree node).occurrence.1.root = root := by
  apply carrier_root_unique input
    (input.occurrenceCarrierNode single (nodeSource input tree node).occurrence)
    (input.occurrenceCarrierNode_valid single (nodeSource input tree node).occurrence)
  rw [faithful node]
  exact (arm.carrier (iso.toEquiv node)).2

include faithful in
/-- Parent occurrence contexts are derived from carrier readback, not assumed to agree. -/
theorem parent_context_eq (node : (ruleMajorTreeGraph tree).Node) :
    parentUnit (nodeSource input tree node) =
      occurrenceReadback root (arm.carrier (iso.toEquiv node)).1 := by
  unfold parentUnit
  rw [← input.occurrenceCarrierNode_readback single (nodeSource input tree node).occurrence,
    node_root_eq input single arm tree iso faithful node, faithful node]

include faithful in
/-- All ordered mark columns agree, including marks on ring-duplicate nodes. -/
theorem marks_eq (node : (ruleMajorTreeGraph tree).Node) :
    referenceMarks input arm.references tree node = arm.marks (iso.toEquiv node) := by
  have label := congrArg NodeLabel.atom?
    (input.occurrenceCarrierNode_label single (nodeSource input tree node).occurrence)
  have atomEq : CarrierNode.atomOf
      (input.occurrenceCarrierNode single (nodeSource input tree node).occurrence) =
      (nodeSource input tree node).occurrence.1.node.current? := by
    have carrierAtom (carrier : CarrierNode input.Atom) :
        (CarrierNode.label carrier).atom? = CarrierNode.atomOf carrier := by
      cases carrier <;> rfl
    simpa only [carrierAtom, OfficialCIPNode.toDeclarativeLabel] using label
  rw [faithful node] at atomEq
  unfold referenceMarks RealCutArm.marks carrierReferenceMarks
  apply List.map_congr_left
  intro reference _
  simp only [referenceMark, referenceBit, carrierReferenceMark, atomEq]

variable (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (mapEq : arm.descriptorMap = cutMap descriptorMap target.1.address.length)
  (widthEq : arm.W = allCutWidth input.moleculeGraph)
  (depthEq : arm.D = allCutDepth input.moleculeGraph)

include faithful mapEq widthEq depthEq in
/-- At every actual edge the source ordinary prior is exactly the uniformly windowed prior.
The rerooted parent follows from the graph edge; it is not an extra correspondence premise. -/
theorem child_prior_eq {parent child : (ruleMajorTreeGraph tree).Node}
    (edge : (ruleMajorTreeGraph tree).child parent child) :
    uniformSourcePrior input single descriptorMap target tree child =
      arm.prior (iso.toEquiv child) := by
  have sourceEdge := (iso.map_child parent child).mp edge
  have predecessor : arm.parentCarrier (iso.toEquiv child) =
      some (arm.carrier (iso.toEquiv parent)).1 := sourceEdge
  rw [arm.prior_eq_sourceCutArm predecessor, mapEq, widthEq, depthEq]
  unfold uniformSourcePrior
  rw [parentSource_of_child tree edge]
  unfold uniformSourceDeepKey sourceChildCut rerootParentOccurrence
  rw [parent_context_eq input single arm tree iso faithful parent,
    node_root_eq input single arm tree iso faithful child,
    faithful child, faithful parent]

include faithful mapEq widthEq depthEq in
/-- The actual deep-prior marker equals the molecular-cut marker.
Every reader-context and mark correspondence is derived from structural carrier faithfulness. -/
theorem marker_eq_source
    (fallback : CompleteLigandRule5Key)
    {read : input.LocalizedRerootCursor (retainedCarrierFuel input) → Option LocalizedAuxiliaryLabel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (W D : Nat) (node : (ruleMajorTreeGraph tree).Node) :
    jointMarkerKey (ruleMajorTreeGraph tree) (deepPrior descriptorMap target fallback tree)
        (referenceMarks input arm.references tree) W D arm.references.length node =
      arm.markerAt W D arm.references.length (iso.toEquiv node) := by
  rw [jointMarkerKey_eq_uniformSource input single descriptorMap target fallback tree realizes]
  apply LocalizedChemicalRingJointMarkerPriorOrderCongruence.jointMarkerKey_iso_of_sibling_order
  · intro parent left right leftEdge rightEdge
    rw [child_prior_eq input single arm tree iso faithful descriptorMap target mapEq widthEq depthEq leftEdge,
      child_prior_eq input single arm tree iso faithful descriptorMap target mapEq widthEq depthEq rightEdge]
    exact ⟨Iff.rfl, Iff.rfl⟩
  · intro current index _
    rw [marks_eq input single arm tree iso faithful current]

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceMarkerTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceMarkerTransport.carrier_root_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceMarkerTransport.node_root_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceMarkerTransport.parent_context_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceMarkerTransport.marks_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceMarkerTransport.child_prior_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceMarkerTransport.marker_eq_source
