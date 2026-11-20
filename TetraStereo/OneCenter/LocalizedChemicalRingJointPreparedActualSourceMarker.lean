import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCutCursorTransport
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceMarkerTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! Actual real-arm joint markers equal the source molecular-cut construction.
The molecular focus/incoming carrier, candidate cutoff map, global prior window and reference
list determine the source arm. Its structural isomorphism, parent-context readback, marker
covariance and comparison agreement are constructed, not hypotheses. The arm may contain
ring duplicates and arbitrary nested branching. The terminal-focus case is separate.
This is a fixed-candidate-state key theorem; recursive model correctness remains separate.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualSourceMarker

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedVirtualTarget
open LocalizedChemicalRingJointMarkerKey LocalizedChemicalRingSourceCutWindows
open LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey
open LocalizedChemicalRingJointPreparedSourceMarkerTransport

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)

/-- The actual mathematical marker of a realized arm has a fully molecular source witness.
All source fields are fixed by the molecular carrier, candidate map and ordered references;
no label correctness, supplied graph map, successful comparison or marker equality is assumed. -/
theorem realArm_marker_eq_source
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (fallback : CompleteLigandRule5Key) (references : List input.Atom)
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (retainedCarrierFuel input) → Option LocalizedAuxiliaryLabel}
    (parent cursor : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (member : cursor ∈ input.executableLocalizedRerootChildren parent)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (actual : input.RuleMajorContextArm (retainedCarrierFuel input) stage read cursor) :
    ∃ source : RealCutArm input.moleculeGraph cursor.occurrence.1.root,
      source.descriptorMap = cutMap descriptorMap target.1.address.length ∧
      source.W = allCutWidth input.moleculeGraph ∧ source.D = allCutDepth input.moleculeGraph ∧
      source.references = references ∧
      input.occurrenceCarrierNode single cursor.occurrence = .real source.focus ∧
      source.incoming.map Subtype.val =
        some (input.occurrenceCarrierNode single parent.occurrence) ∧
      ∀ W D,
        jointMarkerKey (ruleMajorTreeGraph actual.tree)
            (deepPrior descriptorMap target fallback actual.tree)
            (referenceMarks input references actual.tree) W D references.length
            (ruleMajorTreeGraph actual.tree).root =
          source.markerAt W D references.length source.graph.root := by
  have enough : input.certified.input.molecule.atomCount ≤ retainedCarrierFuel input := by
    simp [retainedCarrierFuel]
  obtain ⟨_previous, path, hpath, incoming, child, focusEq, incomingEq, iso,
    carrierEq, _injective, _root, _children, _parents⟩ :=
    input.executableChild_cutCursorTransport single enough parent cursor member real actual
  let source : RealCutArm input.moleculeGraph cursor.occurrence.1.root := {
    descriptorMap := cutMap descriptorMap target.1.address.length
    focus := path
    hfocus := hpath
    incoming := some incoming
    anchor := realAnchor (CutAnchor.realChild child)
    W := allCutWidth input.moleculeGraph
    D := allCutDepth input.moleculeGraph
    references := references
  }
  refine ⟨source, rfl, rfl, rfl, rfl, focusEq, ?_, ?_⟩
  · exact congrArg some incomingEq
  · intro W D
    have faithful : ∀ node,
        input.occurrenceCarrierNode single
            (LocalizedMarkedRetainedCanonicalMarker.nodeSource input actual.tree node).occurrence =
          (source.carrier (iso.toEquiv node)).1 :=
      fun node => (carrierEq node).symm
    have transported := marker_eq_source input single source actual.tree iso faithful
      descriptorMap target rfl rfl rfl fallback
      (LocalizedRuleMajorSortTrace.realizes_of_trace actual.trace)
      W D (ruleMajorTreeGraph actual.tree).root
    exact transported.trans (congrArg
      (fun node : source.graph.Node => source.markerAt W D references.length node) iso.map_root)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualSourceMarker

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualSourceMarker.realArm_marker_eq_source
