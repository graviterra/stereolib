import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedAllSlotSourceMarkers
import TetraStereo.OneCenter.LocalizedChemicalRingSourceCutMarker
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The actual compiled joint marker equals one deterministic source molecular function.
This removes the proof-bearing existential witness from the all-slot refinement. The source
function has no compiled stage, actual sorting callback, generated state or chosen output.
Its candidate map is explicit; recursive candidate-state meaning is a separate obligation.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCompiledSourceMarker

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedVirtualTarget
open LocalizedChemicalRingJointMarkerRanking
open LocalizedChemicalRingJointPreparedAllSlotSourceMarkers
open LocalizedChemicalRingSourceCutMarker
open LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (references : List input.Atom) (W D : Nat) (slot : Fin 4)

/-- Actual compiled markers are the deterministic molecular-cut markers at every frame slot,
including ring duplicates and arbitrary ordered inherited references. -/
theorem compiled_marker_eq_sourceCutMarker :
    let cursor := (rawStateFrames input single state target real unit targetUnit).frame.cursorAt slot
    (compiled input single state target real unit targetUnit references W D slot).markers =
      sourceCutMarker input.moleculeGraph cursor.occurrence.1.root
        (cutMap (rawStateDescriptorMap input state) target.1.address.length)
        (input.occurrenceCarrierNode single cursor.occurrence)
        (input.occurrenceCarrierNode single target) references W D := by
  dsimp only
  let frame := rawStateFrames input single state target real unit targetUnit
  rcases compiled_slot_eq_source input single state target real unit targetUnit references W D slot with
    ⟨source, mapEq, widthEq, depthEq, refsEq, focusEq, incomingEq, markerEq⟩ |
    ⟨source, refsEq, focusEq, incomingEq, markerEq⟩
  · obtain ⟨incoming, present, valueEq⟩ := Option.map_eq_some_iff.mp incomingEq
    have sourceEq := sourceCutMarker_eq_realArm input.moleculeGraph
      (frame.frame.cursorAt slot).occurrence.1.root source incoming present widthEq depthEq W D
    rw [mapEq, refsEq] at sourceEq
    rw [markerEq, focusEq, ← valueEq]
    exact sourceEq.symm
  · rw [markerEq, ← focusEq, ← incomingEq]
    exact (sourceCutMarker_ring input.moleculeGraph
      (frame.frame.cursorAt slot).occurrence.1.root
      (cutMap (rawStateDescriptorMap input state) target.1.address.length)
      source.valid references W D).symm

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCompiledSourceMarker

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCompiledSourceMarker.compiled_marker_eq_sourceCutMarker
