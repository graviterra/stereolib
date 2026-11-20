import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualSourceMarkerExecution
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualTerminalMarker
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Every actual frame slot, real or terminal ring duplicate, has its source molecular marker.
Source fields are fixed by the actual molecular carriers, candidate map and reference list.
No carrier correspondence, comparison success, acyclicity or real-slot premise is needed
by the combined theorem. The auxiliary state remains arbitrary supplied data.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedAllSlotSourceMarkers

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedVirtualTarget
open LocalizedChemicalRingJointMarkerRanking LocalizedChemicalRingJointMarkerKey
open LocalizedChemicalRingJointPreparedIndependentKeys
open LocalizedChemicalRingJointPreparedActualSourceMarkerExecution
open LocalizedChemicalRingJointPreparedActualTerminalMarker
open LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey
open LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal
open LocalizedChemicalRingSourceCutWindows

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (references : List input.Atom) (W D : Nat) (slot : Fin 4)

/-- The actual compiled marker of a ring-terminal slot has no ordinary-prior dependency. -/
theorem compiled_ringSlot_eq_source {distance : Nat}
    (ring : ((rawStateFrames input single state target real unit targetUnit).frame.cursorAt slot).occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.ringDuplicate distance) :
    let frame := rawStateFrames input single state target real unit targetUnit
    ∃ source : TerminalRingCut input.moleculeGraph (frame.frame.cursorAt slot).occurrence.1.root,
      source.references = references ∧
      source.focus.1 = input.occurrenceCarrierNode single (frame.frame.cursorAt slot).occurrence ∧
      source.incoming.1 = input.occurrenceCarrierNode single target ∧
      (compiled input single state target real unit targetUnit references W D slot).markers =
        assembleJointMarker W D references.length
          (references.map fun reference => if source.atom = reference then 1 else 0) [] := by
  let frame := rawStateFrames input single state target real unit targetUnit
  obtain ⟨source, refsEq, focusEq, incomingEq, markerEq⟩ :=
    ringArm_marker_eq_source input single (rawStateDescriptorMap input state) target
      (rootFallback input single state target real unit targetUnit) references
      ⟨target, none⟩ (frame.frame.cursorAt slot) (frame.childAt slot) ring (frame.stages slot).a
  refine ⟨source, refsEq, focusEq, incomingEq, ?_⟩
  have actual := congrArg (fun key : RefinedKey => (ofLex key).2)
    (refinedKey_eq_independent input single state target real unit targetUnit references W D slot)
  change (compiled input single state target real unit targetUnit references W D slot).markers =
    independentJointMarker input single state target real unit targetUnit references W D slot at actual
  have result := actual.trans (markerEq W D)
  rw [source.jointMarkerAt_eq_assemble_map, refsEq] at result
  exact result

/-- Complete real-or-terminal source refinement for every actual frame slot.
The candidate state is explicit; no generated-state chemical meaning is asserted here. -/
theorem compiled_slot_eq_source :
    let frame := rawStateFrames input single state target real unit targetUnit
    (∃ source : RealCutArm input.moleculeGraph (frame.frame.cursorAt slot).occurrence.1.root,
      source.descriptorMap = cutMap (rawStateDescriptorMap input state) target.1.address.length ∧
      source.W = allCutWidth input.moleculeGraph ∧ source.D = allCutDepth input.moleculeGraph ∧
      source.references = references ∧
      input.occurrenceCarrierNode single (frame.frame.cursorAt slot).occurrence = .real source.focus ∧
      source.incoming.map Subtype.val = some (input.occurrenceCarrierNode single target) ∧
      (compiled input single state target real unit targetUnit references W D slot).markers =
        source.markerAt W D references.length source.graph.root) ∨
    (∃ source : TerminalRingCut input.moleculeGraph (frame.frame.cursorAt slot).occurrence.1.root,
      source.references = references ∧
      source.focus.1 = input.occurrenceCarrierNode single (frame.frame.cursorAt slot).occurrence ∧
      source.incoming.1 = input.occurrenceCarrierNode single target ∧
      (compiled input single state target real unit targetUnit references W D slot).markers =
        assembleJointMarker W D references.length
          (references.map fun reference => if source.atom = reference then 1 else 0) []) := by
  rcases input.carrierOccurrence_provenance_simple_or_ring single
      ((rawStateFrames input single state target real unit targetUnit).frame.cursorAt slot).occurrence with
    realSlot | ⟨_distance, ring⟩
  · exact Or.inl (compiled_realSlot_eq_source input single state target real unit targetUnit
      references W D slot realSlot)
  · exact Or.inr (compiled_ringSlot_eq_source input single state target real unit targetUnit
      references W D slot ring)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedAllSlotSourceMarkers

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedAllSlotSourceMarkers.compiled_ringSlot_eq_source
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedAllSlotSourceMarkers.compiled_slot_eq_source
