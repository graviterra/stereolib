import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualSourceMarker
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentKeys
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The actual compiled joint marker at a real frame slot is a source molecular-cut marker.
All successful build and structural correspondence facts are derived. The auxiliary state is
arbitrary and explicit; this does not yet prove the recursive state satisfies a source model.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualSourceMarkerExecution

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedVirtualTarget
open LocalizedChemicalRingJointMarkerRanking
open LocalizedChemicalRingJointPreparedIndependentKeys
open LocalizedChemicalRingJointPreparedActualSourceMarker
open LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey
open LocalizedChemicalRingSourceCutWindows

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (references : List input.Atom) (W D : Nat) (slot : Fin 4)

/-- Every actual real-focus slot has its molecular-cut marker, with its source fields fixed.
Neither a successful build nor carrier/reader/comparison correspondence is assumed. -/
theorem compiled_realSlot_eq_source
    (realSlot : ((rawStateFrames input single state target real unit targetUnit).frame.cursorAt slot).occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom) :
    let frame := rawStateFrames input single state target real unit targetUnit
    ∃ source : RealCutArm input.moleculeGraph (frame.frame.cursorAt slot).occurrence.1.root,
      source.descriptorMap = cutMap (rawStateDescriptorMap input state) target.1.address.length ∧
      source.W = allCutWidth input.moleculeGraph ∧ source.D = allCutDepth input.moleculeGraph ∧
      source.references = references ∧
      input.occurrenceCarrierNode single (frame.frame.cursorAt slot).occurrence = .real source.focus ∧
      source.incoming.map Subtype.val = some (input.occurrenceCarrierNode single target) ∧
      (compiled input single state target real unit targetUnit references W D slot).markers =
        source.markerAt W D references.length source.graph.root := by
  let frame := rawStateFrames input single state target real unit targetUnit
  obtain ⟨source, mapEq, widthEq, depthEq, refsEq, focusEq, incomingEq, markerEq⟩ :=
    realArm_marker_eq_source input single (rawStateDescriptorMap input state) target
      (rootFallback input single state target real unit targetUnit) references
      ⟨target, none⟩ (frame.frame.cursorAt slot) (frame.childAt slot) realSlot
      (frame.stages slot).a
  refine ⟨source, mapEq, widthEq, depthEq, refsEq, focusEq, incomingEq, ?_⟩
  have actual := congrArg (fun key : RefinedKey => (ofLex key).2)
    (refinedKey_eq_independent input single state target real unit targetUnit references W D slot)
  change (compiled input single state target real unit targetUnit references W D slot).markers =
    independentJointMarker input single state target real unit targetUnit references W D slot at actual
  exact actual.trans (markerEq W D)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualSourceMarkerExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualSourceMarkerExecution.compiled_realSlot_eq_source
