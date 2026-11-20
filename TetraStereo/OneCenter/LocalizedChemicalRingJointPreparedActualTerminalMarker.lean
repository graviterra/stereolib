import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDeepCutPrior
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual terminal ring arms have exactly the source terminal marker. The terminal's
prior is immaterial; the ring atom still carries every matching inherited mark.
No supplied source isomorphism, successful comparison or desired label is assumed.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualTerminalMarker

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedCanonicalMarker LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedPromotedKey
open LocalizedChemicalRingJointMarkerKey
open LocalizedChemicalRingJointPreparedIndependentModelSourceTerminal

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)

/-- The actual ring-focus marker is the molecular terminal marker, including all ordered marks.
Both molecular endpoint identities are derived from the actual executable child relation. -/
theorem ringArm_marker_eq_source
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (fallback : CompleteLigandRule5Key) (references : List input.Atom)
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (retainedCarrierFuel input) → Option LocalizedAuxiliaryLabel}
    (parent cursor : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (member : cursor ∈ input.executableLocalizedRerootChildren parent)
    {distance : Nat}
    (ring : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.ringDuplicate distance)
    (actual : input.RuleMajorContextArm (retainedCarrierFuel input) stage read cursor) :
    ∃ source : TerminalRingCut input.moleculeGraph cursor.occurrence.1.root,
      source.references = references ∧
      source.focus.1 = input.occurrenceCarrierNode single cursor.occurrence ∧
      source.incoming.1 = input.occurrenceCarrierNode single parent.occurrence ∧
      ∀ W D,
        jointMarkerKey (ruleMajorTreeGraph actual.tree)
            (deepPrior descriptorMap target fallback actual.tree)
            (referenceMarks input references actual.tree) W D references.length
            (ruleMajorTreeGraph actual.tree).root =
          source.jointMarkerAt (fun _ => fallback) W D := by
  obtain ⟨_previous, path, atom, valid, focusEq, incomingEq, represented⟩ :=
    input.ringExecutableChild_retainedContextArmFaithful single parent cursor member actual ring
  let source : TerminalRingCut input.moleculeGraph cursor.occurrence.1.root :=
    ⟨path, atom, valid, references⟩
  let iso := (Classical.choice represented).symm
  have noChild : ∀ child, ¬ (ruleMajorTreeGraph actual.tree).child
      (ruleMajorTreeGraph actual.tree).root child := by
    intro child edge
    exact (iso.map_child _ _).mp edge
  have current : cursor.occurrence.1.node.current? = some atom := by
    have label := congrArg NodeLabel.atom? (input.occurrenceCarrierNode_label single cursor.occurrence)
    rw [focusEq] at label
    exact label.symm
  refine ⟨source, rfl, focusEq.symm, incomingEq.symm, ?_⟩
  intro W D
  rw [jointMarkerKey_eq_of_childList_eq_nil _ _ W D references.length
    (childList_eq_nil_of_no_child noChild)]
  rw [source.jointMarkerAt_eq_assemble_map]
  congr 1
  unfold referenceMarks
  apply List.map_congr_left
  intro reference _
  simp only [referenceMark, referenceBit, nodeSource_root, actual.sourceEq, current,
    Option.some.injEq]
  rfl

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualTerminalMarker

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualTerminalMarker.ringArm_marker_eq_source
