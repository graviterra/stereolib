import TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModelKernelCertificate

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
open TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
















/-! ## 1. Generic kernel facts about the two-element merge -/

/-- Within the two-element merge, two successes with the *same* label assign that label. -/
theorem mixedTwoElement_same_assigned :
    foldStatus ([some (.chiral .R), some (.chiral .R)] :
      List (Option AromaticCanonicalAuxiliaryLabel)) = .assigned (.chiral .R) := by decide

/-- Within the two-element merge, opposite uppercase labels are a typed conflict. -/
theorem mixedTwoElement_opposite_conflict :
    foldStatus ([some (.chiral .R), some (.chiral .S)] :
      List (Option AromaticCanonicalAuxiliaryLabel)) = .conflict := by decide

/-- Within the two-element merge, an upper/lower-case `chiral`/`pseudoasymmetric` mismatch is a
typed conflict; the local merge never prefers one channel over the other. -/
theorem mixedTwoElement_upperLowerCase_conflict :
    foldStatus ([some (.chiral .R), some (.pseudoasymmetric .r)] :
      List (Option AromaticCanonicalAuxiliaryLabel)) = .conflict := by decide

/-- Within the two-element merge, an absent channel beside a success assigns the success. -/
theorem mixedTwoElement_absent_success :
    foldStatus ([none, some (.chiral .R)] :
      List (Option AromaticCanonicalAuxiliaryLabel)) = .assigned (.chiral .R) := by decide

/-! ## 2. The actual closed CFClBrI source -/

namespace ClosedMixedWitness

open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge.ConstitutionClosedWitness
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel.ClosedConstitutionParserModel

/-- The pinned parser diagram of the closed source carries no coordinates. -/
theorem parserSource_diagram_atomPositions_none :
    annotatedRawCF.toDiagramConfiguration.atomPositions? = none := rfl

/-- No center of the closed source admits an extracted drawing frame. -/
theorem parserSource_extraction_none (center : Fin parserSource.molecule.atomCount) :
    extract? parserSource center = none :=
  extract?_eq_none_of_atomPositions_none parserSource annotatedRawCF.toDiagramConfiguration
    rfl parserSource_diagram_atomPositions_none center

/-- The drawing channel is absent at the closed source for every target and view. -/
theorem parserSource_drawing_absent {carrierFuel : Nat}
    (target : parserSource.AromaticCanonicalOccurrence carrierFuel)
    (view : parserSource.AromaticCanonicalDependencyView target) :
    occurrenceOrdinaryDescriptor? parserSource target view 2 = none :=
  occurrenceOrdinaryDescriptor?_eq_none_of_extraction_none parserSource parserSource_extraction_none
    target view 2

/-- The actual parser channel emits `R` for every restricted view at the actual closed target. -/
theorem parserSource_constitution_descriptor_R
    (view : parserSource.AromaticCanonicalDependencyView parserTarget) :
    constitutionParserRichDescriptor? annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact parserTarget view 2 = some (.chiral RS.R) :=
  parser_actual_constitution_descriptor_R view

/-- The actual recomputed joint status at the closed target is `assigned R`. -/
theorem parserSource_mixed_status_R
    (view : parserSource.AromaticCanonicalDependencyView parserTarget) :
    mixedChannelStatus annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact parserTarget view 2 = .assigned (.chiral RS.R) := by
  unfold mixedChannelStatus mixedChannelOutputs
  rw [parserSource_drawing_absent parserTarget view,
    parserSource_constitution_descriptor_R view]
  exact foldStatus_pair_none_some (Label := AromaticCanonicalAuxiliaryLabel) (.chiral RS.R)

/-- The actual joint evaluator emits `R` at the closed target for every restricted view. -/
theorem parserSource_mixed_joint_descriptor_R
    (view : parserSource.AromaticCanonicalDependencyView parserTarget) :
    mixedJointDescriptor? annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact parserTarget view 2 = some (.chiral RS.R) :=
  (mixedJointDescriptor?_eq_some_iff_status annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact parserTarget view 2
    (.chiral RS.R)).mpr (parserSource_mixed_status_R view)

/-- The named joint assignment, with each successful channel's own independent meaning. -/
theorem parserSource_mixed_output_meaning
    (view : parserSource.AromaticCanonicalDependencyView parserTarget) :
    MixedJointDescriptor annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact parserTarget view 2 (.chiral RS.R) :=
  (mixedJointDescriptor?_eq_some_iff_descriptor annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact parserTarget view 2
    (.chiral RS.R)).mp (parserSource_mixed_joint_descriptor_R view)





theorem parserSource_joint_success_not_resolved
    (view : parserSource.AromaticCanonicalDependencyView parserTarget) :
    mixedJointDescriptor? annotatedRawCF parserSource parserSource_annotationAgreement
        parserSource_writtenExact parserTarget view 2 = some (.chiral RS.R) ∧
      ¬ MixedChannelsResolved annotatedRawCF parserSource parserSource_annotationAgreement
        parserSource_writtenExact parserTarget view 2 := by
  refine ⟨parserSource_mixed_joint_descriptor_R view, ?_⟩
  intro resolved
  unfold MixedChannelsResolved at resolved
  exact resolved.1 (parserSource_drawing_absent parserTarget view)

/-! ## 3. The joint scheduler over the actual closed source -/

/-- The internally scheduled joint state of the actual closed source. -/
noncomputable def closedMixedScheduledState : parserSource.AromaticCanonicalAuxiliaryState 0 :=
  mixedScheduledState annotatedRawCF parserSource parserSource_annotationAgreement
    parserSource_writtenExact 0 2

theorem closedMixedScheduledState_cipModel :
    (parserSource.aromaticCanonicalOccurrenceSystem
      (mixedAuxiliarySemantics annotatedRawCF parserSource parserSource_annotationAgreement
        parserSource_writtenExact 0 2)).CIPModel closedMixedScheduledState :=
  mixedScheduledState_cipModel annotatedRawCF parserSource parserSource_annotationAgreement
    parserSource_writtenExact 0 2

/-- The actual internally constructed joint model state assigns `R` at the closed target, from
its own model equation; no old model state or label is supplied. -/
theorem parserSource_mixed_scheduled_R :
    closedMixedScheduledState parserTarget = some (.chiral RS.R) := by
  have evaluates := mixedModel_evaluates annotatedRawCF parserSource parserSource_annotationAgreement
    parserSource_writtenExact closedMixedScheduledState closedMixedScheduledState_cipModel parserTarget
  rw [← evaluates]
  exact (mixedJointDescriptor?_eq_some_iff_status annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact parserTarget
    (parserSource.aromaticCanonicalDependencyView closedMixedScheduledState parserTarget) 2
    (.chiral RS.R)).mpr (parserSource_mixed_status_R _)

/-- The scheduled joint model output carries the named joint assignment at the closed target. -/
theorem parserSource_mixed_scheduled_meaning :
    MixedJointDescriptor annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact parserTarget
      (parserSource.aromaticCanonicalDependencyView closedMixedScheduledState parserTarget) 2
      (.chiral RS.R) :=
  mixedModel_output_sound annotatedRawCF parserSource parserSource_annotationAgreement
    parserSource_writtenExact closedMixedScheduledState closedMixedScheduledState_cipModel
    parserTarget (.chiral RS.R) parserSource_mixed_scheduled_R

end ClosedMixedWitness

end TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModelKernelCertificate

/-! Trust checks for the actual generic causal/conflict proofs and all closed witnesses above. -/

assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel.mixedJointDescriptor?_eq_some_iff_status
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel.mixedJointDescriptor?_eq_none_iff_status
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel.mixedJointDescriptor?_eq_some_iff_descriptor
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel.mixedConflictDiagnostic_witness
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel.mixedConflictDiagnostic_nonassignment
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel.mixedChannelStatus_conflict_of_actual_disagreement
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel.mixedJointDescriptor?_eq_none_of_actual_disagreement
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel.mixedOutcome_iff
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel.existsUnique_mixedCIPModel
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel.mixedScheduledState_cipModel
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel.mixedModel_evaluates
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel.mixedModel_unique
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel.mixedModel_output_sound
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel.mixedModel_conflict_nonassignment
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel.mixedModel_finalCenter_conflict_nonassignment
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModelKernelCertificate.mixedTwoElement_same_assigned
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModelKernelCertificate.mixedTwoElement_opposite_conflict
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModelKernelCertificate.mixedTwoElement_upperLowerCase_conflict
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModelKernelCertificate.mixedTwoElement_absent_success
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModelKernelCertificate.ClosedMixedWitness.parserSource_diagram_atomPositions_none
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModelKernelCertificate.ClosedMixedWitness.parserSource_extraction_none
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModelKernelCertificate.ClosedMixedWitness.parserSource_drawing_absent
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModelKernelCertificate.ClosedMixedWitness.parserSource_constitution_descriptor_R
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModelKernelCertificate.ClosedMixedWitness.parserSource_mixed_status_R
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModelKernelCertificate.ClosedMixedWitness.parserSource_mixed_joint_descriptor_R
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModelKernelCertificate.ClosedMixedWitness.parserSource_mixed_output_meaning
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModelKernelCertificate.ClosedMixedWitness.parserSource_joint_success_not_resolved
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModelKernelCertificate.ClosedMixedWitness.closedMixedScheduledState_cipModel
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModelKernelCertificate.ClosedMixedWitness.parserSource_mixed_scheduled_R
assert_kernel_only TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModelKernelCertificate.ClosedMixedWitness.parserSource_mixed_scheduled_meaning
