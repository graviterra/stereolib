import TetraStereo.UniversalProof.SourceNativeIndependentDrawingParserWitnessProofs.SourceNativeIndependentDrawingParserWitness
import TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SourceNativeMixedJointConflictWitnessProofs.SourceNativeMixedJointConflictWitness

open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
open SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness
open SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence.ClosedParserWitness
open SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open SourceNativeIndependentDrawingParserWitnessProofs.SourceNativeIndependentDrawingParserWitness
open SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel





















noncomputable def jointSemantics : newSource.AromaticCanonicalRuleSemantics 0 :=
  mixedAuxiliarySemantics annotatedRawCF newSource newSource_annotationAgreement
    parserSource_writtenExact 0 2

noncomputable def jointScheduledState : newSource.AromaticCanonicalAuxiliaryState 0 :=
  mixedScheduledState annotatedRawCF newSource newSource_annotationAgreement
    parserSource_writtenExact 0 2

noncomputable def jointView : newSource.AromaticCanonicalDependencyView newTarget :=
  newSource.aromaticCanonicalDependencyView jointScheduledState newTarget

theorem joint_model_exists_unique :
    ∃! state, (newSource.aromaticCanonicalOccurrenceSystem jointSemantics).CIPModel state :=
  existsUnique_mixedCIPModel annotatedRawCF newSource newSource_annotationAgreement
    parserSource_writtenExact 0 2

theorem jointScheduledState_cipModel :
    (newSource.aromaticCanonicalOccurrenceSystem jointSemantics).CIPModel jointScheduledState :=
  mixedScheduledState_cipModel annotatedRawCF newSource newSource_annotationAgreement
    parserSource_writtenExact 0 2

theorem joint_model_unique (state : newSource.AromaticCanonicalAuxiliaryState 0)
    (model : (newSource.aromaticCanonicalOccurrenceSystem jointSemantics).CIPModel state) :
    state = jointScheduledState :=
  mixedModel_unique annotatedRawCF newSource newSource_annotationAgreement
    parserSource_writtenExact 0 2 state model

theorem parser_R_at_joint_view :
    constitutionParserRichDescriptor? annotatedRawCF newSource newSource_annotationAgreement
      parserSource_writtenExact newTarget jointView 2 = some (.chiral RS.R) :=
  newSource_parser_descriptor_R jointView

theorem drawing_S_at_joint_view :
    occurrenceOrdinaryDescriptor? newSource newTarget jointView 2 = some (.chiral RS.S) :=
  newSource_drawing_S jointView

theorem both_independent_meanings_at_joint_view :
    CanonicalConstitutionParserRichDescriptor annotatedRawCF newSource newSource_annotationAgreement
        parserSource_writtenExact newTarget jointView 2 (.chiral RS.R) ∧
      CanonicalOccurrenceOrdinaryDescriptor newSource newTarget jointView 2 (.chiral RS.S) :=
  ⟨(constitutionParserRichDescriptor?_eq_some_iff_canonical annotatedRawCF newSource
      newSource_annotationAgreement parserSource_writtenExact newTarget jointView 2
      (.chiral RS.R)).mp parser_R_at_joint_view,
   (occurrenceOrdinaryDescriptor?_eq_some_iff_canonical newSource newTarget jointView 2
      (.chiral RS.S)).mp drawing_S_at_joint_view⟩

theorem localMixedChannelsResolved :
    MixedChannelsResolved annotatedRawCF newSource newSource_annotationAgreement
      parserSource_writtenExact newTarget jointView 2 := by
  unfold MixedChannelsResolved
  rw [drawing_S_at_joint_view, parser_R_at_joint_view]
  simp

theorem retained_joint_status_conflict :
    mixedChannelStatus annotatedRawCF newSource newSource_annotationAgreement
      parserSource_writtenExact newTarget jointView 2 = .conflict :=
  mixedChannelStatus_conflict_of_actual_disagreement annotatedRawCF newSource
    newSource_annotationAgreement parserSource_writtenExact newTarget jointView 2
    (.chiral RS.S) (.chiral RS.R) drawing_S_at_joint_view parser_R_at_joint_view (by decide)

theorem joint_descriptor_absent :
    mixedJointDescriptor? annotatedRawCF newSource newSource_annotationAgreement
      parserSource_writtenExact newTarget jointView 2 = none :=
  mixedConflictDiagnostic_nonassignment annotatedRawCF newSource newSource_annotationAgreement
    parserSource_writtenExact newTarget jointView 2 retained_joint_status_conflict

theorem joint_scheduled_target_absent : jointScheduledState newTarget = none :=
  (mixedModel_conflict_nonassignment annotatedRawCF newSource newSource_annotationAgreement
    parserSource_writtenExact jointScheduledState jointScheduledState_cipModel newTarget
    (.chiral RS.S) (.chiral RS.R) drawing_S_at_joint_view parser_R_at_joint_view (by decide)).1

/-- Inhabited local readiness with a retained conflict and absent joint model output. -/
theorem resolved_channels_conflict_and_nonassignment :
    MixedChannelsResolved annotatedRawCF newSource newSource_annotationAgreement
        parserSource_writtenExact newTarget jointView 2 ∧
      MixedConflictDiagnostic annotatedRawCF newSource newSource_annotationAgreement
        parserSource_writtenExact newTarget jointView 2 ∧
      jointScheduledState newTarget = none :=
  ⟨localMixedChannelsResolved, retained_joint_status_conflict, joint_scheduled_target_absent⟩

/-- Every joint model of this actual source has the same conflicting channels and nonassignment.
The model hypothesis is inhabited by `jointScheduledState_cipModel` above. -/
theorem every_joint_model_retains_conflict (state : newSource.AromaticCanonicalAuxiliaryState 0)
    (model : (newSource.aromaticCanonicalOccurrenceSystem jointSemantics).CIPModel state) :
    state newTarget = none ∧
      MixedConflictDiagnostic annotatedRawCF newSource newSource_annotationAgreement
        parserSource_writtenExact newTarget
        (newSource.aromaticCanonicalDependencyView state newTarget) 2 :=
  mixedModel_conflict_nonassignment annotatedRawCF newSource newSource_annotationAgreement
    parserSource_writtenExact state model newTarget (.chiral RS.S) (.chiral RS.R)
    (newSource_drawing_S _) (newSource_parser_descriptor_R _) (by decide)

end TetraStereo.UniversalProof.SourceNativeMixedJointConflictWitnessProofs.SourceNativeMixedJointConflictWitness
