import TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel
import TetraStereo.UniversalProof.SourceNativeMixedJointConflictWitnessProofs.SourceNativeMixedJointConflictWitness

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.SourceNativeMixedScheduledReportProofs.SourceNativeMixedScheduledReport

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel
























structure MixedScheduledRow (source : AuthoritativeChemicalInput) where
  center : source.AromaticCanonicalTetrahedralCenter
  label : Option AromaticCanonicalAuxiliaryLabel
  deriving DecidableEq

variable (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
  (agreement : RawAnnotationAgreement molecule source)
  (writtenExact : molecule.WrittenNeighborExact) (carrierFuel ruleFuel : Nat)

/-- The internally scheduled joint state, read at the candidate's actual final occurrence. -/
noncomputable def mixedScheduledLabel (center : source.AromaticCanonicalTetrahedralCenter) :
    Option AromaticCanonicalAuxiliaryLabel :=
  mixedScheduledState molecule source agreement writtenExact carrierFuel ruleFuel
    (source.aromaticCanonicalFinalOccurrence carrierFuel center)

/-- The own model's dependency view at the candidate's actual final occurrence. -/
noncomputable def mixedScheduledView (center : source.AromaticCanonicalTetrahedralCenter) :
    source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) :=
  source.aromaticCanonicalDependencyView
    (mixedScheduledState molecule source agreement writtenExact carrierFuel ruleFuel)
    (source.aromaticCanonicalFinalOccurrence carrierFuel center)

/-- The internally scheduled label is the actual joint evaluator at the same final target and view. -/
theorem mixedScheduledLabel_eq_actual_descriptor
    (center : source.AromaticCanonicalTetrahedralCenter) :
    mixedScheduledLabel molecule source agreement writtenExact carrierFuel ruleFuel center =
      mixedJointDescriptor? molecule source agreement writtenExact
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)
        (mixedScheduledView molecule source agreement writtenExact carrierFuel ruleFuel center)
        ruleFuel :=
  (mixedModel_evaluates molecule source agreement writtenExact
    (mixedScheduledState molecule source agreement writtenExact carrierFuel ruleFuel)
    (mixedScheduledState_cipModel molecule source agreement writtenExact carrierFuel ruleFuel)
    (source.aromaticCanonicalFinalOccurrence carrierFuel center)).symm

/-- The two actual channel results at the candidate's final occurrence under the own view. -/
noncomputable def mixedScheduledOutputs (center : source.AromaticCanonicalTetrahedralCenter) :
    List (Option AromaticCanonicalAuxiliaryLabel) :=
  mixedChannelOutputs molecule source agreement writtenExact
    (source.aromaticCanonicalFinalOccurrence carrierFuel center)
    (mixedScheduledView molecule source agreement writtenExact carrierFuel ruleFuel center) ruleFuel


noncomputable def mixedScheduledStatus (center : source.AromaticCanonicalTetrahedralCenter) :
    ChannelStatus AromaticCanonicalAuxiliaryLabel :=
  foldStatus (mixedScheduledOutputs molecule source agreement writtenExact carrierFuel ruleFuel
    center)

theorem mixedScheduledLabel_eq_some_iff_status_assigned
    (center : source.AromaticCanonicalTetrahedralCenter)
    (label : AromaticCanonicalAuxiliaryLabel) :
    mixedScheduledLabel molecule source agreement writtenExact carrierFuel ruleFuel center =
        some label ↔
      mixedScheduledStatus molecule source agreement writtenExact carrierFuel ruleFuel center =
        .assigned label := by
  rw [mixedScheduledLabel_eq_actual_descriptor]
  exact mixedJointDescriptor?_eq_some_iff_status molecule source agreement writtenExact
    (source.aromaticCanonicalFinalOccurrence carrierFuel center)
    (mixedScheduledView molecule source agreement writtenExact carrierFuel ruleFuel center) ruleFuel
    label

/-- Exact absence: the row label is `none` precisely on all-absent **or** conflict. Conflict is a
distinct recomputable status, never a nonstereogenicity claim. -/
theorem mixedScheduledLabel_eq_none_iff_status
    (center : source.AromaticCanonicalTetrahedralCenter) :
    mixedScheduledLabel molecule source agreement writtenExact carrierFuel ruleFuel center = none ↔
      (mixedScheduledStatus molecule source agreement writtenExact carrierFuel ruleFuel center =
          .unassigned ∨
        mixedScheduledStatus molecule source agreement writtenExact carrierFuel ruleFuel center =
          .conflict) := by
  rw [mixedScheduledLabel_eq_actual_descriptor]
  exact mixedJointDescriptor?_eq_none_iff_status molecule source agreement writtenExact
    (source.aromaticCanonicalFinalOccurrence carrierFuel center)
    (mixedScheduledView molecule source agreement writtenExact carrierFuel ruleFuel center) ruleFuel

noncomputable def mixedScheduledReport : List (MixedScheduledRow source) :=
  source.aromaticCanonicalTetrahedralCenters.map fun center =>
    { center, label := mixedScheduledLabel molecule source agreement writtenExact carrierFuel
        ruleFuel center }

theorem mem_mixedScheduledReport_iff (row : MixedScheduledRow source) :
    row ∈ mixedScheduledReport molecule source agreement writtenExact carrierFuel ruleFuel ↔
      row.label = mixedScheduledLabel molecule source agreement writtenExact carrierFuel ruleFuel
        row.center := by
  constructor
  · intro present
    rcases List.mem_map.mp present with ⟨center, _, same⟩
    subst row
    rfl
  · intro same
    apply List.mem_map.mpr
    refine ⟨row.center,
      (source.mem_aromaticCanonicalTetrahedralCenters_iff row.center).mpr row.center.property, ?_⟩
    cases row with
    | mk center label =>
        change label = mixedScheduledLabel molecule source agreement writtenExact carrierFuel
          ruleFuel center at same
        subst label
        rfl

/-- Row membership is exactly the own model's assignment at the candidate's final occurrence. -/
theorem mem_mixedScheduledReport_iff_own_model_assigned (row : MixedScheduledRow source) :
    row ∈ mixedScheduledReport molecule source agreement writtenExact carrierFuel ruleFuel ↔
      mixedScheduledState molecule source agreement writtenExact carrierFuel ruleFuel
        (source.aromaticCanonicalFinalOccurrence carrierFuel row.center) = row.label := by
  rw [mem_mixedScheduledReport_iff]
  exact eq_comm

theorem mixedScheduledReport_centers :
    (mixedScheduledReport molecule source agreement writtenExact carrierFuel ruleFuel).map
      MixedScheduledRow.center = source.aromaticCanonicalTetrahedralCenters := by
  unfold mixedScheduledReport
  rw [List.map_map]
  change source.aromaticCanonicalTetrahedralCenters.map id =
    source.aromaticCanonicalTetrahedralCenters
  exact List.map_id _

theorem mixedScheduledReport_center_count_one
    (center : source.AromaticCanonicalTetrahedralCenter) :
    ((mixedScheduledReport molecule source agreement writtenExact carrierFuel ruleFuel).map
      MixedScheduledRow.center).count center = 1 := by
  rw [mixedScheduledReport_centers]
  exact List.count_eq_one_of_mem source.aromaticCanonicalTetrahedralCenters_nodup
    ((source.mem_aromaticCanonicalTetrahedralCenters_iff center).mpr center.property)

/-- Genuine joint-model binding and independent meaning for every assigned row label. Absence is
retained by the model binding; no chemical completeness assertion is made. -/
def MixedScheduledRowMeaning (row : MixedScheduledRow source) : Prop :=
  ∃ state : source.AromaticCanonicalAuxiliaryState carrierFuel,
    (source.aromaticCanonicalOccurrenceSystem
      (mixedAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)).CIPModel
        state ∧
      state (source.aromaticCanonicalFinalOccurrence carrierFuel row.center) = row.label ∧
        ∀ label, row.label = some label →
          MixedJointDescriptor molecule source agreement writtenExact
            (source.aromaticCanonicalFinalOccurrence carrierFuel row.center)
            (source.aromaticCanonicalDependencyView state
              (source.aromaticCanonicalFinalOccurrence carrierFuel row.center)) ruleFuel label

/-- Every emitted row carries the own mixed output meaning, via `mixedModel_output_sound`. -/
theorem mixedScheduledReport_member_sound (row : MixedScheduledRow source)
    (present : row ∈ mixedScheduledReport molecule source agreement writtenExact carrierFuel
      ruleFuel) :
    MixedScheduledRowMeaning molecule source agreement writtenExact carrierFuel ruleFuel row := by
  have emitted := (mem_mixedScheduledReport_iff molecule source agreement writtenExact
    carrierFuel ruleFuel row).mp present
  refine ⟨mixedScheduledState molecule source agreement writtenExact carrierFuel ruleFuel,
    mixedScheduledState_cipModel molecule source agreement writtenExact carrierFuel ruleFuel,
    emitted.symm, ?_⟩
  intro label assigned
  exact mixedModel_output_sound molecule source agreement writtenExact
    (mixedScheduledState molecule source agreement writtenExact carrierFuel ruleFuel)
    (mixedScheduledState_cipModel molecule source agreement writtenExact carrierFuel ruleFuel)
    (source.aromaticCanonicalFinalOccurrence carrierFuel row.center) label
    (emitted.symm.trans assigned)

/-- The per-candidate retained conflict: a typed disagreement of the two actual channels under the
same joint dependency view. It is not a claim of chemical nonstereogenicity. -/
noncomputable def MixedScheduledConflict
    (center : source.AromaticCanonicalTetrahedralCenter) : Prop :=
  mixedScheduledStatus molecule source agreement writtenExact carrierFuel ruleFuel center = .conflict

/-- A conflict exposes two actual successful channels carrying different labels. -/
theorem mixedScheduledConflict_witness
    (center : source.AromaticCanonicalTetrahedralCenter)
    (conflict : MixedScheduledConflict molecule source agreement writtenExact carrierFuel ruleFuel
      center) :
    ∃ first ∈ mixedScheduledOutputs molecule source agreement writtenExact carrierFuel ruleFuel center,
      ∃ second ∈ mixedScheduledOutputs molecule source agreement writtenExact carrierFuel ruleFuel
          center,
        ∃ firstLabel secondLabel,
          first = some firstLabel ∧ second = some secondLabel ∧ firstLabel ≠ secondLabel := by
  have classified := foldStatus_classifies
    (mixedScheduledOutputs molecule source agreement writtenExact carrierFuel ruleFuel center)
  unfold MixedScheduledConflict mixedScheduledStatus at conflict
  rw [conflict] at classified
  exact classified

/-- A conflict row is nonassignment: the diagnostic never becomes a label. -/
theorem mixedScheduledConflict_nonassignment
    (center : source.AromaticCanonicalTetrahedralCenter)
    (conflict : MixedScheduledConflict molecule source agreement writtenExact carrierFuel ruleFuel
      center) :
    mixedScheduledLabel molecule source agreement writtenExact carrierFuel ruleFuel center = none := by
  rw [mixedScheduledLabel_eq_none_iff_status]
  exact Or.inr (by simpa [MixedScheduledConflict] using conflict)

/-! ## Closed coordinate-free actual CF source: one assigned `R` row -/

namespace ClosedMixedReport

open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge.ConstitutionClosedWitness
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel.ClosedConstitutionParserModel

noncomputable def closedCFScheduledState : parserSource.AromaticCanonicalAuxiliaryState 0 :=
  mixedScheduledState annotatedRawCF parserSource parserSource_annotationAgreement
    parserSource_writtenExact 0 2

noncomputable def closedCFView : parserSource.AromaticCanonicalDependencyView parserTarget :=
  parserSource.aromaticCanonicalDependencyView closedCFScheduledState parserTarget

theorem closedCF_drawing_absent {carrierFuel : Nat}
    (target : parserSource.AromaticCanonicalOccurrence carrierFuel)
    (view : parserSource.AromaticCanonicalDependencyView target) :
    occurrenceOrdinaryDescriptor? parserSource target view 2 = none :=
  occurrenceOrdinaryDescriptor?_eq_none_of_extraction_none parserSource
    (fun center => extract?_eq_none_of_atomPositions_none parserSource
      annotatedRawCF.toDiagramConfiguration rfl rfl center) target view 2

theorem closedCF_mixed_status_R (view : parserSource.AromaticCanonicalDependencyView parserTarget) :
    mixedChannelStatus annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact parserTarget view 2 = .assigned (.chiral RS.R) := by
  unfold mixedChannelStatus mixedChannelOutputs
  rw [closedCF_drawing_absent parserTarget view, parser_actual_constitution_descriptor_R view]
  exact foldStatus_pair_none_some (Label := AromaticCanonicalAuxiliaryLabel) (.chiral RS.R)

/-- The own scheduled CF model state assigns `R` at the actual closed target, from its own model
equation; no old model state or label is supplied. -/
theorem closedCF_mixed_scheduled_R :
    closedCFScheduledState parserTarget = some (.chiral RS.R) := by
  have evaluates := mixedModel_evaluates annotatedRawCF parserSource parserSource_annotationAgreement
    parserSource_writtenExact closedCFScheduledState
    (mixedScheduledState_cipModel annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact 0 2) parserTarget
  rw [← evaluates]
  exact (mixedJointDescriptor?_eq_some_iff_status annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact parserTarget closedCFView 2
    (.chiral RS.R)).mpr (closedCF_mixed_status_R _)

noncomputable def actualMixedReport : List (MixedScheduledRow parserSource) :=
  mixedScheduledReport annotatedRawCF parserSource parserSource_annotationAgreement
    parserSource_writtenExact 0 2

def actualMixedRow : MixedScheduledRow parserSource :=
  ⟨parserCenter, some (.chiral RS.R)⟩

theorem actualMixedReport_row_mem : actualMixedRow ∈ actualMixedReport := by
  apply (mem_mixedScheduledReport_iff annotatedRawCF parserSource parserSource_annotationAgreement
    parserSource_writtenExact 0 2 actualMixedRow).mpr
  show some (.chiral RS.R) = closedCFScheduledState parserTarget
  exact closedCF_mixed_scheduled_R.symm

/-- Every row at the actual center is the single assigned `R` row. -/
theorem actualMixedReport_row_unique (row : MixedScheduledRow parserSource)
    (present : row ∈ actualMixedReport) (centerEq : row.center = parserCenter) :
    row = actualMixedRow := by
  have labelEq := (mem_mixedScheduledReport_iff annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact 0 2 row).mp present
  have labelR : row.label = some (.chiral RS.R) := by
    rw [labelEq, centerEq]
    exact closedCF_mixed_scheduled_R
  cases row with
  | mk rowCenter rowLabel =>
      simp only at centerEq labelR
      subst rowCenter
      subst rowLabel
      rfl

theorem actualMixedReport_center_count_one :
    (actualMixedReport.map MixedScheduledRow.center).count parserCenter = 1 :=
  mixedScheduledReport_center_count_one annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact 0 2 parserCenter

theorem actualMixedRow_meaning :
    MixedScheduledRowMeaning annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact 0 2 actualMixedRow :=
  mixedScheduledReport_member_sound annotatedRawCF parserSource parserSource_annotationAgreement
    parserSource_writtenExact 0 2 actualMixedRow actualMixedReport_row_mem

/-- A row is emitted while local channel readiness is false: emission is not admission. The drawing
channel is absent at the coordinate-free source. -/
theorem actualMixedReport_row_not_resolved :
    actualMixedRow ∈ actualMixedReport ∧
      ¬ MixedChannelsResolved annotatedRawCF parserSource parserSource_annotationAgreement
        parserSource_writtenExact parserTarget closedCFView 2 := by
  refine ⟨actualMixedReport_row_mem, ?_⟩
  intro resolved
  unfold MixedChannelsResolved at resolved
  exact resolved.1 (closedCF_drawing_absent parserTarget closedCFView)

end ClosedMixedReport

/-! ## Contradictory solid-wedge actual source: no assigned row, retained conflict -/

namespace ContradictoryMixedReport

open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness
open TetraStereo.UniversalProof.SourceNativeIndependentDrawingParserWitnessProofs.SourceNativeIndependentDrawingParserWitness
open TetraStereo.UniversalProof.SourceNativeMixedJointConflictWitnessProofs.SourceNativeMixedJointConflictWitness

noncomputable def contradictoryReport : List (MixedScheduledRow newSource) :=
  mixedScheduledReport annotatedRawCF newSource newSource_annotationAgreement
    parserSource_writtenExact 0 2

theorem contradictory_target_label_none :
    mixedScheduledLabel annotatedRawCF newSource newSource_annotationAgreement
      parserSource_writtenExact 0 2 newCenter = none := by
  show jointScheduledState newTarget = none
  exact joint_scheduled_target_absent

/-- The contradictory source retains its typed conflict at the actual target. -/
theorem contradictory_status_conflict :
    mixedScheduledStatus annotatedRawCF newSource newSource_annotationAgreement
      parserSource_writtenExact 0 2 newCenter = .conflict := by
  show mixedChannelStatus annotatedRawCF newSource newSource_annotationAgreement
    parserSource_writtenExact newTarget jointView 2 = .conflict
  exact retained_joint_status_conflict

theorem contradictory_report_nonempty :
    ∃ row ∈ contradictoryReport, row.center = newCenter :=
  ⟨⟨newCenter, none⟩,
    (mem_mixedScheduledReport_iff annotatedRawCF newSource newSource_annotationAgreement
      parserSource_writtenExact 0 2 ⟨newCenter, none⟩).mpr contradictory_target_label_none.symm,
    rfl⟩

/-- Every retained row at the actual target is unassigned: the contradictory source emits no
assigned row there, and no transaction is admitted merely because the report has rows. -/
theorem contradictory_no_assigned_row (row : MixedScheduledRow newSource)
    (present : row ∈ contradictoryReport) (centerEq : row.center = newCenter) :
    row.label = none := by
  have labelEq := (mem_mixedScheduledReport_iff annotatedRawCF newSource
    newSource_annotationAgreement parserSource_writtenExact 0 2 row).mp present
  rw [labelEq, centerEq]
  exact contradictory_target_label_none

end ContradictoryMixedReport

end TetraStereo.UniversalProof.SourceNativeMixedScheduledReportProofs.SourceNativeMixedScheduledReport
