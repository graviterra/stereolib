import TetraStereo.UniversalProof.SourceNativeMixedJointAgreementWitnessProofs.SourceNativeMixedJointAgreementWitness
import TetraStereo.UniversalProof.SourceNativeNormalizedMixedProductionProofs.SourceNativeNormalizedMixedProduction
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000





















namespace TetraStereo.UniversalProof.SourceNativeNormalizedMixedAgreementWitnessProofs.SourceNativeNormalizedMixedAgreementWitness

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
open TetraStereo.UniversalProof.SourceNativeMixedParserDrawingCausalModelProofs.SourceNativeMixedParserDrawingCausalModel
open TetraStereo.UniversalProof.SourceNativeMixedBondAuditProofs.SourceNativeMixedBondAudit
open TetraStereo.UniversalProof.SourceNativeMixedJointAnnotationAuditProofs.SourceNativeMixedJointAnnotationAudit
open TetraStereo.UniversalProof.SourceNativeMixedScheduledReportProofs.SourceNativeMixedScheduledReport
open TetraStereo.UniversalProof.SourceNativeMixedJointAgreementWitnessProofs.SourceNativeMixedJointAgreementWitness
  (agreeingSource agreeingCenter agreeingTarget agreeingSource_annotationAgreement
   agreeingSource_index_identity agreeingSource_parser_descriptor_R agreeingSource_drawing_R
   agreeingSource_preliminary_audit_clean)
open TetraStereo.UniversalProof.SourceNativeNormalizedMixedProductionProofs.SourceNativeNormalizedMixedProduction
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness
  (annotatedRawCF parserSource_writtenExact)
open TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeRawAnnotationGuard.ClosedRawCounterexample
  (annotatedCertifiedCF)

local instance : NeZero agreeingSource.molecule.atomCount := ⟨by change (5 : Nat) ≠ 0; decide⟩

/-- Candidate uniqueness is derived from this source's actual finite periodic-element boundary. -/
theorem actual_candidate_unique (center : agreeingSource.AromaticCanonicalTetrahedralCenter) :
    center = agreeingCenter := by
  have onlyCarbon : ∀ atom : agreeingSource.AromaticCanonicalAtom,
      agreeingSource.ConnectivityOnlyTetrahedralCenterAtom atom → atom.val = 0 := by
    unfold ConnectivityOnlyTetrahedralCenterAtom ConnectivityOnlyTetrahedralPeriodicElement
    decide +kernel
  have eligible := ((agreeingSource.mem_aromaticCanonicalTetrahedralCenterSet_iff center.1).mp
    center.2).1
  apply Subtype.ext
  apply Fin.ext
  exact onlyCarbon center.1 eligible

theorem actual_center_member : agreeingCenter ∈ agreeingSource.aromaticCanonicalTetrahedralCenters :=
  (agreeingSource.mem_aromaticCanonicalTetrahedralCenters_iff agreeingCenter).mpr agreeingCenter.2

theorem actual_bond_policy : MixedBondAnnotationsAccepted agreeingSource :=
  (mixedBondAuditIssues_eq_nil_iff agreeingSource).mp agreeingSource_preliminary_audit_clean

/-- Every actual listed bond is semantically backed and permitted; identical records are unique. -/
theorem actual_bonds_and_records :
    SourceBondAnnotationsAccepted agreeingSource ∧ SourceRecordsUnique agreeingSource :=
  actual_bond_policy

theorem actual_annotation_atoms :
    absoluteConfigurationAtoms agreeingSource = [0] ∧ wedgeEndpoints agreeingSource = [0] ∧
      annotatedSourceAtoms agreeingSource = [0, 0] := by
  decide +kernel


theorem actual_joint_channels_R :
    jointDrawingDescriptor? annotatedRawCF agreeingSource agreeingSource_annotationAgreement
        parserSource_writtenExact 0 2 agreeingTarget = some (.chiral RS.R) ∧
      jointParserDescriptor? annotatedRawCF agreeingSource agreeingSource_annotationAgreement
        parserSource_writtenExact 0 2 agreeingTarget = some (.chiral RS.R) :=
  ⟨agreeingSource_drawing_R _, agreeingSource_parser_descriptor_R _⟩

theorem actual_joint_status_R :
    jointStatus annotatedRawCF agreeingSource agreeingSource_annotationAgreement
      parserSource_writtenExact 0 2 agreeingTarget = .assigned (.chiral RS.R) := by
  rw [jointStatus_eq_fold, actual_joint_channels_R.1, actual_joint_channels_R.2]
  exact foldStatus_pair_some_same (Label := AromaticCanonicalAuxiliaryLabel) (.chiral RS.R)

theorem actual_raw_parity_interpreted :
    RawParityJointInterpretation annotatedRawCF agreeingSource agreeingSource_annotationAgreement
      parserSource_writtenExact 0 2 { index := 0, parity := .clockwise } := by
  refine ⟨agreeingCenter, agreeingSource_index_identity, ?_, .chiral RS.R,
    actual_joint_channels_R.2, ?_⟩
  · refine ⟨({ AtomSpec.aliphatic .C with tetrahedral? := some .clockwise } : AtomSpec), ?_, rfl⟩
    rw [agreeingSource_index_identity]
    exact SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence.ClosedParserWitness.parserSource_atom
  · exact (constitutionParserRichDescriptor?_eq_some_iff_canonical annotatedRawCF agreeingSource
      agreeingSource_annotationAgreement parserSource_writtenExact agreeingTarget
      (jointView annotatedRawCF agreeingSource agreeingSource_annotationAgreement
        parserSource_writtenExact 0 2 agreeingTarget) 2 (.chiral RS.R)).mp actual_joint_channels_R.2

theorem actual_annotated_zero_interpreted :
    AnnotatedCenterInterpreted annotatedRawCF agreeingSource agreeingSource_annotationAgreement
      parserSource_writtenExact 0 2 0 := by
  refine ⟨agreeingCenter, (mem_candidatesAt_iff agreeingSource 0 agreeingCenter).mpr
    ⟨actual_center_member, rfl⟩, Or.inr ?_, Or.inr ?_, .chiral RS.R, actual_joint_status_R⟩
  · change jointDrawingDescriptor? annotatedRawCF agreeingSource agreeingSource_annotationAgreement
      parserSource_writtenExact 0 2 agreeingTarget ≠ none
    rw [actual_joint_channels_R.1]
    simp
  · change jointParserDescriptor? annotatedRawCF agreeingSource agreeingSource_annotationAgreement
      parserSource_writtenExact 0 2 agreeingTarget ≠ none
    rw [actual_joint_channels_R.2]
    simp

/-- Every annotated center is covered, including both the raw configuration and wedge endpoint. -/
theorem actual_all_annotation_centers_interpreted (atomIndex : Nat)
    (present : atomIndex ∈ annotatedSourceAtoms agreeingSource) :
    AnnotatedCenterInterpreted annotatedRawCF agreeingSource agreeingSource_annotationAgreement
      parserSource_writtenExact 0 2 atomIndex := by
  rw [actual_annotation_atoms.2.2] at present
  have zero : atomIndex = 0 := by simpa using present
  subst atomIndex
  exact actual_annotated_zero_interpreted

/-- Candidate uniqueness covers ALL actual candidates, rather than only annotated candidates. -/
theorem actual_global_no_conflict (center : agreeingSource.AromaticCanonicalTetrahedralCenter) :
    jointStatus annotatedRawCF agreeingSource agreeingSource_annotationAgreement
      parserSource_writtenExact 0 2
      (agreeingSource.aromaticCanonicalFinalOccurrence 0 center) ≠ .conflict := by
  rw [actual_candidate_unique center]
  change jointStatus annotatedRawCF agreeingSource agreeingSource_annotationAgreement
    parserSource_writtenExact 0 2 agreeingTarget ≠ .conflict
  rw [actual_joint_status_R]
  intro conflict
  cases conflict

theorem actual_global_audit_nil :
    mixedJointAnnotationAudit annotatedRawCF agreeingSource agreeingSource_annotationAgreement
      parserSource_writtenExact 0 2 = [] := by
  rw [mixedJointAnnotationAudit_eq_nil_iff]
  refine ⟨?_, ClosedJointAudit.parserSource_no_raw_directions, actual_bond_policy,
    actual_all_annotation_centers_interpreted, ?_⟩
  · intro annotation present
    rw [ClosedJointAudit.parserSource_rawAtomAnnotations, List.mem_singleton] at present
    rw [present]
    exact actual_raw_parity_interpreted
  · intro center _present
    exact actual_global_no_conflict center

/-- Real certified normalization and actual record agreement, with no requested output label. -/
def actualRequest : NormalizedMixedRequest where
  originalRaw := annotatedRawCF
  normalized := annotatedCertifiedCF
  normalizationEq := rfl
  source := agreeingSource
  agreement := agreeingSource_annotationAgreement
  carrierFuel := 0
  ruleFuel := 2

theorem actual_normalization_binding :
    actualRequest.normalized.result = normalizeRawMolecule actualRequest.originalRaw ∧
      actualRequest.normalized.result.parsed = annotatedRawCF :=
  ⟨actualRequest.normalizationEq, rfl⟩

def actualRRow : MixedScheduledRow agreeingSource := ⟨agreeingCenter, some (.chiral RS.R)⟩

theorem actual_report_R_row : actualRRow ∈ actualRequest.report := by
  apply (mem_mixedScheduledReport_iff annotatedRawCF agreeingSource agreeingSource_annotationAgreement
    parserSource_writtenExact 0 2 actualRRow).mpr
  exact SourceNativeMixedJointAgreementWitnessProofs.SourceNativeMixedJointAgreementWitness.joint_scheduled_R.symm

theorem actual_normalized_production_accepted :
    actualRequest.guardedProduce = some actualRequest.report :=
  (NormalizedMixedRequest.guardedProduce_eq_some_iff actualRequest actualRequest.report).mpr
    ⟨actual_global_audit_nil, rfl⟩

theorem actual_normalized_R_row_count_one :
    (actualRequest.report.map MixedScheduledRow.center).count agreeingCenter = 1 :=
  mixedScheduledReport_center_count_one annotatedRawCF agreeingSource
    agreeingSource_annotationAgreement parserSource_writtenExact 0 2 agreeingCenter

theorem actual_normalized_R_row_meaning :
    MixedScheduledRowMeaning actualRequest.normalized.result.parsed actualRequest.source
      actualRequest.agreement actualRequest.normalized.writtenNeighborExact
      actualRequest.carrierFuel actualRequest.ruleFuel actualRRow :=
  NormalizedMixedRequest.guardedProduce_member_sound actualRequest actualRequest.report
    actual_normalized_production_accepted actualRRow actual_report_R_row


theorem actual_normalized_both_channel_R_witness :
    ∃ rows, actualRequest.guardedProduce = some rows ∧ actualRRow ∈ rows ∧
      (rows.map MixedScheduledRow.center).count agreeingCenter = 1 ∧
      MixedScheduledRowMeaning actualRequest.normalized.result.parsed actualRequest.source
        actualRequest.agreement actualRequest.normalized.writtenNeighborExact
        actualRequest.carrierFuel actualRequest.ruleFuel actualRRow ∧
      jointDrawingDescriptor? annotatedRawCF agreeingSource agreeingSource_annotationAgreement
        parserSource_writtenExact 0 2 agreeingTarget = some (.chiral RS.R) ∧
      jointParserDescriptor? annotatedRawCF agreeingSource agreeingSource_annotationAgreement
        parserSource_writtenExact 0 2 agreeingTarget = some (.chiral RS.R) :=
  ⟨actualRequest.report, actual_normalized_production_accepted, actual_report_R_row,
    actual_normalized_R_row_count_one, actual_normalized_R_row_meaning, actual_joint_channels_R⟩

end TetraStereo.UniversalProof.SourceNativeNormalizedMixedAgreementWitnessProofs.SourceNativeNormalizedMixedAgreementWitness
