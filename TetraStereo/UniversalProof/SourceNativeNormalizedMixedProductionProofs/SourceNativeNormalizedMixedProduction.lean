import TetraStereo.UniversalProof.SourceNativeMixedJointAnnotationAuditProofs.SourceNativeMixedJointAnnotationAudit
import TetraStereo.UniversalProof.SourceNativeMixedScheduledReportProofs.SourceNativeMixedScheduledReport
import TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeRawAnnotationGuard

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.UniversalProof.SourceNativeNormalizedMixedProductionProofs.SourceNativeNormalizedMixedProduction

open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeMixedBondAuditProofs.SourceNativeMixedBondAudit
open TetraStereo.UniversalProof.SourceNativeMixedJointAnnotationAuditProofs.SourceNativeMixedJointAnnotationAudit
open TetraStereo.UniversalProof.SourceNativeMixedScheduledReportProofs.SourceNativeMixedScheduledReport

























structure NormalizedMixedRequest where
  originalRaw : RawMolecule
  normalized : CertifiedChemistryNormalizationResult
  normalizationEq : normalized.result = normalizeRawMolecule originalRaw
  source : AuthoritativeChemicalInput
  agreement : RawAnnotationAgreement normalized.result.parsed source
  carrierFuel : Nat
  ruleFuel : Nat

namespace NormalizedMixedRequest

theorem normalization_binding (request : NormalizedMixedRequest) :
    request.normalized.result = normalizeRawMolecule request.originalRaw :=
  request.normalizationEq

noncomputable def audit (request : NormalizedMixedRequest) :
    List (MixedJointAnnotationIssue request.source) :=
  mixedJointAnnotationAudit request.normalized.result.parsed request.source request.agreement
    request.normalized.writtenNeighborExact request.carrierFuel request.ruleFuel

noncomputable def report (request : NormalizedMixedRequest) :
    List (MixedScheduledRow request.source) :=
  mixedScheduledReport request.normalized.result.parsed request.source request.agreement
    request.normalized.writtenNeighborExact request.carrierFuel request.ruleFuel

noncomputable def guardedProduce (request : NormalizedMixedRequest) :
    Option (List (MixedScheduledRow request.source)) := by
  classical
  exact if request.audit = [] then some request.report else none

theorem guardedProduce_eq_some_iff (request : NormalizedMixedRequest)
    (rows : List (MixedScheduledRow request.source)) :
    request.guardedProduce = some rows ↔ request.audit = [] ∧ rows = request.report := by
  classical
  by_cases accepted : request.audit = []
  · simp [guardedProduce, accepted, eq_comm]
  · simp [guardedProduce, accepted]

theorem guardedProduce_eq_none_iff (request : NormalizedMixedRequest) :
    request.guardedProduce = none ↔ request.audit ≠ [] := by
  classical
  by_cases accepted : request.audit = [] <;> simp [guardedProduce, accepted]



theorem guardedProduce_exists_iff (request : NormalizedMixedRequest) :
    (∃ rows, request.guardedProduce = some rows) ↔
      (∀ annotation, annotation ∈ rawAtomAnnotations request.normalized.result.parsed →
        RawParityJointInterpretation request.normalized.result.parsed request.source
          request.agreement request.normalized.writtenNeighborExact request.carrierFuel
          request.ruleFuel annotation) ∧
      rawBondDirections request.normalized.result.parsed = [] ∧
      MixedBondAnnotationsAccepted request.source ∧
      (∀ atomIndex, atomIndex ∈ annotatedSourceAtoms request.source →
        AnnotatedCenterInterpreted request.normalized.result.parsed request.source
          request.agreement request.normalized.writtenNeighborExact request.carrierFuel
          request.ruleFuel atomIndex) ∧
      (∀ center, center ∈ request.source.aromaticCanonicalTetrahedralCenters →
        jointStatus request.normalized.result.parsed request.source request.agreement
          request.normalized.writtenNeighborExact request.carrierFuel request.ruleFuel
          (request.source.aromaticCanonicalFinalOccurrence request.carrierFuel center) ≠
            .conflict) := by
  constructor
  · rintro ⟨rows, produced⟩
    exact (mixedJointAnnotationAudit_eq_nil_iff _ _ _ _ _ _).mp
      ((guardedProduce_eq_some_iff request rows).mp produced).1
  · intro interpreted
    exact ⟨request.report, (guardedProduce_eq_some_iff request request.report).mpr
      ⟨(mixedJointAnnotationAudit_eq_nil_iff _ _ _ _ _ _).mpr interpreted, rfl⟩⟩

theorem guardedProduce_refuses_issue (request : NormalizedMixedRequest)
    (issue : MixedJointAnnotationIssue request.source) (present : issue ∈ request.audit) :
    request.guardedProduce = none := by
  apply (guardedProduce_eq_none_iff request).mpr
  intro empty
  rw [empty] at present
  exact List.not_mem_nil present

theorem guardedProduce_member_sound (request : NormalizedMixedRequest)
    (rows : List (MixedScheduledRow request.source))
    (produced : request.guardedProduce = some rows) (row : MixedScheduledRow request.source)
    (present : row ∈ rows) :
    MixedScheduledRowMeaning request.normalized.result.parsed request.source request.agreement
      request.normalized.writtenNeighborExact request.carrierFuel request.ruleFuel row := by
  rw [((guardedProduce_eq_some_iff request rows).mp produced).2] at present
  exact mixedScheduledReport_member_sound _ _ _ _ _ _ row present

theorem guardedProduce_raw_annotation_meaning (request : NormalizedMixedRequest)
    (rows : List (MixedScheduledRow request.source))
    (produced : request.guardedProduce = some rows) (annotation : RawAtomAnnotation)
    (present : annotation ∈ rawAtomAnnotations request.normalized.result.parsed) :
    ∃ candidate descriptor,
      (parserIndexViaConversion request.normalized.result.parsed request.source
        request.agreement.1 candidate).val = annotation.index ∧
      jointParserDescriptor? request.normalized.result.parsed request.source request.agreement
        request.normalized.writtenNeighborExact request.carrierFuel request.ruleFuel
        (request.source.aromaticCanonicalFinalOccurrence request.carrierFuel candidate) =
          some descriptor ∧
      CanonicalConstitutionParserRichDescriptor request.normalized.result.parsed request.source
        request.agreement request.normalized.writtenNeighborExact
        (request.source.aromaticCanonicalFinalOccurrence request.carrierFuel candidate)
        (jointView request.normalized.result.parsed request.source request.agreement
          request.normalized.writtenNeighborExact request.carrierFuel request.ruleFuel
          (request.source.aromaticCanonicalFinalOccurrence request.carrierFuel candidate))
        request.ruleFuel descriptor :=
  accepted_raw_parity_has_joint_meaning _ _ _ _ _ _
    ((guardedProduce_eq_some_iff request rows).mp produced).1 annotation present

theorem guardedProduce_annotated_center_meaning (request : NormalizedMixedRequest)
    (rows : List (MixedScheduledRow request.source))
    (produced : request.guardedProduce = some rows) (atomIndex : Nat)
    (present : atomIndex ∈ annotatedSourceAtoms request.source) :
    AnnotatedCenterInterpreted request.normalized.result.parsed request.source
      request.agreement request.normalized.writtenNeighborExact request.carrierFuel
      request.ruleFuel atomIndex :=
  ((guardedProduce_exists_iff request).mp ⟨rows, produced⟩).2.2.2.1 atomIndex present

theorem guardedProduce_refuses_conflict (request : NormalizedMixedRequest)
    (center : request.source.AromaticCanonicalTetrahedralCenter)
    (conflict : jointStatus request.normalized.result.parsed request.source request.agreement
      request.normalized.writtenNeighborExact request.carrierFuel request.ruleFuel
      (request.source.aromaticCanonicalFinalOccurrence request.carrierFuel center) = .conflict) :
    request.guardedProduce = none := by
  apply (guardedProduce_eq_none_iff request).mpr
  intro accepted
  have produced := (guardedProduce_eq_some_iff request request.report).mpr ⟨accepted, rfl⟩
  have noConflict := ((guardedProduce_exists_iff request).mp ⟨request.report, produced⟩).2.2.2.2
  exact noConflict center
    ((request.source.mem_aromaticCanonicalTetrahedralCenters_iff center).mpr center.2) conflict

end NormalizedMixedRequest

namespace ClosedNormalizedMixed

open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge.ConstitutionClosedWitness
open TetraStereo.UniversalProof.SourceNativeIndependentDrawingParserWitnessProofs.SourceNativeIndependentDrawingParserWitness
open TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeRawAnnotationGuard.ClosedRawCounterexample
  (annotatedCertifiedCF)

def actualRequest : NormalizedMixedRequest where
  originalRaw := annotatedRawCF
  normalized := annotatedCertifiedCF
  normalizationEq := rfl
  source := parserSource
  agreement := parserSource_annotationAgreement
  carrierFuel := 0
  ruleFuel := 2

theorem actual_normalization_binding :
    actualRequest.originalRaw = annotatedRawCF ∧
      actualRequest.normalized.result = normalizeRawMolecule annotatedRawCF ∧
      actualRequest.normalized.result.parsed = annotatedRawCF :=
  ⟨rfl, actualRequest.normalizationEq, rfl⟩

theorem actual_audit_nil : actualRequest.audit = [] :=
  ClosedJointAudit.parserSource_audit_pass

theorem actual_report_eq : actualRequest.report = ClosedMixedReport.actualMixedReport := rfl

theorem actual_production_accepted :
    actualRequest.guardedProduce = some ClosedMixedReport.actualMixedReport :=
  (NormalizedMixedRequest.guardedProduce_eq_some_iff _ _).mpr
    ⟨actual_audit_nil, actual_report_eq.symm⟩

theorem actual_production_R_row :
    ∃ rows, actualRequest.guardedProduce = some rows ∧
      ClosedMixedReport.actualMixedRow ∈ rows :=
  ⟨ClosedMixedReport.actualMixedReport, actual_production_accepted,
    ClosedMixedReport.actualMixedReport_row_mem⟩

theorem actual_production_center_count_one :
    (actualRequest.report.map MixedScheduledRow.center).count parserCenter = 1 := by
  rw [actual_report_eq]
  exact ClosedMixedReport.actualMixedReport_center_count_one

theorem actual_production_R_meaning :
    MixedScheduledRowMeaning actualRequest.normalized.result.parsed actualRequest.source
      actualRequest.agreement actualRequest.normalized.writtenNeighborExact
      actualRequest.carrierFuel actualRequest.ruleFuel ClosedMixedReport.actualMixedRow :=
  NormalizedMixedRequest.guardedProduce_member_sound actualRequest
    ClosedMixedReport.actualMixedReport actual_production_accepted ClosedMixedReport.actualMixedRow
    ClosedMixedReport.actualMixedReport_row_mem

/-- The SAME actual certified normalized raw input, now bound to the genuine complete solid
drawing source. Whole diagram equality is neither provided nor required. -/
def solidRequest : NormalizedMixedRequest where
  originalRaw := annotatedRawCF
  normalized := annotatedCertifiedCF
  normalizationEq := rfl
  source := newSource
  agreement := newSource_annotationAgreement
  carrierFuel := 0
  ruleFuel := 2

theorem solid_same_normalization :
    solidRequest.originalRaw = actualRequest.originalRaw ∧
      solidRequest.normalized = actualRequest.normalized ∧
      solidRequest.normalized.result = normalizeRawMolecule solidRequest.originalRaw :=
  ⟨rfl, rfl, solidRequest.normalizationEq⟩

theorem solid_production_refused : solidRequest.guardedProduce = none :=
  (NormalizedMixedRequest.guardedProduce_eq_none_iff solidRequest).mpr
    ClosedJointAudit.solid_audit_refused

end ClosedNormalizedMixed
end TetraStereo.UniversalProof.SourceNativeNormalizedMixedProductionProofs.SourceNativeNormalizedMixedProduction
