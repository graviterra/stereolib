import TetraStereo.UniversalProof.SourceNativeScheduledParserReportProofs.SourceNativeInterpretedParserAudit
import TetraStereo.UniversalProof.SourceNativeScheduledParserReportProofs.SourceNativeScheduledParserReport
import TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeRawAnnotationGuard

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.UniversalProof.SourceNativeScheduledParserReportProofs.SourceNativeNormalizedParserProduction

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserCausalModel
open TetraStereo.UniversalProof.SourceNativeScheduledParserReportProofs.SourceNativeInterpretedParserAudit
open TetraStereo.UniversalProof.SourceNativeScheduledParserReportProofs.SourceNativeScheduledParserReport























structure NormalizedParserRequest where
  normalized : CertifiedChemistryNormalizationResult
  source : AuthoritativeChemicalInput
  agreement : normalized.result.parsed.AuthoritativeStructureAgreement source
  writtenExact : normalized.result.parsed.WrittenNeighborExact
  carrierFuel : Nat
  ruleFuel : Nat

namespace NormalizedParserRequest

noncomputable def audit (request : NormalizedParserRequest) : List ParserAnnotationAuditIssue :=
  parserAnnotationAudit request.normalized.result.parsed request.source request.agreement
    request.writtenExact request.carrierFuel request.ruleFuel

noncomputable def report (request : NormalizedParserRequest) :
    List (ScheduledParserRow request.source) :=
  scheduledParserReport request.normalized.result.parsed request.source request.agreement
    request.writtenExact request.carrierFuel request.ruleFuel

noncomputable def guardedProduce (request : NormalizedParserRequest) :
    Option (List (ScheduledParserRow request.source)) := by
  classical
  exact if request.audit = [] then some request.report else none

theorem guardedProduce_eq_some_iff (request : NormalizedParserRequest)
    (rows : List (ScheduledParserRow request.source)) :
    request.guardedProduce = some rows ↔ request.audit = [] ∧ rows = request.report := by
  classical
  by_cases accepted : request.audit = []
  · simp [guardedProduce, accepted, eq_comm]
  · simp [guardedProduce, accepted]

theorem guardedProduce_eq_none_iff (request : NormalizedParserRequest) :
    request.guardedProduce = none ↔ request.audit ≠ [] := by
  classical
  by_cases accepted : request.audit = [] <;> simp [guardedProduce, accepted]



theorem guardedProduce_exists_iff (request : NormalizedParserRequest) :
    (∃ rows, request.guardedProduce = some rows) ↔
      (∀ annotation, annotation ∈ rawAtomAnnotations request.normalized.result.parsed →
        RawAtomAnnotationInterpretation request.normalized.result.parsed request.source
          request.agreement request.writtenExact request.carrierFuel request.ruleFuel annotation) ∧
        rawBondDirections request.normalized.result.parsed = [] := by
  constructor
  · rintro ⟨rows, produced⟩
    exact (parserAnnotationAudit_eq_nil_iff _ _ _ _ _ _).mp
      ((guardedProduce_eq_some_iff request rows).mp produced).1
  · intro interpreted
    exact ⟨request.report, (guardedProduce_eq_some_iff request request.report).mpr
      ⟨(parserAnnotationAudit_eq_nil_iff _ _ _ _ _ _).mpr interpreted, rfl⟩⟩

theorem guardedProduce_refuses_issue (request : NormalizedParserRequest)
    (issue : ParserAnnotationAuditIssue) (present : issue ∈ request.audit) :
    request.guardedProduce = none := by
  apply (guardedProduce_eq_none_iff request).mpr
  intro empty
  rw [empty] at present
  exact List.not_mem_nil present

theorem guardedProduce_member_sound (request : NormalizedParserRequest)
    (rows : List (ScheduledParserRow request.source))
    (produced : request.guardedProduce = some rows) (row : ScheduledParserRow request.source)
    (present : row ∈ rows) :
    ScheduledParserRowMeaning request.normalized.result.parsed request.source request.agreement
      request.writtenExact request.carrierFuel request.ruleFuel row := by
  rw [((guardedProduce_eq_some_iff request rows).mp produced).2] at present
  exact scheduledParserReport_member_sound _ _ _ _ _ _ row present

/-- Every actual annotation in an accepted normalized input is tied to an actual source candidate,
the internally scheduled final occurrence, and independent rich descriptor meaning. -/
theorem guardedProduce_raw_annotation_meaning (request : NormalizedParserRequest)
    (rows : List (ScheduledParserRow request.source))
    (produced : request.guardedProduce = some rows) (annotation : RawAtomAnnotation)
    (present : annotation ∈ rawAtomAnnotations request.normalized.result.parsed) :
    ∃ candidate descriptor,
      (parserIndexOfAromaticCanonicalCenter request.normalized.result.parsed request.source
        request.agreement candidate).val = annotation.index ∧
      occurrenceParserRichScheduledState request.normalized.result.parsed request.source
        request.agreement request.writtenExact request.carrierFuel request.ruleFuel
        (request.source.aromaticCanonicalFinalOccurrence request.carrierFuel candidate) =
          some descriptor ∧
      OccurrenceParserRichDescriptorMeaning request.normalized.result.parsed request.source
        request.agreement request.writtenExact
        (request.source.aromaticCanonicalFinalOccurrence request.carrierFuel candidate)
        (request.source.aromaticCanonicalDependencyView
          (occurrenceParserRichScheduledState request.normalized.result.parsed request.source
            request.agreement request.writtenExact request.carrierFuel request.ruleFuel)
          (request.source.aromaticCanonicalFinalOccurrence request.carrierFuel candidate))
        request.ruleFuel descriptor :=
  accepted_raw_parity_has_rich_meaning _ _ _ _ _ _
    ((guardedProduce_eq_some_iff request rows).mp produced).1 annotation present

end NormalizedParserRequest

namespace ClosedNormalizedParser

open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness
open TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeRawAnnotationGuard.ClosedRawCounterexample
  (annotatedCertifiedCF)

/-- The actual certified normalizer preserves this literal all-single-bond annotated parser input. -/
theorem normalized_parsed_eq : annotatedCertifiedCF.result.parsed = annotatedRawCF := rfl

/-- Full parser-source binding, not merely equality of the unannotated constitution. -/
def actualRequest : NormalizedParserRequest where
  normalized := annotatedCertifiedCF
  source := parserSource
  agreement := parserSource_agreement
  writtenExact := annotatedCertifiedCF.writtenNeighborExact
  carrierFuel := 0
  ruleFuel := 2

theorem actual_normalization_binding :
    actualRequest.normalized.result = normalizeRawMolecule annotatedRawCF ∧
      actualRequest.source = parserSource ∧
      actualRequest.normalized.result.parsed.AuthoritativeStructureAgreement
        actualRequest.source :=
  ⟨rfl, rfl, actualRequest.agreement⟩

theorem actual_audit_nil : actualRequest.audit = [] :=
  closed_audit_nil

theorem actual_report_eq : actualRequest.report = ClosedParserReport.actualReport := rfl

theorem actual_production_accepted :
    actualRequest.guardedProduce = some ClosedParserReport.actualReport :=
  (NormalizedParserRequest.guardedProduce_eq_some_iff _ _).mpr
    ⟨actual_audit_nil, actual_report_eq.symm⟩

theorem actual_production_R_row :
    ∃ rows, actualRequest.guardedProduce = some rows ∧
      ClosedParserReport.actualRRow ∈ rows :=
  ⟨ClosedParserReport.actualReport, actual_production_accepted,
    ClosedParserReport.actual_R_row_mem⟩

theorem actual_production_center_count_one :
    (actualRequest.report.map ScheduledParserRow.center).count parserCenter = 1 := by
  rw [actual_report_eq]
  exact ClosedParserReport.actual_R_center_count_one

theorem actual_production_R_meaning :
    ScheduledParserRowMeaning actualRequest.normalized.result.parsed actualRequest.source
      actualRequest.agreement actualRequest.writtenExact actualRequest.carrierFuel
      actualRequest.ruleFuel ClosedParserReport.actualRRow :=
  NormalizedParserRequest.guardedProduce_member_sound actualRequest
    ClosedParserReport.actualReport actual_production_accepted ClosedParserReport.actualRRow
    ClosedParserReport.actual_R_row_mem

end ClosedNormalizedParser
end TetraStereo.UniversalProof.SourceNativeScheduledParserReportProofs.SourceNativeNormalizedParserProduction
