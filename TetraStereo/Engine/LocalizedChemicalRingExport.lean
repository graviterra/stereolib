import TetraStereo.Engine.LocalizedChemicalRingExactCertificate
import TetraStereo.Engine.LocalizedChemicalRingCenterProjection
import TetraStereo.Engine.LocalizedChemicalRingChronologyCertificate
import TetraStereo.Engine.CertificateExporter

set_option autoImplicit false

namespace TetraStereo.Engine.LocalizedChemicalRing

open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRingPhysicalAdmission (detectedCoordinateCfg)

/-- Scoped export of exact report semantics and equality of the single-center
projection to the named public report. -/
def ReportCertificateClaim : Prop :=
  (∀ (profile : Profile) (input : Input), coordinatesAdmitted input = true →
    ∃! p, ExactSourceMeaning profile input (detectedCoordinateCfg input.certified) p) ∧
  (∀ (profile : Profile) (input : Input) (c : input.certified.detectedMultiCenterMolecule.Center)
    (contexts : List (List Nat)) (outcome : Option LocalizedAuxiliaryLabel),
    (c.1.val, outcome) ∈ analyze profile input ↔ centerOutcome input c contexts = outcome) ∧
  (∀ (profile : Profile) (input : Input), ∀ cfg p, ExactSourceMeaning profile input cfg p →
    ∀ (c : input.certified.detectedMultiCenterMolecule.Center) outcome,
      (c.1.val, outcome) ∈ analyze profile input → FrozenOutcomeImpact input p c outcome)

theorem reportCertificateProof : ReportCertificateClaim :=
  ⟨existsUnique_exactSourceMeaning_of_coordinates, centerOutcome_mem_iff,
    fun _ _ _ _ meaning => meaning.frozen_disagreement⟩

def reportArtifact : LeanCertificateArtifact where
  kind := .stereoClaim
  title := "Exact accumulated-reference ring report on admitted coordinates"
  claim := ReportCertificateClaim
  proof := reportCertificateProof
  theoremExport :=
    { imports := ["TetraStereo.Engine.LocalizedChemicalRingExactCertificate",
        "TetraStereo.Engine.LocalizedChemicalRingCenterProjection",
        "TetraStereo.Engine.LocalizedChemicalRingChronologyCertificate"]
      options := ["set_option autoImplicit false",
        "open TetraStereo.OneCenter TetraStereo.Engine.LocalizedChemicalRing",
        "open TetraStereo.OneCenter.CertifiedLocalizedCIPInput",
        "open TetraStereo.OneCenter.LocalizedChemicalRingPhysicalAdmission (detectedCoordinateCfg)"]
      namespacePath := ["TetraStereo", "Generated"]
      theoremName := "localizedChemicalRingReport"
      statement := joinLines [
        "(∀ (profile : Profile) (input : Input), coordinatesAdmitted input = true →",
        "    ∃! p, ExactSourceMeaning profile input (detectedCoordinateCfg input.certified) p) ∧",
        "  (∀ (profile : Profile) (input : Input) (c : input.certified.detectedMultiCenterMolecule.Center)",
        "    (contexts : List (List Nat)) (outcome : Option LocalizedAuxiliaryLabel),",
        "    (c.1.val, outcome) ∈ analyze profile input ↔ centerOutcome input c contexts = outcome) ∧",
        "  (∀ (profile : Profile) (input : Input), ∀ cfg p, ExactSourceMeaning profile input cfg p →",
        "    ∀ (c : input.certified.detectedMultiCenterMolecule.Center) outcome,",
        "      (c.1.val, outcome) ∈ analyze profile input → FrozenOutcomeImpact input p c outcome)"]
      proofTerm := "  exact ⟨existsUnique_exactSourceMeaning_of_coordinates, centerOutcome_mem_iff, fun _ _ _ _ meaning => meaning.frozen_disagreement⟩" }

def reportExportEntry : CertificateExportEntry where
  artifact := reportArtifact
  key := "localized-chemical-ring-report"
  description := reportArtifact.title
  fileName := "LocalizedChemicalRingReport.lean"
  source := reportArtifact.source

end TetraStereo.Engine.LocalizedChemicalRing
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.reportCertificateProof
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.reportArtifact
