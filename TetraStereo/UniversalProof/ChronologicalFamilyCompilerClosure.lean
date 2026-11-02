import TetraStereo.UniversalProof.ChronologicalFamilyPhysicalBridge
import TetraStereo.UniversalProof.GeneralWrittenNeighborBridge
import TetraStereo.UniversalProof.ChronologicalFamilyRuntimeSourceBridge
import TetraStereo.Engine.Claims
import TetraStereo.Engine.CertificateExporter

set_option autoImplicit false

namespace TetraStereo.UniversalProof.ChronologicalFamilyCompilerClosure

open TetraStereo.OneCenter TetraStereo.Engine
open TetraStereo.UniversalProof.GeneralParserStateBridge
open TetraStereo.UniversalProof.ChronologicalFamilyRuntimeSourceBridge







def physicalRecords (parities : List TetrahedralInputParity) : RemainingPhysicalRecords parities :=
  ⟨GeneralWrittenNeighborBridge.familyRaw_writtenNeighborExact parities,
    ChronologicalFamilyPhysicalBridge.familyRaw_all_tag_pendant_sites parities⟩

def certifiedFamily (parities : List TetrahedralInputParity) :
    CertifiedChemistryNormalizationResult :=
  pendingCertifiedFromPhysicalRecords parities (physicalRecords parities)
    (ChronologicalFamilyPhysicalBridge.familyRaw_valenceOK parities)

theorem actual_certified_string_intake (parities : List TetrahedralInputParity) :
    parseAndNormalizeOpenSMILESCertified (familyString parities) =
      Except.ok (certifiedFamily parities) :=
  pending_actual_certified_string_intake parities (physicalRecords parities)
    (ChronologicalFamilyPhysicalBridge.familyRaw_valenceOK parities)

theorem certifiedFamily_parsed (parities : List TetrahedralInputParity) :
    (certifiedFamily parities).result.parsed = familyRaw parities :=
  family_normalized_parsed parities

/-- All five report segments and every source-label observation are retained. -/
def FamilyReport (parities : List TetrahedralInputParity) (positive : parities ≠ [])
    (carrierFuel : ℕ) : Prop :=
  let result := (certifiedFamily parities).result
  let domain := family_normalized_domain_of_records parities positive (physicalRecords parities)
  let input := family_normalized_source_input_of_records parities (physicalRecords parities)
  let fuel := analysisFuel (FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery.materialized result)
  analyzeNormalized result = ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.fullRows result fuel ∧
    ((analyzeNormalized result).filter fun assignment => assignment.outcome.assigned) =
      ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.tagRows result fuel ∧
    (ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.tagRows result fuel).map StereoAssignment.unit =
      (rawAnnotatedCenters result).map StereoUnit.tetrahedral ∧
    (∀ assignment ∈ analyzeNormalized result, assignment.outcome.assigned = false →
      assignment.outcome = .refused .notSpecified ∨ assignment.outcome = .refused .rankingUnresolved) ∧
    (∀ index spec parity (observed : result.parsed.atomAt? index = some spec)
      (tagged : spec.tetrahedral? = some parity),
      FirstZSourceDiscoveryAlignmentProofs.FirstZSourceDiscoveryAlignment.ownState result domain
        (ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.familySource result)
        (ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.familyAgreement result domain input) carrierFuel
        ((ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.familySource result).aromaticCanonicalFinalOccurrence
          carrierFuel (ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.tagCenter result domain input index spec
            parity observed tagged)) = some (.chiral
              (FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery.seedDescriptor result fuel index parity)))

theorem familyReport_holds (parities : List TetrahedralInputParity) (positive : parities ≠ [])
    (carrierFuel : ℕ) : FamilyReport parities positive carrierFuel :=
  pending_physical_whole_report_and_own_source parities positive (physicalRecords parities) carrierFuel

theorem otherFourSegments_nil (parities : List TetrahedralInputParity) (positive : parities ≠ []) :
    let branches := normalizedStereoAnalysisBranches (certifiedFamily parities).result
    branches.ordinaryDoubleBond = [] ∧ branches.coupledDoubleBond = [] ∧
      branches.oddCumuleneDoubleBond = [] ∧ branches.extendedAxial = [] :=
  ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.actual_other_four_segments_nil (familyRaw parities)
    (family_normalized_domain_of_records parities positive (physicalRecords parities))
    (family_normalized_source_input_of_records parities (physicalRecords parities))

def FamilyMemberClaim (parities : List TetrahedralInputParity) (positive : parities ≠ [])
    (carrierFuel : ℕ) : Prop :=
  let certificate := certifiedFamily parities
  parseOpenSMILES (familyString parities) = Except.ok (familyRaw parities) ∧
    parseAndNormalizeOpenSMILESCertified (familyString parities) = Except.ok certificate ∧
    certificate.result.parsed = familyRaw parities ∧
    certificate.result.parsed.atomCount = 6 * parities.length + 2 ∧
    certificate.result.parsed.bonds.length = 6 * parities.length + 1 ∧
    certificate.result.parsed.ValenceOK ∧
    certificate.result.parsed.StereochemicalAdmissible ∧
    certificate.result.parsed.Rule2MassesKnown ∧
    ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.ZeroHydrogenDemand (familyRaw parities) ∧
    (let branches := normalizedStereoAnalysisBranches certificate.result;
      branches.ordinaryDoubleBond = [] ∧ branches.coupledDoubleBond = [] ∧
        branches.oddCumuleneDoubleBond = [] ∧ branches.extendedAxial = []) ∧
    FamilyReport parities positive carrierFuel

theorem familyMemberClaim_holds (parities : List TetrahedralInputParity) (positive : parities ≠ [])
    (carrierFuel : ℕ) : FamilyMemberClaim parities positive carrierFuel := by
  unfold FamilyMemberClaim
  exact ⟨parse_family_string parities, actual_certified_string_intake parities,
    certifiedFamily_parsed parities,
    (by rw [certifiedFamily_parsed, familyRaw_atom_count]),
    (by rw [certifiedFamily_parsed, familyRaw_bond_count]),
    (certifiedFamily parities).valenceOK,
    (certifiedFamily parities).stereochemicalAdmissible,
    (certifiedFamily parities).rule2MassesKnown, familyRaw_zero_demand parities,
    otherFourSegments_nil parities positive, familyReport_holds parities positive carrierFuel⟩

def FamilyClaim : Prop :=
  ∀ (parities : List TetrahedralInputParity) (positive : parities ≠ []) (carrierFuel : ℕ),
    FamilyMemberClaim parities positive carrierFuel

theorem familyClaim_holds : FamilyClaim := familyMemberClaim_holds

def fixedPlan : PublicClaimTheoremPlan where
  imports := ["TetraStereo.UniversalProof.ChronologicalFamilyCompilerClosure", "TetraStereo.KernelOnly"]
  namespacePath := ["TetraStereo", "Generated", "ChronologicalStringFamilyCompilerExport"]
  theoremName := "chronologicalStringFamilyCorrect"
  statement := "TetraStereo.UniversalProof.ChronologicalFamilyCompilerClosure.FamilyClaim"
  proofTerm := "  exact TetraStereo.UniversalProof.ChronologicalFamilyCompilerClosure.compiledArtifact_checked\n\nexample : TetraStereo.UniversalProof.ChronologicalFamilyCompilerClosure.compiledArtifact.claim :=\n  chronologicalStringFamilyCorrect\n\nassert_kernel_only TetraStereo.Generated.ChronologicalStringFamilyCompilerExport.chronologicalStringFamilyCorrect"

def compiledArtifact : LeanCertificateArtifact :=
  compilePublicClaim fixedPlan .multiCenterRelation
    "Actual chronological STRING family: certified intake, complete report and own source"
    FamilyClaim familyClaim_holds

theorem compiledArtifact_claim : compiledArtifact.claim = FamilyClaim := rfl

theorem compiledArtifact_checked : compiledArtifact.claim := compiledArtifact.checked

def sourceEntry : CertificateSourceEntry where
  key := "chronological-string-family-compiler-export"
  description := "Actual STRING to certified report and same-source universal family theorem"
  fileName := "ChronologicalFamilyCompilerClosureKernelCertificate.lean"
  source := compiledArtifact.source

theorem sourceEntry_actual_compiler_source : sourceEntry.source = compiledArtifact.source := rfl

def writeFamilyExport (outputDirectory : String) : IO System.FilePath :=
  sourceEntry.writeSource outputDirectory

theorem writeFamilyExport_emits_renderer (outputDirectory : String) :
    writeFamilyExport outputDirectory = (do
      IO.FS.createDirAll (System.FilePath.mk outputDirectory)
      let path := sourceEntry.outputPath outputDirectory
      IO.FS.writeFile path sourceEntry.fileSource
      pure path) := rfl

theorem inhabited_compiler_family_claim :
    ∃ artifact : LeanCertificateArtifact, artifact = compiledArtifact ∧
      artifact.claim = FamilyClaim ∧ artifact.claim ∧ artifact.source = sourceEntry.source :=
  ⟨compiledArtifact, rfl, compiledArtifact_claim, compiledArtifact_checked, rfl⟩

end TetraStereo.UniversalProof.ChronologicalFamilyCompilerClosure
