import TetraStereo.OneCenter.IUPACNormativeManifest
import TetraStereo.OneCenter.Retinoid1981ExplicitCenterLabelCatalog
import TetraStereo.OneCenter.Retinoid1981FigureCatalogImplicitHydrogen
import TetraStereo.KernelOnly

set_option autoImplicit false













namespace TetraStereo.OneCenter
namespace Retinoid1981
namespace TechnicalAuditReadiness

open SourceAudit.Ledger
open FigureGraphTranscription
open FigureAuthorityInput
open StereoparentTableAuthorityInput
open StereoparentTableImplicitHydrogen
open FigureCatalogImplicitHydrogen
open ExplicitEZExampleCatalog
open StereoparentTablePolyeneConfiguration
open ExplicitCenterLabelCatalog

inductive EvidenceCategory where
  | proseAndTableInventory
  | constitutionalGraphs
  | implicitHydrogens
  | explicitDoubleBondConfigurations
  | inheritedStereoparentConfigurations
  | explicitCenterLabels
  deriving DecidableEq, Repr

namespace EvidenceCategory

def all : List EvidenceCategory :=
  [ .proseAndTableInventory
  , .constitutionalGraphs
  , .implicitHydrogens
  , .explicitDoubleBondConfigurations
  , .inheritedStereoparentConfigurations
  , .explicitCenterLabels ]

@[simp] theorem all_exact : all =
    [ .proseAndTableInventory
    , .constitutionalGraphs
    , .implicitHydrogens
    , .explicitDoubleBondConfigurations
    , .inheritedStereoparentConfigurations
    , .explicitCenterLabels ] := by
  rfl

@[simp] theorem count : all.length = 6 := by
  decide

theorem all_nodup : all.Nodup := by
  decide

end EvidenceCategory




structure TechnicalEvidence where
  normativeClauseCount : Nat
  normativeSectionCount : Nat
  stereoparentTableRowCount : Nat
  figureArtifactCount : Nat
  sourceSpecificFigureInputCount : Nat
  tableImplicitHydrogenCount : Nat
  figureImplicitHydrogenCount : Nat
  explicitEZClaimCount : Nat
  inheritedTablePolyeneClaimCount : Nat
  explicitCenterLabelCount : Nat
  normativeClauseCountExact : normativeClauseCount = NormativeClause.all.length
  normativeSectionCountExact :
    normativeSectionCount = SourceAudit.NormativeSection.all.length
  stereoparentTableRowCountExact :
    stereoparentTableRowCount = stereoparentSubstituentRows.length
  figureArtifactCountExact : figureArtifactCount = frozenImageData.length
  sourceSpecificFigureInputCountExact :
    sourceSpecificFigureInputCount = certifiedSourceSpecificAuthorityInputs.length
  tableImplicitHydrogenCountExact :
    tableImplicitHydrogenCount = completedStereoparentTableImplicitHydrogens.length
  figureImplicitHydrogenCountExact :
    figureImplicitHydrogenCount = completedSourceSpecificFigureImplicitHydrogens.length
  explicitEZClaimCountExact : explicitEZClaimCount = explicitEZClaimLedger.length
  inheritedTablePolyeneClaimCountExact :
    inheritedTablePolyeneClaimCount = stereoparentTablePolyeneClaimLedger.length
  explicitCenterLabelCountExact :
    explicitCenterLabelCount = explicitCenterLabelLedger.length
  noUnresolvedAuthorityInputs :
    unresolvedStereoparentTableAuthorityInputs = [] ∧
      unresolvedSourceSpecificAuthorityInputs = []
  noUnresolvedImplicitHydrogens :
    unresolvedStereoparentTableImplicitHydrogens = [] ∧
      unresolvedSourceSpecificFigureImplicitHydrogens = []
  allExplicitEZClaimsGraphAccepted :
    explicitEZExampleEntries.all
      (fun entry => claimsAcceptedByGraph? entry.graph entry.claims) = true
  allInheritedPolyeneClaimsGraphAccepted :
    configuredStereoparentTableEntries.all
      (fun entry => claimsAcceptedByGraph? entry.graph entry.ezClaims) = true
  allExplicitCenterLabelsGraphAccepted :
    explicitCenterLabelEntries.all
      (fun entry => centerLabelsAcceptedByGraph? entry.graph entry.claims) = true

def currentTechnicalEvidence : TechnicalEvidence where
  normativeClauseCount := 62
  normativeSectionCount := 19
  stereoparentTableRowCount := 10
  figureArtifactCount := 14
  sourceSpecificFigureInputCount := 17
  tableImplicitHydrogenCount := 10
  figureImplicitHydrogenCount := 17
  explicitEZClaimCount := 25
  inheritedTablePolyeneClaimCount := 40
  explicitCenterLabelCount := 5
  normativeClauseCountExact := by simp
  normativeSectionCountExact := by simp
  stereoparentTableRowCountExact := by simp
  figureArtifactCountExact := by simp
  sourceSpecificFigureInputCountExact := by simp
  tableImplicitHydrogenCountExact := by simp
  figureImplicitHydrogenCountExact := by simp
  explicitEZClaimCountExact := by simp
  inheritedTablePolyeneClaimCountExact := by simp
  explicitCenterLabelCountExact := by simp
  noUnresolvedAuthorityInputs := by simp
  noUnresolvedImplicitHydrogens := by simp
  allExplicitEZClaimsGraphAccepted := explicit_ez_example_claims_all_accepted
  allInheritedPolyeneClaimsGraphAccepted :=
    configured_stereoparent_table_claims_all_accepted
  allExplicitCenterLabelsGraphAccepted := explicit_center_labels_all_accepted

@[simp] theorem current_technical_evidence_inventory_counts_exact :
    currentTechnicalEvidence.normativeClauseCount = 62 ∧
      currentTechnicalEvidence.normativeSectionCount = 19 ∧
        currentTechnicalEvidence.stereoparentTableRowCount = 10 ∧
          currentTechnicalEvidence.figureArtifactCount = 14 ∧
            currentTechnicalEvidence.sourceSpecificFigureInputCount = 17 := by
  decide

@[simp] theorem current_technical_evidence_completion_counts_exact :
    currentTechnicalEvidence.tableImplicitHydrogenCount = 10 ∧
      currentTechnicalEvidence.figureImplicitHydrogenCount = 17 ∧
        currentTechnicalEvidence.explicitEZClaimCount = 25 ∧
          currentTechnicalEvidence.inheritedTablePolyeneClaimCount = 40 ∧
            currentTechnicalEvidence.explicitCenterLabelCount = 5 := by
  decide

theorem current_technical_evidence_has_no_machine_gap :
    (unresolvedStereoparentTableAuthorityInputs = [] ∧
      unresolvedSourceSpecificAuthorityInputs = []) ∧
      (unresolvedStereoparentTableImplicitHydrogens = [] ∧
        unresolvedSourceSpecificFigureImplicitHydrogens = []) ∧
        explicitEZExampleEntries.all
          (fun entry => claimsAcceptedByGraph? entry.graph entry.claims) = true ∧
          configuredStereoparentTableEntries.all
            (fun entry => claimsAcceptedByGraph? entry.graph entry.ezClaims) = true ∧
            explicitCenterLabelEntries.all
              (fun entry => centerLabelsAcceptedByGraph? entry.graph entry.claims) = true := by
  exact
    ⟨ currentTechnicalEvidence.noUnresolvedAuthorityInputs
    , currentTechnicalEvidence.noUnresolvedImplicitHydrogens
    , currentTechnicalEvidence.allExplicitEZClaimsGraphAccepted
    , currentTechnicalEvidence.allInheritedPolyeneClaimsGraphAccepted
    , currentTechnicalEvidence.allExplicitCenterLabelsGraphAccepted ⟩

/-- This is intentionally computed from the global manifest rather than maintained as a second
status flag. -/
def currentOpenRetinoidReviewRequirements :
    List IUPACNormativeSource.ProvisionAuditRequirement :=
  IUPACNormativeSource.currentOpenProvisionAuditRequirements
    .retinoidRecommendations1981

@[simp] theorem current_open_retinoid_review_requirements_exact :
    currentOpenRetinoidReviewRequirements =
      [ .figureGraphTranscriptionsReviewed ] := by
  decide



structure MachinePreparedForIndependentReview where
  evidence : TechnicalEvidence
  categoriesExact : evidence = currentTechnicalEvidence
  openRequirementsExact : currentOpenRetinoidReviewRequirements =
    [ .figureGraphTranscriptionsReviewed ]

def current_machine_prepared_for_independent_review :
    MachinePreparedForIndependentReview :=
  { evidence := currentTechnicalEvidence
    categoriesExact := rfl
    openRequirementsExact := current_open_retinoid_review_requirements_exact }

theorem current_retinoid_audit_remains_incomplete :
    ¬IUPACNormativeSource.ProvisionAuditComplete .retinoidRecommendations1981 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete]

end TechnicalAuditReadiness
end Retinoid1981
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.TechnicalAuditReadiness.EvidenceCategory.all_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.TechnicalAuditReadiness.current_technical_evidence_inventory_counts_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.TechnicalAuditReadiness.current_technical_evidence_completion_counts_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.TechnicalAuditReadiness.current_technical_evidence_has_no_machine_gap
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.TechnicalAuditReadiness.current_open_retinoid_review_requirements_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.TechnicalAuditReadiness.current_machine_prepared_for_independent_review
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.TechnicalAuditReadiness.current_retinoid_audit_remains_incomplete
