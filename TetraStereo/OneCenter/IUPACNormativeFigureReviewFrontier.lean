import TetraStereo.OneCenter.IUPACNormativeManifest
import TetraStereo.OneCenter.P10FigureTranscriptionContract
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.OneCenter














namespace IUPACNormativeFigureReviewFrontier

open IUPACNormativeSource


def figureReviewTargetCount : IUPACNormativeSource → Nat
  | .blueBook2013P10 => P10FigureTranscription.canonicalFigureTargets.length
  | .blueBook2013Appendix3 => BlueBookAppendix3Audit.Provision.all.length
  | .steroidRecommendations1989 =>
      (Steroid1989.SourceImageArtifact.all.filter fun image => image.isMolecularGraph).length
  | .carotenoidRules1974 =>
      (Carotenoid1974.SourceImageArtifact.all.filter fun image => image.isMolecularGraph).length
  | .retinoidRecommendations1981 =>
      Retinoid1981.SourceAudit.ImageArtifact.pendingGraphTranscriptions.length
  | .carbohydrateRecommendations1996 =>
      (Carbohydrate1996ImageAudit.ImageArtifact.all.filter fun artifact =>
        artifact.data.kind.requiresMolecularGraph).length
  | .aminoAcidPeptideRecommendations1983 =>
      (AminoAcidPeptide1983.SourceImageArtifact.all.filter fun image =>
        image.isGraphOrTopologyDiagram).length
  | .cyclitolRecommendations1973 =>
      (Cyclitol1973.SourceImageArtifact.all.filter fun image =>
        image.isMolecularGraph && image.belongsTo1973Recommendation).length
  | .lipidRecommendations1976 =>
      (Lipid1976.SourceImageArtifact.all.filter fun image => image.isMolecularGraph).length
  | .glycolipidRecommendations1997 =>
      (P10DelegatedAuthorityCorpus.snapshot .glycolipid1997).imageCount
  | _ => 0

/-- This is definitionally the manifest's exact incomplete-source list. -/
def frontierSources : List IUPACNormativeSource :=
  currentIncompleteProvisionAuditSources

def frontierTargetCounts : List Nat :=
  frontierSources.map figureReviewTargetCount

def totalTargetCount : Nat := frontierTargetCounts.sum

/-- The three clusters chosen by target count, not by manifest order. -/
def dominantSources : List IUPACNormativeSource :=
  [ .blueBook2013P10
  , .carbohydrateRecommendations1996
  , .blueBook2013Appendix3 ]

def residualSources : List IUPACNormativeSource :=
  frontierSources.filter fun source => decide (source ∉ dominantSources)

def dominantTargetCount : Nat :=
  (dominantSources.map figureReviewTargetCount).sum

def residualTargetCount : Nat :=
  (residualSources.map figureReviewTargetCount).sum

def frontierRequirementsAreFigureOnly : Bool :=
  frontierSources.all fun source =>
    decide (currentOpenProvisionAuditRequirements source =
      [.figureGraphTranscriptionsReviewed])

@[simp] theorem frontier_sources_exact :
    frontierSources =
      [ .blueBook2013P10
      , .blueBook2013Appendix3
      , .steroidRecommendations1989
      , .carotenoidRules1974
      , .retinoidRecommendations1981
      , .carbohydrateRecommendations1996
      , .aminoAcidPeptideRecommendations1983
      , .cyclitolRecommendations1973
      , .lipidRecommendations1976
      , .glycolipidRecommendations1997 ] := by
  exact currentIncompleteProvisionAuditSources_exact

@[simp] theorem frontier_source_count_exact : frontierSources.length = 10 := by
  rw [frontier_sources_exact]
  decide

@[simp] theorem frontier_target_counts_exact :
    frontierTargetCounts = [473, 171, 68, 48, 14, 425, 95, 42, 21, 13] := by
  decide

@[simp] theorem total_target_count_exact : totalTargetCount = 1370 := by
  decide

@[simp] theorem residual_sources_exact :
    residualSources =
      [ .steroidRecommendations1989
      , .carotenoidRules1974
      , .retinoidRecommendations1981
      , .aminoAcidPeptideRecommendations1983
      , .cyclitolRecommendations1973
      , .lipidRecommendations1976
      , .glycolipidRecommendations1997 ] := by
  decide

@[simp] theorem dominant_target_count_exact : dominantTargetCount = 1069 := by
  decide

@[simp] theorem residual_target_count_exact : residualTargetCount = 301 := by
  decide

theorem dominant_and_residual_partition_frontier :
    (dominantSources ++ residualSources).Perm frontierSources := by
  decide

@[simp] theorem dominant_plus_residual_target_count_exact :
    dominantTargetCount + residualTargetCount = totalTargetCount := by
  decide

theorem dominant_sources_cover_at_least_three_quarters :
    4 * dominantTargetCount ≥ 3 * totalTargetCount := by
  decide

@[simp] theorem frontier_requirements_are_figure_only :
    frontierRequirementsAreFigureOnly = true := by
  decide

theorem every_frontier_source_has_only_figure_review_open
    (source : IUPACNormativeSource) (member : source ∈ frontierSources) :
    currentOpenProvisionAuditRequirements source =
      [.figureGraphTranscriptionsReviewed] := by
  have checked :=
    (List.all_eq_true.mp frontier_requirements_are_figure_only) source member
  simpa [frontierRequirementsAreFigureOnly] using checked

end IUPACNormativeFigureReviewFrontier
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeFigureReviewFrontier.frontier_sources_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeFigureReviewFrontier.frontier_target_counts_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeFigureReviewFrontier.total_target_count_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeFigureReviewFrontier.dominant_and_residual_partition_frontier
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeFigureReviewFrontier.dominant_plus_residual_target_count_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeFigureReviewFrontier.dominant_sources_cover_at_least_three_quarters
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeFigureReviewFrontier.every_frontier_source_has_only_figure_review_open
