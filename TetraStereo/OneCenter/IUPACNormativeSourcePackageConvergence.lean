import TetraStereo.OneCenter.P10IndependentFigureReviewContract
import TetraStereo.OneCenter.Appendix3AtomLevelFigureReviewContract
import TetraStereo.OneCenter.Steroid1989IndependentFigureReviewContract
import TetraStereo.OneCenter.Carotenoid1974IndependentFigureReviewContract
import TetraStereo.OneCenter.Retinoid1981NormativeFigureReviewSeal
import TetraStereo.OneCenter.Carbohydrate1996IndependentFigureReviewContract
import TetraStereo.OneCenter.AminoAcidPeptide1983IndependentFigureReviewContract
import TetraStereo.OneCenter.Cyclitol1973IndependentFigureReviewContract
import TetraStereo.OneCenter.Lipid1976IndependentFigureReviewContract
import TetraStereo.OneCenter.Glycolipid1997IndependentFigureReviewContract
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192












namespace TetraStereo.OneCenter
namespace IUPACNormativeSourcePackageConvergence

open IUPACNormativeFigureReviewConvergence
open IUPACNormativeFigureReviewFrontier

abbrev P10ReviewPackage :=
  Σ SourceFaithful : P10FigureTranscription.AtomLevelFigureTranscription → Prop,
    P10IndependentFigureReviewContract.IndependentReviewPackage SourceFaithful

abbrev Appendix3ReviewPackage :=
  Σ SourceFaithful : Appendix3.AtomLevelFigureReviewContract.AtomLevelStructureTranscription → Prop,
    Σ ArtifactContinuityReviewed : Prop,
      Appendix3.AtomLevelFigureReviewContract.IndependentReviewPackage
        SourceFaithful ArtifactContinuityReviewed

abbrev SteroidReviewPackage :=
  Σ SourceFaithful : Steroid1989.IndependentFigureReviewContract.FigureTranscription → Prop,
    Steroid1989.IndependentFigureReviewContract.IndependentReviewPackage SourceFaithful

abbrev CarotenoidReviewPackage :=
  Σ SourceFaithful : Carotenoid1974.IndependentFigureReviewContract.FigureTranscription → Prop,
    Carotenoid1974.IndependentFigureReviewContract.IndependentReviewPackage SourceFaithful

abbrev RetinoidReviewPackage :=
  Σ ClauseSourceFaithful : Retinoid1981.SourceAudit.Ledger.NormativeClause → Prop,
    Σ TableRowSourceFaithful :
        Retinoid1981.SourceAudit.Ledger.StereoparentSubstituentRow → Prop,
      Σ FigureGraphSourceFaithful :
          Retinoid1981.FigureGraphTranscription.FrozenImageData →
            Retinoid1981.FigureGraphTranscription.FigureGraphFamilyEntry → Prop,
        Retinoid1981.IndependentReviewContract.IndependentReviewPackage
          ClauseSourceFaithful TableRowSourceFaithful FigureGraphSourceFaithful

abbrev CarbohydrateReviewPackage :=
  Σ SourceFaithful : Carbohydrate1996ImageTranscription.AtomLevelImageTranscription → Prop,
    Carbohydrate1996.IndependentFigureReviewContract.IndependentReviewPackage SourceFaithful

abbrev AminoAcidPeptideReviewPackage :=
  Σ SourceFaithful :
      AminoAcidPeptide1983.IndependentFigureReviewContract.DiagramTranscription → Prop,
    AminoAcidPeptide1983.IndependentFigureReviewContract.IndependentReviewPackage SourceFaithful

abbrev CyclitolReviewPackage :=
  Σ SourceFaithful : Cyclitol1973.IndependentFigureReviewContract.FigureTranscription → Prop,
    Cyclitol1973.IndependentFigureReviewContract.IndependentReviewPackage SourceFaithful

abbrev LipidReviewPackage :=
  Σ SourceFaithful : Lipid1976.IndependentFigureReviewContract.FigureTranscription → Prop,
    Lipid1976.IndependentFigureReviewContract.IndependentReviewPackage SourceFaithful

abbrev GlycolipidReviewPackage :=
  Σ SourceFaithful : Glycolipid1997.IndependentFigureReviewContract.FigureTranscription → Prop,
    Σ ArtifactContinuityReviewed : Prop,
      Glycolipid1997.IndependentFigureReviewContract.IndependentReviewPackage
        SourceFaithful ArtifactContinuityReviewed

structure TenSourceSpecificReviewPackages where
  p10 : P10ReviewPackage
  appendix3 : Appendix3ReviewPackage
  steroid : SteroidReviewPackage
  carotenoid : CarotenoidReviewPackage
  retinoid : RetinoidReviewPackage
  carbohydrate : CarbohydrateReviewPackage
  aminoAcidPeptide : AminoAcidPeptideReviewPackage
  cyclitol : CyclitolReviewPackage
  lipid : LipidReviewPackage
  glycolipid : GlycolipidReviewPackage

def sourceSpecificFigureReviewAdopted
    (packages : TenSourceSpecificReviewPackages) : IUPACNormativeSource → Prop
  | .blueBook2013P9 => False
  | .blueBook2013P10 =>
      P10IndependentFigureReviewContract.P10FigureReviewAdopted packages.p10.1
        .blueBook2013P10
  | .blueBook2013Appendix3 =>
      Appendix3.AtomLevelFigureReviewContract.Appendix3FigureReviewAdopted
        packages.appendix3.1 packages.appendix3.2.1 .blueBook2013Appendix3
  | .graphicalRepresentation2006 => False
  | .redBook2005IR9 => False
  | .periodicTable2022 => False
  | .atomicWeights2021 => False
  | .atomicMasses2020 => False
  | .steroidRecommendations1989 =>
      Steroid1989.IndependentFigureReviewContract.SteroidFigureReviewAdopted
        packages.steroid.1 .steroidRecommendations1989
  | .carotenoidRules1974 =>
      Carotenoid1974.IndependentFigureReviewContract.CarotenoidFigureReviewAdopted
        packages.carotenoid.1 .carotenoidRules1974
  | .retinoidRecommendations1981 =>
      Retinoid1981.NormativeFigureReviewSeal.RetinoidFigureReviewAdopted
        packages.retinoid.1 packages.retinoid.2.1 packages.retinoid.2.2.1
        .retinoidRecommendations1981
  | .carbohydrateRecommendations1996 =>
      Carbohydrate1996.IndependentFigureReviewContract.CarbohydrateFigureReviewAdopted
        packages.carbohydrate.1 .carbohydrateRecommendations1996
  | .aminoAcidPeptideRecommendations1983 =>
      AminoAcidPeptide1983.IndependentFigureReviewContract.AminoAcidPeptideFigureReviewAdopted
        packages.aminoAcidPeptide.1 .aminoAcidPeptideRecommendations1983
  | .cyclitolRecommendations1973 =>
      Cyclitol1973.IndependentFigureReviewContract.CyclitolFigureReviewAdopted
        packages.cyclitol.1 .cyclitolRecommendations1973
  | .nucleicAcidRecommendations1970 => False
  | .lipidRecommendations1976 =>
      Lipid1976.IndependentFigureReviewContract.LipidFigureReviewAdopted
        packages.lipid.1 .lipidRecommendations1976
  | .glycolipidRecommendations1997 =>
      Glycolipid1997.IndependentFigureReviewContract.GlycolipidFigureReviewAdopted
        packages.glycolipid.1 packages.glycolipid.2.1 .glycolipidRecommendations1997

private def relabelReviewComplete
    {P Q : IUPACNormativeSource → Prop} {source : IUPACNormativeSource}
    (inputSeal : SourceFigureReviewSeal P source) (complete : Q source) :
    SourceFigureReviewSeal Q source where
  reviewer := inputSeal.reviewer
  frozenSourceSha256 := inputSeal.frozenSourceSha256
  frozenSourceSha256Exact := inputSeal.frozenSourceSha256Exact
  reviewedTargetCount := inputSeal.reviewedTargetCount
  reviewedTargetCountExact := inputSeal.reviewedTargetCountExact
  reviewComplete := complete

def frontierFigureReviewPackage
    (packages : TenSourceSpecificReviewPackages) :
    FrontierFigureReviewPackage (sourceSpecificFigureReviewAdopted packages) where
  «seal» := by
    intro source member
    cases source with
    | blueBook2013P9 => simp [frontier_sources_exact] at member
    | blueBook2013P10 =>
        apply relabelReviewComplete
          (P10IndependentFigureReviewContract.p10SourceFigureReviewSeal packages.p10.2)
        simpa [sourceSpecificFigureReviewAdopted] using
          (P10IndependentFigureReviewContract.p10SourceFigureReviewSeal
            packages.p10.2).reviewComplete
    | blueBook2013Appendix3 =>
        apply relabelReviewComplete
          (Appendix3.AtomLevelFigureReviewContract.appendix3SourceFigureReviewSeal
            packages.appendix3.2.2)
        simpa [sourceSpecificFigureReviewAdopted] using
          (Appendix3.AtomLevelFigureReviewContract.appendix3SourceFigureReviewSeal
            packages.appendix3.2.2).reviewComplete
    | graphicalRepresentation2006 => simp [frontier_sources_exact] at member
    | redBook2005IR9 => simp [frontier_sources_exact] at member
    | periodicTable2022 => simp [frontier_sources_exact] at member
    | atomicWeights2021 => simp [frontier_sources_exact] at member
    | atomicMasses2020 => simp [frontier_sources_exact] at member
    | steroidRecommendations1989 =>
        apply relabelReviewComplete
          (Steroid1989.IndependentFigureReviewContract.steroidSourceFigureReviewSeal
            packages.steroid.2)
        simpa [sourceSpecificFigureReviewAdopted] using
          (Steroid1989.IndependentFigureReviewContract.steroidSourceFigureReviewSeal
            packages.steroid.2).reviewComplete
    | carotenoidRules1974 =>
        apply relabelReviewComplete
          (Carotenoid1974.IndependentFigureReviewContract.carotenoidSourceFigureReviewSeal
            packages.carotenoid.2)
        simpa [sourceSpecificFigureReviewAdopted] using
          (Carotenoid1974.IndependentFigureReviewContract.carotenoidSourceFigureReviewSeal
            packages.carotenoid.2).reviewComplete
    | retinoidRecommendations1981 =>
        apply relabelReviewComplete
          (Retinoid1981.NormativeFigureReviewSeal.retinoidSourceFigureReviewSeal
            packages.retinoid.2.2.2)
        simpa [sourceSpecificFigureReviewAdopted] using
          (Retinoid1981.NormativeFigureReviewSeal.retinoidSourceFigureReviewSeal
            packages.retinoid.2.2.2).reviewComplete
    | carbohydrateRecommendations1996 =>
        apply relabelReviewComplete
          (Carbohydrate1996.IndependentFigureReviewContract.carbohydrateSourceFigureReviewSeal
            packages.carbohydrate.2)
        simpa [sourceSpecificFigureReviewAdopted] using
          (Carbohydrate1996.IndependentFigureReviewContract.carbohydrateSourceFigureReviewSeal
            packages.carbohydrate.2).reviewComplete
    | aminoAcidPeptideRecommendations1983 =>
        apply relabelReviewComplete
          (AminoAcidPeptide1983.IndependentFigureReviewContract.aminoAcidPeptideSourceFigureReviewSeal
            packages.aminoAcidPeptide.2)
        simpa [sourceSpecificFigureReviewAdopted] using
          (AminoAcidPeptide1983.IndependentFigureReviewContract.aminoAcidPeptideSourceFigureReviewSeal
            packages.aminoAcidPeptide.2).reviewComplete
    | cyclitolRecommendations1973 =>
        apply relabelReviewComplete
          (Cyclitol1973.IndependentFigureReviewContract.cyclitolSourceFigureReviewSeal
            packages.cyclitol.2)
        simpa [sourceSpecificFigureReviewAdopted] using
          (Cyclitol1973.IndependentFigureReviewContract.cyclitolSourceFigureReviewSeal
            packages.cyclitol.2).reviewComplete
    | nucleicAcidRecommendations1970 => simp [frontier_sources_exact] at member
    | lipidRecommendations1976 =>
        apply relabelReviewComplete
          (Lipid1976.IndependentFigureReviewContract.lipidSourceFigureReviewSeal
            packages.lipid.2)
        simpa [sourceSpecificFigureReviewAdopted] using
          (Lipid1976.IndependentFigureReviewContract.lipidSourceFigureReviewSeal
            packages.lipid.2).reviewComplete
    | glycolipidRecommendations1997 =>
        apply relabelReviewComplete
          (Glycolipid1997.IndependentFigureReviewContract.glycolipidSourceFigureReviewSeal
            packages.glycolipid.2.2)
        simpa [sourceSpecificFigureReviewAdopted] using
          (Glycolipid1997.IndependentFigureReviewContract.glycolipidSourceFigureReviewSeal
            packages.glycolipid.2.2).reviewComplete

def checklistAfterSourceSpecificReviews
    (packages : TenSourceSpecificReviewPackages)
    (source : IUPACNormativeSource) : IUPACNormativeSource.ProvisionAuditChecklist :=
  checklistAfterFigureReviews (frontierFigureReviewPackage packages) source

theorem every_source_complete_after_source_specific_reviews
    (packages : TenSourceSpecificReviewPackages)
    (source : IUPACNormativeSource) :
    (checklistAfterSourceSpecificReviews packages source).Complete :=
  every_source_complete_after_frontier_figure_reviews
    (frontierFigureReviewPackage packages) source

theorem every_source_has_no_open_requirements_after_source_specific_reviews
    (packages : TenSourceSpecificReviewPackages)
    (source : IUPACNormativeSource) :
    (checklistAfterSourceSpecificReviews packages source).openRequirements = [] :=
  every_source_has_no_open_requirements_after_frontier_figure_reviews
    (frontierFigureReviewPackage packages) source

end IUPACNormativeSourcePackageConvergence
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeSourcePackageConvergence.frontierFigureReviewPackage
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeSourcePackageConvergence.every_source_complete_after_source_specific_reviews
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeSourcePackageConvergence.every_source_has_no_open_requirements_after_source_specific_reviews
