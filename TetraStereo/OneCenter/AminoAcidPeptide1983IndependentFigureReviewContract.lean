import TetraStereo.OneCenter.AminoAcidPeptide1983TechnicalAuditReadiness
import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.IUPACNormativeFigureReviewConvergence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192













namespace TetraStereo.OneCenter
namespace AminoAcidPeptide1983
namespace IndependentFigureReviewContract

open IUPACNormativeFigureReviewConvergence

structure CertifiedMoleculeFamily where
  Parameter : Type
  parameterNonempty : Nonempty Parameter
  instantiate : Parameter → CertifiedAuthoritativeChemicalInput

structure CertifiedReactionFamily where
  Parameter : Type
  parameterNonempty : Nonempty Parameter
  reactants : Parameter → List CertifiedAuthoritativeChemicalInput
  products : Parameter → List CertifiedAuthoritativeChemicalInput
  nonemptyReactants : ∀ parameter, (reactants parameter).length > 0
  nonemptyProducts : ∀ parameter, (products parameter).length > 0

structure ResidueTopologyEdge where
  source : Nat
  target : Nat
  deriving DecidableEq, Repr

/-! A topology is independently useful for peptide/residue diagrams without pretending each node
is an atom. Labels and every connection endpoint must be present. -/
structure CertifiedResidueTopology where
  residueLabels : List String
  residueLabelsNonempty : residueLabels ≠ []
  residueLabelsDeclared : residueLabels.all (fun label => !label.isEmpty) = true
  connections : List ResidueTopologyEdge
  connectionsWithinBounds : connections.all (fun edge =>
    decide (edge.source < residueLabels.length) &&
      decide (edge.target < residueLabels.length)) = true

inductive DiagramDenotation : Type 1 where
  | concreteMolecule (input : CertifiedAuthoritativeChemicalInput)
  | moleculeFamily (family : CertifiedMoleculeFamily)
  | reactionFamily (family : CertifiedReactionFamily)
  | residueTopology (topology : CertifiedResidueTopology)

structure DiagramTranscription : Type 1 where
  artifact : SourceImageArtifact
  diagramTarget : artifact.isGraphOrTopologyDiagram = true
  denotation : DiagramDenotation

def diagramTargets : List SourceImageArtifact :=
  SourceImageArtifact.all.filter fun artifact => artifact.isGraphOrTopologyDiagram

@[simp] theorem diagram_target_count_exact : diagramTargets.length = 95 := by
  decide

theorem diagram_targets_nodup : diagramTargets.Nodup :=
  SourceImageArtifact.all_nodup.filter _

def coveredArtifacts (transcriptions : List DiagramTranscription) : List SourceImageArtifact :=
  transcriptions.map DiagramTranscription.artifact

def ExactDiagramCoverage (transcriptions : List DiagramTranscription) : Prop :=
  (coveredArtifacts transcriptions).Perm diagramTargets

structure ReviewedDiagramTranscription
    (SourceFaithful : DiagramTranscription → Prop) : Type 1 where
  transcription : DiagramTranscription
  reviewer : String
  reviewDate : String
  method : String
  sourceFaithful : SourceFaithful transcription

def reviewedTranscriptions
    {SourceFaithful : DiagramTranscription → Prop}
    (reviews : List (ReviewedDiagramTranscription SourceFaithful)) : List DiagramTranscription :=
  reviews.map ReviewedDiagramTranscription.transcription

def CompleteReviewedCoverage
    {SourceFaithful : DiagramTranscription → Prop}
    (reviews : List (ReviewedDiagramTranscription SourceFaithful)) : Prop :=
  ExactDiagramCoverage (reviewedTranscriptions reviews)

def currentReviewedTranscriptions :
    List (ReviewedDiagramTranscription fun _ => False) := []

@[simp] theorem current_reviewed_coverage_is_incomplete :
    ¬CompleteReviewedCoverage currentReviewedTranscriptions := by
  intro complete
  have impossible : 0 = 95 := by
    calc
      0 = (coveredArtifacts (reviewedTranscriptions currentReviewedTranscriptions)).length := rfl
      _ = diagramTargets.length := complete.length_eq
      _ = 95 := diagram_target_count_exact
  exact Nat.noConfusion impossible

def sourceBundleSha256 : String :=
  (P10DelegatedAuthorityCorpus.snapshot .aminoAcidPeptide1983).bundleSha256

def ReviewMetadataMatches
    (reviewer : DeclaredIndependentReviewer)
    {SourceFaithful : DiagramTranscription → Prop}
    (review : ReviewedDiagramTranscription SourceFaithful) : Prop :=
  review.reviewer = reviewer.identity ∧
    review.reviewDate = reviewer.reviewDate ∧
      review.method = reviewer.method

structure IndependentReviewPackage
    (SourceFaithful : DiagramTranscription → Prop) : Type 1 where
  reviewer : DeclaredIndependentReviewer
  technicalDossier : TechnicalAuditReadiness.MachinePreparedForIndependentReview
  reviews : List (ReviewedDiagramTranscription SourceFaithful)
  completeReviewedCoverage : CompleteReviewedCoverage reviews
  reviewMetadataExact : reviews.Forall (ReviewMetadataMatches reviewer)

namespace IndependentReviewPackage

variable {SourceFaithful : DiagramTranscription → Prop}

@[simp] theorem review_count_exact
    (package : IndependentReviewPackage SourceFaithful) :
    package.reviews.length = 95 := by
  calc
    package.reviews.length = (reviewedTranscriptions package.reviews).length := by
      simp [reviewedTranscriptions]
    _ = (coveredArtifacts (reviewedTranscriptions package.reviews)).length := by
      simp [coveredArtifacts]
    _ = diagramTargets.length := package.completeReviewedCoverage.length_eq
    _ = 95 := diagram_target_count_exact

theorem every_review_metadata_exact
    (package : IndependentReviewPackage SourceFaithful)
    (review : ReviewedDiagramTranscription SourceFaithful)
    (member : review ∈ package.reviews) :
    review.reviewer = package.reviewer.identity ∧
      review.reviewDate = package.reviewer.reviewDate ∧
        review.method = package.reviewer.method :=
  (List.forall_iff_forall_mem.mp package.reviewMetadataExact) review member

end IndependentReviewPackage

@[simp] theorem source_bundle_digest_matches_manifest :
    sourceBundleSha256 =
      (IUPACNormativeSource.sha256? .aminoAcidPeptideRecommendations1983).getD "" :=
  rfl

def AminoAcidPeptideFigureReviewAdopted
    (SourceFaithful : DiagramTranscription → Prop)
    (source : IUPACNormativeSource) : Prop :=
  source = .aminoAcidPeptideRecommendations1983 ∧
    Nonempty (IndependentReviewPackage SourceFaithful)

theorem amino_acid_peptide_figure_review_adopted_of_package
    {SourceFaithful : DiagramTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    AminoAcidPeptideFigureReviewAdopted SourceFaithful
      .aminoAcidPeptideRecommendations1983 :=
  ⟨rfl, ⟨package⟩⟩

def aminoAcidPeptideSourceFigureReviewSeal
    {SourceFaithful : DiagramTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    SourceFigureReviewSeal (AminoAcidPeptideFigureReviewAdopted SourceFaithful)
      .aminoAcidPeptideRecommendations1983 where
  reviewer := package.reviewer
  frozenSourceSha256 := sourceBundleSha256
  frozenSourceSha256Exact := source_bundle_digest_matches_manifest
  reviewedTargetCount := 95
  reviewedTargetCountExact := by decide
  reviewComplete := amino_acid_peptide_figure_review_adopted_of_package package

@[simp] theorem amino_acid_peptide_seal_target_count_exact
    {SourceFaithful : DiagramTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    (aminoAcidPeptideSourceFigureReviewSeal package).reviewedTargetCount = 95 :=
  rfl

def candidateProvisionAuditChecklist
    {SourceFaithful : DiagramTranscription → Prop}
    (_package : IndependentReviewPackage SourceFaithful) :
    IUPACNormativeSource.ProvisionAuditChecklist :=
  (IUPACNormativeSource.currentProvisionAuditChecklist
    .aminoAcidPeptideRecommendations1983).withFigureReview

@[simp] theorem candidate_checklist_complete
    {SourceFaithful : DiagramTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    (candidateProvisionAuditChecklist package).Complete := by
  exact complete_after_confirming_sole_figure_requirement
    (IUPACNormativeSource.currentProvisionAuditChecklist .aminoAcidPeptideRecommendations1983)
    TechnicalAuditReadiness.current_open_amino_acid_peptide_review_requirements_exact

end IndependentFigureReviewContract
end AminoAcidPeptide1983
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.IndependentFigureReviewContract.diagram_target_count_exact
assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.IndependentFigureReviewContract.diagram_targets_nodup
assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.IndependentFigureReviewContract.current_reviewed_coverage_is_incomplete
assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.IndependentFigureReviewContract.IndependentReviewPackage.review_count_exact
assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.IndependentFigureReviewContract.IndependentReviewPackage.every_review_metadata_exact
assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.IndependentFigureReviewContract.source_bundle_digest_matches_manifest
assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.IndependentFigureReviewContract.amino_acid_peptide_figure_review_adopted_of_package
assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.IndependentFigureReviewContract.amino_acid_peptide_seal_target_count_exact
assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.IndependentFigureReviewContract.candidate_checklist_complete
