import TetraStereo.OneCenter.CarbohydrateImageTranscriptionContract
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateSourceDataB
import TetraStereo.KernelOnly

set_option autoImplicit false


















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorSixReviewedImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def artifactOf : Carbohydrate1996ImageAudit.Provision →
    Carbohydrate1996ImageAudit.ImageArtifact
  | .imageArtifact artifact => artifact


def rows : List Carbohydrate1996ImageAudit.Provision :=
  Carbohydrate1996ImageAudit.Provision.transcribed

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := rows.map artifactOf

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 6 := by
  exact Carbohydrate1996ImageAudit.Provision.transcribed_length

@[simp] theorem artifact_count : artifacts.length = 6 := by
  simp [artifacts]

@[simp] theorem provision_count : provisions.length = 6 := by
  simp [provisions]

set_option maxRecDepth 4096 in


@[simp] theorem frozen_artifact_data_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.data =
      [ ⟨"2carb/2C3gif/GLOSA.GIF",
          "f7a79c819b00269cf18888c23a4f6b7974d66cfc71c4b45ada5bccbaebdcee78",
          .genericGlossaryStructure⟩
      , ⟨"2carb/2C3gif/GLOSB.GIF",
          "0e0bddb01154eda184734666e9c1a1fa3a12f9396b09a9f0aa5f6c0d49174c47",
          .genericGlossaryStructure⟩
      , ⟨"2carb/2C3gif/GLOSC.GIF",
          "bd9abe6f1411c02159ccbd02b6c600774f48c31583ea08fa300e00c5a77d23ab",
          .genericGlossaryStructure⟩
      , ⟨"2carb/2C3gif/GLOSD.GIF",
          "526330be0cd9d091c3f316dce59e4c1b8cde0ef07859a412d3b803dd1d02ab83",
          .genericGlossaryStructure⟩
      , ⟨"2carb/2C3gif/GLOSE.GIF",
          "e2fd8088c1b51f2494d7d8a6b18855fda8beb0326c1b0ea0bec12429a77b2733",
          .genericGlossaryStructure⟩
      , ⟨"2carb/2C3gif/LYGL1.GIF",
          "68ad39743b10c4f3d752c46061952a2da039d0be4314eee48915c5ef5ff9488f",
          .erratumCorrectedStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      [ ["glo.html"], ["glo.html"], ["glo.html"], ["glo.html"], ["glo.html"],
        ["33.html", "er336.html", "errat.html"] ] := by
  decide



def graphNontrivial (graph : Carbohydrate1996ImageAudit.StructureGraphTemplate) : Bool :=
  !graph.nodes.isEmpty && !graph.bonds.isEmpty

set_option maxRecDepth 4096 in
@[simp] theorem every_graph_is_well_formed_and_nontrivial :
    artifacts.all (fun artifact =>
      match Carbohydrate1996ImageAudit.symbolicTemplate? artifact.data.relativePath with
      | some graph => graph.wellFormed && graphNontrivial graph
      | none => false) = true := by
  decide

/-- The six rows are the same exact projection already kept outside the textual part-B batch. -/
@[simp] theorem provisions_eq_existing_six_graph_projection :
    provisions =
      GlobalNonDescriptorIndexedSourceData.carbohydrateTranscribedGraphProvisions := by
  rfl

theorem provisions_nodup : provisions.Nodup := by
  rw [provisions_eq_existing_six_graph_projection]
  exact GlobalNonDescriptorIndexedSourceData.carbohydrateTranscribedGraphProvisions_nodup

/-! ## Required atom-level denotation shape -/

inductive DenotationKind where
  | concreteMolecule
  | moleculeFamily
  | reactionFamily
  deriving DecidableEq, Repr

def denotationKind : Carbohydrate1996ImageTranscription.AtomLevelDenotation → DenotationKind
  | .concrete _ => .concreteMolecule
  | .moleculeFamily _ => .moleculeFamily
  | .reactionFamily _ => .reactionFamily

/-- Exact closed six-case graph-level chemistry read from the six rasters.  Separate constructors
retain the wavy open valence, O--R and O--NDP groups, the two distinct arrow roles, and the
corrected linkage instead of collapsing them to the common pyranose ring template. -/
inductive VisualDenotation where
  | glosaAnomericHydroxylFamily
  | glosbWavyOpenValenceGlycosylFamily
  | gloscAnomericOToRGlycosideFamily
  | glosdGlycosidaseCleavageHydrolysisFocus
  | gloseONucleotideDiphosphateGlycosylTransferDonor
  | lygl1LysineNitrogenToGlcNAcC1Linkage
  deriving DecidableEq, Repr

def expectedVisualDenotations : List VisualDenotation :=
  [ .glosaAnomericHydroxylFamily
  , .glosbWavyOpenValenceGlycosylFamily
  , .gloscAnomericOToRGlycosideFamily
  , .glosdGlycosidaseCleavageHydrolysisFocus
  , .gloseONucleotideDiphosphateGlycosylTransferDonor
  , .lygl1LysineNitrogenToGlcNAcC1Linkage
  ]

/-- `GLOSA`, `GLOSB`, and `GLOSC` are generic molecular families; `GLOSD` and `GLOSE`
are reaction families; the corrected `LYGL1` drawing is also a generic molecular family because
the lysine residue and GlcNAc context are not one fully specified concrete molecule. -/
def expectedDenotationKinds : List DenotationKind :=
  [ .moleculeFamily, .moleculeFamily, .moleculeFamily,
    .reactionFamily, .reactionFamily, .moleculeFamily ]

@[simp] theorem expected_denotation_kind_count : expectedDenotationKinds.length = 6 := by
  rfl

@[simp] theorem expected_visual_denotation_count : expectedVisualDenotations.length = 6 := by
  rfl




inductive ReviewerKind where
  | human
  | visionAutomated
  deriving DecidableEq, Repr




structure AutomatedVisualReviewData where
  relativePath : String
  sha256 : String
  denotation : VisualDenotation
  deriving DecidableEq, Repr

def agentVisualReviews : List AutomatedVisualReviewData :=
  [ ⟨"2carb/2C3gif/GLOSA.GIF",
      "f7a79c819b00269cf18888c23a4f6b7974d66cfc71c4b45ada5bccbaebdcee78",
      .glosaAnomericHydroxylFamily⟩
  , ⟨"2carb/2C3gif/GLOSB.GIF",
      "0e0bddb01154eda184734666e9c1a1fa3a12f9396b09a9f0aa5f6c0d49174c47",
      .glosbWavyOpenValenceGlycosylFamily⟩
  , ⟨"2carb/2C3gif/GLOSC.GIF",
      "bd9abe6f1411c02159ccbd02b6c600774f48c31583ea08fa300e00c5a77d23ab",
      .gloscAnomericOToRGlycosideFamily⟩
  , ⟨"2carb/2C3gif/GLOSD.GIF",
      "526330be0cd9d091c3f316dce59e4c1b8cde0ef07859a412d3b803dd1d02ab83",
      .glosdGlycosidaseCleavageHydrolysisFocus⟩
  , ⟨"2carb/2C3gif/GLOSE.GIF",
      "e2fd8088c1b51f2494d7d8a6b18855fda8beb0326c1b0ea0bec12429a77b2733",
      .gloseONucleotideDiphosphateGlycosylTransferDonor⟩
  , ⟨"2carb/2C3gif/LYGL1.GIF",
      "68ad39743b10c4f3d752c46061952a2da039d0be4314eee48915c5ef5ff9488f",
      .lygl1LysineNitrogenToGlcNAcC1Linkage⟩
  ]

@[simp] theorem automated_visual_review_count : agentVisualReviews.length = 6 := by
  rfl

set_option maxRecDepth 4096 in
@[simp] theorem automated_visual_review_paths_and_digests_exact :
    agentVisualReviews.map (fun review => (review.relativePath, review.sha256)) =
      artifacts.map (fun artifact => (artifact.data.relativePath, artifact.data.sha256)) := by
  decide

@[simp] theorem automated_visual_review_denotations_exact :
    agentVisualReviews.map AutomatedVisualReviewData.denotation = expectedVisualDenotations := by
  rfl

def agentVisualReview? (relativePath : String) : Option AutomatedVisualReviewData :=
  agentVisualReviews.find? fun review => review.relativePath == relativePath

/-- The unconditional graph-level source meaning for one image row.  The artifact data fixes the
path and digest, `symbolicTemplate` retains the checked graph, and `visualReview` retains the
independently read six-case meaning including the distinct GLOSD/GLOSE reaction roles. -/
structure VisionReviewedGraphMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  symbolicTemplate : Option Carbohydrate1996ImageAudit.StructureGraphTemplate
  visualReview : Option AutomatedVisualReviewData
  reviewerKind : ReviewerKind
  reviewMethod : String
  reviewLimitations : String
  deriving DecidableEq, Repr

def visionReviewedGraphMeaning
    (row : Carbohydrate1996ImageAudit.Provision) : VisionReviewedGraphMeaning :=
  match row with
  | .imageArtifact artifact =>
      { artifactData := artifact.data
        symbolicTemplate :=
          Carbohydrate1996ImageAudit.symbolicTemplate? artifact.data.relativePath
        visualReview := agentVisualReview? artifact.data.relativePath
        reviewerKind := .visionAutomated
        reviewMethod :=
          "record-750f24b3f75289f0c9cb0ed89efed7a3"
        reviewLimitations :=
          "automated-record-7a3d09ddb2db8d1ebc8941412a570df3" }

set_option maxRecDepth 4096 in
@[simp] theorem vision_reviewed_artifact_data_exact :
    rows.map (fun row => (visionReviewedGraphMeaning row).artifactData) =
      artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.data := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem vision_reviews_present_and_exact :
    rows.map (fun row => (visionReviewedGraphMeaning row).visualReview) =
      agentVisualReviews.map some := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem vision_reviewed_denotations_exact :
    rows.map (fun row =>
      (visionReviewedGraphMeaning row).visualReview.map AutomatedVisualReviewData.denotation) =
      expectedVisualDenotations.map some := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem vision_reviewed_graphs_are_well_formed_and_nontrivial :
    rows.all (fun row =>
      match (visionReviewedGraphMeaning row).symbolicTemplate,
          (visionReviewedGraphMeaning row).visualReview with
      | some graph, some _review => graph.wellFormed && graphNontrivial graph
      | _, _ => false) = true := by
  decide

/-- Exact, unconditional, vision-reviewed **graph-level** source-meaning batch.  This is the
strongest honest promotion supported by the six matching GIFs and the current representation; it
does not inhabit the stronger atom-level transcription contract below. -/
def visionReviewedGraphLevelBatch :
    GlobalNonDescriptorSourceMeaningBatch provisions := by
  simpa [provisions] using
    GlobalNonDescriptorIndexedSourceData.totalMeaningBatch rows
      IUPACNormativeProvision.carbohydrate1996ImageArtifact
      visionReviewedGraphMeaning (by intro _row; rfl)

@[simp] theorem vision_reviewed_entry_provisions_exact :
    visionReviewedGraphLevelBatch.entries.map
        GlobalNonDescriptorSourceMeaningEntry.provision = provisions :=
  visionReviewedGraphLevelBatch.provisions_exact

@[simp] theorem vision_reviewed_entry_count :
    visionReviewedGraphLevelBatch.entries.length = 6 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

theorem vision_reviewed_entry_provisions_nodup :
    (visionReviewedGraphLevelBatch.entries.map
      GlobalNonDescriptorSourceMeaningEntry.provision).Nodup := by
  rw [vision_reviewed_entry_provisions_exact]
  exact provisions_nodup

theorem every_vision_reviewed_entry_nonvacuous
    (sourceEntry : GlobalNonDescriptorSourceMeaningEntry)
    (_member : sourceEntry ∈ visionReviewedGraphLevelBatch.entries) :
    ∃ input, ∃ observation : sourceEntry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        sourceEntry.reference.toReference.Applicable input ∧
          sourceEntry.reference.toReference.Judges input observation :=
  sourceEntry.admittedJudgment





structure InternalAutomatedInspection where
  reviewerKind : ReviewerKind
  reviewerIdentity : String
  reviewDate : String
  method : String
  artifactsSearchedFor : List String
  authoritativeDownloadsObtained : Bool
  allCatalogDigestsMatched : Bool
  visualReviewPerformed : Bool
  graphLevelSourceFidelityEstablished : Bool
  atomLevelSourceFidelityEstablished : Bool
  limitations : String
  deriving DecidableEq, Repr

def currentInternalAutomatedInspection : InternalAutomatedInspection where
  reviewerKind := .visionAutomated
  reviewerIdentity := "automated-record-383f307281f3e8334bf1a04ad8470f83"
  reviewDate := "record-5fef69c92fe2101683b1f8429852bf13"
  method :=
    "record-6dc469e7c658b1698029426df398c751" ++
    "record-ea9290d285b7d60626d7e072d2be287d"
  artifactsSearchedFor :=
    ["GLOSA.GIF", "GLOSB.GIF", "GLOSC.GIF", "GLOSD.GIF", "GLOSE.GIF", "LYGL1.GIF"]
  authoritativeDownloadsObtained := true
  allCatalogDigestsMatched := true
  visualReviewPerformed := true
  graphLevelSourceFidelityEstablished := true
  atomLevelSourceFidelityEstablished := false
  limitations :=
    "automated-record-ad34127f51b57493f29f3fd3c1d79190" ++
    "record-0d62c5a89b64b9b69bc720b31478b94c" ++
    "record-c15b8b92937808903fd756e17664e27e" ++
    "record-e0d68894a9609a7c237678946e030cc9"

@[simp] theorem current_automated_inspection_boundary_exact :
    currentInternalAutomatedInspection.reviewerKind = .visionAutomated ∧
      currentInternalAutomatedInspection.authoritativeDownloadsObtained = true ∧
        currentInternalAutomatedInspection.allCatalogDigestsMatched = true ∧
          currentInternalAutomatedInspection.visualReviewPerformed = true ∧
            currentInternalAutomatedInspection.graphLevelSourceFidelityEstablished = true ∧
              currentInternalAutomatedInspection.atomLevelSourceFidelityEstablished = false := by
  simp [currentInternalAutomatedInspection]

/-! ## Minimal external trust boundary and conditional six-entry constructor -/

/-- External evidence that the bytes actually reviewed are the bytes named by the frozen manifest.
`sha256Implementation` is deliberately supplied at this boundary: Lean does not infer file bytes
from a digest string or claim that an arbitrary function is a cryptographic implementation. -/
structure FrozenSixImageBytesEvidence where
  bytesAtRelativePath : String → ByteArray
  sha256Implementation : ByteArray → String
  digestMatches : ∀ artifact ∈ artifacts,
    sha256Implementation (bytesAtRelativePath artifact.data.relativePath) = artifact.data.sha256



structure IndependentFidelityReview
    (SourceFaithful : Carbohydrate1996ImageTranscription.AtomLevelImageTranscription → Prop) where
  review : Carbohydrate1996ImageTranscription.ReviewedImageTranscription SourceFaithful
  reviewerKind : ReviewerKind
  reviewerIdentityDeclared : review.reviewer ≠ ""
  reviewDateDeclared : review.reviewDate ≠ ""
  methodDeclared : review.method ≠ ""
  visualComparisonPerformed : Bool
  visualComparisonPerformed_true : visualComparisonPerformed = true
  atomLevelComparisonPerformed : Bool
  atomLevelComparisonPerformed_true : atomLevelComparisonPerformed = true
  limitations : String

def IndependentFidelityReview.artifact
    {SourceFaithful :
      Carbohydrate1996ImageTranscription.AtomLevelImageTranscription → Prop}
    (review : IndependentFidelityReview SourceFaithful) :
    Carbohydrate1996ImageAudit.ImageArtifact :=
  review.review.transcription.artifact

def IndependentFidelityReview.denotation
    {SourceFaithful :
      Carbohydrate1996ImageTranscription.AtomLevelImageTranscription → Prop}
    (review : IndependentFidelityReview SourceFaithful) :
    Carbohydrate1996ImageTranscription.AtomLevelDenotation :=
  review.review.transcription.denotation




structure SixImageReviewPackage
    (SourceFaithful : Carbohydrate1996ImageTranscription.AtomLevelImageTranscription → Prop) where
  frozenBytes : FrozenSixImageBytesEvidence
  RealizesVisualDenotation :
    VisualDenotation → Carbohydrate1996ImageTranscription.AtomLevelDenotation → Prop
  reviews : List (IndependentFidelityReview SourceFaithful)
  artifacts_exact : reviews.map IndependentFidelityReview.artifact = artifacts
  denotationKinds_exact :
    reviews.map (fun review => denotationKind review.denotation) = expectedDenotationKinds
  denotations_realize_visual_reviews :
    List.Forall₂
      (fun review visual => RealizesVisualDenotation visual review.denotation)
      reviews expectedVisualDenotations

namespace SixImageReviewPackage

variable {SourceFaithful :
  Carbohydrate1996ImageTranscription.AtomLevelImageTranscription → Prop}

@[simp] theorem review_count (package : SixImageReviewPackage SourceFaithful) :
    package.reviews.length = 6 := by
  rw [← List.length_map (f := IndependentFidelityReview.artifact), package.artifacts_exact]
  exact artifact_count

def reviewProvision (review : IndependentFidelityReview SourceFaithful) :
    IUPACNormativeProvision :=
  .carbohydrate1996ImageArtifact (.imageArtifact review.artifact)

theorem review_provisions_exact (package : SixImageReviewPackage SourceFaithful) :
    package.reviews.map reviewProvision = provisions := by
  have mapped := congrArg
    (List.map fun artifact : Carbohydrate1996ImageAudit.ImageArtifact =>
      IUPACNormativeProvision.carbohydrate1996ImageArtifact (.imageArtifact artifact))
    package.artifacts_exact
  simpa [reviewProvision, artifacts, provisions, rows, artifactOf, List.map_map] using mapped










end SixImageReviewPackage



def currentIndependentFidelityReviews
    (SourceFaithful : Carbohydrate1996ImageTranscription.AtomLevelImageTranscription → Prop) :
    List (IndependentFidelityReview SourceFaithful) := []

theorem current_reviews_do_not_cover_the_six_artifacts
    (SourceFaithful : Carbohydrate1996ImageTranscription.AtomLevelImageTranscription → Prop) :
    (currentIndependentFidelityReviews SourceFaithful).map
        IndependentFidelityReview.artifact ≠ artifacts := by
  intro exactCoverage
  have lengthEquality := congrArg List.length exactCoverage
  simp [currentIndependentFidelityReviews] at lengthEquality

end GlobalNonDescriptorSixReviewedImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSixReviewedImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSixReviewedImageSourceMeanings.every_graph_is_well_formed_and_nontrivial
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSixReviewedImageSourceMeanings.automated_visual_review_paths_and_digests_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSixReviewedImageSourceMeanings.vision_reviewed_graphs_are_well_formed_and_nontrivial
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSixReviewedImageSourceMeanings.vision_reviewed_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSixReviewedImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSixReviewedImageSourceMeanings.current_reviews_do_not_cover_the_six_artifacts
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSixReviewedImageSourceMeanings.SixImageReviewPackage.review_count
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSixReviewedImageSourceMeanings.SixImageReviewPackage.review_provisions_exact
