import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.P10NormativeAudit

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.OneCenter














namespace P10FigureTranscription

def sourceArtifactSha256 : String :=
  "e1185116ad0e61641832931ad87d333e14a8b37ce55e8a19e4570c4c1b42bedf"

def extractionMethod : String :=
  "Poppler pdfimages -list; primary image rows only; soft masks excluded; rendered-page visual classification"

/-- One primary embedded chemical image at a one-based page and one-based local ordinal. -/
structure FigureOccurrence where
  page : Nat
  localOrdinal : Nat
  deriving DecidableEq, Repr

/-- Primary embedded image occurrences on PDF pages 1 through 113. -/
def pageImageCounts : List Nat :=
  [ 0, 0, 0, 3, 4, 2, 7, 4, 8, 3, 4, 5, 5, 4, 4, 5, 6, 4, 5, 3
  , 4, 4, 3, 5, 4, 4, 3, 4, 5, 4, 5, 5, 3, 5, 5, 5, 4, 3, 5, 4
  , 0, 7, 16, 8, 6, 3, 7, 6, 1, 4, 2, 4, 5, 4, 2, 5, 5, 4, 5, 4
  , 5, 4, 7, 3, 3, 5, 5, 4, 6, 5, 5, 3, 4, 4, 5, 3, 2, 1, 4, 2
  , 5, 8, 8, 5, 5, 4, 4, 1, 3, 2, 1, 5, 6, 5, 3, 7, 4, 6, 5, 5
  , 4, 4, 3, 5, 3, 4, 3, 2, 4, 4, 3, 4, 3
  ]

private def enumerateOccurrencesFrom : Nat → List Nat → List FigureOccurrence
  | _, [] => []
  | page, count :: remainingCounts =>
      (List.range count).map (fun ordinal => ⟨page, ordinal + 1⟩) ++
        enumerateOccurrencesFrom (page + 1) remainingCounts

def allImageOccurrences : List FigureOccurrence :=
  enumerateOccurrencesFrom 1 pageImageCounts

def figureBearingPages : List Nat :=
  (allImageOccurrences.map FigureOccurrence.page).eraseDups

/-- Evidence that a later occurrence is the same frozen PDF image object as an earlier one. -/
structure LiteralObjectReuse where
  pdfObjectId : Nat
  canonicalOccurrence : FigureOccurrence
  reusedOccurrence : FigureOccurrence
  occurrencesDiffer : canonicalOccurrence ≠ reusedOccurrence
  deriving Repr

/-- The only repeated primary image objects reported by `pdfimages -list`. -/
def literalObjectReuses : List LiteralObjectReuse :=
  [ ⟨273, ⟨8, 3⟩, ⟨15, 1⟩, by decide⟩
  , ⟨322, ⟨9, 7⟩, ⟨12, 1⟩, by decide⟩
  , ⟨339, ⟨10, 1⟩, ⟨11, 1⟩, by decide⟩
  ]

def reusedOccurrences : List FigureOccurrence :=
  literalObjectReuses.map LiteralObjectReuse.reusedOccurrence

/-- One representative of every distinct embedded chemical drawing. -/
def canonicalFigureTargets : List FigureOccurrence :=
  allImageOccurrences.filter fun occurrence => decide (occurrence ∉ reusedOccurrences)

@[simp] theorem page_image_counts_cover_pdf : pageImageCounts.length = 113 := by
  decide

@[simp] theorem embedded_image_occurrence_sum_exact : pageImageCounts.sum = 476 := by
  decide

@[simp] theorem image_occurrence_count_exact : allImageOccurrences.length = 476 := by
  decide

@[simp] theorem image_occurrences_nodup : allImageOccurrences.Nodup := by
  decide

@[simp] theorem figure_bearing_page_count_exact : figureBearingPages.length = 109 := by
  decide

@[simp] theorem literal_object_reuse_count_exact : literalObjectReuses.length = 3 := by
  decide

@[simp] theorem reused_occurrence_count_exact : reusedOccurrences.length = 3 := by
  decide

@[simp] theorem reused_occurrences_are_targets :
    reusedOccurrences.all (fun occurrence => decide (occurrence ∈ allImageOccurrences)) = true := by
  decide

@[simp] theorem reused_occurrences_nodup : reusedOccurrences.Nodup := by
  decide

@[simp] theorem canonical_figure_target_count_exact : canonicalFigureTargets.length = 473 := by
  decide

@[simp] theorem canonical_figure_targets_nodup : canonicalFigureTargets.Nodup := by
  exact image_occurrences_nodup.filter _



/-- A drawing may contain one molecule or several chemically meaningful molecular graphs. -/
structure AtomLevelFigureTranscription where
  target : FigureOccurrence
  targetCanonical : target ∈ canonicalFigureTargets
  molecularGraphs : List CertifiedAuthoritativeChemicalInput
  molecularGraphsNonempty : molecularGraphs ≠ []

def coveredTargets (transcriptions : List AtomLevelFigureTranscription) :
    List FigureOccurrence :=
  transcriptions.map AtomLevelFigureTranscription.target

/-- Exact coverage is permutation equality with the 473-target canonical queue. -/
def ExactTargetCoverage (transcriptions : List AtomLevelFigureTranscription) : Prop :=
  (coveredTargets transcriptions).Perm canonicalFigureTargets

/-- Source fidelity cannot be inferred from the PDF digest or from target coverage. -/
structure ReviewedFigureTranscription
    (SourceFaithful : AtomLevelFigureTranscription → Prop) where
  transcription : AtomLevelFigureTranscription
  reviewer : String
  reviewDate : String
  method : String
  sourceFaithful : SourceFaithful transcription

def reviewedTranscriptions
    {SourceFaithful : AtomLevelFigureTranscription → Prop}
    (reviews : List (ReviewedFigureTranscription SourceFaithful)) :
    List AtomLevelFigureTranscription :=
  reviews.map ReviewedFigureTranscription.transcription

def CompleteReviewedCoverage
    {SourceFaithful : AtomLevelFigureTranscription → Prop}
    (reviews : List (ReviewedFigureTranscription SourceFaithful)) : Prop :=
  ExactTargetCoverage (reviewedTranscriptions reviews)

/-- Inventory does not silently create source-faithful graph reviews. -/
def currentReviewedTranscriptions :
    List (ReviewedFigureTranscription fun _ => False) := []

@[simp] theorem current_reviewed_coverage_is_incomplete :
    ¬CompleteReviewedCoverage currentReviewedTranscriptions := by
  intro complete
  have impossible : 0 = 473 := by
    calc
      0 = canonicalFigureTargets.length := by
        simpa [currentReviewedTranscriptions, reviewedTranscriptions, coveredTargets] using
          complete.length_eq
      _ = 473 := canonical_figure_target_count_exact
  exact Nat.noConfusion impossible

theorem complete_reviewed_catalog_has_473_transcriptions
    {SourceFaithful : AtomLevelFigureTranscription → Prop}
    (reviews : List (ReviewedFigureTranscription SourceFaithful))
    (complete : CompleteReviewedCoverage reviews) :
    (reviewedTranscriptions reviews).length = 473 := by
  calc
    (reviewedTranscriptions reviews).length =
        (coveredTargets (reviewedTranscriptions reviews)).length := by
      simp [coveredTargets]
    _ = canonicalFigureTargets.length := complete.length_eq
    _ = 473 := canonical_figure_target_count_exact

theorem p10_figure_review_gate_remains_open :
    BlueBookP10Audit.currentSourceReviewFigureGraphTranscriptionsReviewed = false := by
  rfl

end P10FigureTranscription
end TetraStereo.OneCenter
