import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.CarbohydrateImageArtifactAudit

set_option autoImplicit false

namespace TetraStereo.OneCenter














namespace Carbohydrate1996ImageTranscription

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

inductive AtomLevelDenotation : Type 1 where
  | concrete (input : CertifiedAuthoritativeChemicalInput)
  | moleculeFamily (family : CertifiedMoleculeFamily)
  | reactionFamily (family : CertifiedReactionFamily)

/-- A typed image-to-chemistry transcription.  Merely possessing a symbolic image template does
not construct this type. -/
structure AtomLevelImageTranscription : Type 1 where
  artifact : Carbohydrate1996ImageAudit.ImageArtifact
  chemical : artifact.data.kind.requiresMolecularGraph = true
  denotation : AtomLevelDenotation

def coveredArtifacts (transcriptions : List AtomLevelImageTranscription) :
    List Carbohydrate1996ImageAudit.ImageArtifact :=
  transcriptions.map AtomLevelImageTranscription.artifact

/-- Exact catalog coverage: no image is transcribed twice, every chemical image is covered, and no
nonchemical glyph is assigned a molecular denotation. -/
def ExactArtifactCoverage (transcriptions : List AtomLevelImageTranscription) : Prop :=
  (coveredArtifacts transcriptions).Nodup ∧
    Carbohydrate1996ImageAudit.ImageArtifact.all.all (fun artifact =>
      decide (artifact ∈ coveredArtifacts transcriptions) ==
        artifact.data.kind.requiresMolecularGraph) = true

def exactArtifactCoverage? (transcriptions : List AtomLevelImageTranscription) : Bool :=
  decide (coveredArtifacts transcriptions).Nodup &&
    Carbohydrate1996ImageAudit.ImageArtifact.all.all (fun artifact =>
      decide (artifact ∈ coveredArtifacts transcriptions) ==
        artifact.data.kind.requiresMolecularGraph)

@[simp] theorem exactArtifactCoverage?_eq_true_iff
    (transcriptions : List AtomLevelImageTranscription) :
    exactArtifactCoverage? transcriptions = true ↔ ExactArtifactCoverage transcriptions := by
  simp [exactArtifactCoverage?, ExactArtifactCoverage]

/-- Current symbolic templates and external fixtures are not silently promoted to atom-level
source transcriptions. -/
def currentAtomLevelTranscriptions : List AtomLevelImageTranscription := []

@[simp] theorem current_atom_level_image_coverage_is_false :
    exactArtifactCoverage? currentAtomLevelTranscriptions = false := by
  rw [Bool.eq_false_iff]
  intro coverageTrue
  have exactCoverage :=
    (exactArtifactCoverage?_eq_true_iff currentAtomLevelTranscriptions).mp coverageTrue
  have everyArtifactNonchemical :
      ∀ artifact ∈ Carbohydrate1996ImageAudit.ImageArtifact.all,
        artifact.data.kind.requiresMolecularGraph = false := by
    intro artifact member
    have checked := (List.all_eq_true.mp exactCoverage.2) artifact member
    simpa [currentAtomLevelTranscriptions, coveredArtifacts] using checked
  have chemicalArtifactsEmpty :
      (Carbohydrate1996ImageAudit.ImageArtifact.all.filter fun artifact =>
        artifact.data.kind.requiresMolecularGraph) = [] := by
    rw [List.filter_eq_nil_iff]
    intro artifact member
    simp [everyArtifactNonchemical artifact member]
  have chemicalCount :=
    Carbohydrate1996ImageAudit.chemical_and_nonchemical_image_partition.1
  rw [chemicalArtifactsEmpty] at chemicalCount
  have impossible : 0 = 425 := by
    simpa only [List.length_nil] using chemicalCount
  exact Nat.noConfusion impossible

theorem current_atom_level_image_coverage_is_incomplete :
    ¬ExactArtifactCoverage currentAtomLevelTranscriptions := by
  simp [← exactArtifactCoverage?_eq_true_iff]




structure ReviewedImageTranscription
    (SourceFaithful : AtomLevelImageTranscription → Prop) : Type 1 where
  transcription : AtomLevelImageTranscription
  reviewer : String
  reviewDate : String
  method : String
  sourceFaithful : SourceFaithful transcription

def reviewedTranscriptions
    {SourceFaithful : AtomLevelImageTranscription → Prop}
    (reviews : List (ReviewedImageTranscription SourceFaithful)) :
    List AtomLevelImageTranscription :=
  reviews.map ReviewedImageTranscription.transcription

def CompleteReviewedCoverage
    {SourceFaithful : AtomLevelImageTranscription → Prop}
    (reviews : List (ReviewedImageTranscription SourceFaithful)) : Prop :=
  ExactArtifactCoverage (reviewedTranscriptions reviews)

/-- Any complete reviewed catalog has exactly 425 entries, because the frozen corpus has exactly
425 chemical images and five nonchemical glyphs. -/
theorem complete_reviewed_catalog_has_425_transcriptions
    {SourceFaithful : AtomLevelImageTranscription → Prop}
    (reviews : List (ReviewedImageTranscription SourceFaithful))
    (complete : CompleteReviewedCoverage reviews) :
    (reviewedTranscriptions reviews).length = 425 := by
  have nodup := complete.1
  have membership := List.all_eq_true.mp complete.2
  let chemicalArtifacts :=
    Carbohydrate1996ImageAudit.ImageArtifact.all.filter fun artifact =>
      artifact.data.kind.requiresMolecularGraph
  have chemicalNodup : chemicalArtifacts.Nodup :=
    Carbohydrate1996ImageAudit.ImageArtifact.all_nodup.filter _
  have sameMembers : ∀ artifact,
      artifact ∈ chemicalArtifacts ↔
        artifact ∈ coveredArtifacts (reviewedTranscriptions reviews) := by
    intro artifact
    have same := membership artifact artifact.mem_all
    have boolEq :
        decide (artifact ∈ coveredArtifacts (reviewedTranscriptions reviews)) =
          artifact.data.kind.requiresMolecularGraph :=
      beq_iff_eq.mp same
    simp only [chemicalArtifacts, List.mem_filter, artifact.mem_all, true_and]
    rw [← boolEq]
    simp
  have permutation : chemicalArtifacts.Perm
      (coveredArtifacts (reviewedTranscriptions reviews)) :=
    (List.perm_ext_iff_of_nodup chemicalNodup nodup).2 sameMembers
  calc
    (reviewedTranscriptions reviews).length =
        (coveredArtifacts (reviewedTranscriptions reviews)).length := by
          simp [coveredArtifacts]
    _ = chemicalArtifacts.length := permutation.length_eq.symm
    _ = 425 := Carbohydrate1996ImageAudit.chemical_and_nonchemical_image_partition.1

end Carbohydrate1996ImageTranscription
end TetraStereo.OneCenter
