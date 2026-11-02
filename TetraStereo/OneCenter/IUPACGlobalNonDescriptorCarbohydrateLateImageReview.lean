import TetraStereo.OneCenter.CarbohydrateImageArtifactAudit
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateLateImageMeaningTypes

set_option autoImplicit false



namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings

open CarbohydrateLateImageMeaningData

structure VisionReviewedImageMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  sourcePages : List String
  sourceMeaning : Option ImageMeaning
  reviewEvidencePresent : Bool
  reviewerKind : String
  reviewMethod : String
  reviewLimitations : String

def VisionReviewedImageMeaning.complete (entry : VisionReviewedImageMeaning) : Bool :=
  entry.sourceMeaning.isSome && entry.reviewEvidencePresent

def visionReviewedImageMeaningOfPair
    (pair : Carbohydrate1996ImageAudit.ImageArtifact × ImageMeaning) :
    VisionReviewedImageMeaning :=
  { artifactData := pair.1.data
    sourcePages := pair.1.sourcePages
    sourceMeaning := some pair.2
    reviewEvidencePresent := true
    reviewerKind := "visionAutomated"
    reviewMethod := "record-e32a8c200dfa678404a81ce43949e899"
    reviewLimitations := "record-e42a7fb58c48c5f975a7c6fb5e2174c0" }

@[simp] theorem vision_reviewed_pair_complete
    (pair : Carbohydrate1996ImageAudit.ImageArtifact × ImageMeaning) :
    (visionReviewedImageMeaningOfPair pair).complete = true := by rfl

@[simp] theorem vision_reviewed_pairs_complete
    (pairs : List (Carbohydrate1996ImageAudit.ImageArtifact × ImageMeaning)) :
    (pairs.map visionReviewedImageMeaningOfPair).all VisionReviewedImageMeaning.complete = true := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih => simp [ih]

end GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter
