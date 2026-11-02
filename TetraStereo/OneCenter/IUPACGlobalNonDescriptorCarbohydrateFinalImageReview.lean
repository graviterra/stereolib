import TetraStereo.OneCenter.CarbohydrateImageArtifactAudit
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateFinalImageMeaningData

set_option autoImplicit false



namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings

structure VisionReviewedFinalImageMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  sourcePages : List String
  sourceMeaning : Option FinalImageMeaning
  reviewEvidencePresent : Bool
  reviewerKind : String
  reviewMethod : String
  reviewLimitations : String

def VisionReviewedFinalImageMeaning.complete (entry : VisionReviewedFinalImageMeaning) : Bool :=
  entry.sourceMeaning.isSome && entry.reviewEvidencePresent

def visionReviewedFinalImageMeaningOfPair
    (pair : Carbohydrate1996ImageAudit.ImageArtifact × FinalImageMeaning) :
    VisionReviewedFinalImageMeaning :=
  { artifactData := pair.1.data
    sourcePages := pair.1.sourcePages
    sourceMeaning := some pair.2
    reviewEvidencePresent := true
    reviewerKind := "visionAutomated"
    reviewMethod := "record-4c2815434a0c940c52876f44e1e2ad2c"
    reviewLimitations := "record-e42a7fb58c48c5f975a7c6fb5e2174c0" }

@[simp] theorem vision_reviewed_final_pair_complete
    (pair : Carbohydrate1996ImageAudit.ImageArtifact × FinalImageMeaning) :
    (visionReviewedFinalImageMeaningOfPair pair).complete = true := by
  rfl

@[simp] theorem vision_reviewed_final_pairs_complete
    (pairs : List (Carbohydrate1996ImageAudit.ImageArtifact × FinalImageMeaning)) :
    (pairs.map visionReviewedFinalImageMeaningOfPair).all
        VisionReviewedFinalImageMeaning.complete = true := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih => simp [ih]

end GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter
