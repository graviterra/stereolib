import TetraStereo.OneCenter.IUPACNormativeManifestCore
import TetraStereo.KernelOnly

set_option autoImplicit false









namespace TetraStereo.OneCenter
namespace IUPACNormativeCandidateConstructionManifest

def candidateSchema : String := "tetrastereo.normative-candidate.v1"

def validationSchema : String := "tetrastereo.normative-candidate-validation.v1"

structure CandidateFamilyManifest where
  source : IUPACNormativeSource
  targetCount : Nat
  concreteCount : Nat
  moleculeFamilyCount : Nat
  glyphCount : Nat
  sourceMeaningCount : Nat
  atomCount : Nat
  bondCount : Nat
  attachmentPointCount : Nat
  candidateLedgerSha256 : String
  sourceFidelityReviewComplete : Bool
  deriving DecidableEq, Repr

namespace CandidateFamilyManifest

def internallyConsistent (manifest : CandidateFamilyManifest) : Bool :=
  manifest.targetCount ==
    manifest.concreteCount + manifest.moleculeFamilyCount + manifest.glyphCount +
      manifest.sourceMeaningCount

end CandidateFamilyManifest

def familyManifests : List CandidateFamilyManifest :=
  [ { source := .blueBook2013P10
      targetCount := 473
      concreteCount := 414
      moleculeFamilyCount := 59
      glyphCount := 0
      sourceMeaningCount := 0
      atomCount := 11566
      bondCount := 11714
      attachmentPointCount := 121
      candidateLedgerSha256 :=
        "ca844781c2e8bc28a58cfc75b0356ebe449a00fd041c3d8a605217fd0aa4512e"
      sourceFidelityReviewComplete := false }
  , { source := .blueBook2013Appendix3
      targetCount := 171
      concreteCount := 164
      moleculeFamilyCount := 7
      glyphCount := 0
      sourceMeaningCount := 0
      atomCount := 4594
      bondCount := 5037
      attachmentPointCount := 7
      candidateLedgerSha256 :=
        "71ff6e329ffd2cb0c8c8be96d20912debe54763f811d1fdbf682eb805dafe541"
      sourceFidelityReviewComplete := false }
  , { source := .steroidRecommendations1989
      targetCount := 68
      concreteCount := 59
      moleculeFamilyCount := 9
      glyphCount := 0
      sourceMeaningCount := 0
      atomCount := 3528
      bondCount := 4062
      attachmentPointCount := 19
      candidateLedgerSha256 :=
        "7a1fc195e8eb765d27f31056bdd2b48b44e383d6d65b54363e40952df58d113e"
      sourceFidelityReviewComplete := false }
  , { source := .carotenoidRules1974
      targetCount := 48
      concreteCount := 33
      moleculeFamilyCount := 15
      glyphCount := 0
      sourceMeaningCount := 0
      atomCount := 1730
      bondCount := 1756
      attachmentPointCount := 28
      candidateLedgerSha256 :=
        "fdbdaef95cc0de6cbea63a600b5bbfc23f5dc8f916b50652daa59361714de84e"
      sourceFidelityReviewComplete := false }
  , { source := .retinoidRecommendations1981
      targetCount := 14
      concreteCount := 10
      moleculeFamilyCount := 4
      glyphCount := 0
      sourceMeaningCount := 0
      atomCount := 325
      bondCount := 325
      attachmentPointCount := 5
      candidateLedgerSha256 :=
        "3591004050709c8cfc3478c751719d26bcc15187cbe69fc6c6b8bcc3446d397b"
      sourceFidelityReviewComplete := false }
  , { source := .carbohydrateRecommendations1996
      targetCount := 425
      concreteCount := 0
      moleculeFamilyCount := 0
      glyphCount := 0
      sourceMeaningCount := 425
      atomCount := 0
      bondCount := 0
      attachmentPointCount := 0
      candidateLedgerSha256 :=
        "8724cbb92e2584bc7bb99dc667e5c574a6bfdee7af222e8f9125b519174984c9"
      sourceFidelityReviewComplete := false }
  , { source := .aminoAcidPeptideRecommendations1983
      targetCount := 95
      concreteCount := 27
      moleculeFamilyCount := 68
      glyphCount := 0
      sourceMeaningCount := 0
      atomCount := 1277
      bondCount := 761
      attachmentPointCount := 579
      candidateLedgerSha256 :=
        "bd517b0ed7a4d4c158c093e2386976d81a7c0b7094ab0a5ba3dc4dc006b75eae"
      sourceFidelityReviewComplete := false }
  , { source := .cyclitolRecommendations1973
      targetCount := 42
      concreteCount := 41
      moleculeFamilyCount := 1
      glyphCount := 0
      sourceMeaningCount := 0
      atomCount := 600
      bondCount := 596
      attachmentPointCount := 1
      candidateLedgerSha256 :=
        "35030d67954b6517470f2343a6be42b684dd92ddb62ee4ae64d62ad93cbe75ea"
      sourceFidelityReviewComplete := false }
  , { source := .lipidRecommendations1976
      targetCount := 21
      concreteCount := 1
      moleculeFamilyCount := 20
      glyphCount := 0
      sourceMeaningCount := 0
      atomCount := 304
      bondCount := 284
      attachmentPointCount := 54
      candidateLedgerSha256 :=
        "9fee9e501ab7a9a40aac1a89622df8b3bbc45a7b4d6cddccf81a50e0484a304f"
      sourceFidelityReviewComplete := false }
  , { source := .glycolipidRecommendations1997
      targetCount := 13
      concreteCount := 1
      moleculeFamilyCount := 9
      glyphCount := 3
      sourceMeaningCount := 0
      atomCount := 125
      bondCount := 101
      attachmentPointCount := 31
      candidateLedgerSha256 :=
        "69587faa813e208bee4caea869e5d78d8ab168bd81cdb00e92b76e6b410cc315"
      sourceFidelityReviewComplete := false }
  ]

@[simp] theorem family_manifest_count_exact : familyManifests.length = 10 := by
  decide

@[simp] theorem every_family_manifest_internally_consistent :
    familyManifests.all CandidateFamilyManifest.internallyConsistent = true := by
  decide

@[simp] theorem candidate_target_count_exact :
    (familyManifests.map CandidateFamilyManifest.targetCount).sum = 1370 := by
  decide

@[simp] theorem concrete_candidate_count_exact :
    (familyManifests.map CandidateFamilyManifest.concreteCount).sum = 750 := by
  decide

@[simp] theorem molecule_family_candidate_count_exact :
    (familyManifests.map CandidateFamilyManifest.moleculeFamilyCount).sum = 192 := by
  decide

@[simp] theorem glyph_candidate_count_exact :
    (familyManifests.map CandidateFamilyManifest.glyphCount).sum = 3 := by
  decide

@[simp] theorem source_meaning_candidate_count_exact :
    (familyManifests.map CandidateFamilyManifest.sourceMeaningCount).sum = 425 := by
  decide

@[simp] theorem candidate_atom_count_exact :
    (familyManifests.map CandidateFamilyManifest.atomCount).sum = 24049 := by
  decide

@[simp] theorem candidate_bond_count_exact :
    (familyManifests.map CandidateFamilyManifest.bondCount).sum = 24636 := by
  decide

@[simp] theorem candidate_attachment_point_count_exact :
    (familyManifests.map CandidateFamilyManifest.attachmentPointCount).sum = 845 := by
  decide

@[simp] theorem every_candidate_family_remains_unreviewed :
    familyManifests.all (fun manifest => !manifest.sourceFidelityReviewComplete) = true := by
  decide

end IUPACNormativeCandidateConstructionManifest
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeCandidateConstructionManifest.family_manifest_count_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeCandidateConstructionManifest.candidate_target_count_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeCandidateConstructionManifest.every_candidate_family_remains_unreviewed
