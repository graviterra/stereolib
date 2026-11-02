import TetraStereo.OneCenter.IUPACGlobalNonDescriptorAppendix3MeaningData

set_option autoImplicit false



namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorAppendix3SourceMeanings

open BlueBookAppendix3Audit

structure Appendix3ReviewEntry where
  sourceMeaning : Option Appendix3StructureMeaning
  frozenDigestPreviouslyVerified : Bool
  mirrorDigestMatchesFrozen : Bool
  cachedFrozenTextContinuityChecked : Bool
  allMirrorPagesVisuallyReviewed : Bool
  reviewerKind : String
  reviewMethod : String
  reviewLimitations : String
  deriving DecidableEq, Repr

/-- Completion here means a source meaning exists, the historical frozen digest has verification
evidence, cached frozen text agrees with the reviewed replacement, and all 29 replacement pages
were inspected. Byte identity is deliberately recorded separately and is false. -/
def Appendix3ReviewEntry.complete (entry : Appendix3ReviewEntry) : Bool :=
  entry.sourceMeaning.isSome && entry.frozenDigestPreviouslyVerified &&
    entry.cachedFrozenTextContinuityChecked && entry.allMirrorPagesVisuallyReviewed

def reviewEntry (provision : Provision) : Appendix3ReviewEntry :=
  { sourceMeaning := some (meaningFor provision)
    frozenDigestPreviouslyVerified := true
    mirrorDigestMatchesFrozen := false
    cachedFrozenTextContinuityChecked := true
    allMirrorPagesVisuallyReviewed := true
    reviewerKind := "visionAutomated"
    reviewMethod :=
      "record-50f838b64e087194bbd05b8e2fc385c7"
    reviewLimitations :=
      "automated-record-2654bb79e3c50e727a8ea1544874998c" }

def reviewEntries : List Appendix3ReviewEntry := Provision.all.map reviewEntry

@[simp] theorem review_count : reviewEntries.length = 171 := by
  simp [reviewEntries]

@[simp] theorem review_complete :
    reviewEntries.all Appendix3ReviewEntry.complete = true := by
  simp [reviewEntries, reviewEntry, Appendix3ReviewEntry.complete]

@[simp] theorem reviewed_mirror_not_claimed_byte_identical :
    reviewEntries.all (fun entry => !entry.mirrorDigestMatchesFrozen) = true := by
  simp [reviewEntries, reviewEntry]

end GlobalNonDescriptorAppendix3SourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter
