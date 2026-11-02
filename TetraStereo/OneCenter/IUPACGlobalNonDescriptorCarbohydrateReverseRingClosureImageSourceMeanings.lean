import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.remainingImageRows

def rows : List Carbohydrate1996ImageAudit.Provision := priorRemainingImageRows.take 2

def artifactOf : Carbohydrate1996ImageAudit.Provision →
    Carbohydrate1996ImageAudit.ImageArtifact
  | .imageArtifact artifact => artifact

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := rows.map artifactOf

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 2 := by
  simp [rows, priorRemainingImageRows]

@[simp] theorem artifact_count : artifacts.length = 2 := by simp [artifacts]
@[simp] theorem provision_count : provisions.length = 2 := by simp [provisions]

set_option maxRecDepth 4096 in
@[simp] theorem frozen_artifact_data_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.data =
      [ ⟨"2carb/2C0gif/064A.GIF", "50f27d74447565d1736487c517c82e382469ca828e872c22710a071dcc1ae167", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/064B.GIF", "7229d2973e25eb1821a65593fbde3fa86b3321b16801416fe1757b0370a090a2", .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 2 ["06n07.html"] := by
  decide

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

structure RingClosure where
  potentialCarbonylLocant : Nat
  hydroxylLocant : Nat
  ringSize : Nat
  deriving DecidableEq, Repr

inductive AssignmentKind where
  | alpha | beta | absoluteR | absoluteS
  deriving DecidableEq, Repr

structure AnomericAssignment where
  anomericCarbonLocant : Nat
  kind : AssignmentKind
  deriving DecidableEq, Repr

structure ReverseRingClosureMeaning where
  publishedName : String
  parentFischerHydroxylSides :
    List (Nat × Carbohydrate1996ImageAudit.FischerHorizontalSide)
  anomericReferenceAtomLocant : Nat
  ringClosures : List RingClosure
  assignments : List AnomericAssignment
  isopropylideneBridge? : Option (Nat × Nat)
  remainingAldehydeLocants : List Nat
  deriving DecidableEq, Repr

def meanings : List ReverseRingClosureMeaning :=
  [ { publishedName := "(6R)-D-gluco-hexodialdo-6,2-pyranose"
      parentFischerHydroxylSides :=
        [(2, .right), (3, .left), (4, .right), (5, .right)]
      anomericReferenceAtomLocant := 5
      ringClosures := [⟨6, 2, 6⟩]
      assignments := [⟨6, .absoluteR⟩]
      isopropylideneBridge? := none
      remainingAldehydeLocants := [1] }
  , { publishedName :=
        "(6S)-1,2-O-isopropylidene-alpha-D-gluco-hexodialdo-1,4:6,3-difuranose"
      parentFischerHydroxylSides :=
        [(2, .right), (3, .left), (4, .right), (5, .right)]
      anomericReferenceAtomLocant := 5
      ringClosures := [⟨1, 4, 5⟩, ⟨6, 3, 5⟩]
      assignments := [⟨1, .alpha⟩, ⟨6, .absoluteS⟩]
      isopropylideneBridge? := some (1, 2)
      remainingAldehydeLocants := [] } ]

@[simp] theorem meanings_exact : meanings =
    [ { publishedName := "(6R)-D-gluco-hexodialdo-6,2-pyranose"
        parentFischerHydroxylSides :=
          [(2, .right), (3, .left), (4, .right), (5, .right)]
        anomericReferenceAtomLocant := 5
        ringClosures := [⟨6, 2, 6⟩]
        assignments := [⟨6, .absoluteR⟩]
        isopropylideneBridge? := none
        remainingAldehydeLocants := [1] }
    , { publishedName :=
          "(6S)-1,2-O-isopropylidene-alpha-D-gluco-hexodialdo-1,4:6,3-difuranose"
        parentFischerHydroxylSides :=
          [(2, .right), (3, .left), (4, .right), (5, .right)]
        anomericReferenceAtomLocant := 5
        ringClosures := [⟨1, 4, 5⟩, ⟨6, 3, 5⟩]
        assignments := [⟨1, .alpha⟩, ⟨6, .absoluteS⟩]
        isopropylideneBridge? := some (1, 2)
        remainingAldehydeLocants := [] } ] := rfl

def RingClosure.wellFormed (closure : RingClosure) : Bool :=
  closure.potentialCarbonylLocant ≠ closure.hydroxylLocant &&
    closure.ringSize = Nat.max closure.potentialCarbonylLocant closure.hydroxylLocant -
      Nat.min closure.potentialCarbonylLocant closure.hydroxylLocant + 2

def AnomericAssignment.allowedForReference
    (referenceLocant : Nat) (assignment : AnomericAssignment) : Bool :=
  if assignment.anomericCarbonLocant < referenceLocant then
    match assignment.kind with
    | .alpha | .beta => true
    | .absoluteR | .absoluteS => false
  else if referenceLocant < assignment.anomericCarbonLocant then
    match assignment.kind with
    | .alpha | .beta => false
    | .absoluteR | .absoluteS => true
  else false

def ReverseRingClosureMeaning.wellFormed (meaning : ReverseRingClosureMeaning) : Bool :=
  meaning.parentFischerHydroxylSides.length = 4 &&
    (meaning.parentFischerHydroxylSides.map Prod.fst).Nodup &&
      meaning.ringClosures.Nodup && meaning.assignments.Nodup &&
        meaning.ringClosures.all RingClosure.wellFormed &&
          (meaning.ringClosures.map RingClosure.potentialCarbonylLocant) =
            (meaning.assignments.map AnomericAssignment.anomericCarbonLocant) &&
            meaning.assignments.all
              (AnomericAssignment.allowedForReference meaning.anomericReferenceAtomLocant) &&
              meaning.remainingAldehydeLocants.Nodup && !meaning.publishedName.isEmpty

structure ReverseClosureRule where
  alphaBetaOnlyWhenAnomericLocantBelowReference : Bool
  higherAnomericLocantUsesSequenceRuleRorS : Bool
  ringLocantsCitePotentialCarbonylFirst : Bool
  ringLocantsCiteHydroxylSecond : Bool
  ringLocantsMayPrecedeRingSizeSuffix : Bool
  deriving DecidableEq, Repr

def reverseClosureRule : ReverseClosureRule where
  alphaBetaOnlyWhenAnomericLocantBelowReference := true
  higherAnomericLocantUsesSequenceRuleRorS := true
  ringLocantsCitePotentialCarbonylFirst := true
  ringLocantsCiteHydroxylSecond := true
  ringLocantsMayPrecedeRingSizeSuffix := true

def sourceMeaning? : String → Option ReverseRingClosureMeaning
  | "2carb/2C0gif/064A.GIF" => meanings[0]?
  | "2carb/2C0gif/064B.GIF" => meanings[1]?
  | _ => none

def all_meanings_well_formed : Bool :=
  artifacts.all fun artifact =>
    match sourceMeaning? artifact.data.relativePath with
    | some meaning => meaning.wellFormed
    | none => false

structure VisionReviewedImageMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  sourcePages : List String
  sourceMeaning : Option ReverseRingClosureMeaning
  rule : ReverseClosureRule
  reviewerKind : String
  reviewMethod : String
  reviewLimitations : String
  deriving DecidableEq, Repr

def visionReviewedImageMeaning
    (row : Carbohydrate1996ImageAudit.Provision) : VisionReviewedImageMeaning :=
  match row with
  | .imageArtifact artifact =>
      { artifactData := artifact.data
        sourcePages := artifact.sourcePages
        sourceMeaning := sourceMeaning? artifact.data.relativePath
        rule := reverseClosureRule
        reviewerKind := "visionAutomated"
        reviewMethod := "record-1b7e5add3283e6b5f54eaa2fa5deba2f"
        reviewLimitations := "automated-record-dea0f86743dc0740de4fb10ba17511a4" }

def visionReviewedGraphLevelBatch :
    GlobalNonDescriptorSourceMeaningBatch provisions := by
  simpa [provisions] using
    GlobalNonDescriptorIndexedSourceData.totalMeaningBatch rows
      IUPACNormativeProvision.carbohydrate1996ImageArtifact
      visionReviewedImageMeaning (by intro _row; rfl)

@[simp] theorem vision_reviewed_entry_count :
    visionReviewedGraphLevelBatch.entries.length = 2 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact advance from the prior 1,665/543 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 2

@[simp] theorem remaining_image_count : remainingImageRows.length = 370 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 2 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1667 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 541 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.advancedMissingProvisions := by
  have imageEquality := congrArg
    (List.map IUPACNormativeProvision.carbohydrate1996ImageArtifact)
    rows_append_remaining_eq_prior
  let remainingProvisions :=
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact
  have swapPrefix :
      (provisions ++ sourceProvisions .blueBook2013Appendix3).Perm
        (sourceProvisions .blueBook2013Appendix3 ++ provisions) :=
    List.perm_append_comm
  have reordered :
      (provisions ++ advancedMissingProvisions).Perm
        (sourceProvisions .blueBook2013Appendix3 ++
          (provisions ++ remainingProvisions)) := by
    change (provisions ++
        (sourceProvisions .blueBook2013Appendix3 ++ remainingProvisions)).Perm
      (sourceProvisions .blueBook2013Appendix3 ++
        (provisions ++ remainingProvisions))
    simpa only [List.append_assoc] using swapPrefix.append_right remainingProvisions
  have selectedThenRemaining :
      provisions ++ remainingProvisions =
        priorRemainingImageRows.map
          IUPACNormativeProvision.carbohydrate1996ImageArtifact := by
    simpa [provisions, remainingProvisions, List.map_append] using imageEquality
  calc
    (provisions ++ advancedMissingProvisions).Perm _ := reordered
    _ = sourceProvisions .blueBook2013Appendix3 ++
        priorRemainingImageRows.map
          IUPACNormativeProvision.carbohydrate1996ImageArtifact := by
      rw [selectedThenRemaining]
    _ = GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1667 ∧
        advancedMissingProvisions.length = 541 ∧
          92 + 1667 + 541 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.meanings_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
