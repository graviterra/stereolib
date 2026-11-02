import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCoreSourceMeaningBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorSourceMeaningReadiness

set_option autoImplicit false

/-!
# Kernel-certified live source-meaning frontier

The baseline readiness inventory predates materialized source batches.  The reviewed 92-row core
batch is its literal prefix, so this module uses `take`/`drop` to expose the exact live frontier
without filtering or constructing a second finite-set model of the 1,705 baseline rows:

* 92 reviewed source-meaning rows;
* 1,613 still-baseline-partial rows; and
* 595 missing-transcription rows.

The three lists are pairwise disjoint and exhaust the canonical 2,300-row non-descriptor
partition.  Thus release documentation can consume one kernel theorem rather than combining
independent counts arithmetically.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

namespace GlobalNonDescriptorSourceMeaningProgress

def reviewedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCoreSourceMeaning.provisions

/-- The untouched suffix of the pre-materialization 1,705-row baseline. -/
def residualPartiallyFormalizedProvisions : List IUPACNormativeProvision :=
  globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions.drop 92

@[simp] theorem reviewed_count : reviewedProvisions.length = 92 := by
  exact GlobalNonDescriptorCoreSourceMeaning.provision_count

theorem reviewed_nodup : reviewedProvisions.Nodup :=
  GlobalNonDescriptorCoreSourceMeaning.provisions_nodup

private theorem source_of_reviewed_member
    {provision : IUPACNormativeProvision} (member : provision ∈ reviewedProvisions) :
    provision.source = .blueBook2013P9 ∨
      provision.source = .graphicalRepresentation2006 ∨
        provision.source = .redBook2005IR9 := by
  simp only [reviewedProvisions, GlobalNonDescriptorCoreSourceMeaning.provisions,
    List.mem_append] at member
  rcases member with (leading | graphical) | trailing
  · simp [GlobalNonDescriptorCoreAuxiliarySourceRow.leadingProvisions] at leading
    rcases leading with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact Or.inl rfl
  · exact Or.inr (Or.inl
      ((mem_sourceProvisions_iff provision .graphicalRepresentation2006).1 graphical))
  · simp [GlobalNonDescriptorCoreAuxiliarySourceRow.trailingProvisions] at trailing
    rcases trailing with rfl | rfl
    all_goals exact Or.inr (Or.inr rfl)

private theorem source_of_missing_member
    {provision : IUPACNormativeProvision}
    (member : provision ∈ globalNonDescriptorMissingSourceMeaningProvisions) :
    provision.source = .blueBook2013Appendix3 ∨
      provision.source = .carbohydrateRecommendations1996 := by
  rw [mem_globalNonDescriptorMissingSourceMeaningProvisions_iff] at member
  rcases member with appendix | image
  · exact Or.inl ((mem_sourceProvisions_iff provision .blueBook2013Appendix3).1 appendix)
  · obtain ⟨imageProvision, _notTranscribed, rfl⟩ := List.mem_map.mp image
    exact Or.inr rfl

private theorem reviewed_not_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ reviewedProvisions) :
    provision ∉ globalNonDescriptorMissingSourceMeaningProvisions := by
  intro missing
  rcases source_of_reviewed_member member with p9 | graphical | ir9 <;>
    rcases source_of_missing_member missing with appendix | carbohydrate <;> simp_all

def parameterizedBaselineTail : List IUPACNormativeProvision :=
  (parameterizedProvisions.filter fun provision => !descriptorAssignmentBearing? provision).filter
    fun provision => !(decide (provision ∈ globalNonDescriptorMissingSourceMeaningProvisions))

/-- Source order puts the complete core-negative block before every parameterized baseline row. -/
theorem baseline_eq_reviewed_append_parameterizedTail :
    globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions =
      reviewedProvisions ++ parameterizedBaselineTail := by
  simp only [globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions,
    globalNonDescriptorProvisions, descriptorAssignmentNegativeProvisions,
    all_eq_core_append_parameterized, List.filter_append, parameterizedBaselineTail]
  rw [← GlobalNonDescriptorCoreSourceMeaning.provisions_eq_core_negative]
  have coreFilter :
      reviewedProvisions.filter
          (fun provision =>
            !(decide (provision ∈ globalNonDescriptorMissingSourceMeaningProvisions))) =
        reviewedProvisions := by
    apply List.filter_eq_self.2
    intro provision member
    simpa using reviewed_not_missing member
  change
    reviewedProvisions.filter
          (fun provision =>
            !(decide (provision ∈ globalNonDescriptorMissingSourceMeaningProvisions))) ++
        parameterizedBaselineTail =
      reviewedProvisions ++ parameterizedBaselineTail
  rw [coreFilter]

/-- The materialized core batch is exactly the first 92 rows of the old partial inventory. -/
theorem reviewed_eq_take_baseline :
    reviewedProvisions =
      globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions.take 92 := by
  rw [baseline_eq_reviewed_append_parameterizedTail]
  simp

/-- The reviewed batch and the residual suffix reconstruct the old baseline literally. -/
theorem reviewed_append_residual_eq_baseline :
    reviewedProvisions ++ residualPartiallyFormalizedProvisions =
      globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions := by
  rw [reviewed_eq_take_baseline, residualPartiallyFormalizedProvisions]
  exact List.take_append_drop 92 _

/-- Removing the literal 92-row reviewed prefix leaves exactly the filtered parameterized
baseline.  This small equality lets later progress refinements reason by source-family blocks
instead of reducing the complete 1,613-row suffix. -/
theorem residual_eq_parameterizedBaselineTail :
    residualPartiallyFormalizedProvisions = parameterizedBaselineTail := by
  apply List.append_right_injective reviewedProvisions
  change reviewedProvisions ++ residualPartiallyFormalizedProvisions =
    reviewedProvisions ++ parameterizedBaselineTail
  rw [reviewed_append_residual_eq_baseline,
    baseline_eq_reviewed_append_parameterizedTail]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- The parameterized manifest list contains every row of exactly the parameterized constructor
families.  This converse to `parameterizedProvisions_are_parameterized` avoids repeatedly
normalizing the 2,208-row source list in downstream family proofs. -/
theorem mem_parameterizedProvisions_iff_isParameterized
    (provision : IUPACNormativeProvision) :
    provision ∈ parameterizedProvisions ↔ isParameterizedProvision provision = true := by
  constructor
  · exact parameterizedProvisions_are_parameterized provision
  · intro parameterized
    cases provision <;> simp_all [isParameterizedProvision, parameterizedProvisions]

private theorem reviewed_append_residual_nodup :
    (reviewedProvisions ++ residualPartiallyFormalizedProvisions).Nodup := by
  rw [reviewed_append_residual_eq_baseline]
  exact globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions_nodup

theorem residualPartiallyFormalized_nodup :
    residualPartiallyFormalizedProvisions.Nodup :=
  List.Nodup.of_append_right reviewed_append_residual_nodup

@[simp] theorem residualPartiallyFormalized_count :
    residualPartiallyFormalizedProvisions.length = 1613 := by
  have count := congrArg List.length reviewed_append_residual_eq_baseline
  simp only [List.length_append, reviewed_count,
    globalNonDescriptorPartiallyFormalizedSourceMeaningProvisionCount] at count
  omega

theorem reviewed_subset_baselinePartiallyFormalized
    {provision : IUPACNormativeProvision} (member : provision ∈ reviewedProvisions) :
    provision ∈ globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions := by
  rw [← reviewed_append_residual_eq_baseline]
  exact List.mem_append_left _ member

theorem residual_subset_baselinePartiallyFormalized
    {provision : IUPACNormativeProvision}
    (member : provision ∈ residualPartiallyFormalizedProvisions) :
    provision ∈ globalNonDescriptorPartiallyFormalizedSourceMeaningProvisions := by
  rw [← reviewed_append_residual_eq_baseline]
  exact List.mem_append_right _ member

theorem reviewed_disjoint_residual :
    List.Disjoint reviewedProvisions residualPartiallyFormalizedProvisions :=
  List.disjoint_of_nodup_append reviewed_append_residual_nodup

theorem reviewed_disjoint_missing :
    List.Disjoint reviewedProvisions globalNonDescriptorMissingSourceMeaningProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  have baseline := reviewed_subset_baselinePartiallyFormalized reviewed
  exact (List.disjoint_left.mp
    globalNonDescriptorSourceMeaningReadinessPartition_disjoint missing baseline)

theorem residual_disjoint_missing :
    List.Disjoint residualPartiallyFormalizedProvisions
      globalNonDescriptorMissingSourceMeaningProvisions := by
  rw [List.disjoint_left]
  intro provision residual missing
  have baseline := residual_subset_baselinePartiallyFormalized residual
  exact (List.disjoint_left.mp
    globalNonDescriptorSourceMeaningReadinessPartition_disjoint missing baseline)

/-- Exact live frontier, in membership form. -/
theorem mem_reviewed_or_residual_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ reviewedProvisions ∨
      provision ∈ residualPartiallyFormalizedProvisions ∨
        provision ∈ globalNonDescriptorMissingSourceMeaningProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [globalNonDescriptorSourceMeaningReadinessPartition_exact]
  rw [← reviewed_append_residual_eq_baseline]
  simp only [List.mem_append]
  constructor
  · rintro (reviewed | residual | missing)
    · exact Or.inr (Or.inl reviewed)
    · exact Or.inr (Or.inr residual)
    · exact Or.inl missing
  · rintro (missing | reviewed | residual)
    · exact Or.inr (Or.inr missing)
    · exact Or.inl reviewed
    · exact Or.inr (Or.inl residual)

/-- Certified release-status arithmetic attached to the exact disjoint/exhaustive lists. -/
theorem live_frontier_counts :
    reviewedProvisions.length = 92 ∧
      residualPartiallyFormalizedProvisions.length = 1613 ∧
        globalNonDescriptorMissingSourceMeaningProvisions.length = 595 ∧
          92 + 1613 + 595 = 2300 := by
  exact ⟨reviewed_count, residualPartiallyFormalized_count,
    globalNonDescriptorMissingSourceMeaningProvisionCount, by omega⟩

end GlobalNonDescriptorSourceMeaningProgress

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSourceMeaningProgress.reviewed_eq_take_baseline
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSourceMeaningProgress.reviewed_append_residual_eq_baseline
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSourceMeaningProgress.residual_eq_parameterizedBaselineTail
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSourceMeaningProgress.mem_parameterizedProvisions_iff_isParameterized
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSourceMeaningProgress.mem_reviewed_or_residual_or_missing_iff
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSourceMeaningProgress.live_frontier_counts
