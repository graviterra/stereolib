import TetraStereo.OneCenter.IUPACGlobalNonDescriptorAppendix3SourceMeanings
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCanonicalSourceProgram
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192

/-!
# Complete 2,300-row non-descriptor source program

This module assembles the independently reviewed 92-row core batch and the fully materialized
2,208-row parameterized batch.  Their source-family order is not the final manifest order, so the
assembly selects the unique stored entry for each row of `globalNonDescriptorProvisions` and emits
that exact canonical order.  Every selected entry is proved to belong to the combined input batch;
there is no absent-row branch, fallback reference, or synthesized source meaning.

This closes the executable source-program boundary only.  The ten live normative source audits
remain independent inputs to reviewed-semantics and root-certificate issuance.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCompleteSourceProgram

def combinedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCoreSourceMeaning.provisions ++
    GlobalNonDescriptorAppendix3SourceMeanings.advancedMaterializedProvisions

/-- Literal composition of all stored source-meaning entries before canonical reordering. -/
def combinedBatch : GlobalNonDescriptorSourceMeaningBatch combinedProvisions :=
  GlobalNonDescriptorCoreSourceMeaning.batch.append
    GlobalNonDescriptorAppendix3SourceMeanings.advancedMaterializedBatch

@[simp] theorem combined_provision_count : combinedProvisions.length = 2300 := by
  simp [combinedProvisions]

@[simp] theorem combined_entry_count : combinedBatch.entries.length = 2300 := by
  rw [combinedBatch.entries_length, combined_provision_count]

/-- The final Appendix-3 overlay exhausts the canonical set together with the 92-row core. -/
theorem mem_combinedProvisions_iff_canonical (provision : IUPACNormativeProvision) :
    provision ∈ combinedProvisions ↔ provision ∈ globalNonDescriptorProvisions := by
  rw [←
    GlobalNonDescriptorAppendix3SourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  simp only [combinedProvisions, GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions,
    GlobalNonDescriptorAppendix3SourceMeanings.advancedMissingProvisions, List.mem_append,
    List.not_mem_nil, or_false]

private theorem appendix_provisions_eq_prior_missing :
    GlobalNonDescriptorAppendix3SourceMeanings.provisions =
      GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.advancedMissingProvisions := by
  have noImages :
      GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.remainingImageRows = [] :=
    List.eq_nil_of_length_eq_zero
      GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.remaining_image_count
  simp [GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.advancedMissingProvisions,
    noImages, GlobalNonDescriptorAppendix3SourceMeanings.provisions]

private theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorCoreSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorAppendix3SourceMeanings.advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | appendix
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (by
          rw [← appendix_provisions_eq_prior_missing]
          exact appendix)

theorem combined_provisions_nodup : combinedProvisions.Nodup := by
  exact GlobalNonDescriptorCoreSourceMeaning.provisions_nodup.append
    GlobalNonDescriptorAppendix3SourceMeanings.advanced_materialized_nodup
    reviewed_disjoint_advanced_materialized

/-- Set equality plus duplicate-freedom certifies that the source-family batch is a permutation
of the canonical 2,300-row list. -/
theorem combined_provisions_perm_canonical :
    combinedProvisions.Perm globalNonDescriptorProvisions := by
  exact (List.perm_ext_iff_of_nodup combined_provisions_nodup
    globalNonDescriptorProvisions_nodup).2 mem_combinedProvisions_iff_canonical

theorem combined_entry_exists_exact (provision : IUPACNormativeProvision) :
    provision ∈ globalNonDescriptorProvisions ↔
      ∃ entry ∈ combinedBatch.entries, entry.provision = provision := by
  constructor
  · intro canonicalMember
    have combinedMember : provision ∈ combinedProvisions :=
      (mem_combinedProvisions_iff_canonical provision).2 canonicalMember
    have mappedMember :
        provision ∈ combinedBatch.entries.map GlobalNonDescriptorSourceMeaningEntry.provision := by
      rw [combinedBatch.provisions_exact]
      exact combinedMember
    exact List.mem_map.mp mappedMember
  · rintro ⟨entry, entryMember, rfl⟩
    apply (mem_combinedProvisions_iff_canonical entry.provision).1
    rw [← combinedBatch.provisions_exact]
    exact List.mem_map_of_mem entryMember

/-- The unique stored entry for a canonical provision, selected from the complete combined batch. -/
noncomputable def combinedEntryFor
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions) :
    GlobalNonDescriptorSourceMeaningEntry :=
  Classical.choose ((combined_entry_exists_exact provision).1 member)

theorem combinedEntryFor_mem
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions) :
    combinedEntryFor provision member ∈ combinedBatch.entries :=
  (Classical.choose_spec ((combined_entry_exists_exact provision).1 member)).1

@[simp] theorem combinedEntryFor_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions) :
    (combinedEntryFor provision member).provision = provision :=
  (Classical.choose_spec ((combined_entry_exists_exact provision).1 member)).2

/-- Reorder without fallback by mapping over the canonical list with membership attached. -/
noncomputable def canonicalEntries : List GlobalNonDescriptorSourceMeaningEntry :=
  globalNonDescriptorProvisions.attach.map fun provision =>
    combinedEntryFor provision.1 provision.2

@[simp] theorem canonical_entries_provisions_exact :
    canonicalEntries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      globalNonDescriptorProvisions := by
  simp [canonicalEntries]

noncomputable def canonicalManifest : GlobalNonDescriptorCanonicalSourceManifest where
  entries := canonicalEntries
  provisions_exact := canonical_entries_provisions_exact

@[simp] theorem canonical_entry_count : canonicalManifest.entries.length = 2300 := by
  simp [canonicalManifest, canonicalEntries]

/-- Canonical reordering preserves provenance: every output entry is literally one input entry. -/
theorem canonical_entry_from_combined
    (entry : GlobalNonDescriptorSourceMeaningEntry)
    (member : entry ∈ canonicalManifest.entries) :
    entry ∈ combinedBatch.entries := by
  change entry ∈ canonicalEntries at member
  rw [canonicalEntries, List.mem_map] at member
  obtain ⟨provision, _provisionMember, rfl⟩ := member
  exact combinedEntryFor_mem provision.1 provision.2

/-- Caller-free total source-reference program for all 2,300 canonical non-descriptor rows. -/
noncomputable def canonicalSourceProgram : GlobalNonDescriptorSourceReferenceProgram :=
  canonicalManifest.toSourceReferenceProgram

@[simp] theorem canonical_source_supplies_rule
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    canonicalSourceProgram.sourceSuppliesRule provision member = true :=
  rfl

theorem canonical_reference_nonvacuous
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    ∃ input, ∃ observation :
        (canonicalSourceProgram.reference provision member).toReference.Observation,
      input.StructurallyWellFormed ∧
        (canonicalSourceProgram.reference provision member).toReference.Applicable input ∧
          (canonicalSourceProgram.reference provision member).toReference.Judges
            input observation :=
  canonicalManifest.toSourceReferenceProgram_reference_nonvacuous provision member

end GlobalNonDescriptorCompleteSourceProgram
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCompleteSourceProgram.combined_provisions_perm_canonical
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCompleteSourceProgram.canonical_entries_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCompleteSourceProgram.canonical_entry_from_combined
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCompleteSourceProgram.canonical_source_supplies_rule
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCompleteSourceProgram.canonical_reference_nonvacuous
