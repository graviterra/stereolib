import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorSixReviewedImageSourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false











namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorIndexedSourceMeaning

def provisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorIndexedSourceData.provisions ++
    GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions

def batch : GlobalNonDescriptorSourceMeaningBatch provisions :=
  GlobalNonDescriptorIndexedSourceData.batch.append
    GlobalNonDescriptorSixReviewedImageSourceMeanings.visionReviewedGraphLevelBatch

def entries : List GlobalNonDescriptorSourceMeaningEntry := batch.entries

@[simp] theorem provision_count : provisions.length = 595 := by
  simp [provisions]

/-- The indexed batch decomposes into its exact source-family projections, including the final
six transcribed images. -/
theorem mem_provisions_iff_components (provision : IUPACNormativeProvision) :
    provision ∈ provisions ↔
      provision ∈ GlobalNonDescriptorIndexedSourceData.glycolipidProvisions ∨
      provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateScopeParentProvisions ∨
      provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateFoundationProvisions ∨
      provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateNamedParentProvisions ∨
      provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateDerivativeProvisions ∨
      provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateUnsaturatedProvisions ∨
      provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateAlditolAcidProvisions ∨
      provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateHeteroProvisions ∨
      provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateAcetalProvisions ∨
      provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateResidueIonProvisions ∨
      provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateOligosaccharideProvisions ∨
      provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions ∨
      provision ∈ GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions := by
  simp only [provisions, GlobalNonDescriptorIndexedSourceData.provisions,
    GlobalNonDescriptorIndexedSourceData.carbohydrateTextualProvisions,
    GlobalNonDescriptorIndexedSourceData.carbohydrateSourceDataAProvisions,
    GlobalNonDescriptorIndexedSourceData.carbohydrateSourceDataBTextualProvisions,
    List.mem_append, or_assoc]

@[simp] theorem entry_count : entries.length = 595 := by
  rw [entries, batch.entries_length, provision_count]

@[simp] theorem entry_provisions_exact :
    entries.map GlobalNonDescriptorSourceMeaningEntry.provision = provisions := by
  exact batch.provisions_exact

private theorem source_data_disjoint_reviewed_six :
    GlobalNonDescriptorIndexedSourceData.provisions.Disjoint
      GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions := by
  rw [List.disjoint_left]
  intro provision sourceMember reviewedMember
  rw [GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] at reviewedMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp reviewedMember
  cases row with
  | imageArtifact artifact =>
      simp [GlobalNonDescriptorIndexedSourceData.provisions,
        GlobalNonDescriptorIndexedSourceData.carbohydrateTextualProvisions,
        GlobalNonDescriptorIndexedSourceData.glycolipidProvisions,
        GlobalNonDescriptorIndexedSourceData.carbohydrateSourceDataAProvisions,
        GlobalNonDescriptorIndexedSourceData.carbohydrateSourceDataBTextualProvisions,
        GlobalNonDescriptorIndexedSourceData.carbohydrateScopeParentProvisions,
        GlobalNonDescriptorIndexedSourceData.carbohydrateFoundationProvisions,
        GlobalNonDescriptorIndexedSourceData.carbohydrateNamedParentProvisions,
        GlobalNonDescriptorIndexedSourceData.carbohydrateDerivativeProvisions,
        GlobalNonDescriptorIndexedSourceData.carbohydrateUnsaturatedProvisions,
        GlobalNonDescriptorIndexedSourceData.carbohydrateAlditolAcidProvisions,
        GlobalNonDescriptorIndexedSourceData.carbohydrateHeteroProvisions,
        GlobalNonDescriptorIndexedSourceData.carbohydrateAcetalProvisions,
        GlobalNonDescriptorIndexedSourceData.carbohydrateResidueIonProvisions,
        GlobalNonDescriptorIndexedSourceData.carbohydrateOligosaccharideProvisions,
        GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions] at sourceMember

theorem provisions_nodup : provisions.Nodup := by
  exact GlobalNonDescriptorIndexedSourceData.provisions_nodup.append
    GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions_nodup
      source_data_disjoint_reviewed_six

theorem entry_provisions_nodup :
    (entries.map GlobalNonDescriptorSourceMeaningEntry.provision).Nodup := by
  rw [entry_provisions_exact]
  exact provisions_nodup

theorem first_589_entries_are_exact_source_data :
    entries.take 589 = GlobalNonDescriptorIndexedSourceData.entries := by
  simp [entries, batch, GlobalNonDescriptorIndexedSourceData.entries]

theorem final_six_entries_are_exact_vision_reviewed_graph_meanings :
    entries.drop 589 =
      GlobalNonDescriptorSixReviewedImageSourceMeanings.visionReviewedGraphLevelBatch.entries := by
  simp [entries, batch]

theorem every_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (_member : entry ∈ entries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment



private theorem mapped_source_audited
    {Row : Type} (rows : List Row) (wrap : Row → IUPACNormativeProvision)
    (source : IUPACNormativeSource)
    (sourceExact : ∀ row, (wrap row).source = source)
    (audited : IUPACNormativeSource.ProvisionAuditComplete source) :
    (rows.map wrap).Forall fun provision =>
      IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  rw [List.forall_iff_forall_mem]
  intro provision member
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp member
  rw [sourceExact row]
  exact audited

set_option maxRecDepth 4096 in
private theorem source_data_audited
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996)
    (glycolipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .glycolipidRecommendations1997) :
    GlobalNonDescriptorIndexedSourceData.provisions.Forall fun provision =>
      IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  simp only [GlobalNonDescriptorIndexedSourceData.provisions,
    GlobalNonDescriptorIndexedSourceData.carbohydrateTextualProvisions,
    GlobalNonDescriptorIndexedSourceData.carbohydrateSourceDataAProvisions,
    GlobalNonDescriptorIndexedSourceData.carbohydrateSourceDataBTextualProvisions,
    List.forall_append]
  exact ⟨
    mapped_source_audited GlobalNonDescriptorIndexedSourceData.glycolipidRows
      IUPACNormativeProvision.glycolipid1997 .glycolipidRecommendations1997
      (by intro _row; rfl) glycolipidAudited,
    ⟨⟨⟨⟨⟨
      mapped_source_audited GlobalNonDescriptorIndexedSourceData.carbohydrateScopeParentRows
        IUPACNormativeProvision.carbohydrate1996ScopeParent
        .carbohydrateRecommendations1996 (by intro _row; rfl) carbohydrateAudited,
      mapped_source_audited GlobalNonDescriptorIndexedSourceData.carbohydrateFoundationRows
        IUPACNormativeProvision.carbohydrate1996Foundation
        .carbohydrateRecommendations1996 (by intro _row; rfl) carbohydrateAudited⟩,
      mapped_source_audited GlobalNonDescriptorIndexedSourceData.carbohydrateNamedParentRows
        IUPACNormativeProvision.carbohydrate1996NamedParents
        .carbohydrateRecommendations1996 (by intro _row; rfl) carbohydrateAudited⟩,
      mapped_source_audited GlobalNonDescriptorIndexedSourceData.carbohydrateDerivativeRows
        IUPACNormativeProvision.carbohydrate1996Derivatives
        .carbohydrateRecommendations1996 (by intro _row; rfl) carbohydrateAudited⟩,
      mapped_source_audited GlobalNonDescriptorIndexedSourceData.carbohydrateUnsaturatedRows
        IUPACNormativeProvision.carbohydrate1996UnsaturatedBranched
        .carbohydrateRecommendations1996 (by intro _row; rfl) carbohydrateAudited⟩,
      mapped_source_audited GlobalNonDescriptorIndexedSourceData.carbohydrateAlditolAcidRows
        IUPACNormativeProvision.carbohydrate1996AlditolsAcids
        .carbohydrateRecommendations1996 (by intro _row; rfl) carbohydrateAudited⟩,
    ⟨⟨⟨⟨
      mapped_source_audited GlobalNonDescriptorIndexedSourceData.carbohydrateHeteroRows
        IUPACNormativeProvision.carbohydrate1996HeteroSubstitutionAnhydride
        .carbohydrateRecommendations1996 (by intro _row; rfl) carbohydrateAudited,
      mapped_source_audited GlobalNonDescriptorIndexedSourceData.carbohydrateAcetalRows
        IUPACNormativeProvision.carbohydrate1996Acetals
        .carbohydrateRecommendations1996 (by intro _row; rfl) carbohydrateAudited⟩,
      mapped_source_audited GlobalNonDescriptorIndexedSourceData.carbohydrateResidueIonRows
        IUPACNormativeProvision.carbohydrate1996ResiduesIons
        .carbohydrateRecommendations1996 (by intro _row; rfl) carbohydrateAudited⟩,
      mapped_source_audited GlobalNonDescriptorIndexedSourceData.carbohydrateOligosaccharideRows
        IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides
        .carbohydrateRecommendations1996 (by intro _row; rfl) carbohydrateAudited⟩,
      mapped_source_audited GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixRows
        IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary
        .carbohydrateRecommendations1996 (by intro _row; rfl) carbohydrateAudited⟩⟩

set_option maxRecDepth 4096 in
private theorem reviewed_six_audited
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996) :
    GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions.Forall fun provision =>
      IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  exact mapped_source_audited GlobalNonDescriptorSixReviewedImageSourceMeanings.rows
    IUPACNormativeProvision.carbohydrate1996ImageArtifact
    .carbohydrateRecommendations1996 (by intro _row; rfl) carbohydrateAudited

set_option maxRecDepth 4096 in


theorem source_audit_complete_of_carbohydrate_and_glycolipid
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996)
    (glycolipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .glycolipidRecommendations1997)
    (provision : IUPACNormativeProvision) (member : provision ∈ provisions) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have everyAudited : provisions.Forall fun row =>
      IUPACNormativeSource.ProvisionAuditComplete row.source := by
    rw [provisions, List.forall_append]
    exact ⟨source_data_audited carbohydrateAudited glycolipidAudited,
      reviewed_six_audited carbohydrateAudited⟩
  exact (List.forall_iff_forall_mem.mp everyAudited) provision member

end GlobalNonDescriptorIndexedSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorIndexedSourceMeaning.entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorIndexedSourceMeaning.mem_provisions_iff_components
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorIndexedSourceMeaning.first_589_entries_are_exact_source_data
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorIndexedSourceMeaning.final_six_entries_are_exact_vision_reviewed_graph_meanings
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorIndexedSourceMeaning.every_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorIndexedSourceMeaning.source_audit_complete_of_carbohydrate_and_glycolipid
