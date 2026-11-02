import TetraStereo.OneCenter.IUPACGlobalNonDescriptorMaterializedSourceMeaningBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorSourceMeaningProgress
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Exact live materialized source-meaning frontier

This module proves that all 1,613 rows of the frozen residual baseline now have materialized
source meanings. The baseline-partial remainder is empty. The proof is assembled from
source-family partitions; it does not evaluate the aggregate inventory.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorMaterializedSourceMeaningProgress

def materializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorMaterializedSourceMeaning.provisions

def remainingPartiallyFormalizedProvisions : List IUPACNormativeProvision :=
  []

theorem remaining_provisions_exact :
    remainingPartiallyFormalizedProvisions = [] :=
  rfl

theorem mem_residual_iff_parameterized_and_not_missing
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.residualPartiallyFormalizedProvisions ↔
      provision ∈ parameterizedProvisions ∧
        provision ∉ globalNonDescriptorMissingSourceMeaningProvisions := by
  rw [GlobalNonDescriptorSourceMeaningProgress.residual_eq_parameterizedBaselineTail]
  simp only [GlobalNonDescriptorSourceMeaningProgress.parameterizedBaselineTail,
    List.mem_filter]
  constructor
  · rintro ⟨⟨parameterized, _negative⟩, notMissing⟩
    exact ⟨parameterized, by simpa using notMissing⟩
  · rintro ⟨parameterized, notMissing⟩
    have parameterizedShape := parameterizedProvisions_are_parameterized provision parameterized
    have classifierFalse :=
      descriptorAssignmentBearing?_eq_false_of_parameterizedShape provision parameterizedShape
    exact ⟨⟨parameterized, by simp [classifierFalse]⟩, by simpa using notMissing⟩

private theorem mem_glycolipid_materialized_iff_source (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorIndexedSourceData.glycolipidProvisions ∨
        provision ∈ GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions ↔
      provision ∈ sourceProvisions .glycolipidRecommendations1997 := by
  rw [← List.mem_append,
    GlobalNonDescriptorGlycolipidSourceMeaning.materialized_order_perm_source.mem_iff]

private theorem mem_scope_materialized_iff_source (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateScopeParentProvisions ∨
        provision ∈ GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions ↔
      provision ∈ carbohydrate1996ScopeParentSemanticsSlice := by
  rw [or_comm, ← List.mem_append,
    GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completion_then_indexed_exact_source_order]

private theorem mem_foundation_materialized_iff_source (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateFoundationProvisions ∨
        provision ∈ GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions ↔
      provision ∈ carbohydrate1996FoundationSemanticsSlice := by
  rw [or_comm, ← List.mem_append,
    GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completion_then_indexed_exact_source_order]

private theorem mem_named_parent_materialized_iff_source (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateNamedParentProvisions ∨
        provision ∈ GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions ↔
      provision ∈ carbohydrate1996NamedParentsSemanticsSlice := by
  rw [or_comm, ← List.mem_append,
    GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completion_then_indexed_exact_source_order]

private theorem mem_derivative_materialized_iff_source (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateDerivativeProvisions ∨
        provision ∈ GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions ↔
      provision ∈ carbohydrate1996DerivativesSemanticsSlice := by
  rw [or_comm, ← List.mem_append,
    GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completion_then_indexed_exact_source_order]

private theorem mem_unsaturated_materialized_iff_source (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateUnsaturatedProvisions ∨
        provision ∈ GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions ↔
      provision ∈ carbohydrate1996UnsaturatedBranchedSemanticsSlice := by
  rw [or_comm, ← List.mem_append,
    GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completion_then_indexed_exact_source_order]

private theorem mem_alditol_materialized_iff_source (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateAlditolAcidProvisions ∨
        provision ∈ GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions ↔
      provision ∈ carbohydrate1996AlditolsAcidsSemanticsSlice := by
  rw [or_comm, ← List.mem_append,
    GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completion_then_indexed_exact_source_order]

private theorem mem_hetero_materialized_iff_source (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateHeteroProvisions ∨
        provision ∈ GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionProvisions ↔
      provision ∈ carbohydrate1996HeteroSubstitutionAnhydrideSemanticsSlice := by
  rw [or_comm, ← List.mem_append,
    GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completion_then_indexed_exact_source_order]

private theorem mem_acetal_materialized_iff_source (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateAcetalProvisions ∨
        provision ∈ GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionProvisions ↔
      provision ∈ carbohydrate1996AcetalsSemanticsSlice := by
  rw [or_comm, ← List.mem_append,
    GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completion_then_indexed_exact_source_order]

private theorem mem_residue_materialized_iff_source (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateResidueIonProvisions ∨
        provision ∈ GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionProvisions ↔
      provision ∈ carbohydrate1996ResiduesIonsSemanticsSlice := by
  rw [or_comm, ← List.mem_append,
    GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completion_then_indexed_exact_source_order]

private theorem mem_glycoside_materialized_iff_source (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionProvisions ∨
        provision ∈
          GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedProvisions ↔
      provision ∈ carbohydrate1996GlycosidesRingsSemanticsSlice := by
  rw [GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printed_provisions_eq_prior_untranscribed]
  rw [← List.mem_append,
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.semantic_then_untranscribed_exact_source_order]

private theorem mem_oligosaccharide_materialized_iff_source
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateOligosaccharideProvisions ∨
        provision ∈
          GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionProvisions ∨
        provision ∈
          GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedProvisions ↔
      provision ∈ carbohydrate1996OligosaccharidesPolysaccharidesSemanticsSlice := by
  rw [GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printed_provisions_eq_prior_untranscribed]
  rw [← List.mem_append, ← List.mem_append]
  exact
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.materialized_then_untranscribed_order_perm_source.mem_iff

private theorem mem_appendix_materialized_iff_source (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions ∨
        provision ∈ GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionProvisions ↔
      provision ∈ carbohydrate1996AppendixErrataGlossarySemanticsSlice := by
  rw [or_comm, ← List.mem_append,
    GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completion_then_indexed_exact_source_order]

private theorem mem_image_all_and_not_untranscribed_iff_transcribed
    (row : Carbohydrate1996ImageAudit.Provision) :
    row ∈ Carbohydrate1996ImageAudit.Provision.all ∧
        row ∉ Carbohydrate1996ImageAudit.Provision.notTranscribed ↔
      row ∈ Carbohydrate1996ImageAudit.Provision.transcribed := by
  have partition :
      row ∈ Carbohydrate1996ImageAudit.Provision.transcribed ++
          Carbohydrate1996ImageAudit.Provision.notTranscribed ↔
        row ∈ Carbohydrate1996ImageAudit.Provision.all :=
    Carbohydrate1996ImageAudit.Provision.source_partition.mem_iff
  have disjoint : Carbohydrate1996ImageAudit.Provision.transcribed.Disjoint
      Carbohydrate1996ImageAudit.Provision.notTranscribed :=
    List.disjoint_of_nodup_append
      (Carbohydrate1996ImageAudit.Provision.all_nodup.perm
        Carbohydrate1996ImageAudit.Provision.source_partition.symm)
  constructor
  · rintro ⟨all, notUntranscribed⟩
    have : row ∈ Carbohydrate1996ImageAudit.Provision.transcribed ∨
        row ∈ Carbohydrate1996ImageAudit.Provision.notTranscribed := by
      simpa only [List.mem_append] using partition.symm.mp all
    exact this.resolve_right notUntranscribed
  · intro transcribed
    exact ⟨partition.mp (List.mem_append_left _ transcribed),
      fun notTranscribed => (List.disjoint_left.mp disjoint) transcribed notTranscribed⟩

private theorem not_mem_image_untranscribed_iff_transcribed
    (row : Carbohydrate1996ImageAudit.Provision) :
    row ∉ Carbohydrate1996ImageAudit.Provision.notTranscribed ↔
      row ∈ Carbohydrate1996ImageAudit.Provision.transcribed := by
  simpa using mem_image_all_and_not_untranscribed_iff_transcribed row

private theorem mem_image_source_partition (provision : IUPACNormativeProvision) :
    provision ∈ carbohydrate1996ImageArtifactSourceSlice ↔
      provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateTranscribedGraphProvisions ∨
        provision ∈ carbohydrate1996UntranscribedImageSourceSlice := by
  have partition := Carbohydrate1996ImageAudit.Provision.source_partition.map
    IUPACNormativeProvision.carbohydrate1996ImageArtifact
  simpa [carbohydrate1996ImageArtifactSourceSlice,
    GlobalNonDescriptorIndexedSourceData.carbohydrateTranscribedGraphProvisions,
    GlobalNonDescriptorIndexedSourceData.carbohydrateTranscribedGraphRows,
    carbohydrate1996UntranscribedImageSourceSlice, List.map_append] using partition.mem_iff.symm

private def SourceEligible (provision : IUPACNormativeProvision) : Prop :=
  provision ∈ sourceProvisions .blueBook2013P10 ∨
  provision ∈ sourceProvisions .retinoidRecommendations1981 ∨
  provision ∈ sourceProvisions .carotenoidRules1974 ∨
  provision ∈ sourceProvisions .steroidRecommendations1989 ∨
  provision ∈ sourceProvisions .cyclitolRecommendations1973 ∨
  provision ∈ sourceProvisions .nucleicAcidRecommendations1970 ∨
  provision ∈ sourceProvisions .lipidRecommendations1976 ∨
  provision ∈ sourceProvisions .glycolipidRecommendations1997 ∨
  provision ∈ sourceProvisions .aminoAcidPeptideRecommendations1983 ∨
  provision ∈ carbohydrate1996ScopeParentSemanticsSlice ∨
  provision ∈ carbohydrate1996FoundationSemanticsSlice ∨
  provision ∈ carbohydrate1996NamedParentsSemanticsSlice ∨
  provision ∈ carbohydrate1996DerivativesSemanticsSlice ∨
  provision ∈ carbohydrate1996UnsaturatedBranchedSemanticsSlice ∨
  provision ∈ carbohydrate1996AlditolsAcidsSemanticsSlice ∨
  provision ∈ carbohydrate1996HeteroSubstitutionAnhydrideSemanticsSlice ∨
  provision ∈ carbohydrate1996AcetalsSemanticsSlice ∨
  provision ∈ carbohydrate1996ResiduesIonsSemanticsSlice ∨
  provision ∈ carbohydrate1996GlycosidesRingsSemanticsSlice ∨
  provision ∈ carbohydrate1996OligosaccharidesPolysaccharidesSemanticsSlice ∨
  provision ∈ carbohydrate1996AppendixErrataGlossarySemanticsSlice ∨
  provision ∈ GlobalNonDescriptorIndexedSourceData.carbohydrateTranscribedGraphProvisions

set_option maxRecDepth 8192 in
private theorem sourceEligible_subset_parameterized
    {provision : IUPACNormativeProvision} (eligible : SourceEligible provision) :
    provision ∈ parameterizedProvisions := by
  rw [GlobalNonDescriptorSourceMeaningProgress.mem_parameterizedProvisions_iff_isParameterized]
  unfold SourceEligible at eligible
  rcases eligible with h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h
  all_goals
    simp only [sourceProvisions,
    carbohydrate1996ScopeParentSemanticsSlice,
    carbohydrate1996FoundationSemanticsSlice,
    carbohydrate1996NamedParentsSemanticsSlice,
    carbohydrate1996DerivativesSemanticsSlice,
    carbohydrate1996UnsaturatedBranchedSemanticsSlice,
    carbohydrate1996AlditolsAcidsSemanticsSlice,
    carbohydrate1996HeteroSubstitutionAnhydrideSemanticsSlice,
    carbohydrate1996AcetalsSemanticsSlice,
    carbohydrate1996ResiduesIonsSemanticsSlice,
    carbohydrate1996GlycosidesRingsSemanticsSlice,
    carbohydrate1996OligosaccharidesPolysaccharidesSemanticsSlice,
    carbohydrate1996AppendixErrataGlossarySemanticsSlice,
    GlobalNonDescriptorIndexedSourceData.carbohydrateTranscribedGraphProvisions,
    GlobalNonDescriptorIndexedSourceData.carbohydrateTranscribedGraphRows] at h
  all_goals
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp h
    rfl

set_option maxRecDepth 8192 in
private theorem sourceEligible_not_missing
    {provision : IUPACNormativeProvision} (eligible : SourceEligible provision) :
    provision ∉ globalNonDescriptorMissingSourceMeaningProvisions := by
  rw [mem_globalNonDescriptorMissingSourceMeaningProvisions_iff]
  rintro (appendix | image)
  · change provision ∈
      BlueBookAppendix3Audit.Provision.all.map IUPACNormativeProvision.appendix3 at appendix
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp appendix
    simp [SourceEligible, sourceProvisions,
      carbohydrate1996ScopeParentSemanticsSlice,
      carbohydrate1996FoundationSemanticsSlice,
      carbohydrate1996NamedParentsSemanticsSlice,
      carbohydrate1996DerivativesSemanticsSlice,
      carbohydrate1996UnsaturatedBranchedSemanticsSlice,
      carbohydrate1996AlditolsAcidsSemanticsSlice,
      carbohydrate1996HeteroSubstitutionAnhydrideSemanticsSlice,
      carbohydrate1996AcetalsSemanticsSlice,
      carbohydrate1996ResiduesIonsSemanticsSlice,
      carbohydrate1996GlycosidesRingsSemanticsSlice,
      carbohydrate1996OligosaccharidesPolysaccharidesSemanticsSlice,
      carbohydrate1996AppendixErrataGlossarySemanticsSlice,
      GlobalNonDescriptorIndexedSourceData.carbohydrateTranscribedGraphProvisions] at eligible
  · change provision ∈
      Carbohydrate1996ImageAudit.Provision.notTranscribed.map
        IUPACNormativeProvision.carbohydrate1996ImageArtifact at image
    obtain ⟨row, rowUntranscribed, rfl⟩ := List.mem_map.mp image
    have rowTranscribed : row ∈ Carbohydrate1996ImageAudit.Provision.transcribed := by
      simpa [SourceEligible, sourceProvisions,
        carbohydrate1996ScopeParentSemanticsSlice,
        carbohydrate1996FoundationSemanticsSlice,
        carbohydrate1996NamedParentsSemanticsSlice,
        carbohydrate1996DerivativesSemanticsSlice,
        carbohydrate1996UnsaturatedBranchedSemanticsSlice,
        carbohydrate1996AlditolsAcidsSemanticsSlice,
        carbohydrate1996HeteroSubstitutionAnhydrideSemanticsSlice,
        carbohydrate1996AcetalsSemanticsSlice,
        carbohydrate1996ResiduesIonsSemanticsSlice,
        carbohydrate1996GlycosidesRingsSemanticsSlice,
        carbohydrate1996OligosaccharidesPolysaccharidesSemanticsSlice,
        carbohydrate1996AppendixErrataGlossarySemanticsSlice,
        GlobalNonDescriptorIndexedSourceData.carbohydrateTranscribedGraphProvisions,
        GlobalNonDescriptorIndexedSourceData.carbohydrateTranscribedGraphRows] using eligible
    exact (not_mem_image_untranscribed_iff_transcribed row).2 rowTranscribed rowUntranscribed

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem mem_parameterized_and_not_missing_iff_sourceEligible
    (provision : IUPACNormativeProvision) :
    provision ∈ parameterizedProvisions ∧
        provision ∉ globalNonDescriptorMissingSourceMeaningProvisions ↔
      SourceEligible provision := by
  constructor
  · rintro ⟨parameterized, notMissing⟩
    rw [mem_globalNonDescriptorMissingSourceMeaningProvisions_iff] at notMissing
    have imagePartition := mem_image_source_partition provision
    simp only [parameterizedProvisions, SourceEligible, sourceProvisions,
      carbohydrate1996ScopeParentSemanticsSlice,
      carbohydrate1996FoundationSemanticsSlice,
      carbohydrate1996NamedParentsSemanticsSlice,
      carbohydrate1996DerivativesSemanticsSlice,
      carbohydrate1996UnsaturatedBranchedSemanticsSlice,
      carbohydrate1996AlditolsAcidsSemanticsSlice,
      carbohydrate1996HeteroSubstitutionAnhydrideSemanticsSlice,
      carbohydrate1996AcetalsSemanticsSlice,
      carbohydrate1996ResiduesIonsSemanticsSlice,
      carbohydrate1996GlycosidesRingsSemanticsSlice,
      carbohydrate1996OligosaccharidesPolysaccharidesSemanticsSlice,
      carbohydrate1996AppendixErrataGlossarySemanticsSlice,
      List.mem_append] at imagePartition parameterized notMissing ⊢
    simp only [or_assoc] at parameterized ⊢
    rcases parameterized with h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h
    all_goals simp_all
    have imageFull : provision ∈ carbohydrate1996ImageArtifactSourceSlice := by
      simpa [carbohydrate1996ImageArtifactSourceSlice] using h
    have transcribed := imagePartition.mp imageFull
    simp [transcribed]
  · intro eligible
    exact ⟨sourceEligible_subset_parameterized eligible,
      sourceEligible_not_missing eligible⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem mem_materialized_or_remaining_iff_eligible
    (provision : IUPACNormativeProvision) :
    provision ∈ materializedProvisions ∨
        provision ∈ remainingPartiallyFormalizedProvisions ↔
      SourceEligible provision := by
  rw [materializedProvisions,
    GlobalNonDescriptorMaterializedSourceMeaning.mem_provisions_iff_components,
    GlobalNonDescriptorIndexedSourceMeaning.mem_provisions_iff_components]
  simp only [remainingPartiallyFormalizedProvisions,
      GlobalNonDescriptorRetinoidSourceMeaning.provisions_exact,
      GlobalNonDescriptorCarotenoidSourceMeaning.provisions_exact,
      GlobalNonDescriptorSteroidSourceMeaning.provisions_exact,
      GlobalNonDescriptorCyclitolSourceMeaning.provisions_exact,
      GlobalNonDescriptorNucleicAcidSourceMeaning.provisions_exact,
      GlobalNonDescriptorLipidSourceMeaning.provisions_exact,
      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions_exact,
      GlobalNonDescriptorP10SourceMeaning.provisions_exact,
      GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printed_provisions_eq_prior_untranscribed,
      GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printed_provisions_eq_prior_untranscribed,
      GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions_eq_existing_six_graph_projection]
  have glycolipid := mem_glycolipid_materialized_iff_source provision
  have scope := mem_scope_materialized_iff_source provision
  have foundation := mem_foundation_materialized_iff_source provision
  have namedParent := mem_named_parent_materialized_iff_source provision
  have derivative := mem_derivative_materialized_iff_source provision
  have unsaturated := mem_unsaturated_materialized_iff_source provision
  have alditol := mem_alditol_materialized_iff_source provision
  have hetero := mem_hetero_materialized_iff_source provision
  have acetal := mem_acetal_materialized_iff_source provision
  have residue := mem_residue_materialized_iff_source provision
  have glycoside := mem_glycoside_materialized_iff_source provision
  have oligosaccharide := mem_oligosaccharide_materialized_iff_source provision
  have appendix := mem_appendix_materialized_iff_source provision
  unfold SourceEligible
  constructor
  · intro materializedOrRemaining
    simp only [or_assoc] at materializedOrRemaining ⊢
    rcases materializedOrRemaining with
      h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h
    all_goals simp_all
  · intro eligible
    simp only [or_assoc] at eligible ⊢
    rcases eligible with h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h
    all_goals simp_all
    all_goals first
      | (rcases glycolipid with h | h <;> simp [h])
      | (rcases scope with h | h <;> simp [h])
      | (rcases foundation with h | h <;> simp [h])
      | (rcases namedParent with h | h <;> simp [h])
      | (rcases derivative with h | h <;> simp [h])
      | (rcases unsaturated with h | h <;> simp [h])
      | (rcases alditol with h | h <;> simp [h])
      | (rcases hetero with h | h <;> simp [h])
      | (rcases acetal with h | h <;> simp [h])
      | (rcases residue with h | h <;> simp [h])
      | (rcases glycoside with h | h <;> simp [h])
      | (rcases oligosaccharide with h | h | h <;> simp [h])
      | (rcases appendix with h | h <;> simp [h])

theorem mem_parameterized_and_not_missing_iff_materialized_or_remaining
    (provision : IUPACNormativeProvision) :
    provision ∈ parameterizedProvisions ∧
        provision ∉ globalNonDescriptorMissingSourceMeaningProvisions ↔
      provision ∈ materializedProvisions ∨
        provision ∈ remainingPartiallyFormalizedProvisions := by
  rw [mem_parameterized_and_not_missing_iff_sourceEligible,
    mem_materialized_or_remaining_iff_eligible]

@[simp] theorem materialized_count : materializedProvisions.length = 1613 := by
  exact GlobalNonDescriptorMaterializedSourceMeaning.provision_count

@[simp] theorem p10_materialized_count : GlobalNonDescriptorP10SourceMeaning.provisions.length = 71 :=
  GlobalNonDescriptorP10SourceMeaning.provision_count

@[simp] theorem glycoside_ring_printed_materialized_count :
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedProvisions.length = 58 :=
  GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printed_provision_count

@[simp] theorem remaining_count : remainingPartiallyFormalizedProvisions.length = 0 := by
  simp [remainingPartiallyFormalizedProvisions]

theorem materialized_nodup : materializedProvisions.Nodup :=
  GlobalNonDescriptorMaterializedSourceMeaning.provisions_nodup

theorem remaining_nodup : remainingPartiallyFormalizedProvisions.Nodup := by
  simp [remainingPartiallyFormalizedProvisions]

theorem mem_residual_iff_materialized_or_remaining
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.residualPartiallyFormalizedProvisions ↔
      provision ∈ materializedProvisions ∨
        provision ∈ remainingPartiallyFormalizedProvisions := by
  rw [mem_residual_iff_parameterized_and_not_missing,
    mem_parameterized_and_not_missing_iff_materialized_or_remaining]

theorem materialized_subset_residual
    {provision : IUPACNormativeProvision} (member : provision ∈ materializedProvisions) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.residualPartiallyFormalizedProvisions :=
  (mem_residual_iff_materialized_or_remaining provision).2 (Or.inl member)

theorem remaining_subset_residual
    {provision : IUPACNormativeProvision}
    (member : provision ∈ remainingPartiallyFormalizedProvisions) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.residualPartiallyFormalizedProvisions :=
  (mem_residual_iff_materialized_or_remaining provision).2 (Or.inr member)

theorem materialized_disjoint_remaining :
    materializedProvisions.Disjoint remainingPartiallyFormalizedProvisions := by
  simp [remainingPartiallyFormalizedProvisions]

theorem materialized_append_remaining_perm_residual :
    (materializedProvisions ++ remainingPartiallyFormalizedProvisions).Perm
      GlobalNonDescriptorSourceMeaningProgress.residualPartiallyFormalizedProvisions := by
  apply (List.perm_ext_iff_of_nodup
    (materialized_nodup.append remaining_nodup materialized_disjoint_remaining)
    GlobalNonDescriptorSourceMeaningProgress.residualPartiallyFormalized_nodup).2
  intro provision
  rw [List.mem_append]
  exact (mem_residual_iff_materialized_or_remaining provision).symm

theorem reconciled_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      materializedProvisions.length = 1613 ∧
        remainingPartiallyFormalizedProvisions.length = 0 ∧
          globalNonDescriptorMissingSourceMeaningProvisions.length = 595 ∧
            92 + 1613 + 0 + 595 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    materialized_count, remaining_count,
    globalNonDescriptorMissingSourceMeaningProvisionCount, by omega⟩

theorem mem_reviewed_or_materialized_or_remaining_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ materializedProvisions ∨
        provision ∈ remainingPartiallyFormalizedProvisions ∨
          provision ∈ globalNonDescriptorMissingSourceMeaningProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorSourceMeaningProgress.mem_reviewed_or_residual_or_missing_iff]
  rw [mem_residual_iff_materialized_or_remaining]
  tauto

theorem p10_source_audit_still_open :
    ¬IUPACNormativeSource.ProvisionAuditComplete .blueBook2013P10 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete,
    BlueBookP10Audit.currentSourceReviewProvisionEnumerationConfirmed,
    BlueBookP10Audit.currentSourceReviewProseTableCoverageConfirmed,
    BlueBookP10Audit.currentSourceReviewFigureGraphTranscriptionsReviewed]

theorem carbohydrate_source_audit_still_open :
    ¬IUPACNormativeSource.ProvisionAuditComplete .carbohydrateRecommendations1996 :=
  GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.source_audit_still_open

end GlobalNonDescriptorMaterializedSourceMeaningProgress
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaningProgress.remaining_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaningProgress.materialized_append_remaining_perm_residual
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaningProgress.mem_residual_iff_materialized_or_remaining
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaningProgress.mem_reviewed_or_materialized_or_remaining_or_missing_iff
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaningProgress.reconciled_live_frontier_counts
