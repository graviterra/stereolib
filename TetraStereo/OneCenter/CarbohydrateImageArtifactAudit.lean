import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk0
import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk1
import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk2
import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk3
import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk4
import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk5
import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk6
import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk7
import TetraStereo.OneCenter.CarbohydrateImageArtifactCatalogChunk8
import TetraStereo.OneCenter.CarbohydrateImageReferrerCatalogChunk0
import TetraStereo.OneCenter.CarbohydrateImageReferrerCatalogChunk1
import TetraStereo.OneCenter.CarbohydrateImageReferrerCatalogChunk2
import TetraStereo.OneCenter.CarbohydrateImageReferrerCatalogChunk3
import TetraStereo.OneCenter.CarbohydrateImageReferrerCatalogChunk4
import TetraStereo.OneCenter.CarbohydrateImageReferrerCatalogChunk5
import TetraStereo.OneCenter.CarbohydrateImageReferrerCatalogChunk6
import TetraStereo.OneCenter.CarbohydrateImageReferrerCatalogChunk7
import TetraStereo.OneCenter.CarbohydrateImageReferrerCatalogChunk8

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace TetraStereo.OneCenter










namespace Carbohydrate1996ImageAudit

def imageArtifacts : List ImageArtifactData :=
  imageArtifactsChunk0 ++ imageArtifactsChunk1 ++ imageArtifactsChunk2 ++
    imageArtifactsChunk3 ++ imageArtifactsChunk4 ++ imageArtifactsChunk5 ++
    imageArtifactsChunk6 ++ imageArtifactsChunk7 ++ imageArtifactsChunk8

set_option maxRecDepth 4096 in
@[simp] theorem imageArtifacts_length : imageArtifacts.length = 430 := by
  simp only [imageArtifacts, List.length_append, imageArtifactsChunk0_length,
    imageArtifactsChunk1_length, imageArtifactsChunk2_length, imageArtifactsChunk3_length,
    imageArtifactsChunk4_length, imageArtifactsChunk5_length, imageArtifactsChunk6_length,
    imageArtifactsChunk7_length, imageArtifactsChunk8_length]

abbrev ImageArtifact := Fin imageArtifacts.length

namespace ImageArtifact

def all : List ImageArtifact := List.finRange imageArtifacts.length
@[simp] theorem mem_all (artifact : ImageArtifact) : artifact ∈ all := by
  exact List.mem_finRange artifact
theorem all_nodup : all.Nodup := List.nodup_finRange imageArtifacts.length
@[simp] theorem length_all : all.length = 430 := by
  simp [all]

def data (artifact : ImageArtifact) : ImageArtifactData := imageArtifacts.get artifact

end ImageArtifact

private theorem imageArtifact_data_all :
    ImageArtifact.all.map ImageArtifact.data = imageArtifacts := by
  unfold ImageArtifact.all ImageArtifact.data
  exact List.map_get_finRange imageArtifacts

private def frozenImagePaths : List String :=
  imageArtifacts.map ImageArtifactData.relativePath

private theorem frozenImagePaths_chunks :
    frozenImagePaths =
      imageArtifactPathsChunk0 ++ imageArtifactPathsChunk1 ++ imageArtifactPathsChunk2 ++
      imageArtifactPathsChunk3 ++ imageArtifactPathsChunk4 ++ imageArtifactPathsChunk5 ++
      imageArtifactPathsChunk6 ++ imageArtifactPathsChunk7 ++ imageArtifactPathsChunk8 := by
  simp only [frozenImagePaths, imageArtifacts, List.map_append, imageArtifactPathsChunk0,
    imageArtifactPathsChunk1, imageArtifactPathsChunk2, imageArtifactPathsChunk3,
    imageArtifactPathsChunk4, imageArtifactPathsChunk5, imageArtifactPathsChunk6,
    imageArtifactPathsChunk7, imageArtifactPathsChunk8]

private theorem frozenImagePaths_isChain : frozenImagePaths.IsChain (· < ·) := by
  have chain0 := imageArtifactPathsChunk0_isChain
  have chain1 := imageArtifactPathsChunk1_isChain
  have chain2 := imageArtifactPathsChunk2_isChain
  have chain3 := imageArtifactPathsChunk3_isChain
  have chain4 := imageArtifactPathsChunk4_isChain
  have chain5 := imageArtifactPathsChunk5_isChain
  have chain6 := imageArtifactPathsChunk6_isChain
  have chain7 := imageArtifactPathsChunk7_isChain
  have chain8 := imageArtifactPathsChunk8_isChain
  have chain01 := chain0.append chain1 (by decide)
  have chain012 := chain01.append chain2 (by decide)
  have chain0123 := chain012.append chain3 (by decide)
  have chain01234 := chain0123.append chain4 (by decide)
  have chain012345 := chain01234.append chain5 (by decide)
  have chain0123456 := chain012345.append chain6 (by decide)
  have chain01234567 := chain0123456.append chain7 (by decide)
  have chain012345678 := chain01234567.append chain8 (by decide)
  rw [frozenImagePaths_chunks]
  exact chain012345678

theorem relative_paths_are_pairwise_distinct :
    (ImageArtifact.all.map fun artifact => artifact.data.relativePath).Nodup := by
  change (ImageArtifact.all.map
    (ImageArtifactData.relativePath ∘ ImageArtifact.data)).Nodup
  rw [← List.map_map, imageArtifact_data_all]
  exact frozenImagePaths_isChain.pairwise.nodup

/-- Exact HTML-page referrers reconstructed from every captured image-source occurrence. -/
def htmlImageReferrers : List (String × List String) :=
  htmlImageReferrersChunk0 ++ htmlImageReferrersChunk1 ++ htmlImageReferrersChunk2 ++
    htmlImageReferrersChunk3 ++ htmlImageReferrersChunk4 ++ htmlImageReferrersChunk5 ++
    htmlImageReferrersChunk6 ++ htmlImageReferrersChunk7 ++ htmlImageReferrersChunk8

@[simp] theorem htmlImageReferrers_length : htmlImageReferrers.length = 430 := by
  simp only [htmlImageReferrers, List.length_append, htmlImageReferrersChunk0_length,
    htmlImageReferrersChunk1_length, htmlImageReferrersChunk2_length,
    htmlImageReferrersChunk3_length, htmlImageReferrersChunk4_length,
    htmlImageReferrersChunk5_length, htmlImageReferrersChunk6_length,
    htmlImageReferrersChunk7_length, htmlImageReferrersChunk8_length]

@[simp] theorem html_referrer_paths_exactly_match_frozen_image_paths :
    htmlImageReferrers.map Prod.fst = imageArtifacts.map ImageArtifactData.relativePath := by
  simp only [htmlImageReferrers, imageArtifacts, List.map_append,
    htmlImageReferrersChunk0_pathsMatchArtifacts,
    htmlImageReferrersChunk1_pathsMatchArtifacts,
    htmlImageReferrersChunk2_pathsMatchArtifacts,
    htmlImageReferrersChunk3_pathsMatchArtifacts,
    htmlImageReferrersChunk4_pathsMatchArtifacts,
    htmlImageReferrersChunk5_pathsMatchArtifacts,
    htmlImageReferrersChunk6_pathsMatchArtifacts,
    htmlImageReferrersChunk7_pathsMatchArtifacts,
    htmlImageReferrersChunk8_pathsMatchArtifacts]

theorem html_referrer_paths_are_pairwise_distinct :
    (htmlImageReferrers.map Prod.fst).Nodup := by
  rw [html_referrer_paths_exactly_match_frozen_image_paths]
  have imagePathsEq :
      imageArtifacts.map ImageArtifactData.relativePath =
        ImageArtifact.all.map fun artifact => artifact.data.relativePath := by
    decide
  rw [imagePathsEq]
  exact relative_paths_are_pairwise_distinct

def ImageArtifact.htmlIndex (artifact : ImageArtifact) : Fin htmlImageReferrers.length :=
  ⟨artifact.val, by
    simpa only [htmlImageReferrers_length, imageArtifacts_length] using artifact.isLt⟩

def ImageArtifact.sourcePages (artifact : ImageArtifact) : List String :=
  (htmlImageReferrers.get artifact.htmlIndex).2

private theorem htmlImageReferrers_allReferenced :
    htmlImageReferrers.all (fun entry => decide (entry.2 ≠ [])) = true := by
  simp only [htmlImageReferrers, List.all_append,
    htmlImageReferrersChunk0_allReferenced,
    htmlImageReferrersChunk1_allReferenced,
    htmlImageReferrersChunk2_allReferenced,
    htmlImageReferrersChunk3_allReferenced,
    htmlImageReferrersChunk4_allReferenced,
    htmlImageReferrersChunk5_allReferenced,
    htmlImageReferrersChunk6_allReferenced,
    htmlImageReferrersChunk7_allReferenced,
    htmlImageReferrersChunk8_allReferenced, Bool.and_eq_true]
  simp

@[simp] theorem all_frozen_images_are_referenced_by_html :
    ImageArtifact.all.all (fun artifact => decide (artifact.sourcePages ≠ [])) = true := by
  apply List.all_eq_true.mpr
  intro artifact _
  exact (List.all_eq_true.mp htmlImageReferrers_allReferenced)
    (htmlImageReferrers.get artifact.htmlIndex) (List.get_mem htmlImageReferrers artifact.htmlIndex)

theorem every_frozen_image_is_referenced_by_html (artifact : ImageArtifact) :
    artifact.sourcePages ≠ [] := by
  have checked := (List.all_eq_true.mp all_frozen_images_are_referenced_by_html)
    artifact artifact.mem_all
  exact of_decide_eq_true checked

@[simp] theorem image_referrer_multiplicity_distribution :
    (ImageArtifact.all.filter fun artifact => artifact.sourcePages.length = 1).length = 426 ∧
    (ImageArtifact.all.filter fun artifact => artifact.sourcePages.length = 2).length = 1 ∧
    (ImageArtifact.all.filter fun artifact => artifact.sourcePages.length = 3).length = 1 ∧
    (ImageArtifact.all.filter fun artifact => artifact.sourcePages.length = 6).length = 1 ∧
    (ImageArtifact.all.filter fun artifact => artifact.sourcePages.length = 17).length = 1 := by
  decide


def ImageArtifact.symbolicTemplateTranscribed (artifact : ImageArtifact) : Bool :=
  artifact.data.kind.requiresMolecularGraph &&
    (symbolicTemplate? artifact.data.relativePath).isSome

private theorem imageArtifacts_transcribedCount :
    (imageArtifacts.filter ImageArtifactData.symbolicTemplateTranscribed).length = 6 := by
  have h0 := imageArtifactsChunk0_transcribedCount
  have h1 := imageArtifactsChunk1_transcribedCount
  have h2 := imageArtifactsChunk2_transcribedCount
  have h3 := imageArtifactsChunk3_transcribedCount
  have h4 := imageArtifactsChunk4_transcribedCount
  have h5 := imageArtifactsChunk5_transcribedCount
  have h6 := imageArtifactsChunk6_transcribedCount
  have h7 := imageArtifactsChunk7_transcribedCount
  have h8 := imageArtifactsChunk8_transcribedCount
  simp only [imageArtifacts, List.filter_append, List.length_append]
  omega

@[simp] theorem transcribed_image_count :
    (ImageArtifact.all.filter ImageArtifact.symbolicTemplateTranscribed).length = 6 := by
  have count := imageArtifacts_transcribedCount
  rw [← imageArtifact_data_all] at count
  simpa only [List.filter_map, List.length_map, Function.comp_apply,
    ImageArtifact.symbolicTemplateTranscribed] using count

private theorem imageArtifacts_transcribedTemplatesWellFormed :
    (imageArtifacts.filter ImageArtifactData.symbolicTemplateTranscribed).all fun data =>
      match symbolicTemplate? data.relativePath with
      | some graph => graph.wellFormed
      | none => false := by
  have h0 := imageArtifactsChunk0_transcribedTemplatesWellFormed
  have h1 := imageArtifactsChunk1_transcribedTemplatesWellFormed
  have h2 := imageArtifactsChunk2_transcribedTemplatesWellFormed
  have h3 := imageArtifactsChunk3_transcribedTemplatesWellFormed
  have h4 := imageArtifactsChunk4_transcribedTemplatesWellFormed
  have h5 := imageArtifactsChunk5_transcribedTemplatesWellFormed
  have h6 := imageArtifactsChunk6_transcribedTemplatesWellFormed
  have h7 := imageArtifactsChunk7_transcribedTemplatesWellFormed
  have h8 := imageArtifactsChunk8_transcribedTemplatesWellFormed
  simpa only [imageArtifacts, List.filter_append, List.all_append, h0, h1, h2, h3, h4,
    h5, h6, h7, h8]

@[simp] theorem every_transcribed_image_template_is_well_formed :
    (ImageArtifact.all.filter ImageArtifact.symbolicTemplateTranscribed).all fun artifact =>
      match symbolicTemplate? artifact.data.relativePath with
      | some graph => graph.wellFormed
      | none => false := by
  have checked := imageArtifacts_transcribedTemplatesWellFormed
  rw [← imageArtifact_data_all] at checked
  simpa only [List.filter_map, List.all_map, Function.comp_apply,
    ImageArtifact.symbolicTemplateTranscribed] using checked

private theorem imageArtifacts_genericAndErratumTranscribed :
    (imageArtifacts.filter fun data =>
      data.kind = .genericGlossaryStructure ∨ data.kind = .erratumCorrectedStructure).all
      ImageArtifactData.symbolicTemplateTranscribed := by
  have h0 := imageArtifactsChunk0_genericAndErratumTranscribed
  have h1 := imageArtifactsChunk1_genericAndErratumTranscribed
  have h2 := imageArtifactsChunk2_genericAndErratumTranscribed
  have h3 := imageArtifactsChunk3_genericAndErratumTranscribed
  have h4 := imageArtifactsChunk4_genericAndErratumTranscribed
  have h5 := imageArtifactsChunk5_genericAndErratumTranscribed
  have h6 := imageArtifactsChunk6_genericAndErratumTranscribed
  have h7 := imageArtifactsChunk7_genericAndErratumTranscribed
  have h8 := imageArtifactsChunk8_genericAndErratumTranscribed
  simpa only [imageArtifacts, List.filter_append, List.all_append, h0, h1, h2, h3, h4,
    h5, h6, h7, h8]

@[simp] theorem generic_and_erratum_image_templates_are_transcribed :
    (ImageArtifact.all.filter fun artifact =>
      artifact.data.kind = .genericGlossaryStructure ∨
        artifact.data.kind = .erratumCorrectedStructure).all
      ImageArtifact.symbolicTemplateTranscribed := by
  have checked := imageArtifacts_genericAndErratumTranscribed
  rw [← imageArtifact_data_all] at checked
  simpa only [List.filter_map, List.all_map, Function.comp_apply,
    ImageArtifact.symbolicTemplateTranscribed] using checked

def ImageArtifact.graphAuditMaturity (artifact : ImageArtifact) : GraphAuditMaturity :=
  artifact.data.graphAuditMaturity

private theorem imageArtifacts_kindCounts :
    (imageArtifacts.filter fun data =>
      data.kind = .numberedOrChartStructure).length = 419 ∧
    (imageArtifacts.filter fun data =>
      data.kind = .genericGlossaryStructure).length = 5 ∧
    (imageArtifacts.filter fun data =>
      data.kind = .erratumCorrectedStructure).length = 1 ∧
    (imageArtifacts.filter fun data => data.kind = .typographyGlyph).length = 5 := by
  rcases imageArtifactsChunk0_kindCounts with ⟨h00, h01, h02, h03⟩
  rcases imageArtifactsChunk1_kindCounts with ⟨h10, h11, h12, h13⟩
  rcases imageArtifactsChunk2_kindCounts with ⟨h20, h21, h22, h23⟩
  rcases imageArtifactsChunk3_kindCounts with ⟨h30, h31, h32, h33⟩
  rcases imageArtifactsChunk4_kindCounts with ⟨h40, h41, h42, h43⟩
  rcases imageArtifactsChunk5_kindCounts with ⟨h50, h51, h52, h53⟩
  rcases imageArtifactsChunk6_kindCounts with ⟨h60, h61, h62, h63⟩
  rcases imageArtifactsChunk7_kindCounts with ⟨h70, h71, h72, h73⟩
  rcases imageArtifactsChunk8_kindCounts with ⟨h80, h81, h82, h83⟩
  simp only [imageArtifacts, List.filter_append, List.length_append]
  omega

@[simp] theorem captured_image_kind_counts :
    (ImageArtifact.all.filter fun artifact =>
      artifact.data.kind = .numberedOrChartStructure).length = 419 ∧
    (ImageArtifact.all.filter fun artifact =>
      artifact.data.kind = .genericGlossaryStructure).length = 5 ∧
    (ImageArtifact.all.filter fun artifact =>
      artifact.data.kind = .erratumCorrectedStructure).length = 1 ∧
    (ImageArtifact.all.filter fun artifact =>
      artifact.data.kind = .typographyGlyph).length = 5 := by
  have counts := imageArtifacts_kindCounts
  rw [← imageArtifact_data_all] at counts
  simpa only [List.filter_map, List.length_map, Function.comp_apply] using counts

private theorem imageArtifacts_chemicalPartitionCounts :
    (imageArtifacts.filter fun data => data.kind.requiresMolecularGraph).length = 425 ∧
    (imageArtifacts.filter fun data => !data.kind.requiresMolecularGraph).length = 5 := by
  rcases imageArtifactsChunk0_chemicalPartitionCounts with ⟨h00, h01⟩
  rcases imageArtifactsChunk1_chemicalPartitionCounts with ⟨h10, h11⟩
  rcases imageArtifactsChunk2_chemicalPartitionCounts with ⟨h20, h21⟩
  rcases imageArtifactsChunk3_chemicalPartitionCounts with ⟨h30, h31⟩
  rcases imageArtifactsChunk4_chemicalPartitionCounts with ⟨h40, h41⟩
  rcases imageArtifactsChunk5_chemicalPartitionCounts with ⟨h50, h51⟩
  rcases imageArtifactsChunk6_chemicalPartitionCounts with ⟨h60, h61⟩
  rcases imageArtifactsChunk7_chemicalPartitionCounts with ⟨h70, h71⟩
  rcases imageArtifactsChunk8_chemicalPartitionCounts with ⟨h80, h81⟩
  simp only [imageArtifacts, List.filter_append, List.length_append]
  omega

@[simp] theorem chemical_and_nonchemical_image_partition :
    (ImageArtifact.all.filter fun artifact =>
      artifact.data.kind.requiresMolecularGraph).length = 425 ∧
    (ImageArtifact.all.filter fun artifact =>
      !artifact.data.kind.requiresMolecularGraph).length = 5 := by
  have counts := imageArtifacts_chemicalPartitionCounts
  rw [← imageArtifact_data_all] at counts
  simpa only [List.filter_map, List.length_map, Function.comp_apply] using counts

@[simp] theorem untranscribed_chemical_images_are_explicitly_graph_pending
    (artifact : ImageArtifact)
    (pending : artifact.symbolicTemplateTranscribed = false)
    (chemical : artifact.data.kind.requiresMolecularGraph = true) :
    artifact.graphAuditMaturity = .sourceOnlyGraphPending := by
  change artifact.data.symbolicTemplateTranscribed = false at pending
  change artifact.data.graphAuditMaturity = .sourceOnlyGraphPending
  simp [ImageArtifactData.graphAuditMaturity, pending, chemical]

@[simp] theorem transcribed_images_have_symbolic_template_maturity
    (artifact : ImageArtifact)
    (transcribed : artifact.symbolicTemplateTranscribed = true) :
    artifact.graphAuditMaturity = .symbolicTemplateTranscribed := by
  change artifact.data.symbolicTemplateTranscribed = true at transcribed
  change artifact.data.graphAuditMaturity = .symbolicTemplateTranscribed
  simp [ImageArtifactData.graphAuditMaturity, transcribed]

@[simp] theorem every_nonchemical_glyph_is_audited_as_nonchemical
    (artifact : ImageArtifact)
    (glyph : artifact.data.kind.requiresMolecularGraph = false) :
    artifact.graphAuditMaturity = .nonChemicalGlyphAudited := by
  change artifact.data.graphAuditMaturity = .nonChemicalGlyphAudited
  simp [ImageArtifactData.graphAuditMaturity, ImageArtifactData.symbolicTemplateTranscribed,
    glyph]

private theorem imageArtifacts_graphAuditMaturityCounts :
    (imageArtifacts.filter fun data =>
      data.graphAuditMaturity = .symbolicTemplateTranscribed).length = 6 ∧
    (imageArtifacts.filter fun data =>
      data.graphAuditMaturity = .sourceOnlyGraphPending).length = 419 ∧
    (imageArtifacts.filter fun data =>
      data.graphAuditMaturity = .nonChemicalGlyphAudited).length = 5 := by
  rcases imageArtifactsChunk0_graphAuditMaturityCounts with ⟨h00, h01, h02⟩
  rcases imageArtifactsChunk1_graphAuditMaturityCounts with ⟨h10, h11, h12⟩
  rcases imageArtifactsChunk2_graphAuditMaturityCounts with ⟨h20, h21, h22⟩
  rcases imageArtifactsChunk3_graphAuditMaturityCounts with ⟨h30, h31, h32⟩
  rcases imageArtifactsChunk4_graphAuditMaturityCounts with ⟨h40, h41, h42⟩
  rcases imageArtifactsChunk5_graphAuditMaturityCounts with ⟨h50, h51, h52⟩
  rcases imageArtifactsChunk6_graphAuditMaturityCounts with ⟨h60, h61, h62⟩
  rcases imageArtifactsChunk7_graphAuditMaturityCounts with ⟨h70, h71, h72⟩
  rcases imageArtifactsChunk8_graphAuditMaturityCounts with ⟨h80, h81, h82⟩
  simp only [imageArtifacts, List.filter_append, List.length_append]
  omega

@[simp] theorem graph_audit_maturity_counts :
    (ImageArtifact.all.filter fun artifact =>
      artifact.graphAuditMaturity = .symbolicTemplateTranscribed).length = 6 ∧
    (ImageArtifact.all.filter fun artifact =>
      artifact.graphAuditMaturity = .sourceOnlyGraphPending).length = 419 ∧
    (ImageArtifact.all.filter fun artifact =>
      artifact.graphAuditMaturity = .nonChemicalGlyphAudited).length = 5 := by
  have counts := imageArtifacts_graphAuditMaturityCounts
  rw [← imageArtifact_data_all] at counts
  simpa only [List.filter_map, List.length_map, Function.comp_apply,
    ImageArtifact.graphAuditMaturity] using counts

inductive Provision where
  | imageArtifact (artifact : ImageArtifact)
  deriving DecidableEq, Repr

namespace Provision

def all : List Provision := ImageArtifact.all.map Provision.imageArtifact

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision with
  | imageArtifact artifact =>
      exact List.mem_map_of_mem (f := Provision.imageArtifact) artifact.mem_all

theorem all_nodup : all.Nodup :=
  ImageArtifact.all_nodup.map (by intro left right equal; cases equal; rfl)

@[simp] theorem length_all : all.length = 430 := by
  simp [all]

def symbolicTemplateTranscribed : Provision → Bool
  | .imageArtifact artifact => artifact.symbolicTemplateTranscribed

def transcribed : List Provision := all.filter symbolicTemplateTranscribed
def notTranscribed : List Provision := all.filter fun provision => !symbolicTemplateTranscribed provision

@[simp] theorem transcribed_length : transcribed.length = 6 := by
  simpa only [transcribed, all, List.filter_map, List.length_map, Function.comp_apply,
    symbolicTemplateTranscribed] using transcribed_image_count

@[simp] theorem notTranscribed_length : notTranscribed.length = 424 := by
  have partitionLength :=
    List.length_eq_length_filter_add (l := all) symbolicTemplateTranscribed
  change all.length = transcribed.length + notTranscribed.length at partitionLength
  have totalLength := length_all
  have transcribedLength := transcribed_length
  omega

theorem filter_append_filter_not_perm (xs : List Provision) (p : Provision → Bool) :
    (xs.filter p ++ xs.filter fun x => !p x).Perm xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases h : p x = true
      · simpa [h] using List.Perm.cons x ih
      · have hFalse : p x = false := Bool.eq_false_of_not_eq_true h
        have moveX :
            (xs.filter p ++ x :: xs.filter fun y => !p y).Perm
              (x :: xs.filter p ++ xs.filter fun y => !p y) := by
          exact List.perm_middle
        simpa [hFalse] using moveX.trans (List.Perm.cons x ih)

@[simp] theorem source_partition : (transcribed ++ notTranscribed).Perm all := by
  exact filter_append_filter_not_perm all symbolicTemplateTranscribed

end Provision

def Provision.sourceKey : Provision → String
  | .imageArtifact artifact => "Image/" ++ artifact.data.relativePath

end Carbohydrate1996ImageAudit
end TetraStereo.OneCenter
