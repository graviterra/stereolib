import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataCore

set_option autoImplicit false










namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorIndexedSourceData

/-! ## Hetero-substitution and anhydride printed rows: 35 -/

def carbohydrateHeteroRows : List Carbohydrate1996HeteroSubstitutionAnhydride.Provision :=
  Carbohydrate1996HeteroSubstitutionAnhydride.PrintedExample.all.map
    Carbohydrate1996HeteroSubstitutionAnhydride.Provision.printedExample

def carbohydrateHeteroProvisions : List IUPACNormativeProvision :=
  carbohydrateHeteroRows.map
    IUPACNormativeProvision.carbohydrate1996HeteroSubstitutionAnhydride

def carbohydrateHeteroBatch :
    GlobalNonDescriptorSourceMeaningBatch carbohydrateHeteroProvisions := by
  simpa [carbohydrateHeteroProvisions, carbohydrateHeteroRows, List.map_map] using
    totalMeaningBatch Carbohydrate1996HeteroSubstitutionAnhydride.PrintedExample.all
      (fun row => IUPACNormativeProvision.carbohydrate1996HeteroSubstitutionAnhydride
        (.printedExample row))
      Carbohydrate1996HeteroSubstitutionAnhydride.PrintedExample.data (by intro _row; rfl)

@[simp] theorem carbohydrateHeteroProvisionCount :
    carbohydrateHeteroProvisions.length = 35 := by
  simp [carbohydrateHeteroProvisions, carbohydrateHeteroRows]

private theorem carbohydrateHeteroRows_nodup : carbohydrateHeteroRows.Nodup :=
  Carbohydrate1996HeteroSubstitutionAnhydride.Provision.all_nodup.of_append_right

theorem carbohydrateHeteroProvisions_nodup : carbohydrateHeteroProvisions.Nodup := by
  exact carbohydrateHeteroRows_nodup.map
    (by intro left right equal; cases equal; rfl)

/-! ## Acetal printed rows: 21 -/

def carbohydrateAcetalRows : List Carbohydrate1996Acetals.Provision :=
  Carbohydrate1996Acetals.PrintedItem.all.map Carbohydrate1996Acetals.Provision.printedItem

def carbohydrateAcetalProvisions : List IUPACNormativeProvision :=
  carbohydrateAcetalRows.map IUPACNormativeProvision.carbohydrate1996Acetals

def carbohydrateAcetalBatch :
    GlobalNonDescriptorSourceMeaningBatch carbohydrateAcetalProvisions := by
  simpa [carbohydrateAcetalProvisions, carbohydrateAcetalRows, List.map_map] using
    totalMeaningBatch Carbohydrate1996Acetals.PrintedItem.all
      (fun row => IUPACNormativeProvision.carbohydrate1996Acetals (.printedItem row))
      Carbohydrate1996Acetals.PrintedItem.data (by intro _row; rfl)

@[simp] theorem carbohydrateAcetalProvisionCount :
    carbohydrateAcetalProvisions.length = 21 := by
  simp [carbohydrateAcetalProvisions, carbohydrateAcetalRows]

private theorem carbohydrateAcetalRows_nodup : carbohydrateAcetalRows.Nodup :=
  Carbohydrate1996Acetals.Provision.all_nodup.of_append_right

theorem carbohydrateAcetalProvisions_nodup : carbohydrateAcetalProvisions.Nodup := by
  exact carbohydrateAcetalRows_nodup.map
    (by intro left right equal; cases equal; rfl)

/-! ## Residue and ion printed rows: 36 -/

def carbohydrateResidueIonRows : List Carbohydrate1996ResiduesIons.Provision :=
  Carbohydrate1996ResiduesIons.PrintedExample.all.map
    Carbohydrate1996ResiduesIons.Provision.printedExample

def carbohydrateResidueIonProvisions : List IUPACNormativeProvision :=
  carbohydrateResidueIonRows.map IUPACNormativeProvision.carbohydrate1996ResiduesIons

def carbohydrateResidueIonBatch :
    GlobalNonDescriptorSourceMeaningBatch carbohydrateResidueIonProvisions := by
  simpa [carbohydrateResidueIonProvisions, carbohydrateResidueIonRows, List.map_map] using
    totalMeaningBatch Carbohydrate1996ResiduesIons.PrintedExample.all
      (fun row => IUPACNormativeProvision.carbohydrate1996ResiduesIons (.printedExample row))
      Carbohydrate1996ResiduesIons.PrintedExample.data (by intro _row; rfl)

@[simp] theorem carbohydrateResidueIonProvisionCount :
    carbohydrateResidueIonProvisions.length = 36 := by
  simp [carbohydrateResidueIonProvisions, carbohydrateResidueIonRows]

private theorem carbohydrateResidueIonRows_nodup : carbohydrateResidueIonRows.Nodup :=
  Carbohydrate1996ResiduesIons.Provision.all_nodup.of_append_right

theorem carbohydrateResidueIonProvisions_nodup :
    carbohydrateResidueIonProvisions.Nodup := by
  exact carbohydrateResidueIonRows_nodup.map
    (by intro left right equal; cases equal; rfl)

/-! ## Oligosaccharide table and symbol rows: 51 -/

def carbohydrateOligosaccharideRows :
    List Carbohydrate1996OligosaccharidesPolysaccharides.Provision :=
  Carbohydrate1996OligosaccharidesPolysaccharides.DisaccharideTrivialRow.all.map
      Carbohydrate1996OligosaccharidesPolysaccharides.Provision.disaccharideTrivialRow ++
    Carbohydrate1996OligosaccharidesPolysaccharides.SymbolRow.all.map
      Carbohydrate1996OligosaccharidesPolysaccharides.Provision.symbolRow

def carbohydrateOligosaccharideProvisions : List IUPACNormativeProvision :=
  carbohydrateOligosaccharideRows.map
    IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides

private def carbohydrateDisaccharideTrivialBatch :=
  totalMeaningBatch
    Carbohydrate1996OligosaccharidesPolysaccharides.DisaccharideTrivialRow.all
    (fun row => IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides
      (.disaccharideTrivialRow row))
    Carbohydrate1996OligosaccharidesPolysaccharides.DisaccharideTrivialRow.data
    (by intro _row; rfl)

private def carbohydrateSymbolBatch :=
  totalMeaningBatch Carbohydrate1996OligosaccharidesPolysaccharides.SymbolRow.all
    (fun row => IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides
      (.symbolRow row))
    Carbohydrate1996OligosaccharidesPolysaccharides.SymbolRow.data (by intro _row; rfl)

def carbohydrateOligosaccharideBatch :
    GlobalNonDescriptorSourceMeaningBatch carbohydrateOligosaccharideProvisions := by
  simpa [carbohydrateOligosaccharideProvisions, carbohydrateOligosaccharideRows,
    List.map_append, List.map_map] using
      carbohydrateDisaccharideTrivialBatch.append carbohydrateSymbolBatch

@[simp] theorem carbohydrateOligosaccharideProvisionCount :
    carbohydrateOligosaccharideProvisions.length = 51 := by
  simp [carbohydrateOligosaccharideProvisions, carbohydrateOligosaccharideRows]

private theorem carbohydrateOligosaccharideRows_nodup :
    carbohydrateOligosaccharideRows.Nodup := by
  have allNodup :=
    Carbohydrate1996OligosaccharidesPolysaccharides.Provision.all_nodup
  have prefixNodup := allNodup.of_append_left
  have baseAppend :
      (Carbohydrate1996OligosaccharidesPolysaccharides.Provision.base ++
        carbohydrateOligosaccharideRows).Nodup := by
    simpa [Carbohydrate1996OligosaccharidesPolysaccharides.Provision.all,
      carbohydrateOligosaccharideRows, List.append_assoc] using prefixNodup
  exact baseAppend.of_append_right

theorem carbohydrateOligosaccharideProvisions_nodup :
    carbohydrateOligosaccharideProvisions.Nodup := by
  exact carbohydrateOligosaccharideRows_nodup.map
    (by intro left right equal; cases equal; rfl)

/-! ## Appendix, errata, and glossary data rows: 172 -/

def carbohydrateAppendixRows :
    List Carbohydrate1996AppendixErrataGlossary.Provision :=
  ((Carbohydrate1996AppendixErrataGlossary.RetainedNameRow.all.map
        Carbohydrate1996AppendixErrataGlossary.Provision.retainedName ++
      Carbohydrate1996AppendixErrataGlossary.ErratumRow.all.map
        Carbohydrate1996AppendixErrataGlossary.Provision.publishedErratum) ++
    Carbohydrate1996AppendixErrataGlossary.GlossaryCell.all.map
      Carbohydrate1996AppendixErrataGlossary.Provision.glossaryCell) ++
    Carbohydrate1996AppendixErrataGlossary.GlossaryFootnote.all.map
      Carbohydrate1996AppendixErrataGlossary.Provision.glossaryFootnote

def carbohydrateAppendixProvisions : List IUPACNormativeProvision :=
  carbohydrateAppendixRows.map
    IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary

private def carbohydrateRetainedNameBatch :=
  totalMeaningBatch Carbohydrate1996AppendixErrataGlossary.RetainedNameRow.all
    (fun row => IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary
      (.retainedName row))
    Carbohydrate1996AppendixErrataGlossary.RetainedNameRow.data (by intro _row; rfl)

private def carbohydrateErratumBatch :=
  totalMeaningBatch Carbohydrate1996AppendixErrataGlossary.ErratumRow.all
    (fun row => IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary
      (.publishedErratum row))
    Carbohydrate1996AppendixErrataGlossary.ErratumRow.data (by intro _row; rfl)

private def carbohydrateGlossaryCellBatch :=
  totalMeaningBatch Carbohydrate1996AppendixErrataGlossary.GlossaryCell.all
    (fun row => IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary
      (.glossaryCell row))
    Carbohydrate1996AppendixErrataGlossary.GlossaryCell.data (by intro _row; rfl)

private def carbohydrateGlossaryFootnoteBatch :=
  totalMeaningBatch Carbohydrate1996AppendixErrataGlossary.GlossaryFootnote.all
    (fun row => IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary
      (.glossaryFootnote row))
    Carbohydrate1996AppendixErrataGlossary.GlossaryFootnote.meaning (by intro _row; rfl)

def carbohydrateAppendixBatch :
    GlobalNonDescriptorSourceMeaningBatch carbohydrateAppendixProvisions := by
  simpa [carbohydrateAppendixProvisions, carbohydrateAppendixRows,
    List.map_append, List.map_map, List.append_assoc] using
      (((carbohydrateRetainedNameBatch.append carbohydrateErratumBatch).append
        carbohydrateGlossaryCellBatch).append carbohydrateGlossaryFootnoteBatch)

@[simp] theorem carbohydrateAppendixProvisionCount :
    carbohydrateAppendixProvisions.length = 172 := by
  simp [carbohydrateAppendixProvisions, carbohydrateAppendixRows]

private theorem carbohydrateAppendixRows_nodup : carbohydrateAppendixRows.Nodup := by
  have allNodup := Carbohydrate1996AppendixErrataGlossary.Provision.all_nodup
  have baseAppend :
      (Carbohydrate1996AppendixErrataGlossary.Provision.base ++
        carbohydrateAppendixRows).Nodup := by
    simpa [Carbohydrate1996AppendixErrataGlossary.Provision.all,
      carbohydrateAppendixRows, List.append_assoc] using allNodup
  exact baseAppend.of_append_right

theorem carbohydrateAppendixProvisions_nodup : carbohydrateAppendixProvisions.Nodup := by
  exact carbohydrateAppendixRows_nodup.map
    (by intro left right equal; cases equal; rfl)

/-! ## Six transcribed graph-template rows -/

structure TranscribedGraphMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  symbolicTemplate : Option Carbohydrate1996ImageAudit.StructureGraphTemplate
  auditMaturity : Carbohydrate1996ImageAudit.GraphAuditMaturity
  deriving DecidableEq, Repr

def transcribedGraphMeaning
    (row : Carbohydrate1996ImageAudit.Provision) : TranscribedGraphMeaning :=
  match row with
  | .imageArtifact artifact =>
      ⟨artifact.data,
        Carbohydrate1996ImageAudit.symbolicTemplate? artifact.data.relativePath,
        artifact.graphAuditMaturity⟩

/-- A selected partial graph transcription has an actual symbolic template and the corresponding
maturity tag.  This does not prove fidelity to the raster source or complete atom-level meaning. -/
theorem transcribedGraphMeaning_has_symbolicTemplate
    (row : Carbohydrate1996ImageAudit.Provision)
    (member : row ∈ Carbohydrate1996ImageAudit.Provision.transcribed) :
    (transcribedGraphMeaning row).symbolicTemplate.isSome = true ∧
      (transcribedGraphMeaning row).auditMaturity = .symbolicTemplateTranscribed := by
  cases row with
  | imageArtifact artifact =>
      have transcribed : artifact.symbolicTemplateTranscribed = true :=
        (List.mem_filter.mp member).2
      have templateSome :
          (Carbohydrate1996ImageAudit.symbolicTemplate?
            artifact.data.relativePath).isSome = true := by
        have conjunction :
            artifact.data.kind.requiresMolecularGraph = true ∧
              (Carbohydrate1996ImageAudit.symbolicTemplate?
                artifact.data.relativePath).isSome = true := by
          simpa only [Carbohydrate1996ImageAudit.ImageArtifact.symbolicTemplateTranscribed,
            Bool.and_eq_true] using transcribed
        exact conjunction.2
      exact ⟨templateSome,
        Carbohydrate1996ImageAudit.transcribed_images_have_symbolic_template_maturity
          artifact transcribed⟩

def carbohydrateTranscribedGraphRows : List Carbohydrate1996ImageAudit.Provision :=
  Carbohydrate1996ImageAudit.Provision.transcribed

def carbohydrateTranscribedGraphProvisions : List IUPACNormativeProvision :=
  carbohydrateTranscribedGraphRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem carbohydrateTranscribedGraphProvisionCount :
    carbohydrateTranscribedGraphProvisions.length = 6 := by
  simp [carbohydrateTranscribedGraphProvisions, carbohydrateTranscribedGraphRows]

set_option maxRecDepth 8192 in
private theorem carbohydrateTranscribedGraphRows_nodup :
    carbohydrateTranscribedGraphRows.Nodup := by
  change
    (Carbohydrate1996ImageAudit.Provision.all.filter
      Carbohydrate1996ImageAudit.Provision.symbolicTemplateTranscribed).Nodup
  exact Carbohydrate1996ImageAudit.Provision.all_nodup.filter
    Carbohydrate1996ImageAudit.Provision.symbolicTemplateTranscribed

theorem carbohydrateTranscribedGraphProvisions_nodup :
    carbohydrateTranscribedGraphProvisions.Nodup := by
  exact carbohydrateTranscribedGraphRows_nodup.map
    (by intro left right equal; cases equal; rfl)

/-! ## Exact 315-row complete-data part-B projection -/

def carbohydrateSourceDataBTextualProvisions : List IUPACNormativeProvision :=
  carbohydrateHeteroProvisions ++
    carbohydrateAcetalProvisions ++
    carbohydrateResidueIonProvisions ++
    carbohydrateOligosaccharideProvisions ++
    carbohydrateAppendixProvisions

def carbohydrateSourceDataBTextualBatch :
    GlobalNonDescriptorSourceMeaningBatch carbohydrateSourceDataBTextualProvisions := by
  simpa [carbohydrateSourceDataBTextualProvisions, List.append_assoc] using
    carbohydrateHeteroBatch.append
      (carbohydrateAcetalBatch.append
        (carbohydrateResidueIonBatch.append
          (carbohydrateOligosaccharideBatch.append carbohydrateAppendixBatch)))

@[simp] theorem carbohydrateSourceDataBTextualProvisionCount :
    carbohydrateSourceDataBTextualProvisions.length = 315 := by
  simp [carbohydrateSourceDataBTextualProvisions]

theorem carbohydrateSourceDataBTextualProvisions_nodup :
    carbohydrateSourceDataBTextualProvisions.Nodup := by
  have oligosaccharideAppendix :
      (carbohydrateOligosaccharideProvisions ++ carbohydrateAppendixProvisions).Nodup :=
    carbohydrateOligosaccharideProvisions_nodup.append
      carbohydrateAppendixProvisions_nodup
      (by
        simp [List.disjoint_left, carbohydrateOligosaccharideProvisions,
          carbohydrateAppendixProvisions])
  have residueTail :
      (carbohydrateResidueIonProvisions ++
        (carbohydrateOligosaccharideProvisions ++ carbohydrateAppendixProvisions)).Nodup :=
    carbohydrateResidueIonProvisions_nodup.append oligosaccharideAppendix
      (by
        simp [List.disjoint_left, carbohydrateResidueIonProvisions,
          carbohydrateOligosaccharideProvisions, carbohydrateAppendixProvisions])
  have acetalTail :
      (carbohydrateAcetalProvisions ++
        (carbohydrateResidueIonProvisions ++
          (carbohydrateOligosaccharideProvisions ++
            carbohydrateAppendixProvisions))).Nodup :=
    carbohydrateAcetalProvisions_nodup.append residueTail
      (by
        simp [List.disjoint_left, carbohydrateAcetalProvisions,
          carbohydrateResidueIonProvisions, carbohydrateOligosaccharideProvisions,
          carbohydrateAppendixProvisions])
  have allTextualRows :
      (carbohydrateHeteroProvisions ++
        (carbohydrateAcetalProvisions ++
          (carbohydrateResidueIonProvisions ++
            (carbohydrateOligosaccharideProvisions ++
              carbohydrateAppendixProvisions)))).Nodup :=
    carbohydrateHeteroProvisions_nodup.append acetalTail
      (by
        simp [List.disjoint_left, carbohydrateHeteroProvisions,
          carbohydrateAcetalProvisions, carbohydrateResidueIonProvisions,
          carbohydrateOligosaccharideProvisions, carbohydrateAppendixProvisions])
  simpa [carbohydrateSourceDataBTextualProvisions, List.append_assoc] using allTextualRows

def carbohydrateSourceDataBProvisions : List IUPACNormativeProvision :=
  carbohydrateSourceDataBTextualProvisions

def carbohydrateSourceDataBBatch :
    GlobalNonDescriptorSourceMeaningBatch carbohydrateSourceDataBProvisions :=
  carbohydrateSourceDataBTextualBatch

@[simp] theorem carbohydrateSourceDataBProvisionCount :
    carbohydrateSourceDataBProvisions.length = 315 := by
  simp [carbohydrateSourceDataBProvisions]

theorem carbohydrateSourceDataBProvisions_nodup :
    carbohydrateSourceDataBProvisions.Nodup := by
  exact carbohydrateSourceDataBTextualProvisions_nodup

end GlobalNonDescriptorIndexedSourceData
end IUPACNormativeProvision
end TetraStereo.OneCenter
