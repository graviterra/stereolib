import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceMeaningBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorRetinoidSourceMeaningBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarotenoidSourceMeaningBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorSteroidSourceMeaningBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCyclitolSourceMeaningBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorNucleicAcidSourceMeaningBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorLipidSourceMeaningBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorGlycolipidSourceMeaningCompletionBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorAminoAcidPeptideSourceMeaningBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateScopeParentSourceMeaningCompletionBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateFoundationSourceMeaningCompletionBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateNamedParentSourceMeaningCompletionBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateDerivativeSourceMeaningCompletionBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaningCompletionBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaningCompletionBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateHeteroSourceMeaningCompletionBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateAcetalSourceMeaningCompletionBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateResidueIonSourceMeaningCompletionBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaningCompletionBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaningCompletionBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateAppendixSourceMeaningCompletionBatch
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorP10SourceMeaningBatch
import TetraStereo.KernelOnly

set_option autoImplicit false
























namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorMaterializedSourceMeaning

private def provisionsBeforeNamedParent : List IUPACNormativeProvision :=
  (((((((((GlobalNonDescriptorIndexedSourceMeaning.provisions ++
            GlobalNonDescriptorRetinoidSourceMeaning.provisions) ++
              GlobalNonDescriptorCarotenoidSourceMeaning.provisions) ++
                GlobalNonDescriptorSteroidSourceMeaning.provisions) ++
                  GlobalNonDescriptorCyclitolSourceMeaning.provisions) ++
                    GlobalNonDescriptorNucleicAcidSourceMeaning.provisions) ++
                      GlobalNonDescriptorLipidSourceMeaning.provisions) ++
                        GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions) ++
                          GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions) ++
                            GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions) ++
                              GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions

private def provisionsBeforeDerivative : List IUPACNormativeProvision :=
  provisionsBeforeNamedParent ++
    GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions

private def provisionsBeforeUnsaturated : List IUPACNormativeProvision :=
  provisionsBeforeDerivative ++
    GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions

private def provisionsBeforeAlditolAcid : List IUPACNormativeProvision :=
  provisionsBeforeUnsaturated ++
    GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions

private def provisionsBeforeHetero : List IUPACNormativeProvision :=
  provisionsBeforeAlditolAcid ++
    GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions

private def provisionsBeforeAcetal : List IUPACNormativeProvision :=
  provisionsBeforeHetero ++
    GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionProvisions

private def provisionsBeforeResidueIon : List IUPACNormativeProvision :=
  provisionsBeforeAcetal ++
    GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionProvisions

private def provisionsBeforeGlycosideRing : List IUPACNormativeProvision :=
  provisionsBeforeResidueIon ++
    GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionProvisions

private def provisionsBeforeOligosaccharide : List IUPACNormativeProvision :=
  provisionsBeforeGlycosideRing ++
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionProvisions

private def provisionsBeforeAppendix : List IUPACNormativeProvision :=
  provisionsBeforeOligosaccharide ++
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionProvisions

private def provisionsBeforeP10 : List IUPACNormativeProvision :=
  provisionsBeforeAppendix ++
    GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionProvisions

private def provisionsBeforeGlycosidePrinted : List IUPACNormativeProvision :=
  provisionsBeforeP10 ++ GlobalNonDescriptorP10SourceMeaning.provisions

private def provisionsBeforeOligosaccharidePrinted : List IUPACNormativeProvision :=
  provisionsBeforeGlycosidePrinted ++
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedProvisions

def provisions : List IUPACNormativeProvision :=
  provisionsBeforeOligosaccharidePrinted ++
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedProvisions

set_option maxRecDepth 4096 in
private def batchBeforeOligosaccharide :
    GlobalNonDescriptorSourceMeaningBatch provisionsBeforeOligosaccharide :=
  (((((((((((((((((GlobalNonDescriptorIndexedSourceMeaning.batch.append
            GlobalNonDescriptorRetinoidSourceMeaning.batch).append
              GlobalNonDescriptorCarotenoidSourceMeaning.batch).append
                GlobalNonDescriptorSteroidSourceMeaning.batch).append
                  GlobalNonDescriptorCyclitolSourceMeaning.batch).append
                    GlobalNonDescriptorNucleicAcidSourceMeaning.batch).append
                      GlobalNonDescriptorLipidSourceMeaning.batch).append
                        GlobalNonDescriptorGlycolipidSourceMeaning.completionBatch).append
                          GlobalNonDescriptorAminoAcidPeptideSourceMeaning.batch).append
                            GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionBatch).append
                              GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionBatch).append
                                GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionBatch).append
                                  GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionBatch).append
                                    GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionBatch).append
                                      GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionBatch).append
                                        GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionBatch).append
                                          GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionBatch).append
                                            GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionBatch).append
                                              GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionBatch

private def batchBeforeAppendix : GlobalNonDescriptorSourceMeaningBatch provisionsBeforeAppendix :=
  batchBeforeOligosaccharide.append
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionBatch

private def batchBeforeP10 : GlobalNonDescriptorSourceMeaningBatch provisionsBeforeP10 :=
  batchBeforeAppendix.append
    GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionBatch

private def batchBeforeGlycosidePrinted :
    GlobalNonDescriptorSourceMeaningBatch provisionsBeforeGlycosidePrinted :=
  batchBeforeP10.append GlobalNonDescriptorP10SourceMeaning.batch

private def batchBeforeOligosaccharidePrinted :
    GlobalNonDescriptorSourceMeaningBatch provisionsBeforeOligosaccharidePrinted :=
  batchBeforeGlycosidePrinted.append
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedBatch

def batch : GlobalNonDescriptorSourceMeaningBatch provisions :=
  batchBeforeOligosaccharidePrinted.append
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedBatch

def entries : List GlobalNonDescriptorSourceMeaningEntry :=
  batch.entries

@[simp] theorem provision_count : provisions.length = 1613 := by
  simp [provisions, provisionsBeforeOligosaccharidePrinted, provisionsBeforeGlycosidePrinted,
    provisionsBeforeP10, provisionsBeforeAppendix,
    provisionsBeforeOligosaccharide,
    provisionsBeforeGlycosideRing,
    provisionsBeforeResidueIon,
    provisionsBeforeAcetal, provisionsBeforeHetero,
    provisionsBeforeAlditolAcid,
    provisionsBeforeUnsaturated, provisionsBeforeDerivative, provisionsBeforeNamedParent]

/-- Membership in the materialized aggregate is membership in one of its named source-family
components.  Keeping this theorem propositional prevents downstream reconciliation proofs from
reducing the complete 1,613-row list. -/
theorem mem_provisions_iff_components (provision : IUPACNormativeProvision) :
    provision ∈ provisions ↔
      provision ∈ GlobalNonDescriptorIndexedSourceMeaning.provisions ∨
      provision ∈ GlobalNonDescriptorRetinoidSourceMeaning.provisions ∨
      provision ∈ GlobalNonDescriptorCarotenoidSourceMeaning.provisions ∨
      provision ∈ GlobalNonDescriptorSteroidSourceMeaning.provisions ∨
      provision ∈ GlobalNonDescriptorCyclitolSourceMeaning.provisions ∨
      provision ∈ GlobalNonDescriptorNucleicAcidSourceMeaning.provisions ∨
      provision ∈ GlobalNonDescriptorLipidSourceMeaning.provisions ∨
      provision ∈ GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions ∨
      provision ∈ GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions ∨
      provision ∈ GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions ∨
      provision ∈ GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions ∨
      provision ∈ GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions ∨
      provision ∈ GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions ∨
      provision ∈ GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions ∨
      provision ∈ GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions ∨
      provision ∈ GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionProvisions ∨
      provision ∈ GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionProvisions ∨
      provision ∈ GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionProvisions ∨
      provision ∈ GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionProvisions ∨
      provision ∈ GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionProvisions ∨
      provision ∈ GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionProvisions ∨
      provision ∈ GlobalNonDescriptorP10SourceMeaning.provisions ∨
      provision ∈ GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedProvisions ∨
      provision ∈
        GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedProvisions := by
  simp only [provisions, provisionsBeforeOligosaccharidePrinted,
    provisionsBeforeGlycosidePrinted, provisionsBeforeP10,
    provisionsBeforeAppendix, provisionsBeforeOligosaccharide,
    provisionsBeforeGlycosideRing, provisionsBeforeResidueIon, provisionsBeforeAcetal,
    provisionsBeforeHetero, provisionsBeforeAlditolAcid, provisionsBeforeUnsaturated,
    provisionsBeforeDerivative, provisionsBeforeNamedParent, List.mem_append, or_assoc]

@[simp] theorem entry_count : entries.length = 1613 := by
  rw [entries, batch.entries_length, provision_count]

@[simp] theorem entry_provisions_exact :
    entries.map GlobalNonDescriptorSourceMeaningEntry.provision = provisions :=
  batch.provisions_exact

private theorem indexed_disjoint_retinoid :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorRetinoidSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision indexedMember retinoidMember
  rw [GlobalNonDescriptorRetinoidSourceMeaning.provisions] at retinoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp retinoidMember
  simp [GlobalNonDescriptorIndexedSourceMeaning.provisions,
    GlobalNonDescriptorIndexedSourceData.provisions,
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
    GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
    GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] at indexedMember

private theorem indexed_disjoint_carotenoid :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarotenoidSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision indexedMember carotenoidMember
  rw [GlobalNonDescriptorCarotenoidSourceMeaning.provisions] at carotenoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp carotenoidMember
  simp [GlobalNonDescriptorIndexedSourceMeaning.provisions,
    GlobalNonDescriptorIndexedSourceData.provisions,
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
    GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
    GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] at indexedMember

private theorem retinoid_disjoint_carotenoid :
    GlobalNonDescriptorRetinoidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarotenoidSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision retinoidMember carotenoidMember
  rw [GlobalNonDescriptorRetinoidSourceMeaning.provisions] at retinoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp retinoidMember
  simp [GlobalNonDescriptorCarotenoidSourceMeaning.provisions] at carotenoidMember

private theorem indexed_retinoid_disjoint_carotenoid :
    (GlobalNonDescriptorIndexedSourceMeaning.provisions ++
      GlobalNonDescriptorRetinoidSourceMeaning.provisions).Disjoint
        GlobalNonDescriptorCarotenoidSourceMeaning.provisions := by
  exact List.disjoint_append_left.mpr
    ⟨indexed_disjoint_carotenoid, retinoid_disjoint_carotenoid⟩

private theorem indexed_disjoint_steroid :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorSteroidSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision indexedMember steroidMember
  rw [GlobalNonDescriptorSteroidSourceMeaning.provisions] at steroidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp steroidMember
  simp [GlobalNonDescriptorIndexedSourceMeaning.provisions,
    GlobalNonDescriptorIndexedSourceData.provisions,
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
    GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
    GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] at indexedMember

private theorem retinoid_disjoint_steroid :
    GlobalNonDescriptorRetinoidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorSteroidSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision retinoidMember steroidMember
  rw [GlobalNonDescriptorRetinoidSourceMeaning.provisions] at retinoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp retinoidMember
  simp [GlobalNonDescriptorSteroidSourceMeaning.provisions] at steroidMember

private theorem carotenoid_disjoint_steroid :
    GlobalNonDescriptorCarotenoidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorSteroidSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision carotenoidMember steroidMember
  rw [GlobalNonDescriptorCarotenoidSourceMeaning.provisions] at carotenoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp carotenoidMember
  simp [GlobalNonDescriptorSteroidSourceMeaning.provisions] at steroidMember

private theorem prior_disjoint_steroid :
    ((GlobalNonDescriptorIndexedSourceMeaning.provisions ++
      GlobalNonDescriptorRetinoidSourceMeaning.provisions) ++
        GlobalNonDescriptorCarotenoidSourceMeaning.provisions).Disjoint
          GlobalNonDescriptorSteroidSourceMeaning.provisions := by
  exact List.disjoint_append_left.mpr
    ⟨List.disjoint_append_left.mpr ⟨indexed_disjoint_steroid, retinoid_disjoint_steroid⟩,
      carotenoid_disjoint_steroid⟩

private theorem indexed_disjoint_cyclitol :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCyclitolSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision indexedMember cyclitolMember
  rw [GlobalNonDescriptorCyclitolSourceMeaning.provisions] at cyclitolMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp cyclitolMember
  simp [GlobalNonDescriptorIndexedSourceMeaning.provisions,
    GlobalNonDescriptorIndexedSourceData.provisions,
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
    GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
    GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] at indexedMember

private theorem retinoid_disjoint_cyclitol :
    GlobalNonDescriptorRetinoidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCyclitolSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision retinoidMember cyclitolMember
  rw [GlobalNonDescriptorRetinoidSourceMeaning.provisions] at retinoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp retinoidMember
  simp [GlobalNonDescriptorCyclitolSourceMeaning.provisions] at cyclitolMember

private theorem carotenoid_disjoint_cyclitol :
    GlobalNonDescriptorCarotenoidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCyclitolSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision carotenoidMember cyclitolMember
  rw [GlobalNonDescriptorCarotenoidSourceMeaning.provisions] at carotenoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp carotenoidMember
  simp [GlobalNonDescriptorCyclitolSourceMeaning.provisions] at cyclitolMember

private theorem steroid_disjoint_cyclitol :
    GlobalNonDescriptorSteroidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCyclitolSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision steroidMember cyclitolMember
  rw [GlobalNonDescriptorSteroidSourceMeaning.provisions] at steroidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp steroidMember
  simp [GlobalNonDescriptorCyclitolSourceMeaning.provisions] at cyclitolMember

private theorem prior_disjoint_cyclitol :
    (((GlobalNonDescriptorIndexedSourceMeaning.provisions ++
      GlobalNonDescriptorRetinoidSourceMeaning.provisions) ++
        GlobalNonDescriptorCarotenoidSourceMeaning.provisions) ++
          GlobalNonDescriptorSteroidSourceMeaning.provisions).Disjoint
            GlobalNonDescriptorCyclitolSourceMeaning.provisions := by
  exact List.disjoint_append_left.mpr
    ⟨List.disjoint_append_left.mpr
      ⟨List.disjoint_append_left.mpr
        ⟨indexed_disjoint_cyclitol, retinoid_disjoint_cyclitol⟩,
        carotenoid_disjoint_cyclitol⟩,
      steroid_disjoint_cyclitol⟩

private theorem indexed_disjoint_nucleic_acid :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorNucleicAcidSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision indexedMember nucleicAcidMember
  rw [GlobalNonDescriptorNucleicAcidSourceMeaning.provisions] at nucleicAcidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp nucleicAcidMember
  simp [GlobalNonDescriptorIndexedSourceMeaning.provisions,
    GlobalNonDescriptorIndexedSourceData.provisions,
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
    GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
    GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] at indexedMember

private theorem retinoid_disjoint_nucleic_acid :
    GlobalNonDescriptorRetinoidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorNucleicAcidSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision retinoidMember nucleicAcidMember
  rw [GlobalNonDescriptorRetinoidSourceMeaning.provisions] at retinoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp retinoidMember
  simp [GlobalNonDescriptorNucleicAcidSourceMeaning.provisions] at nucleicAcidMember

private theorem carotenoid_disjoint_nucleic_acid :
    GlobalNonDescriptorCarotenoidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorNucleicAcidSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision carotenoidMember nucleicAcidMember
  rw [GlobalNonDescriptorCarotenoidSourceMeaning.provisions] at carotenoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp carotenoidMember
  simp [GlobalNonDescriptorNucleicAcidSourceMeaning.provisions] at nucleicAcidMember

private theorem steroid_disjoint_nucleic_acid :
    GlobalNonDescriptorSteroidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorNucleicAcidSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision steroidMember nucleicAcidMember
  rw [GlobalNonDescriptorSteroidSourceMeaning.provisions] at steroidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp steroidMember
  simp [GlobalNonDescriptorNucleicAcidSourceMeaning.provisions] at nucleicAcidMember

private theorem cyclitol_disjoint_nucleic_acid :
    GlobalNonDescriptorCyclitolSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorNucleicAcidSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision cyclitolMember nucleicAcidMember
  rw [GlobalNonDescriptorCyclitolSourceMeaning.provisions] at cyclitolMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp cyclitolMember
  simp [GlobalNonDescriptorNucleicAcidSourceMeaning.provisions] at nucleicAcidMember

private theorem prior_disjoint_nucleic_acid :
    ((((GlobalNonDescriptorIndexedSourceMeaning.provisions ++
      GlobalNonDescriptorRetinoidSourceMeaning.provisions) ++
        GlobalNonDescriptorCarotenoidSourceMeaning.provisions) ++
          GlobalNonDescriptorSteroidSourceMeaning.provisions) ++
            GlobalNonDescriptorCyclitolSourceMeaning.provisions).Disjoint
              GlobalNonDescriptorNucleicAcidSourceMeaning.provisions := by
  exact List.disjoint_append_left.mpr
    ⟨List.disjoint_append_left.mpr
      ⟨List.disjoint_append_left.mpr
        ⟨List.disjoint_append_left.mpr
          ⟨indexed_disjoint_nucleic_acid, retinoid_disjoint_nucleic_acid⟩,
          carotenoid_disjoint_nucleic_acid⟩,
        steroid_disjoint_nucleic_acid⟩,
      cyclitol_disjoint_nucleic_acid⟩

private theorem indexed_disjoint_lipid :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorLipidSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision indexedMember lipidMember
  rw [GlobalNonDescriptorLipidSourceMeaning.provisions] at lipidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp lipidMember
  simp [GlobalNonDescriptorIndexedSourceMeaning.provisions,
    GlobalNonDescriptorIndexedSourceData.provisions,
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
    GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
    GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] at indexedMember

private theorem retinoid_disjoint_lipid :
    GlobalNonDescriptorRetinoidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorLipidSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision retinoidMember lipidMember
  rw [GlobalNonDescriptorRetinoidSourceMeaning.provisions] at retinoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp retinoidMember
  simp [GlobalNonDescriptorLipidSourceMeaning.provisions] at lipidMember

private theorem carotenoid_disjoint_lipid :
    GlobalNonDescriptorCarotenoidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorLipidSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision carotenoidMember lipidMember
  rw [GlobalNonDescriptorCarotenoidSourceMeaning.provisions] at carotenoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp carotenoidMember
  simp [GlobalNonDescriptorLipidSourceMeaning.provisions] at lipidMember

private theorem steroid_disjoint_lipid :
    GlobalNonDescriptorSteroidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorLipidSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision steroidMember lipidMember
  rw [GlobalNonDescriptorSteroidSourceMeaning.provisions] at steroidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp steroidMember
  simp [GlobalNonDescriptorLipidSourceMeaning.provisions] at lipidMember

private theorem cyclitol_disjoint_lipid :
    GlobalNonDescriptorCyclitolSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorLipidSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision cyclitolMember lipidMember
  rw [GlobalNonDescriptorCyclitolSourceMeaning.provisions] at cyclitolMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp cyclitolMember
  simp [GlobalNonDescriptorLipidSourceMeaning.provisions] at lipidMember

private theorem nucleic_acid_disjoint_lipid :
    GlobalNonDescriptorNucleicAcidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorLipidSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision nucleicAcidMember lipidMember
  rw [GlobalNonDescriptorNucleicAcidSourceMeaning.provisions] at nucleicAcidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp nucleicAcidMember
  simp [GlobalNonDescriptorLipidSourceMeaning.provisions] at lipidMember

private theorem prior_disjoint_lipid :
    (((((GlobalNonDescriptorIndexedSourceMeaning.provisions ++
      GlobalNonDescriptorRetinoidSourceMeaning.provisions) ++
        GlobalNonDescriptorCarotenoidSourceMeaning.provisions) ++
          GlobalNonDescriptorSteroidSourceMeaning.provisions) ++
            GlobalNonDescriptorCyclitolSourceMeaning.provisions) ++
              GlobalNonDescriptorNucleicAcidSourceMeaning.provisions).Disjoint
                GlobalNonDescriptorLipidSourceMeaning.provisions := by
  exact List.disjoint_append_left.mpr
    ⟨List.disjoint_append_left.mpr
      ⟨List.disjoint_append_left.mpr
        ⟨List.disjoint_append_left.mpr
          ⟨List.disjoint_append_left.mpr
            ⟨indexed_disjoint_lipid, retinoid_disjoint_lipid⟩,
            carotenoid_disjoint_lipid⟩,
          steroid_disjoint_lipid⟩,
        cyclitol_disjoint_lipid⟩,
      nucleic_acid_disjoint_lipid⟩

private theorem indexed_disjoint_glycolipid_completion :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision indexedMember completionMember
  rw [GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions,
    GlobalNonDescriptorGlycolipidSourceMeaning.completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have glycolipidMember :
      IUPACNormativeProvision.glycolipid1997 row ∈
        GlobalNonDescriptorIndexedSourceData.glycolipidProvisions := by
    simpa [GlobalNonDescriptorIndexedSourceMeaning.provisions,
      GlobalNonDescriptorIndexedSourceData.provisions,
      GlobalNonDescriptorIndexedSourceData.carbohydrateTextualProvisions,
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
      GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
      GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] using indexedMember
  have completionMapped :
      IUPACNormativeProvision.glycolipid1997 row ∈
        GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions :=
    List.mem_map.mpr ⟨row, rowMember, rfl⟩
  exact (List.disjoint_left.mp
    GlobalNonDescriptorGlycolipidSourceMeaning.completion_disjoint_indexed)
      completionMapped glycolipidMember

private theorem retinoid_disjoint_glycolipid_completion :
    GlobalNonDescriptorRetinoidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision retinoidMember completionMember
  rw [GlobalNonDescriptorRetinoidSourceMeaning.provisions] at retinoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp retinoidMember
  simp [GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions] at completionMember

private theorem carotenoid_disjoint_glycolipid_completion :
    GlobalNonDescriptorCarotenoidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision carotenoidMember completionMember
  rw [GlobalNonDescriptorCarotenoidSourceMeaning.provisions] at carotenoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp carotenoidMember
  simp [GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions] at completionMember

private theorem steroid_disjoint_glycolipid_completion :
    GlobalNonDescriptorSteroidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision steroidMember completionMember
  rw [GlobalNonDescriptorSteroidSourceMeaning.provisions] at steroidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp steroidMember
  simp [GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions] at completionMember

private theorem cyclitol_disjoint_glycolipid_completion :
    GlobalNonDescriptorCyclitolSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision cyclitolMember completionMember
  rw [GlobalNonDescriptorCyclitolSourceMeaning.provisions] at cyclitolMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp cyclitolMember
  simp [GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions] at completionMember

private theorem nucleic_acid_disjoint_glycolipid_completion :
    GlobalNonDescriptorNucleicAcidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision nucleicAcidMember completionMember
  rw [GlobalNonDescriptorNucleicAcidSourceMeaning.provisions] at nucleicAcidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp nucleicAcidMember
  simp [GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions] at completionMember

private theorem lipid_disjoint_glycolipid_completion :
    GlobalNonDescriptorLipidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision lipidMember completionMember
  rw [GlobalNonDescriptorLipidSourceMeaning.provisions] at lipidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp lipidMember
  simp [GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions] at completionMember

private theorem prior_disjoint_glycolipid_completion :
    ((((((GlobalNonDescriptorIndexedSourceMeaning.provisions ++
      GlobalNonDescriptorRetinoidSourceMeaning.provisions) ++
        GlobalNonDescriptorCarotenoidSourceMeaning.provisions) ++
          GlobalNonDescriptorSteroidSourceMeaning.provisions) ++
            GlobalNonDescriptorCyclitolSourceMeaning.provisions) ++
              GlobalNonDescriptorNucleicAcidSourceMeaning.provisions) ++
                GlobalNonDescriptorLipidSourceMeaning.provisions).Disjoint
                  GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions := by
  exact List.disjoint_append_left.mpr
    ⟨List.disjoint_append_left.mpr
      ⟨List.disjoint_append_left.mpr
        ⟨List.disjoint_append_left.mpr
          ⟨List.disjoint_append_left.mpr
            ⟨List.disjoint_append_left.mpr
              ⟨indexed_disjoint_glycolipid_completion,
                retinoid_disjoint_glycolipid_completion⟩,
              carotenoid_disjoint_glycolipid_completion⟩,
            steroid_disjoint_glycolipid_completion⟩,
          cyclitol_disjoint_glycolipid_completion⟩,
        nucleic_acid_disjoint_glycolipid_completion⟩,
      lipid_disjoint_glycolipid_completion⟩

private theorem indexed_disjoint_amino_acid_peptide :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision indexedMember aminoAcidPeptideMember
  rw [GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions] at aminoAcidPeptideMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp aminoAcidPeptideMember
  simp [GlobalNonDescriptorIndexedSourceMeaning.provisions,
    GlobalNonDescriptorIndexedSourceData.provisions,
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
    GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
    GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] at indexedMember

private theorem retinoid_disjoint_amino_acid_peptide :
    GlobalNonDescriptorRetinoidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision retinoidMember aminoAcidPeptideMember
  rw [GlobalNonDescriptorRetinoidSourceMeaning.provisions] at retinoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp retinoidMember
  simp [GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions] at aminoAcidPeptideMember

private theorem carotenoid_disjoint_amino_acid_peptide :
    GlobalNonDescriptorCarotenoidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision carotenoidMember aminoAcidPeptideMember
  rw [GlobalNonDescriptorCarotenoidSourceMeaning.provisions] at carotenoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp carotenoidMember
  simp [GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions] at aminoAcidPeptideMember

private theorem steroid_disjoint_amino_acid_peptide :
    GlobalNonDescriptorSteroidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision steroidMember aminoAcidPeptideMember
  rw [GlobalNonDescriptorSteroidSourceMeaning.provisions] at steroidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp steroidMember
  simp [GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions] at aminoAcidPeptideMember

private theorem cyclitol_disjoint_amino_acid_peptide :
    GlobalNonDescriptorCyclitolSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision cyclitolMember aminoAcidPeptideMember
  rw [GlobalNonDescriptorCyclitolSourceMeaning.provisions] at cyclitolMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp cyclitolMember
  simp [GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions] at aminoAcidPeptideMember

private theorem nucleic_acid_disjoint_amino_acid_peptide :
    GlobalNonDescriptorNucleicAcidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision nucleicAcidMember aminoAcidPeptideMember
  rw [GlobalNonDescriptorNucleicAcidSourceMeaning.provisions] at nucleicAcidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp nucleicAcidMember
  simp [GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions] at aminoAcidPeptideMember

private theorem lipid_disjoint_amino_acid_peptide :
    GlobalNonDescriptorLipidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision lipidMember aminoAcidPeptideMember
  rw [GlobalNonDescriptorLipidSourceMeaning.provisions] at lipidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp lipidMember
  simp [GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions] at aminoAcidPeptideMember

private theorem glycolipid_completion_disjoint_amino_acid_peptide :
    GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions.Disjoint
      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision glycolipidMember aminoAcidPeptideMember
  rw [GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions] at glycolipidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp glycolipidMember
  simp [GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions] at aminoAcidPeptideMember

private theorem prior_disjoint_amino_acid_peptide :
    (((((((GlobalNonDescriptorIndexedSourceMeaning.provisions ++
      GlobalNonDescriptorRetinoidSourceMeaning.provisions) ++
        GlobalNonDescriptorCarotenoidSourceMeaning.provisions) ++
          GlobalNonDescriptorSteroidSourceMeaning.provisions) ++
            GlobalNonDescriptorCyclitolSourceMeaning.provisions) ++
              GlobalNonDescriptorNucleicAcidSourceMeaning.provisions) ++
                GlobalNonDescriptorLipidSourceMeaning.provisions) ++
                  GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions).Disjoint
                    GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions := by
  exact List.disjoint_append_left.mpr
    ⟨List.disjoint_append_left.mpr
      ⟨List.disjoint_append_left.mpr
        ⟨List.disjoint_append_left.mpr
          ⟨List.disjoint_append_left.mpr
            ⟨List.disjoint_append_left.mpr
              ⟨List.disjoint_append_left.mpr
                ⟨indexed_disjoint_amino_acid_peptide,
                  retinoid_disjoint_amino_acid_peptide⟩,
                carotenoid_disjoint_amino_acid_peptide⟩,
              steroid_disjoint_amino_acid_peptide⟩,
            cyclitol_disjoint_amino_acid_peptide⟩,
          nucleic_acid_disjoint_amino_acid_peptide⟩,
        lipid_disjoint_amino_acid_peptide⟩,
      glycolipid_completion_disjoint_amino_acid_peptide⟩

private theorem indexed_disjoint_carbohydrate_scope_parent_completion :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision indexedMember completionMember
  rw [GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedScopeMember :
      IUPACNormativeProvision.carbohydrate1996ScopeParent row ∈
        GlobalNonDescriptorIndexedSourceData.carbohydrateScopeParentProvisions := by
    simpa [GlobalNonDescriptorIndexedSourceMeaning.provisions,
      GlobalNonDescriptorIndexedSourceData.provisions,
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
      GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
      GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] using indexedMember
  have completionMapped :
      IUPACNormativeProvision.carbohydrate1996ScopeParent row ∈
        GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions :=
    List.mem_map.mpr ⟨row, rowMember, rfl⟩
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completion_disjoint_indexed)
      completionMapped indexedScopeMember

private theorem retinoid_disjoint_carbohydrate_scope_parent_completion :
    GlobalNonDescriptorRetinoidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision retinoidMember completionMember
  rw [GlobalNonDescriptorRetinoidSourceMeaning.provisions] at retinoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp retinoidMember
  simp [GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions] at completionMember

private theorem carotenoid_disjoint_carbohydrate_scope_parent_completion :
    GlobalNonDescriptorCarotenoidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision carotenoidMember completionMember
  rw [GlobalNonDescriptorCarotenoidSourceMeaning.provisions] at carotenoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp carotenoidMember
  simp [GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions] at completionMember

private theorem steroid_disjoint_carbohydrate_scope_parent_completion :
    GlobalNonDescriptorSteroidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision steroidMember completionMember
  rw [GlobalNonDescriptorSteroidSourceMeaning.provisions] at steroidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp steroidMember
  simp [GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions] at completionMember

private theorem cyclitol_disjoint_carbohydrate_scope_parent_completion :
    GlobalNonDescriptorCyclitolSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision cyclitolMember completionMember
  rw [GlobalNonDescriptorCyclitolSourceMeaning.provisions] at cyclitolMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp cyclitolMember
  simp [GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions] at completionMember

private theorem nucleic_acid_disjoint_carbohydrate_scope_parent_completion :
    GlobalNonDescriptorNucleicAcidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision nucleicAcidMember completionMember
  rw [GlobalNonDescriptorNucleicAcidSourceMeaning.provisions] at nucleicAcidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp nucleicAcidMember
  simp [GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions] at completionMember

private theorem lipid_disjoint_carbohydrate_scope_parent_completion :
    GlobalNonDescriptorLipidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision lipidMember completionMember
  rw [GlobalNonDescriptorLipidSourceMeaning.provisions] at lipidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp lipidMember
  simp [GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions] at completionMember

private theorem glycolipid_completion_disjoint_carbohydrate_scope_parent_completion :
    GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions.Disjoint
      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision glycolipidMember completionMember
  rw [GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions] at glycolipidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp glycolipidMember
  simp [GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions] at completionMember

private theorem amino_acid_peptide_disjoint_carbohydrate_scope_parent_completion :
    GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision aminoAcidPeptideMember completionMember
  rw [GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions] at aminoAcidPeptideMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp aminoAcidPeptideMember
  simp [GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions] at completionMember

private theorem prior_disjoint_carbohydrate_scope_parent_completion :
    ((((((((GlobalNonDescriptorIndexedSourceMeaning.provisions ++
      GlobalNonDescriptorRetinoidSourceMeaning.provisions) ++
        GlobalNonDescriptorCarotenoidSourceMeaning.provisions) ++
          GlobalNonDescriptorSteroidSourceMeaning.provisions) ++
            GlobalNonDescriptorCyclitolSourceMeaning.provisions) ++
              GlobalNonDescriptorNucleicAcidSourceMeaning.provisions) ++
                GlobalNonDescriptorLipidSourceMeaning.provisions) ++
                  GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions) ++
                    GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions).Disjoint
                      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions := by
  exact List.disjoint_append_left.mpr
    ⟨List.disjoint_append_left.mpr
      ⟨List.disjoint_append_left.mpr
        ⟨List.disjoint_append_left.mpr
          ⟨List.disjoint_append_left.mpr
            ⟨List.disjoint_append_left.mpr
              ⟨List.disjoint_append_left.mpr
                ⟨List.disjoint_append_left.mpr
                  ⟨indexed_disjoint_carbohydrate_scope_parent_completion,
                    retinoid_disjoint_carbohydrate_scope_parent_completion⟩,
                  carotenoid_disjoint_carbohydrate_scope_parent_completion⟩,
                steroid_disjoint_carbohydrate_scope_parent_completion⟩,
              cyclitol_disjoint_carbohydrate_scope_parent_completion⟩,
            nucleic_acid_disjoint_carbohydrate_scope_parent_completion⟩,
          lipid_disjoint_carbohydrate_scope_parent_completion⟩,
        glycolipid_completion_disjoint_carbohydrate_scope_parent_completion⟩,
      amino_acid_peptide_disjoint_carbohydrate_scope_parent_completion⟩

private theorem indexed_disjoint_carbohydrate_foundation_completion :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision indexedMember completionMember
  rw [GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedFoundationMember :
      IUPACNormativeProvision.carbohydrate1996Foundation row ∈
        GlobalNonDescriptorIndexedSourceData.carbohydrateFoundationProvisions := by
    simpa [GlobalNonDescriptorIndexedSourceMeaning.provisions,
      GlobalNonDescriptorIndexedSourceData.provisions,
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
      GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
      GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] using indexedMember
  have completionMapped :
      IUPACNormativeProvision.carbohydrate1996Foundation row ∈
        GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions :=
    List.mem_map.mpr ⟨row, rowMember, rfl⟩
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completion_disjoint_indexed)
      completionMapped indexedFoundationMember

private theorem retinoid_disjoint_carbohydrate_foundation_completion :
    GlobalNonDescriptorRetinoidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision retinoidMember completionMember
  rw [GlobalNonDescriptorRetinoidSourceMeaning.provisions] at retinoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp retinoidMember
  simp [GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions]
    at completionMember

private theorem carotenoid_disjoint_carbohydrate_foundation_completion :
    GlobalNonDescriptorCarotenoidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision carotenoidMember completionMember
  rw [GlobalNonDescriptorCarotenoidSourceMeaning.provisions] at carotenoidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp carotenoidMember
  simp [GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions]
    at completionMember

private theorem steroid_disjoint_carbohydrate_foundation_completion :
    GlobalNonDescriptorSteroidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision steroidMember completionMember
  rw [GlobalNonDescriptorSteroidSourceMeaning.provisions] at steroidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp steroidMember
  simp [GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions]
    at completionMember

private theorem cyclitol_disjoint_carbohydrate_foundation_completion :
    GlobalNonDescriptorCyclitolSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision cyclitolMember completionMember
  rw [GlobalNonDescriptorCyclitolSourceMeaning.provisions] at cyclitolMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp cyclitolMember
  simp [GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions]
    at completionMember

private theorem nucleic_acid_disjoint_carbohydrate_foundation_completion :
    GlobalNonDescriptorNucleicAcidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision nucleicAcidMember completionMember
  rw [GlobalNonDescriptorNucleicAcidSourceMeaning.provisions] at nucleicAcidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp nucleicAcidMember
  simp [GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions]
    at completionMember

private theorem lipid_disjoint_carbohydrate_foundation_completion :
    GlobalNonDescriptorLipidSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision lipidMember completionMember
  rw [GlobalNonDescriptorLipidSourceMeaning.provisions] at lipidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp lipidMember
  simp [GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions]
    at completionMember

private theorem glycolipid_completion_disjoint_carbohydrate_foundation_completion :
    GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions.Disjoint
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision glycolipidMember completionMember
  rw [GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions] at glycolipidMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp glycolipidMember
  simp [GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions]
    at completionMember

private theorem amino_acid_peptide_disjoint_carbohydrate_foundation_completion :
    GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision aminoAcidPeptideMember completionMember
  rw [GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions] at aminoAcidPeptideMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp aminoAcidPeptideMember
  simp [GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions]
    at completionMember

private theorem carbohydrate_scope_parent_completion_disjoint_foundation_completion :
    GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions.Disjoint
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision scopeParentMember foundationMember
  rw [GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions]
    at scopeParentMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp scopeParentMember
  simp [GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions]
    at foundationMember

private theorem prior_disjoint_carbohydrate_foundation_completion :
    (((((((((GlobalNonDescriptorIndexedSourceMeaning.provisions ++
      GlobalNonDescriptorRetinoidSourceMeaning.provisions) ++
        GlobalNonDescriptorCarotenoidSourceMeaning.provisions) ++
          GlobalNonDescriptorSteroidSourceMeaning.provisions) ++
            GlobalNonDescriptorCyclitolSourceMeaning.provisions) ++
              GlobalNonDescriptorNucleicAcidSourceMeaning.provisions) ++
                GlobalNonDescriptorLipidSourceMeaning.provisions) ++
                  GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions) ++
                    GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions) ++
                      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions).Disjoint
                        GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions := by
  exact List.disjoint_append_left.mpr
    ⟨List.disjoint_append_left.mpr
      ⟨List.disjoint_append_left.mpr
        ⟨List.disjoint_append_left.mpr
          ⟨List.disjoint_append_left.mpr
            ⟨List.disjoint_append_left.mpr
              ⟨List.disjoint_append_left.mpr
                ⟨List.disjoint_append_left.mpr
                  ⟨List.disjoint_append_left.mpr
                    ⟨indexed_disjoint_carbohydrate_foundation_completion,
                      retinoid_disjoint_carbohydrate_foundation_completion⟩,
                    carotenoid_disjoint_carbohydrate_foundation_completion⟩,
                  steroid_disjoint_carbohydrate_foundation_completion⟩,
                cyclitol_disjoint_carbohydrate_foundation_completion⟩,
              nucleic_acid_disjoint_carbohydrate_foundation_completion⟩,
            lipid_disjoint_carbohydrate_foundation_completion⟩,
          glycolipid_completion_disjoint_carbohydrate_foundation_completion⟩,
        amino_acid_peptide_disjoint_carbohydrate_foundation_completion⟩,
      carbohydrate_scope_parent_completion_disjoint_foundation_completion⟩

private theorem indexed_disjoint_carbohydrate_named_parent_completion :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision indexedMember completionMember
  rw [GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedNamedParentMember :
      IUPACNormativeProvision.carbohydrate1996NamedParents row ∈
        GlobalNonDescriptorIndexedSourceData.carbohydrateNamedParentProvisions := by
    simpa [GlobalNonDescriptorIndexedSourceMeaning.provisions,
      GlobalNonDescriptorIndexedSourceData.provisions,
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
      GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
      GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] using indexedMember
  have completionMapped :
      IUPACNormativeProvision.carbohydrate1996NamedParents row ∈
        GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions :=
    List.mem_map.mpr ⟨row, rowMember, rfl⟩
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completion_disjoint_indexed)
      completionMapped indexedNamedParentMember

private theorem prior_disjoint_carbohydrate_named_parent_completion :
    provisionsBeforeNamedParent.Disjoint
      GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision priorMember completionMember
  rw [GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionRows] at completionMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp completionMember
  rw [provisionsBeforeNamedParent, List.mem_append] at priorMember
  rcases priorMember with throughScopeParentMember | foundationMember
  · rw [List.mem_append] at throughScopeParentMember
    rcases throughScopeParentMember with throughAminoAcidPeptideMember | scopeParentMember
    · rw [List.mem_append] at throughAminoAcidPeptideMember
      rcases throughAminoAcidPeptideMember with throughGlycolipidMember | aminoAcidPeptideMember
      · rw [List.mem_append] at throughGlycolipidMember
        rcases throughGlycolipidMember with throughLipidMember | glycolipidMember
        · rw [List.mem_append] at throughLipidMember
          rcases throughLipidMember with throughNucleicAcidMember | lipidMember
          · rw [List.mem_append] at throughNucleicAcidMember
            rcases throughNucleicAcidMember with throughCyclitolMember | nucleicAcidMember
            · rw [List.mem_append] at throughCyclitolMember
              rcases throughCyclitolMember with throughSteroidMember | cyclitolMember
              · rw [List.mem_append] at throughSteroidMember
                rcases throughSteroidMember with throughCarotenoidMember | steroidMember
                · rw [List.mem_append] at throughCarotenoidMember
                  rcases throughCarotenoidMember with throughRetinoidMember | carotenoidMember
                  · rw [List.mem_append] at throughRetinoidMember
                    rcases throughRetinoidMember with indexedMember | retinoidMember
                    · exact (List.disjoint_left.mp
                        indexed_disjoint_carbohydrate_named_parent_completion)
                          indexedMember
                          (List.mem_map.mpr ⟨row, _rowMember, rfl⟩)
                    · simp [GlobalNonDescriptorRetinoidSourceMeaning.provisions]
                        at retinoidMember
                  · simp [GlobalNonDescriptorCarotenoidSourceMeaning.provisions]
                      at carotenoidMember
                · simp [GlobalNonDescriptorSteroidSourceMeaning.provisions] at steroidMember
              · simp [GlobalNonDescriptorCyclitolSourceMeaning.provisions] at cyclitolMember
            · simp [GlobalNonDescriptorNucleicAcidSourceMeaning.provisions]
                at nucleicAcidMember
          · simp [GlobalNonDescriptorLipidSourceMeaning.provisions] at lipidMember
        · simp [GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions]
            at glycolipidMember
      · simp [GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions]
          at aminoAcidPeptideMember
    · simp [GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions]
        at scopeParentMember
  · simp [GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions]
      at foundationMember

private theorem indexed_disjoint_carbohydrate_derivative_completion :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision indexedMember completionMember
  rw [GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedDerivativeMember :
      IUPACNormativeProvision.carbohydrate1996Derivatives row ∈
        GlobalNonDescriptorIndexedSourceData.carbohydrateDerivativeProvisions := by
    simpa [GlobalNonDescriptorIndexedSourceMeaning.provisions,
      GlobalNonDescriptorIndexedSourceData.provisions,
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
      GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
      GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] using indexedMember
  have completionMapped :
      IUPACNormativeProvision.carbohydrate1996Derivatives row ∈
        GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions :=
    List.mem_map.mpr ⟨row, rowMember, rfl⟩
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completion_disjoint_indexed)
      completionMapped indexedDerivativeMember

private theorem prior_disjoint_carbohydrate_derivative_completion :
    provisionsBeforeDerivative.Disjoint
      GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision priorMember completionMember
  rw [GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionRows] at completionMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp completionMember
  rw [provisionsBeforeDerivative, List.mem_append] at priorMember
  rcases priorMember with beforeNamedParentMember | namedParentMember
  · rw [provisionsBeforeNamedParent, List.mem_append] at beforeNamedParentMember
    rcases beforeNamedParentMember with throughScopeParentMember | foundationMember
    · rw [List.mem_append] at throughScopeParentMember
      rcases throughScopeParentMember with throughAminoAcidPeptideMember | scopeParentMember
      · rw [List.mem_append] at throughAminoAcidPeptideMember
        rcases throughAminoAcidPeptideMember with throughGlycolipidMember | aminoAcidPeptideMember
        · rw [List.mem_append] at throughGlycolipidMember
          rcases throughGlycolipidMember with throughLipidMember | glycolipidMember
          · rw [List.mem_append] at throughLipidMember
            rcases throughLipidMember with throughNucleicAcidMember | lipidMember
            · rw [List.mem_append] at throughNucleicAcidMember
              rcases throughNucleicAcidMember with throughCyclitolMember | nucleicAcidMember
              · rw [List.mem_append] at throughCyclitolMember
                rcases throughCyclitolMember with throughSteroidMember | cyclitolMember
                · rw [List.mem_append] at throughSteroidMember
                  rcases throughSteroidMember with throughCarotenoidMember | steroidMember
                  · rw [List.mem_append] at throughCarotenoidMember
                    rcases throughCarotenoidMember with throughRetinoidMember | carotenoidMember
                    · rw [List.mem_append] at throughRetinoidMember
                      rcases throughRetinoidMember with indexedMember | retinoidMember
                      · exact (List.disjoint_left.mp
                          indexed_disjoint_carbohydrate_derivative_completion)
                            indexedMember (List.mem_map.mpr ⟨row, _rowMember, rfl⟩)
                      · simp [GlobalNonDescriptorRetinoidSourceMeaning.provisions]
                          at retinoidMember
                    · simp [GlobalNonDescriptorCarotenoidSourceMeaning.provisions]
                        at carotenoidMember
                  · simp [GlobalNonDescriptorSteroidSourceMeaning.provisions] at steroidMember
                · simp [GlobalNonDescriptorCyclitolSourceMeaning.provisions] at cyclitolMember
              · simp [GlobalNonDescriptorNucleicAcidSourceMeaning.provisions]
                  at nucleicAcidMember
            · simp [GlobalNonDescriptorLipidSourceMeaning.provisions] at lipidMember
          · simp [GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions]
              at glycolipidMember
        · simp [GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions]
            at aminoAcidPeptideMember
      · simp [GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions]
          at scopeParentMember
    · simp [GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions]
        at foundationMember
  · simp [GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions]
      at namedParentMember

private theorem indexed_disjoint_carbohydrate_unsaturated_completion :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision indexedMember completionMember
  rw [GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedUnsaturatedMember :
      IUPACNormativeProvision.carbohydrate1996UnsaturatedBranched row ∈
        GlobalNonDescriptorIndexedSourceData.carbohydrateUnsaturatedProvisions := by
    simpa [GlobalNonDescriptorIndexedSourceMeaning.provisions,
      GlobalNonDescriptorIndexedSourceData.provisions,
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
      GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
      GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] using indexedMember
  have completionMapped :
      IUPACNormativeProvision.carbohydrate1996UnsaturatedBranched row ∈
        GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions :=
    List.mem_map.mpr ⟨row, rowMember, rfl⟩
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completion_disjoint_indexed)
      completionMapped indexedUnsaturatedMember

private theorem prior_disjoint_carbohydrate_unsaturated_completion :
    provisionsBeforeUnsaturated.Disjoint
      GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision priorMember completionMember
  rw [GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedMember :
      IUPACNormativeProvision.carbohydrate1996UnsaturatedBranched row ∈
        GlobalNonDescriptorIndexedSourceMeaning.provisions := by
    simpa [provisionsBeforeUnsaturated, provisionsBeforeDerivative, provisionsBeforeNamedParent,
      GlobalNonDescriptorRetinoidSourceMeaning.provisions,
      GlobalNonDescriptorCarotenoidSourceMeaning.provisions,
      GlobalNonDescriptorSteroidSourceMeaning.provisions,
      GlobalNonDescriptorCyclitolSourceMeaning.provisions,
      GlobalNonDescriptorNucleicAcidSourceMeaning.provisions,
      GlobalNonDescriptorLipidSourceMeaning.provisions,
      GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions,
      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions,
      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions] using priorMember
  exact (List.disjoint_left.mp indexed_disjoint_carbohydrate_unsaturated_completion)
    indexedMember (List.mem_map.mpr ⟨row, rowMember, rfl⟩)

private theorem indexed_disjoint_carbohydrate_alditol_acid_completion :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision indexedMember completionMember
  rw [GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedAlditolAcidMember :
      IUPACNormativeProvision.carbohydrate1996AlditolsAcids row ∈
        GlobalNonDescriptorIndexedSourceData.carbohydrateAlditolAcidProvisions := by
    simpa [GlobalNonDescriptorIndexedSourceMeaning.provisions,
      GlobalNonDescriptorIndexedSourceData.provisions,
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
      GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
      GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] using indexedMember
  have completionMapped :
      IUPACNormativeProvision.carbohydrate1996AlditolsAcids row ∈
        GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions :=
    List.mem_map.mpr ⟨row, rowMember, rfl⟩
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completion_disjoint_indexed)
      completionMapped indexedAlditolAcidMember

private theorem prior_disjoint_carbohydrate_alditol_acid_completion :
    provisionsBeforeAlditolAcid.Disjoint
      GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision priorMember completionMember
  rw [GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedMember :
      IUPACNormativeProvision.carbohydrate1996AlditolsAcids row ∈
        GlobalNonDescriptorIndexedSourceMeaning.provisions := by
    simpa [provisionsBeforeAlditolAcid, provisionsBeforeUnsaturated,
      provisionsBeforeDerivative, provisionsBeforeNamedParent,
      GlobalNonDescriptorRetinoidSourceMeaning.provisions,
      GlobalNonDescriptorCarotenoidSourceMeaning.provisions,
      GlobalNonDescriptorSteroidSourceMeaning.provisions,
      GlobalNonDescriptorCyclitolSourceMeaning.provisions,
      GlobalNonDescriptorNucleicAcidSourceMeaning.provisions,
      GlobalNonDescriptorLipidSourceMeaning.provisions,
      GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions,
      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions,
      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions] using priorMember
  exact (List.disjoint_left.mp indexed_disjoint_carbohydrate_alditol_acid_completion)
    indexedMember (List.mem_map.mpr ⟨row, rowMember, rfl⟩)

private theorem indexed_disjoint_carbohydrate_hetero_completion :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision indexedMember completionMember
  rw [GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedHeteroMember :
      IUPACNormativeProvision.carbohydrate1996HeteroSubstitutionAnhydride row ∈
        GlobalNonDescriptorIndexedSourceData.carbohydrateHeteroProvisions := by
    simpa [GlobalNonDescriptorIndexedSourceMeaning.provisions,
      GlobalNonDescriptorIndexedSourceData.provisions,
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
      GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
      GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] using indexedMember
  have completionMapped :
      IUPACNormativeProvision.carbohydrate1996HeteroSubstitutionAnhydride row ∈
        GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionProvisions :=
    List.mem_map.mpr ⟨row, rowMember, rfl⟩
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completion_disjoint_indexed)
      completionMapped indexedHeteroMember

private theorem prior_disjoint_carbohydrate_hetero_completion :
    provisionsBeforeHetero.Disjoint
      GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision priorMember completionMember
  rw [GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedMember :
      IUPACNormativeProvision.carbohydrate1996HeteroSubstitutionAnhydride row ∈
        GlobalNonDescriptorIndexedSourceMeaning.provisions := by
    simpa [provisionsBeforeHetero, provisionsBeforeAlditolAcid,
      provisionsBeforeUnsaturated, provisionsBeforeDerivative, provisionsBeforeNamedParent,
      GlobalNonDescriptorRetinoidSourceMeaning.provisions,
      GlobalNonDescriptorCarotenoidSourceMeaning.provisions,
      GlobalNonDescriptorSteroidSourceMeaning.provisions,
      GlobalNonDescriptorCyclitolSourceMeaning.provisions,
      GlobalNonDescriptorNucleicAcidSourceMeaning.provisions,
      GlobalNonDescriptorLipidSourceMeaning.provisions,
      GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions,
      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions,
      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions] using priorMember
  exact (List.disjoint_left.mp indexed_disjoint_carbohydrate_hetero_completion)
    indexedMember (List.mem_map.mpr ⟨row, rowMember, rfl⟩)

private theorem indexed_disjoint_carbohydrate_acetal_completion :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision indexedMember completionMember
  rw [GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedAcetalMember :
      IUPACNormativeProvision.carbohydrate1996Acetals row ∈
        GlobalNonDescriptorIndexedSourceData.carbohydrateAcetalProvisions := by
    simpa [GlobalNonDescriptorIndexedSourceMeaning.provisions,
      GlobalNonDescriptorIndexedSourceData.provisions,
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
      GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
      GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] using indexedMember
  have completionMapped :
      IUPACNormativeProvision.carbohydrate1996Acetals row ∈
        GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionProvisions :=
    List.mem_map.mpr ⟨row, rowMember, rfl⟩
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completion_disjoint_indexed)
      completionMapped indexedAcetalMember

private theorem prior_disjoint_carbohydrate_acetal_completion :
    provisionsBeforeAcetal.Disjoint
      GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision priorMember completionMember
  rw [GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedMember :
      IUPACNormativeProvision.carbohydrate1996Acetals row ∈
        GlobalNonDescriptorIndexedSourceMeaning.provisions := by
    simpa [provisionsBeforeAcetal, provisionsBeforeHetero, provisionsBeforeAlditolAcid,
      provisionsBeforeUnsaturated, provisionsBeforeDerivative, provisionsBeforeNamedParent,
      GlobalNonDescriptorRetinoidSourceMeaning.provisions,
      GlobalNonDescriptorCarotenoidSourceMeaning.provisions,
      GlobalNonDescriptorSteroidSourceMeaning.provisions,
      GlobalNonDescriptorCyclitolSourceMeaning.provisions,
      GlobalNonDescriptorNucleicAcidSourceMeaning.provisions,
      GlobalNonDescriptorLipidSourceMeaning.provisions,
      GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions,
      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions,
      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionProvisions] using priorMember
  exact (List.disjoint_left.mp indexed_disjoint_carbohydrate_acetal_completion)
    indexedMember (List.mem_map.mpr ⟨row, rowMember, rfl⟩)

private theorem indexed_disjoint_carbohydrate_residue_ion_completion :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision indexedMember completionMember
  rw [GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedResidueIonMember :
      IUPACNormativeProvision.carbohydrate1996ResiduesIons row ∈
        GlobalNonDescriptorIndexedSourceData.carbohydrateResidueIonProvisions := by
    simpa [GlobalNonDescriptorIndexedSourceMeaning.provisions,
      GlobalNonDescriptorIndexedSourceData.provisions,
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
      GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
      GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] using indexedMember
  have completionMapped :
      IUPACNormativeProvision.carbohydrate1996ResiduesIons row ∈
        GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionProvisions :=
    List.mem_map.mpr ⟨row, rowMember, rfl⟩
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completion_disjoint_indexed)
      completionMapped indexedResidueIonMember

private theorem prior_disjoint_carbohydrate_residue_ion_completion :
    provisionsBeforeResidueIon.Disjoint
      GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision priorMember completionMember
  rw [GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedMember :
      IUPACNormativeProvision.carbohydrate1996ResiduesIons row ∈
        GlobalNonDescriptorIndexedSourceMeaning.provisions := by
    simpa [provisionsBeforeResidueIon, provisionsBeforeAcetal, provisionsBeforeHetero,
      provisionsBeforeAlditolAcid, provisionsBeforeUnsaturated, provisionsBeforeDerivative,
      provisionsBeforeNamedParent, GlobalNonDescriptorRetinoidSourceMeaning.provisions,
      GlobalNonDescriptorCarotenoidSourceMeaning.provisions,
      GlobalNonDescriptorSteroidSourceMeaning.provisions,
      GlobalNonDescriptorCyclitolSourceMeaning.provisions,
      GlobalNonDescriptorNucleicAcidSourceMeaning.provisions,
      GlobalNonDescriptorLipidSourceMeaning.provisions,
      GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions,
      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions,
      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionProvisions] using priorMember
  exact (List.disjoint_left.mp indexed_disjoint_carbohydrate_residue_ion_completion)
    indexedMember (List.mem_map.mpr ⟨row, rowMember, rfl⟩)

private theorem prior_disjoint_carbohydrate_glycoside_ring_completion :
    provisionsBeforeGlycosideRing.Disjoint
      GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision priorMember completionMember
  rw [GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionRows]
      at completionMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp completionMember
  simp [provisionsBeforeGlycosideRing, provisionsBeforeResidueIon, provisionsBeforeAcetal,
    provisionsBeforeHetero, provisionsBeforeAlditolAcid, provisionsBeforeUnsaturated,
    provisionsBeforeDerivative, provisionsBeforeNamedParent,
    GlobalNonDescriptorIndexedSourceMeaning.provisions,
    GlobalNonDescriptorIndexedSourceData.provisions,
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
    GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
    GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions,
    GlobalNonDescriptorRetinoidSourceMeaning.provisions,
    GlobalNonDescriptorCarotenoidSourceMeaning.provisions,
    GlobalNonDescriptorSteroidSourceMeaning.provisions,
    GlobalNonDescriptorCyclitolSourceMeaning.provisions,
    GlobalNonDescriptorNucleicAcidSourceMeaning.provisions,
    GlobalNonDescriptorLipidSourceMeaning.provisions,
    GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions,
    GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions,
    GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionProvisions] at priorMember

private theorem indexed_disjoint_carbohydrate_oligosaccharide_completion :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision indexedMember completionMember
  rw [GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionRows]
      at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedOligosaccharideMember :
      IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides row ∈
        GlobalNonDescriptorIndexedSourceData.carbohydrateOligosaccharideProvisions := by
    simpa [GlobalNonDescriptorIndexedSourceMeaning.provisions,
      GlobalNonDescriptorIndexedSourceData.provisions,
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
      GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
      GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] using indexedMember
  have completionMapped :
      IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides row ∈
        GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionProvisions :=
    List.mem_map.mpr ⟨row, rowMember, rfl⟩
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completion_disjoint_indexed)
      completionMapped indexedOligosaccharideMember

private theorem prior_disjoint_carbohydrate_oligosaccharide_completion :
    provisionsBeforeOligosaccharide.Disjoint
      GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision priorMember completionMember
  rw [GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionRows]
      at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedMember :
      IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides row ∈
        GlobalNonDescriptorIndexedSourceMeaning.provisions := by
    simpa [provisionsBeforeOligosaccharide, provisionsBeforeGlycosideRing,
      provisionsBeforeResidueIon, provisionsBeforeAcetal, provisionsBeforeHetero,
      provisionsBeforeAlditolAcid, provisionsBeforeUnsaturated, provisionsBeforeDerivative,
      provisionsBeforeNamedParent, GlobalNonDescriptorRetinoidSourceMeaning.provisions,
      GlobalNonDescriptorCarotenoidSourceMeaning.provisions,
      GlobalNonDescriptorSteroidSourceMeaning.provisions,
      GlobalNonDescriptorCyclitolSourceMeaning.provisions,
      GlobalNonDescriptorNucleicAcidSourceMeaning.provisions,
      GlobalNonDescriptorLipidSourceMeaning.provisions,
      GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions,
      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions,
      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionProvisions] using priorMember
  exact (List.disjoint_left.mp indexed_disjoint_carbohydrate_oligosaccharide_completion)
    indexedMember (List.mem_map.mpr ⟨row, rowMember, rfl⟩)

private theorem indexed_disjoint_carbohydrate_appendix_completion :
    GlobalNonDescriptorIndexedSourceMeaning.provisions.Disjoint
      GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision indexedMember completionMember
  rw [GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedAppendixMember :
      IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary row ∈
        GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions := by
    simpa [GlobalNonDescriptorIndexedSourceMeaning.provisions,
      GlobalNonDescriptorIndexedSourceData.provisions,
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
      GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
      GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions] using indexedMember
  have completionMapped :
      IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary row ∈
        GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionProvisions :=
    List.mem_map.mpr ⟨row, rowMember, rfl⟩
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completion_disjoint_indexed)
      completionMapped indexedAppendixMember

private theorem prior_disjoint_carbohydrate_appendix_completion :
    provisionsBeforeAppendix.Disjoint
      GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionProvisions := by
  rw [List.disjoint_left]
  intro provision priorMember completionMember
  rw [GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionRows] at completionMember
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp completionMember
  have indexedMember :
      IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary row ∈
        GlobalNonDescriptorIndexedSourceMeaning.provisions := by
    simpa [provisionsBeforeAppendix, provisionsBeforeOligosaccharide,
      provisionsBeforeGlycosideRing, provisionsBeforeResidueIon, provisionsBeforeAcetal,
      provisionsBeforeHetero, provisionsBeforeAlditolAcid, provisionsBeforeUnsaturated,
      provisionsBeforeDerivative, provisionsBeforeNamedParent,
      GlobalNonDescriptorRetinoidSourceMeaning.provisions,
      GlobalNonDescriptorCarotenoidSourceMeaning.provisions,
      GlobalNonDescriptorSteroidSourceMeaning.provisions,
      GlobalNonDescriptorCyclitolSourceMeaning.provisions,
      GlobalNonDescriptorNucleicAcidSourceMeaning.provisions,
      GlobalNonDescriptorLipidSourceMeaning.provisions,
      GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions,
      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions,
      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionProvisions,
      GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionProvisions]
      using priorMember
  exact (List.disjoint_left.mp indexed_disjoint_carbohydrate_appendix_completion)
    indexedMember (List.mem_map.mpr ⟨row, rowMember, rfl⟩)

private theorem provisions_before_named_parent_nodup : provisionsBeforeNamedParent.Nodup := by
  rw [provisionsBeforeNamedParent]
  exact (((((((((GlobalNonDescriptorIndexedSourceMeaning.provisions_nodup.append
            GlobalNonDescriptorRetinoidSourceMeaning.provisions_nodup
              indexed_disjoint_retinoid).append
              GlobalNonDescriptorCarotenoidSourceMeaning.provisions_nodup
                indexed_retinoid_disjoint_carotenoid).append
                  GlobalNonDescriptorSteroidSourceMeaning.provisions_nodup
                    prior_disjoint_steroid).append
                      GlobalNonDescriptorCyclitolSourceMeaning.provisions_nodup
                        prior_disjoint_cyclitol).append
                          GlobalNonDescriptorNucleicAcidSourceMeaning.provisions_nodup
                            prior_disjoint_nucleic_acid).append
                              GlobalNonDescriptorLipidSourceMeaning.provisions_nodup
                                prior_disjoint_lipid).append
                                  GlobalNonDescriptorGlycolipidSourceMeaning.completion_provisions_nodup
                                    prior_disjoint_glycolipid_completion).append
                                      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions_nodup
                                        prior_disjoint_amino_acid_peptide).append
                                          GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completion_provisions_nodup
                                            prior_disjoint_carbohydrate_scope_parent_completion).append
                                              GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completion_provisions_nodup
                                                prior_disjoint_carbohydrate_foundation_completion

private theorem provisions_before_derivative_nodup : provisionsBeforeDerivative.Nodup := by
  rw [provisionsBeforeDerivative]
  exact provisions_before_named_parent_nodup.append
    GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completion_provisions_nodup
      prior_disjoint_carbohydrate_named_parent_completion

private theorem provisions_before_unsaturated_nodup : provisionsBeforeUnsaturated.Nodup := by
  rw [provisionsBeforeUnsaturated]
  exact provisions_before_derivative_nodup.append
    GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completion_provisions_nodup
      prior_disjoint_carbohydrate_derivative_completion

private theorem provisions_before_alditol_acid_nodup : provisionsBeforeAlditolAcid.Nodup := by
  rw [provisionsBeforeAlditolAcid]
  exact provisions_before_unsaturated_nodup.append
    GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completion_provisions_nodup
      prior_disjoint_carbohydrate_unsaturated_completion

private theorem provisions_before_hetero_nodup : provisionsBeforeHetero.Nodup := by
  rw [provisionsBeforeHetero]
  exact provisions_before_alditol_acid_nodup.append
    GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completion_provisions_nodup
      prior_disjoint_carbohydrate_alditol_acid_completion

private theorem provisions_before_acetal_nodup : provisionsBeforeAcetal.Nodup := by
  rw [provisionsBeforeAcetal]
  exact provisions_before_hetero_nodup.append
    GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completion_provisions_nodup
      prior_disjoint_carbohydrate_hetero_completion

private theorem provisions_before_residue_ion_nodup : provisionsBeforeResidueIon.Nodup := by
  rw [provisionsBeforeResidueIon]
  exact provisions_before_acetal_nodup.append
    GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completion_provisions_nodup
      prior_disjoint_carbohydrate_acetal_completion

private theorem provisions_before_glycoside_ring_nodup : provisionsBeforeGlycosideRing.Nodup := by
  rw [provisionsBeforeGlycosideRing]
  exact provisions_before_residue_ion_nodup.append
    GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completion_provisions_nodup
      prior_disjoint_carbohydrate_residue_ion_completion

private theorem provisions_before_oligosaccharide_nodup :
    provisionsBeforeOligosaccharide.Nodup := by
  rw [provisionsBeforeOligosaccharide]
  exact provisions_before_glycoside_ring_nodup.append
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completion_provisions_nodup
      prior_disjoint_carbohydrate_glycoside_ring_completion

private theorem provisions_before_appendix_nodup : provisionsBeforeAppendix.Nodup := by
  rw [provisionsBeforeAppendix]
  exact provisions_before_oligosaccharide_nodup.append
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completion_provisions_nodup
      prior_disjoint_carbohydrate_oligosaccharide_completion

private theorem provisions_before_p10_nodup : provisionsBeforeP10.Nodup := by
  rw [provisionsBeforeP10]
  exact provisions_before_appendix_nodup.append
    GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completion_provisions_nodup
      prior_disjoint_carbohydrate_appendix_completion

private theorem prior_disjoint_p10 :
    provisionsBeforeP10.Disjoint GlobalNonDescriptorP10SourceMeaning.provisions := by
  rw [List.disjoint_left]
  intro provision priorMember p10Member
  rw [GlobalNonDescriptorP10SourceMeaning.provisions,
    GlobalNonDescriptorP10SourceMeaning.rows] at p10Member
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp p10Member
  simp [provisionsBeforeP10, provisionsBeforeAppendix, provisionsBeforeOligosaccharide,
    provisionsBeforeGlycosideRing, provisionsBeforeResidueIon, provisionsBeforeAcetal,
    provisionsBeforeHetero, provisionsBeforeAlditolAcid, provisionsBeforeUnsaturated,
    provisionsBeforeDerivative, provisionsBeforeNamedParent,
    GlobalNonDescriptorIndexedSourceMeaning.provisions,
    GlobalNonDescriptorIndexedSourceData.provisions,
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
    GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
    GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions,
    GlobalNonDescriptorRetinoidSourceMeaning.provisions,
    GlobalNonDescriptorCarotenoidSourceMeaning.provisions,
    GlobalNonDescriptorSteroidSourceMeaning.provisions,
    GlobalNonDescriptorCyclitolSourceMeaning.provisions,
    GlobalNonDescriptorNucleicAcidSourceMeaning.provisions,
    GlobalNonDescriptorLipidSourceMeaning.provisions,
    GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions,
    GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions,
    GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionProvisions] at priorMember

private theorem provisions_before_glycoside_printed_nodup :
    provisionsBeforeGlycosidePrinted.Nodup := by
  rw [provisionsBeforeGlycosidePrinted]
  exact provisions_before_p10_nodup.append
    GlobalNonDescriptorP10SourceMeaning.provisions_nodup prior_disjoint_p10

private theorem prior_disjoint_glycoside_printed :
    provisionsBeforeGlycosidePrinted.Disjoint
      GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedProvisions := by
  rw [List.disjoint_left]
  intro provision priorMember printedMember
  rw [GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedProvisions,
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedRows] at printedMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp printedMember
  simp [provisionsBeforeGlycosidePrinted, provisionsBeforeP10, provisionsBeforeAppendix,
    provisionsBeforeOligosaccharide, provisionsBeforeGlycosideRing, provisionsBeforeResidueIon,
    provisionsBeforeAcetal, provisionsBeforeHetero, provisionsBeforeAlditolAcid,
    provisionsBeforeUnsaturated, provisionsBeforeDerivative, provisionsBeforeNamedParent,
    GlobalNonDescriptorIndexedSourceMeaning.provisions,
    GlobalNonDescriptorIndexedSourceData.provisions,
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
    GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
    GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions,
    GlobalNonDescriptorRetinoidSourceMeaning.provisions,
    GlobalNonDescriptorCarotenoidSourceMeaning.provisions,
    GlobalNonDescriptorSteroidSourceMeaning.provisions,
    GlobalNonDescriptorCyclitolSourceMeaning.provisions,
    GlobalNonDescriptorNucleicAcidSourceMeaning.provisions,
    GlobalNonDescriptorLipidSourceMeaning.provisions,
    GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions,
    GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions,
    GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionRows,
    Carbohydrate1996GlycosidesRings.Provision.base,
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionProvisions,
    GlobalNonDescriptorP10SourceMeaning.provisions,
    GlobalNonDescriptorP10SourceMeaning.rows] at priorMember

private theorem provisions_before_oligosaccharide_printed_nodup :
    provisionsBeforeOligosaccharidePrinted.Nodup := by
  rw [provisionsBeforeOligosaccharidePrinted]
  exact provisions_before_glycoside_printed_nodup.append
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printed_provisions_nodup
      prior_disjoint_glycoside_printed

private theorem prior_disjoint_oligosaccharide_printed :
    provisionsBeforeOligosaccharidePrinted.Disjoint
      GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedProvisions := by
  rw [List.disjoint_left]
  intro provision priorMember printedMember
  rw [GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedProvisions,
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedRows] at printedMember
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp printedMember
  simp [provisionsBeforeOligosaccharidePrinted, provisionsBeforeGlycosidePrinted,
    provisionsBeforeP10, provisionsBeforeAppendix, provisionsBeforeOligosaccharide,
    provisionsBeforeGlycosideRing, provisionsBeforeResidueIon, provisionsBeforeAcetal,
    provisionsBeforeHetero, provisionsBeforeAlditolAcid, provisionsBeforeUnsaturated,
    provisionsBeforeDerivative, provisionsBeforeNamedParent,
    GlobalNonDescriptorIndexedSourceMeaning.provisions,
    GlobalNonDescriptorIndexedSourceData.provisions,
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
    GlobalNonDescriptorIndexedSourceData.carbohydrateOligosaccharideRows,
    GlobalNonDescriptorIndexedSourceData.carbohydrateAppendixProvisions,
    GlobalNonDescriptorSixReviewedImageSourceMeanings.provisions,
    GlobalNonDescriptorRetinoidSourceMeaning.provisions,
    GlobalNonDescriptorCarotenoidSourceMeaning.provisions,
    GlobalNonDescriptorSteroidSourceMeaning.provisions,
    GlobalNonDescriptorCyclitolSourceMeaning.provisions,
    GlobalNonDescriptorNucleicAcidSourceMeaning.provisions,
    GlobalNonDescriptorLipidSourceMeaning.provisions,
    GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions,
    GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions,
    GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionProvisions,
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionRows,
    Carbohydrate1996OligosaccharidesPolysaccharides.Provision.base,
    GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionProvisions,
    GlobalNonDescriptorP10SourceMeaning.provisions,
    GlobalNonDescriptorP10SourceMeaning.rows,
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedProvisions,
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedRows] at priorMember

theorem provisions_nodup : provisions.Nodup := by
  rw [provisions]
  exact provisions_before_oligosaccharide_printed_nodup.append
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printed_provisions_nodup
      prior_disjoint_oligosaccharide_printed

theorem entry_provisions_nodup :
    (entries.map GlobalNonDescriptorSourceMeaningEntry.provision).Nodup := by
  rw [entry_provisions_exact]
  exact provisions_nodup

theorem first_595_entries_exact :
    entries.take 595 = GlobalNonDescriptorIndexedSourceMeaning.entries := by
  simp [entries, batch, batchBeforeOligosaccharidePrinted, batchBeforeGlycosidePrinted,
    batchBeforeP10, batchBeforeAppendix,
    batchBeforeOligosaccharide,
    GlobalNonDescriptorIndexedSourceMeaning.entries]

private def entriesAfterOligosaccharide : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionBatch.entries ++
    (GlobalNonDescriptorP10SourceMeaning.batch.entries ++
      (GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedBatch.entries ++
        GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedBatch.entries))

private def entriesAfterGlycosideRing : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionBatch.entries ++
    entriesAfterOligosaccharide

private def entriesAfterResidueIon : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionBatch.entries ++
    entriesAfterGlycosideRing

private def entriesAfterAcetal : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionBatch.entries ++
    entriesAfterResidueIon

private def entriesAfterHetero : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionBatch.entries ++ entriesAfterAcetal

private def entriesAfterAlditolAcid : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionBatch.entries ++ entriesAfterHetero

private def entriesAfterUnsaturated : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionBatch.entries ++
    entriesAfterAlditolAcid

private def entriesAfterDerivative : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionBatch.entries ++
    entriesAfterUnsaturated

private def entriesAfterNamedParent : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionBatch.entries ++
    entriesAfterDerivative

private def entriesAfterFoundation : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionBatch.entries ++
    entriesAfterNamedParent

private def entriesAfterScopeParent : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionBatch.entries ++
    entriesAfterFoundation

private def entriesAfterAminoAcidPeptide : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionBatch.entries ++
    entriesAfterScopeParent

private def entriesAfterGlycolipid : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorAminoAcidPeptideSourceMeaning.batch.entries ++
    entriesAfterAminoAcidPeptide

private def entriesAfterLipid : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorGlycolipidSourceMeaning.completionBatch.entries ++ entriesAfterGlycolipid

private def entriesAfterNucleicAcid : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorLipidSourceMeaning.batch.entries ++ entriesAfterLipid

private def entriesAfterCyclitol : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorNucleicAcidSourceMeaning.batch.entries ++ entriesAfterNucleicAcid

private def entriesAfterSteroid : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorCyclitolSourceMeaning.batch.entries ++ entriesAfterCyclitol

private def entriesAfterCarotenoid : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorSteroidSourceMeaning.batch.entries ++ entriesAfterSteroid

private def entriesAfterRetinoid : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorCarotenoidSourceMeaning.batch.entries ++ entriesAfterCarotenoid

private def entriesAfterIndexed : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorRetinoidSourceMeaning.batch.entries ++ entriesAfterRetinoid

private theorem entries_drop_595_exact : entries.drop 595 = entriesAfterIndexed := by
  simp only [entries, batch, batchBeforeOligosaccharidePrinted, batchBeforeGlycosidePrinted,
    batchBeforeP10, batchBeforeAppendix,
    batchBeforeOligosaccharide,
    GlobalNonDescriptorSourceMeaningBatch.append_entries]
  simp only [List.append_assoc]
  have indexedCount : GlobalNonDescriptorIndexedSourceMeaning.batch.entries.length = 595 := by
    rw [GlobalNonDescriptorIndexedSourceMeaning.batch.entries_length,
      GlobalNonDescriptorIndexedSourceMeaning.provision_count]
  rw [← indexedCount]
  rw [List.drop_left]
  rfl

private theorem drop_after_family {offset count : Nat}
    (family suffix : List GlobalNonDescriptorSourceMeaningEntry)
    (tailExact : entries.drop offset = family ++ suffix)
    (familyCount : family.length = count) :
    entries.drop (offset + count) = suffix := by
  rw [← List.drop_drop, tailExact, ← familyCount]
  exact List.drop_left

private theorem entries_drop_608_exact : entries.drop 608 = entriesAfterRetinoid := by
  simpa [entriesAfterIndexed] using drop_after_family
    GlobalNonDescriptorRetinoidSourceMeaning.batch.entries entriesAfterRetinoid
      entries_drop_595_exact GlobalNonDescriptorRetinoidSourceMeaning.entry_count

private theorem entries_drop_618_exact : entries.drop 618 = entriesAfterCarotenoid := by
  simpa [entriesAfterRetinoid] using drop_after_family
    GlobalNonDescriptorCarotenoidSourceMeaning.batch.entries entriesAfterCarotenoid
      entries_drop_608_exact GlobalNonDescriptorCarotenoidSourceMeaning.entry_count

private theorem entries_drop_680_exact : entries.drop 680 = entriesAfterSteroid := by
  simpa [entriesAfterCarotenoid] using drop_after_family
    GlobalNonDescriptorSteroidSourceMeaning.batch.entries entriesAfterSteroid
      entries_drop_618_exact GlobalNonDescriptorSteroidSourceMeaning.entry_count

private theorem entries_drop_717_exact : entries.drop 717 = entriesAfterCyclitol := by
  simpa [entriesAfterSteroid] using drop_after_family
    GlobalNonDescriptorCyclitolSourceMeaning.batch.entries entriesAfterCyclitol
      entries_drop_680_exact GlobalNonDescriptorCyclitolSourceMeaning.entry_count

private theorem entries_drop_738_exact : entries.drop 738 = entriesAfterNucleicAcid := by
  simpa [entriesAfterCyclitol] using drop_after_family
    GlobalNonDescriptorNucleicAcidSourceMeaning.batch.entries entriesAfterNucleicAcid
      entries_drop_717_exact GlobalNonDescriptorNucleicAcidSourceMeaning.entry_count

private theorem entries_drop_769_exact : entries.drop 769 = entriesAfterLipid := by
  simpa [entriesAfterNucleicAcid] using drop_after_family
    GlobalNonDescriptorLipidSourceMeaning.batch.entries entriesAfterLipid
      entries_drop_738_exact GlobalNonDescriptorLipidSourceMeaning.entry_count

private theorem entries_drop_793_exact : entries.drop 793 = entriesAfterGlycolipid := by
  simpa [entriesAfterLipid] using drop_after_family
    GlobalNonDescriptorGlycolipidSourceMeaning.completionBatch.entries entriesAfterGlycolipid
      entries_drop_769_exact GlobalNonDescriptorGlycolipidSourceMeaning.completion_entry_count

private theorem entries_drop_838_exact : entries.drop 838 = entriesAfterAminoAcidPeptide := by
  simpa [entriesAfterGlycolipid] using drop_after_family
    GlobalNonDescriptorAminoAcidPeptideSourceMeaning.batch.entries entriesAfterAminoAcidPeptide
      entries_drop_793_exact GlobalNonDescriptorAminoAcidPeptideSourceMeaning.entry_count

private theorem entries_drop_917_exact : entries.drop 917 = entriesAfterScopeParent := by
  simpa [entriesAfterAminoAcidPeptide] using drop_after_family
    GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionBatch.entries
      entriesAfterScopeParent entries_drop_838_exact
        GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completion_entry_count

private theorem entries_drop_976_exact : entries.drop 976 = entriesAfterFoundation := by
  simpa [entriesAfterScopeParent] using drop_after_family
    GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionBatch.entries
      entriesAfterFoundation entries_drop_917_exact
        GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completion_entry_count

private theorem entries_drop_1038_exact : entries.drop 1038 = entriesAfterNamedParent := by
  simpa [entriesAfterFoundation] using drop_after_family
    GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionBatch.entries
      entriesAfterNamedParent entries_drop_976_exact
        GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completion_entry_count

private theorem entries_drop_1094_exact : entries.drop 1094 = entriesAfterDerivative := by
  simpa [entriesAfterNamedParent] using drop_after_family
    GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionBatch.entries
      entriesAfterDerivative entries_drop_1038_exact
        GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completion_entry_count

private theorem entries_drop_1136_exact : entries.drop 1136 = entriesAfterUnsaturated := by
  simpa [entriesAfterDerivative] using drop_after_family
    GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionBatch.entries
      entriesAfterUnsaturated entries_drop_1094_exact
        GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completion_entry_count

private theorem entries_drop_1182_exact : entries.drop 1182 = entriesAfterAlditolAcid := by
  simpa [entriesAfterUnsaturated] using drop_after_family
    GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionBatch.entries
      entriesAfterAlditolAcid entries_drop_1136_exact
        GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completion_entry_count

private theorem entries_drop_1216_exact : entries.drop 1216 = entriesAfterHetero := by
  simpa [entriesAfterAlditolAcid] using drop_after_family
    GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionBatch.entries
      entriesAfterHetero entries_drop_1182_exact
        GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completion_entry_count

private theorem entries_drop_1233_exact : entries.drop 1233 = entriesAfterAcetal := by
  simpa [entriesAfterHetero] using drop_after_family
    GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionBatch.entries
      entriesAfterAcetal entries_drop_1216_exact
        GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completion_entry_count

private theorem entries_drop_1257_exact : entries.drop 1257 = entriesAfterResidueIon := by
  simpa [entriesAfterAcetal] using drop_after_family
    GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionBatch.entries
      entriesAfterResidueIon entries_drop_1233_exact
        GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completion_entry_count

private theorem entries_drop_1312_exact : entries.drop 1312 = entriesAfterGlycosideRing := by
  simpa [entriesAfterResidueIon] using drop_after_family
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionBatch.entries
      entriesAfterGlycosideRing entries_drop_1257_exact
        GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completion_entry_count

private theorem entries_drop_1440_exact : entries.drop 1440 = entriesAfterOligosaccharide := by
  simpa [entriesAfterGlycosideRing] using drop_after_family
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionBatch.entries
      entriesAfterOligosaccharide entries_drop_1312_exact
        GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completion_entry_count

private theorem entries_drop_1443_exact :
    entries.drop 1443 = GlobalNonDescriptorP10SourceMeaning.batch.entries ++
      (GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedBatch.entries ++
        GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedBatch.entries) := by
  simpa [entriesAfterOligosaccharide] using drop_after_family
    GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionBatch.entries
      (GlobalNonDescriptorP10SourceMeaning.batch.entries ++
        (GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedBatch.entries ++
          GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedBatch.entries))
      entries_drop_1440_exact
        GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completion_entry_count

private theorem entries_drop_1514_exact : entries.drop 1514 =
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedBatch.entries ++
      GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedBatch.entries := by
  simpa using drop_after_family GlobalNonDescriptorP10SourceMeaning.batch.entries
    (GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedBatch.entries ++
      GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedBatch.entries)
      entries_drop_1443_exact GlobalNonDescriptorP10SourceMeaning.entry_count

private theorem entries_drop_1572_exact : entries.drop 1572 =
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedBatch.entries := by
  simpa using drop_after_family
    GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedBatch.entries
    GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedBatch.entries
      entries_drop_1514_exact
        GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printed_entry_count

theorem retinoid_13_entries_exact :
    (entries.drop 595).take 13 = GlobalNonDescriptorRetinoidSourceMeaning.batch.entries := by
  rw [entries_drop_595_exact, entriesAfterIndexed,
    ← GlobalNonDescriptorRetinoidSourceMeaning.entry_count]
  exact List.take_left

theorem carotenoid_10_entries_exact :
    (entries.drop 608).take 10 = GlobalNonDescriptorCarotenoidSourceMeaning.batch.entries := by
  rw [entries_drop_608_exact, entriesAfterRetinoid,
    ← GlobalNonDescriptorCarotenoidSourceMeaning.entry_count]
  exact List.take_left

theorem steroid_62_entries_exact :
    (entries.drop 618).take 62 = GlobalNonDescriptorSteroidSourceMeaning.batch.entries := by
  rw [entries_drop_618_exact, entriesAfterCarotenoid,
    ← GlobalNonDescriptorSteroidSourceMeaning.entry_count]
  exact List.take_left

theorem cyclitol_37_entries_exact :
    (entries.drop 680).take 37 = GlobalNonDescriptorCyclitolSourceMeaning.batch.entries := by
  rw [entries_drop_680_exact, entriesAfterSteroid,
    ← GlobalNonDescriptorCyclitolSourceMeaning.entry_count]
  exact List.take_left

theorem nucleic_acid_21_entries_exact :
    (entries.drop 717).take 21 = GlobalNonDescriptorNucleicAcidSourceMeaning.batch.entries := by
  rw [entries_drop_717_exact, entriesAfterCyclitol,
    ← GlobalNonDescriptorNucleicAcidSourceMeaning.entry_count]
  exact List.take_left

theorem lipid_31_entries_exact :
    (entries.drop 738).take 31 = GlobalNonDescriptorLipidSourceMeaning.batch.entries := by
  rw [entries_drop_738_exact, entriesAfterNucleicAcid,
    ← GlobalNonDescriptorLipidSourceMeaning.entry_count]
  exact List.take_left

theorem glycolipid_completion_24_entries_exact :
    (entries.drop 769).take 24 =
      GlobalNonDescriptorGlycolipidSourceMeaning.completionBatch.entries := by
  rw [entries_drop_769_exact, entriesAfterLipid,
    ← GlobalNonDescriptorGlycolipidSourceMeaning.completion_entry_count]
  exact List.take_left

theorem amino_acid_peptide_45_entries_exact :
    (entries.drop 793).take 45 =
      GlobalNonDescriptorAminoAcidPeptideSourceMeaning.batch.entries := by
  rw [entries_drop_793_exact, entriesAfterGlycolipid,
    ← GlobalNonDescriptorAminoAcidPeptideSourceMeaning.entry_count]
  exact List.take_left

theorem carbohydrate_scope_parent_79_entries_exact :
    (entries.drop 838).take 79 =
      GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionBatch.entries := by
  rw [entries_drop_838_exact, entriesAfterAminoAcidPeptide,
    ← GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completion_entry_count]
  exact List.take_left

theorem carbohydrate_foundation_59_entries_exact :
    (entries.drop 917).take 59 =
      GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionBatch.entries := by
  rw [entries_drop_917_exact, entriesAfterScopeParent,
    ← GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completion_entry_count]
  exact List.take_left

theorem carbohydrate_named_parent_62_entries_exact :
    (entries.drop 976).take 62 =
      GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionBatch.entries := by
  rw [entries_drop_976_exact, entriesAfterFoundation,
    ← GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completion_entry_count]
  exact List.take_left

theorem carbohydrate_derivative_56_entries_exact :
    (entries.drop 1038).take 56 =
      GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionBatch.entries := by
  rw [entries_drop_1038_exact, entriesAfterNamedParent,
    ← GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completion_entry_count]
  exact List.take_left

theorem carbohydrate_unsaturated_42_entries_exact :
    (entries.drop 1094).take 42 =
      GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionBatch.entries := by
  rw [entries_drop_1094_exact, entriesAfterDerivative,
    ← GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completion_entry_count]
  exact List.take_left

theorem carbohydrate_alditol_acid_46_entries_exact :
    (entries.drop 1136).take 46 =
      GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionBatch.entries := by
  rw [entries_drop_1136_exact, entriesAfterUnsaturated,
    ← GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completion_entry_count]
  exact List.take_left

theorem carbohydrate_hetero_34_entries_exact :
    (entries.drop 1182).take 34 =
      GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionBatch.entries := by
  rw [entries_drop_1182_exact, entriesAfterAlditolAcid,
    ← GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completion_entry_count]
  exact List.take_left

theorem carbohydrate_acetal_17_entries_exact :
    (entries.drop 1216).take 17 =
      GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionBatch.entries := by
  rw [entries_drop_1216_exact, entriesAfterHetero,
    ← GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completion_entry_count]
  exact List.take_left

theorem carbohydrate_residue_ion_24_entries_exact :
    (entries.drop 1233).take 24 =
      GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionBatch.entries := by
  rw [entries_drop_1233_exact, entriesAfterAcetal,
    ← GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completion_entry_count]
  exact List.take_left

theorem carbohydrate_glycoside_ring_through_printed_entries_exact :
    entries.drop 1257 =
      GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionBatch.entries ++
        (GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionBatch.entries ++
          (GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionBatch.entries ++
            (GlobalNonDescriptorP10SourceMeaning.batch.entries ++
              (GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedBatch.entries ++
                GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedBatch.entries)))) := by
  simpa [entriesAfterResidueIon, entriesAfterGlycosideRing, entriesAfterOligosaccharide]
    using entries_drop_1257_exact

theorem carbohydrate_glycoside_ring_55_entries_exact :
    (entries.drop 1257).take 55 =
      GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionBatch.entries := by
  rw [carbohydrate_glycoside_ring_through_printed_entries_exact,
    ← GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completion_entry_count]
  exact List.take_left

theorem carbohydrate_oligosaccharide_128_entries_exact :
    (entries.drop 1312).take 128 =
      GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionBatch.entries := by
  rw [entries_drop_1312_exact, entriesAfterGlycosideRing,
    ← GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completion_entry_count]
  exact List.take_left

theorem final_3_entries_exact :
    (entries.drop 1440).take 3 =
      GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionBatch.entries := by
  rw [entries_drop_1440_exact, entriesAfterOligosaccharide,
    ← GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completion_entry_count]
  exact List.take_left

theorem p10_71_entries_exact :
    (entries.drop 1443).take 71 = GlobalNonDescriptorP10SourceMeaning.batch.entries := by
  rw [entries_drop_1443_exact, ← GlobalNonDescriptorP10SourceMeaning.entry_count]
  exact List.take_left

theorem glycoside_ring_printed_58_entries_exact :
    (entries.drop 1514).take 58 =
      GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedBatch.entries := by
  rw [entries_drop_1514_exact,
    ← GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printed_entry_count]
  exact List.take_left

theorem oligosaccharide_printed_41_entries_exact :
    entries.drop 1572 =
      GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedBatch.entries :=
  entries_drop_1572_exact

theorem every_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (_member : entry ∈ entries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment

private def provisionsBeforeFoundation : List IUPACNormativeProvision :=
  ((((((((GlobalNonDescriptorIndexedSourceMeaning.provisions ++
    GlobalNonDescriptorRetinoidSourceMeaning.provisions) ++
      GlobalNonDescriptorCarotenoidSourceMeaning.provisions) ++
        GlobalNonDescriptorSteroidSourceMeaning.provisions) ++
          GlobalNonDescriptorCyclitolSourceMeaning.provisions) ++
            GlobalNonDescriptorNucleicAcidSourceMeaning.provisions) ++
              GlobalNonDescriptorLipidSourceMeaning.provisions) ++
                GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions) ++
                  GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions) ++
                    GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions

private theorem source_audit_complete_before_foundation
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996)
    (glycolipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .glycolipidRecommendations1997)
    (retinoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .retinoidRecommendations1981)
    (carotenoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carotenoidRules1974)
    (steroidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .steroidRecommendations1989)
    (cyclitolAudited : IUPACNormativeSource.ProvisionAuditComplete
      .cyclitolRecommendations1973)
    (nucleicAcidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .nucleicAcidRecommendations1970)
    (lipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .lipidRecommendations1976)
    (aminoAcidPeptideAudited : IUPACNormativeSource.ProvisionAuditComplete
      .aminoAcidPeptideRecommendations1983)
    (provision : IUPACNormativeProvision) (member : provision ∈ provisionsBeforeFoundation) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  rw [provisionsBeforeFoundation, List.mem_append] at member
  rcases member with throughAminoAcidPeptideMember | scopeParentCompletionMember
  · rw [List.mem_append] at throughAminoAcidPeptideMember
    rcases throughAminoAcidPeptideMember with throughGlycolipidMember | aminoAcidPeptideMember
    · rw [List.mem_append] at throughGlycolipidMember
      rcases throughGlycolipidMember with priorMember | glycolipidCompletionMember
      · rw [List.mem_append] at priorMember
        rcases priorMember with earlierMember | lipidMember
        · rw [List.mem_append] at earlierMember
          rcases earlierMember with stillEarlierMember | nucleicAcidMember
          · rw [List.mem_append] at stillEarlierMember
            rcases stillEarlierMember with priorSpecialists | cyclitolMember
            · rw [List.mem_append] at priorSpecialists
              rcases priorSpecialists with middleMember | steroidMember
              · rw [List.mem_append] at middleMember
                rcases middleMember with firstMember | carotenoidMember
                · rw [List.mem_append] at firstMember
                  rcases firstMember with indexedMember | retinoidMember
                  · exact GlobalNonDescriptorIndexedSourceMeaning.source_audit_complete_of_carbohydrate_and_glycolipid
                      carbohydrateAudited glycolipidAudited provision indexedMember
                  · rw [GlobalNonDescriptorRetinoidSourceMeaning.provisions_exact] at retinoidMember
                    have sourceExact : provision.source = .retinoidRecommendations1981 :=
                      (mem_sourceProvisions_iff provision .retinoidRecommendations1981).1
                        retinoidMember
                    rw [sourceExact]
                    exact retinoidAudited
                · rw [GlobalNonDescriptorCarotenoidSourceMeaning.provisions_exact] at carotenoidMember
                  have sourceExact : provision.source = .carotenoidRules1974 :=
                    (mem_sourceProvisions_iff provision .carotenoidRules1974).1 carotenoidMember
                  rw [sourceExact]
                  exact carotenoidAudited
              · rw [GlobalNonDescriptorSteroidSourceMeaning.provisions_exact] at steroidMember
                have sourceExact : provision.source = .steroidRecommendations1989 :=
                  (mem_sourceProvisions_iff provision .steroidRecommendations1989).1 steroidMember
                rw [sourceExact]
                exact steroidAudited
            · rw [GlobalNonDescriptorCyclitolSourceMeaning.provisions_exact] at cyclitolMember
              have sourceExact : provision.source = .cyclitolRecommendations1973 :=
                (mem_sourceProvisions_iff provision .cyclitolRecommendations1973).1 cyclitolMember
              rw [sourceExact]
              exact cyclitolAudited
          · rw [GlobalNonDescriptorNucleicAcidSourceMeaning.provisions_exact] at nucleicAcidMember
            have sourceExact : provision.source = .nucleicAcidRecommendations1970 :=
              (mem_sourceProvisions_iff provision .nucleicAcidRecommendations1970).1
                nucleicAcidMember
            rw [sourceExact]
            exact nucleicAcidAudited
        · rw [GlobalNonDescriptorLipidSourceMeaning.provisions_exact] at lipidMember
          have sourceExact : provision.source = .lipidRecommendations1976 :=
            (mem_sourceProvisions_iff provision .lipidRecommendations1976).1 lipidMember
          rw [sourceExact]
          exact lipidAudited
      · rw [GlobalNonDescriptorGlycolipidSourceMeaning.completionProvisions] at glycolipidCompletionMember
        obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp glycolipidCompletionMember
        exact glycolipidAudited
    · rw [GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions_exact] at aminoAcidPeptideMember
      have sourceExact : provision.source = .aminoAcidPeptideRecommendations1983 :=
        (mem_sourceProvisions_iff provision .aminoAcidPeptideRecommendations1983).1
          aminoAcidPeptideMember
      rw [sourceExact]
      exact aminoAcidPeptideAudited
  · rw [GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completionProvisions]
      at scopeParentCompletionMember
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp scopeParentCompletionMember
    exact carbohydrateAudited

private theorem source_audit_complete_before_named_parent
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996)
    (glycolipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .glycolipidRecommendations1997)
    (retinoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .retinoidRecommendations1981)
    (carotenoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carotenoidRules1974)
    (steroidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .steroidRecommendations1989)
    (cyclitolAudited : IUPACNormativeSource.ProvisionAuditComplete
      .cyclitolRecommendations1973)
    (nucleicAcidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .nucleicAcidRecommendations1970)
    (lipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .lipidRecommendations1976)
    (aminoAcidPeptideAudited : IUPACNormativeSource.ProvisionAuditComplete
      .aminoAcidPeptideRecommendations1983)
    (provision : IUPACNormativeProvision) (member : provision ∈ provisionsBeforeNamedParent) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  rw [provisionsBeforeNamedParent, ← provisionsBeforeFoundation, List.mem_append] at member
  rcases member with priorMember | foundationCompletionMember
  · exact source_audit_complete_before_foundation carbohydrateAudited glycolipidAudited
      retinoidAudited carotenoidAudited steroidAudited cyclitolAudited nucleicAcidAudited
      lipidAudited aminoAcidPeptideAudited provision priorMember
  · rw [GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completionProvisions]
      at foundationCompletionMember
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp foundationCompletionMember
    exact carbohydrateAudited

private theorem source_audit_complete_before_derivative
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996)
    (glycolipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .glycolipidRecommendations1997)
    (retinoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .retinoidRecommendations1981)
    (carotenoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carotenoidRules1974)
    (steroidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .steroidRecommendations1989)
    (cyclitolAudited : IUPACNormativeSource.ProvisionAuditComplete
      .cyclitolRecommendations1973)
    (nucleicAcidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .nucleicAcidRecommendations1970)
    (lipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .lipidRecommendations1976)
    (aminoAcidPeptideAudited : IUPACNormativeSource.ProvisionAuditComplete
      .aminoAcidPeptideRecommendations1983)
    (provision : IUPACNormativeProvision) (member : provision ∈ provisionsBeforeDerivative) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  rw [provisionsBeforeDerivative, List.mem_append] at member
  rcases member with priorMember | namedParentCompletionMember
  · exact source_audit_complete_before_named_parent carbohydrateAudited glycolipidAudited
      retinoidAudited carotenoidAudited steroidAudited cyclitolAudited nucleicAcidAudited
      lipidAudited aminoAcidPeptideAudited provision priorMember
  · rw [GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completionProvisions]
      at namedParentCompletionMember
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp namedParentCompletionMember
    exact carbohydrateAudited

private theorem source_audit_complete_before_unsaturated
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996)
    (glycolipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .glycolipidRecommendations1997)
    (retinoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .retinoidRecommendations1981)
    (carotenoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carotenoidRules1974)
    (steroidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .steroidRecommendations1989)
    (cyclitolAudited : IUPACNormativeSource.ProvisionAuditComplete
      .cyclitolRecommendations1973)
    (nucleicAcidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .nucleicAcidRecommendations1970)
    (lipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .lipidRecommendations1976)
    (aminoAcidPeptideAudited : IUPACNormativeSource.ProvisionAuditComplete
      .aminoAcidPeptideRecommendations1983)
    (provision : IUPACNormativeProvision) (member : provision ∈ provisionsBeforeUnsaturated) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  rw [provisionsBeforeUnsaturated, List.mem_append] at member
  rcases member with priorMember | derivativeCompletionMember
  · exact source_audit_complete_before_derivative carbohydrateAudited glycolipidAudited
      retinoidAudited carotenoidAudited steroidAudited cyclitolAudited nucleicAcidAudited
      lipidAudited aminoAcidPeptideAudited provision priorMember
  · rw [GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completionProvisions]
      at derivativeCompletionMember
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp derivativeCompletionMember
    exact carbohydrateAudited

private theorem source_audit_complete_before_alditol_acid
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996)
    (glycolipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .glycolipidRecommendations1997)
    (retinoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .retinoidRecommendations1981)
    (carotenoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carotenoidRules1974)
    (steroidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .steroidRecommendations1989)
    (cyclitolAudited : IUPACNormativeSource.ProvisionAuditComplete
      .cyclitolRecommendations1973)
    (nucleicAcidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .nucleicAcidRecommendations1970)
    (lipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .lipidRecommendations1976)
    (aminoAcidPeptideAudited : IUPACNormativeSource.ProvisionAuditComplete
      .aminoAcidPeptideRecommendations1983)
    (provision : IUPACNormativeProvision) (member : provision ∈ provisionsBeforeAlditolAcid) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  rw [provisionsBeforeAlditolAcid, List.mem_append] at member
  rcases member with priorMember | unsaturatedCompletionMember
  · exact source_audit_complete_before_unsaturated carbohydrateAudited glycolipidAudited
      retinoidAudited carotenoidAudited steroidAudited cyclitolAudited nucleicAcidAudited
      lipidAudited aminoAcidPeptideAudited provision priorMember
  · rw [GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completionProvisions]
      at unsaturatedCompletionMember
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp unsaturatedCompletionMember
    exact carbohydrateAudited

private theorem source_audit_complete_before_hetero
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996)
    (glycolipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .glycolipidRecommendations1997)
    (retinoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .retinoidRecommendations1981)
    (carotenoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carotenoidRules1974)
    (steroidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .steroidRecommendations1989)
    (cyclitolAudited : IUPACNormativeSource.ProvisionAuditComplete
      .cyclitolRecommendations1973)
    (nucleicAcidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .nucleicAcidRecommendations1970)
    (lipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .lipidRecommendations1976)
    (aminoAcidPeptideAudited : IUPACNormativeSource.ProvisionAuditComplete
      .aminoAcidPeptideRecommendations1983)
    (provision : IUPACNormativeProvision) (member : provision ∈ provisionsBeforeHetero) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  rw [provisionsBeforeHetero, List.mem_append] at member
  rcases member with priorMember | alditolAcidCompletionMember
  · exact source_audit_complete_before_alditol_acid carbohydrateAudited glycolipidAudited
      retinoidAudited carotenoidAudited steroidAudited cyclitolAudited nucleicAcidAudited
      lipidAudited aminoAcidPeptideAudited provision priorMember
  · rw [GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completionProvisions]
      at alditolAcidCompletionMember
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp alditolAcidCompletionMember
    exact carbohydrateAudited

private theorem source_audit_complete_before_acetal
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996)
    (glycolipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .glycolipidRecommendations1997)
    (retinoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .retinoidRecommendations1981)
    (carotenoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carotenoidRules1974)
    (steroidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .steroidRecommendations1989)
    (cyclitolAudited : IUPACNormativeSource.ProvisionAuditComplete
      .cyclitolRecommendations1973)
    (nucleicAcidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .nucleicAcidRecommendations1970)
    (lipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .lipidRecommendations1976)
    (aminoAcidPeptideAudited : IUPACNormativeSource.ProvisionAuditComplete
      .aminoAcidPeptideRecommendations1983)
    (provision : IUPACNormativeProvision) (member : provision ∈ provisionsBeforeAcetal) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  rw [provisionsBeforeAcetal, List.mem_append] at member
  rcases member with priorMember | heteroCompletionMember
  · exact source_audit_complete_before_hetero carbohydrateAudited glycolipidAudited
      retinoidAudited carotenoidAudited steroidAudited cyclitolAudited nucleicAcidAudited
      lipidAudited aminoAcidPeptideAudited provision priorMember
  · rw [GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completionProvisions]
      at heteroCompletionMember
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp heteroCompletionMember
    exact carbohydrateAudited

private theorem source_audit_complete_before_residue_ion
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996)
    (glycolipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .glycolipidRecommendations1997)
    (retinoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .retinoidRecommendations1981)
    (carotenoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carotenoidRules1974)
    (steroidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .steroidRecommendations1989)
    (cyclitolAudited : IUPACNormativeSource.ProvisionAuditComplete
      .cyclitolRecommendations1973)
    (nucleicAcidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .nucleicAcidRecommendations1970)
    (lipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .lipidRecommendations1976)
    (aminoAcidPeptideAudited : IUPACNormativeSource.ProvisionAuditComplete
      .aminoAcidPeptideRecommendations1983)
    (provision : IUPACNormativeProvision) (member : provision ∈ provisionsBeforeResidueIon) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  rw [provisionsBeforeResidueIon, List.mem_append] at member
  rcases member with priorMember | acetalCompletionMember
  · exact source_audit_complete_before_acetal carbohydrateAudited glycolipidAudited
      retinoidAudited carotenoidAudited steroidAudited cyclitolAudited nucleicAcidAudited
      lipidAudited aminoAcidPeptideAudited provision priorMember
  · rw [GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completionProvisions]
      at acetalCompletionMember
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp acetalCompletionMember
    exact carbohydrateAudited

private theorem source_audit_complete_before_glycoside_ring
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996)
    (glycolipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .glycolipidRecommendations1997)
    (retinoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .retinoidRecommendations1981)
    (carotenoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carotenoidRules1974)
    (steroidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .steroidRecommendations1989)
    (cyclitolAudited : IUPACNormativeSource.ProvisionAuditComplete
      .cyclitolRecommendations1973)
    (nucleicAcidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .nucleicAcidRecommendations1970)
    (lipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .lipidRecommendations1976)
    (aminoAcidPeptideAudited : IUPACNormativeSource.ProvisionAuditComplete
      .aminoAcidPeptideRecommendations1983)
    (provision : IUPACNormativeProvision) (member : provision ∈ provisionsBeforeGlycosideRing) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  rw [provisionsBeforeGlycosideRing, List.mem_append] at member
  rcases member with priorMember | residueIonCompletionMember
  · exact source_audit_complete_before_residue_ion carbohydrateAudited glycolipidAudited
      retinoidAudited carotenoidAudited steroidAudited cyclitolAudited nucleicAcidAudited
      lipidAudited aminoAcidPeptideAudited provision priorMember
  · rw [GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completionProvisions]
      at residueIonCompletionMember
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp residueIonCompletionMember
    exact carbohydrateAudited

private theorem source_audit_complete_before_oligosaccharide
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996)
    (glycolipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .glycolipidRecommendations1997)
    (retinoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .retinoidRecommendations1981)
    (carotenoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carotenoidRules1974)
    (steroidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .steroidRecommendations1989)
    (cyclitolAudited : IUPACNormativeSource.ProvisionAuditComplete
      .cyclitolRecommendations1973)
    (nucleicAcidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .nucleicAcidRecommendations1970)
    (lipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .lipidRecommendations1976)
    (aminoAcidPeptideAudited : IUPACNormativeSource.ProvisionAuditComplete
      .aminoAcidPeptideRecommendations1983)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ provisionsBeforeOligosaccharide) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  rw [provisionsBeforeOligosaccharide, List.mem_append] at member
  rcases member with priorMember | glycosideRingCompletionMember
  · exact source_audit_complete_before_glycoside_ring carbohydrateAudited glycolipidAudited
      retinoidAudited carotenoidAudited steroidAudited cyclitolAudited nucleicAcidAudited
      lipidAudited aminoAcidPeptideAudited provision priorMember
  · rw [GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completionProvisions]
      at glycosideRingCompletionMember
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp glycosideRingCompletionMember
    exact carbohydrateAudited

private theorem source_audit_complete_before_appendix
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996)
    (glycolipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .glycolipidRecommendations1997)
    (retinoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .retinoidRecommendations1981)
    (carotenoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carotenoidRules1974)
    (steroidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .steroidRecommendations1989)
    (cyclitolAudited : IUPACNormativeSource.ProvisionAuditComplete
      .cyclitolRecommendations1973)
    (nucleicAcidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .nucleicAcidRecommendations1970)
    (lipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .lipidRecommendations1976)
    (aminoAcidPeptideAudited : IUPACNormativeSource.ProvisionAuditComplete
      .aminoAcidPeptideRecommendations1983)
    (provision : IUPACNormativeProvision) (member : provision ∈ provisionsBeforeAppendix) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  rw [provisionsBeforeAppendix, List.mem_append] at member
  rcases member with priorMember | oligosaccharideCompletionMember
  · exact source_audit_complete_before_oligosaccharide carbohydrateAudited glycolipidAudited
      retinoidAudited carotenoidAudited steroidAudited cyclitolAudited nucleicAcidAudited
      lipidAudited aminoAcidPeptideAudited provision priorMember
  · rw [GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completionProvisions]
      at oligosaccharideCompletionMember
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp oligosaccharideCompletionMember
    exact carbohydrateAudited


private theorem source_audit_complete_before_p10
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996)
    (glycolipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .glycolipidRecommendations1997)
    (retinoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .retinoidRecommendations1981)
    (carotenoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carotenoidRules1974)
    (steroidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .steroidRecommendations1989)
    (cyclitolAudited : IUPACNormativeSource.ProvisionAuditComplete
      .cyclitolRecommendations1973)
    (nucleicAcidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .nucleicAcidRecommendations1970)
    (lipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .lipidRecommendations1976)
    (aminoAcidPeptideAudited : IUPACNormativeSource.ProvisionAuditComplete
      .aminoAcidPeptideRecommendations1983)
    (provision : IUPACNormativeProvision) (member : provision ∈ provisionsBeforeP10) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  rw [provisionsBeforeP10, List.mem_append] at member
  rcases member with priorMember | appendixCompletionMember
  · exact source_audit_complete_before_appendix carbohydrateAudited glycolipidAudited
      retinoidAudited carotenoidAudited steroidAudited cyclitolAudited nucleicAcidAudited
      lipidAudited aminoAcidPeptideAudited provision priorMember
  · rw [GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completionProvisions]
      at appendixCompletionMember
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp appendixCompletionMember
    exact carbohydrateAudited

private theorem source_audit_complete_before_glycoside_printed
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996)
    (glycolipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .glycolipidRecommendations1997)
    (retinoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .retinoidRecommendations1981)
    (carotenoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carotenoidRules1974)
    (steroidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .steroidRecommendations1989)
    (cyclitolAudited : IUPACNormativeSource.ProvisionAuditComplete
      .cyclitolRecommendations1973)
    (nucleicAcidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .nucleicAcidRecommendations1970)
    (lipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .lipidRecommendations1976)
    (aminoAcidPeptideAudited : IUPACNormativeSource.ProvisionAuditComplete
      .aminoAcidPeptideRecommendations1983)
    (p10Audited : IUPACNormativeSource.ProvisionAuditComplete .blueBook2013P10)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ provisionsBeforeGlycosidePrinted) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  rw [provisionsBeforeGlycosidePrinted, List.mem_append] at member
  rcases member with priorMember | p10Member
  · exact source_audit_complete_before_p10 carbohydrateAudited glycolipidAudited
      retinoidAudited carotenoidAudited steroidAudited cyclitolAudited nucleicAcidAudited
      lipidAudited aminoAcidPeptideAudited provision priorMember
  · rw [GlobalNonDescriptorP10SourceMeaning.provisions,
      GlobalNonDescriptorP10SourceMeaning.rows] at p10Member
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp p10Member
    exact p10Audited

private theorem source_audit_complete_before_oligosaccharide_printed
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996)
    (glycolipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .glycolipidRecommendations1997)
    (retinoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .retinoidRecommendations1981)
    (carotenoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carotenoidRules1974)
    (steroidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .steroidRecommendations1989)
    (cyclitolAudited : IUPACNormativeSource.ProvisionAuditComplete
      .cyclitolRecommendations1973)
    (nucleicAcidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .nucleicAcidRecommendations1970)
    (lipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .lipidRecommendations1976)
    (aminoAcidPeptideAudited : IUPACNormativeSource.ProvisionAuditComplete
      .aminoAcidPeptideRecommendations1983)
    (p10Audited : IUPACNormativeSource.ProvisionAuditComplete .blueBook2013P10)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ provisionsBeforeOligosaccharidePrinted) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  rw [provisionsBeforeOligosaccharidePrinted, List.mem_append] at member
  rcases member with priorMember | printedMember
  · exact source_audit_complete_before_glycoside_printed carbohydrateAudited glycolipidAudited
      retinoidAudited carotenoidAudited steroidAudited cyclitolAudited nucleicAcidAudited
      lipidAudited aminoAcidPeptideAudited p10Audited provision priorMember
  · rw [GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedProvisions,
      GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printedRows] at printedMember
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp printedMember
    exact carbohydrateAudited


theorem source_audit_complete_of_ten_families
    (carbohydrateAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996)
    (glycolipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .glycolipidRecommendations1997)
    (retinoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .retinoidRecommendations1981)
    (carotenoidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .carotenoidRules1974)
    (steroidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .steroidRecommendations1989)
    (cyclitolAudited : IUPACNormativeSource.ProvisionAuditComplete
      .cyclitolRecommendations1973)
    (nucleicAcidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .nucleicAcidRecommendations1970)
    (lipidAudited : IUPACNormativeSource.ProvisionAuditComplete
      .lipidRecommendations1976)
    (aminoAcidPeptideAudited : IUPACNormativeSource.ProvisionAuditComplete
      .aminoAcidPeptideRecommendations1983)
    (p10Audited : IUPACNormativeSource.ProvisionAuditComplete .blueBook2013P10)
    (provision : IUPACNormativeProvision) (member : provision ∈ provisions) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  rw [provisions, List.mem_append] at member
  rcases member with priorMember | printedMember
  · exact source_audit_complete_before_oligosaccharide_printed carbohydrateAudited
      glycolipidAudited
      retinoidAudited carotenoidAudited steroidAudited cyclitolAudited nucleicAcidAudited
      lipidAudited aminoAcidPeptideAudited p10Audited provision priorMember
  · rw [GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedProvisions,
      GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.printedRows] at printedMember
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp printedMember
    exact carbohydrateAudited

end GlobalNonDescriptorMaterializedSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.mem_provisions_iff_components
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.provisions_nodup
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.first_595_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.retinoid_13_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.carotenoid_10_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.steroid_62_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.cyclitol_37_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.nucleic_acid_21_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.lipid_31_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.glycolipid_completion_24_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.amino_acid_peptide_45_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.carbohydrate_scope_parent_79_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.carbohydrate_foundation_59_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.carbohydrate_named_parent_62_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.carbohydrate_derivative_56_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.carbohydrate_unsaturated_42_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.carbohydrate_alditol_acid_46_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.carbohydrate_hetero_34_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.carbohydrate_acetal_17_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.carbohydrate_residue_ion_24_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.carbohydrate_glycoside_ring_through_printed_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.carbohydrate_glycoside_ring_55_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.carbohydrate_oligosaccharide_128_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.final_3_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.p10_71_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.glycoside_ring_printed_58_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.oligosaccharide_printed_41_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.every_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaning.source_audit_complete_of_ten_families
