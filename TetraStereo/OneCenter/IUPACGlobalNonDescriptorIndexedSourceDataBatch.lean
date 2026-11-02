import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateSourceDataA
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateSourceDataB
import TetraStereo.KernelOnly

set_option autoImplicit false










namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorIndexedSourceData

def carbohydrateTextualProvisions : List IUPACNormativeProvision :=
  carbohydrateSourceDataAProvisions ++ carbohydrateSourceDataBTextualProvisions

def carbohydrateTextualBatch :
    GlobalNonDescriptorSourceMeaningBatch carbohydrateTextualProvisions := by
  simpa [carbohydrateTextualProvisions] using
    carbohydrateSourceDataABatch.append carbohydrateSourceDataBTextualBatch

@[simp] theorem carbohydrateTextualProvisionCount :
    carbohydrateTextualProvisions.length = 570 := by
  simp [carbohydrateTextualProvisions]

private def sourceDataAHalf? : IUPACNormativeProvision → Bool
  | .carbohydrate1996ScopeParent _
  | .carbohydrate1996Foundation _
  | .carbohydrate1996NamedParents _
  | .carbohydrate1996Derivatives _
  | .carbohydrate1996UnsaturatedBranched _
  | .carbohydrate1996AlditolsAcids _ => true
  | _ => false

private theorem mappedFamily_forall {Row : Type}
    (rows : List Row)
    (wrap : Row → IUPACNormativeProvision)
    (expected : Bool)
    (classified : ∀ row, sourceDataAHalf? (wrap row) = expected) :
    (rows.map wrap).Forall (fun provision => sourceDataAHalf? provision = expected) := by
  rw [List.forall_iff_forall_mem]
  intro provision member
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp member
  exact classified row

private theorem sourceDataAHalf_forall_A :
    carbohydrateSourceDataAProvisions.Forall
      (fun provision => sourceDataAHalf? provision = true) := by
  simp only [carbohydrateSourceDataAProvisions, List.forall_append]
  exact ⟨⟨⟨⟨⟨
    mappedFamily_forall carbohydrateScopeParentRows
      IUPACNormativeProvision.carbohydrate1996ScopeParent true (by intro _row; rfl),
    mappedFamily_forall carbohydrateFoundationRows
      IUPACNormativeProvision.carbohydrate1996Foundation true (by intro _row; rfl)⟩,
    mappedFamily_forall carbohydrateNamedParentRows
      IUPACNormativeProvision.carbohydrate1996NamedParents true (by intro _row; rfl)⟩,
    mappedFamily_forall carbohydrateDerivativeRows
      IUPACNormativeProvision.carbohydrate1996Derivatives true (by intro _row; rfl)⟩,
    mappedFamily_forall carbohydrateUnsaturatedRows
      IUPACNormativeProvision.carbohydrate1996UnsaturatedBranched true
        (by intro _row; rfl)⟩,
    mappedFamily_forall carbohydrateAlditolAcidRows
      IUPACNormativeProvision.carbohydrate1996AlditolsAcids true (by intro _row; rfl)⟩

set_option maxRecDepth 8192 in
private theorem sourceDataAHalf_forall_BTextual :
    carbohydrateSourceDataBTextualProvisions.Forall
      (fun provision => sourceDataAHalf? provision = false) := by
  simp only [carbohydrateSourceDataBTextualProvisions, List.forall_append]
  exact ⟨⟨⟨⟨
    mappedFamily_forall carbohydrateHeteroRows
      IUPACNormativeProvision.carbohydrate1996HeteroSubstitutionAnhydride false
        (by intro _row; rfl),
    mappedFamily_forall carbohydrateAcetalRows
      IUPACNormativeProvision.carbohydrate1996Acetals false (by intro _row; rfl)⟩,
    mappedFamily_forall carbohydrateResidueIonRows
      IUPACNormativeProvision.carbohydrate1996ResiduesIons false (by intro _row; rfl)⟩,
    mappedFamily_forall carbohydrateOligosaccharideRows
      IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides false
        (by intro _row; rfl)⟩,
    mappedFamily_forall carbohydrateAppendixRows
      IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary false
        (by intro _row; rfl)⟩

theorem carbohydrateTextualProvisions_nodup : carbohydrateTextualProvisions.Nodup := by
  exact carbohydrateSourceDataAProvisions_nodup.append
    carbohydrateSourceDataBTextualProvisions_nodup
    (by
      rw [List.disjoint_left]
      intro provision left right
      have leftClass :=
        (List.forall_iff_forall_mem.mp sourceDataAHalf_forall_A) provision left
      have rightClass :=
        (List.forall_iff_forall_mem.mp sourceDataAHalf_forall_BTextual) provision right
      simp [leftClass] at rightClass)

def provisions : List IUPACNormativeProvision :=
  glycolipidProvisions ++ carbohydrateTextualProvisions

def batch : GlobalNonDescriptorSourceMeaningBatch provisions :=
  glycolipidBatch.append carbohydrateTextualBatch

def entries : List GlobalNonDescriptorSourceMeaningEntry := batch.entries

@[simp] theorem provision_count : provisions.length = 589 := by
  simp [provisions]

@[simp] theorem entry_count : entries.length = 589 := by
  rw [entries, batch.entries_length, provision_count]

@[simp] theorem entry_provisions_exact :
    entries.map GlobalNonDescriptorSourceMeaningEntry.provision = provisions := by
  exact batch.provisions_exact

theorem provisions_nodup : provisions.Nodup := by
  exact glycolipidProvisions_nodup.append carbohydrateTextualProvisions_nodup
      (by
        simp [List.disjoint_left, glycolipidProvisions, carbohydrateTextualProvisions,
          carbohydrateSourceDataAProvisions, carbohydrateSourceDataBTextualProvisions,
          carbohydrateScopeParentProvisions, carbohydrateFoundationProvisions,
          carbohydrateNamedParentProvisions, carbohydrateDerivativeProvisions,
          carbohydrateUnsaturatedProvisions, carbohydrateAlditolAcidProvisions,
          carbohydrateHeteroProvisions, carbohydrateAcetalProvisions,
          carbohydrateResidueIonProvisions, carbohydrateOligosaccharideProvisions,
          carbohydrateAppendixProvisions])

theorem entry_provisions_nodup :
    (entries.map GlobalNonDescriptorSourceMeaningEntry.provision).Nodup := by
  rw [entry_provisions_exact]
  exact provisions_nodup

theorem entry_reference_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (_member : entry ∈ entries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment

end GlobalNonDescriptorIndexedSourceData
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorIndexedSourceData.entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorIndexedSourceData.entry_reference_nonvacuous
