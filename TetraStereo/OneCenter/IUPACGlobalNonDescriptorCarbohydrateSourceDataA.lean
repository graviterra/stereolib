import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataCore

set_option autoImplicit false

/-!
# Indexed carbohydrate source data, part A

This module packages the first 255 one-to-one carbohydrate source-data rows: scope/parent choice,
foundation, named parents, derivatives, unsaturated/branched rules, and alditols/acids.  It
contains no source-key-only or tag-only rows.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorIndexedSourceData

/-! ## Carbohydrate scope and parent choice: 16 -/

def carbohydrateScopeParentRows : List Carbohydrate1996ScopeParent.Provision :=
  Carbohydrate1996ScopeParent.AbbreviationGroup.all.map
      Carbohydrate1996ScopeParent.Provision.abbreviation ++
    Carbohydrate1996ScopeParent.ParentChoiceExample.all.map
      Carbohydrate1996ScopeParent.Provision.parentChoiceExample

def carbohydrateScopeParentProvisions : List IUPACNormativeProvision :=
  carbohydrateScopeParentRows.map IUPACNormativeProvision.carbohydrate1996ScopeParent

private def carbohydrateAbbreviationBatch :=
  totalMeaningBatch Carbohydrate1996ScopeParent.AbbreviationGroup.all
    (fun row => IUPACNormativeProvision.carbohydrate1996ScopeParent (.abbreviation row))
    Carbohydrate1996ScopeParent.AbbreviationGroup.data (by intro _row; rfl)

private def carbohydrateParentChoiceBatch :=
  totalMeaningBatch Carbohydrate1996ScopeParent.ParentChoiceExample.all
    (fun row => IUPACNormativeProvision.carbohydrate1996ScopeParent (.parentChoiceExample row))
    Carbohydrate1996ScopeParent.ParentChoiceExample.data (by intro _row; rfl)

def carbohydrateScopeParentBatch :
    GlobalNonDescriptorSourceMeaningBatch carbohydrateScopeParentProvisions := by
  simpa [carbohydrateScopeParentProvisions, carbohydrateScopeParentRows,
    List.map_append, List.map_map] using
      carbohydrateAbbreviationBatch.append carbohydrateParentChoiceBatch

@[simp] theorem carbohydrateScopeParentProvisionCount :
    carbohydrateScopeParentProvisions.length = 16 := by
  simp [carbohydrateScopeParentProvisions, carbohydrateScopeParentRows]

private theorem carbohydrateScopeParentRows_nodup : carbohydrateScopeParentRows.Nodup := by
  have allNodup := Carbohydrate1996ScopeParent.Provision.all_nodup
  have baseAppend :
      (Carbohydrate1996ScopeParent.Provision.base ++ carbohydrateScopeParentRows).Nodup := by
    simpa [Carbohydrate1996ScopeParent.Provision.all, carbohydrateScopeParentRows,
      List.append_assoc] using allNodup
  exact baseAppend.of_append_right

theorem carbohydrateScopeParentProvisions_nodup :
    carbohydrateScopeParentProvisions.Nodup := by
  exact carbohydrateScopeParentRows_nodup.map
    (by intro left right equal; cases equal; rfl)

/-! ## Carbohydrate foundation conformation table: 12 -/

def carbohydrateFoundationRows : List Carbohydrate1996Foundation.Provision :=
  Carbohydrate1996Foundation.ConformationTableRow.all.map
    Carbohydrate1996Foundation.Provision.conformationTable

def carbohydrateFoundationProvisions : List IUPACNormativeProvision :=
  carbohydrateFoundationRows.map IUPACNormativeProvision.carbohydrate1996Foundation

def carbohydrateFoundationBatch :
    GlobalNonDescriptorSourceMeaningBatch carbohydrateFoundationProvisions := by
  simpa [carbohydrateFoundationProvisions, carbohydrateFoundationRows, List.map_map] using
    totalMeaningBatch Carbohydrate1996Foundation.ConformationTableRow.all
      (fun row => IUPACNormativeProvision.carbohydrate1996Foundation (.conformationTable row))
      Carbohydrate1996Foundation.ConformationTableRow.data (by intro _row; rfl)

@[simp] theorem carbohydrateFoundationProvisionCount :
    carbohydrateFoundationProvisions.length = 12 := by
  simp [carbohydrateFoundationProvisions, carbohydrateFoundationRows]

private theorem carbohydrateFoundationRows_nodup : carbohydrateFoundationRows.Nodup := by
  exact Carbohydrate1996Foundation.Provision.all_nodup.of_append_right

theorem carbohydrateFoundationProvisions_nodup : carbohydrateFoundationProvisions.Nodup := by
  exact carbohydrateFoundationRows_nodup.map
    (by intro left right equal; cases equal; rfl)

/-! ## Named-parent charts and worked examples: 50 -/

def carbohydrateNamedParentRows : List Carbohydrate1996NamedParents.Provision :=
  (Carbohydrate1996NamedParents.AldoseChartRow.all.map
      Carbohydrate1996NamedParents.Provision.aldoseChart ++
    Carbohydrate1996NamedParents.KetoseChartRow.all.map
      Carbohydrate1996NamedParents.Provision.ketoseChart) ++
    Carbohydrate1996NamedParents.WorkedExample.all.map
      Carbohydrate1996NamedParents.Provision.workedExample

def carbohydrateNamedParentProvisions : List IUPACNormativeProvision :=
  carbohydrateNamedParentRows.map IUPACNormativeProvision.carbohydrate1996NamedParents

private def carbohydrateAldoseChartBatch :=
  totalMeaningBatch Carbohydrate1996NamedParents.AldoseChartRow.all
    (fun row => IUPACNormativeProvision.carbohydrate1996NamedParents (.aldoseChart row))
    Carbohydrate1996NamedParents.AldoseChartRow.data (by intro _row; rfl)

private def carbohydrateKetoseChartBatch :=
  totalMeaningBatch Carbohydrate1996NamedParents.KetoseChartRow.all
    (fun row => IUPACNormativeProvision.carbohydrate1996NamedParents (.ketoseChart row))
    Carbohydrate1996NamedParents.KetoseChartRow.data (by intro _row; rfl)

private def carbohydrateNamedWorkedExampleBatch :=
  totalMeaningBatch Carbohydrate1996NamedParents.WorkedExample.all
    (fun row => IUPACNormativeProvision.carbohydrate1996NamedParents (.workedExample row))
    Carbohydrate1996NamedParents.WorkedExample.data (by intro _row; rfl)

def carbohydrateNamedParentBatch :
    GlobalNonDescriptorSourceMeaningBatch carbohydrateNamedParentProvisions := by
  simpa [carbohydrateNamedParentProvisions, carbohydrateNamedParentRows,
    List.map_append, List.map_map, List.append_assoc] using
      (carbohydrateAldoseChartBatch.append carbohydrateKetoseChartBatch).append
        carbohydrateNamedWorkedExampleBatch

@[simp] theorem carbohydrateNamedParentProvisionCount :
    carbohydrateNamedParentProvisions.length = 50 := by
  simp [carbohydrateNamedParentProvisions, carbohydrateNamedParentRows]

private theorem carbohydrateNamedParentRows_nodup : carbohydrateNamedParentRows.Nodup := by
  have allNodup := Carbohydrate1996NamedParents.Provision.all_nodup
  have baseAppend :
      (Carbohydrate1996NamedParents.Provision.base ++ carbohydrateNamedParentRows).Nodup := by
    simpa [Carbohydrate1996NamedParents.Provision.all, carbohydrateNamedParentRows,
      List.append_assoc] using allNodup
  exact baseAppend.of_append_right

theorem carbohydrateNamedParentProvisions_nodup :
    carbohydrateNamedParentProvisions.Nodup := by
  exact carbohydrateNamedParentRows_nodup.map
    (by intro left right equal; cases equal; rfl)

/-! ## Derivative retained-name and printed rows: 66 -/

def carbohydrateDerivativeRows : List Carbohydrate1996Derivatives.Provision :=
  (Carbohydrate1996Derivatives.DeoxyTrivialNameRow.all.map
      Carbohydrate1996Derivatives.Provision.deoxyTrivialName ++
    Carbohydrate1996Derivatives.AminoTrivialNameRow.all.map
      Carbohydrate1996Derivatives.Provision.aminoTrivialName) ++
    Carbohydrate1996Derivatives.PrintedExample.all.map
      Carbohydrate1996Derivatives.Provision.printedExample

def carbohydrateDerivativeProvisions : List IUPACNormativeProvision :=
  carbohydrateDerivativeRows.map IUPACNormativeProvision.carbohydrate1996Derivatives

private def carbohydrateDeoxyTrivialNameBatch :=
  totalMeaningBatch Carbohydrate1996Derivatives.DeoxyTrivialNameRow.all
    (fun row => IUPACNormativeProvision.carbohydrate1996Derivatives (.deoxyTrivialName row))
    Carbohydrate1996Derivatives.DeoxyTrivialNameRow.data (by intro _row; rfl)

private def carbohydrateAminoTrivialNameBatch :=
  totalMeaningBatch Carbohydrate1996Derivatives.AminoTrivialNameRow.all
    (fun row => IUPACNormativeProvision.carbohydrate1996Derivatives (.aminoTrivialName row))
    Carbohydrate1996Derivatives.AminoTrivialNameRow.data (by intro _row; rfl)

private def carbohydrateDerivativePrintedBatch :=
  totalMeaningBatch Carbohydrate1996Derivatives.PrintedExample.all
    (fun row => IUPACNormativeProvision.carbohydrate1996Derivatives (.printedExample row))
    Carbohydrate1996Derivatives.PrintedExample.data (by intro _row; rfl)

def carbohydrateDerivativeBatch :
    GlobalNonDescriptorSourceMeaningBatch carbohydrateDerivativeProvisions := by
  simpa [carbohydrateDerivativeProvisions, carbohydrateDerivativeRows,
    List.map_append, List.map_map, List.append_assoc] using
      (carbohydrateDeoxyTrivialNameBatch.append carbohydrateAminoTrivialNameBatch).append
        carbohydrateDerivativePrintedBatch

@[simp] theorem carbohydrateDerivativeProvisionCount :
    carbohydrateDerivativeProvisions.length = 66 := by
  simp [carbohydrateDerivativeProvisions, carbohydrateDerivativeRows]

private theorem carbohydrateDerivativeRows_nodup : carbohydrateDerivativeRows.Nodup := by
  have allNodup := Carbohydrate1996Derivatives.Provision.all_nodup
  have baseAppend :
      (Carbohydrate1996Derivatives.Provision.base ++ carbohydrateDerivativeRows).Nodup := by
    simpa [Carbohydrate1996Derivatives.Provision.all, carbohydrateDerivativeRows,
      List.append_assoc] using allNodup
  exact baseAppend.of_append_right

theorem carbohydrateDerivativeProvisions_nodup :
    carbohydrateDerivativeProvisions.Nodup := by
  exact carbohydrateDerivativeRows_nodup.map
    (by intro left right equal; cases equal; rfl)

/-! ## Unsaturated and branched rows: 43 -/

def carbohydrateUnsaturatedRows : List Carbohydrate1996UnsaturatedBranched.Provision :=
  Carbohydrate1996UnsaturatedBranched.ChartVRow.all.map
      Carbohydrate1996UnsaturatedBranched.Provision.chartV ++
    Carbohydrate1996UnsaturatedBranched.PrintedExample.all.map
      Carbohydrate1996UnsaturatedBranched.Provision.printedExample

def carbohydrateUnsaturatedProvisions : List IUPACNormativeProvision :=
  carbohydrateUnsaturatedRows.map
    IUPACNormativeProvision.carbohydrate1996UnsaturatedBranched

private def carbohydrateChartVBatch :=
  totalMeaningBatch Carbohydrate1996UnsaturatedBranched.ChartVRow.all
    (fun row =>
      IUPACNormativeProvision.carbohydrate1996UnsaturatedBranched (.chartV row))
    Carbohydrate1996UnsaturatedBranched.ChartVRow.data (by intro _row; rfl)

private def carbohydrateUnsaturatedPrintedBatch :=
  totalMeaningBatch Carbohydrate1996UnsaturatedBranched.PrintedExample.all
    (fun row =>
      IUPACNormativeProvision.carbohydrate1996UnsaturatedBranched (.printedExample row))
    Carbohydrate1996UnsaturatedBranched.PrintedExample.data (by intro _row; rfl)

def carbohydrateUnsaturatedBatch :
    GlobalNonDescriptorSourceMeaningBatch carbohydrateUnsaturatedProvisions := by
  simpa [carbohydrateUnsaturatedProvisions, carbohydrateUnsaturatedRows,
    List.map_append, List.map_map] using
      carbohydrateChartVBatch.append carbohydrateUnsaturatedPrintedBatch

@[simp] theorem carbohydrateUnsaturatedProvisionCount :
    carbohydrateUnsaturatedProvisions.length = 43 := by
  simp [carbohydrateUnsaturatedProvisions, carbohydrateUnsaturatedRows]

private theorem carbohydrateUnsaturatedRows_nodup : carbohydrateUnsaturatedRows.Nodup := by
  have allNodup := Carbohydrate1996UnsaturatedBranched.Provision.all_nodup
  have baseAppend :
      (Carbohydrate1996UnsaturatedBranched.Provision.base ++
        carbohydrateUnsaturatedRows).Nodup := by
    simpa [Carbohydrate1996UnsaturatedBranched.Provision.all, carbohydrateUnsaturatedRows,
      List.append_assoc] using allNodup
  exact baseAppend.of_append_right

theorem carbohydrateUnsaturatedProvisions_nodup :
    carbohydrateUnsaturatedProvisions.Nodup := by
  exact carbohydrateUnsaturatedRows_nodup.map
    (by intro left right equal; cases equal; rfl)

/-! ## Alditol and acid names/examples: 68 -/

def carbohydrateAlditolAcidRows : List Carbohydrate1996AlditolsAcids.Provision :=
  Carbohydrate1996AlditolsAcids.MesoAldaricName.all.map
      Carbohydrate1996AlditolsAcids.Provision.mesoAldaricName ++
    Carbohydrate1996AlditolsAcids.PrintedExample.all.map
      Carbohydrate1996AlditolsAcids.Provision.printedExample

def carbohydrateAlditolAcidProvisions : List IUPACNormativeProvision :=
  carbohydrateAlditolAcidRows.map IUPACNormativeProvision.carbohydrate1996AlditolsAcids

private def carbohydrateMesoAldaricNameBatch :=
  totalMeaningBatch Carbohydrate1996AlditolsAcids.MesoAldaricName.all
    (fun row => IUPACNormativeProvision.carbohydrate1996AlditolsAcids (.mesoAldaricName row))
    Carbohydrate1996AlditolsAcids.MesoAldaricName.text (by intro _row; rfl)

private def carbohydrateAlditolAcidPrintedBatch :=
  totalMeaningBatch Carbohydrate1996AlditolsAcids.PrintedExample.all
    (fun row => IUPACNormativeProvision.carbohydrate1996AlditolsAcids (.printedExample row))
    Carbohydrate1996AlditolsAcids.PrintedExample.data (by intro _row; rfl)

def carbohydrateAlditolAcidBatch :
    GlobalNonDescriptorSourceMeaningBatch carbohydrateAlditolAcidProvisions := by
  simpa [carbohydrateAlditolAcidProvisions, carbohydrateAlditolAcidRows,
    List.map_append, List.map_map] using
      carbohydrateMesoAldaricNameBatch.append carbohydrateAlditolAcidPrintedBatch

@[simp] theorem carbohydrateAlditolAcidProvisionCount :
    carbohydrateAlditolAcidProvisions.length = 68 := by
  simp [carbohydrateAlditolAcidProvisions, carbohydrateAlditolAcidRows]

private theorem carbohydrateAlditolAcidRows_nodup : carbohydrateAlditolAcidRows.Nodup := by
  have allNodup := Carbohydrate1996AlditolsAcids.Provision.all_nodup
  have baseAppend :
      (Carbohydrate1996AlditolsAcids.Provision.base ++ carbohydrateAlditolAcidRows).Nodup := by
    simpa [Carbohydrate1996AlditolsAcids.Provision.all, carbohydrateAlditolAcidRows,
      List.append_assoc] using allNodup
  exact baseAppend.of_append_right

theorem carbohydrateAlditolAcidProvisions_nodup :
    carbohydrateAlditolAcidProvisions.Nodup := by
  exact carbohydrateAlditolAcidRows_nodup.map
    (by intro left right equal; cases equal; rfl)

/-! ## Exact 255-row part-A projection -/

def carbohydrateSourceDataAProvisions : List IUPACNormativeProvision :=
  carbohydrateScopeParentProvisions ++
    carbohydrateFoundationProvisions ++
    carbohydrateNamedParentProvisions ++
    carbohydrateDerivativeProvisions ++
    carbohydrateUnsaturatedProvisions ++
    carbohydrateAlditolAcidProvisions

def carbohydrateSourceDataABatch :
    GlobalNonDescriptorSourceMeaningBatch carbohydrateSourceDataAProvisions := by
  simpa [carbohydrateSourceDataAProvisions, List.append_assoc] using
    carbohydrateScopeParentBatch.append
      (carbohydrateFoundationBatch.append
        (carbohydrateNamedParentBatch.append
          (carbohydrateDerivativeBatch.append
            (carbohydrateUnsaturatedBatch.append carbohydrateAlditolAcidBatch))))

@[simp] theorem carbohydrateSourceDataAProvisionCount :
    carbohydrateSourceDataAProvisions.length = 255 := by
  simp [carbohydrateSourceDataAProvisions]

theorem carbohydrateSourceDataAProvisions_nodup :
    carbohydrateSourceDataAProvisions.Nodup := by
  have unsaturatedAlditol :
      (carbohydrateUnsaturatedProvisions ++ carbohydrateAlditolAcidProvisions).Nodup :=
    carbohydrateUnsaturatedProvisions_nodup.append
      carbohydrateAlditolAcidProvisions_nodup
      (by
        simp [List.disjoint_left, carbohydrateUnsaturatedProvisions,
          carbohydrateAlditolAcidProvisions])
  have derivativeTail :
      (carbohydrateDerivativeProvisions ++
        (carbohydrateUnsaturatedProvisions ++ carbohydrateAlditolAcidProvisions)).Nodup :=
    carbohydrateDerivativeProvisions_nodup.append unsaturatedAlditol
      (by
        simp [List.disjoint_left, carbohydrateDerivativeProvisions,
          carbohydrateUnsaturatedProvisions, carbohydrateAlditolAcidProvisions])
  have namedTail :
      (carbohydrateNamedParentProvisions ++
        (carbohydrateDerivativeProvisions ++
          (carbohydrateUnsaturatedProvisions ++ carbohydrateAlditolAcidProvisions))).Nodup :=
    carbohydrateNamedParentProvisions_nodup.append derivativeTail
      (by
        simp [List.disjoint_left, carbohydrateNamedParentProvisions,
          carbohydrateDerivativeProvisions, carbohydrateUnsaturatedProvisions,
          carbohydrateAlditolAcidProvisions])
  have foundationTail :
      (carbohydrateFoundationProvisions ++
        (carbohydrateNamedParentProvisions ++
          (carbohydrateDerivativeProvisions ++
            (carbohydrateUnsaturatedProvisions ++
              carbohydrateAlditolAcidProvisions)))).Nodup :=
    carbohydrateFoundationProvisions_nodup.append namedTail
      (by
        simp [List.disjoint_left, carbohydrateFoundationProvisions,
          carbohydrateNamedParentProvisions, carbohydrateDerivativeProvisions,
          carbohydrateUnsaturatedProvisions, carbohydrateAlditolAcidProvisions])
  have allRows :
      (carbohydrateScopeParentProvisions ++
        (carbohydrateFoundationProvisions ++
          (carbohydrateNamedParentProvisions ++
            (carbohydrateDerivativeProvisions ++
              (carbohydrateUnsaturatedProvisions ++
                carbohydrateAlditolAcidProvisions))))).Nodup :=
    carbohydrateScopeParentProvisions_nodup.append foundationTail
      (by
        simp [List.disjoint_left, carbohydrateScopeParentProvisions,
          carbohydrateFoundationProvisions, carbohydrateNamedParentProvisions,
          carbohydrateDerivativeProvisions, carbohydrateUnsaturatedProvisions,
          carbohydrateAlditolAcidProvisions])
  simpa [carbohydrateSourceDataAProvisions, List.append_assoc] using allRows

end GlobalNonDescriptorIndexedSourceData
end IUPACNormativeProvision
end TetraStereo.OneCenter
