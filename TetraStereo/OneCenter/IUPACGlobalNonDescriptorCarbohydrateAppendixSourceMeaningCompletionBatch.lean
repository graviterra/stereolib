import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataBatch
import TetraStereo.KernelOnly

set_option autoImplicit false










namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateAppendixSourceMeaning

open GlobalNonDescriptorIndexedSourceData

inductive SemanticDomain where
  | appendixPolicy
  | retainedName
  | publishedErratum
  | glossaryCell
  | glossaryFootnote
  deriving DecidableEq, Repr

def semanticDomain : Carbohydrate1996AppendixErrataGlossary.Provision → SemanticDomain
  | .appendixIsNonlimitingList
  | .appendixGivesSystematicEquivalents
  | .appendixGivesSymbolsWhereEstablished => .appendixPolicy
  | .retainedName _ => .retainedName
  | .publishedErratum _ => .publishedErratum
  | .glossaryCell _ => .glossaryCell
  | .glossaryFootnote _ => .glossaryFootnote

inductive SourceAssertion where
  | appendixIsNonlimitingList
  | appendixGivesSystematicEquivalents
      (correctedRows : List Carbohydrate1996AppendixErrataGlossary.RetainedNameData)
  | appendixGivesSymbolsWhereEstablished
      (correctedRows : List Carbohydrate1996AppendixErrataGlossary.RetainedNameData)
  | retainedName (row : Carbohydrate1996AppendixErrataGlossary.RetainedNameRow)
      (data : Carbohydrate1996AppendixErrataGlossary.RetainedNameData)
  | publishedErratum (row : Carbohydrate1996AppendixErrataGlossary.ErratumRow)
      (data : Carbohydrate1996AppendixErrataGlossary.ErratumData)
  | glossaryCell (cell : Carbohydrate1996AppendixErrataGlossary.GlossaryCell)
      (data : Carbohydrate1996AppendixErrataGlossary.GlossaryCellData)
  | glossaryFootnote (footnote : Carbohydrate1996AppendixErrataGlossary.GlossaryFootnote)
      (meaning : String)
  deriving Repr

def sourceAssertion : Carbohydrate1996AppendixErrataGlossary.Provision → SourceAssertion
  | .appendixIsNonlimitingList => .appendixIsNonlimitingList
  | .appendixGivesSystematicEquivalents =>
      .appendixGivesSystematicEquivalents
        Carbohydrate1996AppendixErrataGlossary.correctedAppendixRows
  | .appendixGivesSymbolsWhereEstablished =>
      .appendixGivesSymbolsWhereEstablished
        Carbohydrate1996AppendixErrataGlossary.correctedAppendixRows
  | .retainedName row => .retainedName row row.data
  | .publishedErratum row => .publishedErratum row row.data
  | .glossaryCell cell => .glossaryCell cell cell.data
  | .glossaryFootnote footnote => .glossaryFootnote footnote footnote.meaning

def SourceAssertion.provision :
    SourceAssertion → Carbohydrate1996AppendixErrataGlossary.Provision
  | .appendixIsNonlimitingList => .appendixIsNonlimitingList
  | .appendixGivesSystematicEquivalents _ => .appendixGivesSystematicEquivalents
  | .appendixGivesSymbolsWhereEstablished _ => .appendixGivesSymbolsWhereEstablished
  | .retainedName row _ => .retainedName row
  | .publishedErratum row _ => .publishedErratum row
  | .glossaryCell cell _ => .glossaryCell cell
  | .glossaryFootnote footnote _ => .glossaryFootnote footnote

@[simp] theorem sourceAssertion_provision_exact
    (row : Carbohydrate1996AppendixErrataGlossary.Provision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

structure SourceMeaning where
  sourceKey : String
  semanticDomain : SemanticDomain
  assertion : SourceAssertion
  deriving Repr

def sourceMeaning (row : Carbohydrate1996AppendixErrataGlossary.Provision) : SourceMeaning :=
  ⟨row.sourceKey, semanticDomain row, sourceAssertion row⟩

@[simp] theorem sourceMeaning_key_exact
    (row : Carbohydrate1996AppendixErrataGlossary.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by rfl

@[simp] theorem sourceMeaning_domain_exact
    (row : Carbohydrate1996AppendixErrataGlossary.Provision) :
    (sourceMeaning row).semanticDomain = semanticDomain row := by rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def fullFamilyRows : List Carbohydrate1996AppendixErrataGlossary.Provision :=
  Carbohydrate1996AppendixErrataGlossary.Provision.all

def fullFamilyProvisions : List IUPACNormativeProvision :=
  fullFamilyRows.map IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary

def completionRows : List Carbohydrate1996AppendixErrataGlossary.Provision :=
  Carbohydrate1996AppendixErrataGlossary.Provision.base

def completionProvisions : List IUPACNormativeProvision :=
  completionRows.map IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary

def completionBatch : GlobalNonDescriptorSourceMeaningBatch completionProvisions :=
  totalMeaningBatch completionRows
    IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary sourceMeaning
      (by intro _row; rfl)

@[simp] theorem full_family_provisions_exact :
    fullFamilyProvisions = carbohydrate1996AppendixErrataGlossarySemanticsSlice := by rfl

@[simp] theorem full_family_provision_count : fullFamilyProvisions.length = 175 := by
  simp [fullFamilyProvisions, fullFamilyRows]

@[simp] theorem completion_provision_count : completionProvisions.length = 3 := by
  simp [completionProvisions, completionRows,
    Carbohydrate1996AppendixErrataGlossary.Provision.base]

@[simp] theorem indexed_provision_count : carbohydrateAppendixProvisions.length = 172 :=
  carbohydrateAppendixProvisionCount

@[simp] theorem completion_entry_count : completionBatch.entries.length = 3 := by
  rw [completionBatch.entries_length, completion_provision_count]

private theorem completion_rows_then_indexed_exact :
    completionRows ++ carbohydrateAppendixRows = fullFamilyRows := by
  simp [completionRows, carbohydrateAppendixRows, fullFamilyRows,
    Carbohydrate1996AppendixErrataGlossary.Provision.all, List.append_assoc]

theorem completion_then_indexed_exact_source_order :
    completionProvisions ++ carbohydrateAppendixProvisions =
      carbohydrate1996AppendixErrataGlossarySemanticsSlice := by
  rw [← full_family_provisions_exact]
  simp only [completionProvisions, carbohydrateAppendixProvisions, fullFamilyProvisions,
    ← List.map_append]
  rw [completion_rows_then_indexed_exact]

theorem materialized_order_perm_source :
    (carbohydrateAppendixProvisions ++ completionProvisions).Perm
      carbohydrate1996AppendixErrataGlossarySemanticsSlice := by
  calc
    (carbohydrateAppendixProvisions ++ completionProvisions).Perm
        (completionProvisions ++ carbohydrateAppendixProvisions) := List.perm_append_comm
    _ = carbohydrate1996AppendixErrataGlossarySemanticsSlice :=
      completion_then_indexed_exact_source_order

theorem completion_disjoint_indexed :
    completionProvisions.Disjoint carbohydrateAppendixProvisions := by
  apply List.disjoint_of_nodup_append
  rw [completion_then_indexed_exact_source_order]
  exact Carbohydrate1996AppendixErrataGlossary.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

set_option maxRecDepth 4096 in
theorem completion_provisions_nodup : completionProvisions.Nodup :=
  Carbohydrate1996AppendixErrataGlossary.Provision.all_nodup.of_append_left.of_append_left.of_append_left.of_append_left.map
    (by intro left right equal; cases equal; rfl)

theorem indexed_provisions_nodup : carbohydrateAppendixProvisions.Nodup :=
  carbohydrateAppendixProvisions_nodup

@[simp] theorem corrected_rows_exact :
    Carbohydrate1996AppendixErrataGlossary.correctedAppendixRows =
      Carbohydrate1996AppendixErrataGlossary.retainedNameRows := by rfl

theorem corrected_appendix_errata_exact :
    (Carbohydrate1996AppendixErrataGlossary.correctedAppendixRows.any fun row =>
      row.retainedName = "Cymarose" ∧
        row.systematicEquivalent = "2,6-Dideoxy-3-O-methyl-ribo-hexose") = true ∧
    (Carbohydrate1996AppendixErrataGlossary.correctedAppendixRows.any fun row =>
      row.retainedName = "Umbelliferose" ∧
        row.systematicEquivalent =
          "β-D-Fructofuranosyl α-D-galactopyranosyl-(1→2)-α-D-glucopyranoside") = true ∧
    (Carbohydrate1996AppendixErrataGlossary.correctedAppendixRows.any fun row =>
      row.retainedName = "Acosamine" ∧
        row.systematicEquivalent = "3-Amino-2,3,6-trideoxy-L-arabino-hexose") = true ∧
    (Carbohydrate1996AppendixErrataGlossary.correctedAppendixRows.any fun row =>
      row.retainedName = "Kansosamine" ∧
        row.systematicEquivalent =
          "4-Amino-4,6-dideoxy-3-C-methyl-2-O-methyl-L-mannose") = true :=
  Carbohydrate1996AppendixErrataGlossary.corrected_appendix_includes_all_four_explicit_appendix_errata

@[simp] theorem completion_entry_provisions_exact :
    completionBatch.entries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      completionProvisions := completionBatch.provisions_exact

theorem every_completion_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (_member : entry ∈ completionBatch.entries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧ entry.reference.toReference.Applicable input ∧
        entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment

theorem source_audit_still_open :
    ¬IUPACNormativeSource.ProvisionAuditComplete .carbohydrateRecommendations1996 := by
  exact IUPACNormativeSource.provisionAuditIncomplete_of_figure_review_open _ rfl

end GlobalNonDescriptorCarbohydrateAppendixSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.full_family_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completion_then_indexed_exact_source_order
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.materialized_order_perm_source
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.corrected_appendix_errata_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.completion_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.every_completion_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAppendixSourceMeaning.source_audit_still_open
