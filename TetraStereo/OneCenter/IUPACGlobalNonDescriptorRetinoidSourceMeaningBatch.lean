import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataCore
import TetraStereo.OneCenter.Retinoid1981SourceAuditLedger
import TetraStereo.KernelOnly

set_option autoImplicit false

















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorRetinoidSourceMeaning

open GlobalNonDescriptorIndexedSourceData

def retainedParents : List Retinoid1981.Parent :=
  [.retinol, .retinal, .retinoicAcid]

/-- A typed, finite source statement.  Payloads retain the actual parent, locant, geometry,
descriptor, ordering, and substitution data instead of reducing a row to its manifest tag. -/
inductive SourceAssertion where
  | stereoparentNameImpliesConfiguration (parents : List Retinoid1981.Parent)
  | retainedParentPolyeneGeometry
      (parent : Retinoid1981.Parent)
      (bondLocants : List Nat)
      (geometry : Retinoid1981.ParentGeometry)
  | stereochemicalLocantsUseRetinoidNumbering (polyeneBondLocants : List Nat)
  | chiralCentersUseRS (descriptors : List Retinoid1981.RS)
  | rsLocantsPrecedeRetinoidName
  | polyeneDefaultsToAllTrans
      (parents : List Retinoid1981.Parent)
      (bondLocants : List Nat)
  | cisCitationsFollowAbsoluteConfiguration
  | ezAllowedAndRequiredWhenAmbiguous
  | substitutionMayChangeEZWithoutGeometryChange
      (before after : Retinoid1981.BondInterpretation)
  | ezNotationCitesEveryDoubleBond (polyeneBondLocants : List Nat)
  | retroSixSevenConfigurationExplicitWhenNeeded
  deriving DecidableEq, Repr

structure SourceMeaning where
  sourceSection : Retinoid1981.SourceAudit.NormativeSection
  normativeClauses : List Retinoid1981.SourceAudit.Ledger.NormativeClause
  assertion : SourceAssertion
  deriving DecidableEq, Repr

/-- Complete source-family compiler for the thirteen already enumerated stereochemical rows. -/
def sourceMeaning : Retinoid1981.Provision → SourceMeaning
  | .stereoparentNameImpliesConfiguration =>
      ⟨.ret2, [.stereoparentNameImpliesStereochemistry],
        .stereoparentNameImpliesConfiguration retainedParents⟩
  | .retinolStereoparent =>
      ⟨.ret2_1, [.compoundOneRetinolDesignation], .retainedParentPolyeneGeometry .retinol
        (Retinoid1981.Parent.polyeneBondLocants .retinol) .trans⟩
  | .retinalStereoparent =>
      ⟨.ret2_2, [.compoundTwoRetinalDesignation], .retainedParentPolyeneGeometry .retinal
        (Retinoid1981.Parent.polyeneBondLocants .retinal) .trans⟩
  | .retinoicAcidStereoparent =>
      ⟨.ret2_3, [.compoundThreeRetinoicAcidDesignation],
        .retainedParentPolyeneGeometry .retinoicAcid
        (Retinoid1981.Parent.polyeneBondLocants .retinoicAcid) .trans⟩
  | .stereochemicalLocantsUseRetinoidNumbering =>
      ⟨.ret3, [.numberingStructuresOneToTen],
        .stereochemicalLocantsUseRetinoidNumbering [7, 9, 11, 13]⟩
  | .chiralCentersUseRS =>
      ⟨.ret5_1, [.chiralCentresUseRS], .chiralCentersUseRS [.R, .S]⟩
  | .rsLocantsPrecedeRetinoidName =>
      ⟨.ret5_1, [.rsSymbolsAndLocantsPrecedeName], .rsLocantsPrecedeRetinoidName⟩
  | .polyeneDefaultsToAllTrans =>
      ⟨.ret5_2, [.polyeneDefaultsToAllTrans],
        .polyeneDefaultsToAllTrans retainedParents [7, 9, 11, 13]⟩
  | .cisCitationsFollowAbsoluteConfiguration =>
      ⟨.ret5_2, [.cisCitationsFollowAbsoluteConfiguration],
        .cisCitationsFollowAbsoluteConfiguration⟩
  | .ezAllowedAndRequiredWhenAmbiguous =>
      ⟨.ret5_2, [.ezMayBeUsed, .ezRequiredWhenAmbiguous],
        .ezAllowedAndRequiredWhenAmbiguous⟩
  | .substitutionMayChangeEZWithoutGeometryChange =>
      ⟨.ret5_2, [.substitutionMayRelabelEZWithoutGeometryChange],
        .substitutionMayChangeEZWithoutGeometryChange
        Retinoid1981.beforeSubstitution Retinoid1981.afterPriorityChangingSubstitution⟩
  | .ezNotationCitesEveryDoubleBond =>
      ⟨.ret5_2, [.allDoubleBondsCitedWithEZ],
        .ezNotationCitesEveryDoubleBond [7, 9, 11, 13]⟩
  | .retroSixSevenConfigurationExplicitWhenNeeded =>
      ⟨.ret5_2, [.retroSixSevenStatedWhenNeeded],
        .retroSixSevenConfigurationExplicitWhenNeeded⟩

@[simp] theorem sourceMeaning_section_exact (row : Retinoid1981.Provision) :
    (sourceMeaning row).sourceSection = row.normativeSection := by
  cases row <;> rfl

@[simp] theorem sourceMeaning_clauses_exact (row : Retinoid1981.Provision) :
    (sourceMeaning row).normativeClauses =
      Retinoid1981.SourceAudit.Ledger.NormativeClause.forProvision row := by
  cases row <;> rfl

theorem sourceMeaning_clauses_mem_ledger (row : Retinoid1981.Provision) :
    (sourceMeaning row).normativeClauses.Forall fun clause =>
      clause ∈ Retinoid1981.SourceAudit.Ledger.NormativeClause.all := by
  rw [sourceMeaning_clauses_exact]
  exact Retinoid1981.SourceAudit.Ledger.NormativeClause.forProvision_mem_all row

theorem sourceMeaning_clause_sections_exact (row : Retinoid1981.Provision) :
    (sourceMeaning row).normativeClauses.Forall fun clause =>
      clause.normativeSection = (sourceMeaning row).sourceSection := by
  rw [sourceMeaning_clauses_exact, sourceMeaning_section_exact]
  exact Retinoid1981.SourceAudit.Ledger.NormativeClause.forProvision_sections_exact row

/-- Distinct provisions retain distinct typed assertions even when several share Ret-5.2. -/
theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  cases left <;> cases right <;> simp [sourceMeaning] at equal ⊢

def rows : List Retinoid1981.Provision :=
  Retinoid1981.Provision.all

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.retinoid1981

def batch : GlobalNonDescriptorSourceMeaningBatch provisions :=
  totalMeaningBatch rows IUPACNormativeProvision.retinoid1981 sourceMeaning
    (by intro _row; rfl)

@[simp] theorem provisions_exact :
    provisions = sourceProvisions .retinoidRecommendations1981 := by
  exact retinoid1981SemanticsSlice_exact

@[simp] theorem provision_count : provisions.length = 13 := by
  simp [provisions, rows]

@[simp] theorem entry_count : batch.entries.length = 13 := by
  rw [batch.entries_length, provision_count]

theorem provisions_nodup : provisions.Nodup := by
  exact Retinoid1981.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

@[simp] theorem entry_provisions_exact :
    batch.entries.map GlobalNonDescriptorSourceMeaningEntry.provision = provisions :=
  batch.provisions_exact

/-- Nonvacuity is stored in every dependent entry created by the family compiler. -/
theorem every_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (_member : entry ∈ batch.entries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment


theorem source_audit_still_open :
    ¬IUPACNormativeSource.ProvisionAuditComplete .retinoidRecommendations1981 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete]

end GlobalNonDescriptorRetinoidSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorRetinoidSourceMeaning.provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorRetinoidSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorRetinoidSourceMeaning.sourceMeaning_clauses_mem_ledger
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorRetinoidSourceMeaning.sourceMeaning_clause_sections_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorRetinoidSourceMeaning.entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorRetinoidSourceMeaning.every_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorRetinoidSourceMeaning.source_audit_still_open
