import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataBatch
import TetraStereo.KernelOnly

set_option autoImplicit false











namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning

open GlobalNonDescriptorIndexedSourceData

inductive SemanticDomain where
  | unsaturation
  | branchedParent
  | branchConfiguration
  | printedExample
  deriving DecidableEq, Repr

def semanticDomain : Carbohydrate1996UnsaturatedBranched.Provision → SemanticDomain
  | .unsaturationScopeContiguousBackboneCarbons
  | .exocyclicUnsaturationUsesGeneralOrganicRules
  | .doubleBondUsesXEnInfixAndEuphonicO
  | .unsaturationInfixAfterChainStem
  | .doubleBondLocantIsLowerCarbon
  | .ezPrecedesWholeNameWhenNecessary
  | .multipleDoubleBondsUseDienAndEuphonicA
  | .glycalNonpreferredOnlyForRingOneTwoDoubleBond
  | .glycalNotGeneralClassName
  | .ringCCROClassificationDependsOnR
  | .ringAtMostSixMayOmitEZ
  | .tripleBondUsesNYn
  | .cumulativeDoubleBondsUseDien
  | .alternativeDehydroDeoxyMethod
  | .deoxyOperationFormallyPrecedesDehydro
  | .dehydroAndDeoxyPrefixesAlphabetized => .unsaturation
  | .branchedRulesModify1980WithCyclicPriority
  | .branchedTrivialNamesExist
  | .listedBranchedEnantiomersNamedSystematically
  | .cyclicApioseSystematicNamePreferred
  | .alphaDErythroApiofuranoseIsAmbiguous
  | .branchedNamedAsSubstitutedUnbranchedParent
  | .cLocantsOnlyRequiredForAmbiguityButMayEmphasize
  | .cyclicParentChainMustIncludeRingAtoms
  | .acyclicBranchedParentUsesTwoCarbTwo
  | .branchesNamedAsSubstitutedAlkylGroups
  | .attachmentActsAsAldehydeAbsentBranchCarbonyl
  | .branchCarbonylOrTerminalAcidDefinesPrefix
  | .alternativeResidueSubstituentRoute
  | .parentChainNumberingUsesTwoCarbTwo
  | .optionalUniqueBranchNumberingScheme
  | .branchNumberingSchemeForbiddenInNames
  | .terminalSubstitutionRoutesToTwoCarbSixteen => .branchedParent
  | .hydroxyCanDetermineBranchPointConfiguration
  | .deoxyBranchPointUsesRemainingSubstituent
  | .branchPointUsesCIPElementPriority
  | .identicalBranchSubstituentsMakeCenterAchiral
  | .achiralBranchPointUsesWholeSequencePrefix
  | .cyclizationCanChangePrefixCenterCount
  | .cyclicAndAcyclicFormsCanHaveDifferentNames
  | .branchCentersUseRSOrStraightforwardCarbohydratePrefix
  | .branchRSGenerallyPreferred
  | .chartV _ => .branchConfiguration
  | .printedExample _ => .printedExample

def unsaturationInfixInventory :
    List ((Carbohydrate1996UnsaturatedBranched.BackboneUnsaturation × Nat) × String) :=
  [ ((.doubleBond, 5),
      Carbohydrate1996UnsaturatedBranched.BackboneUnsaturation.doubleBond.infix 5)
  , ((.tripleBond, 5),
      Carbohydrate1996UnsaturatedBranched.BackboneUnsaturation.tripleBond.infix 5)
  , ((.cumulativeDoubleBonds, 6),
      Carbohydrate1996UnsaturatedBranched.BackboneUnsaturation.cumulativeDoubleBonds.infix 6) ]

def ezOmissionInventory : List ((Bool × Nat) × Bool) :=
  [ ((true, 6), Carbohydrate1996UnsaturatedBranched.ezMayBeOmitted true 6)
  , ((true, 7), Carbohydrate1996UnsaturatedBranched.ezMayBeOmitted true 7)
  , ((false, 5), Carbohydrate1996UnsaturatedBranched.ezMayBeOmitted false 5) ]

def ringEnolParentInventory :
    List (Carbohydrate1996UnsaturatedBranched.RingEnolSubstituentKind ×
      Carbohydrate1996UnsaturatedBranched.RingEnolParentClass) :=
  [ (.hydrogenOrCarbon,
      Carbohydrate1996UnsaturatedBranched.ringEnolParentClass .hydrogenOrCarbon)
  , (.halogenChalcogenOrNitrogenFamily,
      Carbohydrate1996UnsaturatedBranched.ringEnolParentClass
        .halogenChalcogenOrNitrogenFamily) ]

def branchParentEvidenceInventory :
    List (Bool × Carbohydrate1996UnsaturatedBranched.BranchParentEvidence) :=
  [ (true, Carbohydrate1996UnsaturatedBranched.chooseBranchParentEvidence true)
  , (false, Carbohydrate1996UnsaturatedBranched.chooseBranchParentEvidence false) ]

def elementRankInventory : List (String × Option Nat) :=
  [ ("N", Carbohydrate1996UnsaturatedBranched.elementRank "N")
  , ("O", Carbohydrate1996UnsaturatedBranched.elementRank "O")
  , ("C", Carbohydrate1996UnsaturatedBranched.elementRank "C") ]

inductive SourceAssertion where
  | unsaturationScopeContiguousBackboneCarbons
  | exocyclicUnsaturationUsesGeneralOrganicRules
  | doubleBondUsesXEnInfixAndEuphonicO
      (inventory : List ((Carbohydrate1996UnsaturatedBranched.BackboneUnsaturation × Nat) × String))
  | unsaturationInfixAfterChainStem
  | doubleBondLocantIsLowerCarbon
  | ezPrecedesWholeNameWhenNecessary
  | multipleDoubleBondsUseDienAndEuphonicA
  | glycalNonpreferredOnlyForRingOneTwoDoubleBond
  | glycalNotGeneralClassName
  | ringCCROClassificationDependsOnR
      (inventory : List (Carbohydrate1996UnsaturatedBranched.RingEnolSubstituentKind ×
        Carbohydrate1996UnsaturatedBranched.RingEnolParentClass))
  | ringAtMostSixMayOmitEZ (inventory : List ((Bool × Nat) × Bool))
  | tripleBondUsesNYn
      (inventory : List ((Carbohydrate1996UnsaturatedBranched.BackboneUnsaturation × Nat) × String))
  | cumulativeDoubleBondsUseDien
      (inventory : List ((Carbohydrate1996UnsaturatedBranched.BackboneUnsaturation × Nat) × String))
  | alternativeDehydroDeoxyMethod
  | deoxyOperationFormallyPrecedesDehydro
  | dehydroAndDeoxyPrefixesAlphabetized
  | branchedRulesModify1980WithCyclicPriority
  | branchedTrivialNamesExist
  | listedBranchedEnantiomersNamedSystematically
  | cyclicApioseSystematicNamePreferred
  | alphaDErythroApiofuranoseIsAmbiguous
  | branchedNamedAsSubstitutedUnbranchedParent
  | cLocantsOnlyRequiredForAmbiguityButMayEmphasize
  | cyclicParentChainMustIncludeRingAtoms
      (inventory : List (Bool × Carbohydrate1996UnsaturatedBranched.BranchParentEvidence))
  | acyclicBranchedParentUsesTwoCarbTwo
      (inventory : List (Bool × Carbohydrate1996UnsaturatedBranched.BranchParentEvidence))
  | hydroxyCanDetermineBranchPointConfiguration
  | deoxyBranchPointUsesRemainingSubstituent
  | branchPointUsesCIPElementPriority (inventory : List (String × Option Nat))
  | identicalBranchSubstituentsMakeCenterAchiral (first second : String) (result : Bool)
  | achiralBranchPointUsesWholeSequencePrefix
  | cyclizationCanChangePrefixCenterCount
  | cyclicAndAcyclicFormsCanHaveDifferentNames
  | branchesNamedAsSubstitutedAlkylGroups
  | branchCentersUseRSOrStraightforwardCarbohydratePrefix
  | attachmentActsAsAldehydeAbsentBranchCarbonyl
  | branchCarbonylOrTerminalAcidDefinesPrefix
  | branchRSGenerallyPreferred
      (method : Carbohydrate1996UnsaturatedBranched.BranchConfigurationMethod)
  | alternativeResidueSubstituentRoute
  | parentChainNumberingUsesTwoCarbTwo
  | optionalUniqueBranchNumberingScheme
  | branchNumberingSchemeForbiddenInNames
  | terminalSubstitutionRoutesToTwoCarbSixteen
  | chartV (row : Carbohydrate1996UnsaturatedBranched.ChartVRow)
      (data : Carbohydrate1996UnsaturatedBranched.ChartVData)
  | printedExample (row : Carbohydrate1996UnsaturatedBranched.PrintedExample)
      (data : Carbohydrate1996UnsaturatedBranched.PrintedExampleData)
  deriving Repr

def sourceAssertion : Carbohydrate1996UnsaturatedBranched.Provision → SourceAssertion
  | .unsaturationScopeContiguousBackboneCarbons => .unsaturationScopeContiguousBackboneCarbons
  | .exocyclicUnsaturationUsesGeneralOrganicRules => .exocyclicUnsaturationUsesGeneralOrganicRules
  | .doubleBondUsesXEnInfixAndEuphonicO =>
      .doubleBondUsesXEnInfixAndEuphonicO unsaturationInfixInventory
  | .unsaturationInfixAfterChainStem => .unsaturationInfixAfterChainStem
  | .doubleBondLocantIsLowerCarbon => .doubleBondLocantIsLowerCarbon
  | .ezPrecedesWholeNameWhenNecessary => .ezPrecedesWholeNameWhenNecessary
  | .multipleDoubleBondsUseDienAndEuphonicA => .multipleDoubleBondsUseDienAndEuphonicA
  | .glycalNonpreferredOnlyForRingOneTwoDoubleBond => .glycalNonpreferredOnlyForRingOneTwoDoubleBond
  | .glycalNotGeneralClassName => .glycalNotGeneralClassName
  | .ringCCROClassificationDependsOnR => .ringCCROClassificationDependsOnR ringEnolParentInventory
  | .ringAtMostSixMayOmitEZ => .ringAtMostSixMayOmitEZ ezOmissionInventory
  | .tripleBondUsesNYn => .tripleBondUsesNYn unsaturationInfixInventory
  | .cumulativeDoubleBondsUseDien => .cumulativeDoubleBondsUseDien unsaturationInfixInventory
  | .alternativeDehydroDeoxyMethod => .alternativeDehydroDeoxyMethod
  | .deoxyOperationFormallyPrecedesDehydro => .deoxyOperationFormallyPrecedesDehydro
  | .dehydroAndDeoxyPrefixesAlphabetized => .dehydroAndDeoxyPrefixesAlphabetized
  | .branchedRulesModify1980WithCyclicPriority => .branchedRulesModify1980WithCyclicPriority
  | .branchedTrivialNamesExist => .branchedTrivialNamesExist
  | .listedBranchedEnantiomersNamedSystematically => .listedBranchedEnantiomersNamedSystematically
  | .cyclicApioseSystematicNamePreferred => .cyclicApioseSystematicNamePreferred
  | .alphaDErythroApiofuranoseIsAmbiguous => .alphaDErythroApiofuranoseIsAmbiguous
  | .branchedNamedAsSubstitutedUnbranchedParent => .branchedNamedAsSubstitutedUnbranchedParent
  | .cLocantsOnlyRequiredForAmbiguityButMayEmphasize =>
      .cLocantsOnlyRequiredForAmbiguityButMayEmphasize
  | .cyclicParentChainMustIncludeRingAtoms =>
      .cyclicParentChainMustIncludeRingAtoms branchParentEvidenceInventory
  | .acyclicBranchedParentUsesTwoCarbTwo =>
      .acyclicBranchedParentUsesTwoCarbTwo branchParentEvidenceInventory
  | .hydroxyCanDetermineBranchPointConfiguration => .hydroxyCanDetermineBranchPointConfiguration
  | .deoxyBranchPointUsesRemainingSubstituent => .deoxyBranchPointUsesRemainingSubstituent
  | .branchPointUsesCIPElementPriority => .branchPointUsesCIPElementPriority elementRankInventory
  | .identicalBranchSubstituentsMakeCenterAchiral =>
      .identicalBranchSubstituentsMakeCenterAchiral "methyl" "methyl"
        (Carbohydrate1996UnsaturatedBranched.branchPointIsChiral "methyl" "methyl")
  | .achiralBranchPointUsesWholeSequencePrefix => .achiralBranchPointUsesWholeSequencePrefix
  | .cyclizationCanChangePrefixCenterCount => .cyclizationCanChangePrefixCenterCount
  | .cyclicAndAcyclicFormsCanHaveDifferentNames => .cyclicAndAcyclicFormsCanHaveDifferentNames
  | .branchesNamedAsSubstitutedAlkylGroups => .branchesNamedAsSubstitutedAlkylGroups
  | .branchCentersUseRSOrStraightforwardCarbohydratePrefix =>
      .branchCentersUseRSOrStraightforwardCarbohydratePrefix
  | .attachmentActsAsAldehydeAbsentBranchCarbonyl => .attachmentActsAsAldehydeAbsentBranchCarbonyl
  | .branchCarbonylOrTerminalAcidDefinesPrefix => .branchCarbonylOrTerminalAcidDefinesPrefix
  | .branchRSGenerallyPreferred =>
      .branchRSGenerallyPreferred Carbohydrate1996UnsaturatedBranched.preferredBranchConfigurationMethod
  | .alternativeResidueSubstituentRoute => .alternativeResidueSubstituentRoute
  | .parentChainNumberingUsesTwoCarbTwo => .parentChainNumberingUsesTwoCarbTwo
  | .optionalUniqueBranchNumberingScheme => .optionalUniqueBranchNumberingScheme
  | .branchNumberingSchemeForbiddenInNames => .branchNumberingSchemeForbiddenInNames
  | .terminalSubstitutionRoutesToTwoCarbSixteen => .terminalSubstitutionRoutesToTwoCarbSixteen
  | .chartV row => .chartV row row.data
  | .printedExample row => .printedExample row row.data

def SourceAssertion.provision : SourceAssertion → Carbohydrate1996UnsaturatedBranched.Provision
  | .unsaturationScopeContiguousBackboneCarbons => .unsaturationScopeContiguousBackboneCarbons
  | .exocyclicUnsaturationUsesGeneralOrganicRules => .exocyclicUnsaturationUsesGeneralOrganicRules
  | .doubleBondUsesXEnInfixAndEuphonicO _ => .doubleBondUsesXEnInfixAndEuphonicO
  | .unsaturationInfixAfterChainStem => .unsaturationInfixAfterChainStem
  | .doubleBondLocantIsLowerCarbon => .doubleBondLocantIsLowerCarbon
  | .ezPrecedesWholeNameWhenNecessary => .ezPrecedesWholeNameWhenNecessary
  | .multipleDoubleBondsUseDienAndEuphonicA => .multipleDoubleBondsUseDienAndEuphonicA
  | .glycalNonpreferredOnlyForRingOneTwoDoubleBond => .glycalNonpreferredOnlyForRingOneTwoDoubleBond
  | .glycalNotGeneralClassName => .glycalNotGeneralClassName
  | .ringCCROClassificationDependsOnR _ => .ringCCROClassificationDependsOnR
  | .ringAtMostSixMayOmitEZ _ => .ringAtMostSixMayOmitEZ
  | .tripleBondUsesNYn _ => .tripleBondUsesNYn
  | .cumulativeDoubleBondsUseDien _ => .cumulativeDoubleBondsUseDien
  | .alternativeDehydroDeoxyMethod => .alternativeDehydroDeoxyMethod
  | .deoxyOperationFormallyPrecedesDehydro => .deoxyOperationFormallyPrecedesDehydro
  | .dehydroAndDeoxyPrefixesAlphabetized => .dehydroAndDeoxyPrefixesAlphabetized
  | .branchedRulesModify1980WithCyclicPriority => .branchedRulesModify1980WithCyclicPriority
  | .branchedTrivialNamesExist => .branchedTrivialNamesExist
  | .listedBranchedEnantiomersNamedSystematically => .listedBranchedEnantiomersNamedSystematically
  | .cyclicApioseSystematicNamePreferred => .cyclicApioseSystematicNamePreferred
  | .alphaDErythroApiofuranoseIsAmbiguous => .alphaDErythroApiofuranoseIsAmbiguous
  | .branchedNamedAsSubstitutedUnbranchedParent => .branchedNamedAsSubstitutedUnbranchedParent
  | .cLocantsOnlyRequiredForAmbiguityButMayEmphasize =>
      .cLocantsOnlyRequiredForAmbiguityButMayEmphasize
  | .cyclicParentChainMustIncludeRingAtoms _ => .cyclicParentChainMustIncludeRingAtoms
  | .acyclicBranchedParentUsesTwoCarbTwo _ => .acyclicBranchedParentUsesTwoCarbTwo
  | .hydroxyCanDetermineBranchPointConfiguration => .hydroxyCanDetermineBranchPointConfiguration
  | .deoxyBranchPointUsesRemainingSubstituent => .deoxyBranchPointUsesRemainingSubstituent
  | .branchPointUsesCIPElementPriority _ => .branchPointUsesCIPElementPriority
  | .identicalBranchSubstituentsMakeCenterAchiral _ _ _ => .identicalBranchSubstituentsMakeCenterAchiral
  | .achiralBranchPointUsesWholeSequencePrefix => .achiralBranchPointUsesWholeSequencePrefix
  | .cyclizationCanChangePrefixCenterCount => .cyclizationCanChangePrefixCenterCount
  | .cyclicAndAcyclicFormsCanHaveDifferentNames => .cyclicAndAcyclicFormsCanHaveDifferentNames
  | .branchesNamedAsSubstitutedAlkylGroups => .branchesNamedAsSubstitutedAlkylGroups
  | .branchCentersUseRSOrStraightforwardCarbohydratePrefix =>
      .branchCentersUseRSOrStraightforwardCarbohydratePrefix
  | .attachmentActsAsAldehydeAbsentBranchCarbonyl => .attachmentActsAsAldehydeAbsentBranchCarbonyl
  | .branchCarbonylOrTerminalAcidDefinesPrefix => .branchCarbonylOrTerminalAcidDefinesPrefix
  | .branchRSGenerallyPreferred _ => .branchRSGenerallyPreferred
  | .alternativeResidueSubstituentRoute => .alternativeResidueSubstituentRoute
  | .parentChainNumberingUsesTwoCarbTwo => .parentChainNumberingUsesTwoCarbTwo
  | .optionalUniqueBranchNumberingScheme => .optionalUniqueBranchNumberingScheme
  | .branchNumberingSchemeForbiddenInNames => .branchNumberingSchemeForbiddenInNames
  | .terminalSubstitutionRoutesToTwoCarbSixteen => .terminalSubstitutionRoutesToTwoCarbSixteen
  | .chartV row _ => .chartV row
  | .printedExample row _ => .printedExample row

@[simp] theorem sourceAssertion_provision_exact
    (row : Carbohydrate1996UnsaturatedBranched.Provision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

structure SourceMeaning where
  sourceKey : String
  semanticDomain : SemanticDomain
  assertion : SourceAssertion
  deriving Repr

def sourceMeaning (row : Carbohydrate1996UnsaturatedBranched.Provision) : SourceMeaning :=
  ⟨row.sourceKey, semanticDomain row, sourceAssertion row⟩

@[simp] theorem sourceMeaning_key_exact (row : Carbohydrate1996UnsaturatedBranched.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by rfl

@[simp] theorem sourceMeaning_domain_exact (row : Carbohydrate1996UnsaturatedBranched.Provision) :
    (sourceMeaning row).semanticDomain = semanticDomain row := by rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def fullFamilyRows : List Carbohydrate1996UnsaturatedBranched.Provision :=
  Carbohydrate1996UnsaturatedBranched.Provision.all

def fullFamilyProvisions : List IUPACNormativeProvision :=
  fullFamilyRows.map IUPACNormativeProvision.carbohydrate1996UnsaturatedBranched

def completionRows : List Carbohydrate1996UnsaturatedBranched.Provision :=
  Carbohydrate1996UnsaturatedBranched.Provision.base

def completionProvisions : List IUPACNormativeProvision :=
  completionRows.map IUPACNormativeProvision.carbohydrate1996UnsaturatedBranched

def completionBatch : GlobalNonDescriptorSourceMeaningBatch completionProvisions :=
  totalMeaningBatch completionRows IUPACNormativeProvision.carbohydrate1996UnsaturatedBranched
    sourceMeaning (by intro _row; rfl)

@[simp] theorem full_family_provisions_exact :
    fullFamilyProvisions = carbohydrate1996UnsaturatedBranchedSemanticsSlice := by rfl

@[simp] theorem full_family_provision_count : fullFamilyProvisions.length = 85 := by
  simp [fullFamilyProvisions, fullFamilyRows]

@[simp] theorem completion_provision_count : completionProvisions.length = 42 := by
  simp [completionProvisions, completionRows,
    Carbohydrate1996UnsaturatedBranched.Provision.base]

@[simp] theorem completion_entry_count : completionBatch.entries.length = 42 := by
  rw [completionBatch.entries_length, completion_provision_count]

private theorem completion_rows_then_indexed_exact :
    completionRows ++ GlobalNonDescriptorIndexedSourceData.carbohydrateUnsaturatedRows =
      fullFamilyRows := by
  simp [completionRows, fullFamilyRows,
    GlobalNonDescriptorIndexedSourceData.carbohydrateUnsaturatedRows,
    Carbohydrate1996UnsaturatedBranched.Provision.all, List.append_assoc]

theorem completion_then_indexed_exact_source_order :
    completionProvisions ++ GlobalNonDescriptorIndexedSourceData.carbohydrateUnsaturatedProvisions =
      carbohydrate1996UnsaturatedBranchedSemanticsSlice := by
  rw [← full_family_provisions_exact]
  simp only [completionProvisions,
    GlobalNonDescriptorIndexedSourceData.carbohydrateUnsaturatedProvisions,
    fullFamilyProvisions, ← List.map_append]
  rw [completion_rows_then_indexed_exact]

theorem materialized_order_perm_source :
    (GlobalNonDescriptorIndexedSourceData.carbohydrateUnsaturatedProvisions ++
      completionProvisions).Perm carbohydrate1996UnsaturatedBranchedSemanticsSlice := by
  calc
    (GlobalNonDescriptorIndexedSourceData.carbohydrateUnsaturatedProvisions ++
      completionProvisions).Perm
        (completionProvisions ++
          GlobalNonDescriptorIndexedSourceData.carbohydrateUnsaturatedProvisions) :=
      List.perm_append_comm
    _ = carbohydrate1996UnsaturatedBranchedSemanticsSlice :=
      completion_then_indexed_exact_source_order

theorem completion_disjoint_indexed :
    completionProvisions.Disjoint
      GlobalNonDescriptorIndexedSourceData.carbohydrateUnsaturatedProvisions := by
  apply List.disjoint_of_nodup_append
  rw [completion_then_indexed_exact_source_order]
  exact Carbohydrate1996UnsaturatedBranched.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

theorem completion_provisions_nodup : completionProvisions.Nodup := by
  exact Carbohydrate1996UnsaturatedBranched.Provision.all_nodup.of_append_left.of_append_left.map
    (by intro left right equal; cases equal; rfl)

@[simp] theorem completion_entry_provisions_exact :
    completionBatch.entries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      completionProvisions := completionBatch.provisions_exact

theorem every_completion_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (_member : entry ∈ completionBatch.entries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment

theorem source_audit_still_open :
    ¬IUPACNormativeSource.ProvisionAuditComplete .carbohydrateRecommendations1996 := by
  exact IUPACNormativeSource.provisionAuditIncomplete_of_figure_review_open _ rfl

end GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.full_family_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completion_then_indexed_exact_source_order
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.materialized_order_perm_source
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.completion_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.every_completion_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateUnsaturatedSourceMeaning.source_audit_still_open
