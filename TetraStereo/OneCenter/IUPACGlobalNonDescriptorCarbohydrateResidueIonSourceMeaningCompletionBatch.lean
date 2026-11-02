import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataBatch
import TetraStereo.KernelOnly

set_option autoImplicit false











namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning

open GlobalNonDescriptorIndexedSourceData

inductive SemanticDomain where
  | glycosylResidue
  | substituentResidue
  | multivalentResidue
  | radical
  | cation
  | anion
  | radicalIon
  | printedExample
  deriving DecidableEq, Repr

def semanticDomain : Carbohydrate1996ResiduesIons.Provision → SemanticDomain
  | .glycosylResidueDropsAnomericHydroxyAndEToYl
  | .glycosylResiduesUsedForGlycosidesAndOligosaccharides
  | .glycosylAlsoUsedRadicofunctionally => .glycosylResidue
  | .carbohydrateSubstituentPrefixesAllowNoncarbohydrateParent
  | .residueEndingsNCylNOylOrNyl
  | .residueYlMeansLossOfHydrogenAtN
  | .secondaryFreeValenceEquivalentToHydroxy
  | .alditolResiduesUseSameEndings
  | .unlocantedYlMeansLossOfAnomericHydroxy
  | .unlocantedYloxyMeansLossOfAnomericHydroxyHydrogen
  | .retainedAnomericHydroxyCarbonLossUsesOneHydroxyYl
  | .retainedAnomericHydroxyAlphaBetaRefersToFreeValence => .substituentResidue
  | .differentCarbonHydrogenLossUsesDiylTriyl
  | .sameCarbonMultipleHydrogenLossUsesYlidene
  | .phosphaneTerminologyPreferred => .multivalentResidue
  | .radicalNamesFollowSubstituentNames
  | .carbeneUsesYlidene => .radical
  | .carbonHydrideLossCationUsesYlium
  | .oxygenHydronationUsesLocantedOium => .cation
  | .oxygenProtonLossAnionUsesLocantedOate
  | .carbonProtonLossAnionUsesIde => .anion
  | .radicalIonMayAddYlToIonName
  | .unspecifiedRadicalIonMayUsePostposedClass
  | .revisedRadicalIonAuthorityDelegated => .radicalIon
  | .printedExample _ => .printedExample

def anomericReferentInventory :
    List (Carbohydrate1996ResiduesIons.ResidueEvent ×
      Carbohydrate1996ResiduesIons.AnomericSymbolReferent) :=
  [ (.secondaryCarbonHydrogenLoss,
      Carbohydrate1996ResiduesIons.anomericSymbolReferent .secondaryCarbonHydrogenLoss)
  , (.anomericHydroxyLoss,
      Carbohydrate1996ResiduesIons.anomericSymbolReferent .anomericHydroxyLoss)
  , (.anomericHydroxyHydrogenLoss,
      Carbohydrate1996ResiduesIons.anomericSymbolReferent .anomericHydroxyHydrogenLoss)
  , (.anomericCarbonHydrogenLossHydroxyRetained,
      Carbohydrate1996ResiduesIons.anomericSymbolReferent
        .anomericCarbonHydrogenLossHydroxyRetained) ]

def ionSuffixInventory :
    List ((Carbohydrate1996ResiduesIons.ChargeCenter ×
      Carbohydrate1996ResiduesIons.ChargeChange) × Option String) :=
  [ ((.carbon, .hydrideLoss),
      Carbohydrate1996ResiduesIons.ionSuffix .carbon .hydrideLoss)
  , ((.carbon, .protonLoss),
      Carbohydrate1996ResiduesIons.ionSuffix .carbon .protonLoss)
  , ((.carbon, .hydronation),
      Carbohydrate1996ResiduesIons.ionSuffix .carbon .hydronation)
  , ((.oxygen, .hydrideLoss),
      Carbohydrate1996ResiduesIons.ionSuffix .oxygen .hydrideLoss)
  , ((.oxygen, .protonLoss),
      Carbohydrate1996ResiduesIons.ionSuffix .oxygen .protonLoss)
  , ((.oxygen, .hydronation),
      Carbohydrate1996ResiduesIons.ionSuffix .oxygen .hydronation) ]

inductive SourceAssertion where
  | glycosylResidueDropsAnomericHydroxyAndEToYl
  | glycosylResiduesUsedForGlycosidesAndOligosaccharides
  | glycosylAlsoUsedRadicofunctionally
  | carbohydrateSubstituentPrefixesAllowNoncarbohydrateParent
  | residueEndingsNCylNOylOrNyl
  | residueYlMeansLossOfHydrogenAtN
  | secondaryFreeValenceEquivalentToHydroxy
  | alditolResiduesUseSameEndings
  | unlocantedYlMeansLossOfAnomericHydroxy
      (event : Carbohydrate1996ResiduesIons.ResidueEvent)
      (referent : Carbohydrate1996ResiduesIons.AnomericSymbolReferent)
  | unlocantedYloxyMeansLossOfAnomericHydroxyHydrogen
      (event : Carbohydrate1996ResiduesIons.ResidueEvent)
      (referent : Carbohydrate1996ResiduesIons.AnomericSymbolReferent)
  | retainedAnomericHydroxyCarbonLossUsesOneHydroxyYl
      (event : Carbohydrate1996ResiduesIons.ResidueEvent)
      (referent : Carbohydrate1996ResiduesIons.AnomericSymbolReferent)
  | retainedAnomericHydroxyAlphaBetaRefersToFreeValence
      (event : Carbohydrate1996ResiduesIons.ResidueEvent)
      (referent : Carbohydrate1996ResiduesIons.AnomericSymbolReferent)
  | differentCarbonHydrogenLossUsesDiylTriyl
  | sameCarbonMultipleHydrogenLossUsesYlidene
  | phosphaneTerminologyPreferred
  | radicalNamesFollowSubstituentNames
  | carbeneUsesYlidene
  | carbonHydrideLossCationUsesYlium
      (center : Carbohydrate1996ResiduesIons.ChargeCenter)
      (change : Carbohydrate1996ResiduesIons.ChargeChange)
      (suffix : Option String)
  | oxygenHydronationUsesLocantedOium
      (center : Carbohydrate1996ResiduesIons.ChargeCenter)
      (change : Carbohydrate1996ResiduesIons.ChargeChange)
      (suffix : Option String)
  | oxygenProtonLossAnionUsesLocantedOate
      (center : Carbohydrate1996ResiduesIons.ChargeCenter)
      (change : Carbohydrate1996ResiduesIons.ChargeChange)
      (suffix : Option String)
  | carbonProtonLossAnionUsesIde
      (center : Carbohydrate1996ResiduesIons.ChargeCenter)
      (change : Carbohydrate1996ResiduesIons.ChargeChange)
      (suffix : Option String)
  | radicalIonMayAddYlToIonName
  | unspecifiedRadicalIonMayUsePostposedClass
  | revisedRadicalIonAuthorityDelegated
  | printedExample (row : Carbohydrate1996ResiduesIons.PrintedExample)
      (data : Carbohydrate1996ResiduesIons.PrintedExampleData)
  deriving Repr

def sourceAssertion : Carbohydrate1996ResiduesIons.Provision → SourceAssertion
  | .glycosylResidueDropsAnomericHydroxyAndEToYl =>
      .glycosylResidueDropsAnomericHydroxyAndEToYl
  | .glycosylResiduesUsedForGlycosidesAndOligosaccharides =>
      .glycosylResiduesUsedForGlycosidesAndOligosaccharides
  | .glycosylAlsoUsedRadicofunctionally => .glycosylAlsoUsedRadicofunctionally
  | .carbohydrateSubstituentPrefixesAllowNoncarbohydrateParent =>
      .carbohydrateSubstituentPrefixesAllowNoncarbohydrateParent
  | .residueEndingsNCylNOylOrNyl => .residueEndingsNCylNOylOrNyl
  | .residueYlMeansLossOfHydrogenAtN => .residueYlMeansLossOfHydrogenAtN
  | .secondaryFreeValenceEquivalentToHydroxy => .secondaryFreeValenceEquivalentToHydroxy
  | .alditolResiduesUseSameEndings => .alditolResiduesUseSameEndings
  | .unlocantedYlMeansLossOfAnomericHydroxy =>
      .unlocantedYlMeansLossOfAnomericHydroxy .anomericHydroxyLoss
        (Carbohydrate1996ResiduesIons.anomericSymbolReferent .anomericHydroxyLoss)
  | .unlocantedYloxyMeansLossOfAnomericHydroxyHydrogen =>
      .unlocantedYloxyMeansLossOfAnomericHydroxyHydrogen .anomericHydroxyHydrogenLoss
        (Carbohydrate1996ResiduesIons.anomericSymbolReferent .anomericHydroxyHydrogenLoss)
  | .retainedAnomericHydroxyCarbonLossUsesOneHydroxyYl =>
      .retainedAnomericHydroxyCarbonLossUsesOneHydroxyYl
        .anomericCarbonHydrogenLossHydroxyRetained
        (Carbohydrate1996ResiduesIons.anomericSymbolReferent
          .anomericCarbonHydrogenLossHydroxyRetained)
  | .retainedAnomericHydroxyAlphaBetaRefersToFreeValence =>
      .retainedAnomericHydroxyAlphaBetaRefersToFreeValence
        .anomericCarbonHydrogenLossHydroxyRetained
        (Carbohydrate1996ResiduesIons.anomericSymbolReferent
          .anomericCarbonHydrogenLossHydroxyRetained)
  | .differentCarbonHydrogenLossUsesDiylTriyl => .differentCarbonHydrogenLossUsesDiylTriyl
  | .sameCarbonMultipleHydrogenLossUsesYlidene => .sameCarbonMultipleHydrogenLossUsesYlidene
  | .phosphaneTerminologyPreferred => .phosphaneTerminologyPreferred
  | .radicalNamesFollowSubstituentNames => .radicalNamesFollowSubstituentNames
  | .carbeneUsesYlidene => .carbeneUsesYlidene
  | .carbonHydrideLossCationUsesYlium =>
      .carbonHydrideLossCationUsesYlium .carbon .hydrideLoss
        (Carbohydrate1996ResiduesIons.ionSuffix .carbon .hydrideLoss)
  | .oxygenHydronationUsesLocantedOium =>
      .oxygenHydronationUsesLocantedOium .oxygen .hydronation
        (Carbohydrate1996ResiduesIons.ionSuffix .oxygen .hydronation)
  | .oxygenProtonLossAnionUsesLocantedOate =>
      .oxygenProtonLossAnionUsesLocantedOate .oxygen .protonLoss
        (Carbohydrate1996ResiduesIons.ionSuffix .oxygen .protonLoss)
  | .carbonProtonLossAnionUsesIde =>
      .carbonProtonLossAnionUsesIde .carbon .protonLoss
        (Carbohydrate1996ResiduesIons.ionSuffix .carbon .protonLoss)
  | .radicalIonMayAddYlToIonName => .radicalIonMayAddYlToIonName
  | .unspecifiedRadicalIonMayUsePostposedClass => .unspecifiedRadicalIonMayUsePostposedClass
  | .revisedRadicalIonAuthorityDelegated => .revisedRadicalIonAuthorityDelegated
  | .printedExample row => .printedExample row row.data

def SourceAssertion.provision : SourceAssertion → Carbohydrate1996ResiduesIons.Provision
  | .glycosylResidueDropsAnomericHydroxyAndEToYl =>
      .glycosylResidueDropsAnomericHydroxyAndEToYl
  | .glycosylResiduesUsedForGlycosidesAndOligosaccharides =>
      .glycosylResiduesUsedForGlycosidesAndOligosaccharides
  | .glycosylAlsoUsedRadicofunctionally => .glycosylAlsoUsedRadicofunctionally
  | .carbohydrateSubstituentPrefixesAllowNoncarbohydrateParent =>
      .carbohydrateSubstituentPrefixesAllowNoncarbohydrateParent
  | .residueEndingsNCylNOylOrNyl => .residueEndingsNCylNOylOrNyl
  | .residueYlMeansLossOfHydrogenAtN => .residueYlMeansLossOfHydrogenAtN
  | .secondaryFreeValenceEquivalentToHydroxy => .secondaryFreeValenceEquivalentToHydroxy
  | .alditolResiduesUseSameEndings => .alditolResiduesUseSameEndings
  | .unlocantedYlMeansLossOfAnomericHydroxy _ _ =>
      .unlocantedYlMeansLossOfAnomericHydroxy
  | .unlocantedYloxyMeansLossOfAnomericHydroxyHydrogen _ _ =>
      .unlocantedYloxyMeansLossOfAnomericHydroxyHydrogen
  | .retainedAnomericHydroxyCarbonLossUsesOneHydroxyYl _ _ =>
      .retainedAnomericHydroxyCarbonLossUsesOneHydroxyYl
  | .retainedAnomericHydroxyAlphaBetaRefersToFreeValence _ _ =>
      .retainedAnomericHydroxyAlphaBetaRefersToFreeValence
  | .differentCarbonHydrogenLossUsesDiylTriyl => .differentCarbonHydrogenLossUsesDiylTriyl
  | .sameCarbonMultipleHydrogenLossUsesYlidene => .sameCarbonMultipleHydrogenLossUsesYlidene
  | .phosphaneTerminologyPreferred => .phosphaneTerminologyPreferred
  | .radicalNamesFollowSubstituentNames => .radicalNamesFollowSubstituentNames
  | .carbeneUsesYlidene => .carbeneUsesYlidene
  | .carbonHydrideLossCationUsesYlium _ _ _ => .carbonHydrideLossCationUsesYlium
  | .oxygenHydronationUsesLocantedOium _ _ _ => .oxygenHydronationUsesLocantedOium
  | .oxygenProtonLossAnionUsesLocantedOate _ _ _ => .oxygenProtonLossAnionUsesLocantedOate
  | .carbonProtonLossAnionUsesIde _ _ _ => .carbonProtonLossAnionUsesIde
  | .radicalIonMayAddYlToIonName => .radicalIonMayAddYlToIonName
  | .unspecifiedRadicalIonMayUsePostposedClass => .unspecifiedRadicalIonMayUsePostposedClass
  | .revisedRadicalIonAuthorityDelegated => .revisedRadicalIonAuthorityDelegated
  | .printedExample row _ => .printedExample row

@[simp] theorem sourceAssertion_provision_exact
    (row : Carbohydrate1996ResiduesIons.Provision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

structure SourceMeaning where
  sourceKey : String
  semanticDomain : SemanticDomain
  assertion : SourceAssertion
  deriving Repr

def sourceMeaning (row : Carbohydrate1996ResiduesIons.Provision) : SourceMeaning :=
  ⟨row.sourceKey, semanticDomain row, sourceAssertion row⟩

@[simp] theorem sourceMeaning_key_exact (row : Carbohydrate1996ResiduesIons.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by rfl

@[simp] theorem sourceMeaning_domain_exact (row : Carbohydrate1996ResiduesIons.Provision) :
    (sourceMeaning row).semanticDomain = semanticDomain row := by rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def fullFamilyRows : List Carbohydrate1996ResiduesIons.Provision :=
  Carbohydrate1996ResiduesIons.Provision.all

def fullFamilyProvisions : List IUPACNormativeProvision :=
  fullFamilyRows.map IUPACNormativeProvision.carbohydrate1996ResiduesIons

def completionRows : List Carbohydrate1996ResiduesIons.Provision :=
  Carbohydrate1996ResiduesIons.Provision.base

def completionProvisions : List IUPACNormativeProvision :=
  completionRows.map IUPACNormativeProvision.carbohydrate1996ResiduesIons

def completionBatch : GlobalNonDescriptorSourceMeaningBatch completionProvisions :=
  totalMeaningBatch completionRows IUPACNormativeProvision.carbohydrate1996ResiduesIons
    sourceMeaning (by intro _row; rfl)

@[simp] theorem full_family_provisions_exact :
    fullFamilyProvisions = carbohydrate1996ResiduesIonsSemanticsSlice := by rfl

@[simp] theorem full_family_provision_count : fullFamilyProvisions.length = 60 := by
  simp [fullFamilyProvisions, fullFamilyRows]

@[simp] theorem completion_provision_count : completionProvisions.length = 24 := by
  simp [completionProvisions, completionRows, Carbohydrate1996ResiduesIons.Provision.base]

@[simp] theorem completion_entry_count : completionBatch.entries.length = 24 := by
  rw [completionBatch.entries_length, completion_provision_count]

private theorem completion_rows_then_indexed_exact :
    completionRows ++ GlobalNonDescriptorIndexedSourceData.carbohydrateResidueIonRows =
      fullFamilyRows := by
  simp [completionRows, fullFamilyRows,
    GlobalNonDescriptorIndexedSourceData.carbohydrateResidueIonRows,
    Carbohydrate1996ResiduesIons.Provision.all]

theorem completion_then_indexed_exact_source_order :
    completionProvisions ++
      GlobalNonDescriptorIndexedSourceData.carbohydrateResidueIonProvisions =
        carbohydrate1996ResiduesIonsSemanticsSlice := by
  rw [← full_family_provisions_exact]
  simp only [completionProvisions,
    GlobalNonDescriptorIndexedSourceData.carbohydrateResidueIonProvisions,
    fullFamilyProvisions, ← List.map_append]
  rw [completion_rows_then_indexed_exact]

theorem materialized_order_perm_source :
    (GlobalNonDescriptorIndexedSourceData.carbohydrateResidueIonProvisions ++
      completionProvisions).Perm carbohydrate1996ResiduesIonsSemanticsSlice := by
  calc
    (GlobalNonDescriptorIndexedSourceData.carbohydrateResidueIonProvisions ++
      completionProvisions).Perm
        (completionProvisions ++
          GlobalNonDescriptorIndexedSourceData.carbohydrateResidueIonProvisions) :=
      List.perm_append_comm
    _ = carbohydrate1996ResiduesIonsSemanticsSlice := completion_then_indexed_exact_source_order

theorem completion_disjoint_indexed :
    completionProvisions.Disjoint
      GlobalNonDescriptorIndexedSourceData.carbohydrateResidueIonProvisions := by
  apply List.disjoint_of_nodup_append
  rw [completion_then_indexed_exact_source_order]
  exact Carbohydrate1996ResiduesIons.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

theorem completion_provisions_nodup : completionProvisions.Nodup := by
  exact Carbohydrate1996ResiduesIons.Provision.all_nodup.of_append_left.map
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

end GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.full_family_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completion_then_indexed_exact_source_order
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.materialized_order_perm_source
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.completion_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.every_completion_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateResidueIonSourceMeaning.source_audit_still_open
