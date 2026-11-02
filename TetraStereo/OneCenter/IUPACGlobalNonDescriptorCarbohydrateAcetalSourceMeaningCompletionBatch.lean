import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataBatch
import TetraStereo.KernelOnly

set_option autoImplicit false











namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateAcetalSourceMeaning

open GlobalNonDescriptorIndexedSourceData

inductive SemanticDomain where
  | dianhydride
  | cyclicAcetal
  | hemiacetal
  | acetal
  | printedItem
  deriving DecidableEq, Repr

def semanticDomain : Carbohydrate1996Acetals.Provision → SemanticDomain
  | .intermolecularDianhydrideDefinition
  | .mixedParentsPreferredParentFirst
  | .eachLinkUsesHydroxyLocantPair
  | .secondNamedParentLocantsPrimed
  | .bothPairsImmediatelyPrecedeDianhydride => .dianhydride
  | .cyclicAcetalUsesBivalentSubstituentPrefix
  | .repeatedKnownAcetalPairsTypographicallySeparated
  | .cyclicOrthoEstersMayUseCyclicAcetalNames
  | .newAcetalCarbonCenterUsesParenthesizedRSBeforeLocants => .cyclicAcetal
  | .hemiacetalTermsFollowAcetalMethod
  | .monothiohemiacetalIsomersUseOAndSPrefixes
  | .hemiacetalCarbonOneCanBecomeChiral
  | .knownNewHemiacetalCenterUsesRS => .hemiacetal
  | .acetalTermsPostposedAfterSaccharideAndGroups
  | .monothioacetalBondingUsesOAndSPrefixes
  | .acetalCarbonOneCanBecomeChiral
  | .knownNewAcetalCenterUsesRS => .acetal
  | .printedItem _ => .printedItem

def centerDescriptorInventory :
    List (Carbohydrate1996Acetals.NewlyCreatedCarbonCenter ×
      Carbohydrate1996Acetals.RequiredDescriptorFamily) :=
  [ (.cyclicAcetalCarbon,
      Carbohydrate1996Acetals.descriptorForNewCenter .cyclicAcetalCarbon)
  , (.hemiacetalCarbonOne,
      Carbohydrate1996Acetals.descriptorForNewCenter .hemiacetalCarbonOne)
  , (.acetalCarbonOne,
      Carbohydrate1996Acetals.descriptorForNewCenter .acetalCarbonOne) ]

inductive SourceAssertion where
  | intermolecularDianhydrideDefinition
  | mixedParentsPreferredParentFirst
  | eachLinkUsesHydroxyLocantPair
  | secondNamedParentLocantsPrimed
      (locants : Carbohydrate1996Acetals.DianhydrideLocants)
  | bothPairsImmediatelyPrecedeDianhydride
  | cyclicAcetalUsesBivalentSubstituentPrefix
  | repeatedKnownAcetalPairsTypographicallySeparated
  | cyclicOrthoEstersMayUseCyclicAcetalNames
  | newAcetalCarbonCenterUsesParenthesizedRSBeforeLocants
      (center : Carbohydrate1996Acetals.NewlyCreatedCarbonCenter)
      (descriptor : Carbohydrate1996Acetals.RequiredDescriptorFamily)
  | hemiacetalTermsFollowAcetalMethod
  | monothiohemiacetalIsomersUseOAndSPrefixes
  | hemiacetalCarbonOneCanBecomeChiral
  | knownNewHemiacetalCenterUsesRS
      (center : Carbohydrate1996Acetals.NewlyCreatedCarbonCenter)
      (descriptor : Carbohydrate1996Acetals.RequiredDescriptorFamily)
  | acetalTermsPostposedAfterSaccharideAndGroups
  | monothioacetalBondingUsesOAndSPrefixes
  | acetalCarbonOneCanBecomeChiral
  | knownNewAcetalCenterUsesRS
      (center : Carbohydrate1996Acetals.NewlyCreatedCarbonCenter)
      (descriptor : Carbohydrate1996Acetals.RequiredDescriptorFamily)
  | printedItem (row : Carbohydrate1996Acetals.PrintedItem)
      (data : Carbohydrate1996Acetals.PrintedItemData)
  deriving Repr

def sourceAssertion : Carbohydrate1996Acetals.Provision → SourceAssertion
  | .intermolecularDianhydrideDefinition => .intermolecularDianhydrideDefinition
  | .mixedParentsPreferredParentFirst => .mixedParentsPreferredParentFirst
  | .eachLinkUsesHydroxyLocantPair => .eachLinkUsesHydroxyLocantPair
  | .secondNamedParentLocantsPrimed =>
      .secondNamedParentLocantsPrimed Carbohydrate1996Acetals.canonicalDianhydrideLocants
  | .bothPairsImmediatelyPrecedeDianhydride => .bothPairsImmediatelyPrecedeDianhydride
  | .cyclicAcetalUsesBivalentSubstituentPrefix => .cyclicAcetalUsesBivalentSubstituentPrefix
  | .repeatedKnownAcetalPairsTypographicallySeparated =>
      .repeatedKnownAcetalPairsTypographicallySeparated
  | .cyclicOrthoEstersMayUseCyclicAcetalNames => .cyclicOrthoEstersMayUseCyclicAcetalNames
  | .newAcetalCarbonCenterUsesParenthesizedRSBeforeLocants =>
      .newAcetalCarbonCenterUsesParenthesizedRSBeforeLocants .cyclicAcetalCarbon
        (Carbohydrate1996Acetals.descriptorForNewCenter .cyclicAcetalCarbon)
  | .hemiacetalTermsFollowAcetalMethod => .hemiacetalTermsFollowAcetalMethod
  | .monothiohemiacetalIsomersUseOAndSPrefixes => .monothiohemiacetalIsomersUseOAndSPrefixes
  | .hemiacetalCarbonOneCanBecomeChiral => .hemiacetalCarbonOneCanBecomeChiral
  | .knownNewHemiacetalCenterUsesRS =>
      .knownNewHemiacetalCenterUsesRS .hemiacetalCarbonOne
        (Carbohydrate1996Acetals.descriptorForNewCenter .hemiacetalCarbonOne)
  | .acetalTermsPostposedAfterSaccharideAndGroups => .acetalTermsPostposedAfterSaccharideAndGroups
  | .monothioacetalBondingUsesOAndSPrefixes => .monothioacetalBondingUsesOAndSPrefixes
  | .acetalCarbonOneCanBecomeChiral => .acetalCarbonOneCanBecomeChiral
  | .knownNewAcetalCenterUsesRS =>
      .knownNewAcetalCenterUsesRS .acetalCarbonOne
        (Carbohydrate1996Acetals.descriptorForNewCenter .acetalCarbonOne)
  | .printedItem row => .printedItem row row.data

def SourceAssertion.provision : SourceAssertion → Carbohydrate1996Acetals.Provision
  | .intermolecularDianhydrideDefinition => .intermolecularDianhydrideDefinition
  | .mixedParentsPreferredParentFirst => .mixedParentsPreferredParentFirst
  | .eachLinkUsesHydroxyLocantPair => .eachLinkUsesHydroxyLocantPair
  | .secondNamedParentLocantsPrimed _ => .secondNamedParentLocantsPrimed
  | .bothPairsImmediatelyPrecedeDianhydride => .bothPairsImmediatelyPrecedeDianhydride
  | .cyclicAcetalUsesBivalentSubstituentPrefix => .cyclicAcetalUsesBivalentSubstituentPrefix
  | .repeatedKnownAcetalPairsTypographicallySeparated =>
      .repeatedKnownAcetalPairsTypographicallySeparated
  | .cyclicOrthoEstersMayUseCyclicAcetalNames => .cyclicOrthoEstersMayUseCyclicAcetalNames
  | .newAcetalCarbonCenterUsesParenthesizedRSBeforeLocants _ _ =>
      .newAcetalCarbonCenterUsesParenthesizedRSBeforeLocants
  | .hemiacetalTermsFollowAcetalMethod => .hemiacetalTermsFollowAcetalMethod
  | .monothiohemiacetalIsomersUseOAndSPrefixes => .monothiohemiacetalIsomersUseOAndSPrefixes
  | .hemiacetalCarbonOneCanBecomeChiral => .hemiacetalCarbonOneCanBecomeChiral
  | .knownNewHemiacetalCenterUsesRS _ _ => .knownNewHemiacetalCenterUsesRS
  | .acetalTermsPostposedAfterSaccharideAndGroups => .acetalTermsPostposedAfterSaccharideAndGroups
  | .monothioacetalBondingUsesOAndSPrefixes => .monothioacetalBondingUsesOAndSPrefixes
  | .acetalCarbonOneCanBecomeChiral => .acetalCarbonOneCanBecomeChiral
  | .knownNewAcetalCenterUsesRS _ _ => .knownNewAcetalCenterUsesRS
  | .printedItem row _ => .printedItem row

@[simp] theorem sourceAssertion_provision_exact (row : Carbohydrate1996Acetals.Provision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

structure SourceMeaning where
  sourceKey : String
  semanticDomain : SemanticDomain
  assertion : SourceAssertion
  deriving Repr

def sourceMeaning (row : Carbohydrate1996Acetals.Provision) : SourceMeaning :=
  ⟨row.sourceKey, semanticDomain row, sourceAssertion row⟩

@[simp] theorem sourceMeaning_key_exact (row : Carbohydrate1996Acetals.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by rfl

@[simp] theorem sourceMeaning_domain_exact (row : Carbohydrate1996Acetals.Provision) :
    (sourceMeaning row).semanticDomain = semanticDomain row := by rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def fullFamilyRows : List Carbohydrate1996Acetals.Provision :=
  Carbohydrate1996Acetals.Provision.all

def fullFamilyProvisions : List IUPACNormativeProvision :=
  fullFamilyRows.map IUPACNormativeProvision.carbohydrate1996Acetals

def completionRows : List Carbohydrate1996Acetals.Provision :=
  Carbohydrate1996Acetals.Provision.base

def completionProvisions : List IUPACNormativeProvision :=
  completionRows.map IUPACNormativeProvision.carbohydrate1996Acetals

def completionBatch : GlobalNonDescriptorSourceMeaningBatch completionProvisions :=
  totalMeaningBatch completionRows IUPACNormativeProvision.carbohydrate1996Acetals
    sourceMeaning (by intro _row; rfl)

@[simp] theorem full_family_provisions_exact :
    fullFamilyProvisions = carbohydrate1996AcetalsSemanticsSlice := by rfl

@[simp] theorem full_family_provision_count : fullFamilyProvisions.length = 38 := by
  simp [fullFamilyProvisions, fullFamilyRows]

@[simp] theorem completion_provision_count : completionProvisions.length = 17 := by
  simp [completionProvisions, completionRows, Carbohydrate1996Acetals.Provision.base]

@[simp] theorem completion_entry_count : completionBatch.entries.length = 17 := by
  rw [completionBatch.entries_length, completion_provision_count]

private theorem completion_rows_then_indexed_exact :
    completionRows ++ GlobalNonDescriptorIndexedSourceData.carbohydrateAcetalRows =
      fullFamilyRows := by
  simp [completionRows, fullFamilyRows,
    GlobalNonDescriptorIndexedSourceData.carbohydrateAcetalRows,
    Carbohydrate1996Acetals.Provision.all]

theorem completion_then_indexed_exact_source_order :
    completionProvisions ++ GlobalNonDescriptorIndexedSourceData.carbohydrateAcetalProvisions =
      carbohydrate1996AcetalsSemanticsSlice := by
  rw [← full_family_provisions_exact]
  simp only [completionProvisions,
    GlobalNonDescriptorIndexedSourceData.carbohydrateAcetalProvisions,
    fullFamilyProvisions, ← List.map_append]
  rw [completion_rows_then_indexed_exact]

theorem materialized_order_perm_source :
    (GlobalNonDescriptorIndexedSourceData.carbohydrateAcetalProvisions ++
      completionProvisions).Perm carbohydrate1996AcetalsSemanticsSlice := by
  calc
    (GlobalNonDescriptorIndexedSourceData.carbohydrateAcetalProvisions ++
      completionProvisions).Perm
        (completionProvisions ++
          GlobalNonDescriptorIndexedSourceData.carbohydrateAcetalProvisions) :=
      List.perm_append_comm
    _ = carbohydrate1996AcetalsSemanticsSlice := completion_then_indexed_exact_source_order

theorem completion_disjoint_indexed :
    completionProvisions.Disjoint
      GlobalNonDescriptorIndexedSourceData.carbohydrateAcetalProvisions := by
  apply List.disjoint_of_nodup_append
  rw [completion_then_indexed_exact_source_order]
  exact Carbohydrate1996Acetals.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

theorem completion_provisions_nodup : completionProvisions.Nodup := by
  exact Carbohydrate1996Acetals.Provision.all_nodup.of_append_left.map
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

end GlobalNonDescriptorCarbohydrateAcetalSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.full_family_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completion_then_indexed_exact_source_order
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.materialized_order_perm_source
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.completion_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.every_completion_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAcetalSourceMeaning.source_audit_still_open
