import TetraStereo.OneCenter.CarbohydrateHeteroSubstitutionAnhydrideSemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent carbohydrate intermolecular-anhydride and acetal semantics

This module audits 2-Carb-27 through 2-Carb-30.  It covers primed locants for mixed
intermolecular anhydrides and the requirement to assign newly created acetal/hemiacetal carbon
centres with CIP R/S.
-/

namespace Carbohydrate1996Acetals

inductive PrintedItem where
  | fructoseDianhydride
  | fructoseSorboseDianhydride
  | galacturonicRhamnoseDianhydride
  | methyleneXylitol
  | isopropylideneGlucofuranose
  | diisopropylideneMannitol
  | rBenzylideneGlucoside
  | srDibenzylideneAlloside
  | sChloroMethoxyMethyleneMannose
  | rMethylOrthoacetate
  | hemiacetalTemplate
  | ethylHemiacetal
  | ethylDithiohemiacetal
  | oEthylMonothiohemiacetal
  | sEthylMonothiohemiacetal
  | acetalTemplate
  | glucoseDiethylAcetal
  | fructoseDiethylKetal
  | propaneDiylDithioacetal
  | ethylMethylMonothioacetal
  | dimethylMonothioacetal
  deriving DecidableEq, Repr

namespace PrintedItem

def all : List PrintedItem :=
  [ .fructoseDianhydride, .fructoseSorboseDianhydride
  , .galacturonicRhamnoseDianhydride, .methyleneXylitol
  , .isopropylideneGlucofuranose, .diisopropylideneMannitol
  , .rBenzylideneGlucoside, .srDibenzylideneAlloside
  , .sChloroMethoxyMethyleneMannose, .rMethylOrthoacetate
  , .hemiacetalTemplate, .ethylHemiacetal, .ethylDithiohemiacetal
  , .oEthylMonothiohemiacetal, .sEthylMonothiohemiacetal
  , .acetalTemplate, .glucoseDiethylAcetal, .fructoseDiethylKetal
  , .propaneDiylDithioacetal, .ethylMethylMonothioacetal
  , .dimethylMonothioacetal
  ]

@[simp] theorem mem_all (item : PrintedItem) : item ∈ all := by
  cases item <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 21 := by decide

end PrintedItem

structure PrintedItemData where
  sourceKey : String
  printedText : String
  deriving DecidableEq, Repr

def PrintedItem.data : PrintedItem → PrintedItemData
  | .fructoseDianhydride => ⟨"2-Carb-27/27A", "alpha-D-Fructopyranose beta-D-fructopyranose 1,2':1',2-dianhydride"⟩
  | .fructoseSorboseDianhydride => ⟨"2-Carb-27/27B", "alpha-D-Fructopyranose alpha-D-sorbopyranose 1,2':1',2-dianhydride"⟩
  | .galacturonicRhamnoseDianhydride => ⟨"2-Carb-27/27C", "(alpha-D-Galactopyranuronic acid) beta-L-rhamnopyranose 1,2':1',2-dianhydride"⟩
  | .methyleneXylitol => ⟨"2-Carb-28/28A", "2,4-O-Methylenexylitol"⟩
  | .isopropylideneGlucofuranose => ⟨"2-Carb-28/28B", "1,2-O-Isopropylidene-alpha-D-glucofuranose"⟩
  | .diisopropylideneMannitol => ⟨"2-Carb-28/28C", "1,2:5,6-Di-O-isopropylidene-D-mannitol"⟩
  | .rBenzylideneGlucoside => ⟨"2-Carb-28/28D", "Methyl (R)-4,6-O-benzylidene-alpha-D-glucopyranoside"⟩
  | .srDibenzylideneAlloside => ⟨"2-Carb-28/28E", "Methyl (S)-2,3:(R)-4,6-di-O-benzylidene-alpha-D-allopyranoside"⟩
  | .sChloroMethoxyMethyleneMannose => ⟨"2-Carb-28/28F", "3,4,6-Tri-O-benzoyl-[(S)-1,2-O-chloro(methoxy)methylene]-beta-D-mannopyranose"⟩
  | .rMethylOrthoacetate => ⟨"2-Carb-28/28G", "3,4,6-Tri-O-acetyl-alpha-D-glucopyranose (R)-1,2-(methyl orthoacetate); methoxyethylidene alternative"⟩
  | .hemiacetalTemplate => ⟨"2-Carb-29/29A", "hemiacetal/monothiohemiacetal/dithiohemiacetal structural template"⟩
  | .ethylHemiacetal => ⟨"2-Carb-29/29B", "(1S)-Penta-O-benzoyl-D-glucose ethyl hemiacetal"⟩
  | .ethylDithiohemiacetal => ⟨"2-Carb-29/29C", "(1S)-Penta-O-benzoyl-D-glucose ethyl dithiohemiacetal"⟩
  | .oEthylMonothiohemiacetal => ⟨"2-Carb-29/29D", "(1R)-Penta-O-benzoyl-D-glucose O-ethyl monothiohemiacetal"⟩
  | .sEthylMonothiohemiacetal => ⟨"2-Carb-29/29E", "(1S)-Penta-O-benzoyl-D-glucose S-ethyl monothiohemiacetal"⟩
  | .acetalTemplate => ⟨"2-Carb-30/30A", "acetal/monothioacetal/dithioacetal structural template"⟩
  | .glucoseDiethylAcetal => ⟨"2-Carb-30/30B", "D-Glucose diethyl acetal"⟩
  | .fructoseDiethylKetal => ⟨"2-Carb-30/30C", "D-Fructose diethyl ketal"⟩
  | .propaneDiylDithioacetal => ⟨"2-Carb-30/30D", "D-Glucose propane-1,3-diyl dithioacetal"⟩
  | .ethylMethylMonothioacetal => ⟨"2-Carb-30/30E", "(1S)-D-Glucose S-ethyl O-methyl monothioacetal"⟩
  | .dimethylMonothioacetal => ⟨"2-Carb-30/30F", "(1R)-Penta-O-acetyl-D-glucose dimethyl monothioacetal"⟩

theorem printed_item_keys_are_pairwise_distinct :
    (PrintedItem.all.map fun item => item.data.sourceKey).Nodup := by
  decide

inductive Provision where
  | intermolecularDianhydrideDefinition
  | mixedParentsPreferredParentFirst
  | eachLinkUsesHydroxyLocantPair
  | secondNamedParentLocantsPrimed
  | bothPairsImmediatelyPrecedeDianhydride
  | cyclicAcetalUsesBivalentSubstituentPrefix
  | repeatedKnownAcetalPairsTypographicallySeparated
  | cyclicOrthoEstersMayUseCyclicAcetalNames
  | newAcetalCarbonCenterUsesParenthesizedRSBeforeLocants
  | hemiacetalTermsFollowAcetalMethod
  | monothiohemiacetalIsomersUseOAndSPrefixes
  | hemiacetalCarbonOneCanBecomeChiral
  | knownNewHemiacetalCenterUsesRS
  | acetalTermsPostposedAfterSaccharideAndGroups
  | monothioacetalBondingUsesOAndSPrefixes
  | acetalCarbonOneCanBecomeChiral
  | knownNewAcetalCenterUsesRS
  | printedItem (item : PrintedItem)
  deriving DecidableEq, Repr

namespace Provision

def base : List Provision :=
  [ .intermolecularDianhydrideDefinition, .mixedParentsPreferredParentFirst
  , .eachLinkUsesHydroxyLocantPair, .secondNamedParentLocantsPrimed
  , .bothPairsImmediatelyPrecedeDianhydride, .cyclicAcetalUsesBivalentSubstituentPrefix
  , .repeatedKnownAcetalPairsTypographicallySeparated
  , .cyclicOrthoEstersMayUseCyclicAcetalNames
  , .newAcetalCarbonCenterUsesParenthesizedRSBeforeLocants
  , .hemiacetalTermsFollowAcetalMethod, .monothiohemiacetalIsomersUseOAndSPrefixes
  , .hemiacetalCarbonOneCanBecomeChiral, .knownNewHemiacetalCenterUsesRS
  , .acetalTermsPostposedAfterSaccharideAndGroups
  , .monothioacetalBondingUsesOAndSPrefixes, .acetalCarbonOneCanBecomeChiral
  , .knownNewAcetalCenterUsesRS
  ]

def all : List Provision := base ++ PrintedItem.all.map Provision.printedItem

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision with
  | printedItem item =>
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := Provision.printedItem) item.mem_all
  | _ => simp [all, base]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 38 := by decide

end Provision

def Provision.sourceKey : Provision → String
  | .intermolecularDianhydrideDefinition | .mixedParentsPreferredParentFirst
  | .eachLinkUsesHydroxyLocantPair | .secondNamedParentLocantsPrimed
  | .bothPairsImmediatelyPrecedeDianhydride => "2-Carb-27"
  | .cyclicAcetalUsesBivalentSubstituentPrefix
  | .repeatedKnownAcetalPairsTypographicallySeparated
  | .cyclicOrthoEstersMayUseCyclicAcetalNames
  | .newAcetalCarbonCenterUsesParenthesizedRSBeforeLocants => "2-Carb-28"
  | .hemiacetalTermsFollowAcetalMethod | .monothiohemiacetalIsomersUseOAndSPrefixes
  | .hemiacetalCarbonOneCanBecomeChiral | .knownNewHemiacetalCenterUsesRS => "2-Carb-29"
  | .acetalTermsPostposedAfterSaccharideAndGroups
  | .monothioacetalBondingUsesOAndSPrefixes | .acetalCarbonOneCanBecomeChiral
  | .knownNewAcetalCenterUsesRS => "2-Carb-30"
  | .printedItem item => item.data.sourceKey

inductive NewlyCreatedCarbonCenter where
  | cyclicAcetalCarbon
  | hemiacetalCarbonOne
  | acetalCarbonOne
  deriving DecidableEq, Repr

inductive RequiredDescriptorFamily where
  | CIPRS
  deriving DecidableEq, Repr

def descriptorForNewCenter (_ : NewlyCreatedCarbonCenter) : RequiredDescriptorFamily := .CIPRS

@[simp] theorem every_new_acetal_family_center_routes_to_CIP_RS
    (center : NewlyCreatedCarbonCenter) : descriptorForNewCenter center = .CIPRS := by
  cases center <;> rfl

structure DianhydrideLocants where
  firstLink : Nat × Nat
  secondLink : Nat × Nat
  secondParentIsPrimed : Bool
  deriving DecidableEq, Repr

def canonicalDianhydrideLocants : DianhydrideLocants := ⟨(1, 2), (1, 2), true⟩

@[simp] theorem mixed_dianhydride_second_parent_is_primed :
    canonicalDianhydrideLocants.secondParentIsPrimed = true := by rfl

end Carbohydrate1996Acetals

end TetraStereo.OneCenter
