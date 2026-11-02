import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.remainingImageRows

def rows : List Carbohydrate1996ImageAudit.Provision := priorRemainingImageRows.take 59

def artifactOf : Carbohydrate1996ImageAudit.Provision →
    Carbohydrate1996ImageAudit.ImageArtifact
  | .imageArtifact artifact => artifact

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := rows.map artifactOf

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 59 := by simp [rows, priorRemainingImageRows]
@[simp] theorem artifact_count : artifacts.length = 59 := by simp [artifacts]
@[simp] theorem provision_count : provisions.length = 59 := by simp [provisions]

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 8 ["19.html"] ++ List.replicate 13 ["20.html"] ++
        List.replicate 8 ["21.html"] ++ List.replicate 16 ["22.html"] ++
          List.replicate 14 ["23.html"] := by
  decide

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

/-! ## Typed alditol and sugar-acid structures -/

inductive AcidFamily where
  | alditol | aldonic | ketoaldonic | uronic | aldaric
  deriving DecidableEq, Repr, Inhabited

inductive DerivativeKind where
  | alcohol | freeAcid | anion | salt | ester | amide | nitrile
  | lactone | lactam | acylHalide | halfEster | amicAcid | dilactone
  deriving DecidableEq, Repr, Inhabited

inductive RingKind where
  | furanose | pyranose
  deriving DecidableEq, Repr, Inhabited

inductive AbsoluteConfiguration where
  | R | S
  deriving DecidableEq, Repr, Inhabited

structure ConfigurationalGroup where
  prefixText : String
  locants : List Nat
  deriving DecidableEq, Repr, Inhabited

structure RingForm where
  kind : RingKind
  anomericCarbonLocant : Nat
  closureCarbonLocant : Nat
  deriving DecidableEq, Repr, Inhabited

structure HeterocycleClosure where
  carbonylCarbonLocant : Nat
  heteroatomCarbonLocant : Nat
  isNitrogen : Bool := false
  deriving DecidableEq, Repr, Inhabited

structure Modification where
  locants : List Nat
  name : String
  deriving DecidableEq, Repr, Inhabited

structure AbsoluteCenter where
  locant : Nat
  configuration : AbsoluteConfiguration
  deriving DecidableEq, Repr, Inhabited

structure AcidMeaning where
  family : AcidFamily
  primaryName : String
  alternativeNames : List String := []
  rejectedNames : List String := []
  chainLength : Nat
  derivative : DerivativeKind
  carbonylLocants : List Nat := []
  carboxylLocants : List Nat := []
  deoxyLocants : List Nat := []
  configurationGroups : List ConfigurationalGroup := []
  ringForm? : Option RingForm := none
  closures : List HeterocycleClosure := []
  unsaturationLowerLocants : List Nat := []
  modifications : List Modification := []
  isMeso : Bool := false
  absoluteCenters : List AbsoluteCenter := []
  equilibriumRole? : Option String := none
  deriving DecidableEq, Repr, Inhabited

def locantInChain (chainLength locant : Nat) : Bool :=
  decide (0 < locant ∧ locant ≤ chainLength)

def ConfigurationalGroup.wellFormed (chainLength : Nat)
    (group : ConfigurationalGroup) : Bool :=
  !group.prefixText.isEmpty && !group.locants.isEmpty && group.locants.Nodup &&
    group.locants.all (locantInChain chainLength)

def AcidMeaning.wellFormed (meaning : AcidMeaning) : Bool :=
  !meaning.primaryName.isEmpty && decide (1 < meaning.chainLength) &&
    meaning.carbonylLocants.Nodup &&
      meaning.carbonylLocants.all (locantInChain meaning.chainLength) &&
    meaning.carboxylLocants.Nodup &&
      meaning.carboxylLocants.all (locantInChain meaning.chainLength) &&
    meaning.deoxyLocants.Nodup && meaning.deoxyLocants.all (locantInChain meaning.chainLength) &&
    meaning.configurationGroups.all (ConfigurationalGroup.wellFormed meaning.chainLength) &&
    meaning.closures.all fun closure =>
      locantInChain meaning.chainLength closure.carbonylCarbonLocant &&
        locantInChain meaning.chainLength closure.heteroatomCarbonLocant &&
        decide (closure.carbonylCarbonLocant ≠ closure.heteroatomCarbonLocant) &&
    meaning.unsaturationLowerLocants.all fun locant =>
      locantInChain meaning.chainLength locant && decide (locant < meaning.chainLength) &&
    meaning.modifications.all fun modification =>
      !modification.name.isEmpty && !modification.locants.isEmpty &&
        modification.locants.Nodup &&
        modification.locants.all (locantInChain meaning.chainLength) &&
    meaning.absoluteCenters.all fun center => locantInChain meaning.chainLength center.locant &&
    (match meaning.ringForm? with
      | none => true
      | some ring =>
          locantInChain meaning.chainLength ring.anomericCarbonLocant &&
            locantInChain meaning.chainLength ring.closureCarbonLocant &&
            decide (ring.anomericCarbonLocant ≠ ring.closureCarbonLocant))

private def group (prefixText : String) (locants : List Nat) : ConfigurationalGroup :=
  ⟨prefixText, locants⟩

private def furanose (anomeric closure : Nat) : RingForm :=
  ⟨.furanose, anomeric, closure⟩

private def pyranose (anomeric closure : Nat) : RingForm :=
  ⟨.pyranose, anomeric, closure⟩

private def closure (carbonyl heteroatom : Nat) (isNitrogen : Bool := false) :
    HeterocycleClosure :=
  ⟨carbonyl, heteroatom, isNitrogen⟩

private def modAt (name : String) (locants : List Nat) : Modification := ⟨locants, name⟩

private def acid (family : AcidFamily) (primaryName : String) (chainLength : Nat)
    (derivative : DerivativeKind) (alternativeNames : List String := [])
    (rejectedNames : List String := []) (carbonylLocants : List Nat := [])
    (carboxylLocants : List Nat := []) (deoxyLocants : List Nat := [])
    (configurationGroups : List ConfigurationalGroup := [])
    (ringForm? : Option RingForm := none) (closures : List HeterocycleClosure := [])
    (unsaturationLowerLocants : List Nat := []) (modifications : List Modification := [])
    (isMeso : Bool := false) (absoluteCenters : List AbsoluteCenter := [])
    (equilibriumRole? : Option String := none) : AcidMeaning :=
  { family, primaryName, alternativeNames, rejectedNames, chainLength, derivative,
    carbonylLocants, carboxylLocants, deoxyLocants, configurationGroups, ringForm?, closures,
    unsaturationLowerLocants, modifications, isMeso, absoluteCenters, equilibriumRole? }

def alditolImageMeanings : List (List AcidMeaning) :=
  [ [acid .alditol "D-glycero-L-galacto-Heptitol" 7 .alcohol
      (rejectedNames := ["L-glycero-D-manno-Heptitol"])
      (configurationGroups := [group "D-glycero-L-galacto" [2, 3, 4, 5, 6]])]
  , [acid .alditol "D-erythro-L-galacto-Octitol" 8 .alcohol
      (rejectedNames := ["D-threo-L-gulo-Octitol"])
      (configurationGroups := [group "D-erythro-L-galacto" [2, 3, 4, 5, 6, 7]])]
  , [acid .alditol "D-Arabinitol" 5 .alcohol (alternativeNames := ["Ara-ol"])
      (rejectedNames := ["D-Lyxitol"]) (configurationGroups := [group "D-arabino" [2, 3, 4]])]
  , [acid .alditol "D-Glucitol" 6 .alcohol (alternativeNames := ["Glc-ol"])
      (rejectedNames := ["L-Gulitol", "sorbitol"])
      (configurationGroups := [group "D-gluco" [2, 3, 4, 5]])]
  , [acid .alditol "L-Fucitol" 6 .alcohol (alternativeNames := ["L-Fuc-ol", "1-Deoxy-D-galactitol"])
      (rejectedNames := ["6-Deoxy-L-galactitol"]) (deoxyLocants := [1])
      (configurationGroups := [group "L-fuco" [2, 3, 4, 5]])]
  , [acid .alditol "L-Rhamnitol" 6 .alcohol (alternativeNames := ["L-Rha-ol", "1-Deoxy-L-mannitol"])
      (deoxyLocants := [1]) (configurationGroups := [group "L-rhamno" [2, 3, 4, 5]])]
  , [acid .alditol "meso-D-glycero-L-ido-Heptitol" 7 .alcohol
      (configurationGroups := [group "D-glycero-L-ido" [2, 3, 4, 5, 6]]) (isMeso := true)]
  , [acid .alditol "5-O-Methyl-D-galactitol" 6 .alcohol
      (rejectedNames := ["2-O-Methyl-L-galactitol"])
      (configurationGroups := [group "D-galacto" [2, 3, 4, 5]])
      (modifications := [modAt "O-methyl" [5]])] ]

def aldonicImageMeanings : List (List AcidMeaning) :=
  [ [acid .aldonic "D-Gluconic acid" 6 .freeAcid (carboxylLocants := [1])
      (configurationGroups := [group "D-gluco" [2, 3, 4, 5]])]
  , [acid .aldonic "D-Gluconate" 6 .anion (carboxylLocants := [1])
      (configurationGroups := [group "D-gluco" [2, 3, 4, 5]])]
  , [acid .aldonic "2-Amino-2-deoxy-D-gluconic acid" 6 .freeAcid (carboxylLocants := [1])
      (deoxyLocants := [2]) (configurationGroups := [group "D-gluco" [2, 3, 4, 5]])
      (modifications := [modAt "amino" [2]])]
  , [acid .aldonic "Methyl D-gluconate" 6 .ester (carboxylLocants := [1])
      (configurationGroups := [group "D-gluco" [2, 3, 4, 5]])]
  , [acid .aldonic "Isopropyl 3,4-di-O-methyl-L-mannonate" 6 .ester
      (carboxylLocants := [1]) (configurationGroups := [group "L-manno" [2, 3, 4, 5]])
      (modifications := [modAt "O-methyl" [3, 4]])]
  , [acid .aldonic "N,N-Dimethyl-L-xylonamide" 5 .amide (carboxylLocants := [1])
      (configurationGroups := [group "L-xylo" [2, 3, 4]])
      (modifications := [modAt "N,N-dimethyl" [1]])]
  , [acid .aldonic "Methyl 3-deoxy-D-threo-pentonate" 5 .ester (carboxylLocants := [1])
      (deoxyLocants := [3]) (configurationGroups := [group "D-threo" [2, 4]])]
  , [acid .aldonic "Methyl tetra-O-acetyl-L-arabinonate" 5 .ester (carboxylLocants := [1])
      (configurationGroups := [group "L-arabino" [2, 3, 4]])
      (modifications := [modAt "O-acetyl" [2, 3, 4, 5]])]
  , [acid .aldonic "D-Glucono-1,4-lactone" 6 .lactone (carboxylLocants := [1])
      (rejectedNames := ["D-Gluconic acid gamma-lactone"])
      (configurationGroups := [group "D-gluco" [2, 3, 4, 5]]) (closures := [closure 1 4])]
  , [acid .aldonic "D-Glucono-1,5-lactone" 6 .lactone (carboxylLocants := [1])
      (rejectedNames := ["D-Gluconic acid delta-lactone"])
      (configurationGroups := [group "D-gluco" [2, 3, 4, 5]]) (closures := [closure 1 5])]
  , [acid .aldonic "3-Deoxy-D-ribo-hexono-1,5-lactone" 6 .lactone
      (carboxylLocants := [1]) (deoxyLocants := [3])
      (configurationGroups := [group "D-ribo" [2, 4, 5]]) (closures := [closure 1 5])]
  , [acid .aldonic "5-Amino-5-deoxy-D-mannono-1,5-lactam" 6 .lactam
      (carboxylLocants := [1]) (deoxyLocants := [5])
      (configurationGroups := [group "D-manno" [2, 3, 4, 5]])
      (closures := [closure 1 5 true]) (modifications := [modAt "amino" [5]])]
  , [acid .aldonic "Penta-O-acetyl-D-gluconoyl chloride" 6 .acylHalide
      (carboxylLocants := [1]) (configurationGroups := [group "D-gluco" [2, 3, 4, 5]])
      (modifications := [modAt "O-acetyl" [2, 3, 4, 5, 6], modAt "chloride" [1]])] ]

def ketoaldonicImageMeanings : List (List AcidMeaning) :=
  [ [acid .ketoaldonic "D-erythro-Pent-2-ulosonic acid" 5 .freeAcid
      (carbonylLocants := [2]) (carboxylLocants := [1])
      (configurationGroups := [group "D-erythro" [3, 4]])]
  , [acid .ketoaldonic "D-arabino-Hex-5-ulosonic acid" 6 .freeAcid
      (carbonylLocants := [5]) (carboxylLocants := [1])
      (configurationGroups := [group "D-arabino" [2, 3, 4]])]
  , [acid .ketoaldonic "alpha-D-arabino-Hex-2-ulopyranosonic acid" 6 .freeAcid
      (carbonylLocants := [2]) (carboxylLocants := [1])
      (configurationGroups := [group "D-arabino" [3, 4, 5]])
      (ringForm? := some (pyranose 2 6))]
  , [acid .ketoaldonic "3-Deoxy-alpha-D-manno-oct-2-ulopyranosonic acid" 8 .freeAcid
      (alternativeNames := ["Kdo form"]) (carbonylLocants := [2]) (carboxylLocants := [1])
      (deoxyLocants := [3]) (configurationGroups := [group "D-manno" [4, 5, 6, 7]])
      (ringForm? := some (pyranose 2 6))]
  , [acid .ketoaldonic "Ethyl (methyl alpha-D-arabino-hex-2-ulopyranosid)onate" 6 .ester
      (carbonylLocants := [2]) (carboxylLocants := [1])
      (configurationGroups := [group "D-arabino" [3, 4, 5]])
      (ringForm? := some (pyranose 2 6)) (modifications := [modAt "O-methyl" [2]])]
  , [acid .ketoaldonic "beta-D-arabino-Hex-2-ulopyranosono-1,5-lactone" 6 .lactone
      (carbonylLocants := [2]) (carboxylLocants := [1])
      (configurationGroups := [group "D-arabino" [3, 4, 5]])
      (ringForm? := some (pyranose 2 6)) (closures := [closure 1 5])]
  , [acid .ketoaldonic "Indol-3-yl D-xylo-hex-5-ulofuranosonate" 6 .ester
      (alternativeNames := ["isatan B"]) (carbonylLocants := [5]) (carboxylLocants := [1])
      (configurationGroups := [group "D-xylo" [2, 3, 4]])
      (ringForm? := some (furanose 5 2)) (modifications := [modAt "indol-3-yl ester" [1]])]
  , [acid .ketoaldonic "L-xylo-Hex-2-ulosono-1,4-lactone" 6 .lactone
      (carbonylLocants := [2]) (carboxylLocants := [1])
      (configurationGroups := [group "L-xylo" [3, 4, 5]]) (closures := [closure 1 4])
      (equilibriumRole? := some "L-ascorbic acid equilibrium isomer 1")
    , acid .ketoaldonic "L-threo-Hex-2-enono-1,4-lactone" 6 .lactone
      (carboxylLocants := [1]) (configurationGroups := [group "L-threo" [4, 5]])
      (closures := [closure 1 4]) (unsaturationLowerLocants := [2])
      (equilibriumRole? := some "L-ascorbic acid equilibrium isomer 2")
    , acid .ketoaldonic "L-lyxo-Hex-2-ulosono-1,4-lactone" 6 .lactone
      (carbonylLocants := [2]) (carboxylLocants := [1])
      (configurationGroups := [group "L-lyxo" [3, 4, 5]]) (closures := [closure 1 4])
      (equilibriumRole? := some "L-ascorbic acid equilibrium isomer 3") ] ]

def uronicImageMeanings : List (List AcidMeaning) :=
  [ [acid .uronic "D-Glucuronic acid" 6 .freeAcid (carbonylLocants := [1])
      (carboxylLocants := [6]) (configurationGroups := [group "D-gluco" [2, 3, 4, 5]])]
  , [acid .uronic "alpha-D-Mannopyranuronic acid" 6 .freeAcid (carbonylLocants := [1])
      (carboxylLocants := [6]) (configurationGroups := [group "D-manno" [2, 3, 4, 5]])
      (ringForm? := some (pyranose 1 5))]
  , [acid .uronic "Phenyl beta-D-glucopyranosiduronic acid" 6 .freeAcid
      (rejectedNames := ["phenyl beta-D-glucuronoside", "phenyl beta-D-glucuronide"])
      (carboxylLocants := [6]) (configurationGroups := [group "D-gluco" [2, 3, 4, 5]])
      (ringForm? := some (pyranose 1 5)) (modifications := [modAt "phenyl" [1]])]
  , [acid .uronic "Methyl alpha-L-idopyranosiduronic acid" 6 .freeAcid
      (carboxylLocants := [6]) (configurationGroups := [group "L-ido" [2, 3, 4, 5]])
      (ringForm? := some (pyranose 1 5)) (modifications := [modAt "O-methyl" [1]])]
  , [acid .uronic "Methyl 2,3,4-tri-O-acetyl-alpha-D-glucopyranosyluronate bromide" 6 .ester
      (carboxylLocants := [6]) (configurationGroups := [group "D-gluco" [2, 3, 4, 5]])
      (ringForm? := some (pyranose 1 5))
      (modifications := [modAt "O-acetyl" [2, 3, 4], modAt "bromide" [1]])]
  , [acid .uronic "Methyl alpha-L-glucofuranosidurononitrile" 6 .nitrile
      (carboxylLocants := [6]) (configurationGroups := [group "L-gluco" [2, 3, 4, 5]])
      (ringForm? := some (furanose 1 4)) (modifications := [modAt "O-methyl" [1]])]
  , [acid .uronic "Sodium (methyl alpha-L-glucofuranosid)uronate" 6 .salt
      (carboxylLocants := [6]) (configurationGroups := [group "L-gluco" [2, 3, 4, 5]])
      (ringForm? := some (furanose 1 4)) (modifications := [modAt "O-methyl" [1]])]
  , [acid .uronic "Ethyl 2,3,5-tri-O-benzoyl-alpha-D-mannofuranuronate" 6 .ester
      (carboxylLocants := [6]) (configurationGroups := [group "D-manno" [2, 3, 4, 5]])
      (ringForm? := some (furanose 1 4)) (modifications := [modAt "O-benzoyl" [2, 3, 5]])]
  , [acid .uronic "D-Glucurono-6,3-lactone" 6 .lactone (carbonylLocants := [1])
      (carboxylLocants := [6]) (configurationGroups := [group "D-gluco" [2, 3, 4, 5]])
      (closures := [closure 6 3])]
  , [acid .uronic "D-Glucofuranurono-6,3-lactone" 6 .lactone (carboxylLocants := [6])
      (configurationGroups := [group "D-gluco" [2, 3, 4, 5]])
      (ringForm? := some (furanose 1 4)) (closures := [closure 6 3])]
  , [acid .uronic "Methyl alpha-D-glucofuranosidurono-6,3-lactone" 6 .lactone
      (carboxylLocants := [6]) (configurationGroups := [group "D-gluco" [2, 3, 4, 5]])
      (ringForm? := some (furanose 1 4)) (closures := [closure 6 3])
      (modifications := [modAt "O-methyl" [1]])]
  , [acid .uronic "4-Deoxy-L-threo-hex-4-enopyranuronic acid" 6 .freeAcid
      (carboxylLocants := [6]) (deoxyLocants := [4])
      (configurationGroups := [group "L-threo" [2, 3]]) (ringForm? := some (pyranose 1 5))
      (unsaturationLowerLocants := [4])]
  , [acid .uronic "Methyl 4-deoxy-L-threo-hex-4-enopyranuronate" 6 .ester
      (carboxylLocants := [6]) (deoxyLocants := [4])
      (configurationGroups := [group "L-threo" [2, 3]]) (ringForm? := some (pyranose 1 5))
      (unsaturationLowerLocants := [4])]
  , [acid .uronic "Methyl 4-deoxy-alpha-L-threo-hex-4-enopyranosiduronic acid" 6 .freeAcid
      (carboxylLocants := [6]) (deoxyLocants := [4])
      (configurationGroups := [group "L-threo" [2, 3]]) (ringForm? := some (pyranose 1 5))
      (unsaturationLowerLocants := [4]) (modifications := [modAt "O-methyl" [1]])]
  , [acid .uronic "Methyl (phenyl 4-deoxy-beta-L-threo-hex-4-enopyranosid)uronate" 6 .ester
      (carboxylLocants := [6]) (deoxyLocants := [4])
      (configurationGroups := [group "L-threo" [2, 3]]) (ringForm? := some (pyranose 1 5))
      (unsaturationLowerLocants := [4]) (modifications := [modAt "phenyl" [1]])]
  , [acid .uronic "Methyl beta-D-galactopyranosiduronamide" 6 .amide
      (carboxylLocants := [6]) (configurationGroups := [group "D-galacto" [2, 3, 4, 5]])
      (ringForm? := some (pyranose 1 5)) (modifications := [modAt "O-methyl" [1]])] ]

def aldaricImageMeanings : List (List AcidMeaning) :=
  [ [acid .aldaric "L-Altraric acid" 6 .freeAcid (rejectedNames := ["L-Talaric acid"])
      (carboxylLocants := [1, 6]) (configurationGroups := [group "L-altro" [2, 3, 4, 5]])]
  , [acid .aldaric "D-Glucaric acid" 6 .freeAcid (rejectedNames := ["L-Gularic acid"])
      (carboxylLocants := [1, 6]) (configurationGroups := [group "D-gluco" [2, 3, 4, 5]])]
  , [acid .aldaric "L-glycero-D-galacto-Heptaric acid" 7 .freeAcid
      (rejectedNames := ["D-glycero-L-galacto-Heptaric acid"])
      (carboxylLocants := [1, 7])
      (configurationGroups := [group "L-glycero-D-galacto" [2, 3, 4, 5, 6]])]
  , [acid .aldaric "meso-Xylaric acid" 5 .freeAcid (carboxylLocants := [1, 5])
      (configurationGroups := [group "xylo" [2, 3, 4]]) (isMeso := true)]
  , [acid .aldaric "meso-Galactaric acid" 6 .freeAcid (carboxylLocants := [1, 6])
      (configurationGroups := [group "galacto" [2, 3, 4, 5]]) (isMeso := true)]
  , [acid .aldaric "4-O-Methyl-D-galactaric acid" 6 .freeAcid
      (rejectedNames := ["3-O-Methyl-L-galactaric acid"]) (carboxylLocants := [1, 6])
      (configurationGroups := [group "D-galacto" [2, 3, 4, 5]])
      (modifications := [modAt "O-methyl" [4]])]
  , [acid .aldaric "(2R,3R)-Tartaric acid" 4 .freeAcid
      (alternativeNames := ["(+)-Tartaric acid", "L-Threaric acid"])
      (carboxylLocants := [1, 4]) (absoluteCenters := [⟨2, .R⟩, ⟨3, .R⟩])]
  , [acid .aldaric "(2S,3S)-Tartaric acid" 4 .freeAcid
      (alternativeNames := ["(-)-Tartaric acid", "D-Threaric acid"])
      (carboxylLocants := [1, 4]) (absoluteCenters := [⟨2, .S⟩, ⟨3, .S⟩])]
  , [acid .aldaric "(2R,3S)-Tartaric acid" 4 .freeAcid
      (alternativeNames := ["meso-Tartaric acid", "Erythraric acid"])
      (carboxylLocants := [1, 4]) (isMeso := true)
      (absoluteCenters := [⟨2, .R⟩, ⟨3, .S⟩])]
  , [acid .aldaric "1-Methyl hydrogen D-galactarate" 6 .halfEster
      (carboxylLocants := [1, 6]) (configurationGroups := [group "D-galacto" [2, 3, 4, 5]])]
  , [acid .aldaric "6-Methyl hydrogen D-galactarate" 6 .halfEster
      (carboxylLocants := [1, 6]) (configurationGroups := [group "D-galacto" [2, 3, 4, 5]])]
  , [acid .aldaric "D-Glucar-1-amic acid" 6 .amicAcid (carboxylLocants := [1, 6])
      (configurationGroups := [group "D-gluco" [2, 3, 4, 5]])]
  , [acid .aldaric "Methyl D-glucar-6-amate" 6 .amicAcid (carboxylLocants := [1, 6])
      (configurationGroups := [group "D-gluco" [2, 3, 4, 5]])]
  , [acid .aldaric "D-Mannaro-1,4:6,3-dilactone" 6 .dilactone
      (carboxylLocants := [1, 6]) (configurationGroups := [group "D-manno" [2, 3, 4, 5]])
      (closures := [closure 1 4, closure 6 3])] ]

@[simp] theorem alditol_image_count : alditolImageMeanings.length = 8 := rfl
@[simp] theorem aldonic_image_count : aldonicImageMeanings.length = 13 := rfl
@[simp] theorem ketoaldonic_image_count : ketoaldonicImageMeanings.length = 8 := rfl
@[simp] theorem uronic_image_count : uronicImageMeanings.length = 16 := rfl
@[simp] theorem aldaric_image_count : aldaricImageMeanings.length = 14 := rfl

def acidImageMeanings : List (List AcidMeaning) :=
  alditolImageMeanings ++ aldonicImageMeanings ++ ketoaldonicImageMeanings ++
    uronicImageMeanings ++ aldaricImageMeanings

@[simp] theorem acid_image_meaning_count : acidImageMeanings.length = 59 := by
  simp [acidImageMeanings]

@[simp] theorem acid_structure_count : (acidImageMeanings.flatMap id).length = 61 := by decide

@[simp] theorem ascorbic_equilibrium_structure_count :
    (acidImageMeanings[28]?.map List.length) = some 3 := by rfl

private theorem alditol_meanings_well_formed :
    (alditolImageMeanings.flatMap id).all AcidMeaning.wellFormed = true := by decide

private theorem aldonic_meanings_well_formed :
    (aldonicImageMeanings.flatMap id).all AcidMeaning.wellFormed = true := by decide

private theorem ketoaldonic_meanings_well_formed :
    (ketoaldonicImageMeanings.flatMap id).all AcidMeaning.wellFormed = true := by decide

private theorem uronic_meanings_well_formed :
    (uronicImageMeanings.flatMap id).all AcidMeaning.wellFormed = true := by decide

private theorem aldaric_meanings_well_formed :
    (aldaricImageMeanings.flatMap id).all AcidMeaning.wellFormed = true := by decide

@[simp] theorem acid_meanings_well_formed :
    (acidImageMeanings.flatMap id).all AcidMeaning.wellFormed = true := by
  simp only [acidImageMeanings, List.flatMap_append, List.all_append]
  rw [alditol_meanings_well_formed, aldonic_meanings_well_formed,
    ketoaldonic_meanings_well_formed, uronic_meanings_well_formed,
    aldaric_meanings_well_formed]
  decide

structure SourceRule where
  alditolUsesItolEnding : Bool
  symmetricAlditolIsMeso : Bool
  substitutedMesoAlditolRequiresDL : Bool
  aldonicUsesOnicAcidEnding : Bool
  saltAndEsterUseOnate : Bool
  lactoneAndLactamRequireExactClosureLocants : Bool
  ketoaldonicNumberingStartsAtCarboxyl : Bool
  uronicPotentialAldehydeCarbonRemainsOne : Bool
  aldaricUsesAricAcidEnding : Bool
  tartaricAbsoluteDescriptorsPreferred : Bool
  deriving DecidableEq, Repr

def sourceRule : SourceRule where
  alditolUsesItolEnding := true
  symmetricAlditolIsMeso := true
  substitutedMesoAlditolRequiresDL := true
  aldonicUsesOnicAcidEnding := true
  saltAndEsterUseOnate := true
  lactoneAndLactamRequireExactClosureLocants := true
  ketoaldonicNumberingStartsAtCarboxyl := true
  uronicPotentialAldehydeCarbonRemainsOne := true
  aldaricUsesAricAcidEnding := true
  tartaricAbsoluteDescriptorsPreferred := true

/-! ## Total typed lookup and reviewed batch -/

def sourceMeaning? : String → Option (List AcidMeaning)
  | "2carb/2C1gif/191A.GIF" => alditolImageMeanings[0]?
  | "2carb/2C1gif/191B.GIF" => alditolImageMeanings[1]?
  | "2carb/2C1gif/191C.GIF" => alditolImageMeanings[2]?
  | "2carb/2C1gif/191D.GIF" => alditolImageMeanings[3]?
  | "2carb/2C1gif/191E.GIF" => alditolImageMeanings[4]?
  | "2carb/2C1gif/191F.GIF" => alditolImageMeanings[5]?
  | "2carb/2C1gif/192A.GIF" => alditolImageMeanings[6]?
  | "2carb/2C1gif/192B.GIF" => alditolImageMeanings[7]?
  | "2carb/2C2gif/201A.GIF" => aldonicImageMeanings[0]?
  | "2carb/2C2gif/201B.GIF" => aldonicImageMeanings[1]?
  | "2carb/2C2gif/201C.GIF" => aldonicImageMeanings[2]?
  | "2carb/2C2gif/202A.GIF" => aldonicImageMeanings[3]?
  | "2carb/2C2gif/202B.GIF" => aldonicImageMeanings[4]?
  | "2carb/2C2gif/202C.GIF" => aldonicImageMeanings[5]?
  | "2carb/2C2gif/202D.GIF" => aldonicImageMeanings[6]?
  | "2carb/2C2gif/202E.GIF" => aldonicImageMeanings[7]?
  | "2carb/2C2gif/202F.GIF" => aldonicImageMeanings[8]?
  | "2carb/2C2gif/202G.GIF" => aldonicImageMeanings[9]?
  | "2carb/2C2gif/202H.GIF" => aldonicImageMeanings[10]?
  | "2carb/2C2gif/202I.GIF" => aldonicImageMeanings[11]?
  | "2carb/2C2gif/202J.GIF" => aldonicImageMeanings[12]?
  | "2carb/2C2gif/211A.GIF" => ketoaldonicImageMeanings[0]?
  | "2carb/2C2gif/211B.GIF" => ketoaldonicImageMeanings[1]?
  | "2carb/2C2gif/211C.GIF" => ketoaldonicImageMeanings[2]?
  | "2carb/2C2gif/211D.GIF" => ketoaldonicImageMeanings[3]?
  | "2carb/2C2gif/212A.GIF" => ketoaldonicImageMeanings[4]?
  | "2carb/2C2gif/212B.GIF" => ketoaldonicImageMeanings[5]?
  | "2carb/2C2gif/212C.GIF" => ketoaldonicImageMeanings[6]?
  | "2carb/2C2gif/212D.GIF" => ketoaldonicImageMeanings[7]?
  | "2carb/2C2gif/222A.GIF" => uronicImageMeanings[0]?
  | "2carb/2C2gif/222B.GIF" => uronicImageMeanings[1]?
  | "2carb/2C2gif/222C.GIF" => uronicImageMeanings[2]?
  | "2carb/2C2gif/222D.GIF" => uronicImageMeanings[3]?
  | "2carb/2C2gif/222E.GIF" => uronicImageMeanings[4]?
  | "2carb/2C2gif/222F.GIF" => uronicImageMeanings[5]?
  | "2carb/2C2gif/222G.GIF" => uronicImageMeanings[6]?
  | "2carb/2C2gif/222H.GIF" => uronicImageMeanings[7]?
  | "2carb/2C2gif/222I.GIF" => uronicImageMeanings[8]?
  | "2carb/2C2gif/222J.GIF" => uronicImageMeanings[9]?
  | "2carb/2C2gif/222K.GIF" => uronicImageMeanings[10]?
  | "2carb/2C2gif/222L.GIF" => uronicImageMeanings[11]?
  | "2carb/2C2gif/222M.GIF" => uronicImageMeanings[12]?
  | "2carb/2C2gif/222N.GIF" => uronicImageMeanings[13]?
  | "2carb/2C2gif/222O.GIF" => uronicImageMeanings[14]?
  | "2carb/2C2gif/222P.GIF" => uronicImageMeanings[15]?
  | "2carb/2C2gif/231A.GIF" => aldaricImageMeanings[0]?
  | "2carb/2C2gif/231B.GIF" => aldaricImageMeanings[1]?
  | "2carb/2C2gif/231C.GIF" => aldaricImageMeanings[2]?
  | "2carb/2C2gif/232A.GIF" => aldaricImageMeanings[3]?
  | "2carb/2C2gif/232B.GIF" => aldaricImageMeanings[4]?
  | "2carb/2C2gif/232C.GIF" => aldaricImageMeanings[5]?
  | "2carb/2C2gif/233A.GIF" => aldaricImageMeanings[6]?
  | "2carb/2C2gif/233B.GIF" => aldaricImageMeanings[7]?
  | "2carb/2C2gif/233C.GIF" => aldaricImageMeanings[8]?
  | "2carb/2C2gif/234A.GIF" => aldaricImageMeanings[9]?
  | "2carb/2C2gif/234B.GIF" => aldaricImageMeanings[10]?
  | "2carb/2C2gif/234C.GIF" => aldaricImageMeanings[11]?
  | "2carb/2C2gif/234D.GIF" => aldaricImageMeanings[12]?
  | "2carb/2C2gif/234E.GIF" => aldaricImageMeanings[13]?
  | _ => none

def sourceMeaningPairs : List (Carbohydrate1996ImageAudit.ImageArtifact × List AcidMeaning) :=
  List.zip artifacts acidImageMeanings

def allArtifactsHaveSourceMeaning : Bool :=
  decide (sourceMeaningPairs.length = artifacts.length)

@[simp] theorem all_artifacts_have_source_meaning : allArtifactsHaveSourceMeaning = true := by
  simp [allArtifactsHaveSourceMeaning, sourceMeaningPairs]

structure VisionReviewedImageMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  sourcePages : List String
  sourceMeaning : Option (List AcidMeaning)
  reviewerKind : String
  reviewMethod : String
  reviewLimitations : String
  deriving DecidableEq, Repr

def VisionReviewedImageMeaning.complete (entry : VisionReviewedImageMeaning) : Bool :=
  !entry.sourcePages.isEmpty && entry.sourceMeaning.isSome &&
    !entry.reviewerKind.isEmpty && !entry.reviewMethod.isEmpty && !entry.reviewLimitations.isEmpty

def visionReviewedImageMeaning
    (row : Carbohydrate1996ImageAudit.Provision) : VisionReviewedImageMeaning :=
  match row with
  | .imageArtifact artifact =>
      { artifactData := artifact.data
        sourcePages := artifact.sourcePages
        sourceMeaning := sourceMeaning? artifact.data.relativePath
        reviewerKind := "visionAutomated"
        reviewMethod := "record-1b7e5add3283e6b5f54eaa2fa5deba2f"
        reviewLimitations := "automated-record-dea0f86743dc0740de4fb10ba17511a4" }

def visionReviewedImageMeaningOfPair
    (pair : Carbohydrate1996ImageAudit.ImageArtifact × List AcidMeaning) :
    VisionReviewedImageMeaning :=
  { artifactData := pair.1.data
    sourcePages := pair.1.sourcePages
    sourceMeaning := some pair.2
    reviewerKind := "visionAutomated"
    reviewMethod := "record-1b7e5add3283e6b5f54eaa2fa5deba2f"
    reviewLimitations := "automated-record-dea0f86743dc0740de4fb10ba17511a4" }

def visionReviewedMeanings : List VisionReviewedImageMeaning :=
  sourceMeaningPairs.map visionReviewedImageMeaningOfPair

@[simp] theorem vision_reviewed_count : visionReviewedMeanings.length = 59 := by
  simp [visionReviewedMeanings, sourceMeaningPairs]

set_option maxRecDepth 8192 in
@[simp] theorem vision_reviewed_complete :
    visionReviewedMeanings.all VisionReviewedImageMeaning.complete = true := by decide

def visionReviewedGraphLevelBatch :
    GlobalNonDescriptorSourceMeaningBatch provisions := by
  simpa [provisions] using
    GlobalNonDescriptorIndexedSourceData.totalMeaningBatch rows
      IUPACNormativeProvision.carbohydrate1996ImageArtifact
      visionReviewedImageMeaning (by intro _row; rfl)

@[simp] theorem vision_reviewed_entry_count :
    visionReviewedGraphLevelBatch.entries.length = 59 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact advance from the prior 1,782/426 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 59

@[simp] theorem remaining_image_count : remainingImageRows.length = 196 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 59 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1841 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 367 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.advancedMissingProvisions := by
  have imageEquality := congrArg
    (List.map IUPACNormativeProvision.carbohydrate1996ImageArtifact)
    rows_append_remaining_eq_prior
  let remainingProvisions :=
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact
  have swapPrefix :
      (provisions ++ sourceProvisions .blueBook2013Appendix3).Perm
        (sourceProvisions .blueBook2013Appendix3 ++ provisions) :=
    List.perm_append_comm
  have reordered :
      (provisions ++ advancedMissingProvisions).Perm
        (sourceProvisions .blueBook2013Appendix3 ++
          (provisions ++ remainingProvisions)) := by
    change (provisions ++
        (sourceProvisions .blueBook2013Appendix3 ++ remainingProvisions)).Perm
      (sourceProvisions .blueBook2013Appendix3 ++
        (provisions ++ remainingProvisions))
    simpa only [List.append_assoc] using swapPrefix.append_right remainingProvisions
  have selectedThenRemaining :
      provisions ++ remainingProvisions =
        priorRemainingImageRows.map
          IUPACNormativeProvision.carbohydrate1996ImageArtifact := by
    simpa [provisions, remainingProvisions, List.map_append] using imageEquality
  calc
    (provisions ++ advancedMissingProvisions).Perm _ := reordered
    _ = sourceProvisions .blueBook2013Appendix3 ++
        priorRemainingImageRows.map
          IUPACNormativeProvision.carbohydrate1996ImageArtifact := by
      rw [selectedThenRemaining]
    _ = GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1841 ∧
        advancedMissingProvisions.length = 367 ∧
          92 + 1841 + 367 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.acid_meanings_well_formed
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.all_artifacts_have_source_meaning
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
