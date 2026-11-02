import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataBatch
import TetraStereo.KernelOnly

set_option autoImplicit false











namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning

open GlobalNonDescriptorIndexedSourceData

inductive SemanticDomain where
  | aldoseParent
  | dialdoseParent
  | ketoseParent
  | diketoseParent
  | ketoaldoseParent
  | biochemicalParent
  | printedExample
  deriving DecidableEq, Repr

def semanticDomain : Carbohydrate1996NamedParents.Provision → SemanticDomain
  | .aldoseTrivialNamesThreeToSix | .aldoseTrivialNamesGroundPrefixes
  | .aldoseSystematicStemInventory | .aldoseC1CarbonylNumbering
  | .systematicNameStemPlusPrefixes | .configurationalPrefixLowerCase
  | .configurationalPrefixItalicized | .everyPrefixQualifiedDL | .chartIShowsDStructures
  | .trivialParentNamesPreferred | .trivialDerivativeNamesPreferredWhenCentersUnmodified
  | .overFourCentersUseMultiplePrefixes | .groupsAssignedFourFromC1 | .farthestGroupCitedFirst
  | .nonchiralCentersIgnored | .parentAldosesNeedNoSeparatedSequenceRule
  | .systematicNamesMostlyHigherAldoses | .configurationalPrefixesAlsoApplyBeyondAldoses
  | .cyclicAldoseAnomerRoutesToTwoCarbSix | .aldoseChart _ => .aldoseParent
  | .dialdoseReplacesOseWithOdialdose | .dialdoseUsesConfigurationalPrefix
  | .dialdoseParentChoiceUsesTwoCarbTwo | .dialdoseMesoOptionalWhenStructureDefined
  | .cyclicDialdoseClosureLocantsRequired | .dialdoseClosureOrderAnomericThenOxygenBearing
  | .multipleRingDesignatorsAlphabetical => .dialdoseParent
  | .ketoseClassifiedByPotentialCarbonylPosition
  | .ketoseLocantTwoOmittableWhenUnambiguous
  | .chartIVCoversThreeToSixCarbonTwoKetoses | .obsoleteLTrivialKetoseNamesAreRedundant
  | .obsoleteLTrivialKetoseNamesNotForDerivatives
  | .sedoheptuloseAcceptedForDAltroHeptTwoUlose | .ketoseSystematicNameStemPlusPrefix
  | .ketoseStemReplacesOseWithUlose | .carbonylLocantPrecedesUlose
  | .ketoseChainGivesCarbonylLowestLocant | .oddCentralKetoseUsesParentChoiceRule
  | .casKetoseLocantPlacementDiffers | .twoKetosePrefixesFollowAldoseRules
  | .highKetoseCarbonylIgnoredForPrefixes | .highKetoseNonchiralCentersIgnored
  | .ketoseChart _ => .ketoseParent
  | .diketoseReplacesTerminalSeWithDiulose | .diketoseCarbonylLocantsLowest
  | .diketoseCarbonylLocantsBeforeEnding | .diketoseUsesConfigurationalPrefix
  | .diketoseChoiceUsesTwoCarbTwo | .cyclicDiketoseMayNeedClosureLocants
  | .cyclicDiketoseCarbonylClosureLocantFirst | .dividedDiketoseCentersUseOneSequence =>
      .diketoseParent
  | .ketoaldoseNamedAnalogouslyToDiketose | .ketoaldoseUsesUloseInsteadTerminalE
  | .ketoaldoseAldehydeCarbonIsOne | .ketoaldoseAldehydeLocantOmitted
  | .ketoaldoseKetoneLocantInfixUnlessTwo | .sourceRetainsKetoneLocantTwoForClarity
  | .cyclicKetoaldoseMayNeedClosureLocants | .cyclicKetoaldoseCarbonylClosureLocantFirst
  | .ringSizeDesignatorDependsOnClosingCarbonyl => .ketoaldoseParent
  | .biochemicalDehydroNamesWidespread | .dehydroNamesCanBeStereochemicallyRedundant
  | .dehydroNamesNotForDerivatives | .enzymeNamesUseSubstrateParentAndPriorityProduct =>
      .biochemicalParent
  | .workedExample _ => .printedExample

def aldoseStemInventory : List (Nat × Option String) :=
  (List.range 8).map fun offset =>
    let carbonCount := offset + 3
    (carbonCount, Carbohydrate1996NamedParents.aldoseStem carbonCount)

def fiveAndNineCenterGroupInventory : List (Nat × List Nat) :=
  [ (5, Carbohydrate1996NamedParents.configurationGroupSizesFromC1 5)
  , (9, Carbohydrate1996NamedParents.configurationGroupSizesFromC1 9) ]

def fiveAndNineCenterCitationInventory : List (Nat × List Nat) :=
  [ (5, Carbohydrate1996NamedParents.configurationPrefixCitationGroupSizes 5)
  , (9, Carbohydrate1996NamedParents.configurationPrefixCitationGroupSizes 9) ]

def configurationSideExample : List (Option Carbohydrate1996NamedParents.FischerSide) :=
  [some .left, none, some .right, none, some .left]

def ringDesignatorOrderInventory :
    List ((Carbohydrate1996NamedParents.RingSizeDesignator ×
      Carbohydrate1996NamedParents.RingSizeDesignator) ×
        List Carbohydrate1996NamedParents.RingSizeDesignator) :=
  [ ((.furanose, .pyranose),
      Carbohydrate1996NamedParents.orderRingDesignators .furanose .pyranose)
  , ((.pyranose, .furanose),
      Carbohydrate1996NamedParents.orderRingDesignators .pyranose .furanose) ]

def ketoseClassInventory : List (Nat × String) :=
  [ (2, Carbohydrate1996NamedParents.ketoseClass 2)
  , (3, Carbohydrate1996NamedParents.ketoseClass 3)
  , (4, Carbohydrate1996NamedParents.ketoseClass 4) ]

def ketoseLocantOmissionInventory : List ((Nat × Bool) × Bool) :=
  [ ((2, true), Carbohydrate1996NamedParents.ketoseCarbonylLocantMayBeOmitted 2 true)
  , ((2, false), Carbohydrate1996NamedParents.ketoseCarbonylLocantMayBeOmitted 2 false)
  , ((3, true), Carbohydrate1996NamedParents.ketoseCarbonylLocantMayBeOmitted 3 true) ]

def ketoseLocantStyleInventory :
    List (Carbohydrate1996NamedParents.KetoseLocantStyle × String) :=
  [ (.iupac, Carbohydrate1996NamedParents.hexThreeUloseStem .iupac)
  , (.cas, Carbohydrate1996NamedParents.hexThreeUloseStem .cas) ]

def ketoaldoseLocantInventory :
    List (Carbohydrate1996NamedParents.KetoaldoseCarbonyl × Option Nat) :=
  [ (.aldehydic, Carbohydrate1996NamedParents.KetoaldoseCarbonyl.aldehydic.citedLocant?)
  , (.ketonic 2, (Carbohydrate1996NamedParents.KetoaldoseCarbonyl.ketonic 2).citedLocant?)
  , (.ketonic 4, (Carbohydrate1996NamedParents.KetoaldoseCarbonyl.ketonic 4).citedLocant?) ]

def aldoseChartInventory :
    List (Carbohydrate1996NamedParents.AldoseChartRow ×
      Carbohydrate1996NamedParents.AldoseChartData) :=
  Carbohydrate1996NamedParents.AldoseChartRow.all.map fun row => (row, row.data)

def ketoseChartInventory :
    List (Carbohydrate1996NamedParents.KetoseChartRow ×
      Carbohydrate1996NamedParents.KetoseChartData) :=
  Carbohydrate1996NamedParents.KetoseChartRow.all.map fun row => (row, row.data)

def workedExampleInventory :
    List (Carbohydrate1996NamedParents.WorkedExample ×
      Carbohydrate1996NamedParents.WorkedExampleData) :=
  Carbohydrate1996NamedParents.WorkedExample.all.map fun row => (row, row.data)

/- Every source clause has a separate assertion constructor. Executable rules and source tables
retain their concrete inputs and outputs. -/
inductive SourceAssertion where
  | aldoseTrivialNamesThreeToSix
      (inventory : List (Carbohydrate1996NamedParents.AldoseChartRow ×
        Carbohydrate1996NamedParents.AldoseChartData))
  | aldoseTrivialNamesGroundPrefixes
      (inventory : List (Carbohydrate1996NamedParents.AldoseChartRow ×
        Carbohydrate1996NamedParents.AldoseChartData))
  | aldoseSystematicStemInventory (inventory : List (Nat × Option String))
  | aldoseC1CarbonylNumbering (locant : Nat)
  | systematicNameStemPlusPrefixes
  | configurationalPrefixLowerCase
  | configurationalPrefixItalicized
  | everyPrefixQualifiedDL
  | chartIShowsDStructures
      (inventory : List (Carbohydrate1996NamedParents.AldoseChartRow ×
        Carbohydrate1996NamedParents.AldoseChartData))
  | trivialParentNamesPreferred
  | trivialDerivativeNamesPreferredWhenCentersUnmodified
  | overFourCentersUseMultiplePrefixes (centerCounts : List Nat)
  | groupsAssignedFourFromC1 (inventory : List (Nat × List Nat))
  | farthestGroupCitedFirst (inventory : List (Nat × List Nat))
  | nonchiralCentersIgnored
      (positions : List (Option Carbohydrate1996NamedParents.FischerSide))
      (sides : List Carbohydrate1996NamedParents.FischerSide)
  | parentAldosesNeedNoSeparatedSequenceRule
  | systematicNamesMostlyHigherAldoses
  | configurationalPrefixesAlsoApplyBeyondAldoses
  | cyclicAldoseAnomerRoutesToTwoCarbSix (route : String)
  | dialdoseReplacesOseWithOdialdose
  | dialdoseUsesConfigurationalPrefix
  | dialdoseParentChoiceUsesTwoCarbTwo (route : String)
  | dialdoseMesoOptionalWhenStructureDefined
  | cyclicDialdoseClosureLocantsRequired
  | dialdoseClosureOrderAnomericThenOxygenBearing
      (anomeric oxygenBearing : Nat) (locants : List Nat)
  | multipleRingDesignatorsAlphabetical
      (inventory : List ((Carbohydrate1996NamedParents.RingSizeDesignator ×
        Carbohydrate1996NamedParents.RingSizeDesignator) ×
          List Carbohydrate1996NamedParents.RingSizeDesignator))
  | ketoseClassifiedByPotentialCarbonylPosition (inventory : List (Nat × String))
  | ketoseLocantTwoOmittableWhenUnambiguous (inventory : List ((Nat × Bool) × Bool))
  | chartIVCoversThreeToSixCarbonTwoKetoses
      (inventory : List (Carbohydrate1996NamedParents.KetoseChartRow ×
        Carbohydrate1996NamedParents.KetoseChartData))
  | obsoleteLTrivialKetoseNamesAreRedundant
  | obsoleteLTrivialKetoseNamesNotForDerivatives
  | sedoheptuloseAcceptedForDAltroHeptTwoUlose
  | ketoseSystematicNameStemPlusPrefix
  | ketoseStemReplacesOseWithUlose
  | carbonylLocantPrecedesUlose
  | ketoseChainGivesCarbonylLowestLocant
  | oddCentralKetoseUsesParentChoiceRule (route : String)
  | casKetoseLocantPlacementDiffers
      (inventory : List (Carbohydrate1996NamedParents.KetoseLocantStyle × String))
  | twoKetosePrefixesFollowAldoseRules (route : String)
  | highKetoseCarbonylIgnoredForPrefixes
      (positions : List (Option Carbohydrate1996NamedParents.FischerSide))
      (sides : List Carbohydrate1996NamedParents.FischerSide)
  | highKetoseNonchiralCentersIgnored
      (positions : List (Option Carbohydrate1996NamedParents.FischerSide))
      (sides : List Carbohydrate1996NamedParents.FischerSide)
  | diketoseReplacesTerminalSeWithDiulose
  | diketoseCarbonylLocantsLowest
  | diketoseCarbonylLocantsBeforeEnding
  | diketoseUsesConfigurationalPrefix
  | diketoseChoiceUsesTwoCarbTwo (route : String)
  | cyclicDiketoseMayNeedClosureLocants
  | cyclicDiketoseCarbonylClosureLocantFirst
  | dividedDiketoseCentersUseOneSequence
  | ketoaldoseNamedAnalogouslyToDiketose
  | ketoaldoseUsesUloseInsteadTerminalE
  | ketoaldoseAldehydeCarbonIsOne (locant : Nat)
  | ketoaldoseAldehydeLocantOmitted
      (carbonyl : Carbohydrate1996NamedParents.KetoaldoseCarbonyl) (locant : Option Nat)
  | ketoaldoseKetoneLocantInfixUnlessTwo
      (inventory : List (Carbohydrate1996NamedParents.KetoaldoseCarbonyl × Option Nat))
  | sourceRetainsKetoneLocantTwoForClarity (locant : Nat)
  | cyclicKetoaldoseMayNeedClosureLocants
  | cyclicKetoaldoseCarbonylClosureLocantFirst
  | ringSizeDesignatorDependsOnClosingCarbonyl
  | biochemicalDehydroNamesWidespread
  | dehydroNamesCanBeStereochemicallyRedundant
  | dehydroNamesNotForDerivatives
  | enzymeNamesUseSubstrateParentAndPriorityProduct
  | aldoseChart (row : Carbohydrate1996NamedParents.AldoseChartRow)
      (data : Carbohydrate1996NamedParents.AldoseChartData)
  | ketoseChart (row : Carbohydrate1996NamedParents.KetoseChartRow)
      (data : Carbohydrate1996NamedParents.KetoseChartData)
  | workedExample (row : Carbohydrate1996NamedParents.WorkedExample)
      (data : Carbohydrate1996NamedParents.WorkedExampleData)
  deriving Repr

def sourceAssertion : Carbohydrate1996NamedParents.Provision → SourceAssertion
  | .aldoseTrivialNamesThreeToSix => .aldoseTrivialNamesThreeToSix aldoseChartInventory
  | .aldoseTrivialNamesGroundPrefixes => .aldoseTrivialNamesGroundPrefixes aldoseChartInventory
  | .aldoseSystematicStemInventory => .aldoseSystematicStemInventory aldoseStemInventory
  | .aldoseC1CarbonylNumbering => .aldoseC1CarbonylNumbering 1
  | .systematicNameStemPlusPrefixes => .systematicNameStemPlusPrefixes
  | .configurationalPrefixLowerCase => .configurationalPrefixLowerCase
  | .configurationalPrefixItalicized => .configurationalPrefixItalicized
  | .everyPrefixQualifiedDL => .everyPrefixQualifiedDL
  | .chartIShowsDStructures => .chartIShowsDStructures aldoseChartInventory
  | .trivialParentNamesPreferred => .trivialParentNamesPreferred
  | .trivialDerivativeNamesPreferredWhenCentersUnmodified =>
      .trivialDerivativeNamesPreferredWhenCentersUnmodified
  | .overFourCentersUseMultiplePrefixes => .overFourCentersUseMultiplePrefixes [5, 9]
  | .groupsAssignedFourFromC1 => .groupsAssignedFourFromC1 fiveAndNineCenterGroupInventory
  | .farthestGroupCitedFirst => .farthestGroupCitedFirst fiveAndNineCenterCitationInventory
  | .nonchiralCentersIgnored =>
      .nonchiralCentersIgnored configurationSideExample
        (Carbohydrate1996NamedParents.configurationSides configurationSideExample)
  | .parentAldosesNeedNoSeparatedSequenceRule => .parentAldosesNeedNoSeparatedSequenceRule
  | .systematicNamesMostlyHigherAldoses => .systematicNamesMostlyHigherAldoses
  | .configurationalPrefixesAlsoApplyBeyondAldoses =>
      .configurationalPrefixesAlsoApplyBeyondAldoses
  | .cyclicAldoseAnomerRoutesToTwoCarbSix =>
      .cyclicAldoseAnomerRoutesToTwoCarbSix "2-Carb-6"
  | .dialdoseReplacesOseWithOdialdose => .dialdoseReplacesOseWithOdialdose
  | .dialdoseUsesConfigurationalPrefix => .dialdoseUsesConfigurationalPrefix
  | .dialdoseParentChoiceUsesTwoCarbTwo => .dialdoseParentChoiceUsesTwoCarbTwo "2-Carb-2"
  | .dialdoseMesoOptionalWhenStructureDefined => .dialdoseMesoOptionalWhenStructureDefined
  | .cyclicDialdoseClosureLocantsRequired => .cyclicDialdoseClosureLocantsRequired
  | .dialdoseClosureOrderAnomericThenOxygenBearing =>
      .dialdoseClosureOrderAnomericThenOxygenBearing 6 2
        (Carbohydrate1996NamedParents.dialdoseClosureLocants 6 2)
  | .multipleRingDesignatorsAlphabetical =>
      .multipleRingDesignatorsAlphabetical ringDesignatorOrderInventory
  | .ketoseClassifiedByPotentialCarbonylPosition =>
      .ketoseClassifiedByPotentialCarbonylPosition ketoseClassInventory
  | .ketoseLocantTwoOmittableWhenUnambiguous =>
      .ketoseLocantTwoOmittableWhenUnambiguous ketoseLocantOmissionInventory
  | .chartIVCoversThreeToSixCarbonTwoKetoses =>
      .chartIVCoversThreeToSixCarbonTwoKetoses ketoseChartInventory
  | .obsoleteLTrivialKetoseNamesAreRedundant => .obsoleteLTrivialKetoseNamesAreRedundant
  | .obsoleteLTrivialKetoseNamesNotForDerivatives =>
      .obsoleteLTrivialKetoseNamesNotForDerivatives
  | .sedoheptuloseAcceptedForDAltroHeptTwoUlose => .sedoheptuloseAcceptedForDAltroHeptTwoUlose
  | .ketoseSystematicNameStemPlusPrefix => .ketoseSystematicNameStemPlusPrefix
  | .ketoseStemReplacesOseWithUlose => .ketoseStemReplacesOseWithUlose
  | .carbonylLocantPrecedesUlose => .carbonylLocantPrecedesUlose
  | .ketoseChainGivesCarbonylLowestLocant => .ketoseChainGivesCarbonylLowestLocant
  | .oddCentralKetoseUsesParentChoiceRule => .oddCentralKetoseUsesParentChoiceRule "2-Carb-2"
  | .casKetoseLocantPlacementDiffers =>
      .casKetoseLocantPlacementDiffers ketoseLocantStyleInventory
  | .twoKetosePrefixesFollowAldoseRules => .twoKetosePrefixesFollowAldoseRules "2-Carb-8"
  | .highKetoseCarbonylIgnoredForPrefixes =>
      .highKetoseCarbonylIgnoredForPrefixes configurationSideExample
        (Carbohydrate1996NamedParents.highKetoseConfigurationSides configurationSideExample)
  | .highKetoseNonchiralCentersIgnored =>
      .highKetoseNonchiralCentersIgnored configurationSideExample
        (Carbohydrate1996NamedParents.highKetoseConfigurationSides configurationSideExample)
  | .diketoseReplacesTerminalSeWithDiulose => .diketoseReplacesTerminalSeWithDiulose
  | .diketoseCarbonylLocantsLowest => .diketoseCarbonylLocantsLowest
  | .diketoseCarbonylLocantsBeforeEnding => .diketoseCarbonylLocantsBeforeEnding
  | .diketoseUsesConfigurationalPrefix => .diketoseUsesConfigurationalPrefix
  | .diketoseChoiceUsesTwoCarbTwo => .diketoseChoiceUsesTwoCarbTwo "2-Carb-2"
  | .cyclicDiketoseMayNeedClosureLocants => .cyclicDiketoseMayNeedClosureLocants
  | .cyclicDiketoseCarbonylClosureLocantFirst => .cyclicDiketoseCarbonylClosureLocantFirst
  | .dividedDiketoseCentersUseOneSequence => .dividedDiketoseCentersUseOneSequence
  | .ketoaldoseNamedAnalogouslyToDiketose => .ketoaldoseNamedAnalogouslyToDiketose
  | .ketoaldoseUsesUloseInsteadTerminalE => .ketoaldoseUsesUloseInsteadTerminalE
  | .ketoaldoseAldehydeCarbonIsOne => .ketoaldoseAldehydeCarbonIsOne 1
  | .ketoaldoseAldehydeLocantOmitted =>
      .ketoaldoseAldehydeLocantOmitted .aldehydic
        Carbohydrate1996NamedParents.KetoaldoseCarbonyl.aldehydic.citedLocant?
  | .ketoaldoseKetoneLocantInfixUnlessTwo =>
      .ketoaldoseKetoneLocantInfixUnlessTwo ketoaldoseLocantInventory
  | .sourceRetainsKetoneLocantTwoForClarity => .sourceRetainsKetoneLocantTwoForClarity 2
  | .cyclicKetoaldoseMayNeedClosureLocants => .cyclicKetoaldoseMayNeedClosureLocants
  | .cyclicKetoaldoseCarbonylClosureLocantFirst => .cyclicKetoaldoseCarbonylClosureLocantFirst
  | .ringSizeDesignatorDependsOnClosingCarbonyl => .ringSizeDesignatorDependsOnClosingCarbonyl
  | .biochemicalDehydroNamesWidespread => .biochemicalDehydroNamesWidespread
  | .dehydroNamesCanBeStereochemicallyRedundant => .dehydroNamesCanBeStereochemicallyRedundant
  | .dehydroNamesNotForDerivatives => .dehydroNamesNotForDerivatives
  | .enzymeNamesUseSubstrateParentAndPriorityProduct =>
      .enzymeNamesUseSubstrateParentAndPriorityProduct
  | .aldoseChart row => .aldoseChart row row.data
  | .ketoseChart row => .ketoseChart row row.data
  | .workedExample row => .workedExample row row.data

def SourceAssertion.provision : SourceAssertion → Carbohydrate1996NamedParents.Provision
  | .aldoseTrivialNamesThreeToSix _ => .aldoseTrivialNamesThreeToSix
  | .aldoseTrivialNamesGroundPrefixes _ => .aldoseTrivialNamesGroundPrefixes
  | .aldoseSystematicStemInventory _ => .aldoseSystematicStemInventory
  | .aldoseC1CarbonylNumbering _ => .aldoseC1CarbonylNumbering
  | .systematicNameStemPlusPrefixes => .systematicNameStemPlusPrefixes
  | .configurationalPrefixLowerCase => .configurationalPrefixLowerCase
  | .configurationalPrefixItalicized => .configurationalPrefixItalicized
  | .everyPrefixQualifiedDL => .everyPrefixQualifiedDL
  | .chartIShowsDStructures _ => .chartIShowsDStructures
  | .trivialParentNamesPreferred => .trivialParentNamesPreferred
  | .trivialDerivativeNamesPreferredWhenCentersUnmodified =>
      .trivialDerivativeNamesPreferredWhenCentersUnmodified
  | .overFourCentersUseMultiplePrefixes _ => .overFourCentersUseMultiplePrefixes
  | .groupsAssignedFourFromC1 _ => .groupsAssignedFourFromC1
  | .farthestGroupCitedFirst _ => .farthestGroupCitedFirst
  | .nonchiralCentersIgnored _ _ => .nonchiralCentersIgnored
  | .parentAldosesNeedNoSeparatedSequenceRule => .parentAldosesNeedNoSeparatedSequenceRule
  | .systematicNamesMostlyHigherAldoses => .systematicNamesMostlyHigherAldoses
  | .configurationalPrefixesAlsoApplyBeyondAldoses =>
      .configurationalPrefixesAlsoApplyBeyondAldoses
  | .cyclicAldoseAnomerRoutesToTwoCarbSix _ => .cyclicAldoseAnomerRoutesToTwoCarbSix
  | .dialdoseReplacesOseWithOdialdose => .dialdoseReplacesOseWithOdialdose
  | .dialdoseUsesConfigurationalPrefix => .dialdoseUsesConfigurationalPrefix
  | .dialdoseParentChoiceUsesTwoCarbTwo _ => .dialdoseParentChoiceUsesTwoCarbTwo
  | .dialdoseMesoOptionalWhenStructureDefined => .dialdoseMesoOptionalWhenStructureDefined
  | .cyclicDialdoseClosureLocantsRequired => .cyclicDialdoseClosureLocantsRequired
  | .dialdoseClosureOrderAnomericThenOxygenBearing _ _ _ =>
      .dialdoseClosureOrderAnomericThenOxygenBearing
  | .multipleRingDesignatorsAlphabetical _ => .multipleRingDesignatorsAlphabetical
  | .ketoseClassifiedByPotentialCarbonylPosition _ =>
      .ketoseClassifiedByPotentialCarbonylPosition
  | .ketoseLocantTwoOmittableWhenUnambiguous _ => .ketoseLocantTwoOmittableWhenUnambiguous
  | .chartIVCoversThreeToSixCarbonTwoKetoses _ => .chartIVCoversThreeToSixCarbonTwoKetoses
  | .obsoleteLTrivialKetoseNamesAreRedundant => .obsoleteLTrivialKetoseNamesAreRedundant
  | .obsoleteLTrivialKetoseNamesNotForDerivatives =>
      .obsoleteLTrivialKetoseNamesNotForDerivatives
  | .sedoheptuloseAcceptedForDAltroHeptTwoUlose => .sedoheptuloseAcceptedForDAltroHeptTwoUlose
  | .ketoseSystematicNameStemPlusPrefix => .ketoseSystematicNameStemPlusPrefix
  | .ketoseStemReplacesOseWithUlose => .ketoseStemReplacesOseWithUlose
  | .carbonylLocantPrecedesUlose => .carbonylLocantPrecedesUlose
  | .ketoseChainGivesCarbonylLowestLocant => .ketoseChainGivesCarbonylLowestLocant
  | .oddCentralKetoseUsesParentChoiceRule _ => .oddCentralKetoseUsesParentChoiceRule
  | .casKetoseLocantPlacementDiffers _ => .casKetoseLocantPlacementDiffers
  | .twoKetosePrefixesFollowAldoseRules _ => .twoKetosePrefixesFollowAldoseRules
  | .highKetoseCarbonylIgnoredForPrefixes _ _ => .highKetoseCarbonylIgnoredForPrefixes
  | .highKetoseNonchiralCentersIgnored _ _ => .highKetoseNonchiralCentersIgnored
  | .diketoseReplacesTerminalSeWithDiulose => .diketoseReplacesTerminalSeWithDiulose
  | .diketoseCarbonylLocantsLowest => .diketoseCarbonylLocantsLowest
  | .diketoseCarbonylLocantsBeforeEnding => .diketoseCarbonylLocantsBeforeEnding
  | .diketoseUsesConfigurationalPrefix => .diketoseUsesConfigurationalPrefix
  | .diketoseChoiceUsesTwoCarbTwo _ => .diketoseChoiceUsesTwoCarbTwo
  | .cyclicDiketoseMayNeedClosureLocants => .cyclicDiketoseMayNeedClosureLocants
  | .cyclicDiketoseCarbonylClosureLocantFirst => .cyclicDiketoseCarbonylClosureLocantFirst
  | .dividedDiketoseCentersUseOneSequence => .dividedDiketoseCentersUseOneSequence
  | .ketoaldoseNamedAnalogouslyToDiketose => .ketoaldoseNamedAnalogouslyToDiketose
  | .ketoaldoseUsesUloseInsteadTerminalE => .ketoaldoseUsesUloseInsteadTerminalE
  | .ketoaldoseAldehydeCarbonIsOne _ => .ketoaldoseAldehydeCarbonIsOne
  | .ketoaldoseAldehydeLocantOmitted _ _ => .ketoaldoseAldehydeLocantOmitted
  | .ketoaldoseKetoneLocantInfixUnlessTwo _ => .ketoaldoseKetoneLocantInfixUnlessTwo
  | .sourceRetainsKetoneLocantTwoForClarity _ => .sourceRetainsKetoneLocantTwoForClarity
  | .cyclicKetoaldoseMayNeedClosureLocants => .cyclicKetoaldoseMayNeedClosureLocants
  | .cyclicKetoaldoseCarbonylClosureLocantFirst => .cyclicKetoaldoseCarbonylClosureLocantFirst
  | .ringSizeDesignatorDependsOnClosingCarbonyl => .ringSizeDesignatorDependsOnClosingCarbonyl
  | .biochemicalDehydroNamesWidespread => .biochemicalDehydroNamesWidespread
  | .dehydroNamesCanBeStereochemicallyRedundant => .dehydroNamesCanBeStereochemicallyRedundant
  | .dehydroNamesNotForDerivatives => .dehydroNamesNotForDerivatives
  | .enzymeNamesUseSubstrateParentAndPriorityProduct =>
      .enzymeNamesUseSubstrateParentAndPriorityProduct
  | .aldoseChart row _ => .aldoseChart row
  | .ketoseChart row _ => .ketoseChart row
  | .workedExample row _ => .workedExample row

@[simp] theorem sourceAssertion_provision_exact
    (row : Carbohydrate1996NamedParents.Provision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

structure SourceMeaning where
  sourceKey : String
  semanticDomain : SemanticDomain
  assertion : SourceAssertion
  deriving Repr

def sourceMeaning (row : Carbohydrate1996NamedParents.Provision) : SourceMeaning :=
  ⟨row.sourceKey, semanticDomain row, sourceAssertion row⟩

@[simp] theorem sourceMeaning_key_exact (row : Carbohydrate1996NamedParents.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by
  rfl

@[simp] theorem sourceMeaning_domain_exact (row : Carbohydrate1996NamedParents.Provision) :
    (sourceMeaning row).semanticDomain = semanticDomain row := by
  rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def fullFamilyRows : List Carbohydrate1996NamedParents.Provision :=
  Carbohydrate1996NamedParents.Provision.all

def fullFamilyProvisions : List IUPACNormativeProvision :=
  fullFamilyRows.map IUPACNormativeProvision.carbohydrate1996NamedParents

def completionRows : List Carbohydrate1996NamedParents.Provision :=
  Carbohydrate1996NamedParents.Provision.base

def completionProvisions : List IUPACNormativeProvision :=
  completionRows.map IUPACNormativeProvision.carbohydrate1996NamedParents

def completionBatch : GlobalNonDescriptorSourceMeaningBatch completionProvisions :=
  totalMeaningBatch completionRows IUPACNormativeProvision.carbohydrate1996NamedParents
    sourceMeaning (by intro _row; rfl)

@[simp] theorem full_family_provisions_exact :
    fullFamilyProvisions = carbohydrate1996NamedParentsSemanticsSlice := by
  rfl

@[simp] theorem full_family_provision_count : fullFamilyProvisions.length = 112 := by
  simp [fullFamilyProvisions, fullFamilyRows]

@[simp] theorem completion_provision_count : completionProvisions.length = 62 := by
  simp [completionProvisions, completionRows, Carbohydrate1996NamedParents.Provision.base]

@[simp] theorem completion_entry_count : completionBatch.entries.length = 62 := by
  rw [completionBatch.entries_length, completion_provision_count]

private theorem completion_rows_then_indexed_exact :
    completionRows ++ GlobalNonDescriptorIndexedSourceData.carbohydrateNamedParentRows =
      fullFamilyRows := by
  simp [completionRows, fullFamilyRows,
    GlobalNonDescriptorIndexedSourceData.carbohydrateNamedParentRows,
    Carbohydrate1996NamedParents.Provision.all, List.append_assoc]

theorem completion_then_indexed_exact_source_order :
    completionProvisions ++
      GlobalNonDescriptorIndexedSourceData.carbohydrateNamedParentProvisions =
        carbohydrate1996NamedParentsSemanticsSlice := by
  rw [← full_family_provisions_exact]
  simp only [completionProvisions,
    GlobalNonDescriptorIndexedSourceData.carbohydrateNamedParentProvisions,
    fullFamilyProvisions, ← List.map_append]
  rw [completion_rows_then_indexed_exact]

theorem materialized_order_perm_source :
    (GlobalNonDescriptorIndexedSourceData.carbohydrateNamedParentProvisions ++
      completionProvisions).Perm carbohydrate1996NamedParentsSemanticsSlice := by
  calc
    (GlobalNonDescriptorIndexedSourceData.carbohydrateNamedParentProvisions ++
      completionProvisions).Perm
        (completionProvisions ++
          GlobalNonDescriptorIndexedSourceData.carbohydrateNamedParentProvisions) :=
      List.perm_append_comm
    _ = carbohydrate1996NamedParentsSemanticsSlice :=
      completion_then_indexed_exact_source_order

theorem completion_disjoint_indexed :
    completionProvisions.Disjoint
      GlobalNonDescriptorIndexedSourceData.carbohydrateNamedParentProvisions := by
  apply List.disjoint_of_nodup_append
  rw [completion_then_indexed_exact_source_order]
  exact Carbohydrate1996NamedParents.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

theorem completion_provisions_nodup : completionProvisions.Nodup := by
  exact Carbohydrate1996NamedParents.Provision.all_nodup.of_append_left.of_append_left.of_append_left.map
    (by intro left right equal; cases equal; rfl)

@[simp] theorem completion_entry_provisions_exact :
    completionBatch.entries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      completionProvisions :=
  completionBatch.provisions_exact

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

end GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.full_family_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completion_then_indexed_exact_source_order
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.materialized_order_perm_source
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.completion_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.every_completion_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateNamedParentSourceMeaning.source_audit_still_open
