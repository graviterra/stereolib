import TetraStereo.OneCenter.Basic
import TetraStereo.OneCenter.P10DelegatedAuthorityCorpus

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent carbohydrate named-parent stereochemistry semantics

This module audits 2-Carb-8 through 2-Carb-12 of *Nomenclature of Carbohydrates
(Recommendations 1996)*.  It keeps three kinds of source evidence distinct:

* normative naming and configuration clauses;
* every structure row of Chart I and Chart IV used by those clauses; and
* every worked example printed in 2-Carb-8--12.

The data are an independent source-level target.  They are not defined through the production
name parser or descriptor engine, and this module does not claim that later carbohydrate sections
have been transcribed.
-/

namespace Carbohydrate1996NamedParents

inductive FischerSide where
  | left
  | right
  deriving DecidableEq, Repr

def FischerSide.mirror : FischerSide → FischerSide
  | .left => .right
  | .right => .left

@[simp] theorem FischerSide.mirror_mirror (side : FischerSide) :
    side.mirror.mirror = side := by
  cases side <;> rfl

inductive AldoseChartRow where
  | glyceraldehyde
  | erythrose
  | threose
  | ribose
  | arabinose
  | xylose
  | lyxose
  | allose
  | altrose
  | glucose
  | mannose
  | gulose
  | idose
  | galactose
  | talose
  deriving DecidableEq, Repr

namespace AldoseChartRow

def all : List AldoseChartRow :=
  [ .glyceraldehyde, .erythrose, .threose, .ribose, .arabinose, .xylose, .lyxose
  , .allose, .altrose, .glucose, .mannose, .gulose, .idose, .galactose, .talose
  ]

@[simp] theorem mem_all (row : AldoseChartRow) : row ∈ all := by
  cases row <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 15 := by decide

end AldoseChartRow

structure AldoseChartData where
  carbonCount : Nat
  trivialName : String
  configurationalPrefix : String
  abbreviation : Option String
  hydroxySidesFromC2 : List FischerSide
  deriving DecidableEq, Repr

/-- Exact Chart-I D-series rows.  The side lists run down the Fischer projection from C-2. -/
def AldoseChartRow.data : AldoseChartRow → AldoseChartData
  | .glyceraldehyde => ⟨3, "D-Glyceraldehyde", "D-glycero", none, [.right]⟩
  | .erythrose => ⟨4, "D-Erythrose", "D-erythro", none, [.right, .right]⟩
  | .threose => ⟨4, "D-Threose", "D-threo", none, [.left, .right]⟩
  | .ribose => ⟨5, "D-Ribose", "D-ribo", some "D-Rib", [.right, .right, .right]⟩
  | .arabinose => ⟨5, "D-Arabinose", "D-arabino", some "D-Ara", [.left, .right, .right]⟩
  | .xylose => ⟨5, "D-Xylose", "D-xylo", some "D-Xyl", [.right, .left, .right]⟩
  | .lyxose => ⟨5, "D-Lyxose", "D-lyxo", some "D-Lyx", [.left, .left, .right]⟩
  | .allose => ⟨6, "D-Allose", "D-allo", some "D-All", [.right, .right, .right, .right]⟩
  | .altrose => ⟨6, "D-Altrose", "D-altro", some "D-Alt", [.left, .right, .right, .right]⟩
  | .glucose => ⟨6, "D-Glucose", "D-gluco", some "D-Glc", [.right, .left, .right, .right]⟩
  | .mannose => ⟨6, "D-Mannose", "D-manno", some "D-Man", [.left, .left, .right, .right]⟩
  | .gulose => ⟨6, "D-Gulose", "D-gulo", some "D-Gul", [.right, .right, .left, .right]⟩
  | .idose => ⟨6, "D-Idose", "D-ido", some "D-Ido", [.left, .right, .left, .right]⟩
  | .galactose => ⟨6, "D-Galactose", "D-galacto", some "D-Gal", [.right, .left, .left, .right]⟩
  | .talose => ⟨6, "D-Talose", "D-talo", some "D-Tal", [.left, .left, .left, .right]⟩

theorem every_chart_I_row_has_D_configurational_atom (row : AldoseChartRow) :
    row.data.hydroxySidesFromC2.getLast? = some .right := by
  cases row <;> decide

theorem chart_I_trivial_names_are_pairwise_distinct :
    (AldoseChartRow.all.map fun row => row.data.trivialName).Nodup := by
  decide

def mirrorSides (sides : List FischerSide) : List FischerSide :=
  sides.map FischerSide.mirror

@[simp] theorem mirrorSides_involutive (sides : List FischerSide) :
    mirrorSides (mirrorSides sides) = sides := by
  change List.map FischerSide.mirror (List.map FischerSide.mirror sides) = sides
  rw [List.map_map]
  have h : FischerSide.mirror ∘ FischerSide.mirror = id := by
    funext side
    cases side <;> rfl
  rw [h, List.map_id]

inductive KetoseChartRow where
  | dihydroxyacetone
  | erythrulose
  | ribulose
  | xylulose
  | psicose
  | fructose
  | sorbose
  | tagatose
  deriving DecidableEq, Repr

namespace KetoseChartRow

def all : List KetoseChartRow :=
  [ .dihydroxyacetone, .erythrulose, .ribulose, .xylulose
  , .psicose, .fructose, .sorbose, .tagatose
  ]

@[simp] theorem mem_all (row : KetoseChartRow) : row ∈ all := by
  cases row <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 8 := by decide

end KetoseChartRow

structure KetoseChartData where
  carbonCount : Nat
  systematicName : String
  trivialName : Option String
  abbreviation : Option String
  hydroxySidesBelowCarbonyl : List FischerSide
  deriving DecidableEq, Repr

/-- Exact Chart-IV rows.  All are 2-ketoses; dihydroxyacetone has no stereocentre. -/
def KetoseChartRow.data : KetoseChartRow → KetoseChartData
  | .dihydroxyacetone => ⟨3, "1,3-Dihydroxyacetone", none, none, []⟩
  | .erythrulose => ⟨4, "D-glycero-Tetrulose", some "D-Erythrulose", none, [.right]⟩
  | .ribulose => ⟨5, "D-erythro-Pent-2-ulose", some "D-Ribulose", some "D-Rul", [.right, .right]⟩
  | .xylulose => ⟨5, "D-threo-Pent-2-ulose", some "D-Xylulose", some "D-Xul", [.left, .right]⟩
  | .psicose => ⟨6, "D-ribo-Hex-2-ulose", some "D-Psicose", some "D-Psi", [.right, .right, .right]⟩
  | .fructose => ⟨6, "D-arabino-Hex-2-ulose", some "D-Fructose", some "D-Fru", [.left, .right, .right]⟩
  | .sorbose => ⟨6, "D-xylo-Hex-2-ulose", some "D-Sorbose", some "D-Sor", [.right, .left, .right]⟩
  | .tagatose => ⟨6, "D-lyxo-Hex-2-ulose", some "D-Tagatose", some "D-Tag", [.left, .left, .right]⟩

theorem every_chiral_chart_IV_row_has_D_configurational_atom
    (row : KetoseChartRow) (h : row ≠ .dihydroxyacetone) :
    row.data.hydroxySidesBelowCarbonyl.getLast? = some .right := by
  cases row <;> simp_all [KetoseChartRow.data]

theorem chart_IV_systematic_names_are_pairwise_distinct :
    (KetoseChartRow.all.map fun row => row.data.systematicName).Nodup := by
  decide

inductive WorkedExample where
  | higherAldoseGlyceroGluco
  | higherAldoseRiboManno
  | separatedCentersDideoxy
  | dialdoseThreo
  | dialdoseGalacto
  | dialdosePyranose
  | reverseClosureDialdose
  | bicyclicDialdose
  | ketoseSorbose
  | ketoseSedoheptulose
  | ketoseSedoheptulopyranose
  | ketoseGlyceroManno
  | highKetoseArabino
  | highKetoseXylo
  | highKetoseGluco
  | highKetoseThreoAllo
  | highKetoseErythroGluco
  | diketoseThreo
  | diketoseMesoXylo
  | dividedCentersThreo
  | dividedCentersFuranose
  | dividedCentersAltro
  | dividedCentersGlyceroManno
  | dividedCentersGlyceroIdo
  | ketoaldoseArabino
  | ketoaldoseMethylXylo
  | ketoaldoseMethylFuranoside
  deriving DecidableEq, Repr

namespace WorkedExample

def all : List WorkedExample :=
  [ .higherAldoseGlyceroGluco, .higherAldoseRiboManno, .separatedCentersDideoxy
  , .dialdoseThreo, .dialdoseGalacto, .dialdosePyranose, .reverseClosureDialdose
  , .bicyclicDialdose, .ketoseSorbose, .ketoseSedoheptulose
  , .ketoseSedoheptulopyranose, .ketoseGlyceroManno, .highKetoseArabino
  , .highKetoseXylo, .highKetoseGluco, .highKetoseThreoAllo
  , .highKetoseErythroGluco, .diketoseThreo, .diketoseMesoXylo
  , .dividedCentersThreo, .dividedCentersFuranose, .dividedCentersAltro
  , .dividedCentersGlyceroManno, .dividedCentersGlyceroIdo, .ketoaldoseArabino
  , .ketoaldoseMethylXylo, .ketoaldoseMethylFuranoside
  ]

@[simp] theorem mem_all (exampleRow : WorkedExample) : exampleRow ∈ all := by
  cases exampleRow <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 27 := by decide

end WorkedExample

structure WorkedExampleData where
  sourceKey : String
  recommendedName : String
  rejectedName : Option String := none
  deriving DecidableEq, Repr

/-- The printed names attached to every worked structure in 2-Carb-8--12. -/
def WorkedExample.data : WorkedExample → WorkedExampleData
  | .higherAldoseGlyceroGluco =>
      ⟨"2-Carb-8.3/example 083A", "D-glycero-D-gluco-Heptose",
        some "D-gluco-D-glycero-heptose"⟩
  | .higherAldoseRiboManno =>
      ⟨"2-Carb-8.3/example 083B", "L-ribo-D-manno-Nonose",
        some "D-manno-L-ribo-nonose"⟩
  | .separatedCentersDideoxy =>
      ⟨"2-Carb-8.4/example 084", "3,6-Dideoxy-L-threo-L-talo-decose", none⟩
  | .dialdoseThreo => ⟨"2-Carb-9/example 09A", "L-threo-Tetrodialdose", none⟩
  | .dialdoseGalacto => ⟨"2-Carb-9/example 09B", "galacto-Hexodialdose", none⟩
  | .dialdosePyranose =>
      ⟨"2-Carb-9/example 09C", "alpha-D-gluco-Hexodialdo-1,5-pyranose", none⟩
  | .reverseClosureDialdose =>
      ⟨"2-Carb-9/example 09D", "(6R)-D-gluco-Hexodialdo-6,2-pyranose", none⟩
  | .bicyclicDialdose =>
      ⟨"2-Carb-9/example 09E",
        "Methyl alpha-D-gluco-hexodialdo-6,3-furanose-1,5-pyranoside", none⟩
  | .ketoseSorbose =>
      ⟨"2-Carb-10.4/example 104A", "L-xylo-Hex-2-ulose (L-Sorbose)", none⟩
  | .ketoseSedoheptulose =>
      ⟨"2-Carb-10.4/example 104B", "D-altro-Hept-2-ulose (D-Sedoheptulose)", none⟩
  | .ketoseSedoheptulopyranose =>
      ⟨"2-Carb-10.4/example 104C", "D-altro-Hept-2-ulopyranose", none⟩
  | .ketoseGlyceroManno =>
      ⟨"2-Carb-10.4/example 104D", "L-glycero-D-manno-Oct-2-ulose", none⟩
  | .highKetoseArabino =>
      ⟨"2-Carb-10.4/example 104E", "D-arabino-Hex-3-ulose", none⟩
  | .highKetoseXylo =>
      ⟨"2-Carb-10.4/example 104F", "D-xylo-Hex-3-ulose", some "L-xylo-hex-4-ulose"⟩
  | .highKetoseGluco =>
      ⟨"2-Carb-10.4/example 104G", "L-gluco-Hept-4-ulose", some "D-gulo-hept-4-ulose"⟩
  | .highKetoseThreoAllo =>
      ⟨"2-Carb-10.4/example 104H", "L-threo-D-allo-Non-3-ulose", none⟩
  | .highKetoseErythroGluco =>
      ⟨"2-Carb-10.4/example 104I", "L-erythro-L-gluco-Non-5-ulose",
        some "D-threo-L-allo-non-5-ulose"⟩
  | .diketoseThreo =>
      ⟨"2-Carb-11.1/example 111A", "L-threo-Hexo-2,5-diulose", none⟩
  | .diketoseMesoXylo =>
      ⟨"2-Carb-11.1/example 111B", "meso-xylo-Hepto-2,6-diulose", none⟩
  | .dividedCentersThreo =>
      ⟨"2-Carb-11.2/example 112A", "D-threo-Hexo-2,4-diulose", none⟩
  | .dividedCentersFuranose =>
      ⟨"2-Carb-11.2/example 112B", "alpha-D-threo-Hexo-2,4-diulo-2,5-furanose", none⟩
  | .dividedCentersAltro =>
      ⟨"2-Carb-11.2/example 112C", "L-altro-Octo-4,5-diulose",
        some "L-talo-octo-4,5-diulose"⟩
  | .dividedCentersGlyceroManno =>
      ⟨"2-Carb-11.2/example 112D", "L-glycero-D-manno-Nono-2,7-diulose", none⟩
  | .dividedCentersGlyceroIdo =>
      ⟨"2-Carb-11.2/example 112E", "D-glycero-D-ido-Nono-3,6-diulose", none⟩
  | .ketoaldoseArabino =>
      ⟨"2-Carb-12.1/example 121A", "D-arabino-Hexos-3-ulose", none⟩
  | .ketoaldoseMethylXylo =>
      ⟨"2-Carb-12.1/example 121B", "Methyl beta-D-xylo-hexopyranosid-4-ulose", none⟩
  | .ketoaldoseMethylFuranoside =>
      ⟨"2-Carb-12.1/example 121C", "Methyl alpha-L-xylo-hexos-2-ulo-2,5-furanoside", none⟩

theorem worked_example_keys_are_pairwise_distinct :
    (WorkedExample.all.map fun exampleRow => exampleRow.data.sourceKey).Nodup := by
  decide

inductive Provision where
  | aldoseTrivialNamesThreeToSix
  | aldoseTrivialNamesGroundPrefixes
  | aldoseSystematicStemInventory
  | aldoseC1CarbonylNumbering
  | systematicNameStemPlusPrefixes
  | configurationalPrefixLowerCase
  | configurationalPrefixItalicized
  | everyPrefixQualifiedDL
  | chartIShowsDStructures
  | trivialParentNamesPreferred
  | trivialDerivativeNamesPreferredWhenCentersUnmodified
  | overFourCentersUseMultiplePrefixes
  | groupsAssignedFourFromC1
  | farthestGroupCitedFirst
  | nonchiralCentersIgnored
  | parentAldosesNeedNoSeparatedSequenceRule
  | systematicNamesMostlyHigherAldoses
  | configurationalPrefixesAlsoApplyBeyondAldoses
  | cyclicAldoseAnomerRoutesToTwoCarbSix
  | dialdoseReplacesOseWithOdialdose
  | dialdoseUsesConfigurationalPrefix
  | dialdoseParentChoiceUsesTwoCarbTwo
  | dialdoseMesoOptionalWhenStructureDefined
  | cyclicDialdoseClosureLocantsRequired
  | dialdoseClosureOrderAnomericThenOxygenBearing
  | multipleRingDesignatorsAlphabetical
  | ketoseClassifiedByPotentialCarbonylPosition
  | ketoseLocantTwoOmittableWhenUnambiguous
  | chartIVCoversThreeToSixCarbonTwoKetoses
  | obsoleteLTrivialKetoseNamesAreRedundant
  | obsoleteLTrivialKetoseNamesNotForDerivatives
  | sedoheptuloseAcceptedForDAltroHeptTwoUlose
  | ketoseSystematicNameStemPlusPrefix
  | ketoseStemReplacesOseWithUlose
  | carbonylLocantPrecedesUlose
  | ketoseChainGivesCarbonylLowestLocant
  | oddCentralKetoseUsesParentChoiceRule
  | casKetoseLocantPlacementDiffers
  | twoKetosePrefixesFollowAldoseRules
  | highKetoseCarbonylIgnoredForPrefixes
  | highKetoseNonchiralCentersIgnored
  | diketoseReplacesTerminalSeWithDiulose
  | diketoseCarbonylLocantsLowest
  | diketoseCarbonylLocantsBeforeEnding
  | diketoseUsesConfigurationalPrefix
  | diketoseChoiceUsesTwoCarbTwo
  | cyclicDiketoseMayNeedClosureLocants
  | cyclicDiketoseCarbonylClosureLocantFirst
  | dividedDiketoseCentersUseOneSequence
  | ketoaldoseNamedAnalogouslyToDiketose
  | ketoaldoseUsesUloseInsteadTerminalE
  | ketoaldoseAldehydeCarbonIsOne
  | ketoaldoseAldehydeLocantOmitted
  | ketoaldoseKetoneLocantInfixUnlessTwo
  | sourceRetainsKetoneLocantTwoForClarity
  | cyclicKetoaldoseMayNeedClosureLocants
  | cyclicKetoaldoseCarbonylClosureLocantFirst
  | ringSizeDesignatorDependsOnClosingCarbonyl
  | biochemicalDehydroNamesWidespread
  | dehydroNamesCanBeStereochemicallyRedundant
  | dehydroNamesNotForDerivatives
  | enzymeNamesUseSubstrateParentAndPriorityProduct
  | aldoseChart (row : AldoseChartRow)
  | ketoseChart (row : KetoseChartRow)
  | workedExample (exampleRow : WorkedExample)
  deriving DecidableEq, Repr

namespace Provision

def base : List Provision :=
  [ .aldoseTrivialNamesThreeToSix
  , .aldoseTrivialNamesGroundPrefixes
  , .aldoseSystematicStemInventory
  , .aldoseC1CarbonylNumbering
  , .systematicNameStemPlusPrefixes
  , .configurationalPrefixLowerCase
  , .configurationalPrefixItalicized
  , .everyPrefixQualifiedDL
  , .chartIShowsDStructures
  , .trivialParentNamesPreferred
  , .trivialDerivativeNamesPreferredWhenCentersUnmodified
  , .overFourCentersUseMultiplePrefixes
  , .groupsAssignedFourFromC1
  , .farthestGroupCitedFirst
  , .nonchiralCentersIgnored
  , .parentAldosesNeedNoSeparatedSequenceRule
  , .systematicNamesMostlyHigherAldoses
  , .configurationalPrefixesAlsoApplyBeyondAldoses
  , .cyclicAldoseAnomerRoutesToTwoCarbSix
  , .dialdoseReplacesOseWithOdialdose
  , .dialdoseUsesConfigurationalPrefix
  , .dialdoseParentChoiceUsesTwoCarbTwo
  , .dialdoseMesoOptionalWhenStructureDefined
  , .cyclicDialdoseClosureLocantsRequired
  , .dialdoseClosureOrderAnomericThenOxygenBearing
  , .multipleRingDesignatorsAlphabetical
  , .ketoseClassifiedByPotentialCarbonylPosition
  , .ketoseLocantTwoOmittableWhenUnambiguous
  , .chartIVCoversThreeToSixCarbonTwoKetoses
  , .obsoleteLTrivialKetoseNamesAreRedundant
  , .obsoleteLTrivialKetoseNamesNotForDerivatives
  , .sedoheptuloseAcceptedForDAltroHeptTwoUlose
  , .ketoseSystematicNameStemPlusPrefix
  , .ketoseStemReplacesOseWithUlose
  , .carbonylLocantPrecedesUlose
  , .ketoseChainGivesCarbonylLowestLocant
  , .oddCentralKetoseUsesParentChoiceRule
  , .casKetoseLocantPlacementDiffers
  , .twoKetosePrefixesFollowAldoseRules
  , .highKetoseCarbonylIgnoredForPrefixes
  , .highKetoseNonchiralCentersIgnored
  , .diketoseReplacesTerminalSeWithDiulose
  , .diketoseCarbonylLocantsLowest
  , .diketoseCarbonylLocantsBeforeEnding
  , .diketoseUsesConfigurationalPrefix
  , .diketoseChoiceUsesTwoCarbTwo
  , .cyclicDiketoseMayNeedClosureLocants
  , .cyclicDiketoseCarbonylClosureLocantFirst
  , .dividedDiketoseCentersUseOneSequence
  , .ketoaldoseNamedAnalogouslyToDiketose
  , .ketoaldoseUsesUloseInsteadTerminalE
  , .ketoaldoseAldehydeCarbonIsOne
  , .ketoaldoseAldehydeLocantOmitted
  , .ketoaldoseKetoneLocantInfixUnlessTwo
  , .sourceRetainsKetoneLocantTwoForClarity
  , .cyclicKetoaldoseMayNeedClosureLocants
  , .cyclicKetoaldoseCarbonylClosureLocantFirst
  , .ringSizeDesignatorDependsOnClosingCarbonyl
  , .biochemicalDehydroNamesWidespread
  , .dehydroNamesCanBeStereochemicallyRedundant
  , .dehydroNamesNotForDerivatives
  , .enzymeNamesUseSubstrateParentAndPriorityProduct
  ]

def all : List Provision :=
  ((base ++ AldoseChartRow.all.map Provision.aldoseChart) ++
      KetoseChartRow.all.map Provision.ketoseChart) ++
    WorkedExample.all.map Provision.workedExample

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision with
  | aldoseChart row =>
      simp only [all, List.mem_append]
      exact Or.inl (Or.inl (Or.inr
        (List.mem_map_of_mem (f := Provision.aldoseChart) row.mem_all)))
  | ketoseChart row =>
      simp only [all, List.mem_append]
      exact Or.inl (Or.inr
        (List.mem_map_of_mem (f := Provision.ketoseChart) row.mem_all))
  | workedExample exampleRow =>
      simp only [all, List.mem_append]
      exact Or.inr (List.mem_map_of_mem (f := Provision.workedExample) exampleRow.mem_all)
  | _ => simp [all, base]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 112 := by decide

end Provision

def Provision.sourceKey : Provision → String
  | .aldoseTrivialNamesThreeToSix | .aldoseTrivialNamesGroundPrefixes
  | .aldoseChart _ => "2-Carb-8.1/Chart I"
  | .aldoseSystematicStemInventory | .aldoseC1CarbonylNumbering
  | .systematicNameStemPlusPrefixes | .configurationalPrefixLowerCase
  | .configurationalPrefixItalicized | .everyPrefixQualifiedDL | .chartIShowsDStructures
  | .trivialParentNamesPreferred | .trivialDerivativeNamesPreferredWhenCentersUnmodified =>
      "2-Carb-8.2"
  | .overFourCentersUseMultiplePrefixes | .groupsAssignedFourFromC1
  | .farthestGroupCitedFirst => "2-Carb-8.3"
  | .nonchiralCentersIgnored | .parentAldosesNeedNoSeparatedSequenceRule
  | .systematicNamesMostlyHigherAldoses | .configurationalPrefixesAlsoApplyBeyondAldoses =>
      "2-Carb-8.4"
  | .cyclicAldoseAnomerRoutesToTwoCarbSix => "2-Carb-8.5"
  | .dialdoseReplacesOseWithOdialdose | .dialdoseUsesConfigurationalPrefix
  | .dialdoseParentChoiceUsesTwoCarbTwo | .dialdoseMesoOptionalWhenStructureDefined
  | .cyclicDialdoseClosureLocantsRequired
  | .dialdoseClosureOrderAnomericThenOxygenBearing
  | .multipleRingDesignatorsAlphabetical => "2-Carb-9"
  | .ketoseClassifiedByPotentialCarbonylPosition
  | .ketoseLocantTwoOmittableWhenUnambiguous => "2-Carb-10.1"
  | .chartIVCoversThreeToSixCarbonTwoKetoses
  | .obsoleteLTrivialKetoseNamesAreRedundant
  | .obsoleteLTrivialKetoseNamesNotForDerivatives
  | .sedoheptuloseAcceptedForDAltroHeptTwoUlose | .ketoseChart _ => "2-Carb-10.2/Chart IV"
  | .ketoseSystematicNameStemPlusPrefix | .ketoseStemReplacesOseWithUlose
  | .carbonylLocantPrecedesUlose | .ketoseChainGivesCarbonylLowestLocant
  | .oddCentralKetoseUsesParentChoiceRule | .casKetoseLocantPlacementDiffers => "2-Carb-10.3"
  | .twoKetosePrefixesFollowAldoseRules | .highKetoseCarbonylIgnoredForPrefixes
  | .highKetoseNonchiralCentersIgnored => "2-Carb-10.4"
  | .diketoseReplacesTerminalSeWithDiulose | .diketoseCarbonylLocantsLowest
  | .diketoseCarbonylLocantsBeforeEnding | .diketoseUsesConfigurationalPrefix
  | .diketoseChoiceUsesTwoCarbTwo | .cyclicDiketoseMayNeedClosureLocants
  | .cyclicDiketoseCarbonylClosureLocantFirst => "2-Carb-11.1"
  | .dividedDiketoseCentersUseOneSequence => "2-Carb-11.2"
  | .ketoaldoseNamedAnalogouslyToDiketose | .ketoaldoseUsesUloseInsteadTerminalE
  | .ketoaldoseAldehydeCarbonIsOne | .ketoaldoseAldehydeLocantOmitted
  | .ketoaldoseKetoneLocantInfixUnlessTwo | .sourceRetainsKetoneLocantTwoForClarity
  | .cyclicKetoaldoseMayNeedClosureLocants | .cyclicKetoaldoseCarbonylClosureLocantFirst
  | .ringSizeDesignatorDependsOnClosingCarbonyl => "2-Carb-12.1"
  | .biochemicalDehydroNamesWidespread | .dehydroNamesCanBeStereochemicallyRedundant
  | .dehydroNamesNotForDerivatives | .enzymeNamesUseSubstrateParentAndPriorityProduct =>
      "2-Carb-12.2"
  | .workedExample exampleRow => exampleRow.data.sourceKey

/-! ## Executable independent semantics for the general rules -/

def aldoseStem : Nat → Option String
  | 3 => some "triose"
  | 4 => some "tetrose"
  | 5 => some "pentose"
  | 6 => some "hexose"
  | 7 => some "heptose"
  | 8 => some "octose"
  | 9 => some "nonose"
  | 10 => some "decose"
  | _ => none

@[simp] theorem aldose_stem_inventory_is_exact :
    (List.range 8).map (fun offset => aldoseStem (offset + 3)) =
      [ some "triose", some "tetrose", some "pentose", some "hexose"
      , some "heptose", some "octose", some "nonose", some "decose"
      ] := by
  decide

/-- Groups are formed from the C-1 end in blocks of four, with a final shorter block. -/
def configurationGroupSizesFromC1 (centerCount : Nat) : List Nat :=
  List.replicate (centerCount / 4) 4 ++
    if centerCount % 4 = 0 then [] else [centerCount % 4]

/-- Citation reverses those groups, so the group farthest from C-1 is cited first. -/
def configurationPrefixCitationGroupSizes (centerCount : Nat) : List Nat :=
  (configurationGroupSizesFromC1 centerCount).reverse

@[simp] theorem five_center_prefix_grouping :
    configurationGroupSizesFromC1 5 = [4, 1] ∧
      configurationPrefixCitationGroupSizes 5 = [1, 4] := by
  decide

@[simp] theorem nine_center_prefix_grouping :
    configurationGroupSizesFromC1 9 = [4, 4, 1] ∧
      configurationPrefixCitationGroupSizes 9 = [1, 4, 4] := by
  decide

/-- `none` represents an intervening non-chiral center and contributes no configuration side. -/
def configurationSides (centers : List (Option FischerSide)) : List FischerSide :=
  centers.filterMap id

@[simp] theorem intervening_nonchiral_centers_are_ignored :
    configurationSides [some .left, none, some .right, none, some .left] =
      [.left, .right, .left] := by
  rfl

inductive RingSizeDesignator where
  | furanose
  | pyranose
  deriving DecidableEq, Repr

/-- The only two-designator order stated in 2-Carb-9 is alphabetical. -/
def orderRingDesignators (left right : RingSizeDesignator) : List RingSizeDesignator :=
  match left, right with
  | .furanose, .pyranose | .pyranose, .furanose => [.furanose, .pyranose]
  | .furanose, .furanose => [.furanose, .furanose]
  | .pyranose, .pyranose => [.pyranose, .pyranose]

@[simp] theorem furanose_precedes_pyranose_from_either_input_order :
    orderRingDesignators .furanose .pyranose = [.furanose, .pyranose] ∧
      orderRingDesignators .pyranose .furanose = [.furanose, .pyranose] := by
  decide

def dialdoseClosureLocants (anomeric oxygenBearing : Nat) : List Nat :=
  [anomeric, oxygenBearing]

@[simp] theorem dialdose_closure_locant_order_is_not_numeric_sorting :
    dialdoseClosureLocants 6 2 = [6, 2] := by
  rfl

def ketoseClass (potentialCarbonylLocant : Nat) : String :=
  toString potentialCarbonylLocant ++ "-ketose"

@[simp] theorem ketose_class_tracks_potential_carbonyl_locant :
    ketoseClass 3 = "3-ketose" := by
  decide

def ketoseCarbonylLocantMayBeOmitted (locant : Nat) (unambiguous : Bool) : Bool :=
  locant = 2 && unambiguous

@[simp] theorem only_unambiguous_locant_two_is_omittable (locant : Nat) :
    ketoseCarbonylLocantMayBeOmitted locant true = true ↔ locant = 2 := by
  simp [ketoseCarbonylLocantMayBeOmitted]

/-- Prefix extraction ignores carbonyl and other non-chiral positions alike. -/
def highKetoseConfigurationSides (positions : List (Option FischerSide)) : List FischerSide :=
  configurationSides positions

@[simp] theorem high_ketose_carbonyl_is_ignored_for_prefix_selection :
    highKetoseConfigurationSides [some .left, none, some .right, some .right] =
      [.left, .right, .right] := by
  rfl

inductive KetoseLocantStyle where
  | iupac
  | cas
  deriving DecidableEq, Repr

def hexThreeUloseStem : KetoseLocantStyle → String
  | .iupac => "hex-3-ulose"
  | .cas => "3-hexulose"

theorem IUPAC_and_CAS_locant_positions_are_distinct :
    hexThreeUloseStem .iupac ≠ hexThreeUloseStem .cas := by
  decide

inductive KetoaldoseCarbonyl where
  | aldehydic
  | ketonic (locant : Nat)
  deriving DecidableEq, Repr

def KetoaldoseCarbonyl.citedLocant? : KetoaldoseCarbonyl → Option Nat
  | .aldehydic => none
  | .ketonic 2 => none
  | .ketonic locant => some locant

@[simp] theorem ketoaldose_aldehyde_is_numbered_one_but_not_cited :
    KetoaldoseCarbonyl.aldehydic.citedLocant? = none := by
  rfl

@[simp] theorem ketoaldose_non_two_ketone_locant_is_cited (locant : Nat) (h : locant ≠ 2) :
    (KetoaldoseCarbonyl.ketonic locant).citedLocant? = some locant := by
  simp [KetoaldoseCarbonyl.citedLocant?]

end Carbohydrate1996NamedParents

end TetraStereo.OneCenter
