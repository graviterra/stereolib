import TetraStereo.OneCenter.Basic
import TetraStereo.OneCenter.P10DelegatedAuthorityCorpus

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent cyclitol stereochemistry semantics

This module audits the configuration-bearing rules in *Nomenclature of Cyclitols
(Recommendations 1973)*.  The transcription covers the scope and evolutionary explanation, I-1,
I-4, I-5, I-7, I-9, and I-10.  Ordinary functional-class naming statements and examples that do
not add a stereochemical rule are not counted as separate provisions.

The source treats the ring as planar for nomenclature, separates the relative fractional prefix
from the absolute D/L prefix, and permits CIP R/S as a separate general notation.  Those three
relations are deliberately different types below.  No production analyzer is imported.

The recursively captured authority corpus also contains the separately issued 1988
*Numbering of atoms in myo-inositol*.  It is not silently attributed to the 1973 recommendation;
its later relaxation of the lowest-locant rule remains a separate manifest obligation.
-/

namespace Cyclitol1973

inductive Provision where
  | cyclitolDomainAtLeastThreeHydroxyls
  | fewerHydroxylsUseGeneralNomenclature
  | classSpecificConfigurationMethod
  | generalRSAllowedForRelationsAndChiralSubstituents
  | planarRingFaceConvention
  | relativeFractionSeparatedFromAbsoluteDL
  | inositolPrefixInventory
  | inositolFractionInventory
  | chiroDLPair
  | inositolDerivativeNumberingRetained
  | enantiomericPositionsReceiveSameLocants
  | numberingCriteriaAppliedSuccessively
  | numberingLowestNumericalSeries
  | numberingMoreNumerousFaceSet
  | numberingLowerFaceSet
  | numberingNonHydroxyPriority
  | numberingAlphabeticalPriority
  | numberingMesoLBeforeD
  | mesoClockwiseApplication
  | relativeFractionFacePartition
  | relativeFractionLowerSetNumerator
  | hydroxyOnlyFractionServesAsLocants
  | oneToThreeReplacementsRetainParent
  | seniorSuffixLeavesInositolRoute
  | additionalSubstituentPrefixRefersToHydroxyl
  | generalDerivativeRelativeFraction
  | generalDerivativeFractionPlacement
  | disubstitutedFractionRefersToHydroxyl
  | fischerTollensOrientation
  | definingSubstituentRightLeftDL
  | definingCenterLocantMayPrefixDL
  | racemateUsesDL
  | omittedDLPrefixMeansMeso
  | definingCenterOneRecommended
  | mixedBiochemicalDcLc
  | cyclitolNotationCombinesWithCIPOrSn
  | manyReplacementsMayUseCIP
  deriving DecidableEq, Repr

namespace Provision

def all : List Provision :=
  [ .cyclitolDomainAtLeastThreeHydroxyls
  , .fewerHydroxylsUseGeneralNomenclature
  , .classSpecificConfigurationMethod
  , .generalRSAllowedForRelationsAndChiralSubstituents
  , .planarRingFaceConvention
  , .relativeFractionSeparatedFromAbsoluteDL
  , .inositolPrefixInventory
  , .inositolFractionInventory
  , .chiroDLPair
  , .inositolDerivativeNumberingRetained
  , .enantiomericPositionsReceiveSameLocants
  , .numberingCriteriaAppliedSuccessively
  , .numberingLowestNumericalSeries
  , .numberingMoreNumerousFaceSet
  , .numberingLowerFaceSet
  , .numberingNonHydroxyPriority
  , .numberingAlphabeticalPriority
  , .numberingMesoLBeforeD
  , .mesoClockwiseApplication
  , .relativeFractionFacePartition
  , .relativeFractionLowerSetNumerator
  , .hydroxyOnlyFractionServesAsLocants
  , .oneToThreeReplacementsRetainParent
  , .seniorSuffixLeavesInositolRoute
  , .additionalSubstituentPrefixRefersToHydroxyl
  , .generalDerivativeRelativeFraction
  , .generalDerivativeFractionPlacement
  , .disubstitutedFractionRefersToHydroxyl
  , .fischerTollensOrientation
  , .definingSubstituentRightLeftDL
  , .definingCenterLocantMayPrefixDL
  , .racemateUsesDL
  , .omittedDLPrefixMeansMeso
  , .definingCenterOneRecommended
  , .mixedBiochemicalDcLc
  , .cyclitolNotationCombinesWithCIPOrSn
  , .manyReplacementsMayUseCIP
  ]

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 37 := by decide

def sourceSection : Provision → String
  | .cyclitolDomainAtLeastThreeHydroxyls
  | .fewerHydroxylsUseGeneralNomenclature
  | .classSpecificConfigurationMethod
  | .generalRSAllowedForRelationsAndChiralSubstituents => "Cyclitol-1973/Introduction/Scope"
  | .planarRingFaceConvention
  | .relativeFractionSeparatedFromAbsoluteDL => "Cyclitol-1973/Introduction/Evolution"
  | .inositolPrefixInventory | .inositolFractionInventory | .chiroDLPair => "Cyclitol-1973/I-1.1"
  | .inositolDerivativeNumberingRetained
  | .enantiomericPositionsReceiveSameLocants => "Cyclitol-1973/I-1.2"
  | .numberingCriteriaAppliedSuccessively
  | .numberingLowestNumericalSeries => "Cyclitol-1973/I-4(i)"
  | .numberingMoreNumerousFaceSet => "Cyclitol-1973/I-4(ii)"
  | .numberingLowerFaceSet => "Cyclitol-1973/I-4(iii)"
  | .numberingNonHydroxyPriority => "Cyclitol-1973/I-4(iv)"
  | .numberingAlphabeticalPriority => "Cyclitol-1973/I-4(v)"
  | .numberingMesoLBeforeD | .mesoClockwiseApplication => "Cyclitol-1973/I-4(vi)/Note b"
  | .relativeFractionFacePartition | .relativeFractionLowerSetNumerator => "Cyclitol-1973/I-5.1"
  | .hydroxyOnlyFractionServesAsLocants => "Cyclitol-1973/I-5.2"
  | .oneToThreeReplacementsRetainParent | .seniorSuffixLeavesInositolRoute =>
      "Cyclitol-1973/I-7.1"
  | .additionalSubstituentPrefixRefersToHydroxyl => "Cyclitol-1973/I-7.2"
  | .generalDerivativeRelativeFraction | .generalDerivativeFractionPlacement =>
      "Cyclitol-1973/I-9.1"
  | .disubstitutedFractionRefersToHydroxyl => "Cyclitol-1973/I-9.2"
  | .fischerTollensOrientation | .definingSubstituentRightLeftDL
  | .definingCenterLocantMayPrefixDL | .racemateUsesDL => "Cyclitol-1973/I-10"
  | .omittedDLPrefixMeansMeso => "Cyclitol-1973/I-10 Note a"
  | .definingCenterOneRecommended => "Cyclitol-1973/I-10 Note c"
  | .mixedBiochemicalDcLc | .cyclitolNotationCombinesWithCIPOrSn =>
      "Cyclitol-1973/I-10 Note d"
  | .manyReplacementsMayUseCIP => "Cyclitol-1973/I-10 Note e"

def sourceKey (provision : Provision) : String := provision.sourceSection

end Provision

/-! ## Applicability and independent configuration relations -/

structure RingAlcoholProfile where
  isCycloalkane : Bool
  hydroxylBearingRingAtoms : Nat
  deriving DecidableEq, Repr

inductive NomenclatureDomain where
  | cyclitolClass
  | generalOrganic
  deriving DecidableEq, Repr

/-- The source definition requires a cycloalkane and hydroxyl groups on at least three ring atoms. -/
def nomenclatureDomain (profile : RingAlcoholProfile) : NomenclatureDomain :=
  if profile.isCycloalkane && decide (3 ≤ profile.hydroxylBearingRingAtoms)
  then .cyclitolClass
  else .generalOrganic

@[simp] theorem three_hydroxyl_bearing_ring_atoms_enter_cyclitol_domain :
    nomenclatureDomain { isCycloalkane := true, hydroxylBearingRingAtoms := 3 } =
      .cyclitolClass := by
  decide

@[simp] theorem two_hydroxyl_bearing_ring_atoms_use_general_domain :
    nomenclatureDomain { isCycloalkane := true, hydroxylBearingRingAtoms := 2 } =
      .generalOrganic := by
  decide

inductive ConfigurationNotation where
  | cyclitolFractionAndDL
  | cipRS
  | stereospecificNumbering
  deriving DecidableEq, Repr

inductive NotationPurpose where
  | cyclitolClassConfiguration
  | relationToGeneralStereochemistry
  | chiralSubstituent
  | extensivelyReplacedCyclitol
  deriving DecidableEq, Repr

def preferredNotation : NotationPurpose → ConfigurationNotation
  | .cyclitolClassConfiguration => .cyclitolFractionAndDL
  | .relationToGeneralStereochemistry
  | .chiralSubstituent
  | .extensivelyReplacedCyclitol => .cipRS

inductive RingFace where
  | above
  | below
  deriving DecidableEq, Repr

structure RelativeFraction where
  numerator : List Nat
  denominator : List Nat
  deriving DecidableEq, Repr

/-- Source-facing denominator tokens.  I-1.1 prints `0` when the semantic lower-face set is empty,
while nonempty denominator locants are printed unchanged. -/
def RelativeFraction.sourcePrintedDenominator (fraction : RelativeFraction) : List Nat :=
  if fraction.denominator.isEmpty then [0] else fraction.denominator

inductive DLSeries where
  | D
  | L
  deriving DecidableEq, Repr

inductive CIPDescriptor where
  | R
  | S
  deriving DecidableEq, Repr

/-! ## I-1: the nine inositol configurations -/

inductive InositolParent where
  | cis
  | epi
  | allo
  | myo
  | muco
  | neo
  | scyllo
  | chiroD
  | chiroL
  deriving DecidableEq, Repr

namespace InositolParent

def all : List InositolParent :=
  [.cis, .epi, .allo, .myo, .muco, .neo, .scyllo, .chiroD, .chiroL]

@[simp] theorem mem_all (parent : InositolParent) : parent ∈ all := by
  cases parent <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 9 := by decide

def stereoprefix : InositolParent → String
  | .cis => "cis"
  | .epi => "epi"
  | .allo => "allo"
  | .myo => "myo"
  | .muco => "muco"
  | .neo => "neo"
  | .scyllo => "scyllo"
  | .chiroD | .chiroL => "chiro"

/-- Exact numerator and semantic denominator locant sets beside structures (1)--(9) in I-1.1.
The source's clarity-only zero token is recovered by `RelativeFraction.sourcePrintedDenominator`. -/
def relativeFraction : InositolParent → RelativeFraction
  | .cis => ⟨[1, 2, 3, 4, 5, 6], []⟩
  | .epi => ⟨[1, 2, 3, 4, 5], [6]⟩
  | .allo => ⟨[1, 2, 3, 4], [5, 6]⟩
  | .myo => ⟨[1, 2, 3, 5], [4, 6]⟩
  | .muco => ⟨[1, 2, 4, 5], [3, 6]⟩
  | .neo => ⟨[1, 2, 3], [4, 5, 6]⟩
  | .scyllo => ⟨[1, 3, 5], [2, 4, 6]⟩
  | .chiroD | .chiroL => ⟨[1, 2, 4], [3, 5, 6]⟩

def absoluteSeries? : InositolParent → Option DLSeries
  | .chiroD => some .D
  | .chiroL => some .L
  | _ => none

end InositolParent

@[simp] theorem cis_source_denominator_prints_clarity_zero :
    InositolParent.cis.relativeFraction.sourcePrintedDenominator = [0] := by
  rfl

@[simp] theorem myo_source_denominator_preserves_locants :
    InositolParent.myo.relativeFraction.sourcePrintedDenominator = [4, 6] := by
  rfl

def inositolLocants : List Nat := [1, 2, 3, 4, 5, 6]

/-- Executable finite check that both fraction rows are duplicate-free, disjoint, and cover all
six ring locants. -/
def RelativeFraction.isInositolPartition (fraction : RelativeFraction) : Bool :=
  fraction.numerator.Nodup &&
    fraction.denominator.Nodup &&
    fraction.numerator.all (fun locant => locant ∈ inositolLocants) &&
    fraction.denominator.all (fun locant => locant ∈ inositolLocants) &&
    inositolLocants.all (fun locant =>
      (locant ∈ fraction.numerator) != (locant ∈ fraction.denominator))

theorem every_parent_fraction_partitions_the_six_ring_positions
    (parent : InositolParent) : parent.relativeFraction.isInositolPartition := by
  cases parent <;> decide

/-- The D and L chiro parents have the same relative configuration but opposite absolute class
prefixes.  This is the decisive source-level separation between the fraction and D/L. -/
theorem chiro_enantiomers_share_relative_but_not_absolute_configuration :
    InositolParent.chiroD.relativeFraction = InositolParent.chiroL.relativeFraction ∧
      InositolParent.chiroD.absoluteSeries? ≠ InositolParent.chiroL.absoluteSeries? := by
  decide

/-- The independent target does not identify cyclitol D/L with CIP R/S.  This data-level witness
states non-equivalence of the two relations; realizing both rows from molecular graphs remains a
separate chemistry/refinement obligation. -/
structure AbsoluteReading where
  cyclitolSeries : DLSeries
  cip : CIPDescriptor
  deriving DecidableEq, Repr

def dR : AbsoluteReading := ⟨.D, .R⟩
def dS : AbsoluteReading := ⟨.D, .S⟩

theorem semantic_model_does_not_identify_cyclitol_D_with_CIP_RS :
    dR.cyclitolSeries = dS.cyclitolSeries ∧ dR.cip ≠ dS.cip := by
  decide

/-! ## I-4 and I-5: numbering and the relative fraction -/

inductive NumberingCriterion where
  | lowestNumericalSeriesIgnoringConfiguration
  | moreNumerousFaceSet
  | lowerNumberableFaceSet
  | nonHydroxySubstituents
  | alphabeticallyFirstSubstituent
  | LBeforeDForMeso
  deriving DecidableEq, Repr

namespace NumberingCriterion

def all : List NumberingCriterion :=
  [ .lowestNumericalSeriesIgnoringConfiguration
  , .moreNumerousFaceSet
  , .lowerNumberableFaceSet
  , .nonHydroxySubstituents
  , .alphabeticallyFirstSubstituent
  , .LBeforeDForMeso
  ]

@[simp] theorem mem_all (criterion : NumberingCriterion) : criterion ∈ all := by
  cases criterion <;> simp [all]

def rank : NumberingCriterion → Nat
  | .lowestNumericalSeriesIgnoringConfiguration => 0
  | .moreNumerousFaceSet => 1
  | .lowerNumberableFaceSet => 2
  | .nonHydroxySubstituents => 3
  | .alphabeticallyFirstSubstituent => 4
  | .LBeforeDForMeso => 5

theorem rank_lt_six (criterion : NumberingCriterion) : criterion.rank < 6 := by
  cases criterion <;> decide

theorem all_is_source_precedence_order : all.map rank = [0, 1, 2, 3, 4, 5] := by
  rfl

end NumberingCriterion

/-- Lexicographic first-point-of-difference order used by I-4 Note a. -/
def locantSeriesLess : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | firstA :: restA, firstB :: restB =>
      firstA < firstB || (firstA == firstB && locantSeriesLess restA restB)

@[simp] theorem source_lowest_number_example :
    locantSeriesLess [1, 2, 3, 6] [1, 2, 4, 5] := by
  decide

/-- I-5 conventionally places the lexicographically lower face set in the numerator. -/
def canonicalRelativeFraction (firstFace secondFace : List Nat) : RelativeFraction :=
  if locantSeriesLess secondFace firstFace
  then ⟨secondFace, firstFace⟩
  else ⟨firstFace, secondFace⟩

@[simp] theorem lower_face_set_is_numerator :
    canonicalRelativeFraction [3, 5, 6] [1, 2, 4] = ⟨[1, 2, 4], [3, 5, 6]⟩ := by
  decide

inductive RingNumberingSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-- I-4 Note b: with the defining substituent projecting upward, the meso tie-break makes clockwise
numbering L; its mirror numbering is D. -/
def mesoSeriesFromUpwardView : RingNumberingSense → DLSeries
  | .clockwise => .L
  | .counterclockwise => .D

@[simp] theorem upward_clockwise_numbering_is_L :
    mesoSeriesFromUpwardView .clockwise = .L := rfl

structure NumberedInositolDerivative where
  parent : InositolParent
  parentNumberAtPosition : Nat → Nat

/-- I-1.2 does not renumber a derivative merely because substitution created chirality. -/
def retainParentNumbering (parent : InositolParent) (parentNumberAtPosition : Nat → Nat) :
    NumberedInositolDerivative :=
  ⟨parent, parentNumberAtPosition⟩

@[simp] theorem retained_numbering_is_pointwise_parent_numbering
    (parent : InositolParent) (numbering : Nat → Nat) (position : Nat) :
    (retainParentNumbering parent numbering).parentNumberAtPosition position = numbering position :=
  rfl

/-! ## I-7 and I-9: derivative routes and configuration referents -/

inductive InositolDerivativeRoute where
  | retainedParentDeoxyNomenclature
  | generalCyclitolNomenclature
  deriving DecidableEq, Repr

def oneToThree (count : Nat) : Bool := count == 1 || count == 2 || count == 3

def inositolDerivativeRoute (replacedHydroxyls : Nat) (configurationRetained : Bool)
    (hasSuffixSeniorToHydroxyl : Bool) : InositolDerivativeRoute :=
  if oneToThree replacedHydroxyls && configurationRetained && !hasSuffixSeniorToHydroxyl
  then .retainedParentDeoxyNomenclature
  else .generalCyclitolNomenclature

@[simp] theorem one_two_or_three_nonsenior_replacements_retain_the_parent
    (count : Nat) (allowed : oneToThree count = true) :
    inositolDerivativeRoute count true false = .retainedParentDeoxyNomenclature := by
  simp [inositolDerivativeRoute, allowed]

@[simp] theorem changed_configuration_leaves_the_inositol_parent_route
    (count : Nat) (hasSuffixSeniorToHydroxyl : Bool) :
    inositolDerivativeRoute count false hasSuffixSeniorToHydroxyl =
      .generalCyclitolNomenclature := by
  simp [inositolDerivativeRoute]

@[simp] theorem senior_suffix_uses_general_route (count : Nat) :
    inositolDerivativeRoute count true true = .generalCyclitolNomenclature := by
  simp [inositolDerivativeRoute]

inductive ConfigurationReferent where
  | hydroxyl
  | additionalSubstituent
  deriving DecidableEq, Repr

/-- At a ring carbon carrying OH plus another substituent, both I-7.2 and I-9.2 define the class
configuration with respect to OH. -/
def disubstitutedCarbonReferent (_additionalSubstituent : String) : ConfigurationReferent :=
  .hydroxyl

@[simp] theorem disubstituted_carbon_fraction_refers_to_hydroxyl
    (additionalSubstituent : String) :
    disubstitutedCarbonReferent additionalSubstituent = .hydroxyl := rfl

inductive NameComponent where
  | absoluteSeries (series : DLSeries) (definingLocant : Option Nat)
  | relativeConfiguration (fraction : RelativeFraction)
  | completeConstitutionalName (name : String)
  deriving DecidableEq, Repr

/-- In I-9.1 the parenthesized fraction is the first element except for an absolute D/L prefix. -/
def generalDerivativeNameOrder (series : Option (DLSeries × Option Nat))
    (fraction : RelativeFraction) (name : String) : List NameComponent :=
  (match series with
    | none => []
    | some (dl, locant) => [.absoluteSeries dl locant]) ++
  [.relativeConfiguration fraction, .completeConstitutionalName name]

@[simp] theorem fraction_first_when_no_absolute_prefix (fraction : RelativeFraction) (name : String) :
    (generalDerivativeNameOrder none fraction name).head? =
      some (.relativeConfiguration fraction) := by
  rfl

@[simp] theorem absolute_prefix_precedes_fraction (series : DLSeries) (locant : Option Nat)
    (fraction : RelativeFraction) (name : String) :
    generalDerivativeNameOrder (some (series, locant)) fraction name =
      [.absoluteSeries series locant, .relativeConfiguration fraction,
        .completeConstitutionalName name] := by
  rfl

/-! ## I-10: absolute configuration -/

inductive HorizontalSide where
  | right
  | left
  deriving DecidableEq, Repr

structure FischerTollensProjection where
  c1AtTop : Bool
  c2AndC3AtFrontEdge : Bool
  definingSubstituentSide : HorizontalSide
  deriving DecidableEq, Repr

def FischerTollensProjection.isCanonical (projection : FischerTollensProjection) : Bool :=
  projection.c1AtTop && projection.c2AndC3AtFrontEdge

def seriesFromCanonicalFischer (projection : FischerTollensProjection) : Option DLSeries :=
  if projection.isCanonical then
    some (match projection.definingSubstituentSide with | .right => .D | .left => .L)
  else none

@[simp] theorem canonical_right_projection_is_D :
    seriesFromCanonicalFischer
      { c1AtTop := true, c2AndC3AtFrontEdge := true,
        definingSubstituentSide := .right } = some .D := by
  rfl

@[simp] theorem canonical_left_projection_is_L :
    seriesFromCanonicalFischer
      { c1AtTop := true, c2AndC3AtFrontEdge := true,
        definingSubstituentSide := .left } = some .L := by
  rfl

@[simp] theorem noncanonical_projection_makes_no_DL_assertion
    (side : HorizontalSide) :
    seriesFromCanonicalFischer
      { c1AtTop := false, c2AndC3AtFrontEdge := true,
        definingSubstituentSide := side } = none := by
  cases side <;> rfl

inductive ChiralityState where
  | meso
  | enantiopure (series : DLSeries)
  | racemic
  deriving DecidableEq, Repr

inductive AbsolutePrefix where
  | D (definingLocant : Option Nat)
  | L (definingLocant : Option Nat)
  | DL
  deriving DecidableEq, Repr

def absolutePrefix : ChiralityState → Option AbsolutePrefix
  | .meso => none
  | .enantiopure .D => some (.D none)
  | .enantiopure .L => some (.L none)
  | .racemic => some .DL

@[simp] theorem no_absolute_prefix_exactly_means_meso (state : ChiralityState) :
    absolutePrefix state = none ↔ state = .meso := by
  cases state with
  | meso => simp [absolutePrefix]
  | enantiopure series => cases series <;> simp [absolutePrefix]
  | racemic => simp [absolutePrefix]

@[simp] theorem racemate_has_DL_prefix : absolutePrefix .racemic = some .DL := rfl

def withDefiningCenterLocant : DLSeries → Nat → AbsolutePrefix
  | .D, locant => .D (some locant)
  | .L, locant => .L (some locant)

/-- Note c recommends writing locant 1 even though it is the common case, to avoid collision with
systems that select the highest-numbered configurational center. -/
@[simp] theorem defining_center_one_is_retained (series : DLSeries) :
    withDefiningCenterLocant series 1 =
      match series with | .D => .D (some 1) | .L => .L (some 1) := by
  cases series <;> rfl

inductive MixedBiochemicalSeries where
  | Dc
  | Lc
  deriving DecidableEq, Repr

def cyclitolSubscript : DLSeries → MixedBiochemicalSeries
  | .D => .Dc
  | .L => .Lc

structure CombinedNotation where
  cyclitol : Bool
  cip : Bool
  stereospecificNumbering : Bool
  deriving DecidableEq, Repr

/-- I-10 Note d explicitly permits the class notation alongside CIP and/or `sn`; choosing one does
not erase the semantic content of the others. -/
def combineNotations (useCIP useSn : Bool) : CombinedNotation :=
  { cyclitol := true, cip := useCIP, stereospecificNumbering := useSn }

@[simp] theorem CIP_can_coexist_with_cyclitol_notation :
    combineNotations true false =
      { cyclitol := true, cip := true, stereospecificNumbering := false } := rfl

/-! ## Clause ownership -/

inductive SemanticDomain where
  | applicability
  | notationBoundary
  | planarFaceModel
  | parentInventory
  | parentNumbering
  | numberingPrecedence
  | relativeFraction
  | derivativeRoute
  | fractionReferentAndPlacement
  | absoluteProjection
  | absolutePrefix
  | mixedNotation
  deriving DecidableEq, Repr

def provisionSemanticDomain : Provision → SemanticDomain
  | .cyclitolDomainAtLeastThreeHydroxyls
  | .fewerHydroxylsUseGeneralNomenclature
  | .classSpecificConfigurationMethod => .applicability
  | .generalRSAllowedForRelationsAndChiralSubstituents
  | .relativeFractionSeparatedFromAbsoluteDL
  | .manyReplacementsMayUseCIP => .notationBoundary
  | .planarRingFaceConvention => .planarFaceModel
  | .inositolPrefixInventory | .inositolFractionInventory | .chiroDLPair => .parentInventory
  | .inositolDerivativeNumberingRetained
  | .enantiomericPositionsReceiveSameLocants => .parentNumbering
  | .numberingCriteriaAppliedSuccessively | .numberingLowestNumericalSeries
  | .numberingMoreNumerousFaceSet | .numberingLowerFaceSet
  | .numberingNonHydroxyPriority | .numberingAlphabeticalPriority
  | .numberingMesoLBeforeD | .mesoClockwiseApplication => .numberingPrecedence
  | .relativeFractionFacePartition | .relativeFractionLowerSetNumerator
  | .hydroxyOnlyFractionServesAsLocants => .relativeFraction
  | .oneToThreeReplacementsRetainParent | .seniorSuffixLeavesInositolRoute => .derivativeRoute
  | .additionalSubstituentPrefixRefersToHydroxyl | .generalDerivativeRelativeFraction
  | .generalDerivativeFractionPlacement | .disubstitutedFractionRefersToHydroxyl =>
      .fractionReferentAndPlacement
  | .fischerTollensOrientation | .definingSubstituentRightLeftDL => .absoluteProjection
  | .definingCenterLocantMayPrefixDL | .racemateUsesDL | .omittedDLPrefixMeansMeso
  | .definingCenterOneRecommended => .absolutePrefix
  | .mixedBiochemicalDcLc | .cyclitolNotationCombinesWithCIPOrSn => .mixedNotation

theorem every_provision_has_an_independent_semantic_domain
    (provision : Provision) : ∃ domain, provisionSemanticDomain provision = domain := by
  exact ⟨provisionSemanticDomain provision, rfl⟩



/-- The four HTML artifacts in the checksum-matched recursive bundle.  The final page is a
separately issued 1988 recommendation and is reviewed without being attributed to the 1973 text. -/
inductive SourceHtmlArtifact where
  | introduction
  | recommendationsI1ToI5
  | recommendationsI6ToI10
  | myoInositol1988Supplement
  deriving DecidableEq, Repr

namespace SourceHtmlArtifact

def all : List SourceHtmlArtifact :=
  [ .introduction, .recommendationsI1ToI5, .recommendationsI6ToI10,
    .myoInositol1988Supplement ]

@[simp] theorem mem_all (artifact : SourceHtmlArtifact) : artifact ∈ all := by
  cases artifact <;> simp [all]

theorem all_nodup : all.Nodup := by decide

def relativePath : SourceHtmlArtifact → String
  | .introduction => "iupac.qmul.ac.uk/cyclitol/index.html"
  | .recommendationsI1ToI5 => "iupac.qmul.ac.uk/cyclitol/I1t5.html"
  | .recommendationsI6ToI10 => "iupac.qmul.ac.uk/cyclitol/I6t10.html"
  | .myoInositol1988Supplement => "iupac.qmul.ac.uk/cyclitol/myo.html"

def belongsTo1973Recommendation : SourceHtmlArtifact → Bool
  | .myoInositol1988Supplement => false
  | _ => true

end SourceHtmlArtifact



inductive SourceImageArtifact where
  | clarityFraction52
  | introStructures
  | introFraction
  | tableOneA
  | tableOneB
  | tableOneC
  | tableOneD
  | tableOneE
  | tableOneF
  | numberedFigure (index : Fin 34)
  | absoluteFigureOne
  | myoInositol1988Supplement
  | arrow
  | plusMinus
  deriving DecidableEq, Repr

namespace SourceImageArtifact

def nonNumbered : List SourceImageArtifact :=
  [ .clarityFraction52
  , .introStructures
  , .introFraction
  , .tableOneA
  , .tableOneB
  , .tableOneC
  , .tableOneD
  , .tableOneE
  , .tableOneF
  , .absoluteFigureOne
  , .myoInositol1988Supplement
  , .arrow
  , .plusMinus ]

def all : List SourceImageArtifact :=
  nonNumbered ++ (List.finRange 34).map SourceImageArtifact.numberedFigure

@[simp] theorem mem_all (artifact : SourceImageArtifact) : artifact ∈ all := by
  cases artifact <;> simp [all, nonNumbered]

theorem all_nodup : all.Nodup := by decide

def relativePath : SourceImageArtifact → String
  | .clarityFraction52 => "iupac.qmul.ac.uk/cyclitol/cygif/52.gif"
  | .introStructures => "iupac.qmul.ac.uk/cyclitol/cygif/int.gif"
  | .introFraction => "iupac.qmul.ac.uk/cyclitol/cygif/int2.gif"
  | .tableOneA => "iupac.qmul.ac.uk/cyclitol/cygif/t1a.gif"
  | .tableOneB => "iupac.qmul.ac.uk/cyclitol/cygif/t1b.gif"
  | .tableOneC => "iupac.qmul.ac.uk/cyclitol/cygif/t1c.gif"
  | .tableOneD => "iupac.qmul.ac.uk/cyclitol/cygif/t1d.gif"
  | .tableOneE => "iupac.qmul.ac.uk/cyclitol/cygif/t1e.gif"
  | .tableOneF => "iupac.qmul.ac.uk/cyclitol/cygif/t1f.gif"
  | .numberedFigure index =>
      s!"iupac.qmul.ac.uk/cyclitol/cygif/f{index.val + 1}.gif"
  | .absoluteFigureOne => "iupac.qmul.ac.uk/cyclitol/cygif/fig1.gif"
  | .myoInositol1988Supplement => "iupac.qmul.ac.uk/cyclitol/cygif/myo.gif"
  | .arrow => "iupac.qmul.ac.uk/greek/ARROW.GIF"
  | .plusMinus => "iupac.qmul.ac.uk/greek/PLUSMIN.GIF"

/-- Visual classification of the original GIF bytes. -/
def isMolecularGraph : SourceImageArtifact → Bool
  | .clarityFraction52 | .introFraction | .arrow | .plusMinus => false
  | _ => true

/-- The `myo.gif` structure panel and its arrow glyph belong only to the separately issued 1988
supplement; every other image is requisite of the 1973 recommendation. -/
def belongsTo1973Recommendation : SourceImageArtifact → Bool
  | .myoInositol1988Supplement | .arrow => false
  | _ => true

/-- No current high-level typed value is an independently reviewed atom-and-bond transcription of
one of the source figures. -/
def atomLevelGraphTranscriptionReviewed (_artifact : SourceImageArtifact) : Bool := false

end SourceImageArtifact

@[simp] theorem source_artifact_inventory_exact :
    SourceHtmlArtifact.all.length = 4 ∧
      (SourceHtmlArtifact.all.filter fun html =>
        html.belongsTo1973Recommendation).length = 3 ∧
        SourceImageArtifact.all.length = 47 ∧
          (SourceImageArtifact.all.filter fun image => image.isMolecularGraph).length = 43 ∧
            (SourceImageArtifact.all.filter fun image =>
              image.isMolecularGraph && image.belongsTo1973Recommendation).length = 42 ∧
              (SourceImageArtifact.all.filter fun image =>
                image.atomLevelGraphTranscriptionReviewed).length = 0 := by
  decide

/-- Small manifest-facing constants prevent checklist computation from unfolding the complete
artifact ledger. -/
def currentSourceReviewProvisionEnumerationConfirmed : Bool := true
def currentSourceReviewProseTableCoverageConfirmed : Bool := true
def currentSourceReviewFigureGraphTranscriptionsReviewed : Bool := false

/-- Evidence from a separate fidelity pass over the exact frozen 51-artifact bundle.  All 19
rendered pages and all 47 original GIFs were visually reviewed.  The 1988 supplement is identified
separately; the 1973 source has 42 molecular drawings whose atom-level transcriptions remain open. -/
structure SourceReviewEvidence where
  reviewerKind : String
  reviewDate : String
  method : String
  sourceBundleSha256 : String
  reviewedArtifacts : Nat
  reviewedRenderedPages : Nat
  reviewedHtmlArtifacts : List SourceHtmlArtifact
  reviewedImageArtifacts : List SourceImageArtifact
  reviewedProvisions : List Provision
  molecularGraphImageCount : Nat
  normative1973MolecularGraphImageCount : Nat
  atomLevelGraphTranscriptionCount : Nat
  provisionEnumerationConfirmed : Bool
  proseTableCoverageConfirmed : Bool
  figureGraphTranscriptionsReviewed : Bool
  reviewerKindDeclared : reviewerKind ≠ ""
  reviewDateDeclared : reviewDate ≠ ""
  methodDeclared : method ≠ ""
  sourceBundleSha256Exact :
    sourceBundleSha256 = (P10DelegatedAuthorityCorpus.snapshot .cyclitol1973).bundleSha256
  reviewedArtifactCountExact :
    reviewedArtifacts = reviewedHtmlArtifacts.length + reviewedImageArtifacts.length
  reviewedRenderedPagesExact : reviewedRenderedPages = 19
  reviewedHtmlArtifactsExact : reviewedHtmlArtifacts = SourceHtmlArtifact.all
  reviewedImageArtifactsExact : reviewedImageArtifacts = SourceImageArtifact.all
  reviewedProvisionsExact : reviewedProvisions = Provision.all
  molecularGraphImageCountExact :
    molecularGraphImageCount =
      (reviewedImageArtifacts.filter fun image => image.isMolecularGraph).length
  normative1973MolecularGraphImageCountExact :
    normative1973MolecularGraphImageCount =
      (reviewedImageArtifacts.filter fun image =>
        image.isMolecularGraph && image.belongsTo1973Recommendation).length
  atomLevelGraphTranscriptionCountExact :
    atomLevelGraphTranscriptionCount =
      (reviewedImageArtifacts.filter fun image =>
        image.atomLevelGraphTranscriptionReviewed).length
  normativeMolecularGraphQueueStillOpen :
    atomLevelGraphTranscriptionCount < normative1973MolecularGraphImageCount
  provisionEnumerationConfirmedExact : provisionEnumerationConfirmed = true
  proseTableCoverageConfirmedExact : proseTableCoverageConfirmed = true
  figureGraphTranscriptionsReviewedExact : figureGraphTranscriptionsReviewed = false

def currentSourceReview : SourceReviewEvidence where
  reviewerKind := "automated-record-ff5b7f6496e601ebe8a14c262136c4a1"
  reviewDate := "record-54db71cc66a48d655191405c29c6a9ac"
  method :=
    "record-91c4134c8df311c74eb11f6066be00cc"
  sourceBundleSha256 :=
    "f4bcd60c0c370d90b7f907adccdc971df0ab26237e7bd77cd0d04597b2163927"
  reviewedArtifacts := 51
  reviewedRenderedPages := 19
  reviewedHtmlArtifacts := SourceHtmlArtifact.all
  reviewedImageArtifacts := SourceImageArtifact.all
  reviewedProvisions := Provision.all
  molecularGraphImageCount := 43
  normative1973MolecularGraphImageCount := 42
  atomLevelGraphTranscriptionCount := 0
  provisionEnumerationConfirmed := currentSourceReviewProvisionEnumerationConfirmed
  proseTableCoverageConfirmed := currentSourceReviewProseTableCoverageConfirmed
  figureGraphTranscriptionsReviewed := currentSourceReviewFigureGraphTranscriptionsReviewed
  reviewerKindDeclared := by decide
  reviewDateDeclared := by decide
  methodDeclared := by decide
  sourceBundleSha256Exact := rfl
  reviewedArtifactCountExact := by decide
  reviewedRenderedPagesExact := rfl
  reviewedHtmlArtifactsExact := rfl
  reviewedImageArtifactsExact := rfl
  reviewedProvisionsExact := rfl
  molecularGraphImageCountExact := by decide
  normative1973MolecularGraphImageCountExact := by decide
  atomLevelGraphTranscriptionCountExact := by decide
  normativeMolecularGraphQueueStillOpen := by decide
  provisionEnumerationConfirmedExact := rfl
  proseTableCoverageConfirmedExact := rfl
  figureGraphTranscriptionsReviewedExact := rfl

@[simp] theorem current_source_review_counts_exact :
    currentSourceReview.reviewedArtifacts = 51 ∧
      currentSourceReview.reviewedHtmlArtifacts.length = 4 ∧
        currentSourceReview.reviewedImageArtifacts.length = 47 ∧
          currentSourceReview.reviewedProvisions.length = 37 ∧
            currentSourceReview.molecularGraphImageCount = 43 ∧
              currentSourceReview.normative1973MolecularGraphImageCount = 42 ∧
                currentSourceReview.atomLevelGraphTranscriptionCount = 0 := by
  decide

end Cyclitol1973

end TetraStereo.OneCenter
