import TetraStereo.OneCenter.GraphicalRepresentationST0

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent IUPAC 2006 graphical semantics: ST-1.1 and ST-1.2

The normative tables claim to exhaust the possible two-dimensional placements of four explicit
and three explicit bonds around a tetrahedral center.  This module gives every table row a stable,
descriptive constructor and records two independent judgments:

* the general-use recommendation printed under the figures; and
* the formal meaning described in the accompanying prose.

Mapping arbitrary 2D coordinates into one of these rows is intentionally a later perception
theorem.  Consequently, this file transcribes the table without pretending that the current
production parser already recognizes it.
-/

namespace IUPACDrawing2006.ST1

open ST0

inductive NonTetrahedralGeometry where
  | trigonalPlanar
  | tShaped
  | squarePlanar
  | squarePyramidalFour
  | squarePyramidalFive
  | seeSaw
  deriving DecidableEq, Repr

inductive FormalMeaning where
  | tetrahedralByConvention
  | tetrahedralUnambiguous
  | tetrahedralContextDependent
  | ambiguous
  | otherGeometry (possibilities : List NonTetrahedralGeometry)
  deriving DecidableEq, Repr

/-! ## ST-1.1: four explicit bonds -/

inductive FourExplicitCase where
  /-- ST-1.1.1 -/ | twoPlainAndOppositeWedgesAdjacent
  /-- ST-1.1.2 -/ | threePlainAndOneWedge
  /-- ST-1.1.3 -/ | alternatingTypesAtRightAngles
  /-- ST-1.1.4 -/ | largePlainGapWithWedgeInside
  /-- ST-1.1.5 -/ | threeSameWedgesAndOneOther
  /-- ST-1.1.6 -/ | alternatingTypesAwayFromRightAngles
  /-- ST-1.1.7 -/ | oppositeWedgeBetweenTwoSameWedges
  /-- ST-1.1.8 -/ | oppositeWedgeOutsideTwoSameWedges
  /-- ST-1.1.9 -/ | largeSameWedgeGapWithFourthInside
  /-- ST-1.1.10 -/ | twoNonadjacentPlainBonds
  /-- ST-1.1.11 -/ | twoAdjacentPlainAndTwoAdjacentSameWedges
  /-- ST-1.1.12 -/ | largeGapInOverwedgedPattern
  /-- ST-1.1.13 -/ | linearAdjacentPlainPair
  /-- ST-1.1.14 -/ | reflexAdjacentPlainPair
  /-- ST-1.1.15 -/ | linearNonadjacentPlainPair
  /-- ST-1.1.16 -/ | largePlainGapWithWedgeOutside
  /-- ST-1.1.17 -/ | adjacentPairsOfSolidAndHashedWedges
  /-- ST-1.1.18 -/ | largeSameWedgePairWithOtherPairInside
  /-- ST-1.1.19 -/ | reflexPlainPairWithWedgesInside
  /-- ST-1.1.20 -/ | fourWedgesOfOneType
  deriving DecidableEq, Repr

namespace FourExplicitCase

def all : List FourExplicitCase :=
  [ .twoPlainAndOppositeWedgesAdjacent
  , .threePlainAndOneWedge
  , .alternatingTypesAtRightAngles
  , .largePlainGapWithWedgeInside
  , .threeSameWedgesAndOneOther
  , .alternatingTypesAwayFromRightAngles
  , .oppositeWedgeBetweenTwoSameWedges
  , .oppositeWedgeOutsideTwoSameWedges
  , .largeSameWedgeGapWithFourthInside
  , .twoNonadjacentPlainBonds
  , .twoAdjacentPlainAndTwoAdjacentSameWedges
  , .largeGapInOverwedgedPattern
  , .linearAdjacentPlainPair
  , .reflexAdjacentPlainPair
  , .linearNonadjacentPlainPair
  , .largePlainGapWithWedgeOutside
  , .adjacentPairsOfSolidAndHashedWedges
  , .largeSameWedgePairWithOtherPairInside
  , .reflexPlainPairWithWedgesInside
  , .fourWedgesOfOneType
  ]

@[simp] theorem mem_all (depiction : FourExplicitCase) : depiction ∈ all := by
  cases depiction <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 20 := by decide

def sourceSection : FourExplicitCase → String
  | .twoPlainAndOppositeWedgesAdjacent => "ST-1.1.1"
  | .threePlainAndOneWedge => "ST-1.1.2"
  | .alternatingTypesAtRightAngles => "ST-1.1.3"
  | .largePlainGapWithWedgeInside => "ST-1.1.4"
  | .threeSameWedgesAndOneOther => "ST-1.1.5"
  | .alternatingTypesAwayFromRightAngles => "ST-1.1.6"
  | .oppositeWedgeBetweenTwoSameWedges => "ST-1.1.7"
  | .oppositeWedgeOutsideTwoSameWedges => "ST-1.1.8"
  | .largeSameWedgeGapWithFourthInside => "ST-1.1.9"
  | .twoNonadjacentPlainBonds => "ST-1.1.10"
  | .twoAdjacentPlainAndTwoAdjacentSameWedges => "ST-1.1.11"
  | .largeGapInOverwedgedPattern => "ST-1.1.12"
  | .linearAdjacentPlainPair => "ST-1.1.13"
  | .reflexAdjacentPlainPair => "ST-1.1.14"
  | .linearNonadjacentPlainPair => "ST-1.1.15"
  | .largePlainGapWithWedgeOutside => "ST-1.1.16"
  | .adjacentPairsOfSolidAndHashedWedges => "ST-1.1.17"
  | .largeSameWedgePairWithOtherPairInside => "ST-1.1.18"
  | .reflexPlainPairWithWedgesInside => "ST-1.1.19"
  | .fourWedgesOfOneType => "ST-1.1.20"

def generalRecommendation : FourExplicitCase → Recommendation
  | .twoPlainAndOppositeWedgesAdjacent | .threePlainAndOneWedge => .preferred
  | .alternatingTypesAtRightAngles => .acceptable
  | .largePlainGapWithWedgeInside | .threeSameWedgesAndOneOther
  | .alternatingTypesAwayFromRightAngles | .oppositeWedgeBetweenTwoSameWedges
  | .oppositeWedgeOutsideTwoSameWedges | .largeSameWedgeGapWithFourthInside
  | .twoNonadjacentPlainBonds | .twoAdjacentPlainAndTwoAdjacentSameWedges
  | .largeGapInOverwedgedPattern => .notAcceptable
  | .linearAdjacentPlainPair | .reflexAdjacentPlainPair | .linearNonadjacentPlainPair
  | .largePlainGapWithWedgeOutside | .adjacentPairsOfSolidAndHashedWedges
  | .largeSameWedgePairWithOtherPairInside | .reflexPlainPairWithWedgesInside
  | .fourWedgesOfOneType => .wrong

def formalMeaning : FourExplicitCase → FormalMeaning
  | .twoPlainAndOppositeWedgesAdjacent | .threePlainAndOneWedge =>
      .tetrahedralByConvention
  | .alternatingTypesAtRightAngles => .tetrahedralUnambiguous
  | .largePlainGapWithWedgeInside => .tetrahedralContextDependent
  | .threeSameWedgesAndOneOther | .alternatingTypesAwayFromRightAngles
  | .oppositeWedgeBetweenTwoSameWedges | .oppositeWedgeOutsideTwoSameWedges =>
      .tetrahedralUnambiguous
  | .largeSameWedgeGapWithFourthInside | .twoNonadjacentPlainBonds
  | .twoAdjacentPlainAndTwoAdjacentSameWedges => .ambiguous
  | .largeGapInOverwedgedPattern =>
      .otherGeometry [.squarePlanar, .squarePyramidalFour, .seeSaw]
  | .linearAdjacentPlainPair => .otherGeometry [.seeSaw]
  | .reflexAdjacentPlainPair => .otherGeometry [.squarePyramidalFive]
  | .linearNonadjacentPlainPair => .otherGeometry [.squarePlanar]
  | .largePlainGapWithWedgeOutside =>
      .otherGeometry [.seeSaw, .squarePyramidalFour]
  | .adjacentPairsOfSolidAndHashedWedges => .otherGeometry [.squarePlanar]
  | .largeSameWedgePairWithOtherPairInside | .reflexPlainPairWithWedgesInside
  | .fourWedgesOfOneType => .otherGeometry [.squarePyramidalFour]

inductive LargePlainGapContext where
  | generalOrAcyclic
  | threePlainBondsInSameSmallFusedRing
  | twoPlainBondsInRingWithExtremeCongestion
  | perspectiveRingIndividualCenter
  deriving DecidableEq, Repr

/-- The explicit exception hierarchy in ST-1.1.4. -/
def largePlainGapRecommendation : LargePlainGapContext → Recommendation
  | .threePlainBondsInSameSmallFusedRing => .preferred
  | .twoPlainBondsInRingWithExtremeCongestion => .acceptable
  | .generalOrAcyclic | .perspectiveRingIndividualCenter => .notAcceptable

end FourExplicitCase

/-! ## ST-1.2: three explicit bonds and an implicit hydrogen/lone pair -/

inductive ThreeExplicitCase where
  /-- ST-1.2.1 -/ | twoPlainWithOpposingWedge
  /-- ST-1.2.2 -/ | onePlainAndOppositeWedgesWithLargeGap
  /-- ST-1.2.3 -/ | wedgeInsideSmallerPlainAngle
  /-- ST-1.2.4 -/ | wedgeAtLeastLinearFromAdjacentPlain
  /-- ST-1.2.5 -/ | onePlainAndTwoSameWedges
  /-- ST-1.2.6 -/ | threeSameWedgesAllGapsAtMostLinear
  /-- ST-1.2.7 -/ | twoSameWedgesLargeGapWithOppositeInside
  /-- ST-1.2.8 -/ | oppositeWedgesLargeGapWithThirdInside
  /-- ST-1.2.9 -/ | threeSameWedgesWithLargeGap
  /-- ST-1.2.10 -/ | onePlainBetweenOppositeWedges
  /-- ST-1.2.11 -/ | twoSameAndOneOppositeWedgeAllSmallGaps
  /-- ST-1.2.12 -/ | linearPlainPairAndOneWedge
  deriving DecidableEq, Repr

namespace ThreeExplicitCase

def all : List ThreeExplicitCase :=
  [ .twoPlainWithOpposingWedge
  , .onePlainAndOppositeWedgesWithLargeGap
  , .wedgeInsideSmallerPlainAngle
  , .wedgeAtLeastLinearFromAdjacentPlain
  , .onePlainAndTwoSameWedges
  , .threeSameWedgesAllGapsAtMostLinear
  , .twoSameWedgesLargeGapWithOppositeInside
  , .oppositeWedgesLargeGapWithThirdInside
  , .threeSameWedgesWithLargeGap
  , .onePlainBetweenOppositeWedges
  , .twoSameAndOneOppositeWedgeAllSmallGaps
  , .linearPlainPairAndOneWedge
  ]

@[simp] theorem mem_all (depiction : ThreeExplicitCase) : depiction ∈ all := by
  cases depiction <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 12 := by decide

def sourceSection : ThreeExplicitCase → String
  | .twoPlainWithOpposingWedge => "ST-1.2.1"
  | .onePlainAndOppositeWedgesWithLargeGap => "ST-1.2.2"
  | .wedgeInsideSmallerPlainAngle => "ST-1.2.3"
  | .wedgeAtLeastLinearFromAdjacentPlain => "ST-1.2.4"
  | .onePlainAndTwoSameWedges => "ST-1.2.5"
  | .threeSameWedgesAllGapsAtMostLinear => "ST-1.2.6"
  | .twoSameWedgesLargeGapWithOppositeInside => "ST-1.2.7"
  | .oppositeWedgesLargeGapWithThirdInside => "ST-1.2.8"
  | .threeSameWedgesWithLargeGap => "ST-1.2.9"
  | .onePlainBetweenOppositeWedges => "ST-1.2.10"
  | .twoSameAndOneOppositeWedgeAllSmallGaps => "ST-1.2.11"
  | .linearPlainPairAndOneWedge => "ST-1.2.12"

def generalRecommendation : ThreeExplicitCase → Recommendation
  | .twoPlainWithOpposingWedge => .preferred
  | .onePlainAndOppositeWedgesWithLargeGap => .acceptable
  | .wedgeInsideSmallerPlainAngle | .wedgeAtLeastLinearFromAdjacentPlain
  | .onePlainAndTwoSameWedges | .threeSameWedgesAllGapsAtMostLinear
  | .twoSameWedgesLargeGapWithOppositeInside | .oppositeWedgesLargeGapWithThirdInside
  | .threeSameWedgesWithLargeGap | .onePlainBetweenOppositeWedges
  | .twoSameAndOneOppositeWedgeAllSmallGaps | .linearPlainPairAndOneWedge =>
      .notAcceptable

def formalMeaning : ThreeExplicitCase → FormalMeaning
  | .twoPlainWithOpposingWedge => .tetrahedralByConvention
  | .onePlainAndOppositeWedgesWithLargeGap => .tetrahedralUnambiguous
  | .wedgeInsideSmallerPlainAngle | .wedgeAtLeastLinearFromAdjacentPlain =>
      .tetrahedralContextDependent
  | .onePlainAndTwoSameWedges | .threeSameWedgesAllGapsAtMostLinear
  | .twoSameWedgesLargeGapWithOppositeInside => .tetrahedralUnambiguous
  | .oppositeWedgesLargeGapWithThirdInside | .threeSameWedgesWithLargeGap => .ambiguous
  | .onePlainBetweenOppositeWedges | .twoSameAndOneOppositeWedgeAllSmallGaps =>
      .otherGeometry [.trigonalPlanar]
  | .linearPlainPairAndOneWedge => .otherGeometry [.tShaped]

inductive InsidePlainAngleContext where
  | general
  | bridgeheadBond
  | perspectiveRingIndividualCenter
  | reentrantNonPerspectiveRing
  deriving DecidableEq, Repr

/-- ST-1.2.3's bridgehead exception and explicit re-entrant/perspective exclusions. -/
def insidePlainAngleRecommendation : InsidePlainAngleContext → Recommendation
  | .bridgeheadBond => .preferred
  | .general | .perspectiveRingIndividualCenter | .reentrantNonPerspectiveRing =>
      .notAcceptable

end ThreeExplicitCase

/-! ## Implicit hydrogen boundary preceding ST-1.2 -/

structure ImplicitHydrogenContext where
  /-- Count at the wide endpoint, including the wedged bond itself, as stated in ST-1.2. -/
  wideEndpointNonHydrogenBondCount : ℕ
  wideEndpointStereogenic : Bool
  wideEndpointUnambiguouslyNonstereogenic : Bool
  deriving DecidableEq, Repr

def MayOmitHydrogen (context : ImplicitHydrogenContext) : Prop :=
  context.wideEndpointStereogenic = false ∧
  (context.wideEndpointNonHydrogenBondCount ≤ 2 ∨
    context.wideEndpointUnambiguouslyNonstereogenic = true)

theorem hydrogen_not_omissible_across_stereobond_to_stereocenter
    (context : ImplicitHydrogenContext)
    (stereogenic : context.wideEndpointStereogenic = true) :
    ¬MayOmitHydrogen context := by
  intro allowed
  have impossible := allowed.1
  rw [stereogenic] at impossible
  cases impossible

end IUPACDrawing2006.ST1

end TetraStereo.OneCenter
