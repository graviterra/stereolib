import TetraStereo.OneCenter.IUPACGlobalNonDescriptorSourceMeaningEntryConstructors
import TetraStereo.OneCenter.IUPACNormativeManifest
import TetraStereo.OneCenter.GraphicalRepresentationST2
import TetraStereo.OneCenter.GraphicalRepresentationST3to6
import TetraStereo.KernelOnly

set_option autoImplicit false











namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open IUPACDrawing2006

namespace GlobalNonDescriptorGraphicalSourceMeaning

open GlobalNonDescriptorSourceMeaningConstructor

/-! ## ST-0: general graphical vocabulary -/

structure ST0OverviewObservation where
  bond : ST0.OrientedBond
  endpoint : ST0.Endpoint
  interpretation : ST0.Interpretation
  appliesAtEndpoint : Prop

def ST0OverviewJudged (observation : ST0OverviewObservation) : Prop :=
  observation.interpretation = ST0.preferredInterpretation observation.bond ∧
    (observation.appliesAtEndpoint ↔
      ST0.configurationAppliesAt observation.bond observation.endpoint)

structure ST0PlainBondObservation where
  purpose : ST0.BondPurpose
  style : ST0.BondStyle
  recommendation : ST0.Recommendation
  establishesLocalPlane : Prop
  ringContext : ST0.RingBondContext
  ringRecommendation : ST0.Recommendation

def ST0PlainBondJudged (observation : ST0PlainBondObservation) : Prop :=
  observation.recommendation =
      ST0.nonstereogenicBondRecommendation observation.purpose observation.style ∧
    (observation.establishesLocalPlane ↔ ST0.EstablishesLocalPlane observation.style) ∧
    observation.ringRecommendation =
      ST0.ringBondRecommendation observation.ringContext observation.style

structure ST0HashWedgeObservation where
  depth : ST0.Depth
  style : ST0.BondStyle
  preferredForDepth : Prop
  prohibitedAsConfigurationIndicator : Prop
  conventions : List ST0.HashConvention
  usesOneConvention : Prop
  otherNonHydrogenSubstituents : ℕ
  exceptionalAllowed : Prop

def ST0HashWedgeJudged (observation : ST0HashWedgeObservation) : Prop :=
  (observation.preferredForDepth ↔ ST0.preferredDepthStyle observation.depth observation.style) ∧
    (observation.prohibitedAsConfigurationIndicator ↔
      ST0.ProhibitedAsConfigurationIndicator observation.style) ∧
    (observation.usesOneConvention ↔ ST0.UsesOneHashConvention observation.conventions) ∧
    (observation.exceptionalAllowed ↔
      ST0.exceptionalHashedBondAllowed observation.otherNonHydrogenSubstituents)

structure ST0WavyObservation where
  geometry : ST0.WavyGeometry
  wellFormed : Prop
  perspectiveDiagram : Bool
  emphasizeUnknown : Bool
  style : ST0.BondStyle
  recommendation : ST0.Recommendation

def ST0WavyJudged (observation : ST0WavyObservation) : Prop :=
  (observation.wellFormed ↔ ST0.WellFormedWavy observation.geometry) ∧
    observation.recommendation = ST0.unknownConfigurationRecommendation
      observation.perspectiveDiagram observation.emphasizeUnknown observation.style

structure ST0StereocenterBondObservation where
  unavoidable : Bool
  style : ST0.BondStyle
  isStereobond : Bool
  recommendation : ST0.Recommendation

def ST0StereocenterBondJudged (observation : ST0StereocenterBondObservation) : Prop :=
  observation.isStereobond = ST0.isStereobond observation.style ∧
    observation.recommendation =
      ST0.betweenStereocentersRecommendation observation.unavoidable observation.style

def st0RingContextWitness : ST0.RingBondContext where
  inSimpleOrFusedRing := true
  reasonableAcyclicAlternative := true
  spiroOrSurroundedException := false

def st0Entries : List GlobalNonDescriptorSourceMeaningEntry :=
  [ relationalEntry .drawingOverview
      ({ bond := { style := .solidWedge, narrowEnd := .source }, endpoint := .source,
          interpretation := .depth .abovePlane,
          appliesAtEndpoint := ST0.configurationAppliesAt
            { style := .solidWedge, narrowEnd := .source } .source } : ST0OverviewObservation)
      ST0OverviewJudged (by simp [ST0OverviewJudged, ST0.configurationAppliesAt])
  , relationalEntry .drawingPlainBonds
      ({ purpose := .ordinaryConnectivity, style := .plain, recommendation := .preferred,
          establishesLocalPlane := ST0.EstablishesLocalPlane .plain,
          ringContext := st0RingContextWitness,
          ringRecommendation := .preferred } :
        ST0PlainBondObservation)
      ST0PlainBondJudged (by simp [ST0PlainBondJudged, st0RingContextWitness,
        ST0.nonstereogenicBondRecommendation, ST0.EstablishesLocalPlane,
        ST0.ringBondRecommendation])
  , relationalEntry .drawingHashesDashesWedges
      ({ depth := .abovePlane, style := .solidWedge,
          preferredForDepth := ST0.preferredDepthStyle .abovePlane .solidWedge,
          prohibitedAsConfigurationIndicator := ST0.ProhibitedAsConfigurationIndicator .solidWedge,
          conventions := [.preferredWedged],
          usesOneConvention := ST0.UsesOneHashConvention [.preferredWedged],
          otherNonHydrogenSubstituents := 1,
          exceptionalAllowed := ST0.exceptionalHashedBondAllowed 1 } : ST0HashWedgeObservation)
      ST0HashWedgeJudged (by simp [ST0HashWedgeJudged])
  , relationalEntry .drawingWavyBonds
      ({ geometry := { shape := .rounded, constantAmplitude := true, wedged := false },
          wellFormed := ST0.WellFormedWavy
            { shape := .rounded, constantAmplitude := true, wedged := false },
          perspectiveDiagram := true, emphasizeUnknown := true, style := .wavy,
          recommendation := .preferred } : ST0WavyObservation)
      ST0WavyJudged (by simp [ST0WavyJudged])
  , relationalEntry .drawingStereobondsBetweenStereocenters
      ({ unavoidable := true, style := .solidWedge, isStereobond := true,
          recommendation := .acceptable } : ST0StereocenterBondObservation)
      ST0StereocenterBondJudged (by simp [ST0StereocenterBondJudged,
        ST0.betweenStereocentersRecommendation, ST0.isStereobond])
  , functionalEntry .drawingAsterisks true ST0.asteriskRecommendation
  , functionalEntry .drawingCIPStereodescriptors
      ({ hasGraphicalConfiguration := true, hasCIPLabel := true,
          labelAgreesWithDrawing := true } : ST0.CIPLabelContext)
      ST0.cipLabelRecommendation
  , functionalEntry .drawingDiastereoisomerMixtures
      (ST0.DiastereomerMixtureDepiction.explicitMultipleStructures true)
      ST0.diastereomerMixtureRecommendation
  ]

/-! ## ST-1.1 and ST-1.2: exhaustive tetrahedral tables -/

def fourExplicitProvision : ST1.FourExplicitCase → IUPACNormativeProvision
  | .twoPlainAndOppositeWedgesAdjacent => .drawingTetraFourExplicit01
  | .threePlainAndOneWedge => .drawingTetraFourExplicit02
  | .alternatingTypesAtRightAngles => .drawingTetraFourExplicit03
  | .largePlainGapWithWedgeInside => .drawingTetraFourExplicit04
  | .threeSameWedgesAndOneOther => .drawingTetraFourExplicit05
  | .alternatingTypesAwayFromRightAngles => .drawingTetraFourExplicit06
  | .oppositeWedgeBetweenTwoSameWedges => .drawingTetraFourExplicit07
  | .oppositeWedgeOutsideTwoSameWedges => .drawingTetraFourExplicit08
  | .largeSameWedgeGapWithFourthInside => .drawingTetraFourExplicit09
  | .twoNonadjacentPlainBonds => .drawingTetraFourExplicit10
  | .twoAdjacentPlainAndTwoAdjacentSameWedges => .drawingTetraFourExplicit11
  | .largeGapInOverwedgedPattern => .drawingTetraFourExplicit12
  | .linearAdjacentPlainPair => .drawingTetraFourExplicit13
  | .reflexAdjacentPlainPair => .drawingTetraFourExplicit14
  | .linearNonadjacentPlainPair => .drawingTetraFourExplicit15
  | .largePlainGapWithWedgeOutside => .drawingTetraFourExplicit16
  | .adjacentPairsOfSolidAndHashedWedges => .drawingTetraFourExplicit17
  | .largeSameWedgePairWithOtherPairInside => .drawingTetraFourExplicit18
  | .reflexPlainPairWithWedgesInside => .drawingTetraFourExplicit19
  | .fourWedgesOfOneType => .drawingTetraFourExplicit20

def threeExplicitProvision : ST1.ThreeExplicitCase → IUPACNormativeProvision
  | .twoPlainWithOpposingWedge => .drawingTetraThreeExplicit01
  | .onePlainAndOppositeWedgesWithLargeGap => .drawingTetraThreeExplicit02
  | .wedgeInsideSmallerPlainAngle => .drawingTetraThreeExplicit03
  | .wedgeAtLeastLinearFromAdjacentPlain => .drawingTetraThreeExplicit04
  | .onePlainAndTwoSameWedges => .drawingTetraThreeExplicit05
  | .threeSameWedgesAllGapsAtMostLinear => .drawingTetraThreeExplicit06
  | .twoSameWedgesLargeGapWithOppositeInside => .drawingTetraThreeExplicit07
  | .oppositeWedgesLargeGapWithThirdInside => .drawingTetraThreeExplicit08
  | .threeSameWedgesWithLargeGap => .drawingTetraThreeExplicit09
  | .onePlainBetweenOppositeWedges => .drawingTetraThreeExplicit10
  | .twoSameAndOneOppositeWedgeAllSmallGaps => .drawingTetraThreeExplicit11
  | .linearPlainPairAndOneWedge => .drawingTetraThreeExplicit12

structure FourExplicitRowMeaning where
  recommendation : ST0.Recommendation
  formalMeaning : ST1.FormalMeaning
  largePlainGapRecommendation? :
    Option (ST1.FourExplicitCase.LargePlainGapContext → ST0.Recommendation)

def fourExplicitMeaning (depiction : ST1.FourExplicitCase) : FourExplicitRowMeaning where
  recommendation := ST1.FourExplicitCase.generalRecommendation depiction
  formalMeaning := ST1.FourExplicitCase.formalMeaning depiction
  largePlainGapRecommendation? :=
    if depiction = .largePlainGapWithWedgeInside then
      some ST1.FourExplicitCase.largePlainGapRecommendation
    else none

structure ThreeExplicitRowMeaning where
  recommendation : ST0.Recommendation
  formalMeaning : ST1.FormalMeaning
  insidePlainAngleRecommendation? :
    Option (ST1.ThreeExplicitCase.InsidePlainAngleContext → ST0.Recommendation)
  mayOmitHydrogen? : Option (ST1.ImplicitHydrogenContext → Prop)

def threeExplicitMeaning (depiction : ST1.ThreeExplicitCase) : ThreeExplicitRowMeaning where
  recommendation := ST1.ThreeExplicitCase.generalRecommendation depiction
  formalMeaning := ST1.ThreeExplicitCase.formalMeaning depiction
  insidePlainAngleRecommendation? :=
    if depiction = .wedgeInsideSmallerPlainAngle then
      some ST1.ThreeExplicitCase.insidePlainAngleRecommendation
    else none
  mayOmitHydrogen? :=
    if depiction = .twoPlainWithOpposingWedge then some ST1.MayOmitHydrogen else none

def fourExplicitEntry (depiction : ST1.FourExplicitCase) :
    GlobalNonDescriptorSourceMeaningEntry :=
  rowResultEntry (fourExplicitProvision depiction) depiction fourExplicitMeaning

def threeExplicitEntry (depiction : ST1.ThreeExplicitCase) :
    GlobalNonDescriptorSourceMeaningEntry :=
  rowResultEntry (threeExplicitProvision depiction) depiction threeExplicitMeaning

def st1TetrahedralEntries : List GlobalNonDescriptorSourceMeaningEntry :=
  ST1.FourExplicitCase.all.map fourExplicitEntry ++
    ST1.ThreeExplicitCase.all.map threeExplicitEntry

/-! ## ST-1.3--ST-1.11: special tetrahedral and axial cases -/

def evenCumuleneContext : ST1Special.EvenCumuleneAxialApplicability where
  evenPositiveDoubleBondCount := False
  firstEndSubstituentsDifferent := False
  secondEndSubstituentsDifferent := False

def evenCumuleneDepiction : ST1Special.EvenCumuleneDepiction where
  stereobondsUsedAtBothEnds := false
  allFourSubstituentsExplicit := true
  implicitHydrogenOnlyOnUnlabelledCarbon := false
  threePlainOneStereo := false
  adjacentAtomIsStereogenic := false

structure ST1TwoRingBondObservation where
  depiction : ST1Special.TwoRingBondDepiction
  recommendation : ST0.Recommendation
  placement : ST1Special.TwoRingBondPlacement

def ST1TwoRingBondJudged (observation : ST1TwoRingBondObservation) : Prop :=
  observation.recommendation = ST1Special.twoRingBondRecommendation observation.depiction ∧
    observation.placement.exocyclicBisectsLargerRingAngle = true ∧
    observation.placement.oppositeWedgeAngleApproximately60 = true ∧
    observation.placement.complexSubstituentUsesPlainBond = true

structure ST1ReentrantObservation where
  context : ST1Special.ReentrantContext
  substituentDirectedInward : Bool
  recommendation : ST0.Recommendation
  environment : ST1Special.EnvironmentShape
  style : ST0.BondStyle
  configurationStyle : ST0.BondStyle

def ST1ReentrantJudged (observation : ST1ReentrantObservation) : Prop :=
  observation.recommendation = ST1Special.reentrantRecommendation
      observation.context observation.substituentDirectedInward ∧
    observation.configurationStyle =
      ST1Special.wedgeForSameConfiguration observation.environment observation.style

structure ST1EvenCumuleneObservation where
  applicability : ST1Special.EvenCumuleneAxialApplicability
  axiallyStereogenic : Prop
  depiction : ST1Special.EvenCumuleneDepiction
  recommendation : ST0.Recommendation

def ST1EvenCumuleneJudged (observation : ST1EvenCumuleneObservation) : Prop :=
  (observation.axiallyStereogenic ↔
      ST1Special.IsAxiallyStereogenicEvenCumulene observation.applicability) ∧
    observation.recommendation = ST1Special.evenCumuleneRecommendation observation.depiction

structure ST1HinderedBiarylObservation where
  orthoSubstituentCount : ℕ
  depiction : ST1Special.HinderedBiarylDepiction
  recommendation : ST0.Recommendation

def ST1HinderedBiarylJudged (observation : ST1HinderedBiarylObservation) : Prop :=
  ST1Special.HasHinderedBiarylRotation observation.orthoSubstituentCount ∧
    observation.recommendation = ST1Special.hinderedBiarylRecommendation observation.depiction

structure ST1FischerObservation where
  domain : ST1Special.FischerDomain
  recommendation : ST0.Recommendation
  quarterTurn : ST1Special.QuarterTurn
  rotationEffect : ST1Special.ConfigurationEffect

def ST1FischerJudged (observation : ST1FischerObservation) : Prop :=
  observation.recommendation = ST1Special.fischerRecommendation observation.domain ∧
    observation.rotationEffect = ST1Special.fischerRotationEffect observation.quarterTurn

structure ST1HSymbolObservation where
  symbol : ST1Special.HSymbol
  depth : ST0.Depth
  context : ST1Special.HSymbolContext
  recommendation : ST0.Recommendation

def ST1HSymbolJudged (observation : ST1HSymbolObservation) : Prop :=
  observation.depth = ST1Special.hSymbolDepth observation.symbol ∧
    observation.recommendation = ST1Special.hSymbolRecommendation observation.context

def twoRingPlacementWitness : ST1Special.TwoRingBondPlacement where
  exocyclicBisectsLargerRingAngle := true
  oppositeWedgeAngleApproximately60 := true
  complexSubstituentUsesPlainBond := true

def hSymbolContextWitness : ST1Special.HSymbolContext where
  unsaturatedRingFusionCarbon := true
  exactlyOneExocyclicHydrogen := true
  clarityCritical := false

def st1SpecialEntries : List GlobalNonDescriptorSourceMeaningEntry :=
  [ relationalEntry .drawingRingTwoBonds
      ({ depiction := .oneExocyclicWedgeImplicitHydrogen, recommendation := .preferred,
          placement := twoRingPlacementWitness } :
        ST1TwoRingBondObservation)
      ST1TwoRingBondJudged (by simp [ST1TwoRingBondJudged, twoRingPlacementWitness,
        ST1Special.twoRingBondRecommendation])
  , predicateEntry .drawingRingFusion
      ({ exocyclicSubstituentUsesWedge := true, hydrogenMadeExplicitWhenNeeded := true,
          verticalSmallSubstituentOpposesVerticalFusionBond := true } :
        ST1Special.RingFusionDepiction)
      ST1Special.PreferredRingFusionDepiction (by simp [ST1Special.PreferredRingFusionDepiction])
  , functionalEntry .drawingBridgehead
      ST1Special.BridgeheadDepiction.bridgeWedgedSubstituentPlain
      ST1Special.bridgeheadRecommendation
  , predicateEntry .drawingSpiroFusion
      ({ oneRingPlain := true, otherRingHasSolidAndHashedWedge := true,
          wedgedRingIsSmallerWhenSizesDiffer := true,
          wedgedRingIsDistortedWhenSizesEqual := true,
          avoidsStereobondBetweenStereocenters := true,
          regularFusionBondsRemainPlain := true } : ST1Special.SpiroDepiction)
      ST1Special.PreferredSpiroDepiction (by simp [ST1Special.PreferredSpiroDepiction])
  , relationalEntry .drawingReentrantTetrahedralCenters
      ({ context := .unavoidableWithoutSevereRingDistortion, substituentDirectedInward := true,
          recommendation := .acceptable, environment := .reentrant, style := .solidWedge,
          configurationStyle := .hashedWedge } : ST1ReentrantObservation)
      ST1ReentrantJudged (by simp [ST1ReentrantJudged, ST1Special.reentrantRecommendation,
        ST1Special.wedgeForSameConfiguration])
  , functionalEntry .drawingHigherOrderTetrahedralBonds
      ST1Special.HigherOrderStereoPlacement.wedgeOnSinglyBondedLigand
      ST1Special.higherOrderStereoRecommendation
  , relationalEntry .drawingEvenConsecutiveDoubleBonds
      ({ applicability := evenCumuleneContext, depiction := evenCumuleneDepiction,
          axiallyStereogenic :=
            ST1Special.IsAxiallyStereogenicEvenCumulene evenCumuleneContext,
          recommendation := .preferred } : ST1EvenCumuleneObservation)
      ST1EvenCumuleneJudged (by simp [ST1EvenCumuleneJudged, evenCumuleneContext,
        evenCumuleneDepiction, ST1Special.IsAxiallyStereogenicEvenCumulene,
        ST1Special.evenCumuleneRecommendation])
  , relationalEntry .drawingHinderedBiaryls
      ({ orthoSubstituentCount := 3,
          depiction := .oneRingPlainOtherRingTwoConnectedWedges,
          recommendation := .preferred } : ST1HinderedBiarylObservation)
      ST1HinderedBiarylJudged (by simp [ST1HinderedBiarylJudged,
        ST1Special.HasHinderedBiarylRotation, ST1Special.hinderedBiarylRecommendation])
  , relationalEntry .drawingFischerProjections
      ({ domain := .carbohydrateOrDerivative, recommendation := .acceptable,
          quarterTurn := .ninety, rotationEffect := .enantiomer } : ST1FischerObservation)
      ST1FischerJudged (by simp [ST1FischerJudged, ST1Special.fischerRecommendation,
        ST1Special.fischerRotationEffect])
  , functionalEntry .drawingHaworthProjections
      ({ viewerCertainOfHaworthConvention := true, wedgesPresent := false,
          bottomRingBondBold := true, computerInterchange := false } : ST1Special.HaworthDepiction)
      ST1Special.haworthRecommendation
  , functionalEntry .drawingMillsDepictions PUnit.unit (fun _ => ST1Special.millsRecommendation)
  , relationalEntry .drawingHDotDashCircle
      ({ symbol := .dot, depth := .abovePlane,
          context := hSymbolContextWitness,
          recommendation := .avoid } : ST1HSymbolObservation)
      ST1HSymbolJudged (by simp [ST1HSymbolJudged, hSymbolContextWitness,
        ST1Special.hSymbolDepth, ST1Special.hSymbolRecommendation])
  ]

/-! ## ST-2: coordination-geometry table -/

structure ST2SemanticProfile where
  symbol? : Option String
  fixedCoordination? : Option ℕ
  planar : Prop
  requiresAllLigandsExplicit : Prop
  rejectsCarbonOrNitrogenCenter : Prop
  rejectsCarbonGroupIsoelectronicCenter : Prop
  knownChiralityRequiresStereoBonds : Prop

structure ST2SourceObservation where
  drawing : ST2.DrawingObservation
  preferred : Prop
  profile : ST2SemanticProfile

def geometryProvision : ST2.GeometrySection → IUPACNormativeProvision
  | .linear => .drawingLinearGeometry
  | .angular => .drawingAngularGeometry
  | .tShaped => .drawingTShapedGeometry
  | .trigonalPlanar => .drawingTrigonalPlanarGeometry
  | .trigonalPyramidal => .drawingTrigonalPyramidalGeometry
  | .squarePlanar => .drawingSquarePlanarGeometry
  | .squarePyramidalFour => .drawingSquarePyramidalFourGeometry
  | .seeSaw => .drawingSeeSawGeometry
  | .trigonalBipyramidal => .drawingTrigonalBipyramidalGeometry
  | .squarePyramidalFive => .drawingSquarePyramidalFiveGeometry
  | .octahedral => .drawingOctahedralGeometry
  | .trigonalPrismatic => .drawingTrigonalPrismaticGeometry
  | .higherCoordination => .drawingHigherCoordinationGeometry

def geometryMeaning (geometry : ST2.GeometrySection) : ST2SemanticProfile where
  symbol? := geometry.symbol?
  fixedCoordination? := geometry.fixedCoordination?
  planar := geometry.IsPlanar
  requiresAllLigandsExplicit := geometry.RequiresAllLigandsExplicit
  rejectsCarbonOrNitrogenCenter := geometry.RejectsCarbonOrNitrogenCenter
  rejectsCarbonGroupIsoelectronicCenter := geometry.RejectsCarbonGroupIsoelectronicCenter
  knownChiralityRequiresStereoBonds := geometry.KnownChiralityRequiresStereoBonds

def geometryLigandCount : ST2.GeometrySection → ℕ
  | .linear | .angular => 2
  | .tShaped | .trigonalPlanar | .trigonalPyramidal => 3
  | .squarePlanar | .squarePyramidalFour | .seeSaw => 4
  | .trigonalBipyramidal | .squarePyramidalFive => 5
  | .octahedral | .trigonalPrismatic => 6
  | .higherCoordination => 7

def geometryDrawingProbe (geometry : ST2.GeometrySection) : ST2.DrawingObservation where
  geometry := geometry
  ligandCount := geometryLigandCount geometry
  allLigandsExplicit := true
  centralAtomClearlySingleAndLabeled := true
  centralAtomIsSP2Carbon := false
  centralAtomIsCarbonOrNitrogen := false
  centralAtomIsCarbonGroupIsoelectronic := false
  absoluteChiralityKnown := false
  usesSolidAndHashedStereoBonds := true
  polyhedralSolidWithoutCentralAtom := true
  /- No coordinate recognizer or source figure certificate is available in the declarative ST2
  layer.  The probe truthfully reports that it does not establish that missing premise. -/
  matchesPreferredFigureGeometry := False

def ST2SourceJudged (geometry : ST2.GeometrySection)
    (observation : ST2SourceObservation) : Prop :=
  observation.drawing.geometry = geometry ∧
    (observation.preferred ↔ observation.drawing.Preferred) ∧
    observation.profile.symbol? = geometry.symbol? ∧
    observation.profile.fixedCoordination? = geometry.fixedCoordination? ∧
    (observation.profile.planar ↔ geometry.IsPlanar) ∧
    (observation.profile.requiresAllLigandsExplicit ↔ geometry.RequiresAllLigandsExplicit) ∧
    (observation.profile.rejectsCarbonOrNitrogenCenter ↔
      geometry.RejectsCarbonOrNitrogenCenter) ∧
    (observation.profile.rejectsCarbonGroupIsoelectronicCenter ↔
      geometry.RejectsCarbonGroupIsoelectronicCenter) ∧
    (observation.profile.knownChiralityRequiresStereoBonds ↔
      geometry.KnownChiralityRequiresStereoBonds)

def geometryEntry (geometry : ST2.GeometrySection) : GlobalNonDescriptorSourceMeaningEntry :=
  relationalEntry (geometryProvision geometry)
    ({ drawing := geometryDrawingProbe geometry,
        preferred := (geometryDrawingProbe geometry).Preferred,
        profile := geometryMeaning geometry } : ST2SourceObservation)
    (ST2SourceJudged geometry) ⟨rfl, Iff.rfl,
      rfl, rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

def st2Entries : List GlobalNonDescriptorSourceMeaningEntry :=
  ST2.GeometrySection.all.map geometryEntry

/-! ## ST-3--ST-6: perspective, double-bond, larger-unit, and mixture semantics -/

def oddCumuleneLikeSystem : ST4.OddCumuleneLikeSystem where
  oddPositiveConsecutiveDoubleBondCount := False
  substituentsCoplanar := False
  atLeastOneSubstituentAtEachEnd := False

def planarChiralityObservation : ST5.PlanarChiralityObservation where
  referencePortionPlanarOrNearlyPlanar := False
  referencePortionRotationAsymmetric := False
  otherPortionFixedRelativeToPlane := False
  drawingDistinguishesInPlaneFromOutOfPlane := False

structure ST4OddCumuleneSourceObservation where
  system : ST4.OddCumuleneLikeSystem
  usesDoubleBondDepictionRules : Prop

def ST4OddCumuleneSourceJudged (observation : ST4OddCumuleneSourceObservation) : Prop :=
  observation.usesDoubleBondDepictionRules ↔
    ST4.UsesDoubleBondDepictionRules observation.system

structure ST5PlanarChiralitySourceObservation where
  drawing : ST5.PlanarChiralityObservation
  correct : Prop

def ST5PlanarChiralitySourceJudged
    (observation : ST5PlanarChiralitySourceObservation) : Prop :=
  observation.correct ↔ ST5.CorrectPlanarChiralityDepiction observation.drawing

structure ST3RestrictionsObservation where
  use : ST3.PerspectiveUse
  useRecommendation : ST0.Recommendation
  viewDirection : ST3.ViewDirection
  viewRecommendation : ST0.Recommendation
  crossing : ST3.BondCrossing
  unambiguousCrossing : Prop
  crossingAuthority : ST3.DepthCueAuthority

def ST3RestrictionsJudged (observation : ST3RestrictionsObservation) : Prop :=
  observation.useRecommendation = ST3.perspectiveUseRecommendation observation.use ∧
    observation.viewRecommendation = ST3.viewDirectionRecommendation observation.viewDirection ∧
    (observation.unambiguousCrossing ↔ ST3.UnambiguousCrossing observation.crossing) ∧
    observation.crossingAuthority = ST3.crossingDepthAuthority observation.crossing

structure ST3InterpretationObservation where
  indicator : ST3.PerspectiveCenterIndicator
  statement : ST3.ConfigurationStatement
  whollyUnknownUsesPerspective : Bool
  whollyUnknownRecommendation : ST0.Recommendation

def ST3InterpretationJudged (observation : ST3InterpretationObservation) : Prop :=
  observation.statement = ST3.centerStatement observation.indicator ∧
    observation.whollyUnknownRecommendation =
      ST3.whollyUnknownConfigurationRecommendation observation.whollyUnknownUsesPerspective

structure ST4PlacementObservation where
  applicability : ST4.DoubleBondApplicability
  hasDoubleBondConfiguration : Prop
  placement : ST4.SubstituentPlacement
  recommendation : ST0.Recommendation

def ST4PlacementJudged (observation : ST4PlacementObservation) : Prop :=
  (observation.hasDoubleBondConfiguration ↔
      ST4.HasDoubleBondConfiguration observation.applicability) ∧
    observation.recommendation = ST4.substituentPlacementRecommendation observation.placement

structure ST4UnspecifiedObservation where
  method : ST4.UnspecifiedDoubleBondMethod
  recommendation : ST0.Recommendation
  wavyEnd : ST4.TwoSubstituentWavyEnd
  wavyEndAcceptable : Prop

def ST4UnspecifiedJudged (observation : ST4UnspecifiedObservation) : Prop :=
  observation.recommendation = ST4.unspecifiedRecommendation observation.method ∧
    (observation.wavyEndAcceptable ↔ ST4.AcceptableTwoSubstituentWavyEnd observation.wavyEnd)

def perspectiveUseWitness : ST3.PerspectiveUse where
  conveysSpecificThreeDimensionalConcept := true
  isRingSystem := true
  isBridgedRingSystem := true
  accurateComputerInterpretationRequired := false

def crossingWitness : ST3.BondCrossing where
  backBondDiscontinuous := true
  discontinuityWidthRatio := 2
  orderingConflictsWithVerticalDepthCue := false

def doubleBondApplicabilityWitness : ST4.DoubleBondApplicability where
  rotationHindered := False
  firstEndSupportsConfiguration := False
  secondEndSupportsConfiguration := False

def substituentPlacementWitness : ST4.SubstituentPlacement where
  planarPlainBonds := true
  acyclic := true
  twoSameEndSubstituentsOnSameSide := false
  polycyclicGlobalGeometryRequiresException := false

def twoSubstituentWavyEndWitness : ST4.TwoSubstituentWavyEnd where
  firstIsWavy := true
  secondIsWavy := true
  firstConnectsOtherStereocenter := false
  secondConnectsOtherStereocenter := false

def st3to6Entries : List GlobalNonDescriptorSourceMeaningEntry :=
  [ relationalEntry .drawingPerspectiveRestrictions
      ({ use := perspectiveUseWitness,
          useRecommendation := .preferred, viewDirection := .aboveRight,
          viewRecommendation := .preferred,
          crossing := crossingWitness,
          unambiguousCrossing := ST3.UnambiguousCrossing crossingWitness,
          crossingAuthority := .explicitBondDiscontinuity } : ST3RestrictionsObservation)
      ST3RestrictionsJudged (by simp [ST3RestrictionsJudged, ST3.UnambiguousCrossing,
        perspectiveUseWitness, crossingWitness, ST3.crossingDepthAuthority,
        ST3.perspectiveUseRecommendation, ST3.viewDirectionRecommendation])
  , relationalEntry .drawingPerspectiveInterpretation
      ({ indicator := .none, statement := .absoluteAsDrawn,
          whollyUnknownUsesPerspective := false,
          whollyUnknownRecommendation := .preferred } : ST3InterpretationObservation)
      ST3InterpretationJudged (by simp [ST3InterpretationJudged,
        ST3.whollyUnknownConfigurationRecommendation])
  , functionalEntry .drawingPerspectiveBoldBonds ST3.PerspectiveEmphasisStyle.bold
      ST3.emphasisRecommendation
  , relationalEntry .drawingDoubleBondSubstituentPositioning
      ({ applicability := doubleBondApplicabilityWitness,
          hasDoubleBondConfiguration := ST4.HasDoubleBondConfiguration
            doubleBondApplicabilityWitness,
          placement := substituentPlacementWitness,
          recommendation := .preferred } : ST4PlacementObservation)
      ST4PlacementJudged (by simp [ST4PlacementJudged, ST4.HasDoubleBondConfiguration,
        doubleBondApplicabilityWitness, substituentPlacementWitness,
        ST4.substituentPlacementRecommendation])
  , relationalEntry .drawingOddConsecutiveDoubleBonds
      ({ system := oddCumuleneLikeSystem,
          usesDoubleBondDepictionRules := ST4.UsesDoubleBondDepictionRules
            oddCumuleneLikeSystem } : ST4OddCumuleneSourceObservation)
      ST4OddCumuleneSourceJudged (by simp [ST4OddCumuleneSourceJudged])
  , functionalEntry .drawingRingDoubleBonds
      ({ intendedCis := true, drawnCis := true, ringSize := 6,
          intendedConfigurationMatchesDrawing := true } : ST4.RingDoubleBondDepiction)
      ST4.ringDoubleBondRecommendation
  , relationalEntry .drawingUnspecifiedDoubleBondConfiguration
      ({ method := .linearTwoSubstituentsOnePerEnd, recommendation := .preferred,
          wavyEnd := twoSubstituentWavyEndWitness,
          wavyEndAcceptable := ST4.AcceptableTwoSubstituentWavyEnd
            twoSubstituentWavyEndWitness } : ST4UnspecifiedObservation)
      ST4UnspecifiedJudged (by simp [ST4UnspecifiedJudged,
        twoSubstituentWavyEndWitness, ST4.unspecifiedRecommendation,
        ST4.AcceptableTwoSubstituentWavyEnd])
  , functionalEntry .drawingImplicitDoubleBondSubstituents true
      (fun explicit => (ST4.implicitSubstituentSide, ST4.implicitLabelRecommendation explicit))
  , relationalEntry .drawingPlanarChirality
      ({ drawing := planarChiralityObservation,
          correct := ST5.CorrectPlanarChiralityDepiction planarChiralityObservation } :
        ST5PlanarChiralitySourceObservation)
      ST5PlanarChiralitySourceJudged (by simp [ST5PlanarChiralitySourceJudged])
  , functionalEntry .drawingHelicenes
      ({ terminalSolidWedgePair := true, evenRingInterveningBondBold := true,
          optionalOppositeTerminalHashedPair := false, wedgesAwayFromTermini := false } :
        ST5.HeliceneDepiction)
      ST5.heliceneRecommendation
  , functionalEntry .drawingMobiusBands
      ({ crossingOrderShown := true, optionalWedgesOnlyAtCrossing := false,
          wedgesAgreeWithCrossingOrder := true, wedgesElsewhere := false } : ST5.MobiusDepiction)
      ST5.mobiusRecommendation
  , functionalEntry .drawingMolecularPropellers
      ({ planarBladeCount := 3, wedgesInRingsDirectlyAtRotationBonds := true,
          oppositeRingBondsAlsoWedged := true, interveningRingBondsBold := true,
          configurationOnlyOnRemoteSubstituents := false } : ST5.MolecularPropellerDepiction)
      ST5.propellerRecommendation
  , functionalEntry .drawingMixtureRepresentationGoals PUnit.unit
      (fun _ => ST6.allKnowledgeStates)
  , functionalEntry .drawingAsDrawnAbsoluteConfiguration
      ({ hasStereogenicCenters := true, everyStereogenicCenterHasStereoIndicator := true,
          anyStereochemicalInformation := true } : ST6.BareDiagram)
      ST6.bareDiagramMeaning
  , functionalEntry .drawingMixtureExplanatoryText
      ({ allPresentStereoisomersDrawn := true,
          diagramsSameOrientationOrReflections := true, usesAlphabeticAndOrText := true,
          usesNonalphabeticSeparator := false,
          textClearlyAssociatedWithCorrectDiagram := true } : ST6.MixtureExplanation)
      ST6.mixtureExplanationRecommendation
  , functionalEntry .drawingRacemicAndKnownProportions
      ({ bothEnantiomersExplicitlyDrawn := true, ratioTextPresent := true,
          ratioTextLeftToRightOrderMatchesDiagrams := true, exactRatioKnown := true } :
        ST6.KnownRatioExplanation)
      ST6.knownRatioRecommendation
  , functionalEntry .drawingAvoidRacemateRelativeLabels ST6.StructuralLabel.racemateWord
      ST6.structuralLabelRecommendation
  ]

/-! ## Exact canonical graphical batch -/

def entries : List GlobalNonDescriptorSourceMeaningEntry :=
  st0Entries ++ st1TetrahedralEntries ++ st1SpecialEntries ++ st2Entries ++ st3to6Entries

@[simp] theorem st0_entry_provisions_exact :
    st0Entries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      drawingST0SemanticsSlice := by
  rfl

@[simp] theorem st1Tetrahedral_entry_provisions_exact :
    st1TetrahedralEntries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      drawingST1TetrahedralTableSemanticsSlice := by
  rfl

@[simp] theorem st1Special_entry_provisions_exact :
    st1SpecialEntries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      drawingST1SpecialSemanticsSlice := by
  rfl

@[simp] theorem st2_entry_provisions_exact :
    st2Entries.map GlobalNonDescriptorSourceMeaningEntry.provision = drawingST2SemanticsSlice := by
  rfl

@[simp] theorem st3to6_entry_provisions_exact :
    st3to6Entries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      drawingST3to6SemanticsSlice := by
  rfl

@[simp] theorem entry_provisions_exact :
    entries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      sourceProvisions .graphicalRepresentation2006 := by
  rw [entries, List.map_append, List.map_append, List.map_append, List.map_append,
    st0_entry_provisions_exact, st1Tetrahedral_entry_provisions_exact,
    st1Special_entry_provisions_exact, st2_entry_provisions_exact,
    st3to6_entry_provisions_exact]
  exact allDrawingSemanticsSlices_exact

@[simp] theorem entry_count : entries.length = 82 := by
  rw [← List.length_map (f := GlobalNonDescriptorSourceMeaningEntry.provision),
    entry_provisions_exact]
  exact graphicalProvisionCount

theorem sourceProvisions_nodup :
    (sourceProvisions .graphicalRepresentation2006).Nodup := by
  decide

theorem entry_provisions_nodup :
    (entries.map GlobalNonDescriptorSourceMeaningEntry.provision).Nodup := by
  rw [entry_provisions_exact]
  exact sourceProvisions_nodup

theorem entry_exists_exact (provision : IUPACNormativeProvision) :
    provision ∈ sourceProvisions .graphicalRepresentation2006 ↔
      ∃ entry ∈ entries, entry.provision = provision := by
  rw [← entry_provisions_exact, List.mem_map]

theorem source_scope
    (provision : IUPACNormativeProvision)
    (member : provision ∈ sourceProvisions .graphicalRepresentation2006) :
    provision ∈ globalNonDescriptorProvisions := by
  apply (mem_globalNonDescriptorProvisions_iff provision).2
  have graphicalNegative :
      ∀ candidate ∈ sourceProvisions .graphicalRepresentation2006,
        descriptorAssignmentBearing? candidate = false := by
    decide
  intro bearing
  rw [DescriptorAssignmentBearing, graphicalNegative provision member] at bearing
  exact Bool.false_ne_true bearing

def batch :
    GlobalNonDescriptorSourceMeaningBatch (sourceProvisions .graphicalRepresentation2006) where
  entries := entries
  provisions_exact := entry_provisions_exact
  scope := source_scope

@[simp] theorem batch_entries : batch.entries = entries := rfl

/-- The 82-row result is intentionally a partial source batch.  Its type permits source-ordered
append with independently reviewed neighboring batches, while preventing promotion to the final
2,300-row manifest until literal complete-list equality has been proved. -/
theorem batch_exact :
    batch.provisions_exact = entry_provisions_exact := by
  rfl

end GlobalNonDescriptorGraphicalSourceMeaning

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorGraphicalSourceMeaning.entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorGraphicalSourceMeaning.entry_count
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorGraphicalSourceMeaning.entry_exists_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorGraphicalSourceMeaning.source_scope
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorGraphicalSourceMeaning.batch
