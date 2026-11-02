import TetraStereo.OneCenter.GraphicalRepresentationST1Special

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent IUPAC 2006 graphical semantics: ST-3--ST-6

This module completes the provision-level declarative vocabulary for the 2006 graphical corpus:
perspective, double-bond-like systems, larger stereogenic units, and configuration/mixture scope.
It does not claim coordinate recognition or production conformance.
-/

namespace IUPACDrawing2006

open ST0

/-! ## ST-3: perspective -/

namespace ST3

inductive ViewDirection where
  | aboveRight
  | aboveLeft
  | below
  deriving DecidableEq, Repr

structure PerspectiveUse where
  conveysSpecificThreeDimensionalConcept : Bool
  isRingSystem : Bool
  isBridgedRingSystem : Bool
  accurateComputerInterpretationRequired : Bool
  deriving DecidableEq, Repr

def perspectiveUseRecommendation (use : PerspectiveUse) : Recommendation :=
  if use.accurateComputerInterpretationRequired then .avoid
  else if !use.conveysSpecificThreeDimensionalConcept then .avoid
  else if use.isBridgedRingSystem then .preferred
  else if use.isRingSystem then .acceptable
  else .notAcceptable

def viewDirectionRecommendation : ViewDirection → Recommendation
  | .aboveRight => .preferred
  | .aboveLeft => .acceptable
  | .below => .notAcceptable

structure BondCrossing where
  backBondDiscontinuous : Bool
  /-- Exact ratio of discontinuity width to ordinary single-bond width. -/
  discontinuityWidthRatio : ℚ
  orderingConflictsWithVerticalDepthCue : Bool

def UnambiguousCrossing (crossing : BondCrossing) : Prop :=
  crossing.backBondDiscontinuous = true ∧ 2 ≤ crossing.discontinuityWidthRatio

/-- Explicit crossing order takes semantic precedence over the conventional “lower is nearer” cue. -/
inductive DepthCueAuthority where
  | explicitBondDiscontinuity
  | verticalPositionConvention
  deriving DecidableEq, Repr

def crossingDepthAuthority (crossing : BondCrossing) : DepthCueAuthority :=
  if crossing.backBondDiscontinuous then .explicitBondDiscontinuity
  else .verticalPositionConvention

inductive PerspectiveCenterIndicator where
  | none
  | solidOrHashedWedgeAgreeingWithPerspective
  | solidOrHashedWedgeConflictingWithPerspective
  | wavy
  deriving DecidableEq, Repr

inductive ConfigurationStatement where
  | absoluteAsDrawn
  | unknown
  | contradictory
  deriving DecidableEq, Repr

/-- ST-3.2: perspectivity itself supplies absolute configuration; wavy overrides it locally. -/
def centerStatement : PerspectiveCenterIndicator → ConfigurationStatement
  | .none | .solidOrHashedWedgeAgreeingWithPerspective => .absoluteAsDrawn
  | .wavy => .unknown
  | .solidOrHashedWedgeConflictingWithPerspective => .contradictory

@[simp] theorem unmarked_perspective_center_is_absolute :
    centerStatement .none = .absoluteAsDrawn :=
  rfl

def whollyUnknownConfigurationRecommendation (usesPerspective : Bool) : Recommendation :=
  if usesPerspective then .notAcceptable else .preferred

inductive PerspectiveEmphasisStyle where
  | none
  | solidWedge
  | bold
  | hashedWedge
  | unwedgedHashed
  deriving DecidableEq, Repr

def emphasisRecommendation : PerspectiveEmphasisStyle → Recommendation
  | .none => .preferred
  | .solidWedge | .bold => .acceptable
  | .hashedWedge | .unwedgedHashed => .notAcceptable

end ST3

/-! ## ST-4: double-bond configuration -/

namespace ST4

structure DoubleBondApplicability where
  rotationHindered : Prop
  firstEndSupportsConfiguration : Prop
  secondEndSupportsConfiguration : Prop

def HasDoubleBondConfiguration (context : DoubleBondApplicability) : Prop :=
  context.rotationHindered ∧
  context.firstEndSupportsConfiguration ∧
  context.secondEndSupportsConfiguration

structure SubstituentPlacement where
  planarPlainBonds : Bool
  acyclic : Bool
  twoSameEndSubstituentsOnSameSide : Bool
  polycyclicGlobalGeometryRequiresException : Bool
  deriving DecidableEq, Repr

def substituentPlacementRecommendation (placement : SubstituentPlacement) : Recommendation :=
  if placement.polycyclicGlobalGeometryRequiresException then .preferred
  else if placement.acyclic && placement.twoSameEndSubstituentsOnSameSide then .notAcceptable
  else if placement.planarPlainBonds then .preferred
  else .acceptable

/-- An omitted hydrogen or lone pair is placed opposite the existing substituent at that end. -/
inductive RelativeSide where
  | same
  | opposite
  deriving DecidableEq, Repr

def implicitSubstituentSide : RelativeSide := .opposite

structure OddCumuleneLikeSystem where
  oddPositiveConsecutiveDoubleBondCount : Prop
  substituentsCoplanar : Prop
  atLeastOneSubstituentAtEachEnd : Prop

def UsesDoubleBondDepictionRules (system : OddCumuleneLikeSystem) : Prop :=
  system.oddPositiveConsecutiveDoubleBondCount ∧
  system.substituentsCoplanar ∧
  system.atLeastOneSubstituentAtEachEnd

structure RingDoubleBondDepiction where
  intendedCis : Bool
  drawnCis : Bool
  ringSize : ℕ
  intendedConfigurationMatchesDrawing : Bool
  deriving DecidableEq, Repr

def ringDoubleBondRecommendation (depiction : RingDoubleBondDepiction) : Recommendation :=
  if !depiction.intendedConfigurationMatchesDrawing then .notAcceptable
  else if depiction.ringSize ≤ 6 && !depiction.drawnCis then .notAcceptable
  else .preferred

inductive UnspecifiedDoubleBondMethod where
  | linearTwoSubstituentsOnePerEnd
  | wavyAdjacentBond (joinsOtherStereocenter : Bool)
  | explicitConfigurationsWithAndOr
  | crossedDoubleBond
  deriving DecidableEq, Repr

def unspecifiedRecommendation : UnspecifiedDoubleBondMethod → Recommendation
  | .linearTwoSubstituentsOnePerEnd => .preferred
  | .wavyAdjacentBond false => .preferred
  | .wavyAdjacentBond true => .notAcceptable
  | .explicitConfigurationsWithAndOr => .preferred
  | .crossedDoubleBond => .notAcceptable

structure TwoSubstituentWavyEnd where
  firstIsWavy : Bool
  secondIsWavy : Bool
  firstConnectsOtherStereocenter : Bool
  secondConnectsOtherStereocenter : Bool
  deriving DecidableEq, Repr

def AcceptableTwoSubstituentWavyEnd (endView : TwoSubstituentWavyEnd) : Prop :=
  (endView.firstConnectsOtherStereocenter = true → endView.firstIsWavy = false) ∧
  (endView.secondConnectsOtherStereocenter = true → endView.secondIsWavy = false) ∧
  ((endView.firstConnectsOtherStereocenter = false ∧
      endView.secondConnectsOtherStereocenter = false) →
    endView.firstIsWavy = true ∧ endView.secondIsWavy = true)

def implicitLabelRecommendation (substituentBondsExplicit : Bool) : Recommendation :=
  if substituentBondsExplicit then .preferred else .acceptable

end ST4

/-! ## ST-5: larger stereogenic units -/

namespace ST5

structure PlanarChiralityObservation where
  referencePortionPlanarOrNearlyPlanar : Prop
  referencePortionRotationAsymmetric : Prop
  otherPortionFixedRelativeToPlane : Prop
  drawingDistinguishesInPlaneFromOutOfPlane : Prop

def CorrectPlanarChiralityDepiction (observation : PlanarChiralityObservation) : Prop :=
  observation.referencePortionPlanarOrNearlyPlanar ∧
  observation.referencePortionRotationAsymmetric ∧
  observation.otherPortionFixedRelativeToPlane ∧
  observation.drawingDistinguishesInPlaneFromOutOfPlane

structure HeliceneDepiction where
  terminalSolidWedgePair : Bool
  evenRingInterveningBondBold : Bool
  optionalOppositeTerminalHashedPair : Bool
  wedgesAwayFromTermini : Bool
  deriving DecidableEq, Repr

def heliceneRecommendation (depiction : HeliceneDepiction) : Recommendation :=
  if depiction.wedgesAwayFromTermini then .notAcceptable
  else if depiction.terminalSolidWedgePair && depiction.evenRingInterveningBondBold then .preferred
  else if depiction.terminalSolidWedgePair then .acceptable
  else .notAcceptable

structure MobiusDepiction where
  crossingOrderShown : Bool
  optionalWedgesOnlyAtCrossing : Bool
  wedgesAgreeWithCrossingOrder : Bool
  wedgesElsewhere : Bool
  deriving DecidableEq, Repr

def mobiusRecommendation (depiction : MobiusDepiction) : Recommendation :=
  if depiction.wedgesElsewhere || !depiction.wedgesAgreeWithCrossingOrder then .notAcceptable
  else if depiction.crossingOrderShown && depiction.optionalWedgesOnlyAtCrossing then .acceptable
  else if depiction.crossingOrderShown then .preferred
  else .notAcceptable

structure MolecularPropellerDepiction where
  planarBladeCount : ℕ
  wedgesInRingsDirectlyAtRotationBonds : Bool
  oppositeRingBondsAlsoWedged : Bool
  interveningRingBondsBold : Bool
  configurationOnlyOnRemoteSubstituents : Bool
  deriving DecidableEq, Repr

def propellerRecommendation (depiction : MolecularPropellerDepiction) : Recommendation :=
  if depiction.planarBladeCount < 3 then .wrong
  else if depiction.configurationOnlyOnRemoteSubstituents then .notAcceptable
  else if depiction.wedgesInRingsDirectlyAtRotationBonds &&
      depiction.oppositeRingBondsAlsoWedged && depiction.interveningRingBondsBold then .preferred
  else if depiction.wedgesInRingsDirectlyAtRotationBonds then .acceptable
  else .notAcceptable

end ST5

/-! ## ST-6: mixtures and unknown absolute configuration -/

namespace ST6

inductive ConfigurationKnowledge where
  | knownAbsolute
  | unknownAbsoluteSingleStereoisomer
  | racemic
  | enantiomericallyEnriched
  | experimentallyUnknown
  | whollyUnspecified
  | knownRelative
  | unknownRelativeDependence
  deriving DecidableEq, Repr

def allKnowledgeStates : List ConfigurationKnowledge :=
  [ .knownAbsolute, .unknownAbsoluteSingleStereoisomer, .racemic
  , .enantiomericallyEnriched, .experimentallyUnknown, .whollyUnspecified
  , .knownRelative, .unknownRelativeDependence
  ]

theorem allKnowledgeStates_nodup : allKnowledgeStates.Nodup := by decide

@[simp] theorem allKnowledgeStates_length : allKnowledgeStates.length = 8 := by decide

structure BareDiagram where
  hasStereogenicCenters : Bool
  everyStereogenicCenterHasStereoIndicator : Bool
  anyStereochemicalInformation : Bool
  deriving DecidableEq, Repr

inductive BareDiagramMeaning where
  | singleStereoisomerAsDrawn
  | partiallySpecifiedConfiguration
  | molecularEntityUnknownConfiguration
  deriving DecidableEq, Repr

/-- ST-6.2 rejects the historical implicit-racemate default. -/
def bareDiagramMeaning (diagram : BareDiagram) : BareDiagramMeaning :=
  if diagram.hasStereogenicCenters && diagram.everyStereogenicCenterHasStereoIndicator then
    .singleStereoisomerAsDrawn
  else if diagram.anyStereochemicalInformation then .partiallySpecifiedConfiguration
  else .molecularEntityUnknownConfiguration

structure MixtureExplanation where
  allPresentStereoisomersDrawn : Bool
  diagramsSameOrientationOrReflections : Bool
  usesAlphabeticAndOrText : Bool
  usesNonalphabeticSeparator : Bool
  textClearlyAssociatedWithCorrectDiagram : Bool
  deriving DecidableEq, Repr

def mixtureExplanationRecommendation (explanation : MixtureExplanation) : Recommendation :=
  if explanation.usesNonalphabeticSeparator then .notAcceptable
  else if explanation.allPresentStereoisomersDrawn &&
      explanation.diagramsSameOrientationOrReflections &&
      explanation.usesAlphabeticAndOrText &&
      explanation.textClearlyAssociatedWithCorrectDiagram then .preferred
  else .notAcceptable

structure KnownRatioExplanation where
  bothEnantiomersExplicitlyDrawn : Bool
  ratioTextPresent : Bool
  ratioTextLeftToRightOrderMatchesDiagrams : Bool
  exactRatioKnown : Bool
  deriving DecidableEq, Repr

def knownRatioRecommendation (explanation : KnownRatioExplanation) : Recommendation :=
  if !explanation.bothEnantiomersExplicitlyDrawn then .notAcceptable
  else if explanation.exactRatioKnown &&
      explanation.ratioTextPresent && explanation.ratioTextLeftToRightOrderMatchesDiagrams then
    .preferred
  else if explanation.exactRatioKnown then .notAcceptable
  else .acceptable

inductive StructuralLabel where
  | explanatoryAndEnantiomerText
  | explanatoryMixtureText
  | racemateWord
  | racAbbreviation
  | relativeWord
  deriving DecidableEq, Repr

def structuralLabelRecommendation : StructuralLabel → Recommendation
  | .explanatoryAndEnantiomerText | .explanatoryMixtureText => .preferred
  | .racemateWord | .racAbbreviation | .relativeWord => .avoid

end ST6

end IUPACDrawing2006

end TetraStereo.OneCenter
