import TetraStereo.OneCenter.GraphicalRepresentationST1Tetrahedral

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent IUPAC 2006 graphical semantics: ST-1.3--ST-1.11

This module transcribes the special tetrahedral and axial depiction rules that follow the exhaustive
ST-1.1/ST-1.2 tables.  It is a declarative reference layer; recognizing these contexts from an
arbitrary molecular graph and drawing remains a separate production-to-reference obligation.
-/

namespace IUPACDrawing2006.ST1Special

open ST0

/-! ## ST-1.3.1: two ring bonds -/

inductive TwoRingBondDepiction where
  | oneExocyclicWedgeImplicitHydrogen
  | twoSimpleExocyclicOppositeWedges
  | complexExocyclicPlainAndOtherWedged
  | other
  deriving DecidableEq, Repr

def twoRingBondRecommendation : TwoRingBondDepiction → Recommendation
  | .oneExocyclicWedgeImplicitHydrogen
  | .twoSimpleExocyclicOppositeWedges
  | .complexExocyclicPlainAndOtherWedged => .preferred
  | .other => .avoid

/-- Geometric placement clauses for ST-1.3.1 are explicit evidence, not inferred from the style. -/
structure TwoRingBondPlacement where
  exocyclicBisectsLargerRingAngle : Bool
  oppositeWedgeAngleApproximately60 : Bool
  complexSubstituentUsesPlainBond : Bool
  deriving DecidableEq, Repr

/-! ## ST-1.3.2: ring-fusion atoms -/

structure RingFusionDepiction where
  exocyclicSubstituentUsesWedge : Bool
  hydrogenMadeExplicitWhenNeeded : Bool
  verticalSmallSubstituentOpposesVerticalFusionBond : Bool
  deriving DecidableEq, Repr

def PreferredRingFusionDepiction (depiction : RingFusionDepiction) : Prop :=
  depiction.exocyclicSubstituentUsesWedge = true ∧
  depiction.hydrogenMadeExplicitWhenNeeded = true ∧
  depiction.verticalSmallSubstituentOpposesVerticalFusionBond = true

/-! ## ST-1.3.3: bridgeheads -/

inductive BridgeheadDepiction where
  | bridgeWedgedSubstituentPlain
  | bridgeAndSubstituentSameWedgeType
  | bridgePlainSubstituentWedged
  | bridgeAndSubstituentOppositeWedgeTypes
  deriving DecidableEq, Repr

def bridgeheadRecommendation : BridgeheadDepiction → Recommendation
  | .bridgeWedgedSubstituentPlain => .preferred
  | .bridgeAndSubstituentSameWedgeType => .acceptable
  | .bridgePlainSubstituentWedged => .notAcceptable
  | .bridgeAndSubstituentOppositeWedgeTypes => .wrong

/-! ## ST-1.3.4: spiro fusions -/

structure SpiroDepiction where
  oneRingPlain : Bool
  otherRingHasSolidAndHashedWedge : Bool
  wedgedRingIsSmallerWhenSizesDiffer : Bool
  wedgedRingIsDistortedWhenSizesEqual : Bool
  avoidsStereobondBetweenStereocenters : Bool
  regularFusionBondsRemainPlain : Bool
  deriving DecidableEq, Repr

def PreferredSpiroDepiction (depiction : SpiroDepiction) : Prop :=
  depiction.oneRingPlain = true ∧
  depiction.otherRingHasSolidAndHashedWedge = true ∧
  depiction.wedgedRingIsSmallerWhenSizesDiffer = true ∧
  depiction.wedgedRingIsDistortedWhenSizesEqual = true ∧
  depiction.avoidsStereobondBetweenStereocenters = true ∧
  depiction.regularFusionBondsRemainPlain = true

/-! ## ST-1.4: re-entrant atoms -/

inductive ReentrantContext where
  | avoidable
  | unavoidableWithoutSevereRingDistortion
  | erythromycinATraditionalOrientation
  | epoxide
  deriving DecidableEq, Repr

def reentrantRecommendation (context : ReentrantContext)
    (substituentDirectedInward : Bool) : Recommendation :=
  match context with
  | .avoidable | .epoxide => .notAcceptable
  | .unavoidableWithoutSevereRingDistortion => .acceptable
  | .erythromycinATraditionalOrientation =>
      if substituentDirectedInward then .acceptable else .notAcceptable

inductive EnvironmentShape where
  | convex
  | reentrant
  deriving DecidableEq, Repr

/-- Moving the same local configuration between convex and re-entrant drawing environments swaps
solid and hashed wedge sense. -/
def wedgeForSameConfiguration : EnvironmentShape → BondStyle → BondStyle
  | .convex, style => style
  | .reentrant, .solidWedge => .hashedWedge
  | .reentrant, .hashedWedge => .solidWedge
  | .reentrant, style => style

@[simp] theorem reentrant_wedge_swap_involutive (style : BondStyle) :
    wedgeForSameConfiguration .reentrant (wedgeForSameConfiguration .reentrant style) = style := by
  cases style <;> rfl

/-! ## ST-1.5: higher-order bonds at tetrahedral centers -/

inductive HigherOrderStereoPlacement where
  | wedgeOnSinglyBondedLigand
  | wedgeOnHigherOrderBond
  deriving DecidableEq, Repr

def higherOrderStereoRecommendation : HigherOrderStereoPlacement → Recommendation
  | .wedgeOnSinglyBondedLigand => .preferred
  | .wedgeOnHigherOrderBond => .acceptable

/-! ## ST-1.6: even consecutive double bonds -/

structure EvenCumuleneAxialApplicability where
  evenPositiveDoubleBondCount : Prop
  firstEndSubstituentsDifferent : Prop
  secondEndSubstituentsDifferent : Prop

def IsAxiallyStereogenicEvenCumulene (context : EvenCumuleneAxialApplicability) : Prop :=
  context.evenPositiveDoubleBondCount ∧
  context.firstEndSubstituentsDifferent ∧
  context.secondEndSubstituentsDifferent

structure EvenCumuleneDepiction where
  stereobondsUsedAtBothEnds : Bool
  allFourSubstituentsExplicit : Bool
  implicitHydrogenOnlyOnUnlabelledCarbon : Bool
  threePlainOneStereo : Bool
  adjacentAtomIsStereogenic : Bool
  deriving DecidableEq, Repr

def evenCumuleneRecommendation (depiction : EvenCumuleneDepiction) : Recommendation :=
  if depiction.stereobondsUsedAtBothEnds then .notAcceptable
  else if depiction.allFourSubstituentsExplicit then .preferred
  else if depiction.threePlainOneStereo then
    if depiction.adjacentAtomIsStereogenic then .acceptable else .notAcceptable
  else if depiction.implicitHydrogenOnlyOnUnlabelledCarbon then .acceptable
  else .avoid

/-! ## ST-1.7: hindered biaryls -/

def HasHinderedBiarylRotation (orthoSubstituentCount : ℕ) : Prop :=
  3 ≤ orthoSubstituentCount

inductive HinderedBiarylDepiction where
  | oneRingPlainOtherRingTwoConnectedWedges
  | singleWedgeDirectlyConnectedToRotatingBond
  | extraRemoteRingWedges
  | onlyRemoteSubstituentWedges
  deriving DecidableEq, Repr

def hinderedBiarylRecommendation : HinderedBiarylDepiction → Recommendation
  | .oneRingPlainOtherRingTwoConnectedWedges => .preferred
  | .singleWedgeDirectlyConnectedToRotatingBond => .acceptable
  | .extraRemoteRingWedges | .onlyRemoteSubstituentWedges => .notAcceptable

/-! ## ST-1.8: Fischer projections -/

inductive FischerDomain where
  | carbohydrateOrDerivative
  | nonCarbohydrateViewerCertain
  | nonCarbohydrateAmbiguous
  | computerInterchange
  deriving DecidableEq, Repr

def fischerRecommendation : FischerDomain → Recommendation
  | .carbohydrateOrDerivative => .acceptable
  | .nonCarbohydrateViewerCertain => .acceptable
  | .nonCarbohydrateAmbiguous | .computerInterchange => .avoid

inductive QuarterTurn where
  | zero
  | ninety
  | oneEighty
  | twoSeventy
  deriving DecidableEq, Repr

inductive ConfigurationEffect where
  | unchanged
  | enantiomer
  deriving DecidableEq, Repr

/-- Fischer projections are the exception to ordinary in-plane rotation invariance. -/
def fischerRotationEffect : QuarterTurn → ConfigurationEffect
  | .zero | .oneEighty => .unchanged
  | .ninety | .twoSeventy => .enantiomer

@[simp] theorem fischer_ninety_degrees_inverts :
    fischerRotationEffect .ninety = .enantiomer :=
  rfl

/-! ## ST-1.9: Haworth projections -/

structure HaworthDepiction where
  viewerCertainOfHaworthConvention : Bool
  wedgesPresent : Bool
  bottomRingBondBold : Bool
  computerInterchange : Bool
  deriving DecidableEq, Repr

def haworthRecommendation (depiction : HaworthDepiction) : Recommendation :=
  if depiction.computerInterchange || !depiction.viewerCertainOfHaworthConvention then .avoid
  else if depiction.wedgesPresent && !depiction.bottomRingBondBold then .notAcceptable
  else .acceptable

/-! ## ST-1.10: Mills depictions -/

/-- A Mills depiction uses the ordinary in-plane conventions and is the preferred alternative to
an ambiguous perspective Haworth projection. -/
def millsRecommendation : Recommendation := .preferred

/-! ## ST-1.11: H-Dot/H-Dash/H-Circle -/

inductive HSymbol where
  | dot
  | dash
  | circle
  deriving DecidableEq, Repr

def hSymbolDepth : HSymbol → ST0.Depth
  | .dot => .abovePlane
  | .dash | .circle => .belowPlane

structure HSymbolContext where
  unsaturatedRingFusionCarbon : Bool
  exactlyOneExocyclicHydrogen : Bool
  clarityCritical : Bool
  deriving DecidableEq, Repr

def hSymbolRecommendation (context : HSymbolContext) : Recommendation :=
  if !context.unsaturatedRingFusionCarbon || !context.exactlyOneExocyclicHydrogen then .wrong
  else if context.clarityCritical then .avoid
  else .avoid

end IUPACDrawing2006.ST1Special

end TetraStereo.OneCenter
