import TetraStereo.OneCenter.Basic

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent IUPAC 2006 graphical semantics: ST-0

This module transcribes the general graphical rules in ST-0.1--ST-0.8.  It does not reuse the
production SMILES or diagram decoder.  Two notions are kept distinct:

* `Interpretation` records what spatial statement an unambiguous graphical object makes; and
* `Recommendation` records whether IUPAC calls that depiction preferred, acceptable, to be
  avoided, not acceptable, or wrong.

That distinction is normative: the source explicitly includes formally interpretable drawings
that are nevertheless not acceptable.
-/

namespace IUPACDrawing2006.ST0

/-- ST-0.1's recommendation vocabulary.  `avoid` covers textual “should be avoided” cases that
are not assigned the stronger printed label “not acceptable”. -/
inductive Recommendation where
  | preferred
  | acceptable
  | avoid
  | notAcceptable
  | wrong
  deriving DecidableEq, Repr

inductive Endpoint where
  | source
  | target
  deriving DecidableEq, Repr

namespace Endpoint

def other : Endpoint → Endpoint
  | .source => .target
  | .target => .source

@[simp] theorem other_involutive (endpoint : Endpoint) : endpoint.other.other = endpoint := by
  cases endpoint <;> rfl

@[simp] theorem other_ne_self (endpoint : Endpoint) : endpoint.other ≠ endpoint := by
  cases endpoint <;> decide

end Endpoint

/-- The full ST-0 bond-style vocabulary, including styles mentioned only to reject or restrict
them.  A wedge's narrow/wide orientation is carried separately by `OrientedBond`. -/
inductive BondStyle where
  | plain
  | solidWedge
  | hashedWedge
  | unwedgedBold
  | unwedgedHashed
  | dashed
  | wavy
  | wedgedWavy
  | hollowWedge
  deriving DecidableEq, Repr

structure OrientedBond where
  style : BondStyle
  /-- Meaningful for wedged styles.  It is explicit so a decoder cannot silently infer the wrong
  stereogenic end from line width or endpoint order. -/
  narrowEnd : Endpoint := .source
  deriving DecidableEq, Repr

inductive Depth where
  | inPlane
  | abovePlane
  | belowPlane
  deriving DecidableEq, Repr

/-- Spatial statement made at the wide endpoint when the narrow endpoint is the configuration
center. -/
inductive Interpretation where
  | depth (wideEndpoint : Depth)
  | unknownConfiguration
  | noConfigurationStatement
  | ambiguous
  deriving DecidableEq, Repr

/-- ST-0.2--ST-0.4 interpretation of the three preferred abstract bond objects. -/
def preferredInterpretation (bond : OrientedBond) : Interpretation :=
  match bond.style with
  | .plain => .depth .inPlane
  | .solidWedge => .depth .abovePlane
  | .hashedWedge => .depth .belowPlane
  | .wavy => .unknownConfiguration
  | .unwedgedBold | .unwedgedHashed | .dashed | .wedgedWavy | .hollowWedge => .ambiguous

@[simp] theorem solidWedge_means_above (narrow : Endpoint) :
    preferredInterpretation { style := .solidWedge, narrowEnd := narrow } =
      .depth .abovePlane :=
  rfl

@[simp] theorem hashedWedge_means_below (narrow : Endpoint) :
    preferredInterpretation { style := .hashedWedge, narrowEnd := narrow } =
      .depth .belowPlane :=
  rfl

/-- ST-0.3: a directional wedge specifies configuration only at its narrow endpoint. -/
def configurationAppliesAt (bond : OrientedBond) (endpoint : Endpoint) : Prop :=
  (bond.style = .solidWedge ∨ bond.style = .hashedWedge) ∧ endpoint = bond.narrowEnd

theorem configuration_does_not_apply_at_wideEnd (bond : OrientedBond) :
    ¬configurationAppliesAt bond bond.narrowEnd.other := by
  intro applies
  exact Endpoint.other_ne_self bond.narrowEnd applies.2

/-! ## ST-0.2: plain bonds -/

inductive BondPurpose where
  | ordinaryConnectivity
  | configuration
  | perspectiveEmphasis
  | prochiralityOrConformation
  | partialOrHydrogenBond
  | unknownConfiguration
  | mixtureEmphasis
  deriving DecidableEq, Repr

/-- General-use status at a nonstereogenic atom.  The exceptional use of wedges to discuss
prochirality or conformation is explicitly represented instead of contradicting the ordinary rule. -/
def nonstereogenicBondRecommendation (purpose : BondPurpose) (style : BondStyle) : Recommendation :=
  match purpose, style with
  | .ordinaryConnectivity, .plain => .preferred
  | .ordinaryConnectivity, _ => .avoid
  | .prochiralityOrConformation, .solidWedge => .acceptable
  | .prochiralityOrConformation, .hashedWedge => .acceptable
  | .perspectiveEmphasis, .unwedgedBold => .acceptable
  | .partialOrHydrogenBond, .dashed => .preferred
  | .unknownConfiguration, .wavy => .acceptable
  | .mixtureEmphasis, .wavy => .acceptable
  | _, _ => .avoid

@[simp] theorem ordinary_nonstereogenic_plain_preferred :
    nonstereogenicBondRecommendation .ordinaryConnectivity .plain = .preferred :=
  rfl

/-- Plain bonds attached to a stereogenic atom establish its local drawing plane. -/
def EstablishesLocalPlane : BondStyle → Prop
  | .plain => True
  | _ => False

/-- ST-0.2 ring exception boundary. -/
structure RingBondContext where
  inSimpleOrFusedRing : Bool
  reasonableAcyclicAlternative : Bool
  spiroOrSurroundedException : Bool
  deriving DecidableEq, Repr

def ringBondRecommendation (context : RingBondContext) (style : BondStyle) : Recommendation :=
  if !context.inSimpleOrFusedRing then .acceptable
  else if style = .plain then .preferred
  else if (style = .solidWedge ∨ style = .hashedWedge) ∧
      context.spiroOrSurroundedException && !context.reasonableAcyclicAlternative then .acceptable
  else .notAcceptable

/-! ## ST-0.3: hashes, dashes, and wedges -/

/-- Preferred depth-carrying style.  Both wedges are read from narrow to wide; only their depth
sense differs. -/
def preferredDepthStyle (depth : Depth) (style : BondStyle) : Prop :=
  match depth, style with
  | .inPlane, .plain => True
  | .abovePlane, .solidWedge => True
  | .belowPlane, .hashedWedge => True
  | _, _ => False

def ProhibitedAsConfigurationIndicator : BondStyle → Prop
  | .unwedgedBold | .dashed => True
  | _ => False

@[simp] theorem unwedgedBold_not_configuration_indicator :
    ProhibitedAsConfigurationIndicator .unwedgedBold :=
  trivial

@[simp] theorem dashed_not_configuration_indicator :
    ProhibitedAsConfigurationIndicator .dashed :=
  trivial

inductive HashConvention where
  | preferredWedged
  | unwedged
  | reverseWedged
  deriving DecidableEq, Repr

/-- ST-0.3 permits no mixture of hashed-bond conventions within one diagram. -/
def UsesOneHashConvention (conventions : List HashConvention) : Prop :=
  ∀ first ∈ conventions, ∀ second ∈ conventions, first = second

theorem singleton_hash_convention_allowed (convention : HashConvention) :
    UsesOneHashConvention [convention] := by
  simp [UsesOneHashConvention]

/-- Exceptional acceptability condition for an unwedged or reverse-direction hashed bond: the
remote atom has at most one other non-hydrogen substituent. -/
def exceptionalHashedBondAllowed (otherNonHydrogenSubstituents : ℕ) : Prop :=
  otherNonHydrogenSubstituents ≤ 1

/-! ## ST-0.4: wavy bonds -/

inductive WaveShape where
  | rounded
  | angular
  deriving DecidableEq, Repr

structure WavyGeometry where
  shape : WaveShape
  constantAmplitude : Bool
  wedged : Bool
  deriving DecidableEq, Repr

/-- Rounded and angular waves are both permitted, but amplitude is constant and a wedged wavy
bond is discouraged. -/
def WellFormedWavy (geometry : WavyGeometry) : Prop :=
  geometry.constantAmplitude = true ∧ geometry.wedged = false

def unknownConfigurationRecommendation
    (perspectiveDiagram emphasizeUnknown : Bool) (style : BondStyle) : Recommendation :=
  if perspectiveDiagram then
    if style = .wavy then .preferred else .wrong
  else if emphasizeUnknown then
    if style = .wavy then .acceptable else .avoid
  else if style = .plain then .preferred
  else if style = .wavy then .acceptable
  else .avoid

@[simp] theorem perspective_unknown_requires_wavy :
    unknownConfigurationRecommendation true true .wavy = .preferred :=
  rfl

/-! ## ST-0.5: stereobonds between stereocenters -/

def isStereobond : BondStyle → Bool
  | .solidWedge | .hashedWedge | .unwedgedBold | .unwedgedHashed
  | .wavy | .wedgedWavy | .hollowWedge => true
  | .plain | .dashed => false

/-- Status of a bond joining two stereogenic centers.  If no alternative exists, a solid wedge is
acceptable and still applies only at its narrow endpoint; a hashed bond remains ambiguous. -/
def betweenStereocentersRecommendation
    (unavoidable : Bool) (style : BondStyle) : Recommendation :=
  if !isStereobond style then .preferred
  else if !unavoidable then .notAcceptable
  else if style = .solidWedge then .acceptable
  else .notAcceptable

@[simp] theorem hashed_between_stereocenters_notAcceptable (unavoidable : Bool) :
    betweenStereocentersRecommendation unavoidable .hashedWedge = .notAcceptable := by
  cases unavoidable <;> rfl

/-! ## ST-0.6: asterisks -/

inductive AsteriskMeaning where
  | stereogenicCenter
  | isotopicLabel
  | excitedState
  deriving DecidableEq, Repr

/-- An asterisk alone is not a configuration statement; accompanying text is required to disambiguate
even its intended non-configurational meaning. -/
def asteriskRecommendation (hasExplanatoryText : Bool) : Recommendation :=
  if hasExplanatoryText then .avoid else .avoid

/-! ## ST-0.7: CIP stereodescriptors in diagrams -/

structure CIPLabelContext where
  hasGraphicalConfiguration : Bool
  hasCIPLabel : Bool
  labelAgreesWithDrawing : Bool
  deriving DecidableEq, Repr

def cipLabelRecommendation (context : CIPLabelContext) : Recommendation :=
  if context.hasCIPLabel && !context.labelAgreesWithDrawing then .wrong
  else if context.hasGraphicalConfiguration && context.hasCIPLabel then .preferred
  else if context.hasGraphicalConfiguration then .acceptable
  else if context.hasCIPLabel then .notAcceptable
  else .acceptable

@[simp] theorem disagreeing_CIP_label_wrong (graphical : Bool) :
    cipLabelRecommendation
      { hasGraphicalConfiguration := graphical
        hasCIPLabel := true
        labelAgreesWithDrawing := false } = .wrong := by
  cases graphical <;> rfl

@[simp] theorem CIP_label_alone_notAcceptable :
    cipLabelRecommendation
      { hasGraphicalConfiguration := false
        hasCIPLabel := true
        labelAgreesWithDrawing := true } = .notAcceptable :=
  rfl

/-! ## ST-0.8: mixtures of diastereoisomers -/

inductive DiastereomerMixtureDepiction where
  | explicitMultipleStructures (hasExplanatoryText : Bool)
  | historicalBondCode
  | singleStructureWithoutExplanation
  deriving DecidableEq, Repr

def diastereomerMixtureRecommendation : DiastereomerMixtureDepiction → Recommendation
  | .explicitMultipleStructures _ => .preferred
  | .historicalBondCode => .avoid
  | .singleStructureWithoutExplanation => .avoid

@[simp] theorem explicit_diastereomer_structures_preferred (withText : Bool) :
    diastereomerMixtureRecommendation (.explicitMultipleStructures withText) = .preferred :=
  rfl

end IUPACDrawing2006.ST0

end TetraStereo.OneCenter
