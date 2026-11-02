import TetraStereo.OneCenter.P10NormativeAudit
import TetraStereo.OneCenter.Basic

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent Blue Book P-101 stereochemical semantics

P-101 names natural products through retained stereoparent structures.  The retained name is not
merely a graph label: it can denote the absolute configurations of every stated centre and double
bond.  This module records that denotation and the rules for changing, preserving, or globally
inverting it independently of any production name renderer.

The actual Table 10.1/Appendix 3 structure inventory is deliberately a parameter.  Until those
figures have been transcribed, this file supplies partial clause semantics rather than pretending
that a string-to-structure table is complete.
-/

namespace BlueBookP101

/-! ## Retained stereoparent denotation -/

inductive PlaneOrientation where
  | below
  | above
  | unknown
  deriving DecidableEq, Repr

inductive AlphaBetaXi where
  | alpha
  | beta
  | xi
  deriving DecidableEq, Repr

def orientationDescriptor : PlaneOrientation → AlphaBetaXi
  | .below => .alpha
  | .above => .beta
  | .unknown => .xi

@[simp] theorem below_is_alpha : orientationDescriptor .below = .alpha := rfl
@[simp] theorem above_is_beta : orientationDescriptor .above = .beta := rfl
@[simp] theorem unknown_is_xi : orientationDescriptor .unknown = .xi := rfl

inductive CenterConfiguration where
  | alpha
  | beta
  | xi
  | R
  | S
  deriving DecidableEq, Repr

namespace CenterConfiguration

/-- Configurational inversion.  `xi` records unknown orientation, so inversion cannot make it
known and leaves the information state unchanged. -/
def inverted : CenterConfiguration → CenterConfiguration
  | .alpha => .beta
  | .beta => .alpha
  | .xi => .xi
  | .R => .S
  | .S => .R

@[simp] theorem inverted_involutive (configuration : CenterConfiguration) :
    configuration.inverted.inverted = configuration := by
  cases configuration <;> rfl

end CenterConfiguration

inductive DoubleBondConfiguration where
  | E
  | Z
  | cis
  | trans
  | unknown
  deriving DecidableEq, Repr

namespace DoubleBondConfiguration

/-! Reflection does not interchange ordinary `E/Z` or `cis/trans` geometry. -/
def underMirror (configuration : DoubleBondConfiguration) : DoubleBondConfiguration :=
  configuration

@[simp] theorem underMirror_eq (configuration : DoubleBondConfiguration) :
    configuration.underMirror = configuration :=
  rfl

end DoubleBondConfiguration

/-- Configuration denoted by one retained stereoparent. -/
structure StereoparentConfiguration (CenterLocant BondLocant : Type*) where
  centers : CenterLocant → Option CenterConfiguration
  doubleBonds : BondLocant → Option DoubleBondConfiguration

def StereoparentConfiguration.inverted {CenterLocant BondLocant : Type*}
    (configuration : StereoparentConfiguration CenterLocant BondLocant) :
    StereoparentConfiguration CenterLocant BondLocant where
  centers locant := (configuration.centers locant).map CenterConfiguration.inverted
  doubleBonds locant :=
    (configuration.doubleBonds locant).map DoubleBondConfiguration.underMirror

@[simp] theorem stereoparentConfiguration_inverted_involutive
    {CenterLocant BondLocant : Type*}
    (configuration : StereoparentConfiguration CenterLocant BondLocant) :
    configuration.inverted.inverted = configuration := by
  cases configuration
  simp only [StereoparentConfiguration.inverted]
  congr <;> funext locant <;>
    simp [Option.map_map, Function.comp_def]

structure RetainedStereoparent (CenterLocant BondLocant : Type*) where
  name : String
  configuration : StereoparentConfiguration CenterLocant BondLocant

/-- The independent Table 10.1/Appendix 3 authority boundary. -/
structure RetainedStereoparentInventory (CenterLocant BondLocant : Type*) where
  entries : List (RetainedStereoparent CenterLocant BondLocant)
  namesUnique : (entries.map RetainedStereoparent.name).Nodup
  configurationOf : String → Option (StereoparentConfiguration CenterLocant BondLocant)
  configurationOf_exact : ∀ name configuration,
    configurationOf name = some configuration ↔
      ∃ entry ∈ entries, entry.name = name ∧ entry.configuration = configuration

def RetainedStereoparentInventory.NameDenotes
    {CenterLocant BondLocant : Type*}
    (inventory : RetainedStereoparentInventory CenterLocant BondLocant)
    (name : String) (configuration : StereoparentConfiguration CenterLocant BondLocant) : Prop :=
  inventory.configurationOf name = some configuration

theorem retained_name_determines_at_most_one_configuration
    {CenterLocant BondLocant : Type*}
    (inventory : RetainedStereoparentInventory CenterLocant BondLocant)
    {name : String}
    {first second : StereoparentConfiguration CenterLocant BondLocant}
    (firstDenotation : inventory.NameDenotes name first)
    (secondDenotation : inventory.NameDenotes name second) :
    first = second := by
  exact Option.some.inj (firstDenotation.symm.trans secondDenotation)

/-! ## Numbering and local configuration changes -/

inductive FinalNumberingTieBreak where
  | alphaGroupFirst
  | terminalDoubleBondTransGroupFirst
  deriving DecidableEq, Repr

/-- P-101.2.3.2(e) applies the stereochemical tie breaker only after size and alphanumerical
criteria still leave identical groups tied. -/
structure NumberingTieEvidence where
  sameSkeletalAtomCount : Prop
  alphanumericallyIdentical : Prop
  groupsIdentical : Prop
  attachedToProperlyDrawnStereoparent : Bool
  attachedToAcyclicTerminalDoubleBond : Bool

def finalNumberingTieBreak (evidence : NumberingTieEvidence) :
    Option FinalNumberingTieBreak :=
  if evidence.attachedToProperlyDrawnStereoparent then some .alphaGroupFirst
  else if evidence.attachedToAcyclicTerminalDoubleBond then
    some .terminalDoubleBondTransGroupFirst
  else none

inductive ChangedCenterNotation where
  | alphaBetaXi (descriptor : AlphaBetaXi)
  | epi
  | cipR
  | cipS
  deriving DecidableEq, Repr

def preferredChangedCenterNotation : PlaneOrientation → ChangedCenterNotation
  | .below => .alphaBetaXi .alpha
  | .above => .alphaBetaXi .beta
  | .unknown => .alphaBetaXi .xi

def EpiDenotes (parent changed : CenterConfiguration) : Prop :=
  parent ≠ .xi ∧ changed = parent.inverted

theorem epi_inversion_is_involutive {parent changed : CenterConfiguration}
    (epi : EpiDenotes parent changed) :
    EpiDenotes changed parent := by
  unfold EpiDenotes at *
  rcases epi with ⟨known, rfl⟩
  constructor
  · cases parent <;> simp_all [CenterConfiguration.inverted]
  · simp

inductive CIPFallbackReason where
  | configurationNotSpecifiedByAlphaBeta
  | achiralParent
  | ringOpeningCreatesRotatableChiralPortions
  deriving DecidableEq, Repr

def cipFallbackAllowed : CIPFallbackReason → Bool
  | _ => true

/-! ## Configuration preservation under parent modification -/

def PreservesCentersOutside {Locant : Type*} [DecidableEq Locant]
    (changed : List Locant)
    (before after : Locant → Option CenterConfiguration) : Prop :=
  ∀ locant, locant ∉ changed → after locant = before locant

inductive ParentModificationKind where
  | bondFormation
  | bondCleavage
  | heteroatomReplacementByCarbon
  | mancudeFusion
  | substitutiveDerivative
  | doubleBondModification
  deriving DecidableEq, Repr

structure ParentModification (Locant : Type*) where
  kind : ParentModificationKind
  changedCenters : List Locant
  before : Locant → Option CenterConfiguration
  after : Locant → Option CenterConfiguration

def ParentModification.RetainsParentConfiguration {Locant : Type*}
    [DecidableEq Locant] (modification : ParentModification Locant) : Prop :=
  PreservesCentersOutside modification.changedCenters modification.before modification.after

inductive NewCenterSpecification where
  | alpha
  | beta
  | xi
  | R
  | S
  | indicatedHydrogenAlpha
  | indicatedHydrogenBeta
  deriving DecidableEq, Repr

def bondFormationSpecificationAllowed : NewCenterSpecification → Bool
  | _ => true

/-- Bond cleavage retains the original stereoparent numbering even though the bond has gone. -/
structure BondCleavageSemantics (Locant : Type*) where
  firstEndpoint : Locant
  secondEndpoint : Locant
  originalNumberingRetained : Prop
  terminalValencesSatisfiedByHydrogen : Prop

/-- Replacement by `carba` keeps existing numbering and requires configuration of a newly
stereogenic carbon to be stated by the additional-configuration rules. -/
structure CarbaReplacementSemantics where
  originalNumberingRetained : Prop
  newCarbonIsStereogenic : Bool
  newConfigurationSpecified : Bool

def CarbaReplacementSemantics.WellSpecified
    (replacement : CarbaReplacementSemantics) : Prop :=
  replacement.originalNumberingRetained ∧
    (replacement.newCarbonIsStereogenic → replacement.newConfigurationSpecified)

inductive FusionHydrogenLocantKind where
  | attachedComponentPrimed
  | stereoparentUnprimed
  deriving DecidableEq, Repr

/-- In a choice between a primed attached-component locant and an unprimed stereoparent locant,
P-101.5.1.2 chooses the latter. -/
def preferredFusionHydrogenLocant : FusionHydrogenLocantKind :=
  .stereoparentUnprimed

structure FusedIndicatedHydrogenDescriptor where
  locant : String
  orientation : AlphaBetaXi
  parenthesizedAtFront : Prop

inductive SubstitutionNamePart where
  | prefix
  | suffix
  deriving DecidableEq, Repr

/-- `alpha`, `beta`, or `xi`, with its locant, is immediately in front of the prefix or suffix it
configures. -/
structure SubstituentConfigurationPlacement where
  descriptor : AlphaBetaXi
  locant : String
  configuredPart : SubstitutionNamePart
  immediatelyPrecedesConfiguredPart : Prop

/-! ## Double bonds and whole-molecule scope operators -/

inductive DoubleBondDescriptorAuthority where
  | generalEZ
  | carotenoidCisTrans
  | retinoidCisTrans
  deriving DecidableEq, Repr

def doubleBondDescriptorAuthority
    (isCarotenoid isRetinoid : Bool) : DoubleBondDescriptorAuthority :=
  if isCarotenoid then .carotenoidCisTrans
  else if isRetinoid then .retinoidCisTrans
  else .generalEZ

/-- `all-` has natural-product scope and asserts equality of every stated configuration. -/
def AllConfigurationsIdentical {Configuration : Type*}
    (configurations : List Configuration) : Prop :=
  configurations.Pairwise (· = ·)

theorem allConfigurationsIdentical_of_pairwise
    {Configuration : Type*} (configurations : List Configuration)
    (allEqual : configurations.Pairwise (· = ·)) :
    AllConfigurationsIdentical configurations := by
  exact allEqual

/-- `ent-` inverts every centre in the complete name, including named substituents and centres
whose configurations were only implied by retained names. -/
def entConfiguration {CenterLocant BondLocant : Type*}
    (configuration : StereoparentConfiguration CenterLocant BondLocant) :=
  configuration.inverted

@[simp] theorem ent_ent {CenterLocant BondLocant : Type*}
    (configuration : StereoparentConfiguration CenterLocant BondLocant) :
    entConfiguration (entConfiguration configuration) = configuration :=
  stereoparentConfiguration_inverted_involutive configuration

structure NaturalProductRacemate (Entity : Type*) where
  displayed : Entity
  enantiomer : Entity
  distinct : displayed ≠ enantiomer
  mirrorRelated : Prop
  equimolar : Prop
  racPrefixScopesOverWholeNameIncludingEpi : Prop

def LowestCenterIsAlpha {Locant : Type*} [LinearOrder Locant]
    (centers : List (Locant × CenterConfiguration)) : Prop :=
  ∃ leading ∈ centers,
    leading.2 = .alpha ∧ ∀ center ∈ centers, leading.1 ≤ center.1

/-- P-101.8.3 relative configuration is unchanged by global inversion. -/
def RelativeEquivalent {CenterLocant BondLocant : Type*}
    (left right : StereoparentConfiguration CenterLocant BondLocant) : Prop :=
  right = left ∨ right = left.inverted

theorem relativeEquivalent_inversion
    {CenterLocant BondLocant : Type*}
    (configuration : StereoparentConfiguration CenterLocant BondLocant) :
    RelativeEquivalent configuration configuration.inverted :=
  Or.inr rfl

inductive RelativeNotation where
  | relRS
  | starredRS
  | signedOpticalRotationRel
  deriving DecidableEq, Repr

def RelativeNotation.preferredForPIN : RelativeNotation → Bool
  | .relRS => true
  | .starredRS | .signedOpticalRotationRel => false

/-! ## Clause-to-semantics ownership -/

inductive SemanticDomain where
  | retainedParent
  | numbering
  | changedCenter
  | skeletalModification
  | fusion
  | substitution
  | doubleBond
  | wholeMoleculeScope
  deriving DecidableEq, Repr

def provisionSemanticDomain : BlueBookP10Audit.Provision → Option SemanticDomain
  | .p101StereoparentCommonConfiguration
  | .p101ParentNameImpliesConfiguration
  | .p101ParentAlphaBetaXiOrientation
  | .p101StereoparentTableAndStructures => some .retainedParent
  | .p101StereochemicalNumberingTieBreak => some .numbering
  | .p101ChangedCenterAlphaBetaXi | .p101EpiInversion | .p101RSFallback =>
      some .changedCenter
  | .p101BondFormationConfiguration | .p101BondCleavageConfiguration
  | .p101ReplacementConfiguration => some .skeletalModification
  | .p101FusedIndicatedHydrogenConfiguration => some .fusion
  | .p101SubstituentConfigurationPlacement => some .substitution
  | .p101DoubleBondDescriptors | .p101AllPrefix => some .doubleBond
  | .p101EntInversion | .p101Racemates | .p101RelativeConfiguration
  | .p101AchiralParentAndRingOpeningRS => some .wholeMoleculeScope
  | _ => none

def p101Provisions : List BlueBookP10Audit.Provision :=
  [ .p101StereoparentCommonConfiguration
  , .p101StereochemicalNumberingTieBreak
  , .p101ParentNameImpliesConfiguration
  , .p101ParentAlphaBetaXiOrientation
  , .p101ChangedCenterAlphaBetaXi
  , .p101EpiInversion
  , .p101RSFallback
  , .p101StereoparentTableAndStructures
  , .p101BondFormationConfiguration
  , .p101BondCleavageConfiguration
  , .p101ReplacementConfiguration
  , .p101FusedIndicatedHydrogenConfiguration
  , .p101SubstituentConfigurationPlacement
  , .p101DoubleBondDescriptors
  , .p101AllPrefix
  , .p101EntInversion
  , .p101Racemates
  , .p101RelativeConfiguration
  , .p101AchiralParentAndRingOpeningRS
  ]

@[simp] theorem p101Provisions_length : p101Provisions.length = 19 := by
  rfl

theorem every_p101_provision_has_semantic_domain :
    ∀ provision ∈ p101Provisions, (provisionSemanticDomain provision).isSome := by
  intro provision member
  cases provision <;>
    simp [p101Provisions, provisionSemanticDomain] at member ⊢

end BlueBookP101

end TetraStereo.OneCenter
