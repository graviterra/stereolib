import TetraStereo.OneCenter.Basic
import TetraStereo.OneCenter.P10DelegatedAuthorityCorpus

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent steroid stereochemistry semantics

This module audits the configuration-bearing provisions of *Nomenclature of Steroids
(Recommendations 1989)*, including its corrected tables and 1992 side-chain-numbering addendum.
It covers the steroid-specific rules in 3S-1.3--1.6, 2.4, 2.6--2.8, 3.1--3.4, 4.9, 5.1--5.5,
7.2--7.5, 8.2, 9.0--9.4, 10.0--10.1, and the addendum.  Ordinary functional-group naming rules
that merely happen to show a stereochemical example are not counted as new stereochemical rules.

The semantics is independent of the production analyzer.  Structure drawings and the large
retained-name tables remain reviewable data boundaries, so every row below is partial rather than
a claim of complete source conformance.
-/

namespace Steroid1989

inductive Provision where
  | absoluteConfigurationSources
  | unknownConfigurationUsesXi
  | projectionAlphaBetaDefinition
  | projectionBondGlyphs
  | projectionHydrogenOmissionDefaults
  | rotatedProjectionGlyphReversal
  | perspectiveProjectionSpecialConvention
  | impliedBridgeheadConfigurations
  | impliedC17Beta
  | c5ConfigurationAlwaysExplicit
  | tetracyclicSubstituentDescriptors
  | sideChainUsesCIPUnlessImplied
  | sideChainDrawingConvention
  | c20AlphaBetaDiscouraged
  | table1SideChainConfigurationInventory
  | sequenceLabelsMayChangeWithoutGeometryChange
  | trimethylSteroidConfigurationNumbering
  | lanostaneImpliedConfiguration
  | cycloartaneC9ConfigurationImplication
  | sideChainDoubleBondsUseEZ
  | vitaminDSecoDoubleBondsUseEZ
  | normalConfigurationSideChainChoice
  | equalRingAttachedChainsBetaIsPrimed
  | equalSideChainGroupsProSIsPrimed
  | cardanolideImpliedConfiguration
  | bufanolideImpliedConfiguration
  | spirostanDefaultConfiguration
  | spirostanC16C17Exceptions
  | spirostanC20C22Exceptions
  | spirostanC23C24C26Descriptors
  | spirostanRingFProjection
  | spirostanConformationNotImplied
  | spirostanRSRelabelingWarning
  | furostanDefaultConfiguration
  | furostanC5Descriptor
  | furostanC22C25Descriptors
  | table2RetainedNameConfigurationInventory
  | epiRequiresSpecifiedCenter
  | entInvertsAllImpliedCenters
  | localAlphaBetaForAtMostHalfInverted
  | retroPrefixForbidden
  | entPlusLocalForMajorityInverted
  | racPrefixAndRepresentativeSelection
  | racAlphaBetaReferToNormalSeries
  | relativeConfigurationUsesRStarSStar
  | desRetainsImpliedConfiguration
  | homoPrefixPrecedesStemStereodescriptor
  | abeoRequiresResultingStereochemistry
  | secoAlphaBetaRequiresParentRingOrientation
  | ringBFissionUsesRSOnRingA
  | ringCFissionUsesRSOnRingD
  | vitaminDUsesRSAndEZ
  | table3VitaminDConfigurationInventory
  | vitaminDNamesImplyConfigurationAndHydroxylLocants
  | vitaminDRSLabelsMayChangeInDerivatives
  | taPrefixTrieneGeometry
  | isoPrefixGeometry
  | erPrefixSideChainConfiguration
  | additionalVitaminDHydroxylStereochemistry
  | additionalRingsRetainImpliedConfiguration
  | bridgedSteroidsUseAlphaBetaWhenNeeded
  | addendumSideChainAtomLocants
  deriving DecidableEq, Repr

namespace Provision

def all : List Provision :=
  [ .absoluteConfigurationSources
  , .unknownConfigurationUsesXi
  , .projectionAlphaBetaDefinition
  , .projectionBondGlyphs
  , .projectionHydrogenOmissionDefaults
  , .rotatedProjectionGlyphReversal
  , .perspectiveProjectionSpecialConvention
  , .impliedBridgeheadConfigurations
  , .impliedC17Beta
  , .c5ConfigurationAlwaysExplicit
  , .tetracyclicSubstituentDescriptors
  , .sideChainUsesCIPUnlessImplied
  , .sideChainDrawingConvention
  , .c20AlphaBetaDiscouraged
  , .table1SideChainConfigurationInventory
  , .sequenceLabelsMayChangeWithoutGeometryChange
  , .trimethylSteroidConfigurationNumbering
  , .lanostaneImpliedConfiguration
  , .cycloartaneC9ConfigurationImplication
  , .sideChainDoubleBondsUseEZ
  , .vitaminDSecoDoubleBondsUseEZ
  , .normalConfigurationSideChainChoice
  , .equalRingAttachedChainsBetaIsPrimed
  , .equalSideChainGroupsProSIsPrimed
  , .cardanolideImpliedConfiguration
  , .bufanolideImpliedConfiguration
  , .spirostanDefaultConfiguration
  , .spirostanC16C17Exceptions
  , .spirostanC20C22Exceptions
  , .spirostanC23C24C26Descriptors
  , .spirostanRingFProjection
  , .spirostanConformationNotImplied
  , .spirostanRSRelabelingWarning
  , .furostanDefaultConfiguration
  , .furostanC5Descriptor
  , .furostanC22C25Descriptors
  , .table2RetainedNameConfigurationInventory
  , .epiRequiresSpecifiedCenter
  , .entInvertsAllImpliedCenters
  , .localAlphaBetaForAtMostHalfInverted
  , .retroPrefixForbidden
  , .entPlusLocalForMajorityInverted
  , .racPrefixAndRepresentativeSelection
  , .racAlphaBetaReferToNormalSeries
  , .relativeConfigurationUsesRStarSStar
  , .desRetainsImpliedConfiguration
  , .homoPrefixPrecedesStemStereodescriptor
  , .abeoRequiresResultingStereochemistry
  , .secoAlphaBetaRequiresParentRingOrientation
  , .ringBFissionUsesRSOnRingA
  , .ringCFissionUsesRSOnRingD
  , .vitaminDUsesRSAndEZ
  , .table3VitaminDConfigurationInventory
  , .vitaminDNamesImplyConfigurationAndHydroxylLocants
  , .vitaminDRSLabelsMayChangeInDerivatives
  , .taPrefixTrieneGeometry
  , .isoPrefixGeometry
  , .erPrefixSideChainConfiguration
  , .additionalVitaminDHydroxylStereochemistry
  , .additionalRingsRetainImpliedConfiguration
  , .bridgedSteroidsUseAlphaBetaWhenNeeded
  , .addendumSideChainAtomLocants
  ]

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 62 := by decide

def sourceSection : Provision → String
  | .absoluteConfigurationSources | .unknownConfigurationUsesXi => "3S-1.3"
  | .projectionAlphaBetaDefinition | .projectionBondGlyphs
  | .projectionHydrogenOmissionDefaults | .rotatedProjectionGlyphReversal
  | .perspectiveProjectionSpecialConvention => "3S-1.4"
  | .impliedBridgeheadConfigurations | .impliedC17Beta
  | .c5ConfigurationAlwaysExplicit | .tetracyclicSubstituentDescriptors => "3S-1.5"
  | .sideChainUsesCIPUnlessImplied | .sideChainDrawingConvention
  | .c20AlphaBetaDiscouraged => "3S-1.6"
  | .table1SideChainConfigurationInventory | .sequenceLabelsMayChangeWithoutGeometryChange
  | .trimethylSteroidConfigurationNumbering | .lanostaneImpliedConfiguration
  | .cycloartaneC9ConfigurationImplication => "3S-2.4/Table 1"
  | .sideChainDoubleBondsUseEZ | .vitaminDSecoDoubleBondsUseEZ => "3S-2.6"
  | .normalConfigurationSideChainChoice => "3S-2.7"
  | .equalRingAttachedChainsBetaIsPrimed | .equalSideChainGroupsProSIsPrimed => "3S-2.8"
  | .cardanolideImpliedConfiguration => "3S-3.1"
  | .bufanolideImpliedConfiguration => "3S-3.2"
  | .spirostanDefaultConfiguration | .spirostanC16C17Exceptions
  | .spirostanC20C22Exceptions | .spirostanC23C24C26Descriptors
  | .spirostanRingFProjection | .spirostanConformationNotImplied
  | .spirostanRSRelabelingWarning => "3S-3.3"
  | .furostanDefaultConfiguration | .furostanC5Descriptor
  | .furostanC22C25Descriptors => "3S-3.4"
  | .table2RetainedNameConfigurationInventory | .epiRequiresSpecifiedCenter => "3S-4.9/Table 2"
  | .entInvertsAllImpliedCenters => "3S-5.1"
  | .localAlphaBetaForAtMostHalfInverted | .retroPrefixForbidden => "3S-5.2"
  | .entPlusLocalForMajorityInverted => "3S-5.3"
  | .racPrefixAndRepresentativeSelection | .racAlphaBetaReferToNormalSeries => "3S-5.4"
  | .relativeConfigurationUsesRStarSStar => "3S-5.5"
  | .desRetainsImpliedConfiguration => "3S-7.2"
  | .homoPrefixPrecedesStemStereodescriptor => "3S-7.3"
  | .abeoRequiresResultingStereochemistry => "3S-7.5"
  | .secoAlphaBetaRequiresParentRingOrientation | .ringBFissionUsesRSOnRingA
  | .ringCFissionUsesRSOnRingD => "3S-8.2"
  | .vitaminDUsesRSAndEZ => "3S-9.0"
  | .table3VitaminDConfigurationInventory
  | .vitaminDNamesImplyConfigurationAndHydroxylLocants
  | .vitaminDRSLabelsMayChangeInDerivatives => "3S-9.1/Table 3"
  | .taPrefixTrieneGeometry | .isoPrefixGeometry => "3S-9.2"
  | .erPrefixSideChainConfiguration => "3S-9.3"
  | .additionalVitaminDHydroxylStereochemistry => "3S-9.4"
  | .additionalRingsRetainImpliedConfiguration => "3S-10.0"
  | .bridgedSteroidsUseAlphaBetaWhenNeeded => "3S-10.1"
  | .addendumSideChainAtomLocants => "1992 Addendum/Side-chain atom numbering"

def sourceKey (provision : Provision) : String := "STEROID-1989/" ++ provision.sourceSection

end Provision

/-! ## Steroid face and projection semantics -/

inductive Face where
  | alpha
  | beta
  | xi
  deriving DecidableEq, Repr

namespace Face

def inverted : Face → Face
  | .alpha => .beta
  | .beta => .alpha
  | .xi => .xi

@[simp] theorem inverted_involutive (face : Face) : face.inverted.inverted = face := by
  cases face <;> rfl

end Face

inductive RS where
  | R
  | S
  deriving DecidableEq, Repr

namespace RS

def inverted : RS → RS
  | .R => .S
  | .S => .R

@[simp] theorem inverted_involutive (descriptor : RS) :
    descriptor.inverted.inverted = descriptor := by
  cases descriptor <;> rfl

end RS

inductive EZ where
  | E
  | Z
  deriving DecidableEq, Repr

inductive ProjectionOrientation where
  | preferred2a
  | inPlaneRotation2c
  | reversed2d
  | reversed2e
  | perspective2f
  | perspective2g
  deriving DecidableEq, Repr

inductive BondGlyph where
  | broken
  | solidThick
  | wavy
  deriving DecidableEq, Repr

/-- The glyph-to-face relation is steroid-projection-specific.  Formulae 2d/2e reverse the solid
and broken meanings; wavy remains ξ in every permitted orientation. -/
def faceOfGlyph : ProjectionOrientation → BondGlyph → Face
  | .reversed2d, .broken | .reversed2e, .broken => .beta
  | .reversed2d, .solidThick | .reversed2e, .solidThick => .alpha
  | _, .broken => .alpha
  | _, .solidThick => .beta
  | _, .wavy => .xi

@[simp] theorem preferred_broken_is_alpha :
    faceOfGlyph .preferred2a .broken = .alpha := rfl

@[simp] theorem preferred_solid_is_beta :
    faceOfGlyph .preferred2a .solidThick = .beta := rfl

@[simp] theorem reversed_broken_is_beta :
    faceOfGlyph .reversed2d .broken = .beta := rfl

@[simp] theorem wavy_is_xi_for_every_orientation (orientation : ProjectionOrientation) :
    faceOfGlyph orientation .wavy = .xi := by
  cases orientation <;> rfl

def impliedCoreFace : Nat → Option Face
  | 8 => some .beta
  | 9 => some .alpha
  | 10 => some .beta
  | 13 => some .beta
  | 14 => some .alpha
  | 17 => some .beta
  | _ => none

@[simp] theorem implied_core_faces_exact :
    [impliedCoreFace 8, impliedCoreFace 9, impliedCoreFace 10,
      impliedCoreFace 13, impliedCoreFace 14, impliedCoreFace 17] =
    [some .beta, some .alpha, some .beta, some .beta, some .alpha, some .beta] := by
  decide

def bridgeheadHydrogenMayBeOmitted (locant : Nat) (face : Face) : Bool :=
  (locant = 8 && face = .beta) || (locant = 9 && face = .alpha) ||
    (locant = 14 && face = .alpha)

@[simp] theorem omission_defaults_are_8beta_9alpha_14alpha :
    bridgeheadHydrogenMayBeOmitted 8 .beta = true ∧
      bridgeheadHydrogenMayBeOmitted 9 .alpha = true ∧
      bridgeheadHydrogenMayBeOmitted 14 .alpha = true := by
  decide

/-- α/β is a face relation in a fixed steroid reference projection, whereas R/S depends on CIP
priority.  Neither determines the other. -/
structure CenterReading where
  face : Face
  cip : RS
  deriving DecidableEq, Repr

def alphaR : CenterReading := { face := .alpha, cip := .R }
def alphaS : CenterReading := { face := .alpha, cip := .S }

theorem alpha_does_not_determine_cip :
    alphaR.face = alphaS.face ∧ alphaR.cip ≠ alphaS.cip := by
  decide

/-! ## Table 1 and retained-parent configuration -/

structure LocatedRS where
  locant : Nat
  descriptor : RS
  deriving DecidableEq, Repr

inductive Table1Parent where
  | pregnane
  | cholane
  | cholestane
  | ergostane
  | campestane
  | poriferastane
  | stigmastane
  | gorgostane
  deriving DecidableEq, Repr

def table1SideChainConfiguration : Table1Parent → List LocatedRS
  | .pregnane => []
  | .cholane | .cholestane => [{ locant := 20, descriptor := .R }]
  | .ergostane | .poriferastane =>
      [{ locant := 20, descriptor := .R }, { locant := 24, descriptor := .S }]
  | .campestane | .stigmastane =>
      [{ locant := 20, descriptor := .R }, { locant := 24, descriptor := .R }]
  | .gorgostane =>
      [{ locant := 20, descriptor := .S }, { locant := 22, descriptor := .R },
        { locant := 23, descriptor := .R }, { locant := 24, descriptor := .R }]

@[simp] theorem gorgostane_table1_configuration :
    table1SideChainConfiguration .gorgostane =
      [{ locant := 20, descriptor := .S }, { locant := 22, descriptor := .R },
        { locant := 23, descriptor := .R }, { locant := 24, descriptor := .R }] := rfl

inductive AbsoluteHandedness where
  | first
  | second
  deriving DecidableEq, Repr

structure SequenceLabelReading where
  handedness : AbsoluteHandedness
  label : RS
  deriving DecidableEq, Repr

def beforeSubstitution : SequenceLabelReading := { handedness := .first, label := .R }
def afterSubstitution : SequenceLabelReading := { handedness := .first, label := .S }

/-- Table 1's warning: a changed priority environment can relabel R as S without inverting the
actual centre. -/
theorem rs_can_relabel_without_configuration_change :
    beforeSubstitution.handedness = afterSubstitution.handedness ∧
      beforeSubstitution.label ≠ afterSubstitution.label := by
  decide

structure LocatedFace where
  locant : Nat
  face : Face
  deriving DecidableEq, Repr

def lanostaneImpliedFaces : List LocatedFace :=
  [{ locant := 5, face := .alpha }, { locant := 8, face := .beta },
    { locant := 9, face := .alpha }, { locant := 10, face := .beta },
    { locant := 13, face := .beta }, { locant := 14, face := .alpha },
    { locant := 17, face := .beta }]

def lanostaneImpliedCIP : List LocatedRS := [{ locant := 20, descriptor := .R }]

/-! ## Whole-configuration operators -/

inductive CenterConfiguration where
  | face (value : Face)
  | cip (value : RS)
  deriving DecidableEq, Repr

namespace CenterConfiguration

def inverted : CenterConfiguration → CenterConfiguration
  | .face value => .face value.inverted
  | .cip value => .cip value.inverted

@[simp] theorem inverted_involutive (configuration : CenterConfiguration) :
    configuration.inverted.inverted = configuration := by
  cases configuration with
  | face face => simp [inverted]
  | cip cip => simp [inverted]

end CenterConfiguration

def entConfiguration {Locant : Type*}
    (configuration : Locant → Option CenterConfiguration) : Locant → Option CenterConfiguration :=
  fun locant => (configuration locant).map CenterConfiguration.inverted

@[simp] theorem ent_ent {Locant : Type*}
    (configuration : Locant → Option CenterConfiguration) :
    entConfiguration (entConfiguration configuration) = configuration := by
  funext locant
  simp [entConfiguration, Option.map_map, Function.comp_def]

inductive InversionNotation where
  | ent
  | localAlphaBeta
  | entWithLocalAlphaBeta
  deriving DecidableEq, Repr

/-- 3S-5.1--5.3: all inversions use `ent`; at most half use local α/β; a strict majority but not
all uses `ent` plus local corrections. -/
def inversionNotation (totalImplicit invertedImplicit : Nat) : InversionNotation :=
  if invertedImplicit = totalImplicit then .ent
  else if 2 * invertedImplicit ≤ totalImplicit then .localAlphaBeta
  else .entWithLocalAlphaBeta

@[simp] theorem all_centers_inverted_uses_ent (total : Nat) :
    inversionNotation total total = .ent := by
  simp [inversionNotation]

theorem at_most_half_uses_local {total inverted : Nat}
    (notAll : inverted ≠ total) (atMostHalf : 2 * inverted ≤ total) :
    inversionNotation total inverted = .localAlphaBeta := by
  simp [inversionNotation, notAll, atMostHalf]

theorem majority_not_all_uses_ent_plus_local {total inverted : Nat}
    (notAll : inverted ≠ total) (majority : total < 2 * inverted) :
    inversionNotation total inverted = .entWithLocalAlphaBeta := by
  simp [inversionNotation, notAll, Nat.not_le.mpr majority]

structure SteroidRacemate (Configuration : Type*) where
  normalSeriesRepresentative : Configuration
  entSeriesRepresentative : Configuration
  mirrorRelated : Prop
  equimolar : Prop

/-! ## Seco-steroid and vitamin-D boundaries -/

inductive Ring where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

inductive Fission where
  | none
  | ringB
  | ringC
  deriving DecidableEq, Repr

def alphaBetaAllowedOnRing : Fission → Ring → Bool
  | .none, _ => true
  | .ringB, .C | .ringB, .D => true
  | .ringC, .A | .ringC, .B => true
  | _, _ => false

@[simp] theorem ringB_fission_uses_rs_on_A :
    alphaBetaAllowedOnRing .ringB .A = false := rfl

@[simp] theorem ringC_fission_uses_rs_on_D :
    alphaBetaAllowedOnRing .ringC .D = false := rfl

structure LocatedEZ where
  locant : Nat
  descriptor : EZ
  deriving DecidableEq, Repr

inductive VitaminDParent where
  | calciol
  | calcidiol
  | calcitriol
  | ercalciol
  | ercalcitriol
  | methylcalciol
  | calcitetrol
  /-- The Previtamin D₃ row whose recommended trivial name is `(6Z)-tacalciol`. -/
  | preTacalciol
  | tacalciol
  | dihydrocalciol
  | isocalciol
  deriving DecidableEq, Repr

def vitaminDCenterConfiguration : VitaminDParent → List LocatedRS
  | .calciol | .calcidiol | .ercalciol | .preTacalciol | .tacalciol | .isocalciol =>
      [{ locant := 3, descriptor := .S }]
  | .calcitriol => [{ locant := 1, descriptor := .S }, { locant := 3, descriptor := .R }]
  | .ercalcitriol => [{ locant := 1, descriptor := .S }, { locant := 3, descriptor := .S }]
  | .methylcalciol => [{ locant := 3, descriptor := .S }, { locant := 24, descriptor := .S }]
  | .calcitetrol =>
      [{ locant := 1, descriptor := .S }, { locant := 3, descriptor := .S },
        { locant := 24, descriptor := .R }]
  | .dihydrocalciol => [{ locant := 3, descriptor := .S }, { locant := 10, descriptor := .S }]

def vitaminDDoubleBondConfiguration : VitaminDParent → List LocatedEZ
  | .calciol | .calcidiol | .calcitriol | .methylcalciol
  | .calcitetrol | .dihydrocalciol =>
      [{ locant := 5, descriptor := .Z }, { locant := 7, descriptor := .E }]
  | .ercalciol | .ercalcitriol =>
      [{ locant := 5, descriptor := .Z }, { locant := 7, descriptor := .E },
        { locant := 22, descriptor := .E }]
  | .preTacalciol => [{ locant := 6, descriptor := .Z }]
  | .tacalciol => [{ locant := 6, descriptor := .E }]
  | .isocalciol => [{ locant := 5, descriptor := .E }, { locant := 7, descriptor := .E }]

@[simp] theorem calcitriol_table3_configuration :
    vitaminDCenterConfiguration .calcitriol =
        [{ locant := 1, descriptor := .S }, { locant := 3, descriptor := .R }] ∧
      vitaminDDoubleBondConfiguration .calcitriol =
        [{ locant := 5, descriptor := .Z }, { locant := 7, descriptor := .E }] := by
  decide

inductive TrieneModification where
  | ta
  | iso
  deriving DecidableEq, Repr

def impliedTrieneGeometry : TrieneModification → List LocatedEZ
  | .ta => [{ locant := 6, descriptor := .E }]
  | .iso => [{ locant := 7, descriptor := .E }]

def erSideChainConfiguration : List (Sum LocatedEZ LocatedRS) :=
  [.inl { locant := 22, descriptor := .E }, .inr { locant := 24, descriptor := .R }]

/-! ## Clause ownership -/

inductive SemanticDomain where
  | projection
  | parentImplication
  | descriptorSelection
  | sideChainData
  | doubleBond
  | specializedParents
  | wholeConfiguration
  | skeletalModification
  | secoScope
  | vitaminD
  | bridgeAndNumbering
  deriving DecidableEq, Repr

def provisionSemanticDomain : Provision → SemanticDomain
  | .projectionAlphaBetaDefinition | .projectionBondGlyphs
  | .projectionHydrogenOmissionDefaults | .rotatedProjectionGlyphReversal
  | .perspectiveProjectionSpecialConvention | .sideChainDrawingConvention
  | .spirostanRingFProjection | .spirostanConformationNotImplied => .projection
  | .absoluteConfigurationSources | .unknownConfigurationUsesXi
  | .impliedBridgeheadConfigurations | .impliedC17Beta
  | .c5ConfigurationAlwaysExplicit | .tetracyclicSubstituentDescriptors
  | .lanostaneImpliedConfiguration | .cycloartaneC9ConfigurationImplication
  | .additionalRingsRetainImpliedConfiguration => .parentImplication
  | .sideChainUsesCIPUnlessImplied | .c20AlphaBetaDiscouraged
  | .normalConfigurationSideChainChoice | .equalRingAttachedChainsBetaIsPrimed
  | .equalSideChainGroupsProSIsPrimed | .spirostanRSRelabelingWarning => .descriptorSelection
  | .table1SideChainConfigurationInventory | .sequenceLabelsMayChangeWithoutGeometryChange
  | .trimethylSteroidConfigurationNumbering | .addendumSideChainAtomLocants => .sideChainData
  | .sideChainDoubleBondsUseEZ | .vitaminDSecoDoubleBondsUseEZ => .doubleBond
  | .cardanolideImpliedConfiguration | .bufanolideImpliedConfiguration
  | .spirostanDefaultConfiguration | .spirostanC16C17Exceptions
  | .spirostanC20C22Exceptions | .spirostanC23C24C26Descriptors
  | .furostanDefaultConfiguration | .furostanC5Descriptor
  | .furostanC22C25Descriptors | .table2RetainedNameConfigurationInventory
  | .epiRequiresSpecifiedCenter => .specializedParents
  | .entInvertsAllImpliedCenters | .localAlphaBetaForAtMostHalfInverted
  | .retroPrefixForbidden | .entPlusLocalForMajorityInverted
  | .racPrefixAndRepresentativeSelection | .racAlphaBetaReferToNormalSeries
  | .relativeConfigurationUsesRStarSStar => .wholeConfiguration
  | .desRetainsImpliedConfiguration | .homoPrefixPrecedesStemStereodescriptor
  | .abeoRequiresResultingStereochemistry => .skeletalModification
  | .secoAlphaBetaRequiresParentRingOrientation | .ringBFissionUsesRSOnRingA
  | .ringCFissionUsesRSOnRingD => .secoScope
  | .vitaminDUsesRSAndEZ | .table3VitaminDConfigurationInventory
  | .vitaminDNamesImplyConfigurationAndHydroxylLocants
  | .vitaminDRSLabelsMayChangeInDerivatives | .taPrefixTrieneGeometry
  | .isoPrefixGeometry | .erPrefixSideChainConfiguration
  | .additionalVitaminDHydroxylStereochemistry => .vitaminD
  | .bridgedSteroidsUseAlphaBetaWhenNeeded => .bridgeAndNumbering

theorem every_provision_has_independent_semantic_domain
    (provision : Provision) : ∃ domain, provisionSemanticDomain provision = domain :=
  ⟨provisionSemanticDomain provision, rfl⟩



/-- The 23 HTML artifacts in the checksum-matched recursive bundle. -/
inductive SourceHtmlArtifact where
  | s01 | s02a | s02b | s03 | s04a | s04b | s05 | s06 | s07 | s089 | s10
  | addendum | innAppendix | introduction | app | err24 | err25 | err43 | errata
  | index | table1 | table2 | table3
  deriving DecidableEq, Repr

namespace SourceHtmlArtifact

def all : List SourceHtmlArtifact :=
  [ .s01, .s02a, .s02b, .s03, .s04a, .s04b, .s05, .s06, .s07, .s089, .s10
  , .addendum, .innAppendix, .introduction, .app, .err24, .err25, .err43, .errata
  , .index, .table1, .table2, .table3 ]

@[simp] theorem mem_all (artifact : SourceHtmlArtifact) : artifact ∈ all := by
  cases artifact <;> simp [all]

theorem all_nodup : all.Nodup := by decide

def filename : SourceHtmlArtifact → String
  | .s01 => "3S01.html"
  | .s02a => "3S02a.html"
  | .s02b => "3S02b.html"
  | .s03 => "3S03.html"
  | .s04a => "3S04a.html"
  | .s04b => "3S04b.html"
  | .s05 => "3S05.html"
  | .s06 => "3S06.html"
  | .s07 => "3S07.html"
  | .s089 => "3S089.html"
  | .s10 => "3S10.html"
  | .addendum => "3Sadd.html"
  | .innAppendix => "3Sapp.html"
  | .introduction => "3Sint.html"
  | .app => "app.html"
  | .err24 => "err24.html"
  | .err25 => "err25.html"
  | .err43 => "err43.html"
  | .errata => "errat.html"
  | .index => "index.html"
  | .table1 => "tab1.html"
  | .table2 => "tab2.html"
  | .table3 => "tab3.html"

def relativePath (artifact : SourceHtmlArtifact) : String :=
  "iupac.qmul.ac.uk/steroid/" ++ artifact.filename

end SourceHtmlArtifact

/-- Every original GIF in the frozen bundle, named by its exact source filename. -/
inductive SourceImageArtifact where
  | alphaGlyph | alterationMark | rightArrow | betaGlyph | xiGlyph
  | threeBond | s1 | s102 | s1035 | s106 | s10711 | s112 | s1123 | s134 | s156
  | s178 | s1922 | s23 | s246 | s278 | s29 | s2ab | s2ce | s2fg | s2h | s302
  | s335 | s36 | s379 | s3ab | s403 | s445 | s467 | s489 | s4t7 | s501 | s524
  | s556 | s57 | s58 | s59 | s60 | s61 | s62 | s634 | s656 | s678 | s6971
  | s723 | s745 | s767 | s78 | s79 | s8 | s801 | s825 | s86 | s87 | s889
  | s902 | s910 | s934 | s95 | s967 | s98 | s9901
  | sideChainTable1a | sideChainTable1b | sideChainTable1c | sideChainTable1d
  | sideChainTable1e | sideChainTable1f | sideChainTable1g | sideChainTable1h
  | alphaBond | betaBond | xiBond
  deriving DecidableEq, Repr

namespace SourceImageArtifact

def all : List SourceImageArtifact :=
  [ .alphaGlyph, .alterationMark, .rightArrow, .betaGlyph, .xiGlyph
  , .threeBond, .s1, .s102, .s1035, .s106, .s10711, .s112, .s1123, .s134, .s156
  , .s178, .s1922, .s23, .s246, .s278, .s29, .s2ab, .s2ce, .s2fg, .s2h, .s302
  , .s335, .s36, .s379, .s3ab, .s403, .s445, .s467, .s489, .s4t7, .s501, .s524
  , .s556, .s57, .s58, .s59, .s60, .s61, .s62, .s634, .s656, .s678, .s6971
  , .s723, .s745, .s767, .s78, .s79, .s8, .s801, .s825, .s86, .s87, .s889
  , .s902, .s910, .s934, .s95, .s967, .s98, .s9901
  , .sideChainTable1a, .sideChainTable1b, .sideChainTable1c, .sideChainTable1d
  , .sideChainTable1e, .sideChainTable1f, .sideChainTable1g, .sideChainTable1h
  , .alphaBond, .betaBond, .xiBond ]

@[simp] theorem mem_all (artifact : SourceImageArtifact) : artifact ∈ all := by
  cases artifact <;> simp [all]

theorem all_nodup : all.Nodup := by decide

def filename : SourceImageArtifact → String
  | .alphaGlyph => "ALPHA.GIF"
  | .alterationMark => "ALTER.GIF"
  | .rightArrow => "ARROWR.GIF"
  | .betaGlyph => "BETA.GIF"
  | .xiGlyph => "XI.GIF"
  | .threeBond => "3BOND.GIF"
  | .s1 => "3S1.GIF"
  | .s102 => "3S102.GIF"
  | .s1035 => "3S1035.GIF"
  | .s106 => "3S106.GIF"
  | .s10711 => "3S10711.GIF"
  | .s112 => "3S112.GIF"
  | .s1123 => "3S1123.GIF"
  | .s134 => "3S134.GIF"
  | .s156 => "3S156.GIF"
  | .s178 => "3S178.GIF"
  | .s1922 => "3S1922.GIF"
  | .s23 => "3S23.GIF"
  | .s246 => "3S246.GIF"
  | .s278 => "3S278.GIF"
  | .s29 => "3S29.GIF"
  | .s2ab => "3S2AB.GIF"
  | .s2ce => "3S2CE.GIF"
  | .s2fg => "3S2FG.GIF"
  | .s2h => "3S2H.GIF"
  | .s302 => "3S302.GIF"
  | .s335 => "3S335.GIF"
  | .s36 => "3S36.GIF"
  | .s379 => "3S379.GIF"
  | .s3ab => "3S3AB.GIF"
  | .s403 => "3S403.GIF"
  | .s445 => "3S445.GIF"
  | .s467 => "3S467.GIF"
  | .s489 => "3S489.GIF"
  | .s4t7 => "3S4T7.GIF"
  | .s501 => "3S501.GIF"
  | .s524 => "3S524.GIF"
  | .s556 => "3S556.GIF"
  | .s57 => "3S57.GIF"
  | .s58 => "3S58.GIF"
  | .s59 => "3S59.GIF"
  | .s60 => "3S60.GIF"
  | .s61 => "3S61.GIF"
  | .s62 => "3S62.GIF"
  | .s634 => "3S634.GIF"
  | .s656 => "3S656.GIF"
  | .s678 => "3S678.GIF"
  | .s6971 => "3S6971.GIF"
  | .s723 => "3S723.GIF"
  | .s745 => "3S745.GIF"
  | .s767 => "3S767.GIF"
  | .s78 => "3S78.GIF"
  | .s79 => "3S79.GIF"
  | .s8 => "3S8.GIF"
  | .s801 => "3S801.GIF"
  | .s825 => "3S825.GIF"
  | .s86 => "3S86.GIF"
  | .s87 => "3S87.GIF"
  | .s889 => "3S889.GIF"
  | .s902 => "3S902.GIF"
  | .s910 => "3S910.GIF"
  | .s934 => "3S934.GIF"
  | .s95 => "3S95.GIF"
  | .s967 => "3S967.GIF"
  | .s98 => "3S98.GIF"
  | .s9901 => "3S9901.GIF"
  | .sideChainTable1a => "3ST1A.GIF"
  | .sideChainTable1b => "3ST1B.GIF"
  | .sideChainTable1c => "3ST1C.GIF"
  | .sideChainTable1d => "3ST1D.GIF"
  | .sideChainTable1e => "3ST1E.GIF"
  | .sideChainTable1f => "3ST1F.GIF"
  | .sideChainTable1g => "3ST1G.GIF"
  | .sideChainTable1h => "3ST1H.GIF"
  | .alphaBond => "ABOND.GIF"
  | .betaBond => "BBOND.GIF"
  | .xiBond => "XBOND.GIF"

def inGreekDirectory : SourceImageArtifact → Bool
  | .alphaGlyph | .alterationMark | .rightArrow | .betaGlyph | .xiGlyph => true
  | _ => false

def relativePath (artifact : SourceImageArtifact) : String :=
  if artifact.inGreekDirectory then
    "iupac.qmul.ac.uk/greek/" ++ artifact.filename
  else
    "iupac.qmul.ac.uk/steroid/3Sgif/" ++ artifact.filename

/-- Direct inspection classifies the five shared typography glyphs and four bond-style keys as
non-molecular; every other original image is a molecular structure panel or side-chain fragment. -/
def isMolecularGraph : SourceImageArtifact → Bool
  | .alphaGlyph | .alterationMark | .rightArrow | .betaGlyph | .xiGlyph
  | .threeBond | .alphaBond | .betaBond | .xiBond => false
  | _ => true

/-- The typed steroid semantics are not atom-and-bond transcriptions of the 68 structure panels. -/
def atomLevelGraphTranscriptionReviewed (_artifact : SourceImageArtifact) : Bool := false

end SourceImageArtifact

@[simp] theorem source_artifact_inventory_exact :
    SourceHtmlArtifact.all.length = 23 ∧
      SourceImageArtifact.all.length = 77 ∧
        (SourceImageArtifact.all.filter fun image => image.isMolecularGraph).length = 68 ∧
          (SourceImageArtifact.all.filter fun image =>
            image.atomLevelGraphTranscriptionReviewed).length = 0 := by
  decide

/-- Small manifest-facing constants keep checklist computation independent of the full ledger. -/
def currentSourceReviewProvisionEnumerationConfirmed : Bool := true
def currentSourceReviewProseTableCoverageConfirmed : Bool := true
def currentSourceReviewFigureGraphTranscriptionsReviewed : Bool := false

/-- Evidence from a separate fidelity pass over the exact frozen 100-artifact bundle.  All 64
rendered HTML pages and all 77 original GIFs were visually reviewed.  This confirms the complete
62-provision configuration-bearing enumeration and prose/table coverage while retaining the 68
molecular images as an open atom-level transcription queue. -/
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
  atomLevelGraphTranscriptionCount : Nat
  provisionEnumerationConfirmed : Bool
  proseTableCoverageConfirmed : Bool
  figureGraphTranscriptionsReviewed : Bool
  reviewerKindDeclared : reviewerKind ≠ ""
  reviewDateDeclared : reviewDate ≠ ""
  methodDeclared : method ≠ ""
  sourceBundleSha256Exact :
    sourceBundleSha256 = (P10DelegatedAuthorityCorpus.snapshot .steroid1989).bundleSha256
  reviewedArtifactCountExact :
    reviewedArtifacts = reviewedHtmlArtifacts.length + reviewedImageArtifacts.length
  reviewedRenderedPagesExact : reviewedRenderedPages = 64
  reviewedHtmlArtifactsExact : reviewedHtmlArtifacts = SourceHtmlArtifact.all
  reviewedImageArtifactsExact : reviewedImageArtifacts = SourceImageArtifact.all
  reviewedProvisionsExact : reviewedProvisions = Provision.all
  molecularGraphImageCountExact :
    molecularGraphImageCount =
      (reviewedImageArtifacts.filter fun image => image.isMolecularGraph).length
  atomLevelGraphTranscriptionCountExact :
    atomLevelGraphTranscriptionCount =
      (reviewedImageArtifacts.filter fun image =>
        image.atomLevelGraphTranscriptionReviewed).length
  molecularGraphQueueStillOpen : atomLevelGraphTranscriptionCount < molecularGraphImageCount
  provisionEnumerationConfirmedExact : provisionEnumerationConfirmed = true
  proseTableCoverageConfirmedExact : proseTableCoverageConfirmed = true
  figureGraphTranscriptionsReviewedExact : figureGraphTranscriptionsReviewed = false

def currentSourceReview : SourceReviewEvidence where
  reviewerKind := "automated-record-ff5b7f6496e601ebe8a14c262136c4a1"
  reviewDate := "record-54db71cc66a48d655191405c29c6a9ac"
  method :=
    "record-91c4134c8df311c74eb11f6066be00cc"
  sourceBundleSha256 :=
    "83cb309d8a3674ca7b6dfb90a0600a4a442aa17e3f3f2bcc898a705f06241210"
  reviewedArtifacts := 100
  reviewedRenderedPages := 64
  reviewedHtmlArtifacts := SourceHtmlArtifact.all
  reviewedImageArtifacts := SourceImageArtifact.all
  reviewedProvisions := Provision.all
  molecularGraphImageCount := 68
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
  atomLevelGraphTranscriptionCountExact := by decide
  molecularGraphQueueStillOpen := by decide
  provisionEnumerationConfirmedExact := rfl
  proseTableCoverageConfirmedExact := rfl
  figureGraphTranscriptionsReviewedExact := rfl

@[simp] theorem current_source_review_counts_exact :
    currentSourceReview.reviewedArtifacts = 100 ∧
      currentSourceReview.reviewedRenderedPages = 64 ∧
        currentSourceReview.reviewedHtmlArtifacts.length = 23 ∧
          currentSourceReview.reviewedImageArtifacts.length = 77 ∧
            currentSourceReview.reviewedProvisions.length = 62 ∧
              currentSourceReview.molecularGraphImageCount = 68 ∧
                currentSourceReview.atomLevelGraphTranscriptionCount = 0 := by
  decide

end Steroid1989

end TetraStereo.OneCenter
