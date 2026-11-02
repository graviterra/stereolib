import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataCore
import TetraStereo.KernelOnly

set_option autoImplicit false






















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorSteroidSourceMeaning

open GlobalNonDescriptorIndexedSourceData

inductive ConfigurationEvidenceSource where
  | drawnFormula
  | retainedNameTable
  deriving DecidableEq, Repr

inductive ChainMark where
  | unprimed
  | primed
  deriving DecidableEq, Repr

inductive SpecializedParent where
  | cardanolide
  | bufanolide
  | spirostan
  | furostan
  deriving DecidableEq, Repr

inductive ConfigurationStatus where
  | implied
  | explicitDescriptorRequired
  | retainedThroughModification
  | conformationNotImplied
  deriving DecidableEq, Repr

inductive NamingPermission where
  | required
  | allowedWhenNeeded
  | discouraged
  | forbidden
  deriving DecidableEq, Repr

inductive RelativeDescriptor where
  | RStar
  | SStar
  deriving DecidableEq, Repr

inductive SkeletalPrefix where
  | des
  | homo
  | abeo
  | seco
  | retro
  deriving DecidableEq, Repr

inductive NameComponentKind where
  | skeletalPrefix
  | stemStereodescriptor
  deriving DecidableEq, Repr

inductive RacemateRepresentative where
  | normalSeries
  | entSeries
  deriving DecidableEq, Repr

inductive AddendumLocantNotation where
  | superscriptedSideChainAtomLocants
  deriving DecidableEq, Repr

def projectionGlyphAssignments :
    List (Steroid1989.ProjectionOrientation × Steroid1989.BondGlyph × Steroid1989.Face) :=
  [ (.preferred2a, .broken, Steroid1989.faceOfGlyph .preferred2a .broken)
  , (.preferred2a, .solidThick, Steroid1989.faceOfGlyph .preferred2a .solidThick)
  , (.preferred2a, .wavy, Steroid1989.faceOfGlyph .preferred2a .wavy) ]

def rotatedProjectionAssignments :
    List (Steroid1989.ProjectionOrientation × Steroid1989.BondGlyph × Steroid1989.Face) :=
  [ (.reversed2d, .broken, Steroid1989.faceOfGlyph .reversed2d .broken)
  , (.reversed2d, .solidThick, Steroid1989.faceOfGlyph .reversed2d .solidThick)
  , (.reversed2e, .broken, Steroid1989.faceOfGlyph .reversed2e .broken)
  , (.reversed2e, .solidThick, Steroid1989.faceOfGlyph .reversed2e .solidThick) ]

def omissionDefaults : List Steroid1989.LocatedFace :=
  [⟨8, .beta⟩, ⟨9, .alpha⟩, ⟨14, .alpha⟩]

def impliedBridgeheadFaces : List Steroid1989.LocatedFace :=
  [⟨8, .beta⟩, ⟨9, .alpha⟩, ⟨10, .beta⟩, ⟨13, .beta⟩, ⟨14, .alpha⟩]

def table1Inventory : List (Steroid1989.Table1Parent × List Steroid1989.LocatedRS) :=
  [ (.pregnane, Steroid1989.table1SideChainConfiguration .pregnane)
  , (.cholane, Steroid1989.table1SideChainConfiguration .cholane)
  , (.cholestane, Steroid1989.table1SideChainConfiguration .cholestane)
  , (.ergostane, Steroid1989.table1SideChainConfiguration .ergostane)
  , (.campestane, Steroid1989.table1SideChainConfiguration .campestane)
  , (.poriferastane, Steroid1989.table1SideChainConfiguration .poriferastane)
  , (.stigmastane, Steroid1989.table1SideChainConfiguration .stigmastane)
  , (.gorgostane, Steroid1989.table1SideChainConfiguration .gorgostane) ]

def vitaminDParents : List Steroid1989.VitaminDParent :=
  [ .calciol, .calcidiol, .calcitriol, .ercalciol, .ercalcitriol
  , .methylcalciol, .calcitetrol, .preTacalciol, .tacalciol
  , .dihydrocalciol, .isocalciol ]

def vitaminDInventory :
    List (Steroid1989.VitaminDParent × List Steroid1989.LocatedRS ×
      List Steroid1989.LocatedEZ) :=
  vitaminDParents.map fun parent =>
    (parent, Steroid1989.vitaminDCenterConfiguration parent,
      Steroid1989.vitaminDDoubleBondConfiguration parent)

/-- Typed payloads preserve the independent semantic value attached to every steroid row. -/
inductive SourceAssertion where
  | absoluteConfigurationSources (sources : List ConfigurationEvidenceSource)
  | unknownConfigurationUsesXi (unknownFace : Steroid1989.Face)
  | projectionAlphaBetaDefinition (faces : List Steroid1989.Face)
  | projectionBondGlyphs
      (assignments : List (Steroid1989.ProjectionOrientation × Steroid1989.BondGlyph ×
        Steroid1989.Face))
  | projectionHydrogenOmissionDefaults (defaults : List Steroid1989.LocatedFace)
  | rotatedProjectionGlyphReversal
      (assignments : List (Steroid1989.ProjectionOrientation × Steroid1989.BondGlyph ×
        Steroid1989.Face))
  | perspectiveProjectionSpecialConvention (orientations : List Steroid1989.ProjectionOrientation)
  | impliedBridgeheadConfigurations (faces : List Steroid1989.LocatedFace)
  | impliedC17Beta (configuration : Steroid1989.LocatedFace)
  | c5ConfigurationAlwaysExplicit (locant : Nat) (permission : NamingPermission)
  | tetracyclicSubstituentDescriptors (faces : List Steroid1989.Face)
  | sideChainUsesCIPUnlessImplied (descriptors : List Steroid1989.RS)
  | sideChainDrawingConvention (orientation : Steroid1989.ProjectionOrientation)
  | c20AlphaBetaDiscouraged
      (locant : Nat) (permission : NamingPermission) (replacement : List Steroid1989.RS)
  | table1SideChainConfigurationInventory
      (inventory : List (Steroid1989.Table1Parent × List Steroid1989.LocatedRS))
  | sequenceLabelsMayChangeWithoutGeometryChange
      (before after : Steroid1989.SequenceLabelReading)
  | trimethylSteroidConfigurationNumbering (configurationLocants : List Nat)
  | lanostaneImpliedConfiguration
      (faces : List Steroid1989.LocatedFace) (cip : List Steroid1989.LocatedRS)
  | cycloartaneC9ConfigurationImplication (configuration : Steroid1989.LocatedFace)
  | sideChainDoubleBondsUseEZ (descriptors : List Steroid1989.EZ)
  | vitaminDSecoDoubleBondsUseEZ (descriptors : List Steroid1989.EZ)
  | normalConfigurationSideChainChoice (normalChain : ChainMark)
  | equalRingAttachedChainsBetaIsPrimed (face : Steroid1989.Face) (mark : ChainMark)
  | equalSideChainGroupsProSIsPrimed (descriptor : Steroid1989.RS) (mark : ChainMark)
  | cardanolideImpliedConfiguration (parent : SpecializedParent) (status : ConfigurationStatus)
  | bufanolideImpliedConfiguration (parent : SpecializedParent) (status : ConfigurationStatus)
  | spirostanDefaultConfiguration (parent : SpecializedParent) (status : ConfigurationStatus)
  | spirostanC16C17Exceptions (locants : List Nat) (status : ConfigurationStatus)
  | spirostanC20C22Exceptions (locants : List Nat) (status : ConfigurationStatus)
  | spirostanC23C24C26Descriptors (locants : List Nat) (descriptors : List Steroid1989.RS)
  | spirostanRingFProjection (orientation : Steroid1989.ProjectionOrientation)
  | spirostanConformationNotImplied (parent : SpecializedParent) (status : ConfigurationStatus)
  | spirostanRSRelabelingWarning
      (before after : Steroid1989.SequenceLabelReading)
  | furostanDefaultConfiguration (parent : SpecializedParent) (status : ConfigurationStatus)
  | furostanC5Descriptor (locant : Nat) (faces : List Steroid1989.Face)
  | furostanC22C25Descriptors (locants : List Nat) (descriptors : List Steroid1989.RS)
  | table2RetainedNameConfigurationInventory
      (source : ConfigurationEvidenceSource) (status : ConfigurationStatus)
  | epiRequiresSpecifiedCenter (permission : NamingPermission)
  | entInvertsAllImpliedCenters
      (total inverted : Nat) (selectedNotation : Steroid1989.InversionNotation)
  | localAlphaBetaForAtMostHalfInverted
      (total inverted : Nat) (selectedNotation : Steroid1989.InversionNotation)
  | retroPrefixForbidden (skeletalPrefix : SkeletalPrefix) (permission : NamingPermission)
  | entPlusLocalForMajorityInverted
      (total inverted : Nat) (selectedNotation : Steroid1989.InversionNotation)
  | racPrefixAndRepresentativeSelection (representatives : List RacemateRepresentative)
  | racAlphaBetaReferToNormalSeries (representative : RacemateRepresentative)
  | relativeConfigurationUsesRStarSStar (descriptors : List RelativeDescriptor)
  | desRetainsImpliedConfiguration
      (skeletalPrefix : SkeletalPrefix) (status : ConfigurationStatus)
  | homoPrefixPrecedesStemStereodescriptor (order : List NameComponentKind)
  | abeoRequiresResultingStereochemistry
      (skeletalPrefix : SkeletalPrefix) (permission : NamingPermission)
  | secoAlphaBetaRequiresParentRingOrientation
      (readings : List (Steroid1989.Fission × Steroid1989.Ring × Bool))
  | ringBFissionUsesRSOnRingA (allowed : Bool)
  | ringCFissionUsesRSOnRingD (allowed : Bool)
  | vitaminDUsesRSAndEZ (centerDescriptors : List Steroid1989.RS)
      (bondDescriptors : List Steroid1989.EZ)
  | table3VitaminDConfigurationInventory
      (inventory : List (Steroid1989.VitaminDParent × List Steroid1989.LocatedRS ×
        List Steroid1989.LocatedEZ))
  | vitaminDNamesImplyConfigurationAndHydroxylLocants (parents : List Steroid1989.VitaminDParent)
  | vitaminDRSLabelsMayChangeInDerivatives
      (before after : Steroid1989.SequenceLabelReading)
  | taPrefixTrieneGeometry (geometry : List Steroid1989.LocatedEZ)
  | isoPrefixGeometry (geometry : List Steroid1989.LocatedEZ)
  | erPrefixSideChainConfiguration (configuration : List (Sum Steroid1989.LocatedEZ Steroid1989.LocatedRS))
  | additionalVitaminDHydroxylStereochemistry (descriptors : List Steroid1989.RS)
  | additionalRingsRetainImpliedConfiguration (status : ConfigurationStatus)
  | bridgedSteroidsUseAlphaBetaWhenNeeded
      (faces : List Steroid1989.Face) (permission : NamingPermission)
  | addendumSideChainAtomLocants (locantNotation : AddendumLocantNotation)
  deriving DecidableEq, Repr

def sourceAssertion : Steroid1989.Provision → SourceAssertion
  | .absoluteConfigurationSources =>
      .absoluteConfigurationSources [.drawnFormula, .retainedNameTable]
  | .unknownConfigurationUsesXi => .unknownConfigurationUsesXi .xi
  | .projectionAlphaBetaDefinition => .projectionAlphaBetaDefinition [.alpha, .beta]
  | .projectionBondGlyphs => .projectionBondGlyphs projectionGlyphAssignments
  | .projectionHydrogenOmissionDefaults =>
      .projectionHydrogenOmissionDefaults omissionDefaults
  | .rotatedProjectionGlyphReversal =>
      .rotatedProjectionGlyphReversal rotatedProjectionAssignments
  | .perspectiveProjectionSpecialConvention =>
      .perspectiveProjectionSpecialConvention [.perspective2f, .perspective2g]
  | .impliedBridgeheadConfigurations =>
      .impliedBridgeheadConfigurations impliedBridgeheadFaces
  | .impliedC17Beta => .impliedC17Beta ⟨17, .beta⟩
  | .c5ConfigurationAlwaysExplicit => .c5ConfigurationAlwaysExplicit 5 .required
  | .tetracyclicSubstituentDescriptors =>
      .tetracyclicSubstituentDescriptors [.alpha, .beta, .xi]
  | .sideChainUsesCIPUnlessImplied => .sideChainUsesCIPUnlessImplied [.R, .S]
  | .sideChainDrawingConvention => .sideChainDrawingConvention .preferred2a
  | .c20AlphaBetaDiscouraged => .c20AlphaBetaDiscouraged 20 .discouraged [.R, .S]
  | .table1SideChainConfigurationInventory =>
      .table1SideChainConfigurationInventory table1Inventory
  | .sequenceLabelsMayChangeWithoutGeometryChange =>
      .sequenceLabelsMayChangeWithoutGeometryChange
        Steroid1989.beforeSubstitution Steroid1989.afterSubstitution
  -- Table 1 note (2): the three additional methyl groups are numbered 28, 29 and 30.
  | .trimethylSteroidConfigurationNumbering =>
      .trimethylSteroidConfigurationNumbering [28, 29, 30]
  | .lanostaneImpliedConfiguration =>
      .lanostaneImpliedConfiguration Steroid1989.lanostaneImpliedFaces
        Steroid1989.lanostaneImpliedCIP
  -- Table 1 note (2): the named cycloartane parent implies the C-9 change 9α → 9β.
  -- The generic steroid default remains `Steroid1989.impliedCoreFace 9 = some .alpha`.
  | .cycloartaneC9ConfigurationImplication =>
      .cycloartaneC9ConfigurationImplication ⟨9, .beta⟩
  | .sideChainDoubleBondsUseEZ => .sideChainDoubleBondsUseEZ [.E, .Z]
  | .vitaminDSecoDoubleBondsUseEZ => .vitaminDSecoDoubleBondsUseEZ [.E, .Z]
  | .normalConfigurationSideChainChoice => .normalConfigurationSideChainChoice .unprimed
  | .equalRingAttachedChainsBetaIsPrimed => .equalRingAttachedChainsBetaIsPrimed .beta .primed
  | .equalSideChainGroupsProSIsPrimed => .equalSideChainGroupsProSIsPrimed .S .primed
  | .cardanolideImpliedConfiguration => .cardanolideImpliedConfiguration .cardanolide .implied
  | .bufanolideImpliedConfiguration => .bufanolideImpliedConfiguration .bufanolide .implied
  | .spirostanDefaultConfiguration => .spirostanDefaultConfiguration .spirostan .implied
  | .spirostanC16C17Exceptions =>
      .spirostanC16C17Exceptions [16, 17] .explicitDescriptorRequired
  | .spirostanC20C22Exceptions =>
      .spirostanC20C22Exceptions [20, 22] .explicitDescriptorRequired
  | .spirostanC23C24C26Descriptors => .spirostanC23C24C26Descriptors [23, 24, 26] [.R, .S]
  | .spirostanRingFProjection => .spirostanRingFProjection .preferred2a
  | .spirostanConformationNotImplied =>
      .spirostanConformationNotImplied .spirostan .conformationNotImplied
  | .spirostanRSRelabelingWarning =>
      .spirostanRSRelabelingWarning Steroid1989.beforeSubstitution Steroid1989.afterSubstitution
  | .furostanDefaultConfiguration => .furostanDefaultConfiguration .furostan .implied
  | .furostanC5Descriptor => .furostanC5Descriptor 5 [.alpha, .beta]
  | .furostanC22C25Descriptors => .furostanC22C25Descriptors [22, 25] [.R, .S]
  | .table2RetainedNameConfigurationInventory =>
      .table2RetainedNameConfigurationInventory .retainedNameTable .implied
  | .epiRequiresSpecifiedCenter => .epiRequiresSpecifiedCenter .required
  | .entInvertsAllImpliedCenters =>
      .entInvertsAllImpliedCenters 7 7 (Steroid1989.inversionNotation 7 7)
  | .localAlphaBetaForAtMostHalfInverted =>
      .localAlphaBetaForAtMostHalfInverted 8 4 (Steroid1989.inversionNotation 8 4)
  | .retroPrefixForbidden => .retroPrefixForbidden .retro .forbidden
  | .entPlusLocalForMajorityInverted =>
      .entPlusLocalForMajorityInverted 8 5 (Steroid1989.inversionNotation 8 5)
  | .racPrefixAndRepresentativeSelection =>
      .racPrefixAndRepresentativeSelection [.normalSeries, .entSeries]
  | .racAlphaBetaReferToNormalSeries => .racAlphaBetaReferToNormalSeries .normalSeries
  | .relativeConfigurationUsesRStarSStar => .relativeConfigurationUsesRStarSStar [.RStar, .SStar]
  | .desRetainsImpliedConfiguration =>
      .desRetainsImpliedConfiguration .des .retainedThroughModification
  | .homoPrefixPrecedesStemStereodescriptor =>
      .homoPrefixPrecedesStemStereodescriptor [.skeletalPrefix, .stemStereodescriptor]
  | .abeoRequiresResultingStereochemistry =>
      .abeoRequiresResultingStereochemistry .abeo .required
  | .secoAlphaBetaRequiresParentRingOrientation =>
      .secoAlphaBetaRequiresParentRingOrientation
        [(.ringB, .A, Steroid1989.alphaBetaAllowedOnRing .ringB .A),
          (.ringB, .D, Steroid1989.alphaBetaAllowedOnRing .ringB .D),
          (.ringC, .A, Steroid1989.alphaBetaAllowedOnRing .ringC .A),
          (.ringC, .D, Steroid1989.alphaBetaAllowedOnRing .ringC .D)]
  | .ringBFissionUsesRSOnRingA =>
      .ringBFissionUsesRSOnRingA (Steroid1989.alphaBetaAllowedOnRing .ringB .A)
  | .ringCFissionUsesRSOnRingD =>
      .ringCFissionUsesRSOnRingD (Steroid1989.alphaBetaAllowedOnRing .ringC .D)
  | .vitaminDUsesRSAndEZ => .vitaminDUsesRSAndEZ [.R, .S] [.E, .Z]
  | .table3VitaminDConfigurationInventory =>
      .table3VitaminDConfigurationInventory vitaminDInventory
  | .vitaminDNamesImplyConfigurationAndHydroxylLocants =>
      .vitaminDNamesImplyConfigurationAndHydroxylLocants vitaminDParents
  | .vitaminDRSLabelsMayChangeInDerivatives =>
      .vitaminDRSLabelsMayChangeInDerivatives
        Steroid1989.beforeSubstitution Steroid1989.afterSubstitution
  | .taPrefixTrieneGeometry =>
      .taPrefixTrieneGeometry (Steroid1989.impliedTrieneGeometry .ta)
  | .isoPrefixGeometry =>
      .isoPrefixGeometry (Steroid1989.impliedTrieneGeometry .iso)
  | .erPrefixSideChainConfiguration =>
      .erPrefixSideChainConfiguration Steroid1989.erSideChainConfiguration
  | .additionalVitaminDHydroxylStereochemistry =>
      .additionalVitaminDHydroxylStereochemistry [.R, .S]
  | .additionalRingsRetainImpliedConfiguration =>
      .additionalRingsRetainImpliedConfiguration .retainedThroughModification
  | .bridgedSteroidsUseAlphaBetaWhenNeeded =>
      .bridgedSteroidsUseAlphaBetaWhenNeeded [.alpha, .beta] .allowedWhenNeeded
  | .addendumSideChainAtomLocants =>
      .addendumSideChainAtomLocants .superscriptedSideChainAtomLocants

/-- Recovering the owning provision from a typed assertion is used only to prove that distinct
rows cannot collapse; the assertion itself retains its domain-specific source data. -/
def SourceAssertion.provision : SourceAssertion → Steroid1989.Provision
  | .absoluteConfigurationSources _ => .absoluteConfigurationSources
  | .unknownConfigurationUsesXi _ => .unknownConfigurationUsesXi
  | .projectionAlphaBetaDefinition _ => .projectionAlphaBetaDefinition
  | .projectionBondGlyphs _ => .projectionBondGlyphs
  | .projectionHydrogenOmissionDefaults _ => .projectionHydrogenOmissionDefaults
  | .rotatedProjectionGlyphReversal _ => .rotatedProjectionGlyphReversal
  | .perspectiveProjectionSpecialConvention _ => .perspectiveProjectionSpecialConvention
  | .impliedBridgeheadConfigurations _ => .impliedBridgeheadConfigurations
  | .impliedC17Beta _ => .impliedC17Beta
  | .c5ConfigurationAlwaysExplicit _ _ => .c5ConfigurationAlwaysExplicit
  | .tetracyclicSubstituentDescriptors _ => .tetracyclicSubstituentDescriptors
  | .sideChainUsesCIPUnlessImplied _ => .sideChainUsesCIPUnlessImplied
  | .sideChainDrawingConvention _ => .sideChainDrawingConvention
  | .c20AlphaBetaDiscouraged _ _ _ => .c20AlphaBetaDiscouraged
  | .table1SideChainConfigurationInventory _ => .table1SideChainConfigurationInventory
  | .sequenceLabelsMayChangeWithoutGeometryChange _ _ =>
      .sequenceLabelsMayChangeWithoutGeometryChange
  | .trimethylSteroidConfigurationNumbering _ => .trimethylSteroidConfigurationNumbering
  | .lanostaneImpliedConfiguration _ _ => .lanostaneImpliedConfiguration
  | .cycloartaneC9ConfigurationImplication _ => .cycloartaneC9ConfigurationImplication
  | .sideChainDoubleBondsUseEZ _ => .sideChainDoubleBondsUseEZ
  | .vitaminDSecoDoubleBondsUseEZ _ => .vitaminDSecoDoubleBondsUseEZ
  | .normalConfigurationSideChainChoice _ => .normalConfigurationSideChainChoice
  | .equalRingAttachedChainsBetaIsPrimed _ _ => .equalRingAttachedChainsBetaIsPrimed
  | .equalSideChainGroupsProSIsPrimed _ _ => .equalSideChainGroupsProSIsPrimed
  | .cardanolideImpliedConfiguration _ _ => .cardanolideImpliedConfiguration
  | .bufanolideImpliedConfiguration _ _ => .bufanolideImpliedConfiguration
  | .spirostanDefaultConfiguration _ _ => .spirostanDefaultConfiguration
  | .spirostanC16C17Exceptions _ _ => .spirostanC16C17Exceptions
  | .spirostanC20C22Exceptions _ _ => .spirostanC20C22Exceptions
  | .spirostanC23C24C26Descriptors _ _ => .spirostanC23C24C26Descriptors
  | .spirostanRingFProjection _ => .spirostanRingFProjection
  | .spirostanConformationNotImplied _ _ => .spirostanConformationNotImplied
  | .spirostanRSRelabelingWarning _ _ => .spirostanRSRelabelingWarning
  | .furostanDefaultConfiguration _ _ => .furostanDefaultConfiguration
  | .furostanC5Descriptor _ _ => .furostanC5Descriptor
  | .furostanC22C25Descriptors _ _ => .furostanC22C25Descriptors
  | .table2RetainedNameConfigurationInventory _ _ => .table2RetainedNameConfigurationInventory
  | .epiRequiresSpecifiedCenter _ => .epiRequiresSpecifiedCenter
  | .entInvertsAllImpliedCenters _ _ _ => .entInvertsAllImpliedCenters
  | .localAlphaBetaForAtMostHalfInverted _ _ _ => .localAlphaBetaForAtMostHalfInverted
  | .retroPrefixForbidden _ _ => .retroPrefixForbidden
  | .entPlusLocalForMajorityInverted _ _ _ => .entPlusLocalForMajorityInverted
  | .racPrefixAndRepresentativeSelection _ => .racPrefixAndRepresentativeSelection
  | .racAlphaBetaReferToNormalSeries _ => .racAlphaBetaReferToNormalSeries
  | .relativeConfigurationUsesRStarSStar _ => .relativeConfigurationUsesRStarSStar
  | .desRetainsImpliedConfiguration _ _ => .desRetainsImpliedConfiguration
  | .homoPrefixPrecedesStemStereodescriptor _ => .homoPrefixPrecedesStemStereodescriptor
  | .abeoRequiresResultingStereochemistry _ _ => .abeoRequiresResultingStereochemistry
  | .secoAlphaBetaRequiresParentRingOrientation _ => .secoAlphaBetaRequiresParentRingOrientation
  | .ringBFissionUsesRSOnRingA _ => .ringBFissionUsesRSOnRingA
  | .ringCFissionUsesRSOnRingD _ => .ringCFissionUsesRSOnRingD
  | .vitaminDUsesRSAndEZ _ _ => .vitaminDUsesRSAndEZ
  | .table3VitaminDConfigurationInventory _ => .table3VitaminDConfigurationInventory
  | .vitaminDNamesImplyConfigurationAndHydroxylLocants _ =>
      .vitaminDNamesImplyConfigurationAndHydroxylLocants
  | .vitaminDRSLabelsMayChangeInDerivatives _ _ => .vitaminDRSLabelsMayChangeInDerivatives
  | .taPrefixTrieneGeometry _ => .taPrefixTrieneGeometry
  | .isoPrefixGeometry _ => .isoPrefixGeometry
  | .erPrefixSideChainConfiguration _ => .erPrefixSideChainConfiguration
  | .additionalVitaminDHydroxylStereochemistry _ => .additionalVitaminDHydroxylStereochemistry
  | .additionalRingsRetainImpliedConfiguration _ => .additionalRingsRetainImpliedConfiguration
  | .bridgedSteroidsUseAlphaBetaWhenNeeded _ _ => .bridgedSteroidsUseAlphaBetaWhenNeeded
  | .addendumSideChainAtomLocants _ => .addendumSideChainAtomLocants

@[simp] theorem sourceAssertion_provision_exact (row : Steroid1989.Provision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

structure SourceMeaning where
  sourceSection : String
  sourceKey : String
  semanticDomain : Steroid1989.SemanticDomain
  assertion : SourceAssertion
  deriving DecidableEq, Repr

/-- Total source-family compiler for the exact sixty-two-row Steroid 1989 slice. -/
def sourceMeaning (row : Steroid1989.Provision) : SourceMeaning :=
  ⟨row.sourceSection, row.sourceKey, Steroid1989.provisionSemanticDomain row,
    sourceAssertion row⟩

@[simp] theorem sourceMeaning_section_exact (row : Steroid1989.Provision) :
    (sourceMeaning row).sourceSection = row.sourceSection := by
  rfl

@[simp] theorem sourceMeaning_key_exact (row : Steroid1989.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by
  rfl

@[simp] theorem sourceMeaning_domain_exact (row : Steroid1989.Provision) :
    (sourceMeaning row).semanticDomain = Steroid1989.provisionSemanticDomain row := by
  rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def rows : List Steroid1989.Provision :=
  Steroid1989.Provision.all

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.steroid1989

def batch : GlobalNonDescriptorSourceMeaningBatch provisions :=
  totalMeaningBatch rows IUPACNormativeProvision.steroid1989 sourceMeaning
    (by intro _row; rfl)

@[simp] theorem provisions_exact :
    provisions = sourceProvisions .steroidRecommendations1989 := by
  exact steroid1989SemanticsSlice_exact

@[simp] theorem provision_count : provisions.length = 62 := by
  simp [provisions, rows]

@[simp] theorem entry_count : batch.entries.length = 62 := by
  rw [batch.entries_length, provision_count]

theorem provisions_nodup : provisions.Nodup := by
  exact Steroid1989.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

@[simp] theorem entry_provisions_exact :
    batch.entries.map GlobalNonDescriptorSourceMeaningEntry.provision = provisions :=
  batch.provisions_exact

theorem every_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (_member : entry ∈ batch.entries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment


theorem source_audit_still_open :
    ¬IUPACNormativeSource.ProvisionAuditComplete .steroidRecommendations1989 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete,
    Steroid1989.currentSourceReviewProvisionEnumerationConfirmed,
    Steroid1989.currentSourceReviewProseTableCoverageConfirmed,
    Steroid1989.currentSourceReviewFigureGraphTranscriptionsReviewed]

end GlobalNonDescriptorSteroidSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.every_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.source_audit_still_open
