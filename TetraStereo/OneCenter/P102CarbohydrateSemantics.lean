import TetraStereo.OneCenter.P10NormativeAudit
import TetraStereo.OneCenter.Basic
import TetraStereo.OneCenter.RS

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent Blue Book P-102 carbohydrate stereochemical semantics

This module transcribes the configuration-bearing part of the audited P-102 clauses.  It keeps
carbohydrate-relative `D/L` and anomeric `alpha/beta` separate from CIP `R/S`: only the reference
glyceraldehydes identify D with R and L with S.  Table 10.2/10.3 configurational-prefix spellings
are represented by an independently auditable table parameter rather than by production strings.
-/

namespace BlueBookP102

/-! ## Fischer projections and D/L -/

inductive FischerDepth where
  | awayFromViewer
  | towardViewer
  deriving DecidableEq, Repr

structure AcyclicFischerProjection where
  carbonChainVertical : Prop
  lowestNumberedCarbonAtTop : Prop
  verticalCarbonBonds : FischerDepth
  horizontalHydrogenAndHydroxyBonds : FischerDepth

def AcyclicFischerProjection.Normative (projection : AcyclicFischerProjection) : Prop :=
  projection.carbonChainVertical ∧ projection.lowestNumberedCarbonAtTop ∧
    projection.verticalCarbonBonds = .awayFromViewer ∧
    projection.horizontalHydrogenAndHydroxyBonds = .towardViewer

inductive CarbohydrateSeries where
  | D
  | L
  deriving DecidableEq, Repr

inductive FischerSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Series is determined by the hydroxy orientation at the highest-numbered chirality centre. -/
def seriesOfConfigurationalHydroxy : FischerSide → CarbohydrateSeries
  | .right => .D
  | .left => .L

@[simp] theorem right_is_D : seriesOfConfigurationalHydroxy .right = .D := rfl
@[simp] theorem left_is_L : seriesOfConfigurationalHydroxy .left = .L := rfl

/-- D/L is not a general synonym for R/S.  This relation contains only the explicitly stated
glyceraldehyde calibration. -/
inductive GlyceraldehydeCalibration : CarbohydrateSeries → RS → Prop where
  | dR : GlyceraldehydeCalibration .D .R
  | lS : GlyceraldehydeCalibration .L .S

theorem glyceraldehyde_calibration_functional
    {series : CarbohydrateSeries} {first second : RS}
    (firstCalibration : GlyceraldehydeCalibration series first)
    (secondCalibration : GlyceraldehydeCalibration series second) :
    first = second := by
  cases firstCalibration <;> cases secondCalibration <;> rfl

def IsConfigurationalAtom {Locant : Type*} [LinearOrder Locant]
    (chiralCenters : List Locant) (candidate : Locant) : Prop :=
  candidate ∈ chiralCenters ∧ ∀ center ∈ chiralCenters, center ≤ candidate

theorem configurationalAtom_unique {Locant : Type*} [LinearOrder Locant]
    {chiralCenters : List Locant} {first second : Locant}
    (firstConfig : IsConfigurationalAtom chiralCenters first)
    (secondConfig : IsConfigurationalAtom chiralCenters second) :
    first = second := by
  exact le_antisymm (secondConfig.2 first firstConfig.1) (firstConfig.2 second secondConfig.1)

/-! ## Cyclic forms and anomers -/

inductive SugarRingClass where
  | oxirose
  | oxetose
  | furanose
  | pyranose
  | septanose
  deriving DecidableEq, Repr

def SugarRingClass.memberCount : SugarRingClass → Nat
  | .oxirose => 3
  | .oxetose => 4
  | .furanose => 5
  | .pyranose => 6
  | .septanose => 7

theorem sugarRingClass_memberCount_bounds (ring : SugarRingClass) :
    3 ≤ ring.memberCount ∧ ring.memberCount ≤ 7 := by
  cases ring <;> decide

structure CyclicFischerProjection where
  carbonylCarbon : Nat
  ringOxygenSourceCarbon : Nat
  closureShownByLongBond : Prop

structure HaworthProjection where
  ringNearlyPerpendicularToPaper : Prop
  viewedSlightlyFromAbove : Prop
  nearEdgeDrawnBelowFarEdge : Prop
  ringOxygenBehind : Prop
  carbonOneAtRight : Prop

def HaworthProjection.Normative (projection : HaworthProjection) : Prop :=
  projection.ringNearlyPerpendicularToPaper ∧ projection.viewedSlightlyFromAbove ∧
    projection.nearEdgeDrawnBelowFarEdge ∧ projection.ringOxygenBehind ∧
    projection.carbonOneAtRight

inductive AnomericDescriptor where
  | alpha
  | beta
  deriving DecidableEq, Repr

inductive OxygenRelationship where
  | cis
  | trans
  deriving DecidableEq, Repr

/-- Anomeric alpha/beta is a relationship between the exocyclic anomeric oxygen and the oxygen at
the reference centre in the stated Fischer reference plane. -/
def anomericDescriptor : OxygenRelationship → AnomericDescriptor
  | .cis => .alpha
  | .trans => .beta

@[simp] theorem cis_anomer_is_alpha : anomericDescriptor .cis = .alpha := rfl
@[simp] theorem trans_anomer_is_beta : anomericDescriptor .trans = .beta := rfl

structure CyclicMonosaccharideConfiguration (Locant : Type*) where
  anomericCenter : Locant
  referenceCenter : Locant
  anomer : AnomericDescriptor
  series : CarbohydrateSeries
  anomerExplicit : Prop
  anomerImmediatelyBeforeSeries : Prop

/-- For a retained monosaccharide the anomeric reference centre is the configurational atom. -/
def RetainedAnomerReference {Locant : Type*}
    (cyclic : CyclicMonosaccharideConfiguration Locant)
    (configurationalAtom : Locant) : Prop :=
  cyclic.referenceCenter = configurationalAtom

structure LongChainAnomerReference (Locant : Type*) [LinearOrder Locant] where
  referenceCenter : Locant
  centersInRingPrefixGroup : List Locant
  reference_mem : referenceCenter ∈ centersInRingPrefixGroup
  reference_is_highest : ∀ center ∈ centersInRingPrefixGroup, center ≤ referenceCenter

inductive MonosaccharideConformation where
  | chair
  | boat
  | twist
  | otherNonplanar
  deriving DecidableEq, Repr

structure MillsDepiction where
  mainHemiacetalRingInPaperPlane : Prop
  hashedWedgesBelow : Prop
  solidWedgesAbove : Prop

def MillsDepiction.Normative (depiction : MillsDepiction) : Prop :=
  depiction.mainHemiacetalRingInPaperPlane ∧ depiction.hashedWedgesBelow ∧
    depiction.solidWedgesAbove

/-! ## Racemates, anomer mixtures, and parent selection -/

inductive SeriesScope where
  | D
  | L
  | DL
  deriving DecidableEq, Repr

structure DLRacemate (Entity : Type*) where
  dForm : Entity
  lForm : Entity
  distinct : dForm ≠ lForm
  enantiomeric : Prop
  equimolar : Prop

structure AnomerMixture where
  containsAlpha : Prop
  containsBeta : Prop
  descriptorsCitedAsAlphaCommaBetaAtFront : Prop
  haworthAnomericBondsReplacedByHAndOH : Prop

inductive ParentChoiceCriterion where
  | seniorCharacteristicGroup
  | greatestCarbonCount
  | alphabeticConfigurationPrefixOrRetainedName
  | DBeforeL
  | alphaBeforeBeta
  | greatestPrefixSubstitutionCount
  | lowestPrefixLocantSet
  | lowestFirstCitedPrefixLocant
  deriving DecidableEq, Repr

def ParentChoiceCriterion.rank : ParentChoiceCriterion → Nat
  | .seniorCharacteristicGroup => 0
  | .greatestCarbonCount => 1
  | .alphabeticConfigurationPrefixOrRetainedName => 2
  | .DBeforeL => 3
  | .alphaBeforeBeta => 4
  | .greatestPrefixSubstitutionCount => 5
  | .lowestPrefixLocantSet => 6
  | .lowestFirstCitedPrefixLocant => 7

theorem parentChoice_stereochemical_order :
    ParentChoiceCriterion.alphabeticConfigurationPrefixOrRetainedName.rank <
      ParentChoiceCriterion.DBeforeL.rank ∧
    ParentChoiceCriterion.DBeforeL.rank < ParentChoiceCriterion.alphaBeforeBeta.rank := by
  decide

/-! ## Configurational prefixes -/

inductive HydroxyConfiguration where
  | left
  | right
  deriving DecidableEq, Repr

/-- Independent authority table for names such as `glycero`, `gluco`, and `manno`. -/
structure ConfigurationalPrefixTable where
  prefixOf : List HydroxyConfiguration → Option String
  definedOnlyForOneToFour : ∀ pattern name,
    prefixOf pattern = some name → 1 ≤ pattern.length ∧ pattern.length ≤ 4
  functional : ∀ pattern first second,
    prefixOf pattern = some first → prefixOf pattern = some second → first = second

/-- P-102.5.1.1.2 groups centres from the carbonyl end in blocks of at most four, but cites the
farthest group first. -/
structure ValidMultiplePrefixGrouping where
  centersNearCarbonylToFar : List HydroxyConfiguration
  groupsNearToFar : List (List HydroxyConfiguration)
  groups_reconstruct : groupsNearToFar.flatten = centersNearCarbonylToFar
  groups_nonempty : ∀ group ∈ groupsNearToFar, group ≠ []
  groups_at_most_four : ∀ group ∈ groupsNearToFar, group.length ≤ 4
  all_but_last_have_four : ∀ group ∈ groupsNearToFar.dropLast, group.length = 4
  citationOrder : List (List HydroxyConfiguration)
  citationOrder_eq : citationOrder = groupsNearToFar.reverse

/-- Nonchiral gaps are ignored before configurational-prefix assignment. -/
def removeNonchiralGaps : List (Option HydroxyConfiguration) → List HydroxyConfiguration
  | [] => []
  | none :: rest => removeNonchiralGaps rest
  | some configuration :: rest => configuration :: removeNonchiralGaps rest

@[simp] theorem removeNonchiralGaps_none (rest : List (Option HydroxyConfiguration)) :
    removeNonchiralGaps (none :: rest) = removeNonchiralGaps rest :=
  rfl

inductive CarbonylTreatmentForPrefix where
  | twoKetoseSameAsAldose
  | carbonylAtThreeOrHigherIgnored
  deriving DecidableEq, Repr

/-! ## Deoxy, amino, and carbon-substituted sugars -/

structure DeoxygenationSemantics where
  affectsExistingChiralityCenter : Bool
  retainedNameCombinationPreferred : Bool
  systematicCarbohydrateNamePreferred : Bool
  substitutiveCIPNameAppropriate : Bool

def deoxygenationSemantics (affectsCenter : Bool) : DeoxygenationSemantics :=
  if affectsCenter then
    { affectsExistingChiralityCenter := true
      retainedNameCombinationPreferred := false
      systematicCarbohydrateNamePreferred := true
      substitutiveCIPNameAppropriate := true }
  else
    { affectsExistingChiralityCenter := false
      retainedNameCombinationPreferred := true
      systematicCarbohydrateNamePreferred := false
      substitutiveCIPNameAppropriate := true }

@[simp] theorem deoxy_affecting_center_rejects_retained_preference :
    (deoxygenationSemantics true).retainedNameCombinationPreferred = false :=
  rfl

inductive ReplacementGroup where
  | hydroxy
  | amino
  | highestPriorityCarbonSubstituent
  deriving DecidableEq, Repr

/-- Amino replacement preserves the carbohydrate-relative configuration by treating amino as the
hydroxy group it replaces. -/
def equivalentForCarbohydrateConfiguration : ReplacementGroup → ReplacementGroup → Prop
  | .amino, .hydroxy | .hydroxy, .amino => True
  | .highestPriorityCarbonSubstituent, .hydroxy
  | .hydroxy, .highestPriorityCarbonSubstituent => True
  | left, right => left = right

inductive ModifiedCenterRule where
  | highestCIPSubstituentTreatedAsHydroxy
  | useRSForAmbiguity
  | twiceSubstitutedMustUseRS
  | newTerminalCenterMustUseRS
  deriving DecidableEq, Repr

def modifiedCenterRule
    (terminal twiceSubstituted ambiguous : Bool) : ModifiedCenterRule :=
  if terminal then .newTerminalCenterMustUseRS
  else if twiceSubstituted then .twiceSubstitutedMustUseRS
  else if ambiguous then .useRSForAmbiguity
  else .highestCIPSubstituentTreatedAsHydroxy

@[simp] theorem terminal_center_uses_rs (twice ambiguous : Bool) :
    modifiedCenterRule true twice ambiguous = .newTerminalCenterMustUseRS :=
  rfl

@[simp] theorem twice_substituted_center_uses_rs (ambiguous : Bool) :
    modifiedCenterRule false true ambiguous = .twiceSubstitutedMustUseRS :=
  rfl

/-! ## Meso forms and tartaric acid -/

inductive MesoAlditolCondition where
  | unsubstitutedNamedMeso
  | asymmetricDerivativeRequiresDL
  | moreThanFourContiguousCentersRequiresDL
  deriving DecidableEq, Repr

structure AldaricAcidConfiguration where
  mesoDescriptorAllowedForClarity : Prop
  parentChosenByP1024 : Prop

inductive TartaricDescriptorPreference where
  | preferredRS
  | carbohydrateDLAlternative
  | opticalRotationAlternative
  deriving DecidableEq, Repr

def TartaricDescriptorPreference.isPreferred : TartaricDescriptorPreference → Bool
  | .preferredRS => true
  | _ => false

/-! ## Glycosyl groups, disaccharides, and oligosaccharides -/

inductive AnomericReferenceTarget where
  | anomericHydroxy
  | freeValence
  deriving DecidableEq, Repr

/-- When C-1 free valence is made by removing hydrogen rather than hydroxy, alpha/beta describes
the free valence. -/
def glycosylAnomericReference (freeValenceByHydrogenRemoval : Bool) :
    AnomericReferenceTarget :=
  if freeValenceByHydrogenRemoval then .freeValence else .anomericHydroxy

@[simp] theorem c1_hydrogen_removal_refers_to_free_valence :
    glycosylAnomericReference true = .freeValence :=
  rfl

inductive SaccharideReducingEnd where
  | noFreeHemiacetal
  | freeHemiacetal
  deriving DecidableEq, Repr

structure DisaccharideDescriptorRequirements where
  reducingEnd : SaccharideReducingEnd
  bothAnomericDescriptorsCited : Prop
  linkageLocantsCitedWhenFreeHemiacetal : Prop
  parentChosenByP1024 : Prop

structure OligosaccharideDescriptorRequirements where
  unitCount : Nat
  moreThanTwoUnits : 2 < unitCount
  reducingEnd : SaccharideReducingEnd
  componentAnomericDescriptorsCited : Prop
  linkageLocantsCited : Prop
  glycoseParentOnRightWhenFreeHemiacetal : Prop

/-! ## Clause-to-semantics ownership -/

inductive SemanticDomain where
  | projectionAndSeries
  | cyclicAndAnomeric
  | conformationAndDepiction
  | mixtures
  | parentChoice
  | configurationalPrefixes
  | modifiedSugars
  | mesoAndAcids
  | saccharideComponents
  deriving DecidableEq, Repr

def provisionSemanticDomain : BlueBookP10Audit.Provision → Option SemanticDomain
  | .p102AcyclicFischerProjection | .p102DAndL | .p102ConfigurationalAtom =>
      some .projectionAndSeries
  | .p102CyclicFischerProjection | .p102HaworthProjection
  | .p102AnomericCenterRequirement | .p102AlphaBetaAnomerRelation =>
      some .cyclicAndAnomeric
  | .p102MonosaccharideConformation | .p102MillsDepiction =>
      some .conformationAndDepiction
  | .p102DLRacemates | .p102AnomerMixtures => some .mixtures
  | .p102StereochemicalParentChoice => some .parentChoice
  | .p102AldoseConfigurationalPrefixTable | .p102KetoseConfigurationalPrefixTable
  | .p102MultipleConfigurationalPrefixGrouping | .p102NonchiralGapPrefixAssignment
  | .p102LongChainCyclicAnomerReference => some .configurationalPrefixes
  | .p102DeoxyConfigurationPreservationAndCIPBoundary
  | .p102AminoReplacementConfiguration | .p102CSubstitutionHydroxyEquivalence
  | .p102TwiceSubstitutedCenterRS | .p102TerminalSubstitutionNewCenter =>
      some .modifiedSugars
  | .p102MesoAlditols | .p102MesoAldaricAcids | .p102TartaricAcidRS =>
      some .mesoAndAcids
  | .p102GlycosylFreeValenceAnomerDescriptor | .p102DisaccharideAnomerDescriptors
  | .p102OligosaccharideAnomerDescriptors => some .saccharideComponents
  | _ => none

def p102Provisions : List BlueBookP10Audit.Provision :=
  [ .p102AcyclicFischerProjection
  , .p102DAndL
  , .p102ConfigurationalAtom
  , .p102CyclicFischerProjection
  , .p102HaworthProjection
  , .p102AnomericCenterRequirement
  , .p102AlphaBetaAnomerRelation
  , .p102MonosaccharideConformation
  , .p102MillsDepiction
  , .p102DLRacemates
  , .p102AnomerMixtures
  , .p102StereochemicalParentChoice
  , .p102AldoseConfigurationalPrefixTable
  , .p102KetoseConfigurationalPrefixTable
  , .p102MultipleConfigurationalPrefixGrouping
  , .p102NonchiralGapPrefixAssignment
  , .p102LongChainCyclicAnomerReference
  , .p102DeoxyConfigurationPreservationAndCIPBoundary
  , .p102AminoReplacementConfiguration
  , .p102CSubstitutionHydroxyEquivalence
  , .p102TwiceSubstitutedCenterRS
  , .p102TerminalSubstitutionNewCenter
  , .p102MesoAlditols
  , .p102MesoAldaricAcids
  , .p102TartaricAcidRS
  , .p102GlycosylFreeValenceAnomerDescriptor
  , .p102DisaccharideAnomerDescriptors
  , .p102OligosaccharideAnomerDescriptors
  ]

@[simp] theorem p102Provisions_length : p102Provisions.length = 28 := by
  rfl

theorem every_p102_provision_has_semantic_domain :
    ∀ provision ∈ p102Provisions, (provisionSemanticDomain provision).isSome := by
  intro provision member
  cases provision <;>
    simp [p102Provisions, provisionSemanticDomain] at member ⊢

end BlueBookP102

end TetraStereo.OneCenter
