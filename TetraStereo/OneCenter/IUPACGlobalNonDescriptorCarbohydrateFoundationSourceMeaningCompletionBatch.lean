import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataBatch
import TetraStereo.KernelOnly

set_option autoImplicit false












namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateFoundationSourceMeaning

open GlobalNonDescriptorIndexedSourceData

def seriesExampleCenters : List Carbohydrate1996Foundation.ChiralCenter :=
  [⟨2, .left⟩, ⟨4, .right⟩, ⟨3, .left⟩]

def ringSizeInventory : List (Nat × Carbohydrate1996Foundation.RingSizeName) :=
  [ (3, Carbohydrate1996Foundation.ringSizeName 3)
  , (4, Carbohydrate1996Foundation.ringSizeName 4)
  , (5, Carbohydrate1996Foundation.ringSizeName 5)
  , (6, Carbohydrate1996Foundation.ringSizeName 6)
  , (7, Carbohydrate1996Foundation.ringSizeName 7)
  , (8, Carbohydrate1996Foundation.ringSizeName 8) ]

def haworthSideInventory :
    List (Carbohydrate1996Foundation.FischerSide × Carbohydrate1996Foundation.HaworthSide) :=
  [ (.right, Carbohydrate1996Foundation.haworthSideFromModifiedFischer .right)
  , (.left, Carbohydrate1996Foundation.haworthSideFromModifiedFischer .left) ]

def haworthNumberingInventory :
    List (Carbohydrate1996Foundation.HaworthOrientation ×
      Carbohydrate1996Foundation.NumberingSense) :=
  [ (.conventional, Carbohydrate1996Foundation.haworthNumberingSense .conventional)
  , (.inverted, Carbohydrate1996Foundation.haworthNumberingSense .inverted) ]

def millsSideInventory :
    List (Carbohydrate1996Foundation.MillsBond × Carbohydrate1996Foundation.HaworthSide) :=
  [ (.dashed, Carbohydrate1996Foundation.millsSide .dashed)
  , (.thickened, Carbohydrate1996Foundation.millsSide .thickened) ]

def anomerRelationInventory :
    List (Carbohydrate1996Foundation.FormalOxygenRelation ×
      Carbohydrate1996Foundation.Anomer) :=
  [ (.cis, Carbohydrate1996Foundation.anomerFromOxygenRelation .cis)
  , (.trans, Carbohydrate1996Foundation.anomerFromOxygenRelation .trans) ]

def multiplePrefixReferenceExample : Carbohydrate1996Foundation.ConfigurationalGroup :=
  ⟨[2, 3, 4, 5], 5⟩

def shapeInventory : List (Nat × List Carbohydrate1996Foundation.RingShape) :=
  [ (5, Carbohydrate1996Foundation.shapesForRingMemberCount 5)
  , (6, Carbohydrate1996Foundation.shapesForRingMemberCount 6) ]

def conformationInventory :
    List (Carbohydrate1996Foundation.ConformationTableRow ×
      Carbohydrate1996Foundation.ConformationRowData) :=
  Carbohydrate1996Foundation.ConformationTableRow.all.map fun row => (row, row.data)

/- Typed assertion constructors independently name every source clause; modeled functions and
tables retain concrete values. -/
inductive SourceAssertion where
  | fischerChainVerticalLowestNumberAtTop
  | fischerEachCenterInPaperPlane
      (geometry : Carbohydrate1996Foundation.FischerCenterGeometry)
  | fischerNeighboringCarbonsBelowPlane
      (geometry : Carbohydrate1996Foundation.FischerCenterGeometry)
  | fischerHydrogenAndHydroxyAbovePlane
      (geometry : Carbohydrate1996Foundation.FischerCenterGeometry)
  | fischerProjectionDoesNotAssertConformation (assertsConformation : Bool)
  | dlIsAbsoluteGlyceraldehydeRelationship
  | highestNumberedChiralCenterIsConfigurationalAtom
      (centers : List Carbohydrate1996Foundation.ChiralCenter)
      (series : Option Carbohydrate1996Foundation.DLSeries)
  | rightHydroxyAtConfigurationalAtomMeansD
      (side : Carbohydrate1996Foundation.HorizontalSide)
      (series : Carbohydrate1996Foundation.DLSeries)
  | ringOxygenBridgeCanDetermineDL
  | systematicPrefixSpecifiesEveryCHOHCenter
  | multiplePrefixesEachHaveOwnDL
  | anomericConfigurationIsSeparateRelation
  | racemateUsesDL (series : List Carbohydrate1996Foundation.DLSeries)
  | mesoRequiresSymmetryAndOpticalInactivity
      (hasPlaneOfSymmetry : Bool) (symmetry : Carbohydrate1996Foundation.SymmetryClass)
  | rotationSignPrecedesButDoesNotDefineDL
      (first second : Carbohydrate1996Foundation.SeriesAndRotation)
  | racemateMayUsePlusMinus (sign : Carbohydrate1996Foundation.OpticalRotationSign)
  | ringSizeNameInventory
      (inventory : List (Nat × Carbohydrate1996Foundation.RingSizeName))
  | ringClosureLocantsCarbonylFirst
      (closure : Carbohydrate1996Foundation.RingClosureLocants) (printed : List Nat)
  | absentRingSizeHasNoImplication
  | cyclicFischerUsesLongRingBond
  | modifiedFischerRotatesRingFormingCenter
  | modifiedFischerOxygenBridgeBehindPlane
  | modifiedFischerExposesCisTrans
  | ketoseModifiedFischerMayDiffer
  | haworthReferenceOrientation (orientation : Carbohydrate1996Foundation.HaworthOrientation)
  | haworthReferenceNumberingClockwise
      (inventory : List (Carbohydrate1996Foundation.HaworthOrientation ×
        Carbohydrate1996Foundation.NumberingSense))
  | modifiedFischerRightBecomesHaworthBelow
      (inventory : List (Carbohydrate1996Foundation.FischerSide ×
        Carbohydrate1996Foundation.HaworthSide))
  | modifiedFischerLeftBecomesHaworthAbove
      (inventory : List (Carbohydrate1996Foundation.FischerSide ×
        Carbohydrate1996Foundation.HaworthSide))
  | dAldohexoseC6Above
      (series : Carbohydrate1996Foundation.DLSeries) (locant : Nat)
      (side : Carbohydrate1996Foundation.HaworthSide)
  | ringFormingCenterOrientsRemainingChain
  | unconventionalHaworthOrientationsAllowed
  | invertedHaworthNumberingCounterclockwise
      (inventory : List (Carbohydrate1996Foundation.HaworthOrientation ×
        Carbohydrate1996Foundation.NumberingSense))
  | millsDashedMeansBelow
      (inventory : List (Carbohydrate1996Foundation.MillsBond ×
        Carbohydrate1996Foundation.HaworthSide))
  | millsThickMeansAbove
      (inventory : List (Carbohydrate1996Foundation.MillsBond ×
        Carbohydrate1996Foundation.HaworthSide))
  | haworthRepresentationImpliesPlanarRing (impliesPlanar : Bool)
  | explicitConformationalDrawingOverridesPlanarModel (overrides : Bool)
  | ringClosureCreatesAnomericCenter
  | anomersDefinedRelativeToReferenceAtom
  | ordinaryAnomericReferenceIsConfigurationalAtom
  | multiplePrefixAnomericReferenceRule
      (group : Carbohydrate1996Foundation.ConfigurationalGroup) (referenceLocant : Nat)
  | alphaMeansFormalCisOxygens
      (inventory : List (Carbohydrate1996Foundation.FormalOxygenRelation ×
        Carbohydrate1996Foundation.Anomer))
  | betaMeansFormalTransOxygens
      (inventory : List (Carbohydrate1996Foundation.FormalOxygenRelation ×
        Carbohydrate1996Foundation.Anomer))
  | anomericSymbolPlacement
  | simpleSugarReferenceEqualsConfigurationalAtom
  | alphaBetaMarksSameRingSizeMixture
      (knowledge : Carbohydrate1996Foundation.AnomerKnowledge)
      (symbols : List Carbohydrate1996Foundation.Anomer)
  | wavyBondMarksAnomerMixture
  | alphaBetaRequiresLowerAnomericLocant
      (anomericLocant referenceLocant : Nat)
      (descriptors : List Carbohydrate1996Foundation.AnomerDescriptor)
  | reverseRingClosureUsesRS
      (anomericLocant referenceLocant : Nat)
      (descriptors : List Carbohydrate1996Foundation.AnomerDescriptor)
  | reverseClosureRingLocantsCarbonylFirst
      (closure : Carbohydrate1996Foundation.RingClosureLocants) (printed : List Nat)
  | conformationalDescriptorIsNameSuffix
  | fiveMemberedRingShapeInventory (shapes : List Carbohydrate1996Foundation.RingShape)
  | sixMemberedRingShapeInventory (shapes : List Carbohydrate1996Foundation.RingShape)
  | upperReferencePlaneSideUsesSuperscript
      (symbol : Carbohydrate1996Foundation.ConformationSymbol)
  | lowerReferencePlaneSideUsesSubscript
      (symbol : Carbohydrate1996Foundation.ConformationSymbol)
  | heteroatomExoplanarLocantsUseElementSymbol
  | shapeSpecificReferencePlaneRules
      (inventory : List (Carbohydrate1996Foundation.ConformationTableRow ×
        Carbohydrate1996Foundation.ConformationRowData))
  | enantiomerConformationalSymbolsDiffer
      (first second : Carbohydrate1996Foundation.ConformationSymbol)
  | enantiomersUseSameReferencePlane
  | glucoseMirrorFourCOneToOneCFour
      (first second : Carbohydrate1996Foundation.ConformationSymbol)
  | conformationTable
      (row : Carbohydrate1996Foundation.ConformationTableRow)
      (data : Carbohydrate1996Foundation.ConformationRowData)
  deriving Repr

def sourceAssertion : Carbohydrate1996Foundation.Provision → SourceAssertion
  | .fischerChainVerticalLowestNumberAtTop => .fischerChainVerticalLowestNumberAtTop
  | .fischerEachCenterInPaperPlane =>
      .fischerEachCenterInPaperPlane Carbohydrate1996Foundation.canonicalFischerCenter
  | .fischerNeighboringCarbonsBelowPlane =>
      .fischerNeighboringCarbonsBelowPlane Carbohydrate1996Foundation.canonicalFischerCenter
  | .fischerHydrogenAndHydroxyAbovePlane =>
      .fischerHydrogenAndHydroxyAbovePlane Carbohydrate1996Foundation.canonicalFischerCenter
  | .fischerProjectionDoesNotAssertConformation =>
      .fischerProjectionDoesNotAssertConformation false
  | .dlIsAbsoluteGlyceraldehydeRelationship => .dlIsAbsoluteGlyceraldehydeRelationship
  | .highestNumberedChiralCenterIsConfigurationalAtom =>
      .highestNumberedChiralCenterIsConfigurationalAtom seriesExampleCenters
        (Carbohydrate1996Foundation.monosaccharideSeries? seriesExampleCenters)
  | .rightHydroxyAtConfigurationalAtomMeansD =>
      .rightHydroxyAtConfigurationalAtomMeansD .right
        (Carbohydrate1996Foundation.seriesFromConfigurationalHydroxy .right)
  | .ringOxygenBridgeCanDetermineDL => .ringOxygenBridgeCanDetermineDL
  | .systematicPrefixSpecifiesEveryCHOHCenter => .systematicPrefixSpecifiesEveryCHOHCenter
  | .multiplePrefixesEachHaveOwnDL => .multiplePrefixesEachHaveOwnDL
  | .anomericConfigurationIsSeparateRelation => .anomericConfigurationIsSeparateRelation
  | .racemateUsesDL => .racemateUsesDL [.D, .L]
  | .mesoRequiresSymmetryAndOpticalInactivity =>
      .mesoRequiresSymmetryAndOpticalInactivity true
        (Carbohydrate1996Foundation.mesoClass true)
  | .rotationSignPrecedesButDoesNotDefineDL =>
      .rotationSignPrecedesButDoesNotDefineDL
        Carbohydrate1996Foundation.dGlucoseReading Carbohydrate1996Foundation.dFructoseReading
  | .racemateMayUsePlusMinus => .racemateMayUsePlusMinus .plusMinus
  | .ringSizeNameInventory => .ringSizeNameInventory ringSizeInventory
  | .ringClosureLocantsCarbonylFirst =>
      let closure : Carbohydrate1996Foundation.RingClosureLocants := ⟨1, 5⟩
      .ringClosureLocantsCarbonylFirst closure
        (Carbohydrate1996Foundation.printedRingClosureLocants closure)
  | .absentRingSizeHasNoImplication => .absentRingSizeHasNoImplication
  | .cyclicFischerUsesLongRingBond => .cyclicFischerUsesLongRingBond
  | .modifiedFischerRotatesRingFormingCenter => .modifiedFischerRotatesRingFormingCenter
  | .modifiedFischerOxygenBridgeBehindPlane => .modifiedFischerOxygenBridgeBehindPlane
  | .modifiedFischerExposesCisTrans => .modifiedFischerExposesCisTrans
  | .ketoseModifiedFischerMayDiffer => .ketoseModifiedFischerMayDiffer
  | .haworthReferenceOrientation => .haworthReferenceOrientation .conventional
  | .haworthReferenceNumberingClockwise =>
      .haworthReferenceNumberingClockwise haworthNumberingInventory
  | .modifiedFischerRightBecomesHaworthBelow =>
      .modifiedFischerRightBecomesHaworthBelow haworthSideInventory
  | .modifiedFischerLeftBecomesHaworthAbove =>
      .modifiedFischerLeftBecomesHaworthAbove haworthSideInventory
  | .dAldohexoseC6Above => .dAldohexoseC6Above .D 6 .above
  | .ringFormingCenterOrientsRemainingChain => .ringFormingCenterOrientsRemainingChain
  | .unconventionalHaworthOrientationsAllowed => .unconventionalHaworthOrientationsAllowed
  | .invertedHaworthNumberingCounterclockwise =>
      .invertedHaworthNumberingCounterclockwise haworthNumberingInventory
  | .millsDashedMeansBelow => .millsDashedMeansBelow millsSideInventory
  | .millsThickMeansAbove => .millsThickMeansAbove millsSideInventory
  | .haworthRepresentationImpliesPlanarRing => .haworthRepresentationImpliesPlanarRing true
  | .explicitConformationalDrawingOverridesPlanarModel =>
      .explicitConformationalDrawingOverridesPlanarModel true
  | .ringClosureCreatesAnomericCenter => .ringClosureCreatesAnomericCenter
  | .anomersDefinedRelativeToReferenceAtom => .anomersDefinedRelativeToReferenceAtom
  | .ordinaryAnomericReferenceIsConfigurationalAtom =>
      .ordinaryAnomericReferenceIsConfigurationalAtom
  | .multiplePrefixAnomericReferenceRule =>
      .multiplePrefixAnomericReferenceRule multiplePrefixReferenceExample
        (Carbohydrate1996Foundation.anomericReferenceFromGroups multiplePrefixReferenceExample)
  | .alphaMeansFormalCisOxygens => .alphaMeansFormalCisOxygens anomerRelationInventory
  | .betaMeansFormalTransOxygens => .betaMeansFormalTransOxygens anomerRelationInventory
  | .anomericSymbolPlacement => .anomericSymbolPlacement
  | .simpleSugarReferenceEqualsConfigurationalAtom =>
      .simpleSugarReferenceEqualsConfigurationalAtom
  | .alphaBetaMarksSameRingSizeMixture =>
      .alphaBetaMarksSameRingSizeMixture .equilibriumAlphaBeta
        (Carbohydrate1996Foundation.anomerNameSymbols .equilibriumAlphaBeta)
  | .wavyBondMarksAnomerMixture => .wavyBondMarksAnomerMixture
  | .alphaBetaRequiresLowerAnomericLocant =>
      .alphaBetaRequiresLowerAnomericLocant 1 5
        [ .alphaBeta .alpha
        , .alphaBeta .beta ]
  | .reverseRingClosureUsesRS => .reverseRingClosureUsesRS 6 2 [.cipR, .cipS]
  | .reverseClosureRingLocantsCarbonylFirst =>
      let closure : Carbohydrate1996Foundation.RingClosureLocants := ⟨6, 2⟩
      .reverseClosureRingLocantsCarbonylFirst closure
        (Carbohydrate1996Foundation.printedRingClosureLocants closure)
  | .conformationalDescriptorIsNameSuffix => .conformationalDescriptorIsNameSuffix
  | .fiveMemberedRingShapeInventory =>
      .fiveMemberedRingShapeInventory (Carbohydrate1996Foundation.shapesForRingMemberCount 5)
  | .sixMemberedRingShapeInventory =>
      .sixMemberedRingShapeInventory (Carbohydrate1996Foundation.shapesForRingMemberCount 6)
  | .upperReferencePlaneSideUsesSuperscript =>
      .upperReferencePlaneSideUsesSuperscript Carbohydrate1996Foundation.glucoseFourCOne
  | .lowerReferencePlaneSideUsesSubscript =>
      .lowerReferencePlaneSideUsesSubscript Carbohydrate1996Foundation.glucoseFourCOne
  | .heteroatomExoplanarLocantsUseElementSymbol => .heteroatomExoplanarLocantsUseElementSymbol
  | .shapeSpecificReferencePlaneRules => .shapeSpecificReferencePlaneRules conformationInventory
  | .enantiomerConformationalSymbolsDiffer =>
      .enantiomerConformationalSymbolsDiffer Carbohydrate1996Foundation.glucoseFourCOne
        Carbohydrate1996Foundation.glucoseOneCFour
  | .enantiomersUseSameReferencePlane => .enantiomersUseSameReferencePlane
  | .glucoseMirrorFourCOneToOneCFour =>
      .glucoseMirrorFourCOneToOneCFour Carbohydrate1996Foundation.glucoseFourCOne
        (Carbohydrate1996Foundation.mirrorConformationSymbol
          Carbohydrate1996Foundation.glucoseFourCOne)
  | .conformationTable row => .conformationTable row row.data

def SourceAssertion.provision : SourceAssertion → Carbohydrate1996Foundation.Provision
  | .fischerChainVerticalLowestNumberAtTop => .fischerChainVerticalLowestNumberAtTop
  | .fischerEachCenterInPaperPlane _ => .fischerEachCenterInPaperPlane
  | .fischerNeighboringCarbonsBelowPlane _ => .fischerNeighboringCarbonsBelowPlane
  | .fischerHydrogenAndHydroxyAbovePlane _ => .fischerHydrogenAndHydroxyAbovePlane
  | .fischerProjectionDoesNotAssertConformation _ => .fischerProjectionDoesNotAssertConformation
  | .dlIsAbsoluteGlyceraldehydeRelationship => .dlIsAbsoluteGlyceraldehydeRelationship
  | .highestNumberedChiralCenterIsConfigurationalAtom _ _ =>
      .highestNumberedChiralCenterIsConfigurationalAtom
  | .rightHydroxyAtConfigurationalAtomMeansD _ _ => .rightHydroxyAtConfigurationalAtomMeansD
  | .ringOxygenBridgeCanDetermineDL => .ringOxygenBridgeCanDetermineDL
  | .systematicPrefixSpecifiesEveryCHOHCenter => .systematicPrefixSpecifiesEveryCHOHCenter
  | .multiplePrefixesEachHaveOwnDL => .multiplePrefixesEachHaveOwnDL
  | .anomericConfigurationIsSeparateRelation => .anomericConfigurationIsSeparateRelation
  | .racemateUsesDL _ => .racemateUsesDL
  | .mesoRequiresSymmetryAndOpticalInactivity _ _ => .mesoRequiresSymmetryAndOpticalInactivity
  | .rotationSignPrecedesButDoesNotDefineDL _ _ => .rotationSignPrecedesButDoesNotDefineDL
  | .racemateMayUsePlusMinus _ => .racemateMayUsePlusMinus
  | .ringSizeNameInventory _ => .ringSizeNameInventory
  | .ringClosureLocantsCarbonylFirst _ _ => .ringClosureLocantsCarbonylFirst
  | .absentRingSizeHasNoImplication => .absentRingSizeHasNoImplication
  | .cyclicFischerUsesLongRingBond => .cyclicFischerUsesLongRingBond
  | .modifiedFischerRotatesRingFormingCenter => .modifiedFischerRotatesRingFormingCenter
  | .modifiedFischerOxygenBridgeBehindPlane => .modifiedFischerOxygenBridgeBehindPlane
  | .modifiedFischerExposesCisTrans => .modifiedFischerExposesCisTrans
  | .ketoseModifiedFischerMayDiffer => .ketoseModifiedFischerMayDiffer
  | .haworthReferenceOrientation _ => .haworthReferenceOrientation
  | .haworthReferenceNumberingClockwise _ => .haworthReferenceNumberingClockwise
  | .modifiedFischerRightBecomesHaworthBelow _ => .modifiedFischerRightBecomesHaworthBelow
  | .modifiedFischerLeftBecomesHaworthAbove _ => .modifiedFischerLeftBecomesHaworthAbove
  | .dAldohexoseC6Above _ _ _ => .dAldohexoseC6Above
  | .ringFormingCenterOrientsRemainingChain => .ringFormingCenterOrientsRemainingChain
  | .unconventionalHaworthOrientationsAllowed => .unconventionalHaworthOrientationsAllowed
  | .invertedHaworthNumberingCounterclockwise _ => .invertedHaworthNumberingCounterclockwise
  | .millsDashedMeansBelow _ => .millsDashedMeansBelow
  | .millsThickMeansAbove _ => .millsThickMeansAbove
  | .haworthRepresentationImpliesPlanarRing _ => .haworthRepresentationImpliesPlanarRing
  | .explicitConformationalDrawingOverridesPlanarModel _ =>
      .explicitConformationalDrawingOverridesPlanarModel
  | .ringClosureCreatesAnomericCenter => .ringClosureCreatesAnomericCenter
  | .anomersDefinedRelativeToReferenceAtom => .anomersDefinedRelativeToReferenceAtom
  | .ordinaryAnomericReferenceIsConfigurationalAtom =>
      .ordinaryAnomericReferenceIsConfigurationalAtom
  | .multiplePrefixAnomericReferenceRule _ _ => .multiplePrefixAnomericReferenceRule
  | .alphaMeansFormalCisOxygens _ => .alphaMeansFormalCisOxygens
  | .betaMeansFormalTransOxygens _ => .betaMeansFormalTransOxygens
  | .anomericSymbolPlacement => .anomericSymbolPlacement
  | .simpleSugarReferenceEqualsConfigurationalAtom => .simpleSugarReferenceEqualsConfigurationalAtom
  | .alphaBetaMarksSameRingSizeMixture _ _ => .alphaBetaMarksSameRingSizeMixture
  | .wavyBondMarksAnomerMixture => .wavyBondMarksAnomerMixture
  | .alphaBetaRequiresLowerAnomericLocant _ _ _ => .alphaBetaRequiresLowerAnomericLocant
  | .reverseRingClosureUsesRS _ _ _ => .reverseRingClosureUsesRS
  | .reverseClosureRingLocantsCarbonylFirst _ _ => .reverseClosureRingLocantsCarbonylFirst
  | .conformationalDescriptorIsNameSuffix => .conformationalDescriptorIsNameSuffix
  | .fiveMemberedRingShapeInventory _ => .fiveMemberedRingShapeInventory
  | .sixMemberedRingShapeInventory _ => .sixMemberedRingShapeInventory
  | .upperReferencePlaneSideUsesSuperscript _ => .upperReferencePlaneSideUsesSuperscript
  | .lowerReferencePlaneSideUsesSubscript _ => .lowerReferencePlaneSideUsesSubscript
  | .heteroatomExoplanarLocantsUseElementSymbol => .heteroatomExoplanarLocantsUseElementSymbol
  | .shapeSpecificReferencePlaneRules _ => .shapeSpecificReferencePlaneRules
  | .enantiomerConformationalSymbolsDiffer _ _ => .enantiomerConformationalSymbolsDiffer
  | .enantiomersUseSameReferencePlane => .enantiomersUseSameReferencePlane
  | .glucoseMirrorFourCOneToOneCFour _ _ => .glucoseMirrorFourCOneToOneCFour
  | .conformationTable row _ => .conformationTable row

@[simp] theorem sourceAssertion_provision_exact (row : Carbohydrate1996Foundation.Provision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

structure SourceMeaning where
  sourceSection : String
  sourceKey : String
  semanticDomain : Carbohydrate1996Foundation.SemanticDomain
  assertion : SourceAssertion
  deriving Repr

def sourceMeaning (row : Carbohydrate1996Foundation.Provision) : SourceMeaning :=
  ⟨row.sourceSection, row.sourceKey, Carbohydrate1996Foundation.provisionSemanticDomain row,
    sourceAssertion row⟩

@[simp] theorem sourceMeaning_section_exact (row : Carbohydrate1996Foundation.Provision) :
    (sourceMeaning row).sourceSection = row.sourceSection := by
  rfl

@[simp] theorem sourceMeaning_key_exact (row : Carbohydrate1996Foundation.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by
  rfl

@[simp] theorem sourceMeaning_domain_exact (row : Carbohydrate1996Foundation.Provision) :
    (sourceMeaning row).semanticDomain =
      Carbohydrate1996Foundation.provisionSemanticDomain row := by
  rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def fullFamilyRows : List Carbohydrate1996Foundation.Provision :=
  Carbohydrate1996Foundation.Provision.all

def fullFamilyProvisions : List IUPACNormativeProvision :=
  fullFamilyRows.map IUPACNormativeProvision.carbohydrate1996Foundation

def completionRows : List Carbohydrate1996Foundation.Provision :=
  Carbohydrate1996Foundation.Provision.base

def completionProvisions : List IUPACNormativeProvision :=
  completionRows.map IUPACNormativeProvision.carbohydrate1996Foundation

def completionBatch : GlobalNonDescriptorSourceMeaningBatch completionProvisions :=
  totalMeaningBatch completionRows IUPACNormativeProvision.carbohydrate1996Foundation sourceMeaning
    (by intro _row; rfl)

@[simp] theorem full_family_provisions_exact :
    fullFamilyProvisions = carbohydrate1996FoundationSemanticsSlice := by
  rfl

@[simp] theorem full_family_provision_count : fullFamilyProvisions.length = 71 := by
  simp [fullFamilyProvisions, fullFamilyRows]

@[simp] theorem completion_provision_count : completionProvisions.length = 59 := by
  simp [completionProvisions, completionRows, Carbohydrate1996Foundation.Provision.base]

@[simp] theorem completion_entry_count : completionBatch.entries.length = 59 := by
  rw [completionBatch.entries_length, completion_provision_count]

private theorem completion_rows_then_indexed_exact :
    completionRows ++ GlobalNonDescriptorIndexedSourceData.carbohydrateFoundationRows =
      fullFamilyRows := by
  simp [completionRows, fullFamilyRows,
    GlobalNonDescriptorIndexedSourceData.carbohydrateFoundationRows,
    Carbohydrate1996Foundation.Provision.all]

theorem completion_then_indexed_exact_source_order :
    completionProvisions ++ GlobalNonDescriptorIndexedSourceData.carbohydrateFoundationProvisions =
      carbohydrate1996FoundationSemanticsSlice := by
  rw [← full_family_provisions_exact]
  simp only [completionProvisions,
    GlobalNonDescriptorIndexedSourceData.carbohydrateFoundationProvisions,
    fullFamilyProvisions, ← List.map_append]
  rw [completion_rows_then_indexed_exact]

theorem materialized_order_perm_source :
    (GlobalNonDescriptorIndexedSourceData.carbohydrateFoundationProvisions ++
      completionProvisions).Perm carbohydrate1996FoundationSemanticsSlice := by
  calc
    (GlobalNonDescriptorIndexedSourceData.carbohydrateFoundationProvisions ++
      completionProvisions).Perm
        (completionProvisions ++
          GlobalNonDescriptorIndexedSourceData.carbohydrateFoundationProvisions) :=
      List.perm_append_comm
    _ = carbohydrate1996FoundationSemanticsSlice :=
      completion_then_indexed_exact_source_order

theorem completion_disjoint_indexed :
    completionProvisions.Disjoint
      GlobalNonDescriptorIndexedSourceData.carbohydrateFoundationProvisions := by
  apply List.disjoint_of_nodup_append
  rw [completion_then_indexed_exact_source_order]
  exact Carbohydrate1996Foundation.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

theorem completion_provisions_nodup : completionProvisions.Nodup := by
  exact Carbohydrate1996Foundation.Provision.all_nodup.of_append_left.map
    (by intro left right equal; cases equal; rfl)

@[simp] theorem completion_entry_provisions_exact :
    completionBatch.entries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      completionProvisions :=
  completionBatch.provisions_exact

theorem every_completion_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (_member : entry ∈ completionBatch.entries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment

theorem source_audit_still_open :
    ¬IUPACNormativeSource.ProvisionAuditComplete .carbohydrateRecommendations1996 := by
  exact IUPACNormativeSource.provisionAuditIncomplete_of_figure_review_open _ rfl

end GlobalNonDescriptorCarbohydrateFoundationSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.full_family_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completion_then_indexed_exact_source_order
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.materialized_order_perm_source
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.completion_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.every_completion_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFoundationSourceMeaning.source_audit_still_open
