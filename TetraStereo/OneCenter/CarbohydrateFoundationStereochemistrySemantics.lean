import TetraStereo.OneCenter.Basic
import TetraStereo.OneCenter.P10DelegatedAuthorityCorpus

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent carbohydrate foundation stereochemistry semantics

This module audits the configuration-bearing foundation of *Nomenclature of Carbohydrates
(Recommendations 1996)*: 2-Carb-3 through 2-Carb-7.  It covers acyclic Fischer projections,
D/L and configurational prefixes, cyclic representations, anomeric alpha/beta, and the complete
twelve-row conformation table.

Later rules for named monosaccharide classes, derivatives, glycosides, oligosaccharides,
polysaccharides, and the Appendix remain separate source obligations.  Consequently this module is
not a claim that the full 1996 authority has been transcribed.  No production analyzer is imported.

The reverse ring-closure rule of 2-Carb-6.4 is modelled as a *routing decision* only: the family
(`alphaBetaPermitted` versus `requiresCIP`) is decided from the two printed locants and nothing
else.  This module assigns no `R`/`S` value in the reverse branch.  The checked `R`/`S` consumer
that consumes an actual molecular graph, resolved CIP priorities and a physical realization lives
in `CarbohydrateRingClosureFidelity`; no molecular priority information is smuggled into the
locant-only router.
-/

namespace Carbohydrate1996Foundation

inductive ConformationTableRow where
  | aldofuranoseEnvelopeBelow2
  | aldofuranoseEnvelopeAbove3
  | aldofuranoseTwistAbove3Below2
  | aldofuranoseTwistAbove2Below1
  | aldopyranoseChairAbove4Below1
  | pyranoidLactoneChairAbove1Below4
  | aldopyranoseBoatAbove2And5
  | aldopyranoseBoatBelow1And4
  | aldopyranoseSkewAbove1Below3
  | aldopyranoseSkewAbove2BelowO
  | aldopyranoseHalfChairAbove5BelowS
  | pyranoidLactoneEnvelopeAbove5
  deriving DecidableEq, Repr

namespace ConformationTableRow

def all : List ConformationTableRow :=
  [ .aldofuranoseEnvelopeBelow2
  , .aldofuranoseEnvelopeAbove3
  , .aldofuranoseTwistAbove3Below2
  , .aldofuranoseTwistAbove2Below1
  , .aldopyranoseChairAbove4Below1
  , .pyranoidLactoneChairAbove1Below4
  , .aldopyranoseBoatAbove2And5
  , .aldopyranoseBoatBelow1And4
  , .aldopyranoseSkewAbove1Below3
  , .aldopyranoseSkewAbove2BelowO
  , .aldopyranoseHalfChairAbove5BelowS
  , .pyranoidLactoneEnvelopeAbove5
  ]

@[simp] theorem mem_all (row : ConformationTableRow) : row ∈ all := by
  cases row <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 12 := by decide

end ConformationTableRow

inductive Provision where
  | fischerChainVerticalLowestNumberAtTop
  | fischerEachCenterInPaperPlane
  | fischerNeighboringCarbonsBelowPlane
  | fischerHydrogenAndHydroxyAbovePlane
  | fischerProjectionDoesNotAssertConformation
  | dlIsAbsoluteGlyceraldehydeRelationship
  | highestNumberedChiralCenterIsConfigurationalAtom
  | rightHydroxyAtConfigurationalAtomMeansD
  | ringOxygenBridgeCanDetermineDL
  | systematicPrefixSpecifiesEveryCHOHCenter
  | multiplePrefixesEachHaveOwnDL
  | anomericConfigurationIsSeparateRelation
  | racemateUsesDL
  | mesoRequiresSymmetryAndOpticalInactivity
  | rotationSignPrecedesButDoesNotDefineDL
  | racemateMayUsePlusMinus
  | ringSizeNameInventory
  | ringClosureLocantsCarbonylFirst
  | absentRingSizeHasNoImplication
  | cyclicFischerUsesLongRingBond
  | modifiedFischerRotatesRingFormingCenter
  | modifiedFischerOxygenBridgeBehindPlane
  | modifiedFischerExposesCisTrans
  | ketoseModifiedFischerMayDiffer
  | haworthReferenceOrientation
  | haworthReferenceNumberingClockwise
  | modifiedFischerRightBecomesHaworthBelow
  | modifiedFischerLeftBecomesHaworthAbove
  | dAldohexoseC6Above
  | ringFormingCenterOrientsRemainingChain
  | unconventionalHaworthOrientationsAllowed
  | invertedHaworthNumberingCounterclockwise
  | millsDashedMeansBelow
  | millsThickMeansAbove
  | haworthRepresentationImpliesPlanarRing
  | explicitConformationalDrawingOverridesPlanarModel
  | ringClosureCreatesAnomericCenter
  | anomersDefinedRelativeToReferenceAtom
  | ordinaryAnomericReferenceIsConfigurationalAtom
  | multiplePrefixAnomericReferenceRule
  | alphaMeansFormalCisOxygens
  | betaMeansFormalTransOxygens
  | anomericSymbolPlacement
  | simpleSugarReferenceEqualsConfigurationalAtom
  | alphaBetaMarksSameRingSizeMixture
  | wavyBondMarksAnomerMixture
  | alphaBetaRequiresLowerAnomericLocant
  | reverseRingClosureUsesRS
  | reverseClosureRingLocantsCarbonylFirst
  | conformationalDescriptorIsNameSuffix
  | fiveMemberedRingShapeInventory
  | sixMemberedRingShapeInventory
  | upperReferencePlaneSideUsesSuperscript
  | lowerReferencePlaneSideUsesSubscript
  | heteroatomExoplanarLocantsUseElementSymbol
  | shapeSpecificReferencePlaneRules
  | enantiomerConformationalSymbolsDiffer
  | enantiomersUseSameReferencePlane
  | glucoseMirrorFourCOneToOneCFour
  | conformationTable (row : ConformationTableRow)
  deriving DecidableEq, Repr

namespace Provision

def base : List Provision :=
  [ .fischerChainVerticalLowestNumberAtTop
  , .fischerEachCenterInPaperPlane
  , .fischerNeighboringCarbonsBelowPlane
  , .fischerHydrogenAndHydroxyAbovePlane
  , .fischerProjectionDoesNotAssertConformation
  , .dlIsAbsoluteGlyceraldehydeRelationship
  , .highestNumberedChiralCenterIsConfigurationalAtom
  , .rightHydroxyAtConfigurationalAtomMeansD
  , .ringOxygenBridgeCanDetermineDL
  , .systematicPrefixSpecifiesEveryCHOHCenter
  , .multiplePrefixesEachHaveOwnDL
  , .anomericConfigurationIsSeparateRelation
  , .racemateUsesDL
  , .mesoRequiresSymmetryAndOpticalInactivity
  , .rotationSignPrecedesButDoesNotDefineDL
  , .racemateMayUsePlusMinus
  , .ringSizeNameInventory
  , .ringClosureLocantsCarbonylFirst
  , .absentRingSizeHasNoImplication
  , .cyclicFischerUsesLongRingBond
  , .modifiedFischerRotatesRingFormingCenter
  , .modifiedFischerOxygenBridgeBehindPlane
  , .modifiedFischerExposesCisTrans
  , .ketoseModifiedFischerMayDiffer
  , .haworthReferenceOrientation
  , .haworthReferenceNumberingClockwise
  , .modifiedFischerRightBecomesHaworthBelow
  , .modifiedFischerLeftBecomesHaworthAbove
  , .dAldohexoseC6Above
  , .ringFormingCenterOrientsRemainingChain
  , .unconventionalHaworthOrientationsAllowed
  , .invertedHaworthNumberingCounterclockwise
  , .millsDashedMeansBelow
  , .millsThickMeansAbove
  , .haworthRepresentationImpliesPlanarRing
  , .explicitConformationalDrawingOverridesPlanarModel
  , .ringClosureCreatesAnomericCenter
  , .anomersDefinedRelativeToReferenceAtom
  , .ordinaryAnomericReferenceIsConfigurationalAtom
  , .multiplePrefixAnomericReferenceRule
  , .alphaMeansFormalCisOxygens
  , .betaMeansFormalTransOxygens
  , .anomericSymbolPlacement
  , .simpleSugarReferenceEqualsConfigurationalAtom
  , .alphaBetaMarksSameRingSizeMixture
  , .wavyBondMarksAnomerMixture
  , .alphaBetaRequiresLowerAnomericLocant
  , .reverseRingClosureUsesRS
  , .reverseClosureRingLocantsCarbonylFirst
  , .conformationalDescriptorIsNameSuffix
  , .fiveMemberedRingShapeInventory
  , .sixMemberedRingShapeInventory
  , .upperReferencePlaneSideUsesSuperscript
  , .lowerReferencePlaneSideUsesSubscript
  , .heteroatomExoplanarLocantsUseElementSymbol
  , .shapeSpecificReferencePlaneRules
  , .enantiomerConformationalSymbolsDiffer
  , .enantiomersUseSameReferencePlane
  , .glucoseMirrorFourCOneToOneCFour
  ]

def all : List Provision :=
  base ++ ConformationTableRow.all.map Provision.conformationTable

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision with
  | conformationTable row =>
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := Provision.conformationTable) row.mem_all
  | _ => simp [all, base]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 71 := by decide

def sourceSection : Provision → String
  | .fischerChainVerticalLowestNumberAtTop | .fischerEachCenterInPaperPlane
  | .fischerNeighboringCarbonsBelowPlane | .fischerHydrogenAndHydroxyAbovePlane
  | .fischerProjectionDoesNotAssertConformation => "Carbohydrate-1996/2-Carb-3"
  | .dlIsAbsoluteGlyceraldehydeRelationship => "Carbohydrate-1996/2-Carb-4.1"
  | .highestNumberedChiralCenterIsConfigurationalAtom
  | .rightHydroxyAtConfigurationalAtomMeansD
  | .ringOxygenBridgeCanDetermineDL => "Carbohydrate-1996/2-Carb-4.2"
  | .systematicPrefixSpecifiesEveryCHOHCenter | .multiplePrefixesEachHaveOwnDL
  | .anomericConfigurationIsSeparateRelation => "Carbohydrate-1996/2-Carb-4.3"
  | .racemateUsesDL | .mesoRequiresSymmetryAndOpticalInactivity =>
      "Carbohydrate-1996/2-Carb-4.4"
  | .rotationSignPrecedesButDoesNotDefineDL | .racemateMayUsePlusMinus =>
      "Carbohydrate-1996/2-Carb-4.5"
  | .ringSizeNameInventory | .ringClosureLocantsCarbonylFirst
  | .absentRingSizeHasNoImplication => "Carbohydrate-1996/2-Carb-5.1"
  | .cyclicFischerUsesLongRingBond => "Carbohydrate-1996/2-Carb-5.2"
  | .modifiedFischerRotatesRingFormingCenter | .modifiedFischerOxygenBridgeBehindPlane
  | .modifiedFischerExposesCisTrans | .ketoseModifiedFischerMayDiffer =>
      "Carbohydrate-1996/2-Carb-5.3"
  | .haworthReferenceOrientation | .haworthReferenceNumberingClockwise
  | .modifiedFischerRightBecomesHaworthBelow | .modifiedFischerLeftBecomesHaworthAbove
  | .dAldohexoseC6Above | .ringFormingCenterOrientsRemainingChain =>
      "Carbohydrate-1996/2-Carb-5.4"
  | .unconventionalHaworthOrientationsAllowed
  | .invertedHaworthNumberingCounterclockwise => "Carbohydrate-1996/2-Carb-5.5"
  | .millsDashedMeansBelow | .millsThickMeansAbove => "Carbohydrate-1996/2-Carb-5.6"
  | .haworthRepresentationImpliesPlanarRing
  | .explicitConformationalDrawingOverridesPlanarModel => "Carbohydrate-1996/2-Carb-5.7"
  | .ringClosureCreatesAnomericCenter | .anomersDefinedRelativeToReferenceAtom =>
      "Carbohydrate-1996/2-Carb-6.1"
  | .ordinaryAnomericReferenceIsConfigurationalAtom | .multiplePrefixAnomericReferenceRule
  | .alphaMeansFormalCisOxygens | .betaMeansFormalTransOxygens
  | .anomericSymbolPlacement | .simpleSugarReferenceEqualsConfigurationalAtom =>
      "Carbohydrate-1996/2-Carb-6.2"
  | .alphaBetaMarksSameRingSizeMixture | .wavyBondMarksAnomerMixture =>
      "Carbohydrate-1996/2-Carb-6.3"
  | .alphaBetaRequiresLowerAnomericLocant | .reverseRingClosureUsesRS
  | .reverseClosureRingLocantsCarbonylFirst => "Carbohydrate-1996/2-Carb-6.4"
  | .conformationalDescriptorIsNameSuffix => "Carbohydrate-1996/2-Carb-7.1"
  | .fiveMemberedRingShapeInventory | .sixMemberedRingShapeInventory =>
      "Carbohydrate-1996/2-Carb-7.2"
  | .upperReferencePlaneSideUsesSuperscript | .lowerReferencePlaneSideUsesSubscript
  | .heteroatomExoplanarLocantsUseElementSymbol
  | .shapeSpecificReferencePlaneRules => "Carbohydrate-1996/2-Carb-7.3"
  | .enantiomerConformationalSymbolsDiffer | .enantiomersUseSameReferencePlane
  | .glucoseMirrorFourCOneToOneCFour => "Carbohydrate-1996/2-Carb-7.4"
  | .conformationTable _ => "Carbohydrate-1996/2-Carb-7.1/Table 1"

def sourceKey (provision : Provision) : String := provision.sourceSection

end Provision

/-! ## Fischer projection and D/L -/

inductive PaperDepth where
  | inPlane
  | abovePlane
  | belowPlane
  deriving DecidableEq, Repr

structure FischerCenterGeometry where
  center : PaperDepth
  neighboringChainAtoms : PaperDepth
  hydrogenAndHydroxy : PaperDepth
  deriving DecidableEq, Repr

def canonicalFischerCenter : FischerCenterGeometry :=
  ⟨.inPlane, .belowPlane, .abovePlane⟩

@[simp] theorem canonical_fischer_depths_are_exact :
    canonicalFischerCenter = ⟨.inPlane, .belowPlane, .abovePlane⟩ := rfl

inductive HorizontalSide where
  | right
  | left
  deriving DecidableEq, Repr

inductive DLSeries where
  | D
  | L
  deriving DecidableEq, Repr

namespace DLSeries

def inverted : DLSeries → DLSeries
  | .D => .L
  | .L => .D

end DLSeries

def seriesFromConfigurationalHydroxy : HorizontalSide → DLSeries
  | .right => .D
  | .left => .L

@[simp] theorem right_configurational_hydroxy_is_D :
    seriesFromConfigurationalHydroxy .right = .D := rfl

structure ChiralCenter where
  locant : Nat
  hydroxySide : HorizontalSide
  deriving DecidableEq, Repr

def highestNumberedCenter? : List ChiralCenter → Option ChiralCenter
  | [] => none
  | first :: rest =>
      some (rest.foldl (fun current candidate =>
        if current.locant < candidate.locant then candidate else current) first)

def monosaccharideSeries? (centers : List ChiralCenter) : Option DLSeries :=
  (highestNumberedCenter? centers).map fun center =>
    seriesFromConfigurationalHydroxy center.hydroxySide

@[simp] theorem highest_numbered_center_controls_series :
    monosaccharideSeries? [⟨2, .left⟩, ⟨4, .right⟩, ⟨3, .left⟩] = some .D := by
  decide

inductive OpticalRotationSign where
  | plus
  | minus
  | plusMinus
  deriving DecidableEq, Repr

structure SeriesAndRotation where
  series : DLSeries
  rotation : OpticalRotationSign
  deriving DecidableEq, Repr

def dGlucoseReading : SeriesAndRotation := ⟨.D, .plus⟩
def dFructoseReading : SeriesAndRotation := ⟨.D, .minus⟩

theorem D_does_not_determine_optical_rotation_sign :
    dGlucoseReading.series = dFructoseReading.series ∧
      dGlucoseReading.rotation ≠ dFructoseReading.rotation := by
  decide

inductive SymmetryClass where
  | chiral
  | meso
  deriving DecidableEq, Repr

def mesoClass (hasPlaneOfSymmetry : Bool) : SymmetryClass :=
  if hasPlaneOfSymmetry then .meso else .chiral

/-! ## Cyclic representations -/

inductive RingSizeName where
  | oxirose
  | oxetose
  | furanose
  | pyranose
  | septanose
  | octanose
  | larger (memberCount : Nat)
  deriving DecidableEq, Repr

def ringSizeName : Nat → RingSizeName
  | 3 => .oxirose
  | 4 => .oxetose
  | 5 => .furanose
  | 6 => .pyranose
  | 7 => .septanose
  | 8 => .octanose
  | memberCount => .larger memberCount

@[simp] theorem named_ring_sizes_are_exact :
    [ringSizeName 3, ringSizeName 4, ringSizeName 5,
      ringSizeName 6, ringSizeName 7, ringSizeName 8] =
    [.oxirose, .oxetose, .furanose, .pyranose, .septanose, .octanose] := by
  decide

structure RingClosureLocants where
  carbonylLocant : Nat
  hydroxyLocant : Nat
  deriving DecidableEq, Repr

def printedRingClosureLocants (closure : RingClosureLocants) : List Nat :=
  [closure.carbonylLocant, closure.hydroxyLocant]

inductive FischerSide where
  | right
  | left
  deriving DecidableEq, Repr

inductive HaworthSide where
  | below
  | above
  deriving DecidableEq, Repr

def haworthSideFromModifiedFischer : FischerSide → HaworthSide
  | .right => .below
  | .left => .above

@[simp] theorem modified_fischer_to_haworth_sides_are_exact :
    haworthSideFromModifiedFischer .right = .below ∧
      haworthSideFromModifiedFischer .left = .above := by
  decide

inductive HaworthOrientation where
  | conventional
  | inverted
  deriving DecidableEq, Repr

inductive NumberingSense where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

def haworthNumberingSense : HaworthOrientation → NumberingSense
  | .conventional => .clockwise
  | .inverted => .counterclockwise

inductive MillsBond where
  | dashed
  | thickened
  deriving DecidableEq, Repr

def millsSide : MillsBond → HaworthSide
  | .dashed => .below
  | .thickened => .above

/-! ## Anomeric configuration -/

inductive Anomer where
  | alpha
  | beta
  deriving DecidableEq, Repr

inductive FormalOxygenRelation where
  | cis
  | trans
  deriving DecidableEq, Repr

def anomerFromOxygenRelation : FormalOxygenRelation → Anomer
  | .cis => .alpha
  | .trans => .beta

@[simp] theorem alpha_beta_oxygen_relations_are_exact :
    anomerFromOxygenRelation .cis = .alpha ∧
      anomerFromOxygenRelation .trans = .beta := by
  decide

structure ConfigurationalGroup where
  centerLocantsAscending : List Nat
  highestLocant : Nat
  deriving DecidableEq, Repr

/-- With multiple configurational prefixes, select the group next to the anomeric center that
participates in the ring; its highest-numbered center is the reference atom. -/
def anomericReferenceFromGroups (ringParticipatingAdjacentGroup : ConfigurationalGroup) : Nat :=
  ringParticipatingAdjacentGroup.highestLocant

/-- The descriptor alphabet of 2-Carb-6: either the anomeric letter pair, or a sequence-rule
`R`/`S` symbol.  Supplied values of this type are retained losslessly by the fragment source-data
codec (`FragmentSourceDatum.carbohydrateAnomer`). -/
inductive AnomerDescriptor where
  | alphaBeta (anomer : Anomer)
  | cipR
  | cipS
  deriving DecidableEq, Repr

/-- The descriptor *family* permitted by a ring closure.  This is a routing decision only: it says
which alphabet the name may use, never which member of that alphabet applies. -/
inductive AnomerDescriptorFamily where
  /-- The Greek letters `alpha` and `beta` may be used. -/
  | alphaBetaPermitted
  /-- The configuration must be expressed as `R` or `S` according to the sequence rule. -/
  | requiresCIP
  deriving DecidableEq, Repr

namespace AnomerDescriptorFamily

def all : List AnomerDescriptorFamily := [.alphaBetaPermitted, .requiresCIP]

@[simp] theorem mem_all (family : AnomerDescriptorFamily) : family ∈ all := by
  cases family <;> simp [all]

theorem all_nodup : all.Nodup := by decide

end AnomerDescriptorFamily

/-- Source family decision of 2-Carb-6.4.  The Greek letters are applicable only when the anomeric
carbon atom has a lower locant than the anomeric reference atom.  In the other ring-closure
direction -- a carbonyl group with the higher locant closing onto a hydroxy group with the lower
locant -- the configuration is indicated by `R` or `S` according to the sequence rule.

The decision reads only the two printed locants.  It has no molecule, priority-order, geometry or
atom-type input, so it carries no `R`/`S` information. -/
def anomerDescriptorFamily (anomericLocant referenceLocant : Nat) : AnomerDescriptorFamily :=
  if anomericLocant < referenceLocant then .alphaBetaPermitted else .requiresCIP

@[simp] theorem anomerDescriptorFamily_eq_alphaBetaPermitted_iff
    (anomericLocant referenceLocant : Nat) :
    anomerDescriptorFamily anomericLocant referenceLocant = .alphaBetaPermitted ↔
      anomericLocant < referenceLocant := by
  unfold anomerDescriptorFamily
  by_cases lower : anomericLocant < referenceLocant <;> simp [lower]

@[simp] theorem anomerDescriptorFamily_eq_requiresCIP_iff
    (anomericLocant referenceLocant : Nat) :
    anomerDescriptorFamily anomericLocant referenceLocant = .requiresCIP ↔
      ¬ anomericLocant < referenceLocant := by
  unfold anomerDescriptorFamily
  by_cases lower : anomericLocant < referenceLocant <;> simp [lower]

/-- The family decision is a function of the two locants alone.  In particular it is constant under
any change of molecule, priority assignment or geometry: the router contains no such input. -/
theorem anomerDescriptorFamily_congr (anomericLocant referenceLocant anomericLocant'
    referenceLocant' : Nat) (anomericEq : anomericLocant = anomericLocant')
    (referenceEq : referenceLocant = referenceLocant') :
    anomerDescriptorFamily anomericLocant referenceLocant =
      anomerDescriptorFamily anomericLocant' referenceLocant' := by
  rw [anomericEq, referenceEq]

namespace AnomerDescriptor

/-- The family to which a supplied descriptor belongs.  This classifies the descriptor alphabet;
it does not assert that the supplied descriptor is correct for any particular molecule. -/
def family : AnomerDescriptor → AnomerDescriptorFamily
  | .alphaBeta _ => .alphaBetaPermitted
  | .cipR => .requiresCIP
  | .cipS => .requiresCIP

@[simp] theorem family_alphaBeta (anomer : Anomer) :
    (AnomerDescriptor.alphaBeta anomer).family = .alphaBetaPermitted := rfl

@[simp] theorem family_cipR : AnomerDescriptor.cipR.family = .requiresCIP := rfl

@[simp] theorem family_cipS : AnomerDescriptor.cipS.family = .requiresCIP := rfl

end AnomerDescriptor

/-- Family-restricted descriptor router for a ring closure.

* In the lower-anomeric-locant branch it emits exactly `some (alphaBeta anomer)`, the only
  descriptor family 2-Carb-6.4 permits there.
* In the reverse-closure branch it emits `none`.  It does not fabricate `R` from `alpha` or `S`
  from `beta`: the actual sequence-rule assignment is produced by the checked CIP consumer in
  `CarbohydrateRingClosureFidelity`, which requires an actual molecular graph, resolved CIP
  priorities and a physical realization.

Consequently this definition is a source router, not a descriptor oracle. -/
def descriptorForRingClosure? (anomericLocant referenceLocant : Nat) (anomer : Anomer) :
    Option AnomerDescriptor :=
  if anomericLocant < referenceLocant then some (.alphaBeta anomer) else none

@[simp] theorem descriptorForRingClosure?_lower (anomericLocant referenceLocant : Nat)
    (anomer : Anomer) (lower : anomericLocant < referenceLocant) :
    descriptorForRingClosure? anomericLocant referenceLocant anomer =
      some (.alphaBeta anomer) := by
  simp [descriptorForRingClosure?, lower]

@[simp] theorem descriptorForRingClosure?_reverse (anomericLocant referenceLocant : Nat)
    (anomer : Anomer) (notLower : ¬ anomericLocant < referenceLocant) :
    descriptorForRingClosure? anomericLocant referenceLocant anomer = none := by
  simp [descriptorForRingClosure?, notLower]

/-- A letter descriptor is produced exactly in the `alphaBetaPermitted` family. -/
theorem descriptorForRingClosure?_isSome_iff_family (anomericLocant referenceLocant : Nat)
    (anomer : Anomer) :
    (descriptorForRingClosure? anomericLocant referenceLocant anomer).isSome ↔
      anomerDescriptorFamily anomericLocant referenceLocant = .alphaBetaPermitted := by
  by_cases lower : anomericLocant < referenceLocant <;>
    simp [descriptorForRingClosure?, anomerDescriptorFamily, lower]

/-- The lower-locant branch yields the supplied letter descriptor and nothing else. -/
theorem descriptorForRingClosure?_lower_unique (anomericLocant referenceLocant : Nat)
    (anomer : Anomer) (lower : anomericLocant < referenceLocant) (descriptor : AnomerDescriptor) :
    descriptorForRingClosure? anomericLocant referenceLocant anomer = some descriptor ↔
      descriptor = .alphaBeta anomer := by
  rw [descriptorForRingClosure?_lower anomericLocant referenceLocant anomer lower]
  simp [eq_comm]

/-- The lower-locant branch never emits a sequence-rule descriptor. -/
theorem descriptorForRingClosure?_lower_not_cip (anomericLocant referenceLocant : Nat)
    (anomer : Anomer) (lower : anomericLocant < referenceLocant) :
    descriptorForRingClosure? anomericLocant referenceLocant anomer ≠ some .cipR ∧
      descriptorForRingClosure? anomericLocant referenceLocant anomer ≠ some .cipS := by
  simp [descriptorForRingClosure?, lower]

/-- The reverse-closure branch emits no descriptor at all, so no `alpha`-to-`R` (or
`beta`-to-`S`, or any other) letter assignment exists at this layer. -/
theorem descriptorForRingClosure?_reverse_none (anomericLocant referenceLocant : Nat)
    (anomer : Anomer) (notLower : ¬ anomericLocant < referenceLocant)
    (descriptor : AnomerDescriptor) :
    descriptorForRingClosure? anomericLocant referenceLocant anomer ≠ some descriptor := by
  simp [descriptorForRingClosure?, notLower]

@[simp] theorem lower_anomeric_locant_permits_alpha_beta (anomer : Anomer) :
    descriptorForRingClosure? 1 5 anomer = some (.alphaBeta anomer) := by
  simp

/-- Reverse closure (locants 6 and 2, the 2-Carb-6.4 dialdose direction) routes away from the
alpha/beta family entirely; the checked `R`/`S` consumer is the only producer for it. -/
theorem reverse_closure_routes_away_from_alpha_beta (anomer : Anomer) :
    descriptorForRingClosure? 6 2 anomer = none := by
  simp

inductive AnomerKnowledge where
  | alphaOnly
  | betaOnly
  | equilibriumAlphaBeta
  deriving DecidableEq, Repr

def anomerNameSymbols : AnomerKnowledge → List Anomer
  | .alphaOnly => [.alpha]
  | .betaOnly => [.beta]
  | .equilibriumAlphaBeta => [.alpha, .beta]

/-! ## Ring conformation and complete Table 1 -/

inductive RingShape where
  | envelope
  | twist
  | chair
  | boat
  | skew
  | halfChair
  deriving DecidableEq, Repr

inductive SugarRingKind where
  | aldofuranose
  | aldopyranose
  | pyranoidLactone
  deriving DecidableEq, Repr

structure ConformationRowData where
  ringKind : SugarRingKind
  shape : RingShape
  referencePlaneAtoms : List String
  abovePlaneAtoms : List String
  belowPlaneAtoms : List String
  notationText : String
  deriving DecidableEq, Repr

def ConformationTableRow.data : ConformationTableRow → ConformationRowData
  | .aldofuranoseEnvelopeBelow2 =>
      ⟨.aldofuranose, .envelope, ["O-4", "C-1", "C-3", "C-4"], [], ["C-2"], "E₂"⟩
  | .aldofuranoseEnvelopeAbove3 =>
      ⟨.aldofuranose, .envelope, ["C-1", "C-2", "C-4", "O-4"], ["C-3"], [], "³E"⟩
  | .aldofuranoseTwistAbove3Below2 =>
      ⟨.aldofuranose, .twist, ["C-1", "O-4", "C-4"], ["C-3"], ["C-2"], "³T₂"⟩
  | .aldofuranoseTwistAbove2Below1 =>
      ⟨.aldofuranose, .twist, ["C-3", "C-4", "O-4"], ["C-2"], ["C-1"], "²T₁"⟩
  | .aldopyranoseChairAbove4Below1 =>
      ⟨.aldopyranose, .chair, ["C-2", "C-3", "C-5", "O-5"], ["C-4"], ["C-1"], "⁴C₁"⟩
  | .pyranoidLactoneChairAbove1Below4 =>
      ⟨.pyranoidLactone, .chair, ["C-2", "C-3", "C-5", "O-5"], ["C-1"], ["C-4"], "¹C₄"⟩
  | .aldopyranoseBoatAbove2And5 =>
      ⟨.aldopyranose, .boat, ["O-5", "C-1", "C-3", "C-4"], ["C-2", "C-5"], [], "²,⁵B"⟩
  | .aldopyranoseBoatBelow1And4 =>
      ⟨.aldopyranose, .boat, ["C-2", "C-3", "C-5", "O-5"], [], ["C-1", "C-4"], "B₁,₄"⟩
  | .aldopyranoseSkewAbove1Below3 =>
      ⟨.aldopyranose, .skew, ["C-2", "C-4", "C-5", "O-5"], ["C-1"], ["C-3"], "¹S₃"⟩
  | .aldopyranoseSkewAbove2BelowO =>
      ⟨.aldopyranose, .skew, ["C-1", "C-3", "C-4", "C-5"], ["C-2"], ["O-5"], "²Sₒ"⟩
  | .aldopyranoseHalfChairAbove5BelowS =>
      ⟨.aldopyranose, .halfChair, ["C-1", "C-2", "C-3", "C-4"], ["C-5"], ["S-5"], "⁵Hₛ"⟩
  | .pyranoidLactoneEnvelopeAbove5 =>
      ⟨.pyranoidLactone, .envelope,
        ["C-1", "C-2", "C-3", "C-4", "O-5"], ["C-5"], [], "⁵E"⟩

theorem every_conformation_row_has_a_nonempty_reference_plane
    (row : ConformationTableRow) : row.data.referencePlaneAtoms ≠ [] := by
  cases row <;> decide

theorem conformation_notations_are_pairwise_distinct :
    (ConformationTableRow.all.map fun row => row.data.notationText).Nodup := by
  decide

def shapesForRingMemberCount : Nat → List RingShape
  | 5 => [.envelope, .twist]
  | 6 => [.chair, .boat, .skew, .halfChair, .envelope]
  | _ => []

@[simp] theorem ring_shape_inventories_are_exact :
    shapesForRingMemberCount 5 = [.envelope, .twist] ∧
      shapesForRingMemberCount 6 = [.chair, .boat, .skew, .halfChair, .envelope] := by
  decide

structure ConformationSymbol where
  shape : RingShape
  superscriptAtoms : List String
  subscriptAtoms : List String
  deriving DecidableEq, Repr

def mirrorConformationSymbol (symbol : ConformationSymbol) : ConformationSymbol :=
  { symbol with
    superscriptAtoms := symbol.subscriptAtoms
    subscriptAtoms := symbol.superscriptAtoms }

def glucoseFourCOne : ConformationSymbol := ⟨.chair, ["4"], ["1"]⟩
def glucoseOneCFour : ConformationSymbol := ⟨.chair, ["1"], ["4"]⟩

@[simp] theorem glucose_enantiomer_conformation_symbol_is_swapped :
    mirrorConformationSymbol glucoseFourCOne = glucoseOneCFour := rfl

/-! ## Clause ownership -/

inductive SemanticDomain where
  | fischerProjection
  | dlSeries
  | configurationalPrefix
  | mixtureAndRotation
  | ringSizeAndClosure
  | modifiedFischer
  | haworth
  | mills
  | planarVersusConformational
  | anomerDefinition
  | anomerReference
  | anomerMixture
  | reverseClosure
  | conformationNotation
  | conformationMirror
  | conformationTable
  deriving DecidableEq, Repr

def provisionSemanticDomain : Provision → SemanticDomain
  | .fischerChainVerticalLowestNumberAtTop | .fischerEachCenterInPaperPlane
  | .fischerNeighboringCarbonsBelowPlane | .fischerHydrogenAndHydroxyAbovePlane
  | .fischerProjectionDoesNotAssertConformation => .fischerProjection
  | .dlIsAbsoluteGlyceraldehydeRelationship
  | .highestNumberedChiralCenterIsConfigurationalAtom
  | .rightHydroxyAtConfigurationalAtomMeansD
  | .ringOxygenBridgeCanDetermineDL => .dlSeries
  | .systematicPrefixSpecifiesEveryCHOHCenter | .multiplePrefixesEachHaveOwnDL
  | .anomericConfigurationIsSeparateRelation => .configurationalPrefix
  | .racemateUsesDL | .mesoRequiresSymmetryAndOpticalInactivity
  | .rotationSignPrecedesButDoesNotDefineDL | .racemateMayUsePlusMinus => .mixtureAndRotation
  | .ringSizeNameInventory | .ringClosureLocantsCarbonylFirst
  | .absentRingSizeHasNoImplication | .cyclicFischerUsesLongRingBond => .ringSizeAndClosure
  | .modifiedFischerRotatesRingFormingCenter | .modifiedFischerOxygenBridgeBehindPlane
  | .modifiedFischerExposesCisTrans | .ketoseModifiedFischerMayDiffer => .modifiedFischer
  | .haworthReferenceOrientation | .haworthReferenceNumberingClockwise
  | .modifiedFischerRightBecomesHaworthBelow | .modifiedFischerLeftBecomesHaworthAbove
  | .dAldohexoseC6Above | .ringFormingCenterOrientsRemainingChain
  | .unconventionalHaworthOrientationsAllowed
  | .invertedHaworthNumberingCounterclockwise => .haworth
  | .millsDashedMeansBelow | .millsThickMeansAbove => .mills
  | .haworthRepresentationImpliesPlanarRing
  | .explicitConformationalDrawingOverridesPlanarModel => .planarVersusConformational
  | .ringClosureCreatesAnomericCenter | .anomersDefinedRelativeToReferenceAtom
  | .alphaMeansFormalCisOxygens | .betaMeansFormalTransOxygens
  | .anomericSymbolPlacement => .anomerDefinition
  | .ordinaryAnomericReferenceIsConfigurationalAtom | .multiplePrefixAnomericReferenceRule
  | .simpleSugarReferenceEqualsConfigurationalAtom => .anomerReference
  | .alphaBetaMarksSameRingSizeMixture | .wavyBondMarksAnomerMixture => .anomerMixture
  | .alphaBetaRequiresLowerAnomericLocant | .reverseRingClosureUsesRS
  | .reverseClosureRingLocantsCarbonylFirst => .reverseClosure
  | .conformationalDescriptorIsNameSuffix | .fiveMemberedRingShapeInventory
  | .sixMemberedRingShapeInventory | .upperReferencePlaneSideUsesSuperscript
  | .lowerReferencePlaneSideUsesSubscript | .heteroatomExoplanarLocantsUseElementSymbol
  | .shapeSpecificReferencePlaneRules => .conformationNotation
  | .enantiomerConformationalSymbolsDiffer | .enantiomersUseSameReferencePlane
  | .glucoseMirrorFourCOneToOneCFour => .conformationMirror
  | .conformationTable _ => .conformationTable

theorem every_provision_has_an_independent_semantic_domain
    (provision : Provision) : ∃ domain, provisionSemanticDomain provision = domain := by
  exact ⟨provisionSemanticDomain provision, rfl⟩

end Carbohydrate1996Foundation

end TetraStereo.OneCenter
