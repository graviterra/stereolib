import TetraStereo.OneCenter.IUPACP92SaturatedRingProductionRefinement
import TetraStereo.OneCenter.ProductionCIPRule1aCertifiedGlobal

set_option autoImplicit false

/-!
# Production refinement for the two P-92 mancude rows

`ExactAtomicNumber` deliberately permits unreduced representations: `1/2` and `2/4` are the same
Rule-1a value.  The reviewed mancude digraph relation therefore judges rational value equality,
not structural record equality.  This is the same semantic boundary proved by the certified full
production mancude dispatcher.

Both remaining P-92 rows are projections of one pointwise bridge: whenever the production
dispatcher returns a label for a localized mancude edge, that label has exactly the independent
maximum-matching average value.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open DeclarativeCIP
open RawMolecule

/-! ## One pointwise production/reference value bridge -/

theorem certifiedMancudeRule1aLabel_exactAverageValue
    (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (bondRecordsUnique : mol.BondRecordsUnique)
    (attached duplicated : Fin mol.atomCount)
    (localized : mol.toMoleculeGraph.LocalizedMancudeEdge attached duplicated)
    (label : CIPAtomicLabel)
    (produced : mol.mancudeRule1aLabel? attached.val duplicated.val = some label) :
    label.toExactAtomicNumber.value =
      (mol.toMoleculeGraph.exactMancudeAverage attached).value := by
  have sound := mol.certifiedMancudeRule1aSound wellFormed bondRecordsUnique
    attached duplicated label produced
  rw [mol.toMoleculeGraph.exactRule1aMultipleBond_of_localized localized] at sound
  exact sound

/-! ## Mancude digraph observation -/

def p92ProductionMancudeDigraphObservation
    (mol : RawMolecule) (attached : Fin mol.atomCount) (label : CIPAtomicLabel) :
    P92MancudeDigraphAuthorityObservation where
  atomCount := mol.atomCount
  molecule := mol.toMoleculeGraph
  attached := attached
  representedAtomicNumber := label.toExactAtomicNumber

theorem p92ProductionMancudeDigraph_judged
    (source : AuthoritativeChemicalInput)
    (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (bondRecordsUnique : mol.BondRecordsUnique)
    (represents : P92ClassicalConstitutionRepresents source mol.toMoleculeGraph)
    (attached duplicated : Fin mol.atomCount)
    (localized : mol.toMoleculeGraph.LocalizedMancudeEdge attached duplicated)
    (represented : P92MancudeAttachmentRepresented mol.toMoleculeGraph attached)
    (label : CIPAtomicLabel)
    (produced : mol.mancudeRule1aLabel? attached.val duplicated.val = some label) :
    p92MancudeDigraphReference.Judges source
      (p92ProductionMancudeDigraphObservation mol attached label) := by
  exact ⟨represents, represented,
    certifiedMancudeRule1aLabel_exactAverageValue mol wellFormed bondRecordsUnique attached
      duplicated localized label produced⟩

/-! ## Two-sided mancude Rule-1a comparison -/

def p92ProductionRule1aMancudeObservation
    (mol : RawMolecule)
    (leftAttached rightAttached : Fin mol.atomCount)
    (leftLabel rightLabel : CIPAtomicLabel) : P92Rule1aMancudeAuthorityObservation where
  atomCount := mol.atomCount
  molecule := mol.toMoleculeGraph
  leftAttached := leftAttached
  rightAttached := rightAttached
  outcome := compareCIPAtomicLabel leftLabel rightLabel

theorem compareCIPAtomicLabel_eq_compare_exactValues
    (left right : CIPAtomicLabel) :
    compareCIPAtomicLabel left right =
      @compare ℚ Rat.linearOrder.toOrd
        left.toExactAtomicNumber.value right.toExactAtomicNumber.value := by
  rw [compareCIPAtomicLabel_eq_exactOutcomeValue]
  exact (LinearOrder.compare_eq_compareOfLessAndEq _ _).symm

theorem p92ProductionRule1aMancude_judged
    (source : AuthoritativeChemicalInput)
    (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (bondRecordsUnique : mol.BondRecordsUnique)
    (represents : P92ClassicalConstitutionRepresents source mol.toMoleculeGraph)
    (leftAttached leftDuplicated rightAttached rightDuplicated : Fin mol.atomCount)
    (leftLocalized :
      mol.toMoleculeGraph.LocalizedMancudeEdge leftAttached leftDuplicated)
    (rightLocalized :
      mol.toMoleculeGraph.LocalizedMancudeEdge rightAttached rightDuplicated)
    (leftRepresented : P92MancudeAttachmentRepresented mol.toMoleculeGraph leftAttached)
    (rightRepresented : P92MancudeAttachmentRepresented mol.toMoleculeGraph rightAttached)
    (leftLabel rightLabel : CIPAtomicLabel)
    (leftProduced :
      mol.mancudeRule1aLabel? leftAttached.val leftDuplicated.val = some leftLabel)
    (rightProduced :
      mol.mancudeRule1aLabel? rightAttached.val rightDuplicated.val = some rightLabel) :
    p92Rule1aMancudeReference.Judges source
      (p92ProductionRule1aMancudeObservation mol leftAttached rightAttached leftLabel
        rightLabel) := by
  have leftExact := certifiedMancudeRule1aLabel_exactAverageValue mol wellFormed
    bondRecordsUnique leftAttached leftDuplicated leftLocalized leftLabel leftProduced
  have rightExact := certifiedMancudeRule1aLabel_exactAverageValue mol wellFormed
    bondRecordsUnique rightAttached rightDuplicated rightLocalized rightLabel rightProduced
  refine ⟨represents, leftRepresented, rightRepresented, ?_⟩
  unfold ExactAtomicNumber.Outcome
  calc
    @compare ℚ Rat.linearOrder.toOrd
        (mol.toMoleculeGraph.exactMancudeAverage leftAttached).value
        (mol.toMoleculeGraph.exactMancudeAverage rightAttached).value =
        @compare ℚ Rat.linearOrder.toOrd
          leftLabel.toExactAtomicNumber.value rightLabel.toExactAtomicNumber.value := by
          rw [leftExact, rightExact]
    _ = compareCIPAtomicLabel leftLabel rightLabel :=
      (compareCIPAtomicLabel_eq_compare_exactValues leftLabel rightLabel).symm

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.certifiedMancudeRule1aLabel_exactAverageValue
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92ProductionMancudeDigraph_judged
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.compareCIPAtomicLabel_eq_compare_exactValues
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92ProductionRule1aMancude_judged
