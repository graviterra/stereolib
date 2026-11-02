import TetraStereo.OneCenter.CIPAuthoritativeOccurrenceComparator
import TetraStereo.OneCenter.CIPBlueBookConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RawMolecule

/-!
# Conformance of the uncapped primitive path

The external claim that IUPAC P-92 is normative remains outside Lean.  This file proves that the
new size-unbounded primitive path uses (1) the complete finite maximum-matching computation for
localized mancude Rule 1a and (2) the same independently transcribed P-92 primitive decisions as
the already audited descriptor rules.
-/

/-- The authoritative general mancude label is exactly the fuel-free exhaustive
exclude/include maximum-matching calculation. -/
theorem generalMancudeRule1aLabelAuthoritative?_eq_exhaustive
    (mol : RawMolecule) (attached duplicated : ℕ) :
    mol.generalMancudeRule1aLabelAuthoritative? attached duplicated =
      let allEdges := mol.localizedMancudeEdges
      let vertices := edgeComponent allEdges (allEdges.length + 1) [attached] [attached]
      let edges := allEdges.filter fun edge => vertices.contains edge.1 && vertices.contains edge.2
      if !(vertices.contains duplicated) || edges.isEmpty then none
      else
        let stats := mol.exhaustiveMancudeMatchingStats attached edges
        let writtenDoubleCount :=
          (edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2).length
        if stats.size != writtenDoubleCount || stats.count == 0 then none
        else some { numerator := stats.partnerZSum, denominator := stats.count } := by
  simp [generalMancudeRule1aLabelAuthoritative?, mancudeMatchingStats_length_succ]

/-- Authoritative Rule 1a compares exactly the rational values carried by its two independently
observable labels. -/
theorem authoritative_rule1a_conforms_independent_exact
    (mol : RawMolecule) (left right : CanonicalBranchNode)
    (leftLabel rightLabel : CIPAtomicLabel)
    (leftObserved : mol.canonicalRule1aLabelAuthoritative? left = some leftLabel)
    (rightObserved : mol.canonicalRule1aLabelAuthoritative? right = some rightLabel)
    (outcome : Ordering) :
    mol.compareCanonicalNodeRuleAuthoritative? CanonicalRuleStage.rule1a left right =
        some outcome ↔
      DeclarativeCIP.ExactAtomicNumber.Outcome leftLabel.toExactAtomicNumber
        rightLabel.toExactAtomicNumber outcome := by
  simp [compareCanonicalNodeRuleAuthoritative?, leftObserved, rightObserved,
    DeclarativeCIP.ExactAtomicNumber.Outcome,
    compareCIPAtomicLabel_eq_exactOutcomeValue]
  rw [LinearOrder.compare_eq_compareOfLessAndEq]

/-- Primitive conformance certificate for the authoritative node path.  Descriptor Rules 3--5
reuse the independently audited implementation; Rules 1b and 2 are unchanged; Rule 1a is stated
against exact rational observations emitted by the uncapped labeler. -/
structure AuthoritativePrimitiveP92Conformance : Prop where
  descriptors : PrimitiveDescriptorConformance
  rule1a : ∀ (mol : RawMolecule) (left right : CanonicalBranchNode)
      (leftLabel rightLabel : CIPAtomicLabel) (outcome : Ordering),
    mol.canonicalRule1aLabelAuthoritative? left = some leftLabel →
    mol.canonicalRule1aLabelAuthoritative? right = some rightLabel →
    (mol.compareCanonicalNodeRuleAuthoritative? CanonicalRuleStage.rule1a left right =
        some outcome ↔
      DeclarativeCIP.ExactAtomicNumber.Outcome leftLabel.toExactAtomicNumber
        rightLabel.toExactAtomicNumber outcome)
  rule1b : ∀ (mol : RawMolecule) (left right : CanonicalBranchNode),
    mol.compareCanonicalNodeRule CanonicalRuleStage.rule1b left right =
      BlueBookP92.rule1bDecision left.rule1bCode right.rule1bCode
  rule2Real : ∀ (mol : RawMolecule) (left right : CanonicalBranchNode),
    left.provenance = .realAtom → right.provenance = .realAtom →
    mol.compareCanonicalNodeRule CanonicalRuleStage.rule2 left right =
      BlueBookP92.rule2Decision (mol.atomMassAt left.atom) (mol.atomMassAt right.atom)
  exhaustiveMancude : ∀ (mol : RawMolecule) (attached duplicated : ℕ),
    mol.generalMancudeRule1aLabelAuthoritative? attached duplicated =
      let allEdges := mol.localizedMancudeEdges
      let vertices := edgeComponent allEdges (allEdges.length + 1) [attached] [attached]
      let edges := allEdges.filter fun edge => vertices.contains edge.1 && vertices.contains edge.2
      if !(vertices.contains duplicated) || edges.isEmpty then none
      else
        let stats := mol.exhaustiveMancudeMatchingStats attached edges
        let writtenDoubleCount :=
          (edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2).length
        if stats.size != writtenDoubleCount || stats.count == 0 then none
        else some { numerator := stats.partnerZSum, denominator := stats.count }

/-- Checked package for every primitive on the authoritative path. -/
theorem authoritativePrimitiveRules_conform_blueBookP92 :
    AuthoritativePrimitiveP92Conformance where
  descriptors := primitiveDescriptorRules_conform_blueBookP92
  rule1a := by
    intro mol left right leftLabel rightLabel outcome leftObserved rightObserved
    exact authoritative_rule1a_conforms_independent_exact mol left right leftLabel rightLabel
      leftObserved rightObserved outcome
  rule1b := production_rule1b_conforms_blueBookP92
  rule2Real := by
    intro mol left right leftReal rightReal
    exact production_rule2_real_atoms_conforms_blueBookP92 mol left right leftReal rightReal
  exhaustiveMancude := generalMancudeRule1aLabelAuthoritative?_eq_exhaustive

end TetraStereo.OneCenter
