import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule

/-- `atomZAt` at a materialized atom is the actual source atomic number, not the `0` fallback. -/
theorem atomZAt_eq_of_atomAt? (mol : RawMolecule) (index : ℕ) (spec : AtomSpec)
    (observed : mol.atomAt? index = some spec) :
    mol.atomZAt index = spec.element.atomicNumber := by
  simp [RawMolecule.atomZAt, observed]

/-- A `realAtom` node has the exact integral atomic-number Rule-1a label. -/
theorem canonicalRule1aLabel?_realAtom (mol : RawMolecule)
    (node : RawMolecule.CanonicalBranchNode)
    (h : node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom) :
    mol.canonicalRule1aLabel? node =
      some { numerator := mol.atomZAt node.atom, denominator := 1 } := by
  cases hp : node.provenance with
  | realAtom => simp [RawMolecule.canonicalRule1aLabel?, hp]
  | multipleBondDuplicate distance => simp_all
  | ringDuplicate distance => simp_all
  | phantom distance => simp_all

/-- The exact rational label comparator on two integral labels is the plain atomic-number
comparison. -/
theorem compareCIPAtomicLabel_unitValue (a b : ℕ) :
    RawMolecule.compareCIPAtomicLabel { numerator := a, denominator := 1 }
      { numerator := b, denominator := 1 } = compare a b := by
  simp [RawMolecule.compareCIPAtomicLabel, RawMolecule.CIPAtomicLabel.effectiveDenominator]

/-- Strict real-root atomic-label comparison for the raw production node comparator. -/
theorem compareCanonicalNodeRule?_rule1a_realAtom (mol : RawMolecule)
    (left right : RawMolecule.CanonicalBranchNode)
    (hL : left.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hR : right.provenance = RawMolecule.CanonicalNodeProvenance.realAtom) :
    mol.compareCanonicalNodeRule? RawMolecule.CanonicalRuleStage.rule1a left right =
      some (compare (mol.atomZAt left.atom) (mol.atomZAt right.atom)) := by
  have hLabelL := canonicalRule1aLabel?_realAtom mol left hL
  have hLabelR := canonicalRule1aLabel?_realAtom mol right hR
  have hNode : mol.compareCanonicalNodeRule? RawMolecule.CanonicalRuleStage.rule1a left right =
      some (RawMolecule.compareCIPAtomicLabel
        { numerator := mol.atomZAt left.atom, denominator := 1 }
        { numerator := mol.atomZAt right.atom, denominator := 1 }) := by
    simp [RawMolecule.compareCanonicalNodeRule?, hLabelL, hLabelR]
  simp [hNode, compareCIPAtomicLabel_unitValue]

/-- A strict Rule-1a node decision short-circuits `compareCanonicalNodeThrough?` for every stage. -/
theorem compareCanonicalNodeThrough?_eq_of_rule1a (mol : RawMolecule)
    (stage : RawMolecule.CanonicalRuleStage)
    (left right : RawMolecule.CanonicalBranchNode) (decision : Ordering)
    (computed : mol.compareCanonicalNodeRule? RawMolecule.CanonicalRuleStage.rule1a left right =
      some decision)
    (strict : decision ≠ Ordering.eq) :
    mol.compareCanonicalNodeThrough? stage left right = some decision := by
  cases hdec : decision with
  | lt => simp [RawMolecule.compareCanonicalNodeThrough?, computed, hdec]
  | gt => simp [RawMolecule.compareCanonicalNodeThrough?, computed, hdec]
  | eq => exact absurd hdec strict

end TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery
