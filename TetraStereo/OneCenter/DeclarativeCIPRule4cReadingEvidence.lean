import TetraStereo.OneCenter.DeclarativeCIPReadingKeyProjection
import TetraStereo.OneCenter.DeclarativeCIPMolecularEvidence
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! # Independent Rule-4c reading evidence and its ordinary-key projection

For one fixed uppercase reference, this evidence retains the molecular Rule-4a and Rule-4b
observations from `readingEvidence` and adds the molecule-derived Rule-4c pseudoasymmetric
observation. Rule 3 and Rule 5 are masked on the intended simple-bond endpoint. Its ordinary key
therefore orders children by constitution, then the complete Rule-4a, Rule-4b and Rule-4c
components. Lowercase `r` and `s` both remain visible in the Rule-4c component.
-/

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

universe u

noncomputable section
open scoped Classical
open Certificate.CanonicalSphereKey (Key)

section Projection

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)
  (evidence : StereochemicalEvidence graph)

local instance rule4cReadingProjectionNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- Extend the independent per-reference Rules-4a/4b evidence with molecular Rule 4c. -/
def readingEvidence4c (reference : DescriptorSense) : StereochemicalEvidence graph :=
  fun node =>
    { (readingEvidence molecule descriptorMap unit graph reference node) with
      rule4c := rule4cObservation molecule descriptorMap unit graph node
      rule5 := none }

/-- The evidence has exactly Rules 4a, 4b and 4c active. -/
def Rule4abcOnly (evidence : StereochemicalEvidence graph) : Prop :=
  ∀ rule, rule ≠ StereochemicalRule.rule4aStereogenicUnitKind →
    rule ≠ StereochemicalRule.rule4bLikeUnlikeDescriptorPairs →
    rule ≠ StereochemicalRule.rule4cPseudoasymmetricDescriptor →
      ∀ node, stereoLabel graph evidence rule node = ⊥

/-- Evidence for the genuine no-uppercase-reference alternative: only Rules 4a and 4c are active.
This does not rule out lowercase `r` or `s` descriptors. -/
def Rule4acOnly (evidence : StereochemicalEvidence graph) : Prop :=
  ∀ rule, rule ≠ StereochemicalRule.rule4aStereogenicUnitKind →
    rule ≠ StereochemicalRule.rule4cPseudoasymmetricDescriptor →
      ∀ node, stereoLabel graph evidence rule node = ⊥

/-- On a simple-bonded molecule, the per-reference evidence is Rule-4abc-only: Rule 3 follows
from the bond-order bound, and Rule 5 is explicitly masked. -/
theorem rule4abcOnly_readingEvidence4c_of_single
    (singleBonded : ∀ atom other, molecule.bond atom other ≤ 1)
    (reference : DescriptorSense) :
    Rule4abcOnly graph (readingEvidence4c molecule descriptorMap unit graph reference) := by
  intro rule h4a h4b h4c node
  cases rule with
  | rule3DoubleBondGeometry =>
      have hrule3 := molecularEvidence_rule3_eq_none molecule singleBonded
        descriptorMap unit graph node
      change rule3Observation molecule descriptorMap unit graph node = none at hrule3
      change stereoValue .rule3DoubleBondGeometry
        (some (readingEvidence4c molecule descriptorMap unit graph reference node)) = ⊥
      simp [stereoValue, readingEvidence4c, readingEvidence, hrule3, liftObservation]
  | rule4aStereogenicUnitKind => exact (h4a rfl).elim
  | rule4bLikeUnlikeDescriptorPairs => exact (h4b rfl).elim
  | rule4cPseudoasymmetricDescriptor => exact (h4c rfl).elim
  | rule5EnantiomorphicDescriptor =>
      change stereoValue .rule5EnantiomorphicDescriptor
        (some (readingEvidence4c molecule descriptorMap unit graph reference node)) = ⊥
      simp [stereoValue, readingEvidence4c, liftObservation]

/-- The independent Rule-4c component of an ordinary key. -/
def rule4cComponent (evidence : StereochemicalEvidence graph) (W D : ℕ) (node : graph.Node) :
    Key StereoLabel :=
  (ofLex (ordinaryKey molecule graph evidence W D node)).2.getD
      (stereoIndex .rule4cPseudoasymmetricDescriptor) []

/-- The comparison-visible four-component key: constitution, then whole Rule-4a, Rule-4b and
Rule-4c components. -/
def rule4abcKey (evidence : StereochemicalEvidence graph) (W D : ℕ) (node : graph.Node) :
    Lex (List (Key ℤ) × Lex (Key StereoLabel × Lex (Key StereoLabel × Key StereoLabel))) :=
  toLex (ruleKey molecule graph W D node,
    toLex (rule4aComponent molecule graph evidence W D node,
      toLex (rule4bComponent molecule graph evidence W D node,
        rule4cComponent molecule graph evidence W D node)))

/-- Rule 3 and Rule 5 components are determined by the constitutional key under Rule-4abc-only
evidence. -/
theorem shapeComponents_eq_rule4abc
    (h : Rule4abcOnly graph evidence) (W D : ℕ) {x y : graph.Node}
    (constitutionalEq : ruleKey molecule graph W D x = ruleKey molecule graph W D y) :
    (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD 0 [] =
        (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD 0 [] ∧
      (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD 4 [] =
        (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD 4 [] :=
  ⟨botComponent_eq_of_ruleKey_eq molecule graph evidence .rule3DoubleBondGeometry
      (h _ (by decide) (by decide) (by decide)) W D constitutionalEq,
    botComponent_eq_of_ruleKey_eq molecule graph evidence .rule5EnantiomorphicDescriptor
      (h _ (by decide) (by decide) (by decide)) W D constitutionalEq⟩

end Projection

section NoReference

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

local instance rule4cNoReferenceNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- The independent Rule-4c evidence for the empty-reference alternative.  Rule 4b comes from
`rankEvidence` and is therefore absent, while the molecular pseudoasymmetric observation remains
active. -/
def noReferenceEvidence4c : StereochemicalEvidence graph := fun node =>
  { (rankEvidence molecule descriptorMap unit graph node) with
    rule4c := rule4cObservation molecule descriptorMap unit graph node
    rule5 := none }

/-- The no-reference observation is Rule-4ac-only on a simple-bond input. -/
theorem rule4acOnly_noReferenceEvidence4c_of_single
    (singleBonded : ∀ atom other, molecule.bond atom other ≤ 1) :
    Rule4acOnly graph (noReferenceEvidence4c molecule descriptorMap unit graph) := by
  intro rule h4a h4c node
  cases rule with
  | rule3DoubleBondGeometry =>
      have hrule3 := molecularEvidence_rule3_eq_none molecule singleBonded
        descriptorMap unit graph node
      change rule3Observation molecule descriptorMap unit graph node = none at hrule3
      change stereoValue .rule3DoubleBondGeometry
        (some (noReferenceEvidence4c molecule descriptorMap unit graph node)) = ⊥
      simp [stereoValue, noReferenceEvidence4c, rankEvidence, hrule3, liftObservation]
  | rule4aStereogenicUnitKind => exact (h4a rfl).elim
  | rule4bLikeUnlikeDescriptorPairs =>
      change stereoValue .rule4bLikeUnlikeDescriptorPairs
        (some (noReferenceEvidence4c molecule descriptorMap unit graph node)) = ⊥
      simp [stereoValue, noReferenceEvidence4c, rankEvidence, liftObservation]
  | rule4cPseudoasymmetricDescriptor => exact (h4c rfl).elim
  | rule5EnantiomorphicDescriptor =>
      change stereoValue .rule5EnantiomorphicDescriptor
        (some (noReferenceEvidence4c molecule descriptorMap unit graph node)) = ⊥
      simp [stereoValue, noReferenceEvidence4c, rankEvidence, liftObservation]

end NoReference

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.rule4abcOnly_readingEvidence4c_of_single
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.shapeComponents_eq_rule4abc
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.rule4acOnly_noReferenceEvidence4c_of_single
