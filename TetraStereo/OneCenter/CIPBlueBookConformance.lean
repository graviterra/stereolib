import TetraStereo.OneCenter.ProductionCIPRule1aSoundness
import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent Blue Book conformance boundary

This file does not define the executable CIP engine.  It transcribes the primitive priority
judgments in IUPAC Blue Book P-92 into a small, declarative reference semantics and then proves
that the corresponding executable primitives agree with it.

The external assertion that P-92 is the chemically authoritative source is necessarily a
trust-boundary statement, not a theorem of Lean.  What Lean proves here is conditional and exact:
given this transcription of P-92, the named implementation functions have the same outcomes.
-/

namespace BlueBookP92

/-- Independent names for the P-92 rule/subrule slots. -/
inductive SequenceRule where
  | rule1a
  | rule1b
  | rule2
  | rule3
  | rule4a
  | rule4b
  | rule4c
  | rule5
  deriving DecidableEq, Repr

/-- P-92.1.3 evaluation order, using only the independent reference vocabulary. -/
def ruleOrder : List SequenceRule :=
  [ .rule1a, .rule1b, .rule2, .rule3, .rule4a, .rule4b, .rule4c, .rule5 ]

/-- Explicit syntax translation; it is not used to define either rule order. -/
def ofOfficialRule : OfficialCIPSequenceRule → SequenceRule
  | .rule1aAtomicNumber => .rule1a
  | .rule1bDuplicateNodeProximity => .rule1b
  | .rule2AtomicMass => .rule2
  | .rule3DoubleBondGeometry => .rule3
  | .rule4aStereogenicUnitKind => .rule4a
  | .rule4bLikeUnlikeDescriptorPairs => .rule4b
  | .rule4cPseudoasymmetricDescriptor => .rule4c
  | .rule5EnantiomorphicDescriptor => .rule5

/-- Generic higher-number-has-priority decision used by Rules 1a and 2 and by finite encodings of
the descriptor rules. -/
def higherNatDecision (left right : Nat) : Ordering :=
  if left < right then Ordering.lt
  else if right < left then Ordering.gt
  else Ordering.eq

/-- P-92.1.3.1(a): higher atomic number precedes lower. -/
def rule1aDecision (leftAtomicNumber rightAtomicNumber : Nat) : Ordering :=
  higherNatDecision leftAtomicNumber rightAtomicNumber

/-- P-92.1.3.1(b): the duplicate whose corresponding atom is closer to the root precedes the
duplicate whose corresponding atom is farther from the root. -/
def rule1bDecision (leftRootDistance rightRootDistance : Nat) : Ordering :=
  higherNatDecision rightRootDistance leftRootDistance

/-- P-92.1.3.2: higher atomic mass number precedes lower. -/
def rule2Decision (leftMassNumber rightMassNumber : Nat) : Ordering :=
  higherNatDecision leftMassNumber rightMassNumber

/-- Independent Rule-3 domain. -/
inductive Rule3Class where
  | seqCis
  | seqTrans
  | nonstereogenic
  deriving DecidableEq, Repr

def rule3ClassOfOfficial : OfficialRule3Geometry → Rule3Class
  | .seqcis => .seqCis
  | .seqtrans => .seqTrans
  | .nonstereogenic => .nonstereogenic

/-- P-92.1.3.3 priority encoding: seqCis > seqTrans > nonstereogenic. -/
def rule3Priority : Rule3Class → Nat
  | .seqCis => 2
  | .seqTrans => 1
  | .nonstereogenic => 0

def rule3Decision (left right : Rule3Class) : Ordering :=
  higherNatDecision (rule3Priority left) (rule3Priority right)

/-- Independent Rule-4a domain. -/
inductive Rule4aClass where
  | chiral
  | pseudoasymmetric
  | nonstereogenic
  deriving DecidableEq, Repr

def rule4aClassOfOfficial : OfficialStereogenicUnitKind → Rule4aClass
  | .chiral => .chiral
  | .pseudoasymmetric => .pseudoasymmetric
  | .nonstereogenic => .nonstereogenic

/-- P-92.1.3.4(a): chiral > pseudoasymmetric > nonstereogenic. -/
def rule4aPriority : Rule4aClass → Nat
  | .chiral => 2
  | .pseudoasymmetric => 1
  | .nonstereogenic => 0

def rule4aDecision (left right : Rule4aClass) : Ordering :=
  higherNatDecision (rule4aPriority left) (rule4aPriority right)

/-- Independent Rule-4b reference-count domain. -/
inductive Rule4bReferenceCount where
  | one
  | two
  deriving DecidableEq, Repr

def rule4bReferenceCountOfOfficial :
    OfficialRule4bReferenceCount → Rule4bReferenceCount
  | .one => .one
  | .two => .two

/-- P-92.5.2.1 criterion (c)(i): one reference descriptor precedes two. -/
def rule4bReferenceCountPriority : Rule4bReferenceCount → Nat
  | .one => 1
  | .two => 0

def rule4bReferenceCountDecision
    (left right : Rule4bReferenceCount) : Ordering :=
  higherNatDecision (rule4bReferenceCountPriority left) (rule4bReferenceCountPriority right)

/-- Independent Rule-4b pair domain. -/
inductive Rule4bPairClass where
  | like
  | unlike
  deriving DecidableEq, Repr

def rule4bPairClassOfOfficial : OfficialDescriptorPairKind → Rule4bPairClass
  | .like => .like
  | .unlike => .unlike

/-- P-92.1.3.4(b): a like descriptor pair precedes a corresponding unlike pair. -/
def rule4bPairPriority : Rule4bPairClass → Nat
  | .like => 1
  | .unlike => 0

def rule4bPairDecision (left right : Rule4bPairClass) : Ordering :=
  higherNatDecision (rule4bPairPriority left) (rule4bPairPriority right)

/-- Independent Rule-4c symbol domain. -/
inductive Rule4cSymbol where
  | r
  | s
  | m
  | p
  deriving DecidableEq, Repr

def rule4cSymbolOfOfficial : OfficialPseudoasymmetricDescriptor → Rule4cSymbol
  | .r => .r
  | .s => .s
  | .m => .m
  | .p => .p

def rule4cFamily : Rule4cSymbol → Nat
  | .r | .s => 0
  | .m | .p => 1

def rule4cPriority : Rule4cSymbol → Nat
  | .r | .m => 1
  | .s | .p => 0

/-- P-92.1.3.4(c): r > s and m > p.  Cross-family comparisons are outside this primitive. -/
def rule4cDecision? (left right : Rule4cSymbol) : Option Ordering :=
  if rule4cFamily left = rule4cFamily right then
    some (higherNatDecision (rule4cPriority left) (rule4cPriority right))
  else
    none

/-- Independent Rule-5 family and sense domains. -/
inductive Rule5Family where
  | tetrahedralCenter
  | axisOrPlane
  | doubleBondOrCumulene
  deriving DecidableEq, Repr

inductive Rule5Sense where
  | senior
  | junior
  deriving DecidableEq, Repr

structure Rule5Descriptor where
  family : Rule5Family
  auxiliary : Bool
  sense : Rule5Sense
  deriving DecidableEq, Repr

def rule5FamilyOfOfficial : OfficialRule5DescriptorKind → Rule5Family
  | .tetrahedralCenter => .tetrahedralCenter
  | .axisOrPlane => .axisOrPlane
  | .doubleBondOrCumulene => .doubleBondOrCumulene

def rule5SenseOfOfficial : OfficialDescriptorSense → Rule5Sense
  | .senior => .senior
  | .junior => .junior

def rule5DescriptorOfOfficial (descriptor : OfficialRule5Descriptor) : Rule5Descriptor :=
  { family := rule5FamilyOfOfficial descriptor.kind
    auxiliary := descriptor.auxiliary
    sense := rule5SenseOfOfficial descriptor.sense }

def rule5SensePriority : Rule5Sense → Nat
  | .senior => 1
  | .junior => 0

/-- P-92.1.3.5 inside one descriptor family and auxiliary level:
R/M/seqCis > S/P/seqTrans. -/
def rule5Decision? (left right : Rule5Descriptor) : Option Ordering :=
  if left.family = right.family then
    if left.auxiliary = right.auxiliary then
      some (higherNatDecision (rule5SensePriority left.sense) (rule5SensePriority right.sense))
    else
      none
  else
    none

end BlueBookP92

/-! ## Primitive equivalence proofs -/

@[simp] theorem official_rule_order_conforms_blueBookP92 :
    OfficialCIPSequenceRule.all.map BlueBookP92.ofOfficialRule = BlueBookP92.ruleOrder :=
  rfl

theorem official_rule3_conforms_blueBookP92 (left right : OfficialRule3Geometry) :
    OfficialRule3Geometry.compare left right =
      BlueBookP92.rule3Decision (BlueBookP92.rule3ClassOfOfficial left)
        (BlueBookP92.rule3ClassOfOfficial right) := by
  cases left <;> cases right <;> rfl

theorem official_rule4a_conforms_blueBookP92
    (left right : OfficialStereogenicUnitKind) :
    OfficialStereogenicUnitKind.compare left right =
      BlueBookP92.rule4aDecision (BlueBookP92.rule4aClassOfOfficial left)
        (BlueBookP92.rule4aClassOfOfficial right) := by
  cases left <;> cases right <;> rfl

theorem official_rule4b_reference_count_conforms_blueBookP92
    (left right : OfficialRule4bReferenceCount) :
    OfficialRule4bReferenceCount.compare left right =
      BlueBookP92.rule4bReferenceCountDecision
        (BlueBookP92.rule4bReferenceCountOfOfficial left)
        (BlueBookP92.rule4bReferenceCountOfOfficial right) := by
  cases left <;> cases right <;> rfl

theorem official_rule4b_pair_conforms_blueBookP92
    (left right : OfficialDescriptorPairKind) :
    OfficialDescriptorPairKind.compare left right =
      BlueBookP92.rule4bPairDecision (BlueBookP92.rule4bPairClassOfOfficial left)
        (BlueBookP92.rule4bPairClassOfOfficial right) := by
  cases left <;> cases right <;> rfl

theorem official_rule4c_conforms_blueBookP92
    (left right : OfficialPseudoasymmetricDescriptor) :
    OfficialPseudoasymmetricDescriptor.compare? left right =
      BlueBookP92.rule4cDecision? (BlueBookP92.rule4cSymbolOfOfficial left)
        (BlueBookP92.rule4cSymbolOfOfficial right) := by
  cases left <;> cases right <;> rfl

theorem official_rule5_conforms_blueBookP92
    (left right : OfficialRule5Descriptor) :
    OfficialRule5Descriptor.compare? left right =
      BlueBookP92.rule5Decision? (BlueBookP92.rule5DescriptorOfOfficial left)
        (BlueBookP92.rule5DescriptorOfOfficial right) := by
  cases left with
  | mk leftKind leftAux leftSense =>
      cases right with
      | mk rightKind rightAux rightSense =>
          cases leftKind <;> cases rightKind <;> cases leftAux <;> cases rightAux <;>
            cases leftSense <;> cases rightSense <;> rfl



theorem production_rule1a_conforms_independent_exact
    (mol : RawMolecule) (left right : RawMolecule.CanonicalBranchNode)
    (leftLabel rightLabel : RawMolecule.CIPAtomicLabel)
    (leftObserved : mol.canonicalRule1aLabel? left = some leftLabel)
    (rightObserved : mol.canonicalRule1aLabel? right = some rightLabel)
    (outcome : Ordering) :
    mol.compareCanonicalNodeRule? RawMolecule.CanonicalRuleStage.rule1a left right =
        some outcome ↔
      DeclarativeCIP.ExactAtomicNumber.Outcome leftLabel.toExactAtomicNumber
        rightLabel.toExactAtomicNumber outcome :=
  mol.compareCanonicalNodeRule?_rule1a_exactOutcome_iff left right leftLabel rightLabel
    leftObserved rightObserved outcome

/-- The executable Rule-1b node comparator agrees with the independent P-92 closer-to-root
decision on its compiled root-distance observations. -/
theorem production_rule1b_conforms_blueBookP92 (mol : RawMolecule)
    (left right : RawMolecule.CanonicalBranchNode) :
    mol.compareCanonicalNodeRule RawMolecule.CanonicalRuleStage.rule1b left right =
      BlueBookP92.rule1bDecision left.rule1bCode right.rule1bCode := by
  change
    (if left.rule1bRootDistance < right.rule1bRootDistance then Ordering.gt
      else if right.rule1bRootDistance < left.rule1bRootDistance then Ordering.lt
      else Ordering.eq) =
    (if right.rule1bRootDistance < left.rule1bRootDistance then Ordering.lt
      else if left.rule1bRootDistance < right.rule1bRootDistance then Ordering.gt
      else Ordering.eq)
  rcases lt_trichotomy left.rule1bRootDistance right.rule1bRootDistance with
    leftCloser | sameDistance | rightCloser
  · have notRightCloser : ¬right.rule1bRootDistance < left.rule1bRootDistance :=
      Nat.not_lt_of_ge leftCloser.le
    simp [leftCloser, notRightCloser]
  · simp [sameDistance]
  · have notLeftCloser : ¬left.rule1bRootDistance < right.rule1bRootDistance :=
      Nat.not_lt_of_ge rightCloser.le
    simp [rightCloser, notLeftCloser]

theorem compareNat_conforms_blueBookP92_higher (left right : Nat) :
    compare left right = BlueBookP92.higherNatDecision left right := by
  rcases lt_trichotomy left right with leftLower | same | leftHigher
  · simp [BlueBookP92.higherNatDecision, leftLower,
      Nat.compare_eq_lt.mpr leftLower]
  · subst right
    simp [BlueBookP92.higherNatDecision]
  · have notLower : ¬left < right := Nat.not_lt_of_ge leftHigher.le
    simp [BlueBookP92.higherNatDecision, leftHigher, notLower,
      Nat.compare_eq_gt.mpr leftHigher]




theorem production_rule2_real_atoms_conforms_blueBookP92 (mol : RawMolecule)
    (left right : RawMolecule.CanonicalBranchNode)
    (leftReal : left.provenance = .realAtom) (rightReal : right.provenance = .realAtom) :
    mol.compareCanonicalNodeRule RawMolecule.CanonicalRuleStage.rule2 left right =
      BlueBookP92.rule2Decision (mol.atomMassAt left.atom) (mol.atomMassAt right.atom) := by
  simp [RawMolecule.compareCanonicalNodeRule, leftReal, rightReal,
    BlueBookP92.rule2Decision, compareNat_conforms_blueBookP92_higher]

/-! ## Production Rule-4b bridge -/

/-- Occurrence-local production implements the P-92.5.2.1 one-reference-over-two clause. -/
theorem compareOccurrenceRule4b?_one_reference_over_two
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) (leftReference rightFirst rightSecond : RS)
    (leftReferences : occurrenceRule4bReferences mol state fuel [left] = [leftReference])
    (rightReferences :
      occurrenceRule4bReferences mol state fuel [right] = [rightFirst, rightSecond]) :
    compareOccurrenceRule4b? mol state fuel left right =
      some (BlueBookP92.rule4bReferenceCountDecision .one .two) := by
  simp [compareOccurrenceRule4b?, leftReferences, rightReferences,
    BlueBookP92.rule4bReferenceCountDecision, BlueBookP92.rule4bReferenceCountPriority,
    BlueBookP92.higherNatDecision]

/-- The converse orientation of the same P-92.5.2.1 clause. -/
theorem compareOccurrenceRule4b?_two_references_below_one
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) (leftFirst leftSecond rightReference : RS)
    (leftReferences :
      occurrenceRule4bReferences mol state fuel [left] = [leftFirst, leftSecond])
    (rightReferences : occurrenceRule4bReferences mol state fuel [right] = [rightReference]) :
    compareOccurrenceRule4b? mol state fuel left right =
      some (BlueBookP92.rule4bReferenceCountDecision .two .one) := by
  simp [compareOccurrenceRule4b?, leftReferences, rightReferences,
    BlueBookP92.rule4bReferenceCountDecision, BlueBookP92.rule4bReferenceCountPriority,
    BlueBookP92.higherNatDecision]

/-- The older atom-indexed recursive path implements the same normative clause. -/
theorem compareRule4bRecursive?_one_reference_over_two
    (mol : RawMolecule) (state : RawDescriptorState) (center left right : Nat)
    (leftReference rightFirst rightSecond : RS)
    (leftReferences :
      branchRule4bOccurrenceReferences mol state center left = [leftReference])
    (rightReferences :
      branchRule4bOccurrenceReferences mol state center right = [rightFirst, rightSecond]) :
    compareRule4bRecursive? mol state center left right =
      some (BlueBookP92.rule4bReferenceCountDecision .one .two) := by
  simp [compareRule4bRecursive?, leftReferences, rightReferences,
    BlueBookP92.rule4bReferenceCountDecision, BlueBookP92.rule4bReferenceCountPriority,
    BlueBookP92.higherNatDecision]

/-- Checked summary of the primitive descriptor-rule conformance results.  This deliberately does
not claim completeness of molecule-to-digraph construction or stereogenic-unit perception. -/
structure PrimitiveDescriptorConformance : Prop where
  ruleOrder :
    OfficialCIPSequenceRule.all.map BlueBookP92.ofOfficialRule = BlueBookP92.ruleOrder
  rule3 : ∀ left right,
    OfficialRule3Geometry.compare left right =
      BlueBookP92.rule3Decision (BlueBookP92.rule3ClassOfOfficial left)
        (BlueBookP92.rule3ClassOfOfficial right)
  rule4a : ∀ left right,
    OfficialStereogenicUnitKind.compare left right =
      BlueBookP92.rule4aDecision (BlueBookP92.rule4aClassOfOfficial left)
        (BlueBookP92.rule4aClassOfOfficial right)
  rule4bReferenceCount : ∀ left right,
    OfficialRule4bReferenceCount.compare left right =
      BlueBookP92.rule4bReferenceCountDecision
        (BlueBookP92.rule4bReferenceCountOfOfficial left)
        (BlueBookP92.rule4bReferenceCountOfOfficial right)
  rule4bPair : ∀ left right,
    OfficialDescriptorPairKind.compare left right =
      BlueBookP92.rule4bPairDecision (BlueBookP92.rule4bPairClassOfOfficial left)
        (BlueBookP92.rule4bPairClassOfOfficial right)
  rule4c : ∀ left right,
    OfficialPseudoasymmetricDescriptor.compare? left right =
      BlueBookP92.rule4cDecision? (BlueBookP92.rule4cSymbolOfOfficial left)
        (BlueBookP92.rule4cSymbolOfOfficial right)
  rule5 : ∀ left right,
    OfficialRule5Descriptor.compare? left right =
      BlueBookP92.rule5Decision? (BlueBookP92.rule5DescriptorOfOfficial left)
        (BlueBookP92.rule5DescriptorOfOfficial right)

theorem primitiveDescriptorRules_conform_blueBookP92 : PrimitiveDescriptorConformance where
  ruleOrder := official_rule_order_conforms_blueBookP92
  rule3 := official_rule3_conforms_blueBookP92
  rule4a := official_rule4a_conforms_blueBookP92
  rule4bReferenceCount := official_rule4b_reference_count_conforms_blueBookP92
  rule4bPair := official_rule4b_pair_conforms_blueBookP92
  rule4c := official_rule4c_conforms_blueBookP92
  rule5 := official_rule5_conforms_blueBookP92

/-- Single checked certificate for every primitive P-92 layer currently connected to production.

Rule 1a is stated against the independent exact-rational semantics because supported
Mancude/Kekule duplicate labels need not be integral. Rule 2 is intentionally restricted to
physical atom nodes; duplicate-node isotope propagation belongs to the still-open full-digraph
refinement theorem. -/
structure PrimitiveP92Conformance : Prop where
  descriptors : PrimitiveDescriptorConformance
  rule1a : ∀ (mol : RawMolecule) (left right : RawMolecule.CanonicalBranchNode)
      (leftLabel rightLabel : RawMolecule.CIPAtomicLabel) (outcome : Ordering),
    mol.canonicalRule1aLabel? left = some leftLabel →
    mol.canonicalRule1aLabel? right = some rightLabel →
    (mol.compareCanonicalNodeRule? RawMolecule.CanonicalRuleStage.rule1a left right =
        some outcome ↔
      DeclarativeCIP.ExactAtomicNumber.Outcome leftLabel.toExactAtomicNumber
        rightLabel.toExactAtomicNumber outcome)
  rule1b : ∀ (mol : RawMolecule) (left right : RawMolecule.CanonicalBranchNode),
    mol.compareCanonicalNodeRule RawMolecule.CanonicalRuleStage.rule1b left right =
      BlueBookP92.rule1bDecision left.rule1bCode right.rule1bCode
  rule2Real : ∀ (mol : RawMolecule) (left right : RawMolecule.CanonicalBranchNode),
    left.provenance = .realAtom → right.provenance = .realAtom →
    mol.compareCanonicalNodeRule RawMolecule.CanonicalRuleStage.rule2 left right =
      BlueBookP92.rule2Decision (mol.atomMassAt left.atom) (mol.atomMassAt right.atom)

theorem primitiveRules_conform_blueBookP92 : PrimitiveP92Conformance where
  descriptors := primitiveDescriptorRules_conform_blueBookP92
  rule1a := by
    intro mol left right leftLabel rightLabel outcome leftObserved rightObserved
    exact production_rule1a_conforms_independent_exact mol left right leftLabel rightLabel
      leftObserved rightObserved outcome
  rule1b := production_rule1b_conforms_blueBookP92
  rule2Real := by
    intro mol left right leftReal rightReal
    exact production_rule2_real_atoms_conforms_blueBookP92 mol left right leftReal rightReal

end TetraStereo.OneCenter
