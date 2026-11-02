import TetraStereo.OneCenter.CIPAuthoritativeRule1aZeroFillConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open DeclarativeCIP

namespace RawMolecule

/-!
# Complete per-node constitutional refinement for authoritative branches

This file packages the three constitutional sequence-rule bridges at the same pair of realized
positions in two successful complete authoritative branch hierarchies.  Rule 1a uses the
independent exact-rational mancude semantics, Rule 1b the independent total root-distance
semantics, and Rule 2 the independent real-atom/zero-duplicate mass semantics.
-/

/-- Exact independent constitutional meaning of all three authoritative node comparisons at one
shared hierarchy position. -/
structure AuthoritativeConstitutionalNodeConformance
    (mol : RawMolecule) (center leftLigand rightLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (position : List ℕ)
    (leftNode : leftKey.HierarchyNode) (rightNode : rightKey.HierarchyNode)
    (leftSource rightSource : CanonicalBranchNode) : Prop where
  rule1a : ∀ outcome,
    mol.compareCanonicalNodeRuleAuthoritative? .rule1a leftSource rightSource = some outcome ↔
      ExactRule1aOutcomeAt mol.toMoleculeGraph
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
        position outcome
  rule1b : ∀ outcome,
    mol.compareCanonicalNodeRuleAuthoritative? .rule1b leftSource rightSource = some outcome ↔
      ConstitutionalNodeOutcome (mol.canonicalHierarchyMoleculeGraph center leftLigand)
        .rule1bDuplicateNodeProximity position
        (some ((leftKey.toDeclarativeDigraph mol).label leftNode))
        (some ((rightKey.toDeclarativeDigraph mol).label rightNode)) outcome
  rule2 : ∀ outcome,
    mol.compareCanonicalNodeRuleAuthoritative? .rule2 leftSource rightSource = some outcome ↔
      ConstitutionalNodeOutcome (mol.canonicalHierarchyMoleculeGraph center leftLigand)
        .rule2AtomicMass position
        (some ((leftKey.toDeclarativeDigraph mol).label leftNode))
        (some ((rightKey.toDeclarativeDigraph mol).label rightNode)) outcome

/-- Independent first-strict decision for the constitutional rule prefix.  Rule 1a decides when
strict; otherwise Rule 1b decides when strict; otherwise Rule 2 supplies the result, including
equality when all three constitutional observations tie. -/
def constitutionalFirstStrictDecision
    (rule1a rule1b rule2 : Ordering) : Ordering :=
  match rule1a with
  | .lt => .lt
  | .gt => .gt
  | .eq =>
      match rule1b with
      | .lt => .lt
      | .gt => .gt
      | .eq => rule2

/-- Fully declarative meaning of a first-strict Rule-1a/Rule-1b/Rule-2 comparison at one shared
hierarchy position.  The three component outcomes are witnesses of the independent exact Rule-1a,
root-distance Rule-1b, and mass Rule-2 relations; no executable comparison occurs in this
definition. -/
def ExactConstitutionalFirstStrictOutcomeAt
    (mol : RawMolecule) (center leftLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (position : List ℕ)
    (leftNode : leftKey.HierarchyNode) (rightNode : rightKey.HierarchyNode)
    (outcome : Ordering) : Prop :=
  ∃ rule1a rule1b rule2,
    ExactRule1aOutcomeAt mol.toMoleculeGraph
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
        position rule1a ∧
      ConstitutionalNodeOutcome (mol.canonicalHierarchyMoleculeGraph center leftLigand)
        .rule1bDuplicateNodeProximity position
        (some ((leftKey.toDeclarativeDigraph mol).label leftNode))
        (some ((rightKey.toDeclarativeDigraph mol).label rightNode)) rule1b ∧
      ConstitutionalNodeOutcome (mol.canonicalHierarchyMoleculeGraph center leftLigand)
        .rule2AtomicMass position
        (some ((leftKey.toDeclarativeDigraph mol).label leftNode))
        (some ((rightKey.toDeclarativeDigraph mol).label rightNode)) rule2 ∧
      constitutionalFirstStrictDecision rule1a rule1b rule2 = outcome

/-- Independent whole-hierarchy constitutional judgment.  Each rule is exhausted over every
semantic address in sphere-major, parent-slot order before the next rule is consulted. -/
def ExactConstitutionalHierarchyFirstStrictOutcome
    {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (outcome : Ordering) : Prop :=
  ∃ rule1a rule1b rule2,
    ExactRule1aHierarchyOutcome molecule left leftAddressing
        right rightAddressing rule1a ∧
      ConstitutionalHierarchyOutcome molecule .rule1bDuplicateNodeProximity
        left leftAddressing right rightAddressing rule1b ∧
      ConstitutionalHierarchyOutcome molecule .rule2AtomicMass
        left leftAddressing right rightAddressing rule2 ∧
      constitutionalFirstStrictDecision rule1a rule1b rule2 = outcome

/-- Read a source-node observation at a semantic address, using the supplied default only outside
the represented branch support. -/
def canonicalSourceObservationAt {α : Type*} [Inhabited α]
    (key : CanonicalBranchKey) (observe : CanonicalBranchNode → α)
    (position : List ℕ) : α :=
  (key.sourceNodeAtAddress? position).map observe |>.getD default

private theorem compareRule1bRootDistance_eq_nodeRule
    (mol : RawMolecule) (left right : CanonicalBranchNode) :
    compareRule1bRootDistance left.rule1bCode right.rule1bCode =
      mol.compareCanonicalNodeRule .rule1b left right := by
  unfold CanonicalBranchNode.rule1bCode
  rcases lt_trichotomy left.rule1bRootDistance right.rule1bRootDistance with
      less | equal | greater
  · simp [compareRule1bRootDistance, flip, compareCanonicalNodeRule,
      less, Nat.compare_eq_gt.mpr less]
  · simp [compareRule1bRootDistance, flip, compareCanonicalNodeRule, equal]
  · simp [compareRule1bRootDistance, flip, compareCanonicalNodeRule,
      greater, Nat.compare_eq_lt.mpr greater]
    exact greater.le

private theorem constitutionalOutcomeAt_iff_of_nodes
    {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (rule : ConstitutionalRule)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    (position : List ℕ) (leftNode : left.Node) (rightNode : right.Node)
    (leftPosition : leftAddressing.address leftNode = position)
    (rightPosition : rightAddressing.address rightNode = position)
    (outcome : Ordering) :
    ConstitutionalOutcomeAt molecule rule left leftAddressing right rightAddressing
        position outcome ↔
      ConstitutionalNodeOutcome molecule rule position
        (some (left.label leftNode)) (some (right.label rightNode)) outcome := by
  have leftAt : RootedDigraph.Addressing.LabelAt left leftAddressing position
      (some (left.label leftNode)) :=
    Or.inl ⟨leftNode, leftPosition, rfl⟩
  have rightAt : RootedDigraph.Addressing.LabelAt right rightAddressing position
      (some (right.label rightNode)) :=
    Or.inl ⟨rightNode, rightPosition, rfl⟩
  constructor
  · rintro ⟨leftLabel, rightLabel, observedLeft, observedRight, observed⟩
    have leftEq := RootedDigraph.Addressing.labelAt_functional
      left leftAddressing position observedLeft leftAt
    have rightEq := RootedDigraph.Addressing.labelAt_functional
      right rightAddressing position observedRight rightAt
    subst leftLabel
    subst rightLabel
    exact observed
  · intro observed
    exact ⟨some (left.label leftNode), some (right.label rightNode),
      leftAt, rightAt, observed⟩

private theorem not_mem_occupiedAddresses_of_not_mem_sourceSchedule
    (mol : RawMolecule) (key : CanonicalBranchKey) (tree : CanonicalSourceTree)
    (aligned : key.SourceTreeAligned tree) (position : List ℕ)
    (absent : position ∉ key.sourceAddressSchedule) :
    position ∉ RootedDigraph.Addressing.occupiedAddresses
      (key.toDeclarativeDigraph mol) (key.declarativeAddressing mol) := by
  intro occupied
  rw [RootedDigraph.Addressing.mem_occupiedAddresses_iff] at occupied
  rcases occupied with ⟨node, nodePosition⟩
  apply absent
  apply (CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff
    key tree aligned position).2
  change node.1 = position at nodePosition
  rw [← nodePosition]
  exact node.2

private theorem compareLex_schedule_iff_firstDifference
    {α : Type*} (compareValue : α → α → Ordering)
    (left right : List ℕ → α) (positions : List (List ℕ))
    (ordered : positions.Pairwise HierarchyAddressBefore)
    (observation : List ℕ → Ordering → Prop)
    (pointwise : ∀ position outcome,
      compareValue (left position) (right position) = outcome ↔
        observation position outcome)
    (outside : ∀ position, position ∉ positions →
      compareValue (left position) (right position) = .eq)
    (outcome : Ordering) :
    List.compareLex compareValue (positions.map left) (positions.map right) = outcome ↔
      FirstDifferenceOutcome observation outcome := by
  rw [DeclarativeCIP.compareLex_map_iff_firstDifference
    compareValue left right positions ordered outside outcome]
  exact FirstDifferenceOutcome.congr pointwise outcome

/-- The independent whole-hierarchy Rules-1a--2 judgment is single-valued. -/
theorem exactConstitutionalHierarchyFirstStrictOutcome_functional
    {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing)
    {first second : Ordering}
    (hfirst : ExactConstitutionalHierarchyFirstStrictOutcome molecule
      left leftAddressing right rightAddressing first)
    (hsecond : ExactConstitutionalHierarchyFirstStrictOutcome molecule
      left leftAddressing right rightAddressing second) :
    first = second := by
  rcases hfirst with ⟨first1a, first1b, first2, hFirst1a, hFirst1b, hFirst2, firstEq⟩
  rcases hsecond with ⟨second1a, second1b, second2,
    hSecond1a, hSecond1b, hSecond2, secondEq⟩
  have rule1aEq : first1a = second1a :=
    exactRule1aHierarchyOutcome_functional molecule left leftAddressing
      right rightAddressing hFirst1a hSecond1a
  have rule1bEq : first1b = second1b :=
    constitutionalHierarchyOutcome_functional molecule .rule1bDuplicateNodeProximity
      left leftAddressing right rightAddressing hFirst1b hSecond1b
  have rule2Eq : first2 = second2 :=
    constitutionalHierarchyOutcome_functional molecule .rule2AtomicMass
      left leftAddressing right rightAddressing hFirst2 hSecond2
  subst second1a
  subst second1b
  subst second2
  exact firstEq.symm.trans secondEq

/-- Every pair of finite addressed molecular CIP digraphs has one independent constitutional
Rules-1a--2 result. -/
theorem exactConstitutionalHierarchyFirstStrictOutcome_total
    {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (left : RootedDigraph Atom) (leftAddressing : left.Addressing)
    (right : RootedDigraph Atom) (rightAddressing : right.Addressing) :
    ∃ outcome, ExactConstitutionalHierarchyFirstStrictOutcome molecule
      left leftAddressing right rightAddressing outcome := by
  obtain ⟨rule1a, hRule1a⟩ := exactRule1aHierarchyOutcome_total molecule
    left leftAddressing right rightAddressing
  obtain ⟨rule1b, hRule1b⟩ := constitutionalHierarchyOutcome_total molecule
    .rule1bDuplicateNodeProximity left leftAddressing right rightAddressing
  obtain ⟨rule2, hRule2⟩ := constitutionalHierarchyOutcome_total molecule
    .rule2AtomicMass left leftAddressing right rightAddressing
  exact ⟨constitutionalFirstStrictDecision rule1a rule1b rule2,
    rule1a, rule1b, rule2, hRule1a, hRule1b, hRule2, rfl⟩

/-- Exact rule-ordered refinement boundary for a pair of compiled constitutional hierarchy keys.
Rule 1a is refined unconditionally.  Rule 1b is relevant only after the compiled Rule-1a fields
tie, and Rule 2 only after both earlier fields tie.  These conditions are essential: sparse keys
may use slot presence to encode a difference that an earlier rule has already decided, so a later
field need not be meaningful in isolation. -/
structure AuthoritativeConstitutionalHierarchyConformance
    (mol : RawMolecule) (leftKey rightKey : CanonicalBranchKey) : Prop where
  rule1a : ∀ outcome,
    compareSparseCanonicalLayers compareCIPAtomicLabel leftKey.rule1a rightKey.rule1a = outcome ↔
      ExactRule1aHierarchyOutcome mol.toMoleculeGraph
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol) outcome
  rule1b :
    compareSparseCanonicalLayers compareCIPAtomicLabel leftKey.rule1a rightKey.rule1a = .eq →
      ∀ outcome,
        compareSparseCanonicalLayers compareRule1bRootDistance leftKey.rule1b rightKey.rule1b =
            outcome ↔
          ConstitutionalHierarchyOutcome mol.toMoleculeGraph
            .rule1bDuplicateNodeProximity
            (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
            (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol) outcome
  rule2 :
    compareSparseCanonicalLayers compareCIPAtomicLabel leftKey.rule1a rightKey.rule1a = .eq →
      compareSparseCanonicalLayers compareRule1bRootDistance leftKey.rule1b rightKey.rule1b =
          .eq →
        ∀ outcome,
          compareSparseCanonicalLayers compare leftKey.rule2 rightKey.rule2 = outcome ↔
            ConstitutionalHierarchyOutcome mol.toMoleculeGraph .rule2AtomicMass
              (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
              (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol) outcome

/-- Once complete-sphere projection is refined rule by rule, the compiled constitutional key
comparison is exactly the independent whole-hierarchy first-strict judgment. -/
theorem compareCanonicalBranchKeys_exactConstitutionalHierarchyFirstStrict_iff
    (mol : RawMolecule) (leftKey rightKey : CanonicalBranchKey)
    (conformance : AuthoritativeConstitutionalHierarchyConformance mol leftKey rightKey)
    (outcome : Ordering) :
    compareCanonicalBranchKeys leftKey rightKey = outcome ↔
      ExactConstitutionalHierarchyFirstStrictOutcome mol.toMoleculeGraph
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol) outcome := by
  obtain ⟨rule1a, hRule1a⟩ := exactRule1aHierarchyOutcome_total mol.toMoleculeGraph
    (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
    (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
  obtain ⟨rule1b, hRule1b⟩ := constitutionalHierarchyOutcome_total mol.toMoleculeGraph
    .rule1bDuplicateNodeProximity
    (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
    (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
  obtain ⟨rule2, hRule2⟩ := constitutionalHierarchyOutcome_total mol.toMoleculeGraph
    .rule2AtomicMass
    (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
    (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
  have comparedRule1a := (conformance.rule1a rule1a).2 hRule1a
  have compared : compareCanonicalBranchKeys leftKey rightKey =
      constitutionalFirstStrictDecision rule1a rule1b rule2 := by
    cases rule1a with
    | lt =>
        simp [compareCanonicalBranchKeys, compareLex, Ordering.byKey,
          constitutionalFirstStrictDecision, comparedRule1a]
    | gt =>
        simp [compareCanonicalBranchKeys, compareLex, Ordering.byKey,
          constitutionalFirstStrictDecision, comparedRule1a]
    | eq =>
        have comparedRule1b := (conformance.rule1b comparedRule1a rule1b).2 hRule1b
        cases rule1b with
        | lt =>
            simp [compareCanonicalBranchKeys, compareLex, Ordering.byKey,
              constitutionalFirstStrictDecision, comparedRule1a, comparedRule1b]
        | gt =>
            simp [compareCanonicalBranchKeys, compareLex, Ordering.byKey,
              constitutionalFirstStrictDecision, comparedRule1a, comparedRule1b]
        | eq =>
            have comparedRule2 :=
              (conformance.rule2 comparedRule1a comparedRule1b rule2).2 hRule2
            cases rule2 <;>
              simp [compareCanonicalBranchKeys, compareLex, Ordering.byKey,
                constitutionalFirstStrictDecision, comparedRule1a, comparedRule1b,
                comparedRule2]
  constructor
  · intro result
    have decisionEq : constitutionalFirstStrictDecision rule1a rule1b rule2 = outcome :=
      compared.symm.trans result
    exact ⟨rule1a, rule1b, rule2, hRule1a, hRule1b, hRule2, decisionEq⟩
  · intro independent
    have unique := exactConstitutionalHierarchyFirstStrictOutcome_functional
      mol.toMoleculeGraph
      (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
      (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
      independent
      ⟨rule1a, rule1b, rule2, hRule1a, hRule1b, hRule2, rfl⟩
    exact compared.trans unique.symm

/-- Once the three primitive observations conform, the executable authoritative node comparator
through Rule 2 is exactly the independent first-strict constitutional judgment. -/
theorem compareCanonicalNodeThroughAuthoritative?_rule2_exactConstitutionalFirstStrict_iff
    (mol : RawMolecule) (center leftLigand rightLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (position : List ℕ)
    (leftNode : leftKey.HierarchyNode) (rightNode : rightKey.HierarchyNode)
    (leftSource rightSource : CanonicalBranchNode)
    (conformance : AuthoritativeConstitutionalNodeConformance mol center leftLigand rightLigand
      leftKey rightKey position leftNode rightNode leftSource rightSource)
    (outcome : Ordering) :
    mol.compareCanonicalNodeThroughAuthoritative? .rule2 leftSource rightSource = some outcome ↔
      ExactConstitutionalFirstStrictOutcomeAt mol center leftLigand leftKey rightKey
        position leftNode rightNode outcome := by
  obtain ⟨rule1a, hRule1a⟩ := exactRule1aOutcomeAt_total mol.toMoleculeGraph
    (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
    (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol) position
  obtain ⟨rule1b, hRule1b⟩ := constitutionalNodeOutcome_total
    (mol.canonicalHierarchyMoleculeGraph center leftLigand)
    .rule1bDuplicateNodeProximity position
    (some ((leftKey.toDeclarativeDigraph mol).label leftNode))
    (some ((rightKey.toDeclarativeDigraph mol).label rightNode))
  obtain ⟨rule2, hRule2⟩ := constitutionalNodeOutcome_total
    (mol.canonicalHierarchyMoleculeGraph center leftLigand)
    .rule2AtomicMass position
    (some ((leftKey.toDeclarativeDigraph mol).label leftNode))
    (some ((rightKey.toDeclarativeDigraph mol).label rightNode))
  have computedRule1a := (conformance.rule1a rule1a).2 hRule1a
  have computedRule1b := (conformance.rule1b rule1b).2 hRule1b
  have computedRule2 := (conformance.rule2 rule2).2 hRule2
  have computed :
      mol.compareCanonicalNodeThroughAuthoritative? .rule2 leftSource rightSource =
        some (constitutionalFirstStrictDecision rule1a rule1b rule2) := by
    cases rule1a <;> cases rule1b <;> cases rule2 <;>
      simp_all [compareCanonicalNodeThroughAuthoritative?, constitutionalFirstStrictDecision]
  constructor
  · intro result
    have decisionEq : constitutionalFirstStrictDecision rule1a rule1b rule2 = outcome :=
      Option.some.inj (computed.symm.trans result)
    exact ⟨rule1a, rule1b, rule2, hRule1a, hRule1b, hRule2, decisionEq⟩
  · rintro ⟨otherRule1a, otherRule1b, otherRule2,
      hOtherRule1a, hOtherRule1b, hOtherRule2, hDecision⟩
    have rule1aEq : otherRule1a = rule1a :=
      exactRule1aOutcomeAt_functional mol.toMoleculeGraph
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
        position hOtherRule1a hRule1a
    have rule1bEq : otherRule1b = rule1b :=
      constitutionalNodeOutcome_functional
        (mol.canonicalHierarchyMoleculeGraph center leftLigand)
        .rule1bDuplicateNodeProximity position
        (some ((leftKey.toDeclarativeDigraph mol).label leftNode))
        (some ((rightKey.toDeclarativeDigraph mol).label rightNode))
        hOtherRule1b hRule1b
    have rule2Eq : otherRule2 = rule2 :=
      constitutionalNodeOutcome_functional
        (mol.canonicalHierarchyMoleculeGraph center leftLigand)
        .rule2AtomicMass position
        (some ((leftKey.toDeclarativeDigraph mol).label leftNode))
        (some ((rightKey.toDeclarativeDigraph mol).label rightNode))
        hOtherRule2 hRule2
    subst otherRule1a
    subst otherRule1b
    subst otherRule2
    simpa [hDecision] using computed

/-- Successful complete authoritative compilation plus ordinary molecular admission discharges
the exact independent semantics of Rules 1a, 1b, and 2 at every pair of realized nodes occupying
the same hierarchy position. -/
theorem branchCanonicalKeysAuthoritative_constitutionalNodeConformance
    (mol : RawMolecule) (center leftLigand rightLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (admitted : mol.Admissible)
    (leftComputed :
      branchCanonicalKeyAuthoritative? mol center.val leftLigand.val = some leftKey)
    (rightComputed :
      branchCanonicalKeyAuthoritative? mol center.val rightLigand.val = some rightKey)
    (leftComplete : leftKey.complete = true)
    (rightComplete : rightKey.complete = true)
    (position : List ℕ)
    (leftNode : leftKey.HierarchyNode) (rightNode : rightKey.HierarchyNode)
    (leftPosition : leftNode.val = position)
    (rightPosition : rightNode.val = position)
    (leftSource rightSource : CanonicalBranchNode)
    (leftSourceAt : leftKey.sourceNodeAtAddress? leftNode.val = some leftSource)
    (rightSourceAt : rightKey.sourceNodeAtAddress? rightNode.val = some rightSource) :
    AuthoritativeConstitutionalNodeConformance mol center leftLigand rightLigand
      leftKey rightKey position leftNode rightNode leftSource rightSource := by
  have leftStructural := mol.branchCanonicalKeyAuthoritative?_rootedAt_childrenExact
    center.val leftLigand.val leftKey leftComputed leftComplete
  have rightStructural := mol.branchCanonicalKeyAuthoritative?_rootedAt_childrenExact
    center.val rightLigand.val rightKey rightComputed rightComplete
  have leftRule1a :=
    mol.branchCanonicalKeyAuthoritative?_rule1aObservationCorrect
      center leftLigand leftKey admitted leftComputed leftComplete
      leftNode leftSource leftSourceAt
  have rightRule1a :=
    mol.branchCanonicalKeyAuthoritative?_rule1aObservationCorrect
      center rightLigand rightKey admitted rightComputed rightComplete
      rightNode rightSource rightSourceAt
  refine
    { rule1a := ?_
      rule1b := ?_
      rule2 := ?_ }
  · intro outcome
    exact pairedNodeRule1aOutcome_iff_authoritative mol leftKey rightKey position
      leftNode rightNode leftPosition rightPosition leftSource rightSource
      leftRule1a rightRule1a outcome
  · intro outcome
    change some (mol.compareCanonicalNodeRule .rule1b leftSource rightSource) = some outcome ↔ _
    simp only [Option.some.injEq]
    exact CanonicalBranchKey.pairedNodeRule1bOutcome_iff_production
      mol (mol.canonicalHierarchyMoleculeGraph center leftLigand)
      leftKey rightKey center leftLigand center rightLigand
      leftStructural.1 rightStructural.1 leftStructural.2 rightStructural.2
      position leftNode rightNode leftPosition rightPosition
      leftSource rightSource leftSourceAt rightSourceAt outcome
  · intro outcome
    simpa [leftPosition] using
      (branchCanonicalKeysAuthoritative_rule2_nodeOutcome_iff
        mol center leftLigand rightLigand leftKey rightKey admitted
        leftComputed rightComputed leftComplete rightComplete
        leftNode rightNode leftSource rightSource leftSourceAt rightSourceAt outcome)

/-- Successful complete branch compilation discharges every premise of the exact independent
first-strict constitutional comparison theorem. -/
theorem branchCanonicalKeysAuthoritative_rule2_exactConstitutionalFirstStrict_iff
    (mol : RawMolecule) (center leftLigand rightLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (admitted : mol.Admissible)
    (leftComputed :
      branchCanonicalKeyAuthoritative? mol center.val leftLigand.val = some leftKey)
    (rightComputed :
      branchCanonicalKeyAuthoritative? mol center.val rightLigand.val = some rightKey)
    (leftComplete : leftKey.complete = true)
    (rightComplete : rightKey.complete = true)
    (position : List ℕ)
    (leftNode : leftKey.HierarchyNode) (rightNode : rightKey.HierarchyNode)
    (leftPosition : leftNode.val = position)
    (rightPosition : rightNode.val = position)
    (leftSource rightSource : CanonicalBranchNode)
    (leftSourceAt : leftKey.sourceNodeAtAddress? leftNode.val = some leftSource)
    (rightSourceAt : rightKey.sourceNodeAtAddress? rightNode.val = some rightSource)
    (outcome : Ordering) :
    mol.compareCanonicalNodeThroughAuthoritative? .rule2 leftSource rightSource = some outcome ↔
      ExactConstitutionalFirstStrictOutcomeAt mol center leftLigand leftKey rightKey
        position leftNode rightNode outcome := by
  exact compareCanonicalNodeThroughAuthoritative?_rule2_exactConstitutionalFirstStrict_iff
    mol center leftLigand rightLigand leftKey rightKey position leftNode rightNode
    leftSource rightSource
    (branchCanonicalKeysAuthoritative_constitutionalNodeConformance
      mol center leftLigand rightLigand leftKey rightKey admitted
      leftComputed rightComputed leftComplete rightComplete position
      leftNode rightNode leftPosition rightPosition leftSource rightSource
      leftSourceAt rightSourceAt)
    outcome

private theorem branchCanonicalKeysAuthoritative_rule1bOutcomeAt_of_mem_schedule
    (mol : RawMolecule) (center leftLigand rightLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (leftComputed :
      branchCanonicalKeyAuthoritative? mol center.val leftLigand.val = some leftKey)
    (rightComputed :
      branchCanonicalKeyAuthoritative? mol center.val rightLigand.val = some rightKey)
    (leftComplete : leftKey.complete = true)
    (rightComplete : rightKey.complete = true)
    (leftTree rightTree : CanonicalSourceTree)
    (leftTreeAligned : leftKey.SourceTreeAligned leftTree)
    (rightTreeAligned : rightKey.SourceTreeAligned rightTree)
    (schedulesEq : leftKey.sourceAddressSchedule = rightKey.sourceAddressSchedule)
    (position : List ℕ) (present : position ∈ leftKey.sourceAddressSchedule)
    (outcome : Ordering) :
    compareRule1bRootDistance
        (canonicalSourceObservationAt leftKey CanonicalBranchNode.rule1bCode position)
        (canonicalSourceObservationAt rightKey CanonicalBranchNode.rule1bCode position) =
          outcome ↔
      ConstitutionalOutcomeAt mol.toMoleculeGraph .rule1bDuplicateNodeProximity
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
        position outcome := by
  have rightPresent : position ∈ rightKey.sourceAddressSchedule := by
    rwa [← schedulesEq]
  obtain ⟨leftSource, leftSourceAt⟩ :=
    (CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff_exists_source
      leftKey leftTree leftTreeAligned position).mp present
  obtain ⟨rightSource, rightSourceAt⟩ :=
    (CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff_exists_source
      rightKey rightTree rightTreeAligned position).mp rightPresent
  have leftAddress : position ∈ leftKey.hierarchyAddresses :=
    (CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff
      leftKey leftTree leftTreeAligned position).mp present
  have rightAddress : position ∈ rightKey.hierarchyAddresses :=
    (CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff
      rightKey rightTree rightTreeAligned position).mp rightPresent
  let leftNode : leftKey.HierarchyNode := ⟨position, leftAddress⟩
  let rightNode : rightKey.HierarchyNode := ⟨position, rightAddress⟩
  have leftStructural := mol.branchCanonicalKeyAuthoritative?_rootedAt_childrenExact
    center.val leftLigand.val leftKey leftComputed leftComplete
  have rightStructural := mol.branchCanonicalKeyAuthoritative?_rootedAt_childrenExact
    center.val rightLigand.val rightKey rightComputed rightComplete
  have localComparison := CanonicalBranchKey.pairedNodeRule1bOutcome_iff_production
    mol mol.toMoleculeGraph leftKey rightKey center leftLigand center rightLigand
    leftStructural.1 rightStructural.1 leftStructural.2 rightStructural.2
    position leftNode rightNode rfl rfl leftSource rightSource
    leftSourceAt rightSourceAt outcome
  have wrapped := constitutionalOutcomeAt_iff_of_nodes
    mol.toMoleculeGraph .rule1bDuplicateNodeProximity
    (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
    (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
    position leftNode rightNode rfl rfl outcome
  simp only [canonicalSourceObservationAt, leftSourceAt, rightSourceAt,
    Option.map_some, Option.getD_some]
  rw [compareRule1bRootDistance_eq_nodeRule]
  exact localComparison.trans wrapped.symm

/-- After the Rule-1a support-establishing tie, the compiled whole-hierarchy Rule-1b projection is
exactly the independent first-difference Rule-1b judgment. -/
theorem branchCanonicalKeysAuthoritative_rule1bHierarchyOutcome_iff
    (mol : RawMolecule) (center leftLigand rightLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (leftComputed :
      branchCanonicalKeyAuthoritative? mol center.val leftLigand.val = some leftKey)
    (rightComputed :
      branchCanonicalKeyAuthoritative? mol center.val rightLigand.val = some rightKey)
    (leftComplete : leftKey.complete = true)
    (rightComplete : rightKey.complete = true)
    (rule1aTie : compareSparseCanonicalLayers compareCIPAtomicLabel
      leftKey.rule1a rightKey.rule1a = .eq)
    (outcome : Ordering) :
    compareSparseCanonicalLayers compareRule1bRootDistance
        leftKey.rule1b rightKey.rule1b = outcome ↔
      ConstitutionalHierarchyOutcome mol.toMoleculeGraph
        .rule1bDuplicateNodeProximity
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
        outcome := by
  have leftAligned := mol.branchCanonicalKeyAuthoritative?_sourceAligned
    center.val leftLigand.val leftKey leftComputed
  have rightAligned := mol.branchCanonicalKeyAuthoritative?_sourceAligned
    center.val rightLigand.val rightKey rightComputed
  obtain ⟨leftTree, leftTreeAligned⟩ :=
    mol.branchCanonicalKeyAuthoritative?_sourceTreeAligned
      center.val leftLigand.val leftKey leftComputed
  obtain ⟨rightTree, rightTreeAligned⟩ :=
    mol.branchCanonicalKeyAuthoritative?_sourceTreeAligned
      center.val rightLigand.val rightKey rightComputed
  have schedulesEq :=
    CanonicalBranchKey.AuthoritativeSourceAligned.sourceAddressSchedule_eq_of_rule1a_tie
      mol leftKey rightKey leftAligned rightAligned rule1aTie
  have ordered := mol.branchCanonicalKeyAuthoritative?_sourceAddressSchedule_pairwise
    center.val leftLigand.val leftKey leftComputed
  rw [compareRule1b_eq_compareLex_sourceSchedule_of_rule1a_tie
    mol leftKey rightKey leftAligned rightAligned rule1aTie]
  rw [CanonicalBranchKey.SourceTreeAligned.map_observation_eq_schedule_map
    leftKey leftTree leftTreeAligned CanonicalBranchNode.rule1bCode]
  rw [CanonicalBranchKey.SourceTreeAligned.map_observation_eq_schedule_map
    rightKey rightTree rightTreeAligned CanonicalBranchNode.rule1bCode]
  rw [← schedulesEq]
  apply compareLex_schedule_iff_firstDifference
    compareRule1bRootDistance
    (canonicalSourceObservationAt leftKey CanonicalBranchNode.rule1bCode)
    (canonicalSourceObservationAt rightKey CanonicalBranchNode.rule1bCode)
    leftKey.sourceAddressSchedule ordered
    (ConstitutionalOutcomeAt mol.toMoleculeGraph .rule1bDuplicateNodeProximity
      (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
      (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol))
  · intro position localOutcome
    by_cases present : position ∈ leftKey.sourceAddressSchedule
    · exact branchCanonicalKeysAuthoritative_rule1bOutcomeAt_of_mem_schedule
        mol center leftLigand rightLigand leftKey rightKey
        leftComputed rightComputed leftComplete rightComplete
        leftTree rightTree leftTreeAligned rightTreeAligned schedulesEq
        position present localOutcome
    · have rightAbsent : position ∉ rightKey.sourceAddressSchedule := by
        rwa [← schedulesEq]
      have leftLookup : leftKey.sourceNodeAtAddress? position = none := by
        cases found : leftKey.sourceNodeAtAddress? position with
        | none => rfl
        | some source =>
            exact (present ((CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff_exists_source
                leftKey leftTree leftTreeAligned position).2 ⟨source, found⟩)).elim
      have rightLookup : rightKey.sourceNodeAtAddress? position = none := by
        cases found : rightKey.sourceNodeAtAddress? position with
        | none => rfl
        | some source =>
            exact (rightAbsent ((CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff_exists_source
                rightKey rightTree rightTreeAligned position).2 ⟨source, found⟩)).elim
      have semanticEq := constitutionalOutcomeAt_eq_of_outside mol.toMoleculeGraph
        .rule1bDuplicateNodeProximity
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
        position
        (not_mem_occupiedAddresses_of_not_mem_sourceSchedule
          mol leftKey leftTree leftTreeAligned position present)
        (not_mem_occupiedAddresses_of_not_mem_sourceSchedule
          mol rightKey rightTree rightTreeAligned position rightAbsent)
      constructor
      · intro computed
        have localEq : localOutcome = .eq := by
          simpa [canonicalSourceObservationAt, leftLookup, rightLookup,
            compareRule1bRootDistance, flip] using computed.symm
        rw [localEq]
        exact semanticEq
      · intro semantic
        have localEq : localOutcome = .eq :=
          constitutionalOutcomeAt_functional mol.toMoleculeGraph
            .rule1bDuplicateNodeProximity
            (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
            (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
            position semantic semanticEq
        rw [localEq]
        simp [canonicalSourceObservationAt, leftLookup, rightLookup,
          compareRule1bRootDistance, flip]
  · intro position absent
    have rightAbsent : position ∉ rightKey.sourceAddressSchedule := by
      rwa [← schedulesEq]
    have leftLookup : leftKey.sourceNodeAtAddress? position = none := by
      cases found : leftKey.sourceNodeAtAddress? position with
      | none => rfl
      | some source =>
          exact (absent ((CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff_exists_source
              leftKey leftTree leftTreeAligned position).2 ⟨source, found⟩)).elim
    have rightLookup : rightKey.sourceNodeAtAddress? position = none := by
      cases found : rightKey.sourceNodeAtAddress? position with
      | none => rfl
      | some source =>
          exact (rightAbsent ((CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff_exists_source
              rightKey rightTree rightTreeAligned position).2 ⟨source, found⟩)).elim
    simp [canonicalSourceObservationAt, leftLookup, rightLookup,
      compareRule1bRootDistance, flip]

private theorem branchCanonicalKeysAuthoritative_rule2OutcomeAt_of_mem_schedule
    (mol : RawMolecule) (center leftLigand rightLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (admitted : mol.Admissible)
    (leftComputed :
      branchCanonicalKeyAuthoritative? mol center.val leftLigand.val = some leftKey)
    (rightComputed :
      branchCanonicalKeyAuthoritative? mol center.val rightLigand.val = some rightKey)
    (leftComplete : leftKey.complete = true)
    (rightComplete : rightKey.complete = true)
    (leftTree rightTree : CanonicalSourceTree)
    (leftTreeAligned : leftKey.SourceTreeAligned leftTree)
    (rightTreeAligned : rightKey.SourceTreeAligned rightTree)
    (schedulesEq : leftKey.sourceAddressSchedule = rightKey.sourceAddressSchedule)
    (position : List ℕ) (present : position ∈ leftKey.sourceAddressSchedule)
    (outcome : Ordering) :
    compare
        (canonicalSourceObservationAt leftKey mol.canonicalRule2Mass position)
        (canonicalSourceObservationAt rightKey mol.canonicalRule2Mass position) = outcome ↔
      ConstitutionalOutcomeAt mol.toMoleculeGraph .rule2AtomicMass
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
        position outcome := by
  have rightPresent : position ∈ rightKey.sourceAddressSchedule := by
    rwa [← schedulesEq]
  obtain ⟨leftSource, leftSourceAt⟩ :=
    (CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff_exists_source
      leftKey leftTree leftTreeAligned position).mp present
  obtain ⟨rightSource, rightSourceAt⟩ :=
    (CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff_exists_source
      rightKey rightTree rightTreeAligned position).mp rightPresent
  have leftAddress : position ∈ leftKey.hierarchyAddresses :=
    (CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff
      leftKey leftTree leftTreeAligned position).mp present
  have rightAddress : position ∈ rightKey.hierarchyAddresses :=
    (CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff
      rightKey rightTree rightTreeAligned position).mp rightPresent
  let leftNode : leftKey.HierarchyNode := ⟨position, leftAddress⟩
  let rightNode : rightKey.HierarchyNode := ⟨position, rightAddress⟩
  have localComparison := branchCanonicalKeysAuthoritative_rule2_nodeOutcome_iff
    mol center leftLigand rightLigand leftKey rightKey admitted
    leftComputed rightComputed leftComplete rightComplete
    leftNode rightNode leftSource rightSource leftSourceAt rightSourceAt outcome
  have localToMolecule :
      compare (mol.canonicalRule2Mass leftSource)
          (mol.canonicalRule2Mass rightSource) = outcome ↔
        ConstitutionalNodeOutcome mol.toMoleculeGraph .rule2AtomicMass position
          (some ((leftKey.toDeclarativeDigraph mol).label leftNode))
          (some ((rightKey.toDeclarativeDigraph mol).label rightNode)) outcome := by
    change some (compare (mol.canonicalRule2Mass leftSource)
        (mol.canonicalRule2Mass rightSource)) = some outcome ↔ _ at localComparison
    simp only [Option.some.injEq] at localComparison
    simpa [ConstitutionalNodeOutcome, nodeAtomicMass] using localComparison
  have wrapped := constitutionalOutcomeAt_iff_of_nodes
    mol.toMoleculeGraph .rule2AtomicMass
    (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
    (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
    position leftNode rightNode rfl rfl outcome
  simp only [canonicalSourceObservationAt, leftSourceAt, rightSourceAt,
    Option.map_some, Option.getD_some]
  exact localToMolecule.trans wrapped.symm

/-- On a common support established by Rule 1a, the compiled whole-hierarchy Rule-2 projection is
exactly the independent first-difference mass judgment. -/
theorem branchCanonicalKeysAuthoritative_rule2HierarchyOutcome_iff
    (mol : RawMolecule) (center leftLigand rightLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (admitted : mol.Admissible)
    (leftComputed :
      branchCanonicalKeyAuthoritative? mol center.val leftLigand.val = some leftKey)
    (rightComputed :
      branchCanonicalKeyAuthoritative? mol center.val rightLigand.val = some rightKey)
    (leftComplete : leftKey.complete = true)
    (rightComplete : rightKey.complete = true)
    (rule1aTie : compareSparseCanonicalLayers compareCIPAtomicLabel
      leftKey.rule1a rightKey.rule1a = .eq)
    (outcome : Ordering) :
    compareSparseCanonicalLayers compare leftKey.rule2 rightKey.rule2 = outcome ↔
      ConstitutionalHierarchyOutcome mol.toMoleculeGraph .rule2AtomicMass
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
        outcome := by
  have leftAligned := mol.branchCanonicalKeyAuthoritative?_sourceAligned
    center.val leftLigand.val leftKey leftComputed
  have rightAligned := mol.branchCanonicalKeyAuthoritative?_sourceAligned
    center.val rightLigand.val rightKey rightComputed
  obtain ⟨leftTree, leftTreeAligned⟩ :=
    mol.branchCanonicalKeyAuthoritative?_sourceTreeAligned
      center.val leftLigand.val leftKey leftComputed
  obtain ⟨rightTree, rightTreeAligned⟩ :=
    mol.branchCanonicalKeyAuthoritative?_sourceTreeAligned
      center.val rightLigand.val rightKey rightComputed
  have schedulesEq :=
    CanonicalBranchKey.AuthoritativeSourceAligned.sourceAddressSchedule_eq_of_rule1a_tie
      mol leftKey rightKey leftAligned rightAligned rule1aTie
  have ordered := mol.branchCanonicalKeyAuthoritative?_sourceAddressSchedule_pairwise
    center.val leftLigand.val leftKey leftComputed
  rw [compareRule2_eq_compareLex_sourceSchedule_of_rule1a_tie
    mol leftKey rightKey leftAligned rightAligned rule1aTie]
  rw [CanonicalBranchKey.SourceTreeAligned.map_observation_eq_schedule_map
    leftKey leftTree leftTreeAligned mol.canonicalRule2Mass]
  rw [CanonicalBranchKey.SourceTreeAligned.map_observation_eq_schedule_map
    rightKey rightTree rightTreeAligned mol.canonicalRule2Mass]
  rw [← schedulesEq]
  apply compareLex_schedule_iff_firstDifference
    compare
    (canonicalSourceObservationAt leftKey mol.canonicalRule2Mass)
    (canonicalSourceObservationAt rightKey mol.canonicalRule2Mass)
    leftKey.sourceAddressSchedule ordered
    (ConstitutionalOutcomeAt mol.toMoleculeGraph .rule2AtomicMass
      (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
      (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol))
  · intro position localOutcome
    by_cases present : position ∈ leftKey.sourceAddressSchedule
    · exact branchCanonicalKeysAuthoritative_rule2OutcomeAt_of_mem_schedule
        mol center leftLigand rightLigand leftKey rightKey admitted
        leftComputed rightComputed leftComplete rightComplete
        leftTree rightTree leftTreeAligned rightTreeAligned schedulesEq
        position present localOutcome
    · have rightAbsent : position ∉ rightKey.sourceAddressSchedule := by
        rwa [← schedulesEq]
      have leftLookup : leftKey.sourceNodeAtAddress? position = none := by
        cases found : leftKey.sourceNodeAtAddress? position with
        | none => rfl
        | some source =>
            exact (present ((CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff_exists_source
              leftKey leftTree leftTreeAligned position).2 ⟨source, found⟩)).elim
      have rightLookup : rightKey.sourceNodeAtAddress? position = none := by
        cases found : rightKey.sourceNodeAtAddress? position with
        | none => rfl
        | some source =>
            exact (rightAbsent ((CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff_exists_source
              rightKey rightTree rightTreeAligned position).2 ⟨source, found⟩)).elim
      have semanticEq := constitutionalOutcomeAt_eq_of_outside mol.toMoleculeGraph
        .rule2AtomicMass
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
        position
        (not_mem_occupiedAddresses_of_not_mem_sourceSchedule
          mol leftKey leftTree leftTreeAligned position present)
        (not_mem_occupiedAddresses_of_not_mem_sourceSchedule
          mol rightKey rightTree rightTreeAligned position rightAbsent)
      constructor
      · intro computed
        have localEq : localOutcome = .eq := by
          simpa [canonicalSourceObservationAt, leftLookup, rightLookup] using computed.symm
        rw [localEq]
        exact semanticEq
      · intro semantic
        have localEq : localOutcome = .eq :=
          constitutionalOutcomeAt_functional mol.toMoleculeGraph .rule2AtomicMass
            (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
            (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
            position semantic semanticEq
        rw [localEq]
        simp [canonicalSourceObservationAt, leftLookup, rightLookup]
  · intro position absent
    have rightAbsent : position ∉ rightKey.sourceAddressSchedule := by
      rwa [← schedulesEq]
    have leftLookup : leftKey.sourceNodeAtAddress? position = none := by
      cases found : leftKey.sourceNodeAtAddress? position with
      | none => rfl
      | some source =>
          exact (absent ((CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff_exists_source
            leftKey leftTree leftTreeAligned position).2 ⟨source, found⟩)).elim
    have rightLookup : rightKey.sourceNodeAtAddress? position = none := by
      cases found : rightKey.sourceNodeAtAddress? position with
      | none => rfl
      | some source =>
          exact (rightAbsent ((CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff_exists_source
            rightKey rightTree rightTreeAligned position).2 ⟨source, found⟩)).elim
    simp [canonicalSourceObservationAt, leftLookup, rightLookup]

/-- Successful complete authoritative compilation now discharges both later constitutional
hierarchy projections automatically.  The sole remaining premise is the unconditional sparse
Rule-1a/zero-observation bridge, whose unequal-support case is genuinely Rule-1a-specific. -/
theorem branchCanonicalKeysAuthoritative_constitutionalHierarchyConformance_of_rule1a
    (mol : RawMolecule) (center leftLigand rightLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (admitted : mol.Admissible)
    (leftComputed :
      branchCanonicalKeyAuthoritative? mol center.val leftLigand.val = some leftKey)
    (rightComputed :
      branchCanonicalKeyAuthoritative? mol center.val rightLigand.val = some rightKey)
    (leftComplete : leftKey.complete = true)
    (rightComplete : rightKey.complete = true)
    (rule1aConformance : ∀ outcome,
      compareSparseCanonicalLayers compareCIPAtomicLabel
          leftKey.rule1a rightKey.rule1a = outcome ↔
        ExactRule1aHierarchyOutcome mol.toMoleculeGraph
          (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
          (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
          outcome) :
    AuthoritativeConstitutionalHierarchyConformance mol leftKey rightKey := by
  refine
    { rule1a := rule1aConformance
      rule1b := ?_
      rule2 := ?_ }
  · intro rule1aTie outcome
    exact branchCanonicalKeysAuthoritative_rule1bHierarchyOutcome_iff
      mol center leftLigand rightLigand leftKey rightKey
      leftComputed rightComputed leftComplete rightComplete rule1aTie outcome
  · intro rule1aTie _rule1bTie outcome
    exact branchCanonicalKeysAuthoritative_rule2HierarchyOutcome_iff
      mol center leftLigand rightLigand leftKey rightKey admitted
      leftComputed rightComputed leftComplete rightComplete rule1aTie outcome

/-- With that one Rule-1a projection premise, the complete compiled constitutional comparator is
already equivalent to the independent whole-hierarchy Rules-1a--2 judgment. -/
theorem branchCanonicalKeysAuthoritative_exactConstitutionalHierarchyFirstStrict_iff_of_rule1a
    (mol : RawMolecule) (center leftLigand rightLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (admitted : mol.Admissible)
    (leftComputed :
      branchCanonicalKeyAuthoritative? mol center.val leftLigand.val = some leftKey)
    (rightComputed :
      branchCanonicalKeyAuthoritative? mol center.val rightLigand.val = some rightKey)
    (leftComplete : leftKey.complete = true)
    (rightComplete : rightKey.complete = true)
    (rule1aConformance : ∀ outcome,
      compareSparseCanonicalLayers compareCIPAtomicLabel
          leftKey.rule1a rightKey.rule1a = outcome ↔
        ExactRule1aHierarchyOutcome mol.toMoleculeGraph
          (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
          (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
          outcome)
    (outcome : Ordering) :
    compareCanonicalBranchKeys leftKey rightKey = outcome ↔
      ExactConstitutionalHierarchyFirstStrictOutcome mol.toMoleculeGraph
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
        outcome := by
  exact compareCanonicalBranchKeys_exactConstitutionalHierarchyFirstStrict_iff
    mol leftKey rightKey
    (branchCanonicalKeysAuthoritative_constitutionalHierarchyConformance_of_rule1a
      mol center leftLigand rightLigand leftKey rightKey admitted
      leftComputed rightComputed leftComplete rightComplete rule1aConformance)
    outcome

/-- Mass admission supplies the positivity premise of the unconditional Rule-1a bridge, so a
successful complete authoritative pair satisfies all constitutional Rules 1a, 1b, and 2 without
an externally supplied comparison hypothesis. -/
theorem branchCanonicalKeysAuthoritative_constitutionalHierarchyConformance
    (mol : RawMolecule) (center leftLigand rightLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (admitted : mol.Admissible)
    (known : mol.Rule2MassesKnown)
    (leftComputed :
      branchCanonicalKeyAuthoritative? mol center.val leftLigand.val = some leftKey)
    (rightComputed :
      branchCanonicalKeyAuthoritative? mol center.val rightLigand.val = some rightKey)
    (leftComplete : leftKey.complete = true)
    (rightComplete : rightKey.complete = true) :
    AuthoritativeConstitutionalHierarchyConformance mol leftKey rightKey := by
  apply branchCanonicalKeysAuthoritative_constitutionalHierarchyConformance_of_rule1a
    mol center leftLigand rightLigand leftKey rightKey admitted
      leftComputed rightComputed leftComplete rightComplete
  intro outcome
  exact branchCanonicalKeysAuthoritative_rule1aHierarchyOutcome_iff
    mol center leftLigand rightLigand leftKey rightKey admitted known
      leftComputed rightComputed leftComplete rightComplete outcome

/-- End-to-end constitutional theorem for a pair of complete authoritative ligand keys: the
compiled Rules-1a--2 comparison is exactly the independently specified whole-hierarchy
first-strict judgment. -/
theorem branchCanonicalKeysAuthoritative_exactConstitutionalHierarchyFirstStrict_iff
    (mol : RawMolecule) (center leftLigand rightLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (admitted : mol.Admissible)
    (known : mol.Rule2MassesKnown)
    (leftComputed :
      branchCanonicalKeyAuthoritative? mol center.val leftLigand.val = some leftKey)
    (rightComputed :
      branchCanonicalKeyAuthoritative? mol center.val rightLigand.val = some rightKey)
    (leftComplete : leftKey.complete = true)
    (rightComplete : rightKey.complete = true)
    (outcome : Ordering) :
    compareCanonicalBranchKeys leftKey rightKey = outcome ↔
      ExactConstitutionalHierarchyFirstStrictOutcome mol.toMoleculeGraph
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
        outcome := by
  exact compareCanonicalBranchKeys_exactConstitutionalHierarchyFirstStrict_iff
    mol leftKey rightKey
      (branchCanonicalKeysAuthoritative_constitutionalHierarchyConformance
        mol center leftLigand rightLigand leftKey rightKey admitted known
          leftComputed rightComputed leftComplete rightComplete)
    outcome

end RawMolecule

end

end TetraStereo.OneCenter
