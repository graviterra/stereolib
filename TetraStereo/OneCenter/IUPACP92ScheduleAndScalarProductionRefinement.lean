import TetraStereo.OneCenter.IUPACP92Rule1aProductionRefinement
import TetraStereo.OneCenter.DeclarativeCIPPreorder

set_option autoImplicit false

/-!
# Production refinement for P-92 schedule and scalar rows

This module connects three further P-92 authority rows to total production functions:

* sphere-major comparison executes `firstStrictOnHierarchySchedule`;
* exhaustive rule ordering selects the least-ranked strict sequence rule, or reports a total tie;
* saturated-compound Rule 1a compares the exact atomic-number labels directly.

The constructions produce the reviewed observations themselves and prove their independent
`Judges` relations.  No arbitrary outcome or first-decisive witness is accepted from a caller.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open DeclarativeCIP

/-! ## Sphere-major first-difference execution -/

def p92ProductionSphereExplorationObservation
    (comparison : P92LigandComparisonAuthorityContext)
    (positions : List (List Nat)) (comparisonAt : List Nat → Ordering) :
    P92SphereExplorationAuthorityObservation where
  comparison := comparison
  positions := positions
  comparisonAt := comparisonAt
  outcome := firstStrictOnHierarchySchedule positions comparisonAt

theorem p92ProductionSphereExploration_judged
    (source : AuthoritativeChemicalInput)
    (comparison : P92LigandComparisonAuthorityContext)
    (positions : List (List Nat)) (comparisonAt : List Nat → Ordering)
    (ready : comparison.Ready source)
    (ordered : positions.Pairwise HierarchyAddressBefore)
    (outside : ∀ position, position ∉ positions → comparisonAt position = Ordering.eq) :
    p92SphereExplorationReference.Judges source
      (p92ProductionSphereExplorationObservation comparison positions comparisonAt) := by
  exact ⟨ready, ordered, outside,
    firstStrictOnHierarchySchedule_is_firstDifference comparisonAt positions ordered outside⟩

/-! ## Total first-decisive sequence-rule selection -/

theorem exists_first_strict_sequenceRule
    (outcomeAt : SequenceRule → Ordering)
    (notAllTie : ¬ ∀ rule, outcomeAt rule = Ordering.eq) :
    ∃ rule,
      P92OrderingStrict (outcomeAt rule) ∧
        ∀ earlier, earlier.Before rule → outcomeAt earlier = Ordering.eq := by
  classical
  push_neg at notAllTie
  let decisiveRank : Nat → Prop := fun rank =>
    ∃ rule, rule.rank = rank ∧ outcomeAt rule ≠ Ordering.eq
  have rankExists : ∃ rank, decisiveRank rank := by
    rcases notAllTie with ⟨rule, decisive⟩
    exact ⟨rule.rank, rule, rfl, decisive⟩
  let firstRank := Nat.find rankExists
  rcases Nat.find_spec rankExists with ⟨rule, rankEq, decisive⟩
  refine ⟨rule, ?_, ?_⟩
  · cases outcomeEq : outcomeAt rule with
    | lt | gt => simp [P92OrderingStrict]
    | eq => exact (decisive outcomeEq).elim
  · intro earlier before
    by_contra earlierNotTie
    have earlierWitness : decisiveRank earlier.rank :=
      ⟨earlier, rfl, earlierNotTie⟩
    have minimal : firstRank ≤ earlier.rank := Nat.find_min' rankExists earlierWitness
    have earlierLt : earlier.rank < firstRank := by
      simpa [SequenceRule.Before, firstRank, rankEq] using before
    exact (Nat.not_lt_of_ge minimal) earlierLt

def firstStrictSequenceRule?
    (outcomeAt : SequenceRule → Ordering) : Option SequenceRule :=
  if outcomeAt .rule1aAtomicNumber = Ordering.eq then
    if outcomeAt .rule1bDuplicateNodeProximity = Ordering.eq then
      if outcomeAt .rule2AtomicMass = Ordering.eq then
        if outcomeAt .rule3DoubleBondGeometry = Ordering.eq then
          if outcomeAt .rule4aStereogenicUnitKind = Ordering.eq then
            if outcomeAt .rule4bLikeUnlikeDescriptorPairs = Ordering.eq then
              if outcomeAt .rule4cPseudoasymmetricDescriptor = Ordering.eq then
                if outcomeAt .rule5EnantiomorphicDescriptor = Ordering.eq then
                  if outcomeAt .rule6ReferencePromotion = Ordering.eq then none
                  else some .rule6ReferencePromotion
                else some .rule5EnantiomorphicDescriptor
              else some .rule4cPseudoasymmetricDescriptor
            else some .rule4bLikeUnlikeDescriptorPairs
          else some .rule4aStereogenicUnitKind
        else some .rule3DoubleBondGeometry
      else some .rule2AtomicMass
    else some .rule1bDuplicateNodeProximity
  else some .rule1aAtomicNumber

theorem p92OrderingStrict_ne_eq {outcome : Ordering}
    (strict : P92OrderingStrict outcome) : outcome ≠ Ordering.eq := by
  cases outcome <;> simp_all [P92OrderingStrict]

theorem firstStrictSequenceRule_eq_some_of_spec
    (outcomeAt : SequenceRule → Ordering) (rule : SequenceRule)
    (strict : P92OrderingStrict (outcomeAt rule))
    (earlierTie : ∀ earlier, earlier.Before rule →
      outcomeAt earlier = Ordering.eq) :
    firstStrictSequenceRule? outcomeAt = some rule := by
  have ruleNeTie := p92OrderingStrict_ne_eq strict
  cases rule with
  | rule1aAtomicNumber =>
      simp [firstStrictSequenceRule?, ruleNeTie]
  | rule1bDuplicateNodeProximity =>
      have h1 := earlierTie .rule1aAtomicNumber (by
        simp [SequenceRule.Before, SequenceRule.rank])
      simp [firstStrictSequenceRule?, h1, ruleNeTie]
  | rule2AtomicMass =>
      have h1 := earlierTie .rule1aAtomicNumber (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h2 := earlierTie .rule1bDuplicateNodeProximity (by
        simp [SequenceRule.Before, SequenceRule.rank])
      simp [firstStrictSequenceRule?, h1, h2, ruleNeTie]
  | rule3DoubleBondGeometry =>
      have h1 := earlierTie .rule1aAtomicNumber (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h2 := earlierTie .rule1bDuplicateNodeProximity (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h3 := earlierTie .rule2AtomicMass (by
        simp [SequenceRule.Before, SequenceRule.rank])
      simp [firstStrictSequenceRule?, h1, h2, h3, ruleNeTie]
  | rule4aStereogenicUnitKind =>
      have h1 := earlierTie .rule1aAtomicNumber (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h2 := earlierTie .rule1bDuplicateNodeProximity (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h3 := earlierTie .rule2AtomicMass (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h4 := earlierTie .rule3DoubleBondGeometry (by
        simp [SequenceRule.Before, SequenceRule.rank])
      simp [firstStrictSequenceRule?, h1, h2, h3, h4, ruleNeTie]
  | rule4bLikeUnlikeDescriptorPairs =>
      have h1 := earlierTie .rule1aAtomicNumber (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h2 := earlierTie .rule1bDuplicateNodeProximity (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h3 := earlierTie .rule2AtomicMass (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h4 := earlierTie .rule3DoubleBondGeometry (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h5 := earlierTie .rule4aStereogenicUnitKind (by
        simp [SequenceRule.Before, SequenceRule.rank])
      simp [firstStrictSequenceRule?, h1, h2, h3, h4, h5, ruleNeTie]
  | rule4cPseudoasymmetricDescriptor =>
      have h1 := earlierTie .rule1aAtomicNumber (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h2 := earlierTie .rule1bDuplicateNodeProximity (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h3 := earlierTie .rule2AtomicMass (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h4 := earlierTie .rule3DoubleBondGeometry (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h5 := earlierTie .rule4aStereogenicUnitKind (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h6 := earlierTie .rule4bLikeUnlikeDescriptorPairs (by
        simp [SequenceRule.Before, SequenceRule.rank])
      simp [firstStrictSequenceRule?, h1, h2, h3, h4, h5, h6, ruleNeTie]
  | rule5EnantiomorphicDescriptor =>
      have h1 := earlierTie .rule1aAtomicNumber (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h2 := earlierTie .rule1bDuplicateNodeProximity (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h3 := earlierTie .rule2AtomicMass (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h4 := earlierTie .rule3DoubleBondGeometry (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h5 := earlierTie .rule4aStereogenicUnitKind (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h6 := earlierTie .rule4bLikeUnlikeDescriptorPairs (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h7 := earlierTie .rule4cPseudoasymmetricDescriptor (by
        simp [SequenceRule.Before, SequenceRule.rank])
      simp [firstStrictSequenceRule?, h1, h2, h3, h4, h5, h6, h7, ruleNeTie]
  | rule6ReferencePromotion =>
      have h1 := earlierTie .rule1aAtomicNumber (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h2 := earlierTie .rule1bDuplicateNodeProximity (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h3 := earlierTie .rule2AtomicMass (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h4 := earlierTie .rule3DoubleBondGeometry (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h5 := earlierTie .rule4aStereogenicUnitKind (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h6 := earlierTie .rule4bLikeUnlikeDescriptorPairs (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h7 := earlierTie .rule4cPseudoasymmetricDescriptor (by
        simp [SequenceRule.Before, SequenceRule.rank])
      have h8 := earlierTie .rule5EnantiomorphicDescriptor (by
        simp [SequenceRule.Before, SequenceRule.rank])
      simp [firstStrictSequenceRule?, h1, h2, h3, h4, h5, h6, h7, h8, ruleNeTie]

theorem firstStrictSequenceRule_eq_none_iff
    (outcomeAt : SequenceRule → Ordering) :
    firstStrictSequenceRule? outcomeAt = none ↔
      ∀ rule, outcomeAt rule = Ordering.eq := by
  constructor
  · intro selectedNone
    by_contra notAllTie
    let first := Classical.choose (exists_first_strict_sequenceRule outcomeAt notAllTie)
    have firstSpec := Classical.choose_spec
      (exists_first_strict_sequenceRule outcomeAt notAllTie)
    have selectedFirst : firstStrictSequenceRule? outcomeAt = some first :=
      firstStrictSequenceRule_eq_some_of_spec outcomeAt first firstSpec.1 firstSpec.2
    rw [selectedNone] at selectedFirst
    contradiction
  · intro allTie
    simp [firstStrictSequenceRule?, allTie]

theorem firstStrictSequenceRule_eq_some_iff
    (outcomeAt : SequenceRule → Ordering) (rule : SequenceRule) :
    firstStrictSequenceRule? outcomeAt = some rule ↔
      P92OrderingStrict (outcomeAt rule) ∧
        ∀ earlier, earlier.Before rule → outcomeAt earlier = Ordering.eq := by
  constructor
  · intro selectedRule
    have notAllTie : ¬∀ candidate, outcomeAt candidate = Ordering.eq := by
      intro allTie
      have selectedNone :=
        (firstStrictSequenceRule_eq_none_iff outcomeAt).2 allTie
      rw [selectedNone] at selectedRule
      contradiction
    let first := Classical.choose (exists_first_strict_sequenceRule outcomeAt notAllTie)
    have firstSpec := Classical.choose_spec
      (exists_first_strict_sequenceRule outcomeAt notAllTie)
    have selectedFirst : firstStrictSequenceRule? outcomeAt = some first :=
      firstStrictSequenceRule_eq_some_of_spec outcomeAt first firstSpec.1 firstSpec.2
    have firstExact : first = rule := Option.some.inj (selectedFirst.symm.trans selectedRule)
    subst rule
    exact firstSpec
  · rintro ⟨strict, earlierTie⟩
    exact firstStrictSequenceRule_eq_some_of_spec outcomeAt rule strict earlierTie

def p92ProductionRuleExhaustivityObservation
    (comparison : P92LigandComparisonAuthorityContext)
    (outcomeAt : SequenceRule → Ordering) : P92RuleExhaustivityAuthorityObservation :=
  match firstStrictSequenceRule? outcomeAt with
  | none =>
      { comparison := comparison
        outcomeAt := outcomeAt
        firstDecisive? := none
        outcome := Ordering.eq }
  | some first =>
      { comparison := comparison
        outcomeAt := outcomeAt
        firstDecisive? := some first
        outcome := outcomeAt first }

theorem p92ProductionRuleExhaustivity_judged
    (source : AuthoritativeChemicalInput)
    (comparison : P92LigandComparisonAuthorityContext)
    (ready : comparison.Ready source)
    (outcomeAt : SequenceRule → Ordering) :
    p92RuleExhaustivityReference.Judges source
      (p92ProductionRuleExhaustivityObservation comparison outcomeAt) := by
  cases selected : firstStrictSequenceRule? outcomeAt with
  | none =>
      have allTie := (firstStrictSequenceRule_eq_none_iff outcomeAt).1 selected
      simp [p92RuleExhaustivityReference, p92ProductionRuleExhaustivityObservation,
        selected, ready,
        P92RuleExhaustivityJudged, allTie]
  | some rule =>
      have ruleSpec := (firstStrictSequenceRule_eq_some_iff outcomeAt rule).1 selected
      simpa [p92RuleExhaustivityReference, p92ProductionRuleExhaustivityObservation, selected,
        P92RuleExhaustivityJudged] using
        (show comparison.Ready source ∧
            P92OrderingStrict (outcomeAt rule) ∧
              outcomeAt rule = outcomeAt rule ∧
              ∀ earlier, earlier.Before rule → outcomeAt earlier = Ordering.eq from
          ⟨ready, ruleSpec.1, rfl, ruleSpec.2⟩)

/-! ## Saturated-compound Rule-1a comparison -/

def p92ProductionRule1aSaturatedCompoundsObservation
    (atomCount : Nat) (molecule : MoleculeGraph (Fin atomCount))
    (left right : Fin atomCount) : P92Rule1aSaturatedCompoundsAuthorityObservation where
  atomCount := atomCount
  molecule := molecule
  left := left
  right := right
  outcome := @compare ℚ Rat.linearOrder.toOrd
    (ExactAtomicNumber.ofNat (molecule.atomZ left)).value
    (ExactAtomicNumber.ofNat (molecule.atomZ right)).value

theorem p92ProductionRule1aSaturatedCompounds_judged
    (source : AuthoritativeChemicalInput)
    (atomCount : Nat) (molecule : MoleculeGraph (Fin atomCount))
    (left right : Fin atomCount)
    (represents : P92ClassicalConstitutionRepresents source molecule)
    (leftSaturated : P92AtomSaturated molecule left)
    (rightSaturated : P92AtomSaturated molecule right) :
    p92Rule1aSaturatedCompoundsReference.Judges source
      (p92ProductionRule1aSaturatedCompoundsObservation atomCount molecule left right) := by
  change P92ClassicalConstitutionRepresents source molecule ∧
    P92AtomSaturated molecule left ∧ P92AtomSaturated molecule right ∧
      ExactAtomicNumber.Outcome
        (ExactAtomicNumber.ofNat (molecule.atomZ left))
        (ExactAtomicNumber.ofNat (molecule.atomZ right))
        (@compare ℚ Rat.linearOrder.toOrd
          (ExactAtomicNumber.ofNat (molecule.atomZ left)).value
          (ExactAtomicNumber.ofNat (molecule.atomZ right)).value)
  refine ⟨represents, leftSaturated, rightSaturated, ?_⟩
  unfold ExactAtomicNumber.Outcome
  rfl

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92ProductionSphereExploration_judged
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.exists_first_strict_sequenceRule
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.firstStrictSequenceRule_eq_none_iff
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.firstStrictSequenceRule_eq_some_iff
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92ProductionRuleExhaustivity_judged
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p92ProductionRule1aSaturatedCompounds_judged
