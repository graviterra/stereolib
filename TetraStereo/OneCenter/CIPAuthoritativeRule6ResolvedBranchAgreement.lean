import TetraStereo.OneCenter.CIPAuthoritativeRule6ResolvedApplicability
import TetraStereo.OneCenter.CIPAuthoritativeRule6UnannotatedPerception
import TetraStereo.OneCenter.Rule6ReferenceOrbitSemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter.Rule6ReferenceBranchAgreementSemantics

open RawMolecule
open AuthoritativeCIPRule6P92Enumeration
open Rule6FourWayFamilySemantics
open Rule6ReferenceFamilySemantics

/-!
# Parity-free P-92 Rule-6 branch agreement

Execution totality does not make a promoted Rule-6 ranking strict and does not make rankings made
from different reference choices agree in handedness.  Those are chemical facts about the
resolved descriptor-bearing branches.  This file isolates exactly that irreducible remainder.

The predicates below mention neither a returned descriptor nor success of an executable family
checker.  They say directly that the independently enumerated reference rankings exist, are
strict where P-92 requires strictness, and have one common permutation parity.  The main theorem
proves that this parity-free statement is exactly the existing resolved stereogenicity predicate.
-/

/-- For either written tetrahedral sense, descriptor projection is injective in permutation
parity. -/
theorem rule6DescriptorOfParity_injective (parity : TetrahedralInputParity) :
    Function.Injective (RawMolecule.descriptorOfParity parity) := by
  intro first second equal
  cases parity <;> cases first <;> cases second <;>
    simp_all [RawMolecule.descriptorOfParity]

/-- A nonempty P-92 reference family has branch agreement when one strict anchor ranking exists
and every enumerated reference has a strict ranking of the same permutation parity.

The anchor is existential rather than the head of the executable list, so the proposition does
not privilege an implementation traversal order. -/
def Rule6ReferenceFamilyBranchAgreement (backend : ProductionRule6RankingBackend)
    (references : List Nat) : Prop :=
  ∃ anchorReference anchorRanking,
    anchorReference ∈ references ∧
      backend anchorReference = some anchorRanking ∧
      anchorRanking.unique = true ∧
      ∀ reference, reference ∈ references →
        ∃ ranking,
          backend reference = some ranking ∧
            ranking.unique = true ∧
            RawMolecule.permutationIsEven ranking.positions =
              RawMolecule.permutationIsEven anchorRanking.positions

/-- Exact descriptor elimination for an independently enumerated P-92 reference family.
Branch agreement is independent of written parity, and is equivalent to existence of a common
descriptor for either chosen parity. -/
theorem rule6ReferenceFamilyBranchAgreement_iff_exists_commonDescriptor
    (backend : ProductionRule6RankingBackend) (references : List Nat)
    (parity : TetrahedralInputParity) :
    Rule6ReferenceFamilyBranchAgreement backend references ↔
      ∃ descriptor, CommonRule6Descriptor backend parity references descriptor := by
  constructor
  · rintro ⟨anchorReference, anchorRanking, anchorMember, anchorEq, anchorUnique, common⟩
    let descriptor := RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven anchorRanking.positions)
    refine ⟨descriptor, ?_, ?_⟩
    · intro referencesEq
      simp [referencesEq] at anchorMember
    · intro reference member
      rcases common reference member with ⟨ranking, rankingEq, unique, parityEq⟩
      exact ⟨ranking, rankingEq, unique, by
        exact congrArg (RawMolecule.descriptorOfParity parity) parityEq⟩
  · rintro ⟨descriptor, referencesNonempty, common⟩
    rcases List.exists_mem_of_ne_nil references referencesNonempty with
      ⟨anchorReference, anchorMember⟩
    rcases common anchorReference anchorMember with
      ⟨anchorRanking, anchorEq, anchorUnique, anchorDescriptor⟩
    refine ⟨anchorReference, anchorRanking, anchorMember, anchorEq, anchorUnique, ?_⟩
    intro reference member
    rcases common reference member with
      ⟨ranking, rankingEq, unique, rankingDescriptor⟩
    refine ⟨ranking, rankingEq, unique, ?_⟩
    apply rule6DescriptorOfParity_injective parity
    exact rankingDescriptor.trans anchorDescriptor.symm

/-- Two completed strict reference rankings disagree at the parity-free semantic level. -/
def HasRule6ReferenceParityConflict (backend : ProductionRule6RankingBackend)
    (references : List Nat) : Prop :=
  ∃ firstReference, firstReference ∈ references ∧
    ∃ secondReference, secondReference ∈ references ∧
      ∃ firstRanking secondRanking,
        backend firstReference = some firstRanking ∧
        backend secondReference = some secondRanking ∧
        firstRanking.unique = true ∧ secondRanking.unique = true ∧
        RawMolecule.permutationIsEven firstRanking.positions ≠
          RawMolecule.permutationIsEven secondRanking.positions

/-- Descriptor conflict is exactly parity conflict, for either arbitrary written sense. -/
theorem hasRule6ReferenceDescriptorConflict_iff_parityConflict
    (backend : ProductionRule6RankingBackend) (references : List Nat)
    (parity : TetrahedralInputParity) :
    HasRule6ReferenceDescriptorConflict backend parity references ↔
      HasRule6ReferenceParityConflict backend references := by
  constructor
  · rintro ⟨firstReference, firstMember, secondReference, secondMember,
      firstRanking, secondRanking, firstEq, secondEq, firstUnique, secondUnique,
      descriptorsDifferent⟩
    refine ⟨firstReference, firstMember, secondReference, secondMember,
      firstRanking, secondRanking, firstEq, secondEq, firstUnique, secondUnique, ?_⟩
    intro parityEqual
    exact descriptorsDifferent
      (congrArg (RawMolecule.descriptorOfParity parity) parityEqual)
  · rintro ⟨firstReference, firstMember, secondReference, secondMember,
      firstRanking, secondRanking, firstEq, secondEq, firstUnique, secondUnique,
      parityDifferent⟩
    refine ⟨firstReference, firstMember, secondReference, secondMember,
      firstRanking, secondRanking, firstEq, secondEq, firstUnique, secondUnique, ?_⟩
    intro descriptorsEqual
    exact parityDifferent (rule6DescriptorOfParity_injective parity descriptorsEqual)

/-- Under total per-reference execution, branch agreement fails for exactly the two genuinely
chemical reasons left after totality: a non-strict promoted ranking or a cross-reference
handedness conflict. -/
theorem rule6ReferenceFamilyBranchAgreement_iff_no_semantic_failure
    (backend : ProductionRule6RankingBackend) (references : List Nat)
    (referencesNonempty : references ≠ [])
    (rankingTotal : ∀ reference, reference ∈ references →
      ∃ ranking, backend reference = some ranking) :
    Rule6ReferenceFamilyBranchAgreement backend references ↔
      ¬ (HasNonStrictRule6Reference backend references ∨
        HasRule6ReferenceParityConflict backend references) := by
  have noCommonIffFailure :=
    no_commonRule6Descriptor_iff_nonStrict_or_descriptorConflict
      backend .clockwise references referencesNonempty rankingTotal
  have failureIff :
      (HasNonStrictRule6Reference backend references ∨
          HasRule6ReferenceDescriptorConflict backend .clockwise references) ↔
        (HasNonStrictRule6Reference backend references ∨
          HasRule6ReferenceParityConflict backend references) :=
    or_congr Iff.rfl
      (hasRule6ReferenceDescriptorConflict_iff_parityConflict
        backend references .clockwise)
  constructor
  · intro agreement semanticFailure
    have common :=
      (rule6ReferenceFamilyBranchAgreement_iff_exists_commonDescriptor
        backend references .clockwise).mp agreement
    exact (noCommonIffFailure.mpr (failureIff.mpr semanticFailure)) common
  · intro noFailure
    apply (rule6ReferenceFamilyBranchAgreement_iff_exists_commonDescriptor
      backend references .clockwise).mpr
    by_contra noCommon
    exact noFailure (failureIff.mp (noCommonIffFailure.mp noCommon))

/-- Relational, traversal-free statement of agreement over P-92's exact two-group rank-one
reference class. -/
def Rule6TwoGroupEnumeratedBranchAgreement (backend : ProductionRule6RankingBackend)
    (sorted : List Nat) (adjacent : List (Option Ordering)) : Prop :=
  ∃ anchorReference anchorRanking,
    TwoGroupEnumeratedReferencePosition sorted adjacent anchorReference ∧
      backend anchorReference = some anchorRanking ∧
      anchorRanking.unique = true ∧
      ∀ reference, TwoGroupEnumeratedReferencePosition sorted adjacent reference →
        ∃ ranking,
          backend reference = some ranking ∧
            ranking.unique = true ∧
            RawMolecule.permutationIsEven ranking.positions =
              RawMolecule.permutationIsEven anchorRanking.positions

/-- The production list constructor enumerates precisely the traversal-free two-group relation,
so the corresponding branch-agreement propositions are equivalent. -/
theorem rule6ReferenceFamilyBranchAgreement_iff_twoGroupEnumerated
    (backend : ProductionRule6RankingBackend)
    (sorted : List Nat) (adjacent : List (Option Ordering)) :
    Rule6ReferenceFamilyBranchAgreement backend
        (rule6EquivalentReferencePositions sorted adjacent) ↔
      Rule6TwoGroupEnumeratedBranchAgreement backend sorted adjacent := by
  unfold Rule6ReferenceFamilyBranchAgreement Rule6TwoGroupEnumeratedBranchAgreement
  simp_rw [mem_rule6EquivalentReferencePositions_iff_enumerated]

/-- The prescribed three-group singleton family agrees exactly when its one promoted ranking
exists and is strict. -/
theorem rule6SingletonReferenceFamilyBranchAgreement_iff
    (backend : ProductionRule6RankingBackend) (reference : Nat) :
    Rule6ReferenceFamilyBranchAgreement backend [reference] ↔
      ∃ ranking, backend reference = some ranking ∧ ranking.unique = true := by
  constructor
  · rintro ⟨anchorReference, anchorRanking, anchorMember,
      anchorEq, anchorUnique, _common⟩
    have anchorIdentity : anchorReference = reference := by simpa using anchorMember
    subst anchorReference
    exact ⟨anchorRanking, anchorEq, anchorUnique⟩
  · rintro ⟨ranking, rankingEq, unique⟩
    refine ⟨reference, ranking, by simp, rankingEq, unique, ?_⟩
    intro otherReference otherMember
    have otherIdentity : otherReference = reference := by simpa using otherMember
    subst otherReference
    exact ⟨ranking, rankingEq, unique, rfl⟩

/-- Parity-free form of the three dependent-four-way carrier equations. -/
def Rule6FourWayCarrierBranchAgreement (first second : Rule6TrackedRanking) : Prop :=
  first.positions ≠ second.positions ∧
    RawMolecule.permutationIsEven first.positions =
      RawMolecule.permutationIsEven second.positions ∧
    first.unique = second.unique

/-- The three parity-free semantic reasons for refusing two completed dependent four-way
rankings. -/
def HasRule6FourWayCarrierSemanticFailure
    (first second : Rule6TrackedRanking) : Prop :=
  first.positions = second.positions ∨
    RawMolecule.permutationIsEven first.positions ≠
      RawMolecule.permutationIsEven second.positions ∨
    first.unique ≠ second.unique

/-- The descriptor-projected four-way failure relation is exactly its parity-free form for either
written tetrahedral sense. -/
theorem hasFourWayCarrierFailure_iff_semanticFailure
    (parity : TetrahedralInputParity) (first second : Rule6TrackedRanking) :
    HasFourWayCarrierFailure parity first second ↔
      HasRule6FourWayCarrierSemanticFailure first second := by
  constructor
  · rintro (samePositions | descriptorsDifferent | uniqueDifferent)
    · exact Or.inl samePositions
    · right
      left
      intro parityEqual
      exact descriptorsDifferent
        (congrArg (RawMolecule.descriptorOfParity parity) parityEqual)
    · exact Or.inr (Or.inr uniqueDifferent)
  · rintro (samePositions | parityDifferent | uniqueDifferent)
    · exact Or.inl samePositions
    · right
      left
      intro descriptorsEqual
      exact parityDifferent (rule6DescriptorOfParity_injective parity descriptorsEqual)
    · exact Or.inr (Or.inr uniqueDifferent)

/-- The descriptor-valued coherence equation is exactly parity-free carrier agreement for either
written sense. -/
theorem fourWayCarrierCoherent_iff_branchAgreement
    (parity : TetrahedralInputParity) (first second : Rule6TrackedRanking) :
    FourWayCarrierCoherent parity first second ↔
      Rule6FourWayCarrierBranchAgreement first second := by
  constructor
  · rintro ⟨positionsDifferent, descriptorsEqual, uniqueEqual⟩
    exact ⟨positionsDifferent,
      rule6DescriptorOfParity_injective parity descriptorsEqual, uniqueEqual⟩
  · rintro ⟨positionsDifferent, parityEqual, uniqueEqual⟩
    exact ⟨positionsDifferent,
      congrArg (RawMolecule.descriptorOfParity parity) parityEqual, uniqueEqual⟩

/-- Descriptor-free agreement of the two dependent rankings prescribed by P-92's four-way
carrier. -/
def AuthoritativeRule6FourWayBranchAgreement (backend : ProductionRule6RankingBackend)
    (sorted : List Nat) : Prop :=
  ∃ firstReference first second,
    sorted[0]? = some firstReference ∧
      backend firstReference = some first ∧
      backend (first.positions[1]?.getD 0) = some second ∧
      Rule6FourWayCarrierBranchAgreement first second

/-- A completed dependent four-way carrier has one of the three parity-free semantic failure
witnesses. -/
def AuthoritativeRule6FourWaySemanticFailure (backend : ProductionRule6RankingBackend)
    (sorted : List Nat) : Prop :=
  ∃ firstReference first second,
    sorted[0]? = some firstReference ∧
      backend firstReference = some first ∧
      backend (first.positions[1]?.getD 0) = some second ∧
      HasRule6FourWayCarrierSemanticFailure first second

/-- Exact descriptor elimination for the dependent four-way carrier. -/
theorem authoritativeRule6FourWayBranchAgreement_iff_exists_descriptor
    (backend : ProductionRule6RankingBackend) (sorted : List Nat)
    (parity : TetrahedralInputParity) :
    AuthoritativeRule6FourWayBranchAgreement backend sorted ↔
      ∃ descriptor,
        AuthoritativeCIPRule6P92Enumeration.AuthoritativeFourWayDescriptorJudgment
          backend parity sorted descriptor := by
  constructor
  · rintro ⟨firstReference, first, second, firstReferenceEq,
      firstEq, secondEq, agreement⟩
    let descriptor := if second.unique then
        RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven second.positions)
      else
        RS.swap (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven second.positions))
    refine ⟨descriptor, firstReference, first, second,
      firstReferenceEq, firstEq, secondEq, ?_, rfl⟩
    exact (fourWayCarrierCoherent_iff_branchAgreement parity first second).mpr agreement
  · rintro ⟨_descriptor, firstReference, first, second, firstReferenceEq,
      firstEq, secondEq, coherent, _descriptorEq⟩
    exact ⟨firstReference, first, second, firstReferenceEq, firstEq, secondEq,
      (fourWayCarrierCoherent_iff_branchAgreement parity first second).mp coherent⟩

/-- Once the first position and all promoted rankings are operationally available, four-way
descriptor refusal is exactly an explicit parity-free carrier failure. -/
theorem authoritativeRule6FourWayDescriptor?_eq_none_iff_semanticFailure
    (backend : ProductionRule6RankingBackend) (sorted : List Nat)
    (parity : TetrahedralInputParity)
    (firstPresent : ∃ firstReference, sorted[0]? = some firstReference)
    (rankingTotal : ∀ reference, ∃ ranking, backend reference = some ranking) :
    authoritativeOccurrenceRule6FourWayDescriptor? backend parity sorted = none ↔
      AuthoritativeRule6FourWaySemanticFailure backend sorted := by
  rcases
      authoritativeOccurrenceRule6FourWay_failureClassification_exists
        backend parity sorted firstPresent rankingTotal with
    ⟨firstReference, first, second, firstReferenceEq, firstEq, secondEq, classified⟩
  constructor
  · intro descriptorNone
    exact ⟨firstReference, first, second, firstReferenceEq, firstEq, secondEq,
      (hasFourWayCarrierFailure_iff_semanticFailure parity first second).mp
        (classified.mp descriptorNone)⟩
  · rintro ⟨specifiedReference, specifiedFirst, specifiedSecond,
      specifiedReferenceEq, specifiedFirstEq, specifiedSecondEq, failure⟩
    have referenceIdentity : specifiedReference = firstReference :=
      Option.some.inj (specifiedReferenceEq.symm.trans firstReferenceEq)
    subst specifiedReference
    have firstIdentity : specifiedFirst = first :=
      Option.some.inj (specifiedFirstEq.symm.trans firstEq)
    subst specifiedFirst
    have secondIdentity : specifiedSecond = second :=
      Option.some.inj (specifiedSecondEq.symm.trans secondEq)
    subst specifiedSecond
    exact classified.mpr
      ((hasFourWayCarrierFailure_iff_semanticFailure parity first second).mpr failure)

/-- Under total execution of a nonempty reference family, descriptor refusal is exactly
non-strictness or parity conflict, with no executable-output premise. -/
theorem rule6FamilyDescriptorWithBackend?_eq_none_iff_semanticFailure
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (references : List Nat)
    (referencesNonempty : references ≠ [])
    (rankingTotal : ∀ reference, reference ∈ references →
      ∃ ranking, backend reference = some ranking) :
    rule6FamilyDescriptorWithBackend? backend parity references = none ↔
      HasNonStrictRule6Reference backend references ∨
        HasRule6ReferenceParityConflict backend references :=
  (rule6FamilyDescriptorWithBackend?_eq_none_iff_failureWitness
      backend parity references referencesNonempty rankingTotal).trans
    (or_congr Iff.rfl
      (hasRule6ReferenceDescriptorConflict_iff_parityConflict
        backend references parity))

/-- A singleton reference family cannot have a cross-reference parity conflict. -/
theorem not_hasRule6ReferenceParityConflict_singleton
    (backend : ProductionRule6RankingBackend) (reference : Nat) :
    ¬ HasRule6ReferenceParityConflict backend [reference] := by
  rintro ⟨firstReference, firstMember, secondReference, secondMember,
    firstRanking, secondRanking, firstEq, secondEq, _firstUnique, _secondUnique,
    parityDifferent⟩
  have firstIdentity : firstReference = reference := by simpa using firstMember
  have secondIdentity : secondReference = reference := by simpa using secondMember
  subst firstReference
  subst secondReference
  have rankingIdentity : firstRanking = secondRanking :=
    Option.some.inj (firstEq.symm.trans secondEq)
  subst secondRanking
  exact parityDifferent rfl

/-- With total execution of its prescribed singleton, the three-group descriptor refuses exactly
when that one promoted ranking is non-strict. -/
theorem authoritativeOccurrenceRule6ThreeGroupDescriptor?_eq_none_iff_nonStrict
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands sorted : List Nat)
    (parity : TetrahedralInputParity)
    (rankingTotal : ∀ reference,
      ∃ ranking,
        authoritativeOccurrenceRule6PositionRankingBackend
          mol state fuel roots ligands reference = some ranking) :
    authoritativeOccurrenceRule6ThreeGroupDescriptor?
        mol state fuel roots ligands sorted parity = none ↔
      HasNonStrictRule6Reference
        (authoritativeOccurrenceRule6PositionRankingBackend
          mol state fuel roots ligands)
        (rule6ThreeGroupReferencePositions sorted) := by
  let backend :=
    authoritativeOccurrenceRule6PositionRankingBackend mol state fuel roots ligands
  let references := rule6ThreeGroupReferencePositions sorted
  have referencesEq : references = [sorted[1]?.getD 0] := rfl
  have referencesNonempty : references ≠ [] := by simp [referencesEq]
  have familyTotal : ∀ reference, reference ∈ references →
      ∃ ranking, backend reference = some ranking := by
    intro reference _member
    exact rankingTotal reference
  have classified := rule6FamilyDescriptorWithBackend?_eq_none_iff_semanticFailure
    backend parity references referencesNonempty familyTotal
  have projection :
      authoritativeOccurrenceRule6ThreeGroupDescriptor?
          mol state fuel roots ligands sorted parity = none ↔
        rule6FamilyDescriptorWithBackend?
          backend parity references = none := by
    cases familyEq : rule6FamilyDescriptorWithBackend?
        backend parity references <;>
      simp [authoritativeOccurrenceRule6ThreeGroupDescriptor?,
        authoritativeOccurrenceRule6PositionFamilyDescriptor?,
        backend, references, familyEq]
  rw [projection, classified]
  have noConflict : ¬ HasRule6ReferenceParityConflict backend references := by
    simpa [referencesEq] using
      not_hasRule6ReferenceParityConflict_singleton backend (sorted[1]?.getD 0)
  tauto

end TetraStereo.OneCenter.Rule6ReferenceBranchAgreementSemantics

namespace TetraStereo.OneCenter.AuthoritativeCIPRule6Scheduler

open RawMolecule
open DeclarativeCIP
open DeclarativeCIP.ProductionOccurrenceRules456
open AuthoritativeCIPRule6P92Enumeration
open Rule6ReferenceBranchAgreementSemantics

/-- The minimal independent P-92 applicability fact remaining after the initial Rules-1a--5
partition has been resolved.

* one group uses the two dependent promoted rankings and the three parity-free carrier equations;
* two groups use every position in the exact rank-one equivalence-class enumeration;
* three groups use the prescribed rank-one singleton, after the local-reference gate.

No descriptor, executable family result, or public output occurs in this proposition. -/
def AuthoritativeRule6ResolvedBranchAgreement
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List Nat) (adjacent : List (Option Ordering)) : Prop :=
  let ligands := mol.ligandsWithLonePair node.atom
  let backend := authoritativeOccurrenceRule6PositionRankingBackend
    mol state fuel roots ligands
  let groupCount := rule6GroupCount adjacent
  (groupCount = 1 ∧
      AuthoritativeRule6FourWayBranchAgreement backend sorted) ∨
    (groupCount = 2 ∧
      Rule6ReferenceFamilyBranchAgreement backend
        (rule6EquivalentReferencePositions sorted adjacent)) ∨
    (groupCount = 3 ∧
      ∃ referenceRoot,
        roots[sorted[1]?.getD 0]? = some referenceRoot ∧
        adjacent[1]?.getD none = some Ordering.eq ∧
        occurrenceBranchHasLocalReference (mol := mol) state fuel [referenceRoot] = true ∧
        Rule6ReferenceFamilyBranchAgreement backend
          (rule6ThreeGroupReferencePositions sorted))

/-- Exact characterization of resolved source Rule-6 stereogenicity by independent, parity-free
P-92 enumeration and branch-agreement semantics.  This removes the existential descriptor from
the chemical premise; conversely, every such agreement determines the descriptor for either
arbitrary written sense. -/
theorem authoritativeRule6ResolvedStereogenic_iff_branchAgreement
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List Nat) (adjacent : List (Option Ordering)) :
    AuthoritativeRule6ResolvedStereogenic mol state fuel node roots sorted adjacent ↔
      AuthoritativeRule6ResolvedBranchAgreement
        mol state fuel node roots sorted adjacent := by
  let ligands := mol.ligandsWithLonePair node.atom
  let backend := authoritativeOccurrenceRule6PositionRankingBackend
    mol state fuel roots ligands
  let groupCount := rule6GroupCount adjacent
  change
    (∃ descriptor,
      (groupCount = 1 ∧
          AuthoritativeFourWayDescriptorJudgment
            backend .clockwise sorted descriptor) ∨
        (groupCount = 2 ∧
          Rule6ReferenceFamilySemantics.CommonRule6Descriptor backend .clockwise
            (rule6EquivalentReferencePositions sorted adjacent) descriptor) ∨
        (groupCount = 3 ∧
          ∃ referenceRoot,
            roots[sorted[1]?.getD 0]? = some referenceRoot ∧
            adjacent[1]?.getD none = some Ordering.eq ∧
            occurrenceBranchHasLocalReference (mol := mol) state fuel [referenceRoot] = true ∧
            Rule6ReferenceFamilySemantics.CommonRule6Descriptor backend .clockwise
              (rule6ThreeGroupReferencePositions sorted) (RS.swap descriptor))) ↔
      (groupCount = 1 ∧
          AuthoritativeRule6FourWayBranchAgreement backend sorted) ∨
        (groupCount = 2 ∧
          Rule6ReferenceFamilyBranchAgreement backend
            (rule6EquivalentReferencePositions sorted adjacent)) ∨
        (groupCount = 3 ∧
          ∃ referenceRoot,
            roots[sorted[1]?.getD 0]? = some referenceRoot ∧
            adjacent[1]?.getD none = some Ordering.eq ∧
            occurrenceBranchHasLocalReference (mol := mol) state fuel [referenceRoot] = true ∧
            Rule6ReferenceFamilyBranchAgreement backend
              (rule6ThreeGroupReferencePositions sorted))
  constructor
  · rintro ⟨descriptor, fourWay | twoOrThree⟩
    · exact Or.inl ⟨fourWay.1,
        (authoritativeRule6FourWayBranchAgreement_iff_exists_descriptor
          backend sorted .clockwise).mpr ⟨descriptor, fourWay.2⟩⟩
    · rcases twoOrThree with twoGroup | threeGroup
      · exact Or.inr (Or.inl ⟨twoGroup.1,
          (rule6ReferenceFamilyBranchAgreement_iff_exists_commonDescriptor
            backend (rule6EquivalentReferencePositions sorted adjacent) .clockwise).mpr
              ⟨descriptor, twoGroup.2⟩⟩)
      · rcases threeGroup with ⟨groupThree, referenceRoot, referenceRootEq,
          middleTie, localReference, common⟩
        exact Or.inr (Or.inr ⟨groupThree, referenceRoot, referenceRootEq,
          middleTie, localReference,
          (rule6ReferenceFamilyBranchAgreement_iff_exists_commonDescriptor
            backend (rule6ThreeGroupReferencePositions sorted) .clockwise).mpr
              ⟨RS.swap descriptor, common⟩⟩)
  · rintro (fourWay | twoOrThree)
    · rcases
          (authoritativeRule6FourWayBranchAgreement_iff_exists_descriptor
            backend sorted .clockwise).mp fourWay.2 with
          ⟨descriptor, judgment⟩
      exact ⟨descriptor, Or.inl ⟨fourWay.1, judgment⟩⟩
    · rcases twoOrThree with twoGroup | threeGroup
      · rcases
            (rule6ReferenceFamilyBranchAgreement_iff_exists_commonDescriptor
              backend (rule6EquivalentReferencePositions sorted adjacent) .clockwise).mp
                twoGroup.2 with
            ⟨descriptor, common⟩
        exact ⟨descriptor, Or.inr (Or.inl ⟨twoGroup.1, common⟩)⟩
      · rcases threeGroup with ⟨groupThree, referenceRoot, referenceRootEq,
          middleTie, localReference, agreement⟩
        rcases
            (rule6ReferenceFamilyBranchAgreement_iff_exists_commonDescriptor
              backend (rule6ThreeGroupReferencePositions sorted) .clockwise).mp agreement with
          ⟨commonDescriptor, common⟩
        refine ⟨RS.swap commonDescriptor, Or.inr (Or.inr ⟨groupThree,
          referenceRoot, referenceRootEq, middleTie, localReference, ?_⟩)⟩
        simpa using common

/-! ## Exact semantic classification of unresolved execution -/

/-- Operational availability needed to separate computation gaps from chemical Rule-6 refusal.

The first promoted position is needed by the one-group carrier; the rank-one root is needed by
the three-group local-reference gate; total promoted ranking is shared by every descriptor-bearing
branch.  None of these clauses mentions a descriptor or a result of the resolved adapter. -/
def AuthoritativeResolvedRule6OperationalDomain
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List Nat) : Prop :=
  let ligands := mol.ligandsWithLonePair node.atom
  let backend := authoritativeOccurrenceRule6PositionRankingBackend
    mol state fuel roots ligands
  (∃ firstReference, sorted[0]? = some firstReference) ∧
    (∃ referenceRoot, roots[sorted[1]?.getD 0]? = some referenceRoot) ∧
    ∀ reference, ∃ ranking, backend reference = some ranking

/-- The semantic failure of a resolved P-92 branch, after its primitive inputs and promoted
rankings are operationally available.

The alternatives are exhaustive and descriptor-free:

* a one-group dependent carrier violates position distinctness, parity agreement, or uniqueness
  agreement;
* a two-group reference class contains a non-strict ranking or a parity conflict;
* an admitted three-group local-reference branch has a non-strict singleton ranking.

An absent middle tie or local reference is a resolved nonstereogenic answer, not an unresolved
ranking. -/
def AuthoritativeResolvedRule6SemanticFailure
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List Nat) (adjacent : List (Option Ordering)) : Prop :=
  let ligands := mol.ligandsWithLonePair node.atom
  let backend := authoritativeOccurrenceRule6PositionRankingBackend
    mol state fuel roots ligands
  let groupCount := rule6GroupCount adjacent
  (groupCount = 1 ∧
      AuthoritativeRule6FourWaySemanticFailure backend sorted) ∨
    (groupCount = 2 ∧
      (Rule6ReferenceFamilySemantics.HasNonStrictRule6Reference backend
          (rule6EquivalentReferencePositions sorted adjacent) ∨
        HasRule6ReferenceParityConflict backend
          (rule6EquivalentReferencePositions sorted adjacent))) ∨
    (groupCount = 3 ∧
      ∃ referenceRoot,
        roots[sorted[1]?.getD 0]? = some referenceRoot ∧
        adjacent[1]?.getD none = some Ordering.eq ∧
        occurrenceBranchHasLocalReference (mol := mol) state fuel [referenceRoot] = true ∧
        Rule6ReferenceFamilySemantics.HasNonStrictRule6Reference backend
          (rule6ThreeGroupReferencePositions sorted))

/-- On the explicit operational domain, resolved execution is absent exactly for one of the
parity-free chemical failures above. -/
theorem authoritativeResolvedRule6Stereogenicity?_eq_none_iff_semanticFailure
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List Nat) (adjacent : List (Option Ordering))
    (operational : AuthoritativeResolvedRule6OperationalDomain
      mol state fuel node roots sorted) :
    authoritativeResolvedRule6Stereogenicity?
        mol state fuel node roots sorted adjacent = none ↔
      AuthoritativeResolvedRule6SemanticFailure
        mol state fuel node roots sorted adjacent := by
  let ligands := mol.ligandsWithLonePair node.atom
  let backend := authoritativeOccurrenceRule6PositionRankingBackend
    mol state fuel roots ligands
  let groupCount := rule6GroupCount adjacent
  rcases operational with ⟨firstPresent, rootPresent, rankingTotal⟩
  change authoritativeResolvedRule6Stereogenicity?
      mol state fuel node roots sorted adjacent = none ↔
    (groupCount = 1 ∧ AuthoritativeRule6FourWaySemanticFailure backend sorted) ∨
      (groupCount = 2 ∧
        (Rule6ReferenceFamilySemantics.HasNonStrictRule6Reference backend
            (rule6EquivalentReferencePositions sorted adjacent) ∨
          HasRule6ReferenceParityConflict backend
            (rule6EquivalentReferencePositions sorted adjacent))) ∨
      (groupCount = 3 ∧
        ∃ referenceRoot,
          roots[sorted[1]?.getD 0]? = some referenceRoot ∧
          adjacent[1]?.getD none = some Ordering.eq ∧
          occurrenceBranchHasLocalReference (mol := mol) state fuel [referenceRoot] = true ∧
          Rule6ReferenceFamilySemantics.HasNonStrictRule6Reference backend
            (rule6ThreeGroupReferencePositions sorted))
  have fourWay := authoritativeRule6FourWayDescriptor?_eq_none_iff_semanticFailure
    backend sorted .clockwise firstPresent rankingTotal
  have twoGroup := rule6FamilyDescriptorWithBackend?_eq_none_iff_semanticFailure
    backend .clockwise (rule6EquivalentReferencePositions sorted adjacent)
      (rule6EquivalentReferencePositions_ne_nil sorted adjacent)
      (fun reference _member => rankingTotal reference)
  have threeGroup := authoritativeOccurrenceRule6ThreeGroupDescriptor?_eq_none_iff_nonStrict
    mol state fuel roots ligands sorted .clockwise rankingTotal
  by_cases groupOne : groupCount = 1
  · have groupTwo : groupCount ≠ 2 := by omega
    have groupThree : groupCount ≠ 3 := by omega
    simpa [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
      groupOne, groupTwo, groupThree] using fourWay
  · by_cases groupTwo : groupCount = 2
    · have groupThree : groupCount ≠ 3 := by omega
      simpa [authoritativeResolvedRule6Stereogenicity?,
        authoritativeOccurrenceRule6TwoGroupDescriptor?,
        authoritativeOccurrenceRule6PositionFamilyDescriptor?,
        ligands, backend, groupCount, groupOne, groupTwo, groupThree] using twoGroup
    · by_cases groupThree : groupCount = 3
      · rcases rootPresent with ⟨referenceRoot, referenceRootEq⟩
        by_cases middleTie : adjacent[1]?.getD none = some Ordering.eq
        · by_cases localReference : occurrenceBranchHasLocalReference
              (mol := mol) state fuel [referenceRoot] = true
          · simpa [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
              groupOne, groupTwo, groupThree, referenceRootEq,
              middleTie, localReference] using threeGroup
          · simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
              groupThree, referenceRootEq,
              middleTie, localReference]
        · simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
            groupThree, referenceRootEq, middleTie]
      · simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
          groupOne, groupTwo, groupThree]

/-- The public resolved unannotated adapter reports `rankingUnresolved` exactly for the same
parity-free semantic failure. -/
theorem authoritativeResolvedRule6UnannotatedOutcome?_eq_rankingUnresolved_iff_semanticFailure
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List Nat) (adjacent : List (Option Ordering))
    (operational : AuthoritativeResolvedRule6OperationalDomain
      mol state fuel node roots sorted) :
    authoritativeResolvedRule6UnannotatedOutcome?
        mol state fuel node roots sorted adjacent =
          some (.refused .rankingUnresolved) ↔
      AuthoritativeResolvedRule6SemanticFailure
        mol state fuel node roots sorted adjacent := by
  cases computed : authoritativeResolvedRule6Stereogenicity?
      mol state fuel node roots sorted adjacent with
  | none =>
      simp [authoritativeResolvedRule6UnannotatedOutcome?, computed,
        (authoritativeResolvedRule6Stereogenicity?_eq_none_iff_semanticFailure
          mol state fuel node roots sorted adjacent operational).mp computed]
  | some decision =>
      have noFailure : ¬ AuthoritativeResolvedRule6SemanticFailure
          mol state fuel node roots sorted adjacent := by
        intro failure
        have absent :=
          (authoritativeResolvedRule6Stereogenicity?_eq_none_iff_semanticFailure
            mol state fuel node roots sorted adjacent operational).mpr failure
        rw [computed] at absent
        contradiction
      cases decision <;>
        simp [authoritativeResolvedRule6UnannotatedOutcome?, computed, noFailure]

/-! ## Source-level refusal classification -/

/-- Every fully constructed source Rule-6 frame satisfies the resolved operational domain.

This is the only extra premise needed for exact source-level semantic refusal: earlier failures
are classified directly, while a frame that reaches promoted Rule 6 must supply the positions,
rank-one cursor, and promoted rankings used by the resolved classification. -/
def AuthoritativeSourceRule6ResolvedOperationalDomain
    (mol : RawMolecule) (fuel center : Nat) : Prop :=
  let node := canonicalCenterRoot center
  let roots := authoritativeSourceRule6LigandCursors mol center
  ∀ aux sorted adjacent,
    buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = some aux →
    sortAuthoritativeRule6InitialPositions?
        mol aux fuel roots (List.range 4) = some sorted →
    compareAuthoritativeRule6InitialAdjacent?
        mol aux fuel roots sorted = some adjacent →
    AuthoritativeResolvedRule6OperationalDomain
      mol aux fuel node roots sorted

/-- Primitive occurrence-state construction failed for a four-coordinate source center. -/
def AuthoritativeSourceRule6ConstructionFailure
    (mol : RawMolecule) (fuel center : Nat) : Prop :=
  (mol.ligandsWithLonePair center).length = 4 ∧
    buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = none

/-- Rules-1a--5 could not sort the four source ligand positions. -/
def AuthoritativeSourceRule6InitialSortFailure
    (mol : RawMolecule) (fuel center : Nat) : Prop :=
  let ligands := mol.ligandsWithLonePair center
  let roots := authoritativeSourceRule6LigandCursors mol center
  ∃ aux,
    ligands.length = 4 ∧
    buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = some aux ∧
    sortAuthoritativeRule6InitialPositions?
      mol aux fuel roots (List.range 4) = none

/-- Adjacent Rules-1a--5 comparisons could not be constructed after sorting. -/
def AuthoritativeSourceRule6AdjacentComparisonFailure
    (mol : RawMolecule) (fuel center : Nat) : Prop :=
  let ligands := mol.ligandsWithLonePair center
  let roots := authoritativeSourceRule6LigandCursors mol center
  ∃ aux sorted,
    ligands.length = 4 ∧
    buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = some aux ∧
    sortAuthoritativeRule6InitialPositions?
      mol aux fuel roots (List.range 4) = some sorted ∧
    compareAuthoritativeRule6InitialAdjacent?
      mol aux fuel roots sorted = none

/-- The returned initial ordering contains a descending adjacent pair and therefore does not
constitute the canonical resolved partition expected by P-92. -/
def AuthoritativeSourceRule6NoncanonicalInitialOrder
    (mol : RawMolecule) (fuel center : Nat) : Prop :=
  let ligands := mol.ligandsWithLonePair center
  let roots := authoritativeSourceRule6LigandCursors mol center
  ∃ aux sorted adjacent,
    ligands.length = 4 ∧
    buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = some aux ∧
    sortAuthoritativeRule6InitialPositions?
      mol aux fuel roots (List.range 4) = some sorted ∧
    compareAuthoritativeRule6InitialAdjacent?
      mol aux fuel roots sorted = some adjacent ∧
    some Ordering.lt ∈ adjacent

/-- Constitutional parity at the source center could not be decided. -/
def AuthoritativeSourceRule6TopologyFailure
    (mol : RawMolecule) (fuel center : Nat) : Prop :=
  let ligands := mol.ligandsWithLonePair center
  let roots := authoritativeSourceRule6LigandCursors mol center
  ∃ aux sorted adjacent,
    ligands.length = 4 ∧
    buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = some aux ∧
    sortAuthoritativeRule6InitialPositions?
      mol aux fuel roots (List.range 4) = some sorted ∧
    compareAuthoritativeRule6InitialAdjacent?
      mol aux fuel roots sorted = some adjacent ∧
    some Ordering.lt ∉ adjacent ∧
    hasOddConstitutionAutomorphismAtCenter mol center ligands
      (fun left right =>
        (compareAuthoritativeRule6InitialPositions?
          mol aux fuel roots left right).any
            fun decision => decision.ordering = Ordering.eq) = none

/-- Construction, sorting, adjacency, and constitutional parity succeeded; promoted Rule 6 then
encountered one of the parity-free semantic failures classified above. -/
def AuthoritativeSourceRule6PromotedSemanticFailure
    (mol : RawMolecule) (fuel center : Nat) : Prop :=
  let node := canonicalCenterRoot center
  let ligands := mol.ligandsWithLonePair center
  let roots := authoritativeSourceRule6LigandCursors mol center
  ∃ aux sorted adjacent,
    ligands.length = 4 ∧
    buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = some aux ∧
    sortAuthoritativeRule6InitialPositions?
      mol aux fuel roots (List.range 4) = some sorted ∧
    compareAuthoritativeRule6InitialAdjacent?
      mol aux fuel roots sorted = some adjacent ∧
    some Ordering.lt ∉ adjacent ∧
    hasOddConstitutionAutomorphismAtCenter mol center ligands
      (fun left right =>
        (compareAuthoritativeRule6InitialPositions?
          mol aux fuel roots left right).any
            fun decision => decision.ordering = Ordering.eq) = some false ∧
    AuthoritativeResolvedRule6SemanticFailure
      mol aux fuel node roots sorted adjacent






def AuthoritativeSourceRule6SemanticUnresolved
    (mol : RawMolecule) (fuel center : Nat) : Prop :=
  AuthoritativeSourceRule6ConstructionFailure mol fuel center ∨
    AuthoritativeSourceRule6InitialSortFailure mol fuel center ∨
    AuthoritativeSourceRule6AdjacentComparisonFailure mol fuel center ∨
    AuthoritativeSourceRule6NoncanonicalInitialOrder mol fuel center ∨
    AuthoritativeSourceRule6TopologyFailure mol fuel center ∨
    AuthoritativeSourceRule6PromotedSemanticFailure mol fuel center

/-- Exact source refusal theorem on the explicit resolved operational domain.

This is the direct replacement theorem for an opaque
`authoritativeSourceRule6Stereogenicity? ... = none` premise: rewrite it to the six independently
meaningful source and promoted failure cases in `AuthoritativeSourceRule6SemanticUnresolved`. -/
theorem authoritativeSourceRule6Stereogenicity?_eq_none_iff_semanticUnresolved
    (mol : RawMolecule) (fuel center : Nat)
    (operational : AuthoritativeSourceRule6ResolvedOperationalDomain mol fuel center) :
    authoritativeSourceRule6Stereogenicity? mol fuel center = none ↔
      AuthoritativeSourceRule6SemanticUnresolved mol fuel center := by
  let node := canonicalCenterRoot center
  let ligands := mol.ligandsWithLonePair center
  let roots := authoritativeSourceRule6LigandCursors mol center
  constructor
  · intro computed
    by_cases ligandsLength : ligands.length = 4
    · cases auxEq : buildOccurrenceAuxStateFullyAuthoritative? mol fuel center with
      | none =>
          exact Or.inl ⟨ligandsLength, auxEq⟩
      | some aux =>
          cases sortedEq : sortAuthoritativeRule6InitialPositions?
              mol aux fuel roots (List.range 4) with
          | none =>
              exact Or.inr (Or.inl ⟨aux, ligandsLength, auxEq, sortedEq⟩)
          | some sorted =>
              cases adjacentEq : compareAuthoritativeRule6InitialAdjacent?
                  mol aux fuel roots sorted with
              | none =>
                  exact Or.inr (Or.inr (Or.inl
                    ⟨aux, sorted, ligandsLength, auxEq, sortedEq, adjacentEq⟩))
              | some adjacent =>
                  by_cases adjacentLt : some Ordering.lt ∈ adjacent
                  · exact Or.inr (Or.inr (Or.inr (Or.inl
                      ⟨aux, sorted, adjacent, ligandsLength, auxEq,
                        sortedEq, adjacentEq, adjacentLt⟩)))
                  · let initialBefore := fun left right =>
                      (compareAuthoritativeRule6InitialPositions?
                        mol aux fuel roots left right).any
                          fun decision => decision.ordering = Ordering.eq
                    cases oddEq : hasOddConstitutionAutomorphismAtCenter
                        mol center ligands initialBefore with
                    | none =>
                        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                          ⟨aux, sorted, adjacent, ligandsLength, auxEq, sortedEq,
                            adjacentEq, adjacentLt, by simpa [initialBefore] using oddEq⟩))))
                    | some odd =>
                        cases odd
                        · have resolvedNone : authoritativeResolvedRule6Stereogenicity?
                              mol aux fuel node roots sorted adjacent = none := by
                            simpa [authoritativeSourceRule6Stereogenicity?, node,
                              ligands, roots, ligandsLength, auxEq, sortedEq,
                              adjacentEq, adjacentLt, initialBefore, oddEq] using computed
                          have semanticFailure :=
                            (authoritativeResolvedRule6Stereogenicity?_eq_none_iff_semanticFailure
                              mol aux fuel node roots sorted adjacent
                                (operational aux sorted adjacent auxEq sortedEq adjacentEq)).mp
                                  resolvedNone
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                            ⟨aux, sorted, adjacent, ligandsLength, auxEq, sortedEq,
                              adjacentEq, adjacentLt,
                              by simpa [initialBefore] using oddEq, semanticFailure⟩))))
                        · simp [authoritativeSourceRule6Stereogenicity?,
                            ligands, roots, ligandsLength, auxEq, sortedEq,
                            adjacentEq, adjacentLt, initialBefore, oddEq] at computed
    · simp [authoritativeSourceRule6Stereogenicity?, ligands,
        ligandsLength] at computed
  · rintro (construction | initialSort | adjacentComparison |
      noncanonicalOrder | topologyFailure | promotedFailure)
    · rcases construction with ⟨ligandsLength, auxEq⟩
      simp [authoritativeSourceRule6Stereogenicity?, ligandsLength, auxEq]
    · rcases initialSort with ⟨aux, ligandsLength, auxEq, sortedEq⟩
      simp [authoritativeSourceRule6Stereogenicity?,
        ligandsLength, auxEq, sortedEq]
    · rcases adjacentComparison with
        ⟨aux, sorted, ligandsLength, auxEq, sortedEq, adjacentEq⟩
      simp [authoritativeSourceRule6Stereogenicity?,
        ligandsLength, auxEq, sortedEq, adjacentEq]
    · rcases noncanonicalOrder with
        ⟨aux, sorted, adjacent, ligandsLength, auxEq, sortedEq, adjacentEq, adjacentLt⟩
      simp [authoritativeSourceRule6Stereogenicity?,
        ligandsLength, auxEq, sortedEq, adjacentEq, adjacentLt]
    · rcases topologyFailure with
        ⟨aux, sorted, adjacent, ligandsLength, auxEq, sortedEq, adjacentEq,
          adjacentLt, oddEq⟩
      simp [authoritativeSourceRule6Stereogenicity?,
        ligandsLength, auxEq, sortedEq, adjacentEq, adjacentLt,
        oddEq]
    · rcases promotedFailure with
        ⟨aux, sorted, adjacent, ligandsLength, auxEq, sortedEq, adjacentEq,
          adjacentLt, oddEq, semanticFailure⟩
      have resolvedNone :=
        (authoritativeResolvedRule6Stereogenicity?_eq_none_iff_semanticFailure
          mol aux fuel node roots sorted adjacent
            (operational aux sorted adjacent auxEq sortedEq adjacentEq)).mpr semanticFailure
      simpa [authoritativeSourceRule6Stereogenicity?, node,
        ligands, roots, ligandsLength, auxEq, sortedEq, adjacentEq, adjacentLt,
        oddEq] using resolvedNone

/-- Source-level public `rankingUnresolved` output has exactly the same six semantic causes. -/
theorem authoritativeSourceRule6UnannotatedOutcome?_eq_rankingUnresolved_iff_semanticUnresolved
    (mol : RawMolecule) (fuel center : Nat)
    (operational : AuthoritativeSourceRule6ResolvedOperationalDomain mol fuel center) :
    authoritativeSourceRule6UnannotatedOutcome? mol fuel center =
        some (.refused .rankingUnresolved) ↔
      AuthoritativeSourceRule6SemanticUnresolved mol fuel center := by
  cases computed : authoritativeSourceRule6Stereogenicity? mol fuel center with
  | none =>
      simp [authoritativeSourceRule6UnannotatedOutcome?, computed,
        (authoritativeSourceRule6Stereogenicity?_eq_none_iff_semanticUnresolved
          mol fuel center operational).mp computed]
  | some decision =>
      have noFailure : ¬ AuthoritativeSourceRule6SemanticUnresolved mol fuel center := by
        intro failure
        have absent :=
          (authoritativeSourceRule6Stereogenicity?_eq_none_iff_semanticUnresolved
            mol fuel center operational).mpr failure
        rw [computed] at absent
        contradiction
      cases decision <;>
        simp [authoritativeSourceRule6UnannotatedOutcome?, computed, noFailure]

/-- Source-level Rule-6 applicability with the operationally constructed auxiliary state and
Rules-1a--5 partition retained, but with the final descriptor-existential clause replaced by its
minimal parity-free P-92 branch-agreement meaning. -/
def AuthoritativeSourceRule6BranchAgreement
    (mol : RawMolecule) (fuel center : Nat) : Prop :=
  let node := canonicalCenterRoot center
  let ligands := mol.ligandsWithLonePair center
  let roots := authoritativeSourceRule6LigandCursors mol center
  ∃ aux sorted adjacent,
    ligands.length = 4 ∧
    buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = some aux ∧
    sortAuthoritativeRule6InitialPositions?
      mol aux fuel roots (List.range 4) = some sorted ∧
    compareAuthoritativeRule6InitialAdjacent?
      mol aux fuel roots sorted = some adjacent ∧
    some Ordering.lt ∉ adjacent ∧
    hasOddConstitutionAutomorphismAtCenter mol center ligands
      (fun left right =>
        (compareAuthoritativeRule6InitialPositions?
          mol aux fuel roots left right).any
            fun decision => decision.ordering = Ordering.eq) = some false ∧
    AuthoritativeRule6ResolvedBranchAgreement
      mol aux fuel node roots sorted adjacent

/-- Exact source-level replacement theorem: the former resolved-stereogenicity clause contributes
precisely the independently enumerated parity-free P-92 branch-agreement predicate above. -/
theorem authoritativeSourceRule6Stereogenic_iff_branchAgreement
    (mol : RawMolecule) (fuel center : Nat) :
    AuthoritativeSourceRule6Stereogenic mol fuel center ↔
      AuthoritativeSourceRule6BranchAgreement mol fuel center := by
  unfold AuthoritativeSourceRule6Stereogenic AuthoritativeSourceRule6BranchAgreement
  constructor
  · rintro ⟨aux, sorted, adjacent, ligandsLength, auxEq, sortedEq, adjacentEq,
      adjacentNotLt, oddFalse, resolved⟩
    exact ⟨aux, sorted, adjacent, ligandsLength, auxEq, sortedEq, adjacentEq,
      adjacentNotLt, oddFalse,
      (authoritativeRule6ResolvedStereogenic_iff_branchAgreement
        mol aux fuel (canonicalCenterRoot center)
          (authoritativeSourceRule6LigandCursors mol center) sorted adjacent).mp resolved⟩
  · rintro ⟨aux, sorted, adjacent, ligandsLength, auxEq, sortedEq, adjacentEq,
      adjacentNotLt, oddFalse, agreement⟩
    exact ⟨aux, sorted, adjacent, ligandsLength, auxEq, sortedEq, adjacentEq,
      adjacentNotLt, oddFalse,
      (authoritativeRule6ResolvedStereogenic_iff_branchAgreement
        mol aux fuel (canonicalCenterRoot center)
          (authoritativeSourceRule6LigandCursors mol center) sorted adjacent).mpr agreement⟩

end TetraStereo.OneCenter.AuthoritativeCIPRule6Scheduler

namespace TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness

open RawMolecule
open DeclarativeCIP.ProductionOccurrenceRules456
open Rule6ReferenceBranchAgreementSemantics
open Rule6ReferenceOrbitSemantics

namespace DescriptorBranchingRule6CIPFrame

/-- The constitutional-orbit theorem supplies the parity-free agreement predicate directly.
This is the independent topology route to the two-group component of resolved applicability. -/
theorem rule6ReferenceFamilyBranchAgreement_of_constitutionalOrbit
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (writtenExact : mol.WrittenNeighborExact) (parity : TetrahedralInputParity)
    (backend : ProductionRule6RankingBackend) (references : List Nat)
    (referencesNonempty : references ≠ [])
    (oddFalse : hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
      (fun left right =>
        rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
      some false)
    (strict : StrictRule6ReferenceFamily backend references)
    (orbit : frame.ReferenceRankingsFormConstitutionalOrbit backend references) :
    Rule6ReferenceFamilyBranchAgreement backend references := by
  apply (rule6ReferenceFamilyBranchAgreement_iff_exists_commonDescriptor
    backend references parity).mpr
  exact frame.commonRule6Descriptor_of_constitutionalOrbit writtenExact parity backend references
    referencesNonempty oddFalse strict orbit

end DescriptorBranchingRule6CIPFrame

end TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness
