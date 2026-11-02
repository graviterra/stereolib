import TetraStereo.OneCenter.Rule6PartitionGroupCount
import TetraStereo.OneCenter.ProductionRule6Certificate

set_option autoImplicit false

namespace TetraStereo.OneCenter.Rule6ReferenceFamilySemantics

/-!
# Independent semantics of a Rule-6 reference family

The production all-reference checker is operationally phrased around the first ranking it returns.
This module removes that implementation choice.  A reference family has a common descriptor when
it is nonempty and every member independently has a strict promoted ranking with that descriptor.
The executable checker succeeds iff this proposition holds.

When every listed ranking is structurally executable, failure is classified exactly: at least one
reference is non-strict, or two strict references produce opposite descriptors.  There is no third
fuel, lookup, early-exit, or list-plumbing failure hidden at this boundary.
-/

open RawMolecule

/-- Reference-choice-independent Rule-6 descriptor semantics for an arbitrary ranking backend. -/
def CommonRule6Descriptor (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (references : List Nat) (descriptor : RS) : Prop :=
  references ≠ [] ∧
    ∀ reference, reference ∈ references →
      ProductionRule6BackendDescriptorJudgment backend parity reference descriptor

/-- Descriptor projection of the backend-parametric all-reference checker.  Keeping this
definition independent of any molecule representation makes the final descriptor theorem reusable
for raw, occurrence, and position-to-atom adapted backends. -/
def rule6FamilyDescriptorWithBackend? (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (references : List Nat) : Option RS := do
  let ranking ← rankProductionRule6EquivalentReferencesWithBackend? backend parity references
  some (RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven ranking.positions))

/-- A common family descriptor, when it exists, is unique. -/
theorem commonRule6Descriptor_functional
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (references : List Nat) {first second : RS}
    (firstCommon : CommonRule6Descriptor backend parity references first)
    (secondCommon : CommonRule6Descriptor backend parity references second) :
    first = second := by
  cases references with
  | nil => exact False.elim (firstCommon.1 rfl)
  | cons reference remaining =>
      exact productionRule6BackendDescriptorJudgment_functional backend parity reference
        (firstCommon.2 reference (by simp)) (secondCommon.2 reference (by simp))

/-- The executable all-reference check succeeds exactly when the independently stated reference
family has a common descriptor. -/
theorem rankProductionRule6EquivalentReferencesWithBackend?_success_iff_commonDescriptor
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (references : List Nat) :
    (∃ first,
      rankProductionRule6EquivalentReferencesWithBackend? backend parity references =
        some first) ↔
      ∃ descriptor, CommonRule6Descriptor backend parity references descriptor := by
  constructor
  · rintro ⟨first, accepted⟩
    rcases rankProductionRule6EquivalentReferencesWithBackend?_sound backend parity references
      first accepted with ⟨certificate⟩
    let descriptor := RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven first.positions)
    have referencePresent : references.head?.isSome = true := by
      rw [certificate.reference_head]
      rfl
    refine ⟨descriptor, ?_, certificate.all_references⟩
    intro referencesEq
    simp [referencesEq] at referencePresent
  · rintro ⟨descriptor, referencesNonempty, common⟩
    cases references with
    | nil => exact False.elim (referencesNonempty rfl)
    | cons firstReference remaining =>
        rcases common firstReference (by simp) with
          ⟨first, firstRanking, firstUnique, firstDescriptor⟩
        refine ⟨first,
          rankProductionRule6EquivalentReferencesWithBackend?_complete backend parity
            (firstReference :: remaining) first ?_⟩
        refine
          { firstReferencePosition := firstReference
            reference_head := rfl
            first_ranking := firstRanking
            first_unique := firstUnique
            all_references := ?_ }
        intro reference member
        rcases common reference member with
          ⟨ranking, rankingEq, unique, descriptorEq⟩
        exact ⟨ranking, rankingEq, unique, descriptorEq.trans firstDescriptor.symm⟩

/-- The descriptor projection emits exactly the unique descriptor shared by every strict
reference ranking. -/
theorem rule6FamilyDescriptorWithBackend?_eq_some_iff_commonDescriptor
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (references : List Nat) (descriptor : RS) :
    rule6FamilyDescriptorWithBackend? backend parity references = some descriptor ↔
      CommonRule6Descriptor backend parity references descriptor := by
  constructor
  · intro emitted
    unfold rule6FamilyDescriptorWithBackend? at emitted
    cases acceptedEq : rankProductionRule6EquivalentReferencesWithBackend?
        backend parity references with
    | none => simp [acceptedEq] at emitted
    | some first =>
        have descriptorEq : RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven first.positions) = descriptor := by
          simpa [acceptedEq] using emitted
        rcases rankProductionRule6EquivalentReferencesWithBackend?_sound
            backend parity references first acceptedEq with ⟨certificate⟩
        have referencesNonempty : references ≠ [] := by
          intro referencesEq
          simpa [referencesEq] using certificate.reference_head
        refine ⟨referencesNonempty, ?_⟩
        intro reference member
        rcases certificate.all_references reference member with
          ⟨ranking, rankingEq, unique, sameAsFirst⟩
        exact ⟨ranking, rankingEq, unique, sameAsFirst.trans descriptorEq⟩
  · intro common
    have commonExists : ∃ candidate,
        CommonRule6Descriptor backend parity references candidate :=
      ⟨descriptor, common⟩
    rcases
        (rankProductionRule6EquivalentReferencesWithBackend?_success_iff_commonDescriptor
          backend parity references).2 commonExists with ⟨first, acceptedEq⟩
    rcases rankProductionRule6EquivalentReferencesWithBackend?_sound
        backend parity references first acceptedEq with ⟨certificate⟩
    have firstMember : certificate.firstReferencePosition ∈ references := by
      cases references with
      | nil => exact False.elim (common.1 rfl)
      | cons head tail =>
          have headEq : certificate.firstReferencePosition = head := by
            simpa using certificate.reference_head.symm
          simp [headEq]
    rcases common.2 certificate.firstReferencePosition firstMember with
      ⟨ranking, rankingEq, _unique, rankingDescriptor⟩
    have rankingEqFirst : ranking = first :=
      Option.some.inj (rankingEq.symm.trans certificate.first_ranking)
    subst ranking
    unfold rule6FamilyDescriptorWithBackend?
    simp [acceptedEq, rankingDescriptor]

/-- Failure of the executable checker is exactly nonexistence of a common family descriptor. -/
theorem rankProductionRule6EquivalentReferencesWithBackend?_eq_none_iff_no_commonDescriptor
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (references : List Nat) :
    rankProductionRule6EquivalentReferencesWithBackend? backend parity references = none ↔
      ¬ ∃ descriptor, CommonRule6Descriptor backend parity references descriptor := by
  constructor
  · intro resultNone common
    rcases
        (rankProductionRule6EquivalentReferencesWithBackend?_success_iff_commonDescriptor
          backend parity references).mpr common with ⟨first, accepted⟩
    rw [resultNone] at accepted
    contradiction
  · intro noCommon
    cases resultEq : rankProductionRule6EquivalentReferencesWithBackend? backend parity references
      with
    | none => rfl
    | some first =>
        exact False.elim (noCommon
          ((rankProductionRule6EquivalentReferencesWithBackend?_success_iff_commonDescriptor
            backend parity references).mp ⟨first, resultEq⟩))

/-- One listed reference has a completed but non-strict promoted ranking. -/
def HasNonStrictRule6Reference (backend : ProductionRule6RankingBackend)
    (references : List Nat) : Prop :=
  ∃ reference, reference ∈ references ∧
    ∃ ranking, backend reference = some ranking ∧ ranking.unique = false

/-- Two listed references have completed strict rankings but opposite final descriptors. -/
def HasRule6ReferenceDescriptorConflict (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (references : List Nat) : Prop :=
  ∃ firstReference, firstReference ∈ references ∧
    ∃ secondReference, secondReference ∈ references ∧
      ∃ firstRanking secondRanking,
        backend firstReference = some firstRanking ∧
        backend secondReference = some secondRanking ∧
        firstRanking.unique = true ∧ secondRanking.unique = true ∧
        RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven firstRanking.positions) ≠
          RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven secondRanking.positions)

/-- With nonempty references and total per-reference ranking, failure of common-descriptor
semantics has exactly two possible witnesses: non-strictness or descriptor conflict. -/
theorem no_commonRule6Descriptor_iff_nonStrict_or_descriptorConflict
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (references : List Nat)
    (referencesNonempty : references ≠ [])
    (rankingTotal : ∀ reference, reference ∈ references →
      ∃ ranking, backend reference = some ranking) :
    (¬ ∃ descriptor, CommonRule6Descriptor backend parity references descriptor) ↔
      HasNonStrictRule6Reference backend references ∨
        HasRule6ReferenceDescriptorConflict backend parity references := by
  constructor
  · intro noCommon
    by_cases nonStrict : HasNonStrictRule6Reference backend references
    · exact Or.inl nonStrict
    · right
      rcases List.exists_mem_of_ne_nil references referencesNonempty with
        ⟨firstReference, firstMember⟩
      rcases rankingTotal firstReference firstMember with ⟨firstRanking, firstRankingEq⟩
      have firstUnique : firstRanking.unique = true := by
        cases uniqueEq : firstRanking.unique with
        | false =>
            exact False.elim (nonStrict
              ⟨firstReference, firstMember, firstRanking, firstRankingEq, uniqueEq⟩)
        | true => rfl
      let descriptor := RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven firstRanking.positions)
      by_contra noConflict
      apply noCommon
      refine ⟨descriptor, referencesNonempty, ?_⟩
      intro reference member
      rcases rankingTotal reference member with ⟨ranking, rankingEq⟩
      have unique : ranking.unique = true := by
        cases uniqueEq : ranking.unique with
        | false =>
            exact False.elim
              (nonStrict ⟨reference, member, ranking, rankingEq, uniqueEq⟩)
        | true => rfl
      have descriptorEq : RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven ranking.positions) = descriptor := by
        by_contra different
        exact noConflict
          ⟨firstReference, firstMember, reference, member, firstRanking, ranking,
            firstRankingEq, rankingEq, firstUnique, unique, Ne.symm different⟩
      exact ⟨ranking, rankingEq, unique, descriptorEq⟩
  · rintro (nonStrict | conflict) ⟨descriptor, _, common⟩
    · rcases nonStrict with ⟨reference, member, ranking, rankingEq, uniqueFalse⟩
      rcases common reference member with
        ⟨commonRanking, commonRankingEq, commonUnique, _⟩
      have rankingEqual : ranking = commonRanking :=
        Option.some.inj (rankingEq.symm.trans commonRankingEq)
      subst commonRanking
      rw [uniqueFalse] at commonUnique
      contradiction
    · rcases conflict with
        ⟨firstReference, firstMember, secondReference, secondMember,
          firstRanking, secondRanking, firstRankingEq, secondRankingEq,
          _, _, different⟩
      rcases common firstReference firstMember with
        ⟨commonFirst, commonFirstEq, _, commonFirstDescriptor⟩
      rcases common secondReference secondMember with
        ⟨commonSecond, commonSecondEq, _, commonSecondDescriptor⟩
      have firstEqual : firstRanking = commonFirst :=
        Option.some.inj (firstRankingEq.symm.trans commonFirstEq)
      have secondEqual : secondRanking = commonSecond :=
        Option.some.inj (secondRankingEq.symm.trans commonSecondEq)
      subst commonFirst
      subst commonSecond
      exact different (commonFirstDescriptor.trans commonSecondDescriptor.symm)

/-- Under total reference execution, executable failure is equivalently an explicit non-strict
reference or a pair of strict references with opposite descriptors. -/
theorem rankProductionRule6EquivalentReferencesWithBackend?_eq_none_iff_failureWitness
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (references : List Nat)
    (referencesNonempty : references ≠ [])
    (rankingTotal : ∀ reference, reference ∈ references →
      ∃ ranking, backend reference = some ranking) :
    rankProductionRule6EquivalentReferencesWithBackend? backend parity references = none ↔
      HasNonStrictRule6Reference backend references ∨
        HasRule6ReferenceDescriptorConflict backend parity references :=
  (rankProductionRule6EquivalentReferencesWithBackend?_eq_none_iff_no_commonDescriptor
      backend parity references).trans
    (no_commonRule6Descriptor_iff_nonStrict_or_descriptorConflict backend parity references
      referencesNonempty rankingTotal)

/-- Under total execution of a nonempty family, the final descriptor projection refuses exactly
for the same two semantic reasons as the underlying all-reference checker. -/
theorem rule6FamilyDescriptorWithBackend?_eq_none_iff_failureWitness
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (references : List Nat)
    (referencesNonempty : references ≠ [])
    (rankingTotal : ∀ reference, reference ∈ references →
      ∃ ranking, backend reference = some ranking) :
    rule6FamilyDescriptorWithBackend? backend parity references = none ↔
      HasNonStrictRule6Reference backend references ∨
        HasRule6ReferenceDescriptorConflict backend parity references := by
  have classification :=
    rankProductionRule6EquivalentReferencesWithBackend?_eq_none_iff_failureWitness
      backend parity references referencesNonempty rankingTotal
  constructor
  · intro descriptorNone
    have rankingNone :
        rankProductionRule6EquivalentReferencesWithBackend? backend parity references = none := by
      cases acceptedEq : rankProductionRule6EquivalentReferencesWithBackend?
          backend parity references with
      | none => rfl
      | some ranking =>
          simp [rule6FamilyDescriptorWithBackend?, acceptedEq] at descriptorNone
    exact classification.mp rankingNone
  · intro failure
    have rankingNone := classification.mpr failure
    simp [rule6FamilyDescriptorWithBackend?, rankingNone]

end TetraStereo.OneCenter.Rule6ReferenceFamilySemantics
