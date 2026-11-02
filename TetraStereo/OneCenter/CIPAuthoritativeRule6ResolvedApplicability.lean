import TetraStereo.OneCenter.CIPAuthoritativeRule6ScheduledAnalysis

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.AuthoritativeCIPRule6Scheduler

open RawMolecule
open DeclarativeCIP
open DeclarativeCIP.ProductionOccurrenceRules456
open ProductionCIPOccurrenceDiscovery
open AuthoritativeCIPRule6P92Enumeration
open Rule6ReferenceFamilySemantics

/-!
# Resolved chemical applicability of the authoritative Rule-6 result

The public scheduler is already exact with respect to its proof-relevant derivation relation.
This file removes the last result-constructor circularity inside the Rule-6 fallback.  Once the
ordinary Rules-1a--5 frame, topology gate, and geometry-independent parity input have been
resolved, applicability is stated solely by the independent P-92 reference-family judgments.
Neither `authoritativeOccurrenceRule6Result?` nor the existence of a production result occurs in
the predicate below.
-/

/-- Independent applicability of one resolved P-92 Rule-6 branch.

The first disjunct is the dependent four-reference carrier.  The second is the complete rank-one
reference family for a two-group partition.  The third is the prescribed rank-one singleton for a
three-group partition, including its local-reference gate and descriptor reversal. -/
def AuthoritativeRule6ResolvedBranchApplicability
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (parity : TetrahedralInputParity) (sorted : List Nat)
    (adjacent : List (Option Ordering)) (descriptor : RS) : Prop :=
  let ligands := mol.ligandsWithLonePair node.atom
  let backend := authoritativeOccurrenceRule6PositionRankingBackend
    mol state fuel roots ligands
  let groupCount := rule6GroupCount adjacent
  (groupCount = 1 ∧
      AuthoritativeFourWayDescriptorJudgment backend parity sorted descriptor) ∨
    (groupCount = 2 ∧
      CommonRule6Descriptor backend parity
        (rule6EquivalentReferencePositions sorted adjacent) descriptor) ∨
    (groupCount = 3 ∧
      ∃ referenceRoot,
        roots[sorted[1]?.getD 0]? = some referenceRoot ∧
        adjacent[1]?.getD none = some Ordering.eq ∧
        occurrenceBranchHasLocalReference (mol := mol) state fuel [referenceRoot] = true ∧
        CommonRule6Descriptor backend parity
          (rule6ThreeGroupReferencePositions sorted) (RS.swap descriptor))

/-! ## Descriptor-free parity transport -/

/-- Reverse the written tetrahedral input sense. -/
def oppositeTetrahedralInputParity : TetrahedralInputParity → TetrahedralInputParity
  | .clockwise => .anticlockwise
  | .anticlockwise => .clockwise

@[simp] theorem oppositeTetrahedralInputParity_involutive
    (parity : TetrahedralInputParity) :
    oppositeTetrahedralInputParity (oppositeTetrahedralInputParity parity) = parity := by
  cases parity <;> rfl

/-- Reversing the written parity reverses the descriptor of every fixed priority order. -/
@[simp] theorem descriptorOfParity_opposite
    (parity : TetrahedralInputParity) (even : Bool) :
    RawMolecule.descriptorOfParity (oppositeTetrahedralInputParity parity) even =
      RS.swap (RawMolecule.descriptorOfParity parity even) := by
  cases parity <;> cases even <;> rfl

/-- A strict promoted reference judgment transports across reversal of the arbitrary written
parity, changing only the descriptor sense. -/
theorem productionRule6BackendDescriptorJudgment_opposite
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (reference : Nat) (descriptor : RS)
    (judgment : ProductionRule6BackendDescriptorJudgment
      backend parity reference descriptor) :
    ProductionRule6BackendDescriptorJudgment backend
      (oppositeTetrahedralInputParity parity) reference (RS.swap descriptor) := by
  rcases judgment with ⟨ranking, accepted, unique, descriptorEq⟩
  exact ⟨ranking, accepted, unique, by
    rw [descriptorOfParity_opposite, descriptorEq]⟩

/-- Common reference-family applicability is independent of the arbitrary written parity. -/
theorem commonRule6Descriptor_opposite
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (references : List Nat) (descriptor : RS)
    (common : CommonRule6Descriptor backend parity references descriptor) :
    CommonRule6Descriptor backend (oppositeTetrahedralInputParity parity)
      references (RS.swap descriptor) := by
  refine ⟨common.1, ?_⟩
  intro reference member
  exact productionRule6BackendDescriptorJudgment_opposite backend parity reference descriptor
    (common.2 reference member)

/-- The dependent four-way coherence equations do not depend on which written parity is chosen. -/
theorem fourWayCarrierCoherent_opposite
    (parity : TetrahedralInputParity) (first second : Rule6TrackedRanking)
    (coherent : Rule6FourWayFamilySemantics.FourWayCarrierCoherent parity first second) :
    Rule6FourWayFamilySemantics.FourWayCarrierCoherent
      (oppositeTetrahedralInputParity parity) first second := by
  rcases coherent with ⟨different, sameDescriptor, sameUnique⟩
  refine ⟨different, ?_, sameUnique⟩
  rw [descriptorOfParity_opposite, descriptorOfParity_opposite]
  exact congrArg RS.swap sameDescriptor

/-- The full dependent four-way descriptor judgment reverses exactly when written parity is
reversed. -/
theorem authoritativeFourWayDescriptorJudgment_opposite
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (sorted : List Nat) (descriptor : RS)
    (judgment : AuthoritativeFourWayDescriptorJudgment
      backend parity sorted descriptor) :
    AuthoritativeFourWayDescriptorJudgment backend
      (oppositeTetrahedralInputParity parity) sorted (RS.swap descriptor) := by
  rcases judgment with ⟨firstReference, first, second,
    firstReferenceEq, firstEq, secondEq, coherent, descriptorEq⟩
  refine ⟨firstReference, first, second, firstReferenceEq, firstEq, secondEq,
    fourWayCarrierCoherent_opposite parity first second coherent, ?_⟩
  cases parity <;>
    cases evenEq : RawMolecule.permutationIsEven second.positions <;>
    cases uniqueEq : second.unique <;>
    cases descriptor <;>
    simp_all [oppositeTetrahedralInputParity, RawMolecule.descriptorOfParity,
      evenEq, uniqueEq, RS.swap]

/-- Reversing the arbitrary parity reverses the resolved branch descriptor and preserves
applicability. -/
theorem authoritativeRule6ResolvedBranchApplicability_opposite
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (parity : TetrahedralInputParity) (sorted : List Nat)
    (adjacent : List (Option Ordering)) (descriptor : RS)
    (applicable : AuthoritativeRule6ResolvedBranchApplicability
      mol state fuel node roots parity sorted adjacent descriptor) :
    AuthoritativeRule6ResolvedBranchApplicability mol state fuel node roots
      (oppositeTetrahedralInputParity parity) sorted adjacent (RS.swap descriptor) := by
  unfold AuthoritativeRule6ResolvedBranchApplicability at applicable ⊢
  rcases applicable with fourWay | twoOrThree
  · exact Or.inl ⟨fourWay.1,
      authoritativeFourWayDescriptorJudgment_opposite _ parity sorted descriptor fourWay.2⟩
  · rcases twoOrThree with twoGroup | threeGroup
    · exact Or.inr (Or.inl ⟨twoGroup.1,
        commonRule6Descriptor_opposite _ parity _ descriptor twoGroup.2⟩)
    · rcases threeGroup with ⟨groupThree, referenceRoot, referenceRootEq,
        middleTie, localReference, common⟩
      refine Or.inr (Or.inr ⟨groupThree, referenceRoot, referenceRootEq,
        middleTie, localReference, ?_⟩)
      have transported := commonRule6Descriptor_opposite _ parity _ (RS.swap descriptor) common
      simpa using transported

/-- Exact parity-independent form: the two arbitrary written senses have the same resolved
stereogenicity proposition, while their concrete descriptors are opposite. -/
theorem authoritativeRule6ResolvedBranchApplicability_opposite_iff
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (parity : TetrahedralInputParity) (sorted : List Nat)
    (adjacent : List (Option Ordering)) (descriptor : RS) :
    AuthoritativeRule6ResolvedBranchApplicability
        mol state fuel node roots parity sorted adjacent descriptor ↔
      AuthoritativeRule6ResolvedBranchApplicability mol state fuel node roots
        (oppositeTetrahedralInputParity parity) sorted adjacent (RS.swap descriptor) := by
  constructor
  · exact authoritativeRule6ResolvedBranchApplicability_opposite
      mol state fuel node roots parity sorted adjacent descriptor
  · intro opposite
    have transported := authoritativeRule6ResolvedBranchApplicability_opposite
      mol state fuel node roots (oppositeTetrahedralInputParity parity) sorted adjacent
        (RS.swap descriptor) opposite
    simpa using transported

/-- Descriptor-free resolved Rule-6 stereogenicity. `clockwise` is a harmless reference
orientation, not an input annotation. -/
def AuthoritativeRule6ResolvedStereogenic
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List Nat) (adjacent : List (Option Ordering)) : Prop :=
  ∃ descriptor, AuthoritativeRule6ResolvedBranchApplicability mol state fuel node roots
    .clockwise sorted adjacent descriptor

/-- The descriptor-free predicate can equivalently use either possible written parity. -/
theorem authoritativeRule6ResolvedStereogenic_iff_exists_applicable
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List Nat) (adjacent : List (Option Ordering))
    (parity : TetrahedralInputParity) :
    AuthoritativeRule6ResolvedStereogenic mol state fuel node roots sorted adjacent ↔
      ∃ descriptor, AuthoritativeRule6ResolvedBranchApplicability mol state fuel node roots
        parity sorted adjacent descriptor := by
  cases parity
  · constructor
    · rintro ⟨descriptor, applicable⟩
      exact ⟨RS.swap descriptor,
        authoritativeRule6ResolvedBranchApplicability_opposite
          mol state fuel node roots .clockwise sorted adjacent descriptor applicable⟩
    · rintro ⟨descriptor, applicable⟩
      exact ⟨RS.swap descriptor, by
        simpa using authoritativeRule6ResolvedBranchApplicability_opposite
          mol state fuel node roots .anticlockwise sorted adjacent descriptor applicable⟩
  · rfl

/-! ## Executable descriptor-free unannotated perception -/

/-- Descriptor-free authoritative Rule-6 perception on an already resolved initial frame.

`clockwise` is used only as the proved-harmless reference orientation. A successful branch is
reported as `true`; an admitted non-Rule-6 partition or a missing three-group local reference is
reported as `false`; incomplete promoted reference evaluation remains `none`. -/
def authoritativeResolvedRule6Stereogenicity?
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List Nat) (adjacent : List (Option Ordering)) : Option Bool :=
  let ligands := mol.ligandsWithLonePair node.atom
  let backend := authoritativeOccurrenceRule6PositionRankingBackend
    mol state fuel roots ligands
  let groupCount := rule6GroupCount adjacent
  if groupCount == 1 then
    (authoritativeOccurrenceRule6FourWayDescriptor?
      backend .clockwise sorted).map fun _ => true
  else if groupCount == 2 then
    (authoritativeOccurrenceRule6TwoGroupDescriptor?
      mol state fuel roots ligands sorted adjacent .clockwise).map fun _ => true
  else if groupCount == 3 then do
    let referenceRoot ← roots[sorted[1]?.getD 0]?
    if adjacent[1]?.getD none != some Ordering.eq ||
        occurrenceBranchHasLocalReference (mol := mol) state fuel [referenceRoot] != true then
      some false
    else
      (authoritativeOccurrenceRule6ThreeGroupDescriptor?
        mol state fuel roots ligands sorted .clockwise).map fun _ => true
  else
    some false

/-- The executable descriptor-free adapter returns `true` exactly for the independent,
parity-independent resolved stereogenicity proposition. -/
theorem authoritativeResolvedRule6Stereogenicity?_eq_some_true_iff
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List Nat) (adjacent : List (Option Ordering)) :
    authoritativeResolvedRule6Stereogenicity?
        mol state fuel node roots sorted adjacent = some true ↔
      AuthoritativeRule6ResolvedStereogenic
        mol state fuel node roots sorted adjacent := by
  let ligands := mol.ligandsWithLonePair node.atom
  let backend := authoritativeOccurrenceRule6PositionRankingBackend
    mol state fuel roots ligands
  let groupCount := rule6GroupCount adjacent
  change authoritativeResolvedRule6Stereogenicity?
        mol state fuel node roots sorted adjacent = some true ↔
    ∃ descriptor,
      (groupCount = 1 ∧
          AuthoritativeFourWayDescriptorJudgment
            backend .clockwise sorted descriptor) ∨
        (groupCount = 2 ∧
          CommonRule6Descriptor backend .clockwise
            (rule6EquivalentReferencePositions sorted adjacent) descriptor) ∨
        (groupCount = 3 ∧
          ∃ referenceRoot,
            roots[sorted[1]?.getD 0]? = some referenceRoot ∧
            adjacent[1]?.getD none = some Ordering.eq ∧
            occurrenceBranchHasLocalReference (mol := mol) state fuel [referenceRoot] = true ∧
            CommonRule6Descriptor backend .clockwise
              (rule6ThreeGroupReferencePositions sorted) (RS.swap descriptor))
  by_cases groupOne : groupCount = 1
  · have groupTwo : groupCount ≠ 2 := by omega
    have groupThree : groupCount ≠ 3 := by omega
    simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
      groupOne, groupTwo, groupThree,
      authoritativeOccurrenceRule6FourWayDescriptor?_eq_some_iff_judgment]
  · by_cases groupTwo : groupCount = 2
    · have groupThree : groupCount ≠ 3 := by omega
      simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
        groupOne, groupTwo, groupThree,
        authoritativeOccurrenceRule6TwoGroupDescriptor?_eq_some_iff_commonDescriptor]
    · by_cases groupThree : groupCount = 3
      · let reference := sorted[1]?.getD 0
        cases referenceRootEq : roots[reference]? with
        | none =>
            simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
              groupOne, groupTwo, groupThree, reference, referenceRootEq]
        | some referenceRoot =>
            by_cases middleTie : adjacent[1]?.getD none = some Ordering.eq
            · by_cases localReference : occurrenceBranchHasLocalReference
                  (mol := mol) state fuel [referenceRoot] = true
              · simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
                  groupOne, groupTwo, groupThree, reference, referenceRootEq,
                  middleTie, localReference, rule6ThreeGroupReferencePositions,
                  authoritativeOccurrenceRule6ThreeGroupDescriptor?_eq_some_iff_swappedCommonDescriptor]
              · simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
                  groupOne, groupTwo, groupThree, reference, referenceRootEq,
                  middleTie, localReference]
            · simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
                groupOne, groupTwo, groupThree, reference, referenceRootEq, middleTie]
      · simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
          groupOne, groupTwo, groupThree]

/-- Unannotated public outcome adapter for the authoritative resolved Rule-6 perception result.
It deliberately never emits `R/S`: a stereogenic center without configuration evidence is
reported as configuration-unspecified, while incomplete reference evaluation is reported as
ranking-unresolved. -/
def authoritativeResolvedRule6UnannotatedOutcome?
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List Nat) (adjacent : List (Option Ordering)) : Option StereoOutcome :=
  match authoritativeResolvedRule6Stereogenicity?
      mol state fuel node roots sorted adjacent with
  | some true => some (.refused .notSpecified)
  | some false => none
  | none => some (.refused .rankingUnresolved)

/-- The unannotated adapter reports configuration-unspecified exactly when the independent
resolved Rule-6 stereogenicity predicate holds. -/
theorem authoritativeResolvedRule6UnannotatedOutcome?_eq_notSpecified_iff
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List Nat) (adjacent : List (Option Ordering)) :
    authoritativeResolvedRule6UnannotatedOutcome?
        mol state fuel node roots sorted adjacent =
          some (.refused .notSpecified) ↔
      AuthoritativeRule6ResolvedStereogenic
        mol state fuel node roots sorted adjacent := by
  cases perceivedEq : authoritativeResolvedRule6Stereogenicity?
      mol state fuel node roots sorted adjacent with
  | none =>
      have notStereogenic : ¬ AuthoritativeRule6ResolvedStereogenic
          mol state fuel node roots sorted adjacent := by
        intro stereogenic
        have accepted :=
          (authoritativeResolvedRule6Stereogenicity?_eq_some_true_iff
            mol state fuel node roots sorted adjacent).mpr stereogenic
        rw [perceivedEq] at accepted
        contradiction
      simp [authoritativeResolvedRule6UnannotatedOutcome?, perceivedEq, notStereogenic]
  | some perceived =>
      cases perceived
      · have notStereogenic : ¬ AuthoritativeRule6ResolvedStereogenic
            mol state fuel node roots sorted adjacent := by
          intro stereogenic
          have accepted :=
            (authoritativeResolvedRule6Stereogenicity?_eq_some_true_iff
              mol state fuel node roots sorted adjacent).mpr stereogenic
          rw [perceivedEq] at accepted
          contradiction
        simp [authoritativeResolvedRule6UnannotatedOutcome?, perceivedEq, notStereogenic]
      · constructor
        · intro _emitted
          exact
            (authoritativeResolvedRule6Stereogenicity?_eq_some_true_iff
              mol state fuel node roots sorted adjacent).mp perceivedEq
        · intro _stereogenic
          simp [authoritativeResolvedRule6UnannotatedOutcome?, perceivedEq]

/-- After all pre-Rule-6 carrier gates have been independently resolved, the authoritative result
constructor succeeds with `descriptor` iff one of the three exact P-92 branch judgments applies.
This is the missing completeness converse to `authoritativeOccurrenceRule6Result?_sound`. -/
theorem authoritativeOccurrenceRule6Result?_success_with_descriptor_iff_resolvedApplicability
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (spec : AtomSpec) (parity : TetrahedralInputParity)
    (sorted : List Nat) (adjacent : List (Option Ordering)) (descriptor : RS)
    (atomEq : mol.atomAt? node.atom = some spec)
    (parityEq : spec.tetrahedral? = some parity)
    (ligandsLength : (mol.ligandsWithLonePair node.atom).length = 4)
    (rootsLength : roots.length = 4)
    (sortedEq : sortAuthoritativeRule6InitialPositions?
      mol state fuel roots (List.range 4) = some sorted)
    (adjacentEq : compareAuthoritativeRule6InitialAdjacent?
      mol state fuel roots sorted = some adjacent)
    (adjacentNotLt : some Ordering.lt ∉ adjacent)
    (oddFalse : hasOddConstitutionAutomorphismAtCenter mol node.atom
      (mol.ligandsWithLonePair node.atom)
      (fun left right =>
        (compareAuthoritativeRule6InitialPositions?
          mol state fuel roots left right).any
            fun decision => decision.ordering = Ordering.eq) = some false) :
    (∃ result,
      authoritativeOccurrenceRule6Result? mol state fuel node roots = some result ∧
        result.fact.descriptor = descriptor) ↔
      AuthoritativeRule6ResolvedBranchApplicability
        mol state fuel node roots parity sorted adjacent descriptor := by
  let ligands := mol.ligandsWithLonePair node.atom
  let backend := authoritativeOccurrenceRule6PositionRankingBackend
    mol state fuel roots ligands
  let groupCount := rule6GroupCount adjacent
  let initialBefore := fun left right =>
    (compareAuthoritativeRule6InitialPositions?
      mol state fuel roots left right).any
        fun decision => decision.ordering = Ordering.eq
  let oddTopology? := hasOddConstitutionAutomorphismAtCenter
    mol node.atom ligands initialBefore
  have ligandsLength' : ligands.length = 4 := ligandsLength
  have oddFalse' : oddTopology? = some false := oddFalse
  change (∃ result,
      authoritativeOccurrenceRule6Result? mol state fuel node roots = some result ∧
        result.fact.descriptor = descriptor) ↔
    (groupCount = 1 ∧
        AuthoritativeFourWayDescriptorJudgment backend parity sorted descriptor) ∨
      (groupCount = 2 ∧
        CommonRule6Descriptor backend parity
          (rule6EquivalentReferencePositions sorted adjacent) descriptor) ∨
      (groupCount = 3 ∧
        ∃ referenceRoot,
          roots[sorted[1]?.getD 0]? = some referenceRoot ∧
          adjacent[1]?.getD none = some Ordering.eq ∧
          occurrenceBranchHasLocalReference (mol := mol) state fuel [referenceRoot] = true ∧
          CommonRule6Descriptor backend parity
            (rule6ThreeGroupReferencePositions sorted) (RS.swap descriptor))
  constructor
  · rintro ⟨result, computed, resultDescriptor⟩
    by_cases groupOne : groupCount = 1
    · left
      refine ⟨groupOne, ?_⟩
      cases agreementEq : authoritativeOccurrenceRule6FourWayAgreement?
          backend parity sorted with
      | none =>
          simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
            ligandsLength', rootsLength, sortedEq, adjacentEq, adjacentNotLt,
            groupCount, initialBefore, oddTopology?, oddFalse', backend,
            groupOne, agreementEq] at computed
      | some agreement =>
          have resultEq : result =
              { fact :=
                  { key := canonicalOccurrenceKey node
                    atom := node.atom
                    descriptor := agreement.descriptor
                    uppercase := agreement.secondRanking.pseudoComparisons != 1
                    priorityPositions := agreement.secondRanking.positions }
                parity := parity
                ligands := ligands
                roots := roots
                sorted := sorted
                adjacent := adjacent
                groupCount := groupCount
                oddTopology? := oddTopology?
                carrier := .fourWay agreement } := by
            simpa [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
              ligandsLength', rootsLength, sortedEq, adjacentEq, adjacentNotLt,
              groupCount, initialBefore, oddTopology?, oddFalse', backend,
              groupOne, agreementEq] using computed.symm
          subst result
          have agreementDescriptor : agreement.descriptor = descriptor := by
            simpa using resultDescriptor
          apply (authoritativeOccurrenceRule6FourWayDescriptor?_eq_some_iff_judgment
            backend parity sorted descriptor).mp
          simp [authoritativeOccurrenceRule6FourWayDescriptor?, agreementEq,
            agreementDescriptor]
    · by_cases groupTwo : groupCount = 2
      · right
        left
        refine ⟨groupTwo, ?_⟩
        let references := rule6EquivalentReferencePositions sorted adjacent
        cases rankingEq : rankProductionRule6EquivalentReferencesWithBackend?
            backend parity references with
        | none =>
            simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
              ligandsLength', rootsLength, sortedEq, adjacentEq, adjacentNotLt,
              groupCount, initialBefore, oddTopology?, oddFalse', backend,
              groupOne, groupTwo, references, rankingEq] at computed
        | some ranking =>
            have resultEq : result =
                { fact :=
                    { key := canonicalOccurrenceKey node
                      atom := node.atom
                      descriptor := RawMolecule.descriptorOfParity parity
                        (RawMolecule.permutationIsEven ranking.positions)
                      uppercase := ranking.pseudoComparisons != 1
                      priorityPositions := ranking.positions }
                  parity := parity
                  ligands := ligands
                  roots := roots
                  sorted := sorted
                  adjacent := adjacent
                  groupCount := groupCount
                  oddTopology? := oddTopology?
                  carrier := .twoGroup references ranking } := by
              simpa [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
                ligandsLength', rootsLength, sortedEq, adjacentEq, adjacentNotLt,
                groupCount, initialBefore, oddTopology?, oddFalse', backend,
                groupOne, groupTwo, references, rankingEq] using computed.symm
            subst result
            have rankingDescriptor : RawMolecule.descriptorOfParity parity
                (RawMolecule.permutationIsEven ranking.positions) = descriptor := by
              simpa using resultDescriptor
            apply (rule6FamilyDescriptorWithBackend?_eq_some_iff_commonDescriptor
              backend parity references descriptor).mp
            simp [rule6FamilyDescriptorWithBackend?, rankingEq, rankingDescriptor]
      · by_cases groupThree : groupCount = 3
        · right
          right
          refine ⟨groupThree, ?_⟩
          let reference := sorted[1]?.getD 0
          cases referenceRootEq : roots[reference]? with
          | none =>
              simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
                ligandsLength', rootsLength, sortedEq, adjacentEq, adjacentNotLt,
                groupCount, initialBefore, oddTopology?, oddFalse', backend,
                groupOne, groupTwo, groupThree, reference, referenceRootEq] at computed
          | some referenceRoot =>
              by_cases middleTie : adjacent[1]?.getD none = some Ordering.eq
              · by_cases localReference : occurrenceBranchHasLocalReference
                    (mol := mol) state fuel [referenceRoot] = true
                · cases rankingEq : rankProductionRule6EquivalentReferencesWithBackend?
                      backend parity [reference] with
                  | none =>
                      simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
                        ligandsLength', rootsLength, sortedEq, adjacentEq, adjacentNotLt,
                        groupCount, initialBefore, oddTopology?, oddFalse', backend,
                        groupOne, groupTwo, groupThree, reference, referenceRootEq,
                        middleTie, localReference, rankingEq] at computed
                  | some ranking =>
                      have resultEq : result =
                          { fact :=
                              { key := canonicalOccurrenceKey node
                                atom := node.atom
                                descriptor := RS.swap
                                  (RawMolecule.descriptorOfParity parity
                                    (RawMolecule.permutationIsEven ranking.positions))
                                uppercase := true
                                priorityPositions := ranking.positions }
                            parity := parity
                            ligands := ligands
                            roots := roots
                            sorted := sorted
                            adjacent := adjacent
                            groupCount := groupCount
                            oddTopology? := oddTopology?
                            carrier := .threeGroup reference ranking } := by
                        simpa [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
                          ligandsLength', rootsLength, sortedEq, adjacentEq, adjacentNotLt,
                          groupCount, initialBefore, oddTopology?, oddFalse', backend,
                          groupOne, groupTwo, groupThree, reference, referenceRootEq,
                          middleTie, localReference, rankingEq] using computed.symm
                      subst result
                      have rankingDescriptor : RS.swap
                          (RawMolecule.descriptorOfParity parity
                            (RawMolecule.permutationIsEven ranking.positions)) = descriptor := by
                        exact resultDescriptor
                      refine ⟨referenceRoot, ?_, middleTie, localReference, ?_⟩
                      · rfl
                      · apply
                          (authoritativeOccurrenceRule6ThreeGroupDescriptor?_eq_some_iff_swappedCommonDescriptor
                            mol state fuel roots ligands sorted parity descriptor).mp
                        simp [authoritativeOccurrenceRule6ThreeGroupDescriptor?,
                          authoritativeOccurrenceRule6PositionFamilyDescriptor?,
                          rule6FamilyDescriptorWithBackend?, backend, reference,
                          rule6ThreeGroupReferencePositions, rankingEq, rankingDescriptor]
                · simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
                    ligandsLength', rootsLength, sortedEq, adjacentEq, adjacentNotLt,
                    groupCount, initialBefore, oddTopology?, oddFalse', backend,
                    groupOne, groupTwo, groupThree, reference, referenceRootEq,
                    middleTie, localReference] at computed
              · simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
                  ligandsLength', rootsLength, sortedEq, adjacentEq, adjacentNotLt,
                  groupCount, initialBefore, oddTopology?, oddFalse', backend,
                  groupOne, groupTwo, groupThree, reference, referenceRootEq,
                  middleTie] at computed
        · simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
            ligandsLength', rootsLength, sortedEq, adjacentEq, adjacentNotLt,
            groupCount, initialBefore, oddTopology?, oddFalse', backend,
            groupOne, groupTwo, groupThree] at computed
  · rintro (fourWay | twoOrThree)
    · rcases fourWay with ⟨groupOne, judgment⟩
      have descriptorEq :=
        (authoritativeOccurrenceRule6FourWayDescriptor?_eq_some_iff_judgment
          backend parity sorted descriptor).mpr judgment
      cases agreementEq : authoritativeOccurrenceRule6FourWayAgreement?
          backend parity sorted with
      | none => simp [authoritativeOccurrenceRule6FourWayDescriptor?, agreementEq] at descriptorEq
      | some agreement =>
          have agreementDescriptor : agreement.descriptor = descriptor := by
            simpa [authoritativeOccurrenceRule6FourWayDescriptor?, agreementEq] using descriptorEq
          let result : OccurrenceRule6Result :=
            { fact :=
                { key := canonicalOccurrenceKey node
                  atom := node.atom
                  descriptor := agreement.descriptor
                  uppercase := agreement.secondRanking.pseudoComparisons != 1
                  priorityPositions := agreement.secondRanking.positions }
              parity := parity
              ligands := ligands
              roots := roots
              sorted := sorted
              adjacent := adjacent
              groupCount := groupCount
              oddTopology? := oddTopology?
              carrier := .fourWay agreement }
          refine ⟨result, ?_, by simpa [result] using agreementDescriptor⟩
          simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
            ligandsLength', rootsLength, sortedEq, adjacentEq, adjacentNotLt,
            groupCount, initialBefore, oddTopology?, oddFalse', backend,
            groupOne, agreementEq, result]
    · rcases twoOrThree with twoGroup | threeGroup
      · rcases twoGroup with ⟨groupTwo, common⟩
        have descriptorEq :=
          (rule6FamilyDescriptorWithBackend?_eq_some_iff_commonDescriptor
            backend parity (rule6EquivalentReferencePositions sorted adjacent) descriptor).mpr
              common
        let references := rule6EquivalentReferencePositions sorted adjacent
        cases rankingEq : rankProductionRule6EquivalentReferencesWithBackend?
            backend parity references with
        | none => simp [rule6FamilyDescriptorWithBackend?, references, rankingEq] at descriptorEq
        | some ranking =>
            have rankingDescriptor : RawMolecule.descriptorOfParity parity
                (RawMolecule.permutationIsEven ranking.positions) = descriptor := by
              simpa [rule6FamilyDescriptorWithBackend?, references, rankingEq] using descriptorEq
            have groupOne : groupCount ≠ 1 := by omega
            let result : OccurrenceRule6Result :=
              { fact :=
                  { key := canonicalOccurrenceKey node
                    atom := node.atom
                    descriptor := RawMolecule.descriptorOfParity parity
                      (RawMolecule.permutationIsEven ranking.positions)
                    uppercase := ranking.pseudoComparisons != 1
                    priorityPositions := ranking.positions }
                parity := parity
                ligands := ligands
                roots := roots
                sorted := sorted
                adjacent := adjacent
                groupCount := groupCount
                oddTopology? := oddTopology?
                carrier := .twoGroup references ranking }
            refine ⟨result, ?_, by simpa [result] using rankingDescriptor⟩
            simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
              ligandsLength', rootsLength, sortedEq, adjacentEq, adjacentNotLt,
              groupCount, initialBefore, oddTopology?, oddFalse', backend,
              groupOne, groupTwo, references, rankingEq, result]
      · rcases threeGroup with ⟨groupThree, referenceRoot, referenceRootEq,
          middleTie, localReference, common⟩
        have descriptorEq :=
          (authoritativeOccurrenceRule6ThreeGroupDescriptor?_eq_some_iff_swappedCommonDescriptor
            mol state fuel roots ligands sorted parity descriptor).mpr common
        let reference := sorted[1]?.getD 0
        cases rankingEq : rankProductionRule6EquivalentReferencesWithBackend?
            backend parity [reference] with
        | none =>
            simp [authoritativeOccurrenceRule6ThreeGroupDescriptor?,
              authoritativeOccurrenceRule6PositionFamilyDescriptor?,
              rule6FamilyDescriptorWithBackend?, backend, reference,
              rule6ThreeGroupReferencePositions, rankingEq] at descriptorEq
        | some ranking =>
            have rankingDescriptor : RS.swap (RawMolecule.descriptorOfParity parity
                (RawMolecule.permutationIsEven ranking.positions)) = descriptor := by
              simpa [authoritativeOccurrenceRule6ThreeGroupDescriptor?,
                authoritativeOccurrenceRule6PositionFamilyDescriptor?,
                rule6FamilyDescriptorWithBackend?, backend, reference,
                rule6ThreeGroupReferencePositions, rankingEq] using descriptorEq
            have groupOne : groupCount ≠ 1 := by omega
            have groupTwo : groupCount ≠ 2 := by omega
            let result : OccurrenceRule6Result :=
              { fact :=
                  { key := canonicalOccurrenceKey node
                    atom := node.atom
                    descriptor := RS.swap (RawMolecule.descriptorOfParity parity
                      (RawMolecule.permutationIsEven ranking.positions))
                    uppercase := true
                    priorityPositions := ranking.positions }
                parity := parity
                ligands := ligands
                roots := roots
                sorted := sorted
                adjacent := adjacent
                groupCount := groupCount
                oddTopology? := oddTopology?
                carrier := .threeGroup reference ranking }
            refine ⟨result, ?_, by simpa [result] using rankingDescriptor⟩
            simp [authoritativeOccurrenceRule6Result?, atomEq, parityEq, ligands,
              ligandsLength', rootsLength, sortedEq, adjacentEq, adjacentNotLt,
              groupCount, initialBefore, oddTopology?, oddFalse', backend,
              groupOne, groupTwo, groupThree, reference, referenceRootEq,
              middleTie, localReference, rankingEq, result]

/-! ## Fixed-point and public-list completeness -/

/-- Pure resolved Rule-6 applicability at a final unit produces a literal member of the public
authoritative list, with the requested descriptor and physical-unit multiplicity one.  The
hypotheses contain the independently resolved pre-Rule-6 frame and branch proposition; they do not
assume result, label, derivation, solved-state assignment, or public-list success. -/
theorem every_resolvedRule6Applicable_finalUnit_public_exactly_once
    {mol : RawMolecule} (discovery : Discovery mol) (fuel : Nat)
    (unit : FinalUnit mol) (aux : OccurrenceAuxState)
    (roots : List CanonicalRerootCursor) (spec : AtomSpec)
    (parity : TetrahedralInputParity) (sorted : List Nat)
    (adjacent : List (Option Ordering)) (descriptor : RS)
    (auxEq : executableStateFor? discovery
      (authoritativeSolvedState discovery fuel) (finalOccurrence discovery unit) = some aux)
    (rootsEq : targetLigandFrame? discovery (finalOccurrence discovery unit) = some roots)
    (atomEq : mol.atomAt?
      (sourceNode discovery (finalOccurrence discovery unit)).atom = some spec)
    (parityEq : spec.tetrahedral? = some parity)
    (ligandsLength : (mol.ligandsWithLonePair
      (sourceNode discovery (finalOccurrence discovery unit)).atom).length = 4)
    (rootsLength : roots.length = 4)
    (sortedEq : sortAuthoritativeRule6InitialPositions? mol aux fuel roots (List.range 4) =
      some sorted)
    (adjacentEq : compareAuthoritativeRule6InitialAdjacent? mol aux fuel roots sorted =
      some adjacent)
    (adjacentNotLt : some Ordering.lt ∉ adjacent)
    (oddFalse : hasOddConstitutionAutomorphismAtCenter mol
      (sourceNode discovery (finalOccurrence discovery unit)).atom
      (mol.ligandsWithLonePair
        (sourceNode discovery (finalOccurrence discovery unit)).atom)
      (fun left right =>
        (compareAuthoritativeRule6InitialPositions?
          mol aux fuel roots left right).any
            fun decision => decision.ordering = Ordering.eq) = some false)
    (applicable : AuthoritativeRule6ResolvedBranchApplicability mol aux fuel
      (sourceNode discovery (finalOccurrence discovery unit)) roots parity sorted adjacent
        descriptor)
    (ordinaryNone : ordinaryLabel? discovery fuel
      (authoritativeSolvedState discovery fuel) (finalOccurrence discovery unit) = none) :
    ∃ assignment : AuthoritativeScheduledAssignment discovery,
      assignment ∈ analyzeAuthoritativeScheduledTetrahedral discovery fuel ∧
        assignment.unit = unit ∧
        assignment.label.fact.descriptor = descriptor ∧
        List.count unit
          ((analyzeAuthoritativeScheduledTetrahedral discovery fuel).map
            AuthoritativeScheduledAssignment.unit) = 1 := by
  let target := finalOccurrence discovery unit
  let node := sourceNode discovery target
  obtain ⟨result, resultEq, resultDescriptor⟩ :=
    (authoritativeOccurrenceRule6Result?_success_with_descriptor_iff_resolvedApplicability
      mol aux fuel node roots spec parity sorted adjacent descriptor atomEq parityEq
      ligandsLength rootsLength sortedEq adjacentEq adjacentNotLt oddFalse).mpr applicable
  have frameEq : target.node = Sum.inl () := rfl
  let label : Label discovery :=
    labelOfFinalFact discovery target result.fact () frameEq
  have rule6Accepted : authoritativeRule6Label? discovery fuel
      (authoritativeSolvedState discovery fuel) target = some label := by
    apply (authoritativeRule6Label?_eq_some_iff discovery fuel
      (authoritativeSolvedState discovery fuel) target label).mpr
    refine ⟨(), frameEq, aux, roots, result, ?_, ?_, ?_, ?_⟩
    · simpa [target] using auxEq
    · simpa [target] using rootsEq
    · simpa [node] using resultEq
    · rfl
  have derivedAccepted : authoritativeDerive? discovery fuel
      (authoritativeSolvedState discovery fuel) target = some label := by
    simp [authoritativeDerive?, ordinaryNone, target, rule6Accepted]
  have model := authoritativeSolvedState_cipModel discovery fuel
  have modelDerived := model target
  have modelStep : authoritativeDerive? discovery fuel
      (authoritativeSolvedState discovery fuel) target =
        authoritativeSolvedState discovery fuel target :=
    (authoritativeDerivation_iff_derive? discovery fuel
      (authoritativeSolvedState discovery fuel) target
        (authoritativeSolvedState discovery fuel target)).mp (by
          simpa [authoritativeOccurrenceSystem] using modelDerived)
  have assigned : authoritativeSolvedState discovery fuel target = some label :=
    modelStep.symm.trans derivedAccepted
  let assignment : AuthoritativeScheduledAssignment discovery := { unit, label }
  have projected : authoritativeScheduledAssignmentAt? discovery
      (authoritativeSolvedState discovery fuel) unit = some assignment := by
    simp [authoritativeScheduledAssignmentAt?, target, assigned, assignment]
  have present : assignment ∈ analyzeAuthoritativeScheduledTetrahedral discovery fuel :=
    (mem_analyzeAuthoritativeScheduledTetrahedral_iff discovery fuel assignment).mpr projected
  refine ⟨assignment, present, rfl, ?_, ?_⟩
  · simpa [assignment, label] using resultDescriptor
  · simpa [assignment] using
      authoritativeScheduledAssignment_unit_count_eq_one discovery fuel assignment present

end TetraStereo.OneCenter.AuthoritativeCIPRule6Scheduler
