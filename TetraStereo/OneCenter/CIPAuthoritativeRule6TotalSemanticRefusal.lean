import TetraStereo.OneCenter.CIPAuthoritativeRule6DerivedSpatialIntegration

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter
namespace AuthoritativeCIPRule6Scheduler

open RawMolecule
open DeclarativeCIP.ProductionOccurrenceRules456
open Rule6ReferenceFamilySemantics
open Rule6ReferenceBranchAgreementSemantics
open AuthoritativeCIPRule6P92Enumeration

/-!
# Unconditional semantic classification of authoritative Rule-6 refusal

The branch-agreement layer classifies chemical refusal once promoted ranking is operational.  The
public analyzer, however, must also explain every `rankingUnresolved` result on arbitrary admitted
input.  This module removes the operational premise.  Missing promoted rankings are absorbed by
the negation of the same descriptor-free branch-agreement relations, yielding an unconditional
source theorem and an exact replacement judgment through the final coordinate-derived analyzer.
-/

private theorem option_eq_none_iff_not_exists_eq_some {α : Type*} (value : Option α) :
    value = none ↔ ¬∃ output, value = some output := by
  cases value <;> simp

/-- Four-way descriptor absence is unconditionally the negation of the parity-free dependent
carrier agreement.  Missing first or dependent rankings are included without mentioning a
descriptor-valued result. -/
theorem authoritativeOccurrenceRule6FourWayDescriptor?_eq_none_iff_not_branchAgreement
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (sorted : List Nat) :
    authoritativeOccurrenceRule6FourWayDescriptor? backend parity sorted = none ↔
      ¬AuthoritativeRule6FourWayBranchAgreement backend sorted := by
  rw [option_eq_none_iff_not_exists_eq_some]
  apply not_congr
  constructor
  · rintro ⟨descriptor, emitted⟩
    exact
      (authoritativeRule6FourWayBranchAgreement_iff_exists_descriptor
        backend sorted parity).mpr
        ⟨descriptor,
          (authoritativeOccurrenceRule6FourWayDescriptor?_eq_some_iff_judgment
            backend parity sorted descriptor).mp emitted⟩
  · intro agreement
    obtain ⟨descriptor, judgment⟩ :=
      (authoritativeRule6FourWayBranchAgreement_iff_exists_descriptor
        backend sorted parity).mp agreement
    exact ⟨descriptor,
      (authoritativeOccurrenceRule6FourWayDescriptor?_eq_some_iff_judgment
        backend parity sorted descriptor).mpr judgment⟩

/-- Reference-family descriptor absence is unconditionally the negation of strict common-parity
branch agreement.  This covers both genuine non-strict/parity conflict and a missing promoted
ranking. -/
theorem rule6FamilyDescriptorWithBackend?_eq_none_iff_not_branchAgreement
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (references : List Nat) :
    rule6FamilyDescriptorWithBackend? backend parity references = none ↔
      ¬Rule6ReferenceFamilyBranchAgreement backend references := by
  rw [option_eq_none_iff_not_exists_eq_some]
  apply not_congr
  constructor
  · rintro ⟨descriptor, emitted⟩
    exact
      (rule6ReferenceFamilyBranchAgreement_iff_exists_commonDescriptor
        backend references parity).mpr
        ⟨descriptor,
          (rule6FamilyDescriptorWithBackend?_eq_some_iff_commonDescriptor
            backend parity references descriptor).mp emitted⟩
  · intro agreement
    obtain ⟨descriptor, common⟩ :=
      (rule6ReferenceFamilyBranchAgreement_iff_exists_commonDescriptor
        backend references parity).mp agreement
    exact ⟨descriptor,
      (rule6FamilyDescriptorWithBackend?_eq_some_iff_commonDescriptor
        backend parity references descriptor).mpr common⟩

/-- The descriptor swap in the three-group singleton cannot introduce or remove failure. -/
theorem authoritativeOccurrenceRule6ThreeGroupDescriptor?_eq_none_iff_not_branchAgreement
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands sorted : List Nat)
    (parity : TetrahedralInputParity) :
    authoritativeOccurrenceRule6ThreeGroupDescriptor?
        mol state fuel roots ligands sorted parity = none ↔
      ¬Rule6ReferenceFamilyBranchAgreement
        (authoritativeOccurrenceRule6PositionRankingBackend
          mol state fuel roots ligands)
        (rule6ThreeGroupReferencePositions sorted) := by
  let backend :=
    authoritativeOccurrenceRule6PositionRankingBackend mol state fuel roots ligands
  have classified := rule6FamilyDescriptorWithBackend?_eq_none_iff_not_branchAgreement
    backend parity (rule6ThreeGroupReferencePositions sorted)
  cases familyEq : rule6FamilyDescriptorWithBackend?
      backend parity (rule6ThreeGroupReferencePositions sorted) with
  | none =>
      have noAgreement := classified.mp familyEq
      simp [authoritativeOccurrenceRule6ThreeGroupDescriptor?,
        authoritativeOccurrenceRule6PositionFamilyDescriptor?, backend, familyEq, noAgreement]
  | some descriptor =>
      have agreement : Rule6ReferenceFamilyBranchAgreement backend
          (rule6ThreeGroupReferencePositions sorted) := by
        by_contra noAgreement
        have absent := classified.mpr noAgreement
        rw [familyEq] at absent
        contradiction
      simp [authoritativeOccurrenceRule6ThreeGroupDescriptor?,
        authoritativeOccurrenceRule6PositionFamilyDescriptor?, backend, familyEq, agreement]

/-- Exhaustive descriptor-free failure of the resolved Rule-6 adapter, including missing
promoted rankings as well as completed semantic disagreement. -/
def AuthoritativeResolvedRule6TotalSemanticFailure
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List Nat) (adjacent : List (Option Ordering)) : Prop :=
  let ligands := mol.ligandsWithLonePair node.atom
  let backend := authoritativeOccurrenceRule6PositionRankingBackend
    mol state fuel roots ligands
  let groupCount := rule6GroupCount adjacent
  (groupCount = 1 ∧
      ¬AuthoritativeRule6FourWayBranchAgreement backend sorted) ∨
    (groupCount = 2 ∧
      ¬Rule6ReferenceFamilyBranchAgreement backend
        (rule6EquivalentReferencePositions sorted adjacent)) ∨
    (groupCount = 3 ∧
      (roots[sorted[1]?.getD 0]? = none ∨
        ∃ referenceRoot,
          roots[sorted[1]?.getD 0]? = some referenceRoot ∧
          adjacent[1]?.getD none = some Ordering.eq ∧
          occurrenceBranchHasLocalReference (mol := mol) state fuel [referenceRoot] = true ∧
          ¬Rule6ReferenceFamilyBranchAgreement backend
            (rule6ThreeGroupReferencePositions sorted)))

/-- Unconditional resolved refusal theorem.  No operational-domain premise, result-success
premise, or descriptor-valued semantic predicate remains. -/
theorem authoritativeResolvedRule6Stereogenicity?_eq_none_iff_totalSemanticFailure
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List Nat) (adjacent : List (Option Ordering)) :
    authoritativeResolvedRule6Stereogenicity?
        mol state fuel node roots sorted adjacent = none ↔
      AuthoritativeResolvedRule6TotalSemanticFailure
        mol state fuel node roots sorted adjacent := by
  let ligands := mol.ligandsWithLonePair node.atom
  let backend := authoritativeOccurrenceRule6PositionRankingBackend
    mol state fuel roots ligands
  let groupCount := rule6GroupCount adjacent
  change authoritativeResolvedRule6Stereogenicity?
      mol state fuel node roots sorted adjacent = none ↔
    (groupCount = 1 ∧
        ¬AuthoritativeRule6FourWayBranchAgreement backend sorted) ∨
      (groupCount = 2 ∧
        ¬Rule6ReferenceFamilyBranchAgreement backend
          (rule6EquivalentReferencePositions sorted adjacent)) ∨
      (groupCount = 3 ∧
        (roots[sorted[1]?.getD 0]? = none ∨
          ∃ referenceRoot,
            roots[sorted[1]?.getD 0]? = some referenceRoot ∧
            adjacent[1]?.getD none = some Ordering.eq ∧
            occurrenceBranchHasLocalReference (mol := mol) state fuel [referenceRoot] = true ∧
            ¬Rule6ReferenceFamilyBranchAgreement backend
              (rule6ThreeGroupReferencePositions sorted)))
  have fourWay :=
    authoritativeOccurrenceRule6FourWayDescriptor?_eq_none_iff_not_branchAgreement
      backend .clockwise sorted
  have twoGroup := rule6FamilyDescriptorWithBackend?_eq_none_iff_not_branchAgreement
    backend .clockwise (rule6EquivalentReferencePositions sorted adjacent)
  have threeGroup :=
    authoritativeOccurrenceRule6ThreeGroupDescriptor?_eq_none_iff_not_branchAgreement
      mol state fuel roots ligands sorted .clockwise
  by_cases groupOne : groupCount = 1
  · have groupTwo : groupCount ≠ 2 := by omega
    have groupThree : groupCount ≠ 3 := by omega
    simpa [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
      groupOne, groupTwo, groupThree] using fourWay
  · by_cases groupTwo : groupCount = 2
    · have groupThree : groupCount ≠ 3 := by omega
      simpa [authoritativeResolvedRule6Stereogenicity?,
        authoritativeOccurrenceRule6TwoGroupDescriptor?,
        authoritativeOccurrenceRule6PositionFamilyDescriptor?, ligands, backend, groupCount,
        groupOne, groupTwo, groupThree] using twoGroup
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
              · simpa [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
                  groupOne, groupTwo, groupThree, reference, referenceRootEq,
                  middleTie, localReference] using threeGroup
              · simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
                  groupOne, groupTwo, groupThree, reference, referenceRootEq,
                  middleTie, localReference]
            · simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
                groupOne, groupTwo, groupThree, reference, referenceRootEq, middleTie]
      · simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
          groupOne, groupTwo, groupThree]

/-- Public resolved `rankingUnresolved` is exactly the unconditional total semantic failure. -/
theorem authoritativeResolvedRule6UnannotatedOutcome?_eq_rankingUnresolved_iff_totalSemanticFailure
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List Nat) (adjacent : List (Option Ordering)) :
    authoritativeResolvedRule6UnannotatedOutcome?
        mol state fuel node roots sorted adjacent = some (.refused .rankingUnresolved) ↔
      AuthoritativeResolvedRule6TotalSemanticFailure
        mol state fuel node roots sorted adjacent := by
  cases computed : authoritativeResolvedRule6Stereogenicity?
      mol state fuel node roots sorted adjacent with
  | none =>
      simp [authoritativeResolvedRule6UnannotatedOutcome?, computed,
        (authoritativeResolvedRule6Stereogenicity?_eq_none_iff_totalSemanticFailure
          mol state fuel node roots sorted adjacent).mp computed]
  | some decision =>
      have noFailure : ¬AuthoritativeResolvedRule6TotalSemanticFailure
          mol state fuel node roots sorted adjacent := by
        intro failure
        have absent :=
          (authoritativeResolvedRule6Stereogenicity?_eq_none_iff_totalSemanticFailure
            mol state fuel node roots sorted adjacent).mpr failure
        rw [computed] at absent
        contradiction
      cases decision <;>
        simp [authoritativeResolvedRule6UnannotatedOutcome?, computed, noFailure]

/-- A fully reached source frame whose resolved P-92 branch is unavailable or disagrees. -/
def AuthoritativeSourceRule6PromotedTotalSemanticFailure
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
    AuthoritativeResolvedRule6TotalSemanticFailure
      mol aux fuel node roots sorted adjacent

/-- Exhaustive source-level unresolved meaning, with no operational premise. -/
def AuthoritativeSourceRule6TotalSemanticUnresolved
    (mol : RawMolecule) (fuel center : Nat) : Prop :=
  AuthoritativeSourceRule6ConstructionFailure mol fuel center ∨
    AuthoritativeSourceRule6InitialSortFailure mol fuel center ∨
    AuthoritativeSourceRule6AdjacentComparisonFailure mol fuel center ∨
    AuthoritativeSourceRule6NoncanonicalInitialOrder mol fuel center ∨
    AuthoritativeSourceRule6TopologyFailure mol fuel center ∨
    AuthoritativeSourceRule6PromotedTotalSemanticFailure mol fuel center

/-- Every source `none` is exactly one of the five primitive construction failures or the
descriptor-free total promoted failure. -/
theorem authoritativeSourceRule6Stereogenicity?_eq_none_iff_totalSemanticUnresolved
    (mol : RawMolecule) (fuel center : Nat) :
    authoritativeSourceRule6Stereogenicity? mol fuel center = none ↔
      AuthoritativeSourceRule6TotalSemanticUnresolved mol fuel center := by
  let node := canonicalCenterRoot center
  let ligands := mol.ligandsWithLonePair center
  let roots := authoritativeSourceRule6LigandCursors mol center
  constructor
  · intro computed
    by_cases ligandsLength : ligands.length = 4
    · cases auxEq : buildOccurrenceAuxStateFullyAuthoritative? mol fuel center with
      | none => exact Or.inl ⟨ligandsLength, auxEq⟩
      | some aux =>
          cases sortedEq : sortAuthoritativeRule6InitialPositions?
              mol aux fuel roots (List.range 4) with
          | none => exact Or.inr (Or.inl ⟨aux, ligandsLength, auxEq, sortedEq⟩)
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
                          have failure :=
                            (authoritativeResolvedRule6Stereogenicity?_eq_none_iff_totalSemanticFailure
                              mol aux fuel node roots sorted adjacent).mp resolvedNone
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                            ⟨aux, sorted, adjacent, ligandsLength, auxEq, sortedEq,
                              adjacentEq, adjacentLt,
                              by simpa [initialBefore] using oddEq, failure⟩))))
                        · simp [authoritativeSourceRule6Stereogenicity?, node,
                            ligands, roots, ligandsLength, auxEq, sortedEq,
                            adjacentEq, adjacentLt, initialBefore, oddEq] at computed
    · simp [authoritativeSourceRule6Stereogenicity?, node,
        ligands, roots, ligandsLength] at computed
  · rintro (construction | initialSort | adjacentComparison |
      noncanonicalOrder | topologyFailure | promotedFailure)
    · rcases construction with ⟨ligandsLength, auxEq⟩
      simp [authoritativeSourceRule6Stereogenicity?, node,
        ligands, roots, ligandsLength, auxEq]
    · rcases initialSort with ⟨aux, ligandsLength, auxEq, sortedEq⟩
      simp [authoritativeSourceRule6Stereogenicity?, node,
        ligands, roots, ligandsLength, auxEq, sortedEq]
    · rcases adjacentComparison with
        ⟨aux, sorted, ligandsLength, auxEq, sortedEq, adjacentEq⟩
      simp [authoritativeSourceRule6Stereogenicity?, node,
        ligands, roots, ligandsLength, auxEq, sortedEq, adjacentEq]
    · rcases noncanonicalOrder with
        ⟨aux, sorted, adjacent, ligandsLength, auxEq, sortedEq, adjacentEq, adjacentLt⟩
      simp [authoritativeSourceRule6Stereogenicity?, node,
        ligands, roots, ligandsLength, auxEq, sortedEq, adjacentEq, adjacentLt]
    · rcases topologyFailure with
        ⟨aux, sorted, adjacent, ligandsLength, auxEq, sortedEq, adjacentEq,
          adjacentLt, oddEq⟩
      simp [authoritativeSourceRule6Stereogenicity?, node,
        ligands, roots, ligandsLength, auxEq, sortedEq, adjacentEq, adjacentLt, oddEq]
    · rcases promotedFailure with
        ⟨aux, sorted, adjacent, ligandsLength, auxEq, sortedEq, adjacentEq,
          adjacentLt, oddEq, failure⟩
      have resolvedNone :=
        (authoritativeResolvedRule6Stereogenicity?_eq_none_iff_totalSemanticFailure
          mol aux fuel node roots sorted adjacent).mpr failure
      simpa [authoritativeSourceRule6Stereogenicity?, node,
        ligands, roots, ligandsLength, auxEq, sortedEq, adjacentEq, adjacentLt,
        oddEq] using resolvedNone

/-- The source public adapter reports `rankingUnresolved` exactly for the unconditional source
classification. -/
theorem authoritativeSourceRule6UnannotatedOutcome?_eq_rankingUnresolved_iff_totalSemanticUnresolved
    (mol : RawMolecule) (fuel center : Nat) :
    authoritativeSourceRule6UnannotatedOutcome? mol fuel center =
        some (.refused .rankingUnresolved) ↔
      AuthoritativeSourceRule6TotalSemanticUnresolved mol fuel center := by
  cases computed : authoritativeSourceRule6Stereogenicity? mol fuel center with
  | none =>
      simp [authoritativeSourceRule6UnannotatedOutcome?, computed,
        (authoritativeSourceRule6Stereogenicity?_eq_none_iff_totalSemanticUnresolved
          mol fuel center).mp computed]
  | some decision =>
      have noFailure : ¬AuthoritativeSourceRule6TotalSemanticUnresolved mol fuel center := by
        intro failure
        have absent :=
          (authoritativeSourceRule6Stereogenicity?_eq_none_iff_totalSemanticUnresolved
            mol fuel center).mpr failure
        rw [computed] at absent
        contradiction
      cases decision <;>
        simp [authoritativeSourceRule6UnannotatedOutcome?, computed, noFailure]

end AuthoritativeCIPRule6Scheduler
end TetraStereo.OneCenter

namespace TetraStereo.OneCenter
namespace AuthoritativeCIPRule6Scheduler

open RawMolecule

/-! ## Replacement judgments through the normalized analyzer -/

/-- Semantic replacement for the old ranking-unresolved predicate.  The primitive tetrahedral
dispatch conditions are retained literally; the final opaque source `none` is replaced by the
unconditional source classification proved above. -/
def AuthoritativeUnannotatedTetrahedralTotalSemanticRankingUnresolved
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) : Prop :=
  ∃ spec,
    result.parsed.atomAt? center = some spec ∧
    spec.tetrahedral? = none ∧
    BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame result mol center ∧
    rankBranchPositionsThroughOfficialContext?
        result mol state fuel center (mol.writtenNeighbors center) = none ∧
    hasTerminalTetrahedralTie result mol state fuel center
        (mol.writtenNeighbors center) = false ∧
    AuthoritativeSourceRule6TotalSemanticUnresolved mol fuel center

/-- The former executable-none predicate and the unconditional semantic replacement are exactly
equivalent. -/
theorem authoritativeUnannotatedTetrahedralRankingUnresolved_iff_totalSemantic
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) :
    AuthoritativeUnannotatedTetrahedralRankingUnresolved result mol state fuel center ↔
      AuthoritativeUnannotatedTetrahedralTotalSemanticRankingUnresolved
        result mol state fuel center := by
  unfold AuthoritativeUnannotatedTetrahedralRankingUnresolved
    AuthoritativeUnannotatedTetrahedralTotalSemanticRankingUnresolved
  constructor
  · rintro ⟨spec, atomEq, parityEq, frame, rankingEq, tieEq, sourceNone⟩
    exact ⟨spec, atomEq, parityEq, frame, rankingEq, tieEq,
      (authoritativeSourceRule6Stereogenicity?_eq_none_iff_totalSemanticUnresolved
        mol fuel center).mp sourceNone⟩
  · rintro ⟨spec, atomEq, parityEq, frame, rankingEq, tieEq, semantic⟩
    exact ⟨spec, atomEq, parityEq, frame, rankingEq, tieEq,
      (authoritativeSourceRule6Stereogenicity?_eq_none_iff_totalSemanticUnresolved
        mol fuel center).mpr semantic⟩

/-- Exact one-center public refusal theorem with no operational premise. -/
theorem unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_rankingUnresolved_iff_totalSemantic
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) :
    unannotatedTetrahedralOutcomeWithAuthoritativeRule6?
        result mol state fuel center = some (.refused .rankingUnresolved) ↔
      AuthoritativeUnannotatedTetrahedralTotalSemanticRankingUnresolved
        result mol state fuel center :=
  (unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_rankingUnresolved_iff
    result mol state fuel center).trans
      (authoritativeUnannotatedTetrahedralRankingUnresolved_iff_totalSemantic
        result mol state fuel center)

/-- Assignment-level unannotated judgment with the total semantic refusal clause. -/
def AuthoritativeUnannotatedTetrahedralTotalSemanticAssignmentJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (assignment : StereoAssignment) : Prop :=
  (assignment =
      { unit := .tetrahedral center, outcome := .refused .notSpecified } ∧
    AuthoritativeUnannotatedTetrahedralStereogenic
      result mol state fuel center) ∨
  (assignment =
      { unit := .tetrahedral center, outcome := .refused .rankingUnresolved } ∧
    AuthoritativeUnannotatedTetrahedralTotalSemanticRankingUnresolved
      result mol state fuel center)

theorem authoritativeUnannotatedTetrahedralAssignmentJudgment_iff_totalSemantic
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) (assignment : StereoAssignment) :
    AuthoritativeUnannotatedTetrahedralAssignmentJudgment
        result mol state fuel center assignment ↔
      AuthoritativeUnannotatedTetrahedralTotalSemanticAssignmentJudgment
        result mol state fuel center assignment := by
  unfold AuthoritativeUnannotatedTetrahedralAssignmentJudgment
    AuthoritativeUnannotatedTetrahedralTotalSemanticAssignmentJudgment
  constructor
  · rintro (specified | unresolved)
    · exact Or.inl specified
    · exact Or.inr ⟨unresolved.1,
        (authoritativeUnannotatedTetrahedralRankingUnresolved_iff_totalSemantic
          result mol state fuel center).mp unresolved.2⟩
  · rintro (specified | unresolved)
    · exact Or.inl specified
    · exact Or.inr ⟨unresolved.1,
        (authoritativeUnannotatedTetrahedralRankingUnresolved_iff_totalSemantic
          result mol state fuel center).mpr unresolved.2⟩

/-- Exact executable assignment theorem against the total semantic judgment. -/
theorem unannotatedTetrahedralAssignmentWithAuthoritativeRule6?_eq_some_iff_totalSemantic
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) (assignment : StereoAssignment) :
    unannotatedTetrahedralAssignmentWithAuthoritativeRule6?
        result mol state fuel center = some assignment ↔
      AuthoritativeUnannotatedTetrahedralTotalSemanticAssignmentJudgment
        result mol state fuel center assignment :=
  (unannotatedTetrahedralAssignmentWithAuthoritativeRule6?_eq_some_iff
    result mol state fuel center assignment).trans
      (authoritativeUnannotatedTetrahedralAssignmentJudgment_iff_totalSemantic
        result mol state fuel center assignment)

/-- Annotated centers retain their existing P-93 judgment; only the unannotated refusal clause is
semantically refined. -/
def AuthoritativePublicTetrahedralTotalSemanticAssignmentJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (assignment : StereoAssignment) : Prop :=
  match result.parsed.atomAt? center with
  | none => False
  | some spec =>
      match spec.tetrahedral? with
      | none =>
          AuthoritativeUnannotatedTetrahedralTotalSemanticAssignmentJudgment
            result mol state fuel center assignment
      | some _ =>
          BlueBookP93.Acyclic.AnnotatedTetrahedralAssignmentJudgment
            result mol state fuel center assignment

theorem authoritativePublicTetrahedralAssignmentJudgment_iff_totalSemantic
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) (assignment : StereoAssignment) :
    AuthoritativePublicTetrahedralAssignmentJudgment
        result mol state fuel center assignment ↔
      AuthoritativePublicTetrahedralTotalSemanticAssignmentJudgment
        result mol state fuel center assignment := by
  unfold AuthoritativePublicTetrahedralAssignmentJudgment
    AuthoritativePublicTetrahedralTotalSemanticAssignmentJudgment
  cases atomEq : result.parsed.atomAt? center with
  | none => simp [atomEq]
  | some spec =>
      cases parityEq : spec.tetrahedral? with
      | none =>
          simpa [atomEq, parityEq] using
            (authoritativeUnannotatedTetrahedralAssignmentJudgment_iff_totalSemantic
              result mol state fuel center assignment)
      | some parity => simp [atomEq, parityEq]

/-- Complete five-branch normalized judgment with the unconditional semantic Rule-6 refusal. -/
def TotalSemanticallyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) : Prop :=
  let mol := result.parsed.withExplicitHydrogens
  let fuel := analysisFuel mol
  let state := discoverRawDescriptors result mol fuel
  let geometryState := normalizedGeometryDescriptorState result mol fuel state
  (∃ center < result.parsed.atomCount,
      AuthoritativePublicTetrahedralTotalSemanticAssignmentJudgment
        result mol state fuel center assignment) ∨
    (∃ record ∈ result.stereobonds.doubleBondAssignments,
      BlueBookP93.Acyclic.OrdinaryDoubleBondAssignmentJudgment
        result mol state fuel record assignment) ∨
    IndependentlyJudgedNormalizedDescriptorDependentDoubleBondAssignment result assignment ∨
      (∃ chain ∈ result.parsed.extendedDoubleBondChains,
        BlueBookP93.Acyclic.OddCumuleneDoubleBondAssignmentJudgment
          result mol geometryState fuel chain assignment) ∨
        ∃ carrier ∈ mol.extendedTetrahedralParityCarriers,
          BlueBookP93.Acyclic.ExtendedTetrahedralAxialAssignmentJudgment
            result mol geometryState fuel carrier assignment

theorem independentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6_iff_totalSemantic
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) :
    IndependentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6 result assignment ↔
      TotalSemanticallyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6
        result assignment := by
  unfold IndependentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6
    TotalSemanticallyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6
  constructor
  · rintro (tetrahedral | remaining)
    · left
      obtain ⟨center, bound, judged⟩ := tetrahedral
      exact ⟨center, bound,
        (authoritativePublicTetrahedralAssignmentJudgment_iff_totalSemantic
          result result.parsed.withExplicitHydrogens
            (discoverRawDescriptors result result.parsed.withExplicitHydrogens
              (analysisFuel result.parsed.withExplicitHydrogens))
            (analysisFuel result.parsed.withExplicitHydrogens) center assignment).mp judged⟩
    · exact Or.inr remaining
  · rintro (tetrahedral | remaining)
    · left
      obtain ⟨center, bound, judged⟩ := tetrahedral
      exact ⟨center, bound,
        (authoritativePublicTetrahedralAssignmentJudgment_iff_totalSemantic
          result result.parsed.withExplicitHydrogens
            (discoverRawDescriptors result result.parsed.withExplicitHydrogens
              (analysisFuel result.parsed.withExplicitHydrogens))
            (analysisFuel result.parsed.withExplicitHydrogens) center assignment).mpr judged⟩
    · exact Or.inr remaining

/-- Exact normalized public membership against the unconditional semantic specification. -/
theorem mem_analyzeNormalizedWithAuthoritativeRule6_iff_totalSemanticallyJudged
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) :
    assignment ∈ analyzeNormalizedWithAuthoritativeRule6 result ↔
      result.parsed.rule2MassesKnown? = true ∧
      result.expandedStereochemicalAdmissible? = true ∧
      TotalSemanticallyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6
        result assignment :=
  (mem_analyzeNormalizedWithAuthoritativeRule6_iff_independently_judged
    result assignment).trans
      (and_congr Iff.rfl (and_congr Iff.rfl
        (independentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6_iff_totalSemantic
          result assignment)))

end AuthoritativeCIPRule6Scheduler

open RawMolecule
open AuthoritativeCIPRule6Scheduler

/-! ## Transport through occurrence override and the final spatial analyzer -/

/-- Native occurrence-override judgment with the total semantic normalized base. -/
def TotalSemanticRule6OccurrenceNativeAssignmentJudgment
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) : Prop :=
  ∃ base,
    result.parsed.rule2MassesKnown? = true ∧
    result.expandedStereochemicalAdmissible? = true ∧
    TotalSemanticallyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6 result base ∧
    AuthoritativeOccurrenceOverrideJudgment result base assignment

theorem authoritativeRule6OccurrenceNativeAssignmentJudgment_iff_totalSemantic
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) :
    AuthoritativeRule6OccurrenceNativeAssignmentJudgment result assignment ↔
      TotalSemanticRule6OccurrenceNativeAssignmentJudgment result assignment := by
  unfold AuthoritativeRule6OccurrenceNativeAssignmentJudgment
    TotalSemanticRule6OccurrenceNativeAssignmentJudgment
  constructor
  · rintro ⟨base, masses, admissible, judged, override⟩
    exact ⟨base, masses, admissible,
      (independentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6_iff_totalSemantic
        result base).mp judged, override⟩
  · rintro ⟨base, masses, admissible, judged, override⟩
    exact ⟨base, masses, admissible,
      (independentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6_iff_totalSemantic
        result base).mpr judged, override⟩

/-- Observed-geometry policy with the refined native prefix. -/
def TotalSemanticRule6ObservedGeometryPublicAssignmentJudgment
    (certified : CertifiedChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations)
    (assignment : StereoAssignment) : Prop :=
  let native := analyzeCertifiedNormalizedWithAuthoritativeRule6 certified
  let observed := observedGeometryAssignments certified.result observations native
  (TotalSemanticRule6OccurrenceNativeAssignmentJudgment certified.result assignment ∧
      NativeAssignmentNotReplacedByObservedPolyhedron observed assignment) ∨
    ObservedGeometryAssignmentsPolicyJudgment
      certified.result observations native assignment

theorem authoritativeRule6ObservedGeometryPublicAssignmentJudgment_iff_totalSemantic
    (certified : CertifiedChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations) (assignment : StereoAssignment) :
    AuthoritativeRule6ObservedGeometryPublicAssignmentJudgment
        certified observations assignment ↔
      TotalSemanticRule6ObservedGeometryPublicAssignmentJudgment
        certified observations assignment := by
  unfold AuthoritativeRule6ObservedGeometryPublicAssignmentJudgment
    TotalSemanticRule6ObservedGeometryPublicAssignmentJudgment
  exact or_congr
    (and_congr
      (authoritativeRule6OccurrenceNativeAssignmentJudgment_iff_totalSemantic
        certified.result assignment) Iff.rfl)
    Iff.rfl

/-- Final coordinate-derived public judgment with the unconditional semantic Rule-6 refusal. -/
def TotalSemanticAuthoritativeRule6DerivedSpatialPublicAssignmentJudgment
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) : Prop :=
  let rawHelixFree := observations.withoutRawHelices
  let filtered := rawHelixFree.withoutRawPlanesAfterSpatialValidation certified.result spatial
  TotalSemanticRule6ObservedGeometryPublicAssignmentJudgment certified filtered assignment ∨
    BlueBookP93.GeometryIngress.AuthoritativeRule6PlanarDerivedPublicContributionJudgment
      certified spatial rawHelixFree derivedPlanes assignment ∨
    BlueBookP93.GeometryIngress.AuthoritativeRule6CoordinateDerivedHelicalPublicContributionJudgment
      certified spatial observations derivedPlanes derivedHelices assignment

theorem authoritativeRule6DerivedSpatialPublicAssignmentJudgment_iff_totalSemantic
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) :
    AuthoritativeRule6DerivedSpatialPublicAssignmentJudgment certified spatial observations
        derivedPlanes derivedHelices assignment ↔
      TotalSemanticAuthoritativeRule6DerivedSpatialPublicAssignmentJudgment
        certified spatial observations derivedPlanes derivedHelices assignment := by
  unfold AuthoritativeRule6DerivedSpatialPublicAssignmentJudgment
    TotalSemanticAuthoritativeRule6DerivedSpatialPublicAssignmentJudgment
  exact or_congr
    (authoritativeRule6ObservedGeometryPublicAssignmentJudgment_iff_totalSemantic
      certified
        (observations.withoutRawHelices.withoutRawPlanesAfterSpatialValidation
          certified.result spatial) assignment)
    Iff.rfl

/-- Exact final public theorem: every coordinate-derived assignment, including
`rankingUnresolved`, is characterized without an opaque source `none` or an operational-domain
premise. -/
theorem
    mem_analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedSpatialGeometry_iff_totalSemantic
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration) (observations : IndexedCIPGeometryObservations)
    (derivedPlanes : List IndexedPlanarDerivedTetrahedronObservation)
    (derivedHelices : List IndexedHelicalGeometryObservation)
    (assignment : StereoAssignment) :
    assignment ∈
        analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedPlanarHelicalSpatialGeometry
          certified spatial observations derivedPlanes derivedHelices ↔
      TotalSemanticAuthoritativeRule6DerivedSpatialPublicAssignmentJudgment
        certified spatial observations derivedPlanes derivedHelices assignment :=
  (mem_analyzeCertifiedNormalizedWithAuthoritativeRule6DerivedSpatialGeometry_iff_publicJudgment
    certified spatial observations derivedPlanes derivedHelices assignment).trans
      (authoritativeRule6DerivedSpatialPublicAssignmentJudgment_iff_totalSemantic
        certified spatial observations derivedPlanes derivedHelices assignment)

end TetraStereo.OneCenter
