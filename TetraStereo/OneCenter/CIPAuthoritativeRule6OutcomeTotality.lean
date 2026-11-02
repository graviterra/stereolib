import TetraStereo.OneCenter.CIPAuthoritativeRule6TotalSemanticRefusal

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter
namespace AuthoritativeCIPRule6Scheduler

open RawMolecule
open DeclarativeCIP
open DeclarativeCIP.ProductionOccurrenceRules456
open ProductionCIPOccurrenceDiscovery
open AuthoritativeCIPRule6P92Enumeration
open Rule6ReferenceFamilySemantics

/-!
# Total semantic outcomes for source-level Rule 6

The existing source semantics identify successful stereogenic perception and every unresolved
execution branch.  This module supplies the missing exact meaning of the executable `some false`
branch.  The three meanings are consequently exhaustive on every input: stereogenic,
nonstereogenic, or semantically unresolved.
-/

/-- Exact resolved-frame meaning of a negative Rule-6 stereogenicity decision.

A resolved frame is negatively decided either because the Rules-1a--5 partition is outside the
one-, two-, and three-group Rule-6 cases, or because a three-group frame has its middle root but
lacks the required middle tie or local reference.  Failed promoted comparisons are deliberately
not included: they have the already-proved unresolved meaning. -/
def AuthoritativeResolvedRule6Nonstereogenic
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor)
    (sorted : List Nat) (adjacent : List (Option Ordering)) : Prop :=
  let groupCount := rule6GroupCount adjacent
  (groupCount = 3 ∧
      ∃ referenceRoot,
        roots[sorted[1]?.getD 0]? = some referenceRoot ∧
        (adjacent[1]?.getD none ≠ some Ordering.eq ∨
          occurrenceBranchHasLocalReference
              (mol := mol) state fuel [referenceRoot] ≠ true)) ∨
    (groupCount ≠ 1 ∧ groupCount ≠ 2 ∧ groupCount ≠ 3)

/-- The resolved executable returns `some false` exactly for the explicit negative semantic
case. -/
theorem authoritativeResolvedRule6Stereogenicity?_eq_some_false_iff
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List Nat) (adjacent : List (Option Ordering)) :
    authoritativeResolvedRule6Stereogenicity?
        mol state fuel node roots sorted adjacent = some false ↔
      AuthoritativeResolvedRule6Nonstereogenic
        mol state fuel roots sorted adjacent := by
  let ligands := mol.ligandsWithLonePair node.atom
  let backend := authoritativeOccurrenceRule6PositionRankingBackend
    mol state fuel roots ligands
  let groupCount := rule6GroupCount adjacent
  change authoritativeResolvedRule6Stereogenicity?
      mol state fuel node roots sorted adjacent = some false ↔
    (groupCount = 3 ∧
        ∃ referenceRoot,
          roots[sorted[1]?.getD 0]? = some referenceRoot ∧
          (adjacent[1]?.getD none ≠ some Ordering.eq ∨
            occurrenceBranchHasLocalReference
                (mol := mol) state fuel [referenceRoot] ≠ true)) ∨
      (groupCount ≠ 1 ∧ groupCount ≠ 2 ∧ groupCount ≠ 3)
  by_cases groupOne : groupCount = 1
  · have groupTwo : groupCount ≠ 2 := by omega
    have groupThree : groupCount ≠ 3 := by omega
    simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
      groupOne, groupTwo, groupThree]
  · by_cases groupTwo : groupCount = 2
    · have groupThree : groupCount ≠ 3 := by omega
      simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
        groupOne, groupTwo, groupThree]
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
                  middleTie, localReference]
              · simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
                  groupOne, groupTwo, groupThree, reference, referenceRootEq,
                  middleTie, localReference]
            · simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
                groupOne, groupTwo, groupThree, reference, referenceRootEq, middleTie]
      · simp [authoritativeResolvedRule6Stereogenicity?, ligands, backend, groupCount,
          groupOne, groupTwo, groupThree]

/-- Exact source-center meaning of a negative Rule-6 stereogenicity decision.

The source can decide negatively for three disjoint operational reasons: the center has no
four-position tetrahedral frame, an odd partition-preserving constitutional automorphism is
present, or the fully constructed frame reaches the resolved negative case above. -/
def AuthoritativeSourceRule6Nonstereogenic
    (mol : RawMolecule) (fuel center : Nat) : Prop :=
  let ligands := mol.ligandsWithLonePair center
  let roots := authoritativeSourceRule6LigandCursors mol center
  ligands.length ≠ 4 ∨
    ∃ aux sorted adjacent,
      ligands.length = 4 ∧
      buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = some aux ∧
      sortAuthoritativeRule6InitialPositions?
        mol aux fuel roots (List.range 4) = some sorted ∧
      compareAuthoritativeRule6InitialAdjacent?
        mol aux fuel roots sorted = some adjacent ∧
      some Ordering.lt ∉ adjacent ∧
      (hasOddConstitutionAutomorphismAtCenter mol center ligands
          (fun left right =>
            (compareAuthoritativeRule6InitialPositions?
              mol aux fuel roots left right).any
                fun decision => decision.ordering = Ordering.eq) = some true ∨
        (hasOddConstitutionAutomorphismAtCenter mol center ligands
            (fun left right =>
              (compareAuthoritativeRule6InitialPositions?
                mol aux fuel roots left right).any
                  fun decision => decision.ordering = Ordering.eq) = some false ∧
            AuthoritativeResolvedRule6Nonstereogenic
            mol aux fuel roots sorted adjacent))

/-- Source Rule 6 returns `some false` exactly for the explicit nonstereogenic meaning. -/
theorem authoritativeSourceRule6Stereogenicity?_eq_some_false_iff
    (mol : RawMolecule) (fuel center : Nat) :
    authoritativeSourceRule6Stereogenicity? mol fuel center = some false ↔
      AuthoritativeSourceRule6Nonstereogenic mol fuel center := by
  let node := canonicalCenterRoot center
  let ligands := mol.ligandsWithLonePair center
  let roots := authoritativeSourceRule6LigandCursors mol center
  change authoritativeSourceRule6Stereogenicity? mol fuel center = some false ↔
    ligands.length ≠ 4 ∨
      ∃ aux sorted adjacent,
        ligands.length = 4 ∧
        buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = some aux ∧
        sortAuthoritativeRule6InitialPositions?
          mol aux fuel roots (List.range 4) = some sorted ∧
        compareAuthoritativeRule6InitialAdjacent?
          mol aux fuel roots sorted = some adjacent ∧
        some Ordering.lt ∉ adjacent ∧
        (hasOddConstitutionAutomorphismAtCenter mol center ligands
            (fun left right =>
              (compareAuthoritativeRule6InitialPositions?
                mol aux fuel roots left right).any
                  fun decision => decision.ordering = Ordering.eq) = some true ∨
          (hasOddConstitutionAutomorphismAtCenter mol center ligands
              (fun left right =>
                (compareAuthoritativeRule6InitialPositions?
                  mol aux fuel roots left right).any
                    fun decision => decision.ordering = Ordering.eq) = some false ∧
            AuthoritativeResolvedRule6Nonstereogenic
              mol aux fuel roots sorted adjacent))
  constructor
  · intro computed
    by_cases ligandsLength : ligands.length = 4
    · right
      cases auxEq : buildOccurrenceAuxStateFullyAuthoritative? mol fuel center with
      | none => simp [authoritativeSourceRule6Stereogenicity?, ligands,
          ligandsLength, auxEq] at computed
      | some aux =>
          cases sortedEq : sortAuthoritativeRule6InitialPositions?
              mol aux fuel roots (List.range 4) with
          | none => simp [authoritativeSourceRule6Stereogenicity?, ligands, roots,
              ligandsLength, auxEq, sortedEq] at computed
          | some sorted =>
              cases adjacentEq : compareAuthoritativeRule6InitialAdjacent?
                  mol aux fuel roots sorted with
              | none => simp [authoritativeSourceRule6Stereogenicity?, ligands, roots,
                  ligandsLength, auxEq, sortedEq, adjacentEq] at computed
              | some adjacent =>
                  by_cases adjacentLt : some Ordering.lt ∈ adjacent
                  · simp [authoritativeSourceRule6Stereogenicity?, ligands, roots,
                      ligandsLength, auxEq, sortedEq, adjacentEq, adjacentLt] at computed
                  · let initialBefore := fun left right =>
                      (compareAuthoritativeRule6InitialPositions?
                        mol aux fuel roots left right).any
                          fun decision => decision.ordering = Ordering.eq
                    cases oddEq : hasOddConstitutionAutomorphismAtCenter
                        mol center ligands initialBefore with
                    | none => simp [authoritativeSourceRule6Stereogenicity?, ligands, roots,
                        ligandsLength, auxEq, sortedEq, adjacentEq, adjacentLt,
                        initialBefore, oddEq] at computed
                    | some odd =>
                        cases odd
                        · have resolved :=
                            (authoritativeResolvedRule6Stereogenicity?_eq_some_false_iff
                              mol aux fuel node roots sorted adjacent).mp (by
                                simpa [authoritativeSourceRule6Stereogenicity?, ligands, roots,
                                  ligandsLength, auxEq, sortedEq, adjacentEq, adjacentLt,
                                  initialBefore, oddEq] using computed)
                          exact ⟨aux, sorted, adjacent, ligandsLength, rfl, sortedEq,
                            adjacentEq, adjacentLt, Or.inr ⟨by simpa [initialBefore] using oddEq,
                              resolved⟩⟩
                        · exact ⟨aux, sorted, adjacent, ligandsLength, rfl, sortedEq,
                            adjacentEq, adjacentLt,
                            Or.inl (by simpa [initialBefore] using oddEq)⟩
    · exact Or.inl ligandsLength
  · rintro (ligandsLength | ⟨aux, sorted, adjacent, ligandsLength, auxEq,
      sortedEq, adjacentEq, adjacentLt, odd⟩)
    · simp [authoritativeSourceRule6Stereogenicity?, ligands, ligandsLength]
    · rcases odd with oddTrue | ⟨oddFalse, resolved⟩
      · simp [authoritativeSourceRule6Stereogenicity?, node, ligands, roots,
          ligandsLength, auxEq, sortedEq, adjacentEq, adjacentLt, oddTrue]
      · have resolvedEq :=
          (authoritativeResolvedRule6Stereogenicity?_eq_some_false_iff
            mol aux fuel node roots sorted adjacent).mpr resolved
        simpa [authoritativeSourceRule6Stereogenicity?, node, ligands, roots,
          ligandsLength, auxEq, sortedEq, adjacentEq, adjacentLt, oddFalse]
          using resolvedEq

/-- Every source-level Rule-6 computation has at least one of the three chemically meaningful
outcome classes. -/
theorem authoritativeSourceRule6SemanticOutcome_total
    (mol : RawMolecule) (fuel center : Nat) :
    AuthoritativeSourceRule6Stereogenic mol fuel center ∨
      AuthoritativeSourceRule6Nonstereogenic mol fuel center ∨
      AuthoritativeSourceRule6TotalSemanticUnresolved mol fuel center := by
  cases computed : authoritativeSourceRule6Stereogenicity? mol fuel center with
  | none =>
      exact Or.inr (Or.inr
        ((authoritativeSourceRule6Stereogenicity?_eq_none_iff_totalSemanticUnresolved
          mol fuel center).mp computed))
  | some decision =>
      cases decision
      · exact Or.inr (Or.inl
          ((authoritativeSourceRule6Stereogenicity?_eq_some_false_iff
            mol fuel center).mp computed))
      · exact Or.inl
          ((authoritativeSourceRule6Stereogenicity?_eq_some_true_iff
            mol fuel center).mp computed)

/-- The three total source meanings are exhaustive and pairwise exclusive. -/
theorem authoritativeSourceRule6SemanticOutcome_exactlyOne
    (mol : RawMolecule) (fuel center : Nat) :
    (AuthoritativeSourceRule6Stereogenic mol fuel center ∨
        AuthoritativeSourceRule6Nonstereogenic mol fuel center ∨
        AuthoritativeSourceRule6TotalSemanticUnresolved mol fuel center) ∧
      ¬(AuthoritativeSourceRule6Stereogenic mol fuel center ∧
          AuthoritativeSourceRule6Nonstereogenic mol fuel center) ∧
      ¬(AuthoritativeSourceRule6Stereogenic mol fuel center ∧
          AuthoritativeSourceRule6TotalSemanticUnresolved mol fuel center) ∧
      ¬(AuthoritativeSourceRule6Nonstereogenic mol fuel center ∧
          AuthoritativeSourceRule6TotalSemanticUnresolved mol fuel center) := by
  refine ⟨authoritativeSourceRule6SemanticOutcome_total mol fuel center, ?_, ?_, ?_⟩
  · rintro ⟨stereogenic, nonstereogenic⟩
    have positive :=
      (authoritativeSourceRule6Stereogenicity?_eq_some_true_iff
        mol fuel center).mpr stereogenic
    have negative :=
      (authoritativeSourceRule6Stereogenicity?_eq_some_false_iff
        mol fuel center).mpr nonstereogenic
    rw [positive] at negative
    contradiction
  · rintro ⟨stereogenic, unresolved⟩
    have positive :=
      (authoritativeSourceRule6Stereogenicity?_eq_some_true_iff
        mol fuel center).mpr stereogenic
    have absent :=
      (authoritativeSourceRule6Stereogenicity?_eq_none_iff_totalSemanticUnresolved
        mol fuel center).mpr unresolved
    rw [positive] at absent
    contradiction
  · rintro ⟨nonstereogenic, unresolved⟩
    have negative :=
      (authoritativeSourceRule6Stereogenicity?_eq_some_false_iff
        mol fuel center).mpr nonstereogenic
    have absent :=
      (authoritativeSourceRule6Stereogenicity?_eq_none_iff_totalSemanticUnresolved
        mol fuel center).mpr unresolved
    rw [negative] at absent
    contradiction

/-- The public unannotated adapter omits a center exactly when Rule 6 has resolved it as
nonstereogenic. -/
theorem authoritativeSourceRule6UnannotatedOutcome?_eq_none_iff_nonstereogenic
    (mol : RawMolecule) (fuel center : Nat) :
    authoritativeSourceRule6UnannotatedOutcome? mol fuel center = none ↔
      AuthoritativeSourceRule6Nonstereogenic mol fuel center := by
  cases computed : authoritativeSourceRule6Stereogenicity? mol fuel center with
  | none =>
      have notNegative : ¬AuthoritativeSourceRule6Nonstereogenic mol fuel center := by
        intro negative
        have falseEq :=
          (authoritativeSourceRule6Stereogenicity?_eq_some_false_iff
            mol fuel center).mpr negative
        rw [computed] at falseEq
        contradiction
      simp [authoritativeSourceRule6UnannotatedOutcome?, computed, notNegative]
  | some decision =>
      cases decision
      · simpa [authoritativeSourceRule6UnannotatedOutcome?, computed] using
          (authoritativeSourceRule6Stereogenicity?_eq_some_false_iff
            mol fuel center)
      · have notNegative : ¬AuthoritativeSourceRule6Nonstereogenic mol fuel center := by
          intro negative
          have falseEq :=
            (authoritativeSourceRule6Stereogenicity?_eq_some_false_iff
              mol fuel center).mpr negative
          rw [computed] at falseEq
          contradiction
        simp [authoritativeSourceRule6UnannotatedOutcome?, computed, notNegative]

end AuthoritativeCIPRule6Scheduler
end TetraStereo.OneCenter
