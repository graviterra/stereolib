import TetraStereo.OneCenter.CIPAuthoritativeRule6ResolvedApplicability
import TetraStereo.OneCenter.CIPStereogenicPerceptionConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeCIPRule6Scheduler

open RawMolecule
open DeclarativeCIP
open DeclarativeCIP.ProductionOccurrenceRules456
open BlueBookP92.Perception

/-!
# Source-level unannotated Rule-6 perception

The resolved Rule-6 adapter is deliberately independent of input parity, but still expects an
auxiliary occurrence state and a resolved four-position Rules-1a--5 partition.  This module closes
that source seam.  It constructs those inputs from an arbitrary molecular center, then installs the
result as the Rule-6 fallback of a molecule-wide unannotated tetrahedral scan.

No successful `authoritativeOccurrenceRule6Result?`, emitted descriptor, or public-list membership
appears in the source stereogenicity predicate below.
-/

/-- The source Rule-6 frame has one cursor per physical ligand position.

Multiple-bond duplicate nodes belong below the corresponding ligand root in the CIP digraph; they
are not additional ligand positions at the stereogenic center. -/
def authoritativeSourceRule6LigandCursors
    (mol : RawMolecule) (center : Nat) : List CanonicalRerootCursor :=
  (mol.ligandsWithLonePair center).map fun ligand =>
    { node := canonicalRoot center ligand
      previous? := some (canonicalCenterRoot center) }

@[simp] theorem authoritativeSourceRule6LigandCursors_length
    (mol : RawMolecule) (center : Nat) :
    (authoritativeSourceRule6LigandCursors mol center).length =
      (mol.ligandsWithLonePair center).length := by
  simp [authoritativeSourceRule6LigandCursors]

/-- Descriptor-free authoritative Rule-6 perception directly from a molecular center.

An odd constitutional automorphism is a proved nonstereogenic result. Failure to construct the
auxiliary state, initial partition, or topology decision remains unresolved. -/
def authoritativeSourceRule6Stereogenicity?
    (mol : RawMolecule) (fuel center : Nat) : Option Bool :=
  let node := canonicalCenterRoot center
  let ligands := mol.ligandsWithLonePair center
  let roots := authoritativeSourceRule6LigandCursors mol center
  if ligands.length = 4 then
    match buildOccurrenceAuxStateFullyAuthoritative? mol fuel center with
    | none => none
    | some aux =>
        match sortAuthoritativeRule6InitialPositions?
            mol aux fuel roots (List.range 4) with
        | none => none
        | some sorted =>
            match compareAuthoritativeRule6InitialAdjacent?
                mol aux fuel roots sorted with
            | none => none
            | some adjacent =>
                if some Ordering.lt ∈ adjacent then none
                else
                  let initialBefore := fun left right =>
                    (compareAuthoritativeRule6InitialPositions?
                      mol aux fuel roots left right).any
                        fun decision => decision.ordering = Ordering.eq
                  match hasOddConstitutionAutomorphismAtCenter
                      mol center ligands initialBefore with
                  | none => none
                  | some true => some false
                  | some false =>
                      authoritativeResolvedRule6Stereogenicity?
                        mol aux fuel node roots sorted adjacent
  else some false

/-- Independent source-level applicability of Rule 6 at an unannotated center.

The existential witnesses are outputs of primitive molecule-to-digraph construction and the
uncapped Rules-1a--5 partition.  The final clause is the parity-independent P-92 branch relation.
In particular, the proposition does not assume that a Rule-6 result or descriptor was emitted. -/
def AuthoritativeSourceRule6Stereogenic
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
    AuthoritativeRule6ResolvedStereogenic
      mol aux fuel node roots sorted adjacent

/-- The source adapter succeeds exactly for the independent source-level applicability relation. -/
theorem authoritativeSourceRule6Stereogenicity?_eq_some_true_iff
    (mol : RawMolecule) (fuel center : Nat) :
    authoritativeSourceRule6Stereogenicity? mol fuel center = some true ↔
      AuthoritativeSourceRule6Stereogenic mol fuel center := by
  let node := canonicalCenterRoot center
  let ligands := mol.ligandsWithLonePair center
  let roots := authoritativeSourceRule6LigandCursors mol center
  change authoritativeSourceRule6Stereogenicity? mol fuel center = some true ↔
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
      AuthoritativeRule6ResolvedStereogenic
        mol aux fuel node roots sorted adjacent
  constructor
  · intro computed
    by_cases ligandsLength : ligands.length = 4
    · cases auxEq : buildOccurrenceAuxStateFullyAuthoritative? mol fuel center with
      | none =>
          simp [authoritativeSourceRule6Stereogenicity?, ligands,
            ligandsLength, auxEq] at computed
      | some aux =>
          cases sortedEq : sortAuthoritativeRule6InitialPositions?
              mol aux fuel roots (List.range 4) with
          | none =>
              simp [authoritativeSourceRule6Stereogenicity?, ligands,
                roots, ligandsLength, auxEq, sortedEq] at computed
          | some sorted =>
              cases adjacentEq : compareAuthoritativeRule6InitialAdjacent?
                  mol aux fuel roots sorted with
              | none =>
                  simp [authoritativeSourceRule6Stereogenicity?, ligands,
                    roots, ligandsLength, auxEq, sortedEq, adjacentEq] at computed
              | some adjacent =>
                  by_cases adjacentLt : some Ordering.lt ∈ adjacent
                  · simp [authoritativeSourceRule6Stereogenicity?, ligands,
                      roots, ligandsLength, auxEq, sortedEq, adjacentEq,
                      adjacentLt] at computed
                  · let initialBefore := fun left right =>
                      (compareAuthoritativeRule6InitialPositions?
                        mol aux fuel roots left right).any
                          fun decision => decision.ordering = Ordering.eq
                    cases oddEq : hasOddConstitutionAutomorphismAtCenter
                        mol center ligands initialBefore with
                    | none =>
                        simp [authoritativeSourceRule6Stereogenicity?, ligands,
                          roots, ligandsLength, auxEq, sortedEq, adjacentEq,
                          adjacentLt, initialBefore, oddEq] at computed
                    | some odd =>
                        cases odd
                        · have resolved :=
                            (authoritativeResolvedRule6Stereogenicity?_eq_some_true_iff
                              mol aux fuel node roots sorted adjacent).mp (by
                                simpa [authoritativeSourceRule6Stereogenicity?,
                                  ligands, roots, ligandsLength, auxEq, sortedEq,
                                  adjacentEq, adjacentLt, initialBefore, oddEq]
                                  using computed)
                          exact ⟨aux, sorted, adjacent, ligandsLength, rfl,
                            sortedEq, adjacentEq, adjacentLt,
                            by simpa [initialBefore] using oddEq, resolved⟩
                        · simp [authoritativeSourceRule6Stereogenicity?, ligands,
                            roots, ligandsLength, auxEq, sortedEq, adjacentEq,
                            adjacentLt, initialBefore, oddEq] at computed
    · simp [authoritativeSourceRule6Stereogenicity?, ligands,
        ligandsLength] at computed
  · rintro ⟨aux, sorted, adjacent, ligandsLength, auxEq,
      sortedEq, adjacentEq, adjacentLt, oddEq, resolved⟩
    have resolvedEq :=
      (authoritativeResolvedRule6Stereogenicity?_eq_some_true_iff
        mol aux fuel node roots sorted adjacent).mpr resolved
    simpa [authoritativeSourceRule6Stereogenicity?, node, ligands, roots,
      ligandsLength, auxEq, sortedEq, adjacentEq,
      adjacentLt, oddEq] using resolvedEq

/-- Public unannotated outcome of the source-level Rule-6 adapter. -/
def authoritativeSourceRule6UnannotatedOutcome?
    (mol : RawMolecule) (fuel center : Nat) : Option StereoOutcome :=
  match authoritativeSourceRule6Stereogenicity? mol fuel center with
  | some true => some (.refused .notSpecified)
  | some false => none
  | none => some (.refused .rankingUnresolved)

/-- Source-level configuration-unspecified output is exact. -/
theorem authoritativeSourceRule6UnannotatedOutcome?_eq_notSpecified_iff
    (mol : RawMolecule) (fuel center : Nat) :
    authoritativeSourceRule6UnannotatedOutcome? mol fuel center =
        some (.refused .notSpecified) ↔
      AuthoritativeSourceRule6Stereogenic mol fuel center := by
  cases computed : authoritativeSourceRule6Stereogenicity? mol fuel center with
  | none =>
      have notApplicable : ¬ AuthoritativeSourceRule6Stereogenic mol fuel center := by
        intro applicable
        have success :=
          (authoritativeSourceRule6Stereogenicity?_eq_some_true_iff
            mol fuel center).mpr applicable
        rw [computed] at success
        contradiction
      simp [authoritativeSourceRule6UnannotatedOutcome?, computed, notApplicable]
  | some decision =>
      cases decision
      · have notApplicable : ¬ AuthoritativeSourceRule6Stereogenic mol fuel center := by
          intro applicable
          have success :=
            (authoritativeSourceRule6Stereogenicity?_eq_some_true_iff
              mol fuel center).mpr applicable
          rw [computed] at success
          contradiction
        simp [authoritativeSourceRule6UnannotatedOutcome?, computed, notApplicable]
      · constructor
        · intro _emitted
          exact
            (authoritativeSourceRule6Stereogenicity?_eq_some_true_iff
              mol fuel center).mp computed
        · intro _applicable
          simp [authoritativeSourceRule6UnannotatedOutcome?, computed]

/-! ## Integration into the unannotated tetrahedral scan -/

/-- Unannotated tetrahedral perception with the uncapped authoritative Rule-6 source fallback.

The existing strict Rules-1a--5 result retains precedence. When that stage is unresolved, the
complete Rule-6 decision is attempted before a legacy terminal-tie result is allowed to exclude
the center. This ordering is required because a Rules-1a--5 tie is exactly the situation in which
Rule 6 can still establish a strict ligand order. -/
def unannotatedTetrahedralOutcomeWithAuthoritativeRule6?
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) : Option StereoOutcome :=
  match result.parsed.atomAt? center with
  | none => none
  | some spec =>
      match spec.tetrahedral? with
      | some _ => none
      | none =>
          if ConnectivityOnlyTetrahedralFrame result mol center then
            let ligands := mol.writtenNeighbors center
            match rankBranchPositionsThroughOfficialContext?
                result mol state fuel center ligands with
            | some _ => some (.refused .notSpecified)
            | none =>
                match authoritativeSourceRule6Stereogenicity? mol fuel center with
                | some true => some (.refused .notSpecified)
                | some false => none
                | none =>
                    if hasTerminalTetrahedralTie result mol state fuel center ligands then none
                    else some (.refused .rankingUnresolved)
          else none

/-- Independent source meaning of a configuration-unspecified result from the integrated
unannotated analyzer. -/
def AuthoritativeUnannotatedTetrahedralStereogenic
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) : Prop :=
  ∃ spec,
    result.parsed.atomAt? center = some spec ∧
    spec.tetrahedral? = none ∧
    ConnectivityOnlyTetrahedralFrame result mol center ∧
    ((∃ positions,
        rankBranchPositionsThroughOfficialContext?
          result mol state fuel center (mol.writtenNeighbors center) = some positions) ∨
      (rankBranchPositionsThroughOfficialContext?
          result mol state fuel center (mol.writtenNeighbors center) = none ∧
        AuthoritativeSourceRule6Stereogenic mol fuel center))

/-- Exact success theorem for the integrated unannotated analyzer. -/
theorem unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_notSpecified_iff
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) :
    unannotatedTetrahedralOutcomeWithAuthoritativeRule6?
        result mol state fuel center = some (.refused .notSpecified) ↔
      AuthoritativeUnannotatedTetrahedralStereogenic
        result mol state fuel center := by
  unfold unannotatedTetrahedralOutcomeWithAuthoritativeRule6?
  unfold AuthoritativeUnannotatedTetrahedralStereogenic
  cases atomEq : result.parsed.atomAt? center with
  | none => simp
  | some spec =>
      cases parityEq : spec.tetrahedral? with
      | some parity => simp [parityEq]
      | none =>
          by_cases frame : ConnectivityOnlyTetrahedralFrame result mol center
          · cases rankingEq : rankBranchPositionsThroughOfficialContext?
                result mol state fuel center (mol.writtenNeighbors center) with
            | some positions => simp [parityEq, frame, rankingEq]
            | none =>
                cases sourceEq : authoritativeSourceRule6Stereogenicity? mol fuel center with
                | none =>
                    cases tieEq : hasTerminalTetrahedralTie result mol state fuel center
                        (mol.writtenNeighbors center) <;>
                      simp [parityEq, frame, rankingEq, sourceEq, tieEq,
                        ← authoritativeSourceRule6Stereogenicity?_eq_some_true_iff]
                | some decision =>
                    cases decision <;>
                      simp [parityEq, frame, rankingEq, sourceEq,
                        ← authoritativeSourceRule6Stereogenicity?_eq_some_true_iff]
          · simp [parityEq, frame]

/-- Assignment adapter for the authoritative unannotated branch. -/
def unannotatedTetrahedralAssignmentWithAuthoritativeRule6?
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) : Option StereoAssignment :=
  (unannotatedTetrahedralOutcomeWithAuthoritativeRule6?
    result mol state fuel center).map fun outcome =>
      { unit := .tetrahedral center, outcome := outcome }

/-- Ordinary tetrahedral dispatch with the authoritative unannotated Rule-6 branch installed. -/
def tetrahedralAssignmentWithAuthoritativeRule6?
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) : Option StereoAssignment :=
  match result.parsed.atomAt? center with
  | none => none
  | some spec =>
      match spec.tetrahedral? with
      | none =>
          unannotatedTetrahedralAssignmentWithAuthoritativeRule6?
            result mol state fuel center
      | some _ => annotatedTetrahedralAssignment? result mol state fuel center

/-- Molecule-wide ordinary-tetrahedral scan with authoritative unannotated Rule-6 perception. -/
def tetrahedralAssignmentsWithAuthoritativeRule6
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat) : List StereoAssignment :=
  (List.range result.parsed.atomCount).filterMap
    (tetrahedralAssignmentWithAuthoritativeRule6? result mol state fuel)

/-- Every local output retains the atom at which it was requested. -/
theorem tetrahedralAssignmentWithAuthoritativeRule6?_unit
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) (assignment : StereoAssignment)
    (computed : tetrahedralAssignmentWithAuthoritativeRule6?
      result mol state fuel center = some assignment) :
    assignment.unit = .tetrahedral center := by
  unfold tetrahedralAssignmentWithAuthoritativeRule6? at computed
  cases atomEq : result.parsed.atomAt? center with
  | none => simp [atomEq] at computed
  | some spec =>
      cases parityEq : spec.tetrahedral? with
      | none =>
          unfold unannotatedTetrahedralAssignmentWithAuthoritativeRule6? at computed
          cases outcomeEq : unannotatedTetrahedralOutcomeWithAuthoritativeRule6?
              result mol state fuel center with
          | none => simp [atomEq, parityEq, outcomeEq] at computed
          | some outcome =>
              simp [atomEq, parityEq, outcomeEq] at computed
              subst assignment
              rfl
      | some parity =>
          unfold annotatedTetrahedralAssignment? at computed
          cases outcomeEq : annotatedTetrahedralOutcome? result mol state fuel center with
          | none => simp [atomEq, parityEq, outcomeEq] at computed
          | some outcome =>
              simp [atomEq, parityEq, outcomeEq] at computed
              subst assignment
              rfl

/-- The authoritative ordinary-tetrahedral scan contains no duplicate assignments. -/
theorem tetrahedralAssignmentsWithAuthoritativeRule6_nodup
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat) :
    (tetrahedralAssignmentsWithAuthoritativeRule6 result mol state fuel).Nodup := by
  unfold tetrahedralAssignmentsWithAuthoritativeRule6
  apply List.nodup_range.filterMap
  intro left right assignment leftComputed rightComputed
  have leftUnit := tetrahedralAssignmentWithAuthoritativeRule6?_unit
    result mol state fuel left assignment leftComputed
  have rightUnit := tetrahedralAssignmentWithAuthoritativeRule6?_unit
    result mol state fuel right assignment rightComputed
  have : left = right := by
    simpa using leftUnit.symm.trans rightUnit
  exact this

/-- Projection to physical tetrahedral units also remains duplicate-free. -/
theorem tetrahedralAssignmentsWithAuthoritativeRule6_units_nodup
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat) :
    ((tetrahedralAssignmentsWithAuthoritativeRule6 result mol state fuel).map
      StereoAssignment.unit).Nodup := by
  apply (tetrahedralAssignmentsWithAuthoritativeRule6_nodup
    result mol state fuel).map_on
  intro left leftMem right rightMem sameUnit
  rw [tetrahedralAssignmentsWithAuthoritativeRule6, List.mem_filterMap] at leftMem rightMem
  obtain ⟨leftCenter, _leftBound, leftComputed⟩ := leftMem
  obtain ⟨rightCenter, _rightBound, rightComputed⟩ := rightMem
  have leftUnit := tetrahedralAssignmentWithAuthoritativeRule6?_unit
    result mol state fuel leftCenter left leftComputed
  have rightUnit := tetrahedralAssignmentWithAuthoritativeRule6?_unit
    result mol state fuel rightCenter right rightComputed
  have centers : leftCenter = rightCenter := by
    simpa [leftUnit, rightUnit] using sameUnit
  subst rightCenter
  exact Option.some.inj (leftComputed.symm.trans rightComputed)

/-- Every independently applicable unannotated center occurs in the molecule-wide authoritative
scan exactly once, and is reported as configuration-unspecified rather than assigned arbitrary
`R/S`. -/
theorem every_authoritativeUnannotatedTetrahedralStereogenic_public_exactly_once
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (centerBound : center < result.parsed.atomCount)
    (stereogenic : AuthoritativeUnannotatedTetrahedralStereogenic
      result mol state fuel center) :
    ∃ assignment,
      assignment ∈ tetrahedralAssignmentsWithAuthoritativeRule6 result mol state fuel ∧
      assignment.unit = .tetrahedral center ∧
      assignment.outcome = .refused .notSpecified ∧
      List.count (.tetrahedral center)
        ((tetrahedralAssignmentsWithAuthoritativeRule6 result mol state fuel).map
          StereoAssignment.unit) = 1 := by
  let assignment : StereoAssignment :=
    { unit := .tetrahedral center, outcome := .refused .notSpecified }
  have outcomeEq :=
    (unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_notSpecified_iff
      result mol state fuel center).mpr stereogenic
  rcases stereogenic with ⟨spec, atomEq, parityEq, _frame, _ranking⟩
  have localEq : tetrahedralAssignmentWithAuthoritativeRule6?
      result mol state fuel center = some assignment := by
    simp [tetrahedralAssignmentWithAuthoritativeRule6?, atomEq, parityEq,
      unannotatedTetrahedralAssignmentWithAuthoritativeRule6?, outcomeEq, assignment]
  have present : assignment ∈ tetrahedralAssignmentsWithAuthoritativeRule6
      result mol state fuel := by
    rw [tetrahedralAssignmentsWithAuthoritativeRule6, List.mem_filterMap]
    exact ⟨center, List.mem_range.mpr centerBound, localEq⟩
  refine ⟨assignment, present, rfl, rfl, ?_⟩
  exact List.count_eq_one_of_mem
    (tetrahedralAssignmentsWithAuthoritativeRule6_units_nodup result mol state fuel)
    (List.mem_map.mpr ⟨assignment, present, rfl⟩)

end AuthoritativeCIPRule6Scheduler
end TetraStereo.OneCenter
