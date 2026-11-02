import TetraStereo.OneCenter.CIPAuthoritativeRule6UnannotatedChemicalCompleteness
import TetraStereo.OneCenter.CIPAuthoritativeStereoAssignmentConformance

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter
namespace AuthoritativeCIPRule6Scheduler

open RawMolecule

/-!
# Integration of authoritative unannotated Rule 6 into the normalized public analyzer

The normalized analyzer already separates its five public branches.  This module replaces exactly
its tetrahedral branch with `tetrahedralAssignmentsWithAuthoritativeRule6`; the ordinary-double,
descriptor-dependent-double, odd-cumulene, and extended-axial branches are retained literally.
-/

/-- The five production branches with the authoritative unannotated Rule-6 tetrahedral scan
installed.  Every non-tetrahedral field is definitionally the existing normalized field. -/
def normalizedStereoAnalysisBranchesWithAuthoritativeRule6
    (result : ChemistryNormalizationResult) : NormalizedStereoAnalysisBranches :=
  let mol := result.parsed.withExplicitHydrogens
  let fuel := analysisFuel mol
  let state := discoverRawDescriptors result mol fuel
  { normalizedStereoAnalysisBranches result with
    tetrahedral := tetrahedralAssignmentsWithAuthoritativeRule6
      result mol state fuel }

@[simp] theorem normalizedStereoAnalysisBranchesWithAuthoritativeRule6_tetrahedral
    (result : ChemistryNormalizationResult) :
    (normalizedStereoAnalysisBranchesWithAuthoritativeRule6 result).tetrahedral =
      tetrahedralAssignmentsWithAuthoritativeRule6
        result result.parsed.withExplicitHydrogens
          (discoverRawDescriptors result result.parsed.withExplicitHydrogens
            (analysisFuel result.parsed.withExplicitHydrogens))
          (analysisFuel result.parsed.withExplicitHydrogens) := by
  rfl

@[simp] theorem normalizedStereoAnalysisBranchesWithAuthoritativeRule6_ordinaryDoubleBond
    (result : ChemistryNormalizationResult) :
    (normalizedStereoAnalysisBranchesWithAuthoritativeRule6 result).ordinaryDoubleBond =
      (normalizedStereoAnalysisBranches result).ordinaryDoubleBond := by
  rfl

@[simp] theorem normalizedStereoAnalysisBranchesWithAuthoritativeRule6_coupledDoubleBond
    (result : ChemistryNormalizationResult) :
    (normalizedStereoAnalysisBranchesWithAuthoritativeRule6 result).coupledDoubleBond =
      (normalizedStereoAnalysisBranches result).coupledDoubleBond := by
  rfl

@[simp] theorem normalizedStereoAnalysisBranchesWithAuthoritativeRule6_oddCumuleneDoubleBond
    (result : ChemistryNormalizationResult) :
    (normalizedStereoAnalysisBranchesWithAuthoritativeRule6 result).oddCumuleneDoubleBond =
      (normalizedStereoAnalysisBranches result).oddCumuleneDoubleBond := by
  rfl

@[simp] theorem normalizedStereoAnalysisBranchesWithAuthoritativeRule6_extendedAxial
    (result : ChemistryNormalizationResult) :
    (normalizedStereoAnalysisBranchesWithAuthoritativeRule6 result).extendedAxial =
      (normalizedStereoAnalysisBranches result).extendedAxial := by
  rfl

/-- The production-shaped normalized analyzer with only the legacy unannotated Rule-6 fallback
replaced.  The two molecule-wide admission guards and branch ordering are unchanged. -/
def analyzeNormalizedWithAuthoritativeRule6
    (result : ChemistryNormalizationResult) : List StereoAssignment :=
  if !result.parsed.rule2MassesKnown? then [] else
  if !result.expandedStereochemicalAdmissible? then [] else
  let branches := normalizedStereoAnalysisBranchesWithAuthoritativeRule6 result
  branches.tetrahedral ++ branches.ordinaryDoubleBond ++ branches.coupledDoubleBond ++
    branches.oddCumuleneDoubleBond ++ branches.extendedAxial

/-- Exact guarded branch normal form for the replacement analyzer. -/
theorem mem_analyzeNormalizedWithAuthoritativeRule6_iff_branch
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) :
    assignment ∈ analyzeNormalizedWithAuthoritativeRule6 result ↔
      result.parsed.rule2MassesKnown? = true ∧
      result.expandedStereochemicalAdmissible? = true ∧
      (assignment ∈
          (normalizedStereoAnalysisBranchesWithAuthoritativeRule6 result).tetrahedral ∨
        assignment ∈ (normalizedStereoAnalysisBranches result).ordinaryDoubleBond ∨
        assignment ∈ (normalizedStereoAnalysisBranches result).coupledDoubleBond ∨
        assignment ∈ (normalizedStereoAnalysisBranches result).oddCumuleneDoubleBond ∨
        assignment ∈ (normalizedStereoAnalysisBranches result).extendedAxial) := by
  cases massesKnown : result.parsed.rule2MassesKnown? <;>
    cases admissible : result.expandedStereochemicalAdmissible? <;>
    simp [analyzeNormalizedWithAuthoritativeRule6, massesKnown, admissible,
      List.mem_append]

private theorem ordinaryDoubleBond_member_not_tetrahedral
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (present : assignment ∈
      (normalizedStereoAnalysisBranches result).ordinaryDoubleBond) (center : Nat) :
    assignment.unit ≠ .tetrahedral center := by
  have explicitPresent : assignment ∈ ordinaryDoubleBondAssignments
      result result.parsed.withExplicitHydrogens
        (discoverRawDescriptors result result.parsed.withExplicitHydrogens
          (analysisFuel result.parsed.withExplicitHydrogens))
        (analysisFuel result.parsed.withExplicitHydrogens) := by
    simpa using present
  obtain ⟨record, _recordPresent, judged⟩ :=
    (mem_ordinaryDoubleBondAssignments_iff_independent_judgment
      result result.parsed.withExplicitHydrogens
        (discoverRawDescriptors result result.parsed.withExplicitHydrogens
          (analysisFuel result.parsed.withExplicitHydrogens))
        (analysisFuel result.parsed.withExplicitHydrogens) assignment).mp explicitPresent
  rcases record with ⟨left, right, inputStereo⟩
  have unitEq : assignment.unit = .doubleBond left right := judged.1
  simp [unitEq]

private theorem coupledDoubleBond_member_not_tetrahedral
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (present : assignment ∈
      (normalizedStereoAnalysisBranches result).coupledDoubleBond) (center : Nat) :
    assignment.unit ≠ .tetrahedral center := by
  have judged :=
    (mem_normalizedCoupledDoubleBond_iff_independent_judgment
      result assignment).mp present
  dsimp [IndependentlyJudgedNormalizedDescriptorDependentDoubleBondAssignment] at judged
  obtain ⟨record, _recordPresent, routed⟩ := judged
  rcases record with ⟨left, right, inputStereo⟩
  have unitEq : assignment.unit = .doubleBond left right := by
    exact routed.2.1
  simp [unitEq]

private theorem oddCumuleneDoubleBond_member_not_tetrahedral
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (present : assignment ∈
      (normalizedStereoAnalysisBranches result).oddCumuleneDoubleBond) (center : Nat) :
    assignment.unit ≠ .tetrahedral center := by
  have explicitPresent : assignment ∈ oddCumuleneDoubleBondAssignments
      result result.parsed.withExplicitHydrogens
        (normalizedGeometryDescriptorState result result.parsed.withExplicitHydrogens
          (analysisFuel result.parsed.withExplicitHydrogens)
          (discoverRawDescriptors result result.parsed.withExplicitHydrogens
            (analysisFuel result.parsed.withExplicitHydrogens)))
        (analysisFuel result.parsed.withExplicitHydrogens) := by
    simpa using present
  obtain ⟨chain, _chainPresent, judged⟩ :=
    (mem_oddCumuleneDoubleBondAssignments_iff_independent_judgment
      result result.parsed.withExplicitHydrogens
        (normalizedGeometryDescriptorState result result.parsed.withExplicitHydrogens
          (analysisFuel result.parsed.withExplicitHydrogens)
          (discoverRawDescriptors result result.parsed.withExplicitHydrogens
            (analysisFuel result.parsed.withExplicitHydrogens)))
        (analysisFuel result.parsed.withExplicitHydrogens) assignment).mp explicitPresent
  rcases judged with ⟨_odd, judged⟩
  cases frameEq : cumulatedChainTerminalFrame? chain with
  | none => simp [frameEq] at judged
  | some frame =>
      rcases frame with ⟨left, leftPartner, right, rightPartner⟩
      simp only [frameEq] at judged
      have unitEq : assignment.unit = .doubleBond left right := by
        exact judged.1
      simp [unitEq]

private theorem extendedAxial_member_not_tetrahedral
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (present : assignment ∈
      (normalizedStereoAnalysisBranches result).extendedAxial) (center : Nat) :
    assignment.unit ≠ .tetrahedral center := by
  obtain ⟨carrier, _carrierPresent, judged⟩ :=
    (mem_normalizedExtendedAxial_iff_independent_judgment result assignment).mp present
  have unitEq : assignment.unit = .axis carrier.left carrier.right := judged.1
  simp [unitEq]

private theorem nonTetrahedralBranches_member_not_tetrahedral
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) (center : Nat)
    (present :
      assignment ∈ (normalizedStereoAnalysisBranches result).ordinaryDoubleBond ∨
      assignment ∈ (normalizedStereoAnalysisBranches result).coupledDoubleBond ∨
      assignment ∈ (normalizedStereoAnalysisBranches result).oddCumuleneDoubleBond ∨
      assignment ∈ (normalizedStereoAnalysisBranches result).extendedAxial) :
    assignment.unit ≠ .tetrahedral center := by
  rcases present with ordinary | coupled | odd | axial
  · exact ordinaryDoubleBond_member_not_tetrahedral result assignment ordinary center
  · exact coupledDoubleBond_member_not_tetrahedral result assignment coupled center
  · exact oddCumuleneDoubleBond_member_not_tetrahedral result assignment odd center
  · exact extendedAxial_member_not_tetrahedral result assignment axial center

/-- No retained non-tetrahedral branch contributes a tetrahedral physical unit. -/
theorem normalizedNonTetrahedralBranches_tetrahedral_count_eq_zero
    (result : ChemistryNormalizationResult) (center : Nat) :
    List.count (.tetrahedral center)
      (((normalizedStereoAnalysisBranches result).ordinaryDoubleBond ++
        (normalizedStereoAnalysisBranches result).coupledDoubleBond ++
        (normalizedStereoAnalysisBranches result).oddCumuleneDoubleBond ++
        (normalizedStereoAnalysisBranches result).extendedAxial).map
          StereoAssignment.unit) = 0 := by
  apply List.count_eq_zero.mpr
  intro unitPresent
  obtain ⟨assignment, assignmentPresent, unitEq⟩ := List.mem_map.mp unitPresent
  apply nonTetrahedralBranches_member_not_tetrahedral result assignment center
  · simp only [List.mem_append] at assignmentPresent
    rcases assignmentPresent with older | axial
    · rcases older with old | odd
      · rcases old with ordinary | coupled
        · exact Or.inl ordinary
        · exact Or.inr (Or.inl coupled)
      · exact Or.inr (Or.inr (Or.inl odd))
    · exact Or.inr (Or.inr (Or.inr axial))
  · exact unitEq

private theorem unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_not_assigned
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) (outcome : StereoOutcome)
    (computed : unannotatedTetrahedralOutcomeWithAuthoritativeRule6?
      result mol state fuel center = some outcome) :
    outcome.assigned = false := by
  unfold unannotatedTetrahedralOutcomeWithAuthoritativeRule6? at computed
  cases atomEq : result.parsed.atomAt? center with
  | none => simp [atomEq] at computed
  | some spec =>
      cases parityEq : spec.tetrahedral? with
      | some parity => simp [atomEq, parityEq] at computed
      | none =>
          by_cases frame :
              BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame result mol center
          · cases rankingEq : rankBranchPositionsThroughOfficialContext?
                result mol state fuel center (mol.writtenNeighbors center) with
            | some positions =>
                simp [atomEq, parityEq, frame, rankingEq] at computed
                rcases computed with ⟨_frame, rfl⟩
                rfl
            | none =>
                cases sourceEq : authoritativeSourceRule6Stereogenicity?
                    mol fuel center with
                | none =>
                    cases tieEq : hasTerminalTetrahedralTie result mol state fuel center
                        (mol.writtenNeighbors center) with
                    | false =>
                        simp [atomEq, parityEq, frame, rankingEq, sourceEq, tieEq] at computed
                        rcases computed with ⟨_frame, rfl⟩
                        rfl
                    | true =>
                        simp [atomEq, parityEq, frame, rankingEq, sourceEq, tieEq] at computed
                | some decision =>
                    cases decision
                    · simp [atomEq, parityEq, frame, rankingEq, sourceEq] at computed
                    · simp [atomEq, parityEq, frame, rankingEq, sourceEq] at computed
                      rcases computed with ⟨_frame, rfl⟩
                      rfl
          · simp [atomEq, parityEq, frame] at computed

private theorem unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_possible
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) (outcome : StereoOutcome)
    (computed : unannotatedTetrahedralOutcomeWithAuthoritativeRule6?
      result mol state fuel center = some outcome) :
    outcome = .refused .notSpecified ∨
      outcome = .refused .rankingUnresolved := by
  unfold unannotatedTetrahedralOutcomeWithAuthoritativeRule6? at computed
  cases atomEq : result.parsed.atomAt? center with
  | none => simp [atomEq] at computed
  | some spec =>
      cases parityEq : spec.tetrahedral? with
      | some parity => simp [atomEq, parityEq] at computed
      | none =>
          by_cases frame :
              BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame result mol center
          · cases rankingEq : rankBranchPositionsThroughOfficialContext?
                result mol state fuel center (mol.writtenNeighbors center) with
            | some positions =>
                simp [atomEq, parityEq, frame, rankingEq] at computed
                exact Or.inl computed.symm
            | none =>
                cases sourceEq : authoritativeSourceRule6Stereogenicity?
                    mol fuel center with
                | none =>
                    cases tieEq : hasTerminalTetrahedralTie result mol state fuel center
                        (mol.writtenNeighbors center) with
                    | false =>
                        simp [atomEq, parityEq, frame, rankingEq, sourceEq, tieEq] at computed
                        exact Or.inr computed.symm
                    | true =>
                        simp [atomEq, parityEq, frame, rankingEq, sourceEq, tieEq] at computed
                | some decision =>
                    cases decision
                    · simp [atomEq, parityEq, frame, rankingEq, sourceEq] at computed
                    · simp [atomEq, parityEq, frame, rankingEq, sourceEq] at computed
                      exact Or.inl computed.symm
          · simp [atomEq, parityEq, frame] at computed

/-- Independent meaning of the only unresolved output admitted by the authoritative unannotated
Rule-6 adapter. Earlier constitutional ranking has failed, the source occurrence construction has
returned no Boolean stereogenicity decision, and only then the legacy terminal-tie test permits an
unresolved result rather than excluding the center. -/
def AuthoritativeUnannotatedTetrahedralRankingUnresolved
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
    authoritativeSourceRule6Stereogenicity? mol fuel center = none

/-- Exact independent characterization of the authoritative ranking-unresolved refusal. -/
theorem unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_rankingUnresolved_iff
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) :
    unannotatedTetrahedralOutcomeWithAuthoritativeRule6?
        result mol state fuel center = some (.refused .rankingUnresolved) ↔
      AuthoritativeUnannotatedTetrahedralRankingUnresolved
        result mol state fuel center := by
  unfold unannotatedTetrahedralOutcomeWithAuthoritativeRule6?
  unfold AuthoritativeUnannotatedTetrahedralRankingUnresolved
  cases atomEq : result.parsed.atomAt? center with
  | none => simp [atomEq]
  | some spec =>
      cases parityEq : spec.tetrahedral? with
      | some parity => simp [atomEq, parityEq]
      | none =>
          by_cases frame :
              BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame result mol center
          · cases rankingEq : rankBranchPositionsThroughOfficialContext?
                result mol state fuel center (mol.writtenNeighbors center) with
            | some positions => simp [atomEq, parityEq, frame, rankingEq]
            | none =>
                cases sourceEq : authoritativeSourceRule6Stereogenicity?
                    mol fuel center with
                | none =>
                    cases tieEq : hasTerminalTetrahedralTie result mol state fuel center
                        (mol.writtenNeighbors center) with
                    | false =>
                        simp [atomEq, parityEq, frame, rankingEq, sourceEq, tieEq]
                    | true =>
                        simp [atomEq, parityEq, frame, rankingEq, sourceEq, tieEq]
                | some decision =>
                    cases decision <;>
                      simp [atomEq, parityEq, frame, rankingEq, sourceEq]
          · simp [atomEq, parityEq, frame]

/-- Complete independent two-case meaning of every successful unannotated Rule-6 outcome. -/
theorem unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_some_iff
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) (outcome : StereoOutcome) :
    unannotatedTetrahedralOutcomeWithAuthoritativeRule6?
        result mol state fuel center = some outcome ↔
      (outcome = .refused .notSpecified ∧
        AuthoritativeUnannotatedTetrahedralStereogenic result mol state fuel center) ∨
      (outcome = .refused .rankingUnresolved ∧
        AuthoritativeUnannotatedTetrahedralRankingUnresolved
          result mol state fuel center) := by
  constructor
  · intro computed
    have possible :=
      unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_possible
        result mol state fuel center outcome computed
    rcases possible with rfl | rfl
    · left
      exact ⟨rfl,
        (unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_notSpecified_iff
          result mol state fuel center).mp computed⟩
    · right
      exact ⟨rfl,
        (unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_rankingUnresolved_iff
          result mol state fuel center).mp computed⟩
  · rintro (⟨rfl, stereogenic⟩ | ⟨rfl, unresolved⟩)
    · exact
        (unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_notSpecified_iff
          result mol state fuel center).mpr stereogenic
    · exact
        (unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_rankingUnresolved_iff
          result mol state fuel center).mpr unresolved

/-- Independent assignment-level meaning for the authoritative unannotated branch. -/
def AuthoritativeUnannotatedTetrahedralAssignmentJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (assignment : StereoAssignment) : Prop :=
  (assignment =
      { unit := .tetrahedral center, outcome := .refused .notSpecified } ∧
    AuthoritativeUnannotatedTetrahedralStereogenic
      result mol state fuel center) ∨
  (assignment =
      { unit := .tetrahedral center, outcome := .refused .rankingUnresolved } ∧
    AuthoritativeUnannotatedTetrahedralRankingUnresolved
      result mol state fuel center)

/-- Exact assignment theorem for the authoritative unannotated branch. -/
theorem unannotatedTetrahedralAssignmentWithAuthoritativeRule6?_eq_some_iff
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (assignment : StereoAssignment) :
    unannotatedTetrahedralAssignmentWithAuthoritativeRule6?
        result mol state fuel center = some assignment ↔
      AuthoritativeUnannotatedTetrahedralAssignmentJudgment
        result mol state fuel center assignment := by
  unfold unannotatedTetrahedralAssignmentWithAuthoritativeRule6?
  unfold AuthoritativeUnannotatedTetrahedralAssignmentJudgment
  constructor
  · intro computed
    cases outcomeEq : unannotatedTetrahedralOutcomeWithAuthoritativeRule6?
        result mol state fuel center with
    | none => simp [outcomeEq] at computed
    | some outcome =>
        simp [outcomeEq] at computed
        have semantic :=
          (unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_some_iff
            result mol state fuel center outcome).mp outcomeEq
        rcases semantic with ⟨outcomeEq', stereogenic⟩ | ⟨outcomeEq', unresolved⟩
        · subst outcome
          exact Or.inl ⟨computed.symm, stereogenic⟩
        · subst outcome
          exact Or.inr ⟨computed.symm, unresolved⟩
  · rintro (⟨rfl, stereogenic⟩ | ⟨rfl, unresolved⟩)
    · rw [(unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_notSpecified_iff
        result mol state fuel center).mpr stereogenic]
      rfl
    · rw [(unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_rankingUnresolved_iff
        result mol state fuel center).mpr unresolved]
      rfl

/-- The independent public tetrahedral judgment after installing authoritative unannotated
Rule 6.  Annotated centers retain the existing P-93 judgment literally. -/
def AuthoritativePublicTetrahedralAssignmentJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (assignment : StereoAssignment) : Prop :=
  match result.parsed.atomAt? center with
  | none => False
  | some spec =>
      match spec.tetrahedral? with
      | none =>
          AuthoritativeUnannotatedTetrahedralAssignmentJudgment
            result mol state fuel center assignment
      | some _ =>
          BlueBookP93.Acyclic.AnnotatedTetrahedralAssignmentJudgment
            result mol state fuel center assignment

/-- Exact one-center boundary for annotated and authoritative-unannotated tetrahedral dispatch. -/
theorem tetrahedralAssignmentWithAuthoritativeRule6?_eq_some_iff_independent_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (assignment : StereoAssignment) :
    tetrahedralAssignmentWithAuthoritativeRule6?
        result mol state fuel center = some assignment ↔
      AuthoritativePublicTetrahedralAssignmentJudgment
        result mol state fuel center assignment := by
  unfold tetrahedralAssignmentWithAuthoritativeRule6?
  unfold AuthoritativePublicTetrahedralAssignmentJudgment
  cases atomEq : result.parsed.atomAt? center with
  | none => simp [atomEq]
  | some spec =>
      cases parityEq : spec.tetrahedral? with
      | none =>
          simpa [atomEq, parityEq] using
            (unannotatedTetrahedralAssignmentWithAuthoritativeRule6?_eq_some_iff
              result mol state fuel center assignment)
      | some parity =>
          simpa [atomEq, parityEq] using
            (annotatedTetrahedralAssignment?_eq_some_iff_independent_judgment
              result mol state fuel center assignment)

/-- Exact list boundary for the complete authoritative tetrahedral scan. -/
theorem mem_tetrahedralAssignmentsWithAuthoritativeRule6_iff_independent_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat) (assignment : StereoAssignment) :
    assignment ∈ tetrahedralAssignmentsWithAuthoritativeRule6 result mol state fuel ↔
      ∃ center < result.parsed.atomCount,
        AuthoritativePublicTetrahedralAssignmentJudgment
          result mol state fuel center assignment := by
  constructor
  · intro present
    rw [tetrahedralAssignmentsWithAuthoritativeRule6, List.mem_filterMap] at present
    obtain ⟨center, centerPresent, computed⟩ := present
    exact ⟨center, List.mem_range.mp centerPresent,
      (tetrahedralAssignmentWithAuthoritativeRule6?_eq_some_iff_independent_judgment
        result mol state fuel center assignment).mp computed⟩
  · rintro ⟨center, centerBound, judgment⟩
    rw [tetrahedralAssignmentsWithAuthoritativeRule6, List.mem_filterMap]
    exact ⟨center, List.mem_range.mpr centerBound,
      (tetrahedralAssignmentWithAuthoritativeRule6?_eq_some_iff_independent_judgment
        result mol state fuel center assignment).mpr judgment⟩

/-- Independent meaning of all five branches in the normalized authoritative-Rule-6 analyzer. -/
def IndependentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) : Prop :=
  let mol := result.parsed.withExplicitHydrogens
  let fuel := analysisFuel mol
  let state := discoverRawDescriptors result mol fuel
  let geometryState := normalizedGeometryDescriptorState result mol fuel state
  (∃ center < result.parsed.atomCount,
      AuthoritativePublicTetrahedralAssignmentJudgment
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

/-- Exact branch normal form of the independent replacement-pipeline specification. -/
theorem independentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6_iff_branch
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) :
    IndependentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6 result assignment ↔
      assignment ∈
          (normalizedStereoAnalysisBranchesWithAuthoritativeRule6 result).tetrahedral ∨
        assignment ∈ (normalizedStereoAnalysisBranches result).ordinaryDoubleBond ∨
        IndependentlyJudgedNormalizedDescriptorDependentDoubleBondAssignment
          result assignment ∨
        assignment ∈ (normalizedStereoAnalysisBranches result).oddCumuleneDoubleBond ∨
        assignment ∈ (normalizedStereoAnalysisBranches result).extendedAxial := by
  simp only [IndependentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6,
    normalizedStereoAnalysisBranchesWithAuthoritativeRule6_tetrahedral,
    normalizedStereoAnalysisBranches_ordinaryDoubleBond,
    normalizedStereoAnalysisBranches_oddCumuleneDoubleBond,
    mem_tetrahedralAssignmentsWithAuthoritativeRule6_iff_independent_judgment,
    mem_ordinaryDoubleBondAssignments_iff_independent_judgment,
    mem_oddCumuleneDoubleBondAssignments_iff_independent_judgment,
    mem_normalizedExtendedAxial_iff_independent_judgment]

/-- Final exact public theorem for the replacement raw analyzer: an assignment is emitted if and
only if both unchanged molecule-wide admission guards pass and one of the five independent
stereochemical judgments holds.  This covers descriptors and conservative refusals alike. -/
theorem mem_analyzeNormalizedWithAuthoritativeRule6_iff_independently_judged
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) :
    assignment ∈ analyzeNormalizedWithAuthoritativeRule6 result ↔
      result.parsed.rule2MassesKnown? = true ∧
      result.expandedStereochemicalAdmissible? = true ∧
      IndependentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6
        result assignment := by
  constructor
  · intro present
    obtain ⟨massesKnown, admissible, branch⟩ :=
      (mem_analyzeNormalizedWithAuthoritativeRule6_iff_branch
        result assignment).mp present
    refine ⟨massesKnown, admissible,
      (independentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6_iff_branch
        result assignment).mpr ?_⟩
    rcases branch with tetrahedral | ordinary | coupled | odd | axial
    · exact Or.inl tetrahedral
    · exact Or.inr (Or.inl ordinary)
    · exact Or.inr (Or.inr (Or.inl
        ((mem_normalizedCoupledDoubleBond_iff_independent_judgment
          result assignment).mp coupled)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl odd)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr axial)))
  · rintro ⟨massesKnown, admissible, judgment⟩
    have branch :=
      (independentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6_iff_branch
        result assignment).mp judgment
    apply (mem_analyzeNormalizedWithAuthoritativeRule6_iff_branch
      result assignment).mpr
    refine ⟨massesKnown, admissible, ?_⟩
    rcases branch with tetrahedral | ordinary | coupled | odd | axial
    · exact Or.inl tetrahedral
    · exact Or.inr (Or.inl ordinary)
    · exact Or.inr (Or.inr (Or.inl
        ((mem_normalizedCoupledDoubleBond_iff_independent_judgment
          result assignment).mpr coupled)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl odd)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr axial)))

private theorem assigned_tetrahedralAssignmentWithAuthoritativeRule6?_eq_original
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) (assignment : StereoAssignment)
    (computed : tetrahedralAssignmentWithAuthoritativeRule6?
      result mol state fuel center = some assignment)
    (assigned : assignment.outcome.assigned = true) :
    tetrahedralAssignment? result mol state fuel center = some assignment := by
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
              have outcomeNotAssigned :=
                unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_not_assigned
                  result mol state fuel center outcome outcomeEq
              simp [atomEq, parityEq, outcomeEq] at computed
              subst assignment
              rw [outcomeNotAssigned] at assigned
              contradiction
      | some parity =>
          simpa [tetrahedralAssignment?, atomEq, parityEq] using computed

private theorem assigned_authoritativeTetrahedral_member_originalTetrahedral
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (present : assignment ∈
      (normalizedStereoAnalysisBranchesWithAuthoritativeRule6 result).tetrahedral)
    (assigned : assignment.outcome.assigned = true) :
    assignment ∈ (normalizedStereoAnalysisBranches result).tetrahedral := by
  rw [normalizedStereoAnalysisBranchesWithAuthoritativeRule6_tetrahedral,
    tetrahedralAssignmentsWithAuthoritativeRule6, List.mem_filterMap] at present
  obtain ⟨center, centerPresent, computed⟩ := present
  rw [normalizedStereoAnalysisBranches_tetrahedral,
    tetrahedralAssignments, List.mem_filterMap]
  exact ⟨center, centerPresent,
    assigned_tetrahedralAssignmentWithAuthoritativeRule6?_eq_original
      result result.parsed.withExplicitHydrogens
        (discoverRawDescriptors result result.parsed.withExplicitHydrogens
          (analysisFuel result.parsed.withExplicitHydrogens))
        (analysisFuel result.parsed.withExplicitHydrogens) center assignment computed assigned⟩

/-- Every descriptor-bearing output of the complete replacement analyzer retains an independent
P-92/P-93 assignment judgment.  The new unannotated Rule-6 branch emits refusals only, so any
assigned tetrahedral result is necessarily the unchanged annotated branch; all four other
families are definitionally the already-proved normalized branches. -/
theorem analyzeNormalizedWithAuthoritativeRule6_assigned_member_independently_judged
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (present : assignment ∈ analyzeNormalizedWithAuthoritativeRule6 result)
    (assigned : assignment.outcome.assigned = true) :
    IndependentlyJudgedNormalizedStereoAssignment result assignment := by
  obtain ⟨_massesKnown, _admissible, branch⟩ :=
    (mem_analyzeNormalizedWithAuthoritativeRule6_iff_branch result assignment).mp present
  apply (independentlyJudgedNormalizedStereoAssignment_iff_branch_membership
    result assignment).mpr
  rcases branch with tetrahedral | ordinary | coupled | odd | axial
  · exact Or.inl
      (assigned_authoritativeTetrahedral_member_originalTetrahedral
        result assignment tetrahedral assigned)
  · exact Or.inr (Or.inl ordinary)
  · exact Or.inr (Or.inr (Or.inl
      ((mem_normalizedCoupledDoubleBond_iff_independent_judgment
        result assignment).mp coupled)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl odd)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr axial)))

/-- Every chemically applicable unannotated Rule-6 center reaches the actual replacement analyzer
whenever the unchanged molecule-wide admission guards accept the normalized molecule. -/
theorem every_chemicallyApplicable_unannotatedRule6Center_mem_completePipeline
    (result : ChemistryNormalizationResult)
    (state : RawDescriptorState) (center : Nat)
    (massesKnown : result.parsed.rule2MassesKnown? = true)
    (admissible : result.expandedStereochemicalAdmissible? = true)
    (applicable : AuthoritativeUnannotatedRule6ChemicalApplicability
      result result.parsed.withExplicitHydrogens state center)
    (stateEq : state = discoverRawDescriptors result result.parsed.withExplicitHydrogens
      (analysisFuel result.parsed.withExplicitHydrogens)) :
    ∃ assignment,
      assignment ∈ analyzeNormalizedWithAuthoritativeRule6 result ∧
      assignment.unit = .tetrahedral center ∧
      assignment.outcome = .refused .notSpecified := by
  subst state
  have writtenExact : result.parsed.withExplicitHydrogens.WrittenNeighborExact :=
    ((result.expandedStereochemicalAdmissible?_eq_true_iff).mp admissible).2
  obtain ⟨assignment, tetrahedralPresent, unitEq, outcomeEq, _count⟩ :=
    every_chemicallyApplicable_unannotatedRule6Center_public_exactly_once
      result result.parsed.withExplicitHydrogens
        (discoverRawDescriptors result result.parsed.withExplicitHydrogens
          (analysisFuel result.parsed.withExplicitHydrogens)) center writtenExact applicable
  refine ⟨assignment, ?_, unitEq, outcomeEq⟩
  apply (mem_analyzeNormalizedWithAuthoritativeRule6_iff_branch result assignment).mpr
  exact ⟨massesKnown, admissible, Or.inl tetrahedralPresent⟩

/-- The stronger molecule-wide multiplicity statement.  A chemically applicable unannotated
Rule-6 center occurs exactly once in the complete guarded analyzer: once in the authoritative
tetrahedral scan and zero times in every retained non-tetrahedral branch. -/
theorem every_chemicallyApplicable_unannotatedRule6Center_completePipeline_exactly_once
    (result : ChemistryNormalizationResult)
    (state : RawDescriptorState) (center : Nat)
    (massesKnown : result.parsed.rule2MassesKnown? = true)
    (admissible : result.expandedStereochemicalAdmissible? = true)
    (applicable : AuthoritativeUnannotatedRule6ChemicalApplicability
      result result.parsed.withExplicitHydrogens state center)
    (stateEq : state = discoverRawDescriptors result result.parsed.withExplicitHydrogens
      (analysisFuel result.parsed.withExplicitHydrogens)) :
    ∃ assignment,
      assignment ∈ analyzeNormalizedWithAuthoritativeRule6 result ∧
      assignment.unit = .tetrahedral center ∧
      assignment.outcome = .refused .notSpecified ∧
      List.count (.tetrahedral center)
        ((analyzeNormalizedWithAuthoritativeRule6 result).map StereoAssignment.unit) = 1 := by
  subst state
  have writtenExact : result.parsed.withExplicitHydrogens.WrittenNeighborExact :=
    ((result.expandedStereochemicalAdmissible?_eq_true_iff).mp admissible).2
  obtain ⟨assignment, tetrahedralPresent, unitEq, outcomeEq, tetrahedralCount⟩ :=
    every_chemicallyApplicable_unannotatedRule6Center_public_exactly_once
      result result.parsed.withExplicitHydrogens
        (discoverRawDescriptors result result.parsed.withExplicitHydrogens
          (analysisFuel result.parsed.withExplicitHydrogens)) center writtenExact applicable
  have publicPresent : assignment ∈ analyzeNormalizedWithAuthoritativeRule6 result := by
    apply (mem_analyzeNormalizedWithAuthoritativeRule6_iff_branch result assignment).mpr
    exact ⟨massesKnown, admissible, Or.inl tetrahedralPresent⟩
  have nonTetrahedralCount :=
    normalizedNonTetrahedralBranches_tetrahedral_count_eq_zero result center
  have tetrahedralCountAtProductionFuel :
      List.count (.tetrahedral center)
        ((tetrahedralAssignmentsWithAuthoritativeRule6
          result result.parsed.withExplicitHydrogens
            (discoverRawDescriptors result result.parsed.withExplicitHydrogens
              (analysisFuel result.parsed.withExplicitHydrogens))
            (analysisFuel result.parsed.withExplicitHydrogens)).map
              StereoAssignment.unit) = 1 := by
    simpa [unannotatedRule6ChemicalFuel] using tetrahedralCount
  have analyzerEq : analyzeNormalizedWithAuthoritativeRule6 result =
      tetrahedralAssignmentsWithAuthoritativeRule6
          result result.parsed.withExplicitHydrogens
            (discoverRawDescriptors result result.parsed.withExplicitHydrogens
              (analysisFuel result.parsed.withExplicitHydrogens))
            (analysisFuel result.parsed.withExplicitHydrogens) ++
        ((normalizedStereoAnalysisBranches result).ordinaryDoubleBond ++
          (normalizedStereoAnalysisBranches result).coupledDoubleBond ++
          (normalizedStereoAnalysisBranches result).oddCumuleneDoubleBond ++
          (normalizedStereoAnalysisBranches result).extendedAxial) := by
    simp [analyzeNormalizedWithAuthoritativeRule6, massesKnown, admissible,
      normalizedStereoAnalysisBranchesWithAuthoritativeRule6, List.append_assoc]
  refine ⟨assignment, publicPresent, unitEq, outcomeEq, ?_⟩
  rw [analyzerEq, List.map_append, List.count_append, tetrahedralCountAtProductionFuel,
    nonTetrahedralCount]

end AuthoritativeCIPRule6Scheduler
end TetraStereo.OneCenter
