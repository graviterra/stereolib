import TetraStereo.OneCenter.CIPAuthoritativeRule6CompletePipelineIntegration
import TetraStereo.OneCenter.CIPAuthoritativeRule6ResolvedBranchAgreement

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter
namespace AuthoritativeCIPRule6Scheduler

open RawMolecule

/-!
# Semantic integration of unannotated Rule-6 refusal

The complete-pipeline boundary originally retained one executable clause in the meaning of an
unannotated tetrahedral `rankingUnresolved` refusal.  This module replaces precisely that clause
with the six-way semantic source classification, under the explicit operational domain proved
necessary by the source refusal theorem.

No chemical universality is asserted: every exact theorem below carries either the one-center
operational premise or its bounded molecule-wide family explicitly.
-/

/-- The independent meaning of an integrated unannotated tetrahedral ranking refusal after
eliminating the source adapter result.

The final clause expands, through `AuthoritativeSourceRule6SemanticUnresolved`, to construction,
sort, adjacency, noncanonical-order, topology, or promoted Rule-6 semantic failure. -/
def AuthoritativeUnannotatedTetrahedralSemanticRankingUnresolved
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
    AuthoritativeSourceRule6SemanticUnresolved mol fuel center

/-- Exact elimination of the last executable source-refusal clause from the existing integrated
ranking-unresolved applicability predicate. -/
theorem authoritativeUnannotatedTetrahedralRankingUnresolved_iff_semantic
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (operational : AuthoritativeSourceRule6ResolvedOperationalDomain mol fuel center) :
    AuthoritativeUnannotatedTetrahedralRankingUnresolved
        result mol state fuel center ↔
      AuthoritativeUnannotatedTetrahedralSemanticRankingUnresolved
        result mol state fuel center := by
  unfold AuthoritativeUnannotatedTetrahedralRankingUnresolved
  unfold AuthoritativeUnannotatedTetrahedralSemanticRankingUnresolved
  rw [authoritativeSourceRule6Stereogenicity?_eq_none_iff_semanticUnresolved
    mol fuel center operational]

/-- The one-center integrated public outcome is `rankingUnresolved` exactly for the fully semantic
refusal predicate. -/
theorem unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_rankingUnresolved_iff_semantic
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (operational : AuthoritativeSourceRule6ResolvedOperationalDomain mol fuel center) :
    unannotatedTetrahedralOutcomeWithAuthoritativeRule6?
        result mol state fuel center = some (.refused .rankingUnresolved) ↔
      AuthoritativeUnannotatedTetrahedralSemanticRankingUnresolved
        result mol state fuel center :=
  (unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_rankingUnresolved_iff
      result mol state fuel center).trans
    (authoritativeUnannotatedTetrahedralRankingUnresolved_iff_semantic
      result mol state fuel center operational)

/-- Complete two-case semantic normal form for every present one-center unannotated outcome.
Configuration-unspecified readiness retains its independent stereogenicity judgment; unresolved
refusal uses only the six-way semantic failure classification. -/
theorem unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_some_iff_semantic
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) (outcome : StereoOutcome)
    (operational : AuthoritativeSourceRule6ResolvedOperationalDomain mol fuel center) :
    unannotatedTetrahedralOutcomeWithAuthoritativeRule6?
        result mol state fuel center = some outcome ↔
      (outcome = .refused .notSpecified ∧
        AuthoritativeUnannotatedTetrahedralStereogenic
          result mol state fuel center) ∨
      (outcome = .refused .rankingUnresolved ∧
        AuthoritativeUnannotatedTetrahedralSemanticRankingUnresolved
          result mol state fuel center) := by
  rw [unannotatedTetrahedralOutcomeWithAuthoritativeRule6?_eq_some_iff]
  rw [authoritativeUnannotatedTetrahedralRankingUnresolved_iff_semantic
    result mol state fuel center operational]

/-- Assignment-level meaning of the authoritative unannotated branch with its unresolved arm
stated semantically.  The successful configuration-unspecified arm is unchanged. -/
def AuthoritativeUnannotatedTetrahedralSemanticAssignmentJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (assignment : StereoAssignment) : Prop :=
  (assignment =
      { unit := .tetrahedral center, outcome := .refused .notSpecified } ∧
    AuthoritativeUnannotatedTetrahedralStereogenic
      result mol state fuel center) ∨
  (assignment =
      { unit := .tetrahedral center, outcome := .refused .rankingUnresolved } ∧
    AuthoritativeUnannotatedTetrahedralSemanticRankingUnresolved
      result mol state fuel center)

/-- Exact assignment adapter theorem with semantic refusal and no executable source-none premise. -/
theorem unannotatedTetrahedralAssignmentWithAuthoritativeRule6?_eq_some_iff_semantic
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (assignment : StereoAssignment)
    (operational : AuthoritativeSourceRule6ResolvedOperationalDomain mol fuel center) :
    unannotatedTetrahedralAssignmentWithAuthoritativeRule6?
        result mol state fuel center = some assignment ↔
      AuthoritativeUnannotatedTetrahedralSemanticAssignmentJudgment
        result mol state fuel center assignment := by
  rw [unannotatedTetrahedralAssignmentWithAuthoritativeRule6?_eq_some_iff]
  unfold AuthoritativeUnannotatedTetrahedralAssignmentJudgment
  unfold AuthoritativeUnannotatedTetrahedralSemanticAssignmentJudgment
  rw [authoritativeUnannotatedTetrahedralRankingUnresolved_iff_semantic
    result mol state fuel center operational]

/-- Public one-center tetrahedral judgment with semantic refusal on the unannotated branch.
Annotated P-93 assignment remains literally unchanged. -/
def AuthoritativePublicTetrahedralSemanticAssignmentJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (assignment : StereoAssignment) : Prop :=
  match result.parsed.atomAt? center with
  | none => False
  | some spec =>
      match spec.tetrahedral? with
      | none =>
          AuthoritativeUnannotatedTetrahedralSemanticAssignmentJudgment
            result mol state fuel center assignment
      | some _ =>
          BlueBookP93.Acyclic.AnnotatedTetrahedralAssignmentJudgment
            result mol state fuel center assignment

/-- Existing and semantic public one-center judgments coincide on the explicit operational
domain. -/
theorem authoritativePublicTetrahedralAssignmentJudgment_iff_semantic
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat)
    (assignment : StereoAssignment)
    (operational : AuthoritativeSourceRule6ResolvedOperationalDomain mol fuel center) :
    AuthoritativePublicTetrahedralAssignmentJudgment
        result mol state fuel center assignment ↔
      AuthoritativePublicTetrahedralSemanticAssignmentJudgment
        result mol state fuel center assignment := by
  unfold AuthoritativePublicTetrahedralAssignmentJudgment
  unfold AuthoritativePublicTetrahedralSemanticAssignmentJudgment
  cases atomEq : result.parsed.atomAt? center with
  | none => simp [atomEq]
  | some spec =>
      cases parityEq : spec.tetrahedral? with
      | some parity => simp [atomEq, parityEq]
      | none =>
          simp only [atomEq, parityEq]
          unfold AuthoritativeUnannotatedTetrahedralAssignmentJudgment
          unfold AuthoritativeUnannotatedTetrahedralSemanticAssignmentJudgment
          rw [authoritativeUnannotatedTetrahedralRankingUnresolved_iff_semantic
            result mol state fuel center operational]

/-- Bounded operational family required by the molecule-wide tetrahedral scan. -/
def AuthoritativeTetrahedralScanRule6OperationalDomain
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel : Nat) : Prop :=
  ∀ center, center < result.parsed.atomCount →
    AuthoritativeSourceRule6ResolvedOperationalDomain mol fuel center

/-- Exact public tetrahedral-list membership after replacing all unannotated ranking-refusal
clauses by the semantic classification. -/
theorem mem_tetrahedralAssignmentsWithAuthoritativeRule6_iff_semantic_judgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel : Nat) (assignment : StereoAssignment)
    (operational : AuthoritativeTetrahedralScanRule6OperationalDomain result mol fuel) :
    assignment ∈ tetrahedralAssignmentsWithAuthoritativeRule6 result mol state fuel ↔
      ∃ center < result.parsed.atomCount,
        AuthoritativePublicTetrahedralSemanticAssignmentJudgment
          result mol state fuel center assignment := by
  rw [mem_tetrahedralAssignmentsWithAuthoritativeRule6_iff_independent_judgment]
  constructor
  · rintro ⟨center, centerBound, judgment⟩
    exact ⟨center, centerBound,
      (authoritativePublicTetrahedralAssignmentJudgment_iff_semantic
        result mol state fuel center assignment
          (operational center centerBound)).mp judgment⟩
  · rintro ⟨center, centerBound, judgment⟩
    exact ⟨center, centerBound,
      (authoritativePublicTetrahedralAssignmentJudgment_iff_semantic
        result mol state fuel center assignment
          (operational center centerBound)).mpr judgment⟩

/-- Five-branch normalized judgment with semantic unannotated Rule-6 refusal. -/
def SemanticallyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment) : Prop :=
  let mol := result.parsed.withExplicitHydrogens
  let fuel := analysisFuel mol
  let state := discoverRawDescriptors result mol fuel
  let geometryState := normalizedGeometryDescriptorState result mol fuel state
  (∃ center < result.parsed.atomCount,
      AuthoritativePublicTetrahedralSemanticAssignmentJudgment
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

/-- Operational domain specialized to the production-normalized molecule and fuel. -/
def AuthoritativeNormalizedRule6OperationalDomain
    (result : ChemistryNormalizationResult) : Prop :=
  let mol := result.parsed.withExplicitHydrogens
  AuthoritativeTetrahedralScanRule6OperationalDomain result mol (analysisFuel mol)

/-- The former normalized independent judgment and its semantic-refusal form are equivalent under
the bounded operational family. -/
theorem independentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6_iff_semantic
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (operational : AuthoritativeNormalizedRule6OperationalDomain result) :
    IndependentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6 result assignment ↔
      SemanticallyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6
        result assignment := by
  let mol := result.parsed.withExplicitHydrogens
  let fuel := analysisFuel mol
  let state := discoverRawDescriptors result mol fuel
  change
    ((∃ center < result.parsed.atomCount,
        AuthoritativePublicTetrahedralAssignmentJudgment
          result mol state fuel center assignment) ∨ _) ↔
      ((∃ center < result.parsed.atomCount,
        AuthoritativePublicTetrahedralSemanticAssignmentJudgment
          result mol state fuel center assignment) ∨ _)
  apply or_congr
  · constructor
    · rintro ⟨center, centerBound, judgment⟩
      exact ⟨center, centerBound,
        (authoritativePublicTetrahedralAssignmentJudgment_iff_semantic
          result mol state fuel center assignment
            (operational center centerBound)).mp judgment⟩
    · rintro ⟨center, centerBound, judgment⟩
      exact ⟨center, centerBound,
        (authoritativePublicTetrahedralAssignmentJudgment_iff_semantic
          result mol state fuel center assignment
            (operational center centerBound)).mpr judgment⟩
  · exact Iff.rfl

/-- Exact complete public-analyzer membership with every unannotated Rule-6 unresolved output
explained by the six-way semantic classification. -/
theorem mem_analyzeNormalizedWithAuthoritativeRule6_iff_semantically_judged
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (operational : AuthoritativeNormalizedRule6OperationalDomain result) :
    assignment ∈ analyzeNormalizedWithAuthoritativeRule6 result ↔
      result.parsed.rule2MassesKnown? = true ∧
      result.expandedStereochemicalAdmissible? = true ∧
      SemanticallyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6
        result assignment :=
  (mem_analyzeNormalizedWithAuthoritativeRule6_iff_independently_judged
      result assignment).trans
    (and_congr Iff.rfl
      (and_congr Iff.rfl
        (independentlyJudgedNormalizedStereoAssignmentWithAuthoritativeRule6_iff_semantic
          result assignment operational)))

end AuthoritativeCIPRule6Scheduler
end TetraStereo.OneCenter
