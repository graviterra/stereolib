import TetraStereo.OneCenter.P94WholeMoleculeEvidenceAggregator

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularRequestScheduler

open CoordinateTwistInOut
open P94MolecularAggregator

/-!
# Exhaustive finite P-94 twist and in-out request scheduling

The molecule aggregator accepts explicit twist and in-out requests because their direct-rotation
and framework/electron relations cannot be inferred from coordinates alone.  This module removes a
different caller seam: selection of the candidate path and selection of an observation pair.

For each finite state ledger, every duplicate-free bounded path is enumerated.  The scheduler keeps
exactly the pairs of legs that meet at the candidate and form a simple combined path.  For each
finite in-out observation ledger, every ordered pair is emitted.  The existing independent family
judgments still decide boat/chair geometry, direct rotation edges, bridge sufficiency, direction,
and same-site identity.  Thus scheduling is finite and exhaustive without manufacturing any
chemical premise.
-/

/-! ## Every duplicate-free path through one finite state ledger -/

noncomputable def boundedNodupStatePaths {State : Type*} [DecidableEq State]
    (states : List State) : Finset (List State) :=
  ((states.toFinset.powerset.toList.flatMap fun vertices =>
    vertices.toList.permutations).toFinset)

theorem mem_boundedNodupStatePaths_iff {State : Type*} [DecidableEq State]
    (states path : List State) :
    path ∈ boundedNodupStatePaths states ↔
      path.Nodup ∧ ∀ state ∈ path, state ∈ states := by
  constructor
  · intro present
    have listPresent :
        path ∈ states.toFinset.powerset.toList.flatMap
          (fun vertices => vertices.toList.permutations) := by
      simpa [boundedNodupStatePaths] using present
    rcases List.mem_flatMap.mp listPresent with
      ⟨vertices, verticesPresent, permutationPresent⟩
    have verticesSubset : vertices ⊆ states.toFinset :=
      Finset.mem_powerset.mp (by simpa using verticesPresent)
    have permutation : path.Perm vertices.toList :=
      List.mem_permutations.mp permutationPresent
    refine ⟨permutation.nodup_iff.mpr vertices.nodup_toList, ?_⟩
    intro state statePresent
    have vertexPresent : state ∈ vertices.toList := permutation.mem_iff.mp statePresent
    exact List.mem_toFinset.mp (verticesSubset (by simpa using vertexPresent))
  · rintro ⟨nodup, bounded⟩
    apply List.mem_toFinset.mpr
    apply List.mem_flatMap.mpr
    refine ⟨path.toFinset, ?_, ?_⟩
    · apply Finset.mem_toList.mpr
      apply Finset.mem_powerset.mpr
      intro state statePresent
      exact List.mem_toFinset.mpr (bounded state (List.mem_toFinset.mp statePresent))
    · exact List.mem_permutations.mpr (path.toFinset_toList nodup).symm

/-! ## Twist path candidates -/

/-- Finite complete-state data shared by every candidate path generated from one conformational
ledger.  The direct-rotation relation remains independent evidence and is merely copied into each
request. -/
structure CoordinateTwistLedger (State : Type*) where
  unit : P94ConformationUnit
  states : List State
  spatialAt : State → SpatialConfiguration
  independentSingleBondRotation : State → State → Prop

structure TwistPathCandidate (State : Type*) where
  candidate : State
  firstLeg : List State
  secondLeg : List State
  deriving DecidableEq

def TwistPathCandidate.StructurallyValid {State : Type*} [DecidableEq State]
    (ledger : CoordinateTwistLedger State) (candidate : TwistPathCandidate State) : Prop :=
  candidate.candidate ∈ ledger.states ∧
    candidate.firstLeg ∈ boundedNodupStatePaths ledger.states ∧
    candidate.secondLeg ∈ boundedNodupStatePaths ledger.states ∧
    candidate.firstLeg.getLast? = some candidate.candidate ∧
    candidate.secondLeg.head? = some candidate.candidate ∧
    (candidate.firstLeg ++ candidate.secondLeg.tail).Nodup

noncomputable instance twistPathCandidateStructurallyValidDecidable
    {State : Type*} [DecidableEq State]
    (ledger : CoordinateTwistLedger State) (candidate : TwistPathCandidate State) :
    Decidable (candidate.StructurallyValid ledger) :=
  Classical.propDecidable _

private noncomputable def twistPathCandidateUniverse {State : Type*} [DecidableEq State]
    (ledger : CoordinateTwistLedger State) : Finset (TwistPathCandidate State) :=
  (ledger.states.toFinset.product
    ((boundedNodupStatePaths ledger.states).product
      (boundedNodupStatePaths ledger.states))).image fun entry =>
        { candidate := entry.1
          firstLeg := entry.2.1
          secondLeg := entry.2.2 }

private theorem mem_twistPathCandidateUniverse_iff
    {State : Type*} [DecidableEq State]
    (ledger : CoordinateTwistLedger State) (candidate : TwistPathCandidate State) :
    candidate ∈ twistPathCandidateUniverse ledger ↔
      candidate.candidate ∈ ledger.states ∧
        candidate.firstLeg ∈ boundedNodupStatePaths ledger.states ∧
        candidate.secondLeg ∈ boundedNodupStatePaths ledger.states := by
  constructor
  · intro present
    rcases Finset.mem_image.mp present with ⟨entry, entryPresent, equal⟩
    rcases Finset.mem_product.mp entryPresent with ⟨statePresent, pathsPresent⟩
    rcases Finset.mem_product.mp pathsPresent with ⟨firstPresent, secondPresent⟩
    cases equal
    exact ⟨List.mem_toFinset.mp statePresent, firstPresent, secondPresent⟩
  · rintro ⟨statePresent, firstPresent, secondPresent⟩
    apply Finset.mem_image.mpr
    refine ⟨(candidate.candidate, candidate.firstLeg, candidate.secondLeg), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨List.mem_toFinset.mpr statePresent,
          Finset.mem_product.mpr ⟨firstPresent, secondPresent⟩⟩
    · cases candidate
      rfl

/-- Every structurally possible simple two-leg path through the finite ledger, with no path-length
fuel and no caller-selected candidate. -/
noncomputable def scheduledTwistPathCandidates {State : Type*} [DecidableEq State]
    (ledger : CoordinateTwistLedger State) : Finset (TwistPathCandidate State) :=
  (twistPathCandidateUniverse ledger).filter
    (TwistPathCandidate.StructurallyValid ledger)

theorem mem_scheduledTwistPathCandidates_iff {State : Type*} [DecidableEq State]
    (ledger : CoordinateTwistLedger State) (candidate : TwistPathCandidate State) :
    candidate ∈ scheduledTwistPathCandidates ledger ↔
      candidate.StructurallyValid ledger := by
  constructor
  · exact fun present => (Finset.mem_filter.mp present).2
  · intro valid
    apply Finset.mem_filter.mpr
    exact ⟨(mem_twistPathCandidateUniverse_iff ledger candidate).mpr
      ⟨valid.1, valid.2.1, valid.2.2.1⟩, valid⟩

def CoordinateTwistLedger.toInput {State : Type*}
    (ledger : CoordinateTwistLedger State) (candidate : TwistPathCandidate State) :
    CoordinateTwistInput State :=
  { unit := ledger.unit
    states := ledger.states
    spatialAt := ledger.spatialAt
    independentSingleBondRotation := ledger.independentSingleBondRotation
    candidate := candidate.candidate
    firstLeg := candidate.firstLeg
    secondLeg := candidate.secondLeg }

noncomputable def scheduledCoordinateTwistInputs {State : Type*} [DecidableEq State]
    (ledger : CoordinateTwistLedger State) : List (CoordinateTwistInput State) :=
  (scheduledTwistPathCandidates ledger).toList.map ledger.toInput

theorem mem_scheduledCoordinateTwistInputs_iff {State : Type*} [DecidableEq State]
    (ledger : CoordinateTwistLedger State) (input : CoordinateTwistInput State) :
    input ∈ scheduledCoordinateTwistInputs ledger ↔
      ∃ candidate ∈ scheduledTwistPathCandidates ledger, ledger.toInput candidate = input := by
  simp [scheduledCoordinateTwistInputs]

/-! ## Every ordered in-out observation pair -/

structure CoordinateInOutLedger (Framework : Type*) where
  unit : P94ConformationUnit
  observations : List (CoordinateInOutObservation Framework)

def scheduledCoordinateInOutInputs {Framework : Type*}
    (ledger : CoordinateInOutLedger Framework) : List (CoordinateInOutInput Framework) :=
  ledger.observations.flatMap fun first =>
    ledger.observations.map fun second =>
      { unit := ledger.unit, first := first, second := second }

theorem mem_scheduledCoordinateInOutInputs_iff {Framework : Type*}
    (ledger : CoordinateInOutLedger Framework) (input : CoordinateInOutInput Framework) :
    input ∈ scheduledCoordinateInOutInputs ledger ↔
      ∃ first ∈ ledger.observations, ∃ second ∈ ledger.observations,
        ({ unit := ledger.unit, first := first, second := second } :
          CoordinateInOutInput Framework) = input := by
  simp [scheduledCoordinateInOutInputs]

/-! ## Composition with the verified molecule aggregator -/

structure MolecularEvidenceLedgerPlan (State Framework : Type*) where
  spatial : SpatialConfiguration
  twistLedgers : List (CoordinateTwistLedger State)
  inOutLedgers : List (CoordinateInOutLedger Framework)

noncomputable def MolecularEvidenceLedgerPlan.toEvidencePlan
    {State Framework : Type*} [DecidableEq State]
    (plan : MolecularEvidenceLedgerPlan State Framework) :
    MolecularEvidencePlan State Framework :=
  { spatial := plan.spatial
    twistInputs := plan.twistLedgers.flatMap scheduledCoordinateTwistInputs
    inOutInputs := plan.inOutLedgers.flatMap scheduledCoordinateInOutInputs }

noncomputable def molecularOutcomesFromLedgers {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularEvidenceLedgerPlan State Framework) : List (MolecularOutcome State Framework) :=
  molecularOutcomes premises certified plan.toEvidencePlan

theorem molecularOutcomesFromLedgers_map_request
    {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularEvidenceLedgerPlan State Framework) :
    (molecularOutcomesFromLedgers premises certified plan).map MolecularOutcome.request =
      molecularRequests certified.result.parsed plan.toEvidencePlan :=
  molecularOutcomes_map_request premises certified plan.toEvidencePlan

theorem molecularOutcomesFromLedgers_all_correct
    {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularEvidenceLedgerPlan State Framework) :
    ∀ outcome ∈ molecularOutcomesFromLedgers premises certified plan,
      outcome.Correct premises certified.result.parsed plan.spatial :=
  molecularOutcomes_all_correct premises certified plan.toEvidencePlan

abbrev IndependentMolecularAssignmentFromLedgers
    {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (plan : MolecularEvidenceLedgerPlan State Framework)
    (assignment : P94ConformationAssignment) : Prop :=
  IndependentMolecularAssignment premises molecule plan.toEvidencePlan assignment

noncomputable def molecularAssignmentsFromLedgers
    {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularEvidenceLedgerPlan State Framework) : List P94ConformationAssignment :=
  molecularAssignments premises certified plan.toEvidencePlan

theorem molecularAssignmentsFromLedgers_mem_iff_independent
    {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularEvidenceLedgerPlan State Framework)
    (assignment : P94ConformationAssignment) :
    assignment ∈ molecularAssignmentsFromLedgers premises certified plan ↔
      IndependentMolecularAssignmentFromLedgers premises certified.result.parsed plan assignment :=
  molecularAssignments_mem_iff_independent premises certified plan.toEvidencePlan assignment

theorem molecularAssignmentsFromLedgers_nodup
    {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularEvidenceLedgerPlan State Framework) :
    (molecularAssignmentsFromLedgers premises certified plan).Nodup :=
  molecularAssignments_nodup premises certified plan.toEvidencePlan

theorem molecularAssignmentFromLedgers_count_eq_one_iff
    {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularEvidenceLedgerPlan State Framework)
    (assignment : P94ConformationAssignment) :
    List.count assignment (molecularAssignmentsFromLedgers premises certified plan) = 1 ↔
      IndependentMolecularAssignmentFromLedgers premises certified.result.parsed plan assignment :=
  molecularAssignment_count_eq_one_iff premises certified plan.toEvidencePlan assignment

theorem molecularAssignmentFromLedgers_count_eq_zero_iff
    {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularEvidenceLedgerPlan State Framework)
    (assignment : P94ConformationAssignment) :
    List.count assignment (molecularAssignmentsFromLedgers premises certified plan) = 0 ↔
      ¬IndependentMolecularAssignmentFromLedgers
        premises certified.result.parsed plan assignment :=
  molecularAssignment_count_eq_zero_iff premises certified plan.toEvidencePlan assignment

end BlueBookP94.P94MolecularRequestScheduler
end TetraStereo.OneCenter
