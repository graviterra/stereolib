import TetraStereo.UniversalProof.NextFrontier.FramedParsedParityFinish

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace TetraStereo.UniversalProof.FramedParsedParityFinishEqualSupport
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.FramedParsedParityFamily
open TetraStereo.UniversalProof.FramedParsedParitySeed
open TetraStereo.UniversalProof.FramedParsedParitySchedulerCenter
open TetraStereo.UniversalProof.FramedParsedParitySchedulerLeaves
open TetraStereo.UniversalProof.FramedParsedParityFinish

/-- The exact primitive guard inside the maintained auxiliary fold. This definition observes
that guard, without changing its comparator, seed, symmetry search or occurrence caller. -/
def auxiliaryRefusalGate (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (seed : RawDescriptorState) (fuel center : Nat) : Bool :=
  let ligands := mol.ligandsWithLonePair center
  let uncachedCompareAt := fun left right =>
    compareBranchesBeforeRule6? result mol seed fuel center
      (ligands.getD left 0) (ligands.getD right 0)
  let comparisonCache := cachePositionComparisons ligands.length uncachedCompareAt
  let compareAt := cachedPositionComparison? comparisonCache
  let oddSeedSymmetry? := hasOddConstitutionAutomorphismAtCenter mol center ligands
    (fun left right => compareAt left right == some Ordering.eq)
  oddSeedSymmetry? != some false && (tetrahedralOccurrenceFact? mol fuel center).isNone

/-- Actual primitive guard and guarded assignment refusal suffice for the real singleton fold.
The provisional descriptor constructor is not assumed unavailable. -/
theorem auxiliary_noop_singleton (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel center : Nat) (seed : RawDescriptorState)
    (unresolved : (rawAnnotatedCenters result).filter
      (fun atom => (seed.factAt? atom).isNone) = [center])
    (refused : auxiliaryRefusalGate result mol seed fuel center = true)
    (unassigned : tetrahedralFactFromState? result mol seed maxEvidenceSize fuel center = none) :
    solveAuxiliaryDescriptorDependencies result mol maxEvidenceSize fuel seed = seed := by
  dsimp only [auxiliaryRefusalGate] at refused
  have notPair : (seed.isEmpty && ([center] : List Nat).length == 2) = false := by
    cases seed.isEmpty <;> rfl
  unfold solveAuxiliaryDescriptorDependencies
  rw [unresolved]
  dsimp only []
  rw [notPair]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [refused]
  unfold auxiliarySimultaneousDescriptorState
  simp only [List.foldl_cons, List.foldl_nil]
  simp [unassigned]

/-- Expand only the streaming one-center enumeration. Four primitive candidate refusals imply
its actual .none summary; no desired source or solver output equation is a premise. -/
theorem exact_summary_none_singleton (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel center : Nat) (seed : RawDescriptorState)
    (rTrue : exactAuxiliaryDescriptorCandidate? result mol maxEvidenceSize fuel seed
      [center] [(RS.R, true)] = none)
    (sTrue : exactAuxiliaryDescriptorCandidate? result mol maxEvidenceSize fuel seed
      [center] [(RS.S, true)] = none)
    (rFalse : exactAuxiliaryDescriptorCandidate? result mol maxEvidenceSize fuel seed
      [center] [(RS.R, false)] = none)
    (sFalse : exactAuxiliaryDescriptorCandidate? result mol maxEvidenceSize fuel seed
      [center] [(RS.S, false)] = none) :
    exactAuxiliaryDescriptorSolutionSummary result mol maxEvidenceSize fuel seed [center] =
      .none := by
  simp [exactAuxiliaryDescriptorSolutionSummary, searchAuxiliaryDescriptorEnvironments,
    foldAuxiliaryDescriptorEnvironmentsUntil, AuxiliarySolutionSummary.addCandidate,
    rTrue, sTrue, rFalse, sFalse]

theorem exact_auxiliary_noop_singleton (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel center : Nat) (seed : RawDescriptorState)
    (unresolved : (rawAnnotatedCenters result).filter
      (fun atom => (seed.factAt? atom).isNone) = [center])
    (summary : exactAuxiliaryDescriptorSolutionSummary result mol maxEvidenceSize fuel seed
      [center] = .none) :
    solveExactAuxiliaryDescriptorDependencies result mol maxEvidenceSize fuel seed = seed := by
  unfold solveExactAuxiliaryDescriptorDependencies
  rw [unresolved]
  dsimp only
  split
  · rfl
  · rw [summary]

/-- The center guard leaf already accepted by the scheduler entails this actual equal-arm
assignment refusal, before any finishing-stage premise is considered. -/
theorem equal_center_unassigned (center arm : TetrahedralInputParity) :
    tetrahedralFactFromState? (actualResult center arm arm) (actualMol center arm arm)
      (stateD center arm arm) 100 (actualFuel center arm arm) 1 = none := by
  have same : stateD center arm arm = expectedSeed arm arm := by
    cases arm <;> rfl
  rw [same, central_update_fact]
  cases arm <;> rfl

theorem equal_auxiliary_from_guard (center arm : TetrahedralInputParity)
    (refused : auxiliaryRefusalGate (actualResult center arm arm) (actualMol center arm arm)
      (stateD center arm arm) (actualFuel center arm arm) 1 = true) :
    solveAuxiliaryDescriptorDependencies (actualResult center arm arm) (actualMol center arm arm)
      100 (actualFuel center arm arm) (stateD center arm arm) = stateD center arm arm := by
  apply auxiliary_noop_singleton _ _ _ _ 1 _
  · exact (unresolved_centers center arm arm).trans (if_pos rfl)
  · exact refused
  · exact equal_center_unassigned center arm

end TetraStereo.UniversalProof.FramedParsedParityFinishEqualSupport
