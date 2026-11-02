import TetraStereo.UniversalProof.NextFrontier.FramedParsedParitySchedulerLeaves
import TetraStereo.UniversalProof.NextFrontier.SeedToSourceBridge

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace TetraStereo.UniversalProof.FramedParsedParityFinish
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.FramedParsedParitySeed
open TetraStereo.UniversalProof.FramedParsedParitySchedulerCenter
open TetraStereo.UniversalProof.FramedParsedParitySchedulerLeaves

/-- Actual annotation/lookup leaf. Equal arms have unresolved [1], not an empty list. -/
theorem unresolved_centers (center left right : TetrahedralInputParity) :
    (rawAnnotatedCenters (actualResult center left right)).filter
      (fun atom => ((stateD center left right).factAt? atom).isNone) =
        if left = right then [1] else [] := by
  cases center <;> cases left <;> cases right <;> decide +kernel

/-- Both seed facts and the lowercase central fact fail the actual carrier's admission guard.
This is a small field/condition reduction, not traversal of a guessed cyclic witness. -/
theorem normalize_stateD (center left right : TetrahedralInputParity) :
    normalizeTwoCyclicRule6AnchorCarrier (actualMol center left right)
      (actualFuel center left right) (stateD center left right) = stateD center left right := by
  cases center <;> cases left <;> cases right <;> decide +kernel

/-- Generic empty unresolved-list reduction of the actual constructive auxiliary algorithm. -/
theorem auxiliary_noop_of_empty (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : Nat) (seed : RawDescriptorState)
    (empty : (rawAnnotatedCenters result).filter
      (fun center => (seed.factAt? center).isNone) = []) :
    solveAuxiliaryDescriptorDependencies result mol maxEvidenceSize fuel seed = seed := by
  simp [solveAuxiliaryDescriptorDependencies, empty, auxiliarySimultaneousDescriptorState]

theorem exact_auxiliary_noop_of_empty (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : Nat) (seed : RawDescriptorState)
    (empty : (rawAnnotatedCenters result).filter
      (fun center => (seed.factAt? center).isNone) = []) :
    solveExactAuxiliaryDescriptorDependencies result mol maxEvidenceSize fuel seed = seed := by
  simp [solveExactAuxiliaryDescriptorDependencies, empty]

/-- Finishing only delegates to the actual exact solver, or returns the same state. -/
theorem finish_noop_of_exact_noop (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel : Nat) (stable : RawDescriptorState)
    (exactNoop : solveExactAuxiliaryDescriptorDependencies result mol 100 fuel stable = stable) :
    finishRawDescriptorSource result mol fuel stable = stable := by
  unfold finishRawDescriptorSource
  dsimp only
  split
  · rfl
  · exact exactNoop

theorem opposite_unresolved_empty (center left right : TetrahedralInputParity)
    (opposite : left ≠ right) :
    (rawAnnotatedCenters (actualResult center left right)).filter
      (fun atom => ((stateD center left right).factAt? atom).isNone) = [] := by
  rw [unresolved_centers]
  simp only [opposite, if_false]

theorem opposite_auxiliary_noop (center left right : TetrahedralInputParity)
    (opposite : left ≠ right) :
    solveAuxiliaryDescriptorDependencies (actualResult center left right)
      (actualMol center left right) 100 (actualFuel center left right)
      (stateD center left right) = stateD center left right := by
  exact auxiliary_noop_of_empty _ _ _ _ _ (opposite_unresolved_empty center left right opposite)

theorem opposite_finish_noop (center left right : TetrahedralInputParity)
    (opposite : left ≠ right) :
    finishRawDescriptorSource (actualResult center left right) (actualMol center left right)
      (actualFuel center left right) (stateD center left right) = stateD center left right := by
  apply finish_noop_of_exact_noop
  exact exact_auxiliary_noop_of_empty _ _ _ _ _
    (opposite_unresolved_empty center left right opposite)

/-- The production selector, derived from actual stages and the independently proved seed.
This restricted theorem covers the four opposite-arm members; equal-arm solver leaves are separate. -/
theorem opposite_actual_source (center left right : TetrahedralInputParity)
    (opposite : left ≠ right) :
    discoverRawDescriptorSource (actualResult center left right) (actualMol center left right)
      (actualFuel center left right) = stateD center left right := by
  exact SeedToSourceBridge.source_of_nonempty_seed_transition
    (actualResult center left right) (actualMol center left right) (actualFuel center left right)
    (expectedSeed left right) (stateD center left right) (actual_initial center left right)
    rfl (stabilized_from_seed center left right) (stabilized_from_stateD center left right)
    (opposite_auxiliary_noop center left right opposite)
    (opposite_finish_noop center left right opposite)

theorem opposite_actual_descriptors (center left right : TetrahedralInputParity)
    (opposite : left ≠ right) :
    discoverRawDescriptors (actualResult center left right) (actualMol center left right)
      (actualFuel center left right) = stateD center left right := by
  unfold discoverRawDescriptors
  rw [opposite_actual_source center left right opposite]
  exact normalize_stateD center left right

end TetraStereo.UniversalProof.FramedParsedParityFinish
